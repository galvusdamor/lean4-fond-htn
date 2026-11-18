import HtnComplexity.TMEnc.TMEncFixExactMark
import HtnComplexity.TMEnc.TMEncFixExec
import HtnComplexity.TMEnc.TMEncFixSize
/-!
# Homing normalisation of a Turing machine

The simulation correctness of the repaired encoding of Theorem 4.3.7 is proved in
`HtnComplexity/TMEnc/TMEncFixExec.lean` (completeness) and
`HtnComplexity/TMEnc/TMEncFixExactMark.lean` (soundness):

* `HTN.TMEnc.solvable_of_homingRunBumpFree` — a **homing** accepting run of *exactly* `K` steps
  that never moves the head left from the first tape cell can be written out as a solution plan;
* `HTN.TMEnc.encodingSoundFix` — a solution plan yields an accepting run of at most `K` steps.

The gap between the two is the shape of the run: the construction encodes runs of exactly `K`
steps that end with the head back on the first tape cell and that never bump into the left end.
The source assumes "w.l.o.g." that an accepting machine has such a run.  This file discharges
that assumption by an explicit **normalisation of the machine**:

    N  ⟼  N⁺ = homingMachine N ,     w ⟼ w⁺ = markInput N w .

The construction is the obvious one.

* The tape alphabet becomes `Γ × Bool`; the second component marks the **first tape cell** and is
  never changed by any transition, so the machine can see when it is at the left end.  The input
  `w⁺ = markInput N w` carries the mark on its first letter (this is why `w ≠ []` is needed).
* The state set becomes `Q ⊕ Bool`.  On `Sum.inl q` the machine simulates `N`, replacing a left
  move at the marked cell by `Move.stay` — which is the same configuration, since
  `Move.apply Move.left 0 = 0` — so that the run is *bump free*.  From an accepting state of `N`
  it may enter the **homing phase** `Sum.inr false`, which walks left until it sees the mark, and
  then the **home state** `Sum.inr true`, which idles at the first cell forever.  The only
  accepting state of `N⁺` is `Sum.inr true`.

## Main results

* `HTN.TMEnc.homingRunBumpFree_homingMachine` — if `N` accepts `w` within `K` steps then `N⁺` has
  a homing, bump-free accepting run of *exactly* `K'` steps, for every `K' ≥ 2K + 1`;
* `HTN.TMEnc.acceptsWithin_of_homingMachine` — conversely, if `N⁺` accepts `w⁺` within `M` steps
  then `N` accepts `w` within `M` steps;
* `HTN.TMEnc.solvable_problemFix_homingMachine` and
  `HTN.TMEnc.acceptsWithin_of_solvable_homingMachine` — the two halves at the level of the
  encoded planning problem, and
* `HTN.TMEnc.solvable_problemFix_homingMachine_iff` — for a machine that is *clocked* at `K`
  (one that cannot accept later than at step `K` without accepting within `K`, which is the
  situation of the hardness argument, where `N` is a machine deciding a language in time `K`),

      (problemFix N⁺ w⁺ K').Solvable  ↔  N.AcceptsWithin w K      (K' ≥ 2K+1),

  i.e. the encoding of the *normalised* machine decides acceptance of the original one.
  `HTN.TMEnc.encodingCorrect_homingMachine` is the same statement in the exponential-time
  wording of the source (`AcceptsExp`).
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} (N : NTM Q Γ)

/-! ### The construction -/

/-- The move a simulating transition makes: a left move at the marked (first) tape cell becomes
`Move.stay`, which has the same effect (`Move.apply Move.left 0 = 0`) but does not bump into the
left end of the tape. -/
def homeMove (b : Bool) (m : Move) : Move :=
  if b = true ∧ m = Move.left then Move.stay else m

/-- The transition of the homing phase: at the marked cell go to the home state, otherwise walk
one cell to the left. -/
def homeStep (Q : Type) {Γ : Type} (x : Γ × Bool) : (Q ⊕ Bool) × (Γ × Bool) × Move :=
  if x.2 then (Sum.inr true, x, Move.stay) else (Sum.inr false, x, Move.left)

/-- The transition relation of the normalised machine. -/
def homingStep (N : NTM Q Γ) :
    (Q ⊕ Bool) → (Γ × Bool) → Set ((Q ⊕ Bool) × (Γ × Bool) × Move)
  | Sum.inl q, x =>
      {y | ∃ q' a' m, (q', a', m) ∈ N.step q x.1 ∧ y = (Sum.inl q', (a', x.2), homeMove x.2 m)} ∪
        {y | q ∈ N.accept ∧ y = homeStep Q x}
  | Sum.inr false, x => {homeStep Q x}
  | Sum.inr true, x => {(Sum.inr true, x, Move.stay)}

/-- **The normalised machine.**  It simulates `N` on the marked tape, never moves left from the
first cell, and once `N` has accepted it walks home and idles there in its only accepting
state. -/
def homingMachine (N : NTM Q Γ) : NTM (Q ⊕ Bool) (Γ × Bool) where
  step := homingStep N
  init := Sum.inl N.init
  accept := {Sum.inr true}
  blank := (N.blank, false)

/-- The input of the normalised machine: the input of `N` with its first letter marked. -/
def markInput (N : NTM Q Γ) (w : List Γ) : List (Γ × Bool) :=
  (List.range w.length).map fun i => (w.getD i N.blank, decide (i = 0))

@[simp] lemma markInput_length (w : List Γ) : (markInput N w).length = w.length := by
  simp [markInput]

lemma markInput_getD {w : List Γ} (hw : w ≠ []) (i : ℕ) :
    (markInput N w).getD i (N.blank, false) = (w.getD i N.blank, decide (i = 0)) := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw
  rcases lt_or_ge i w.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa [markInput] using hi)]
    simp [markInput, hi]
  · rw [List.getD_eq_default _ _ (by simpa [markInput] using hi)]
    have h0 : i ≠ 0 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    simp [h0]

/-! ### Bump-free runs -/

/-- `ReachesBF M n c c'` is `TM.NTM.Reaches` for bump-free steps (`HTN.TMEnc.StepBumpFree`). -/
def ReachesBF {Q' Γ' : Type} (M : NTM Q' Γ') : ℕ → Config Q' Γ' → Config Q' Γ' → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ d, StepBumpFree M c d ∧ ReachesBF M n d c'

lemma ReachesBF.trans {Q' Γ' : Type} {M : NTM Q' Γ'} {m n : ℕ} {c d e : Config Q' Γ'}
    (h₁ : ReachesBF M m c d) (h₂ : ReachesBF M n d e) : ReachesBF M (m + n) c e := by
  induction m generalizing c with
  | zero => cases h₁; simpa using h₂
  | succ m ih =>
      obtain ⟨x, hx, hxd⟩ := h₁
      rw [show m + 1 + n = (m + n) + 1 by omega]
      exact ⟨x, hx, ih hxd⟩

/-- A bump-free run can be turned into an explicit sequence of configurations that is constant
after its last step. -/
lemma exists_path_of_reachesBF {Q' Γ' : Type} {M : NTM Q' Γ'} {m : ℕ} {c c' : Config Q' Γ'}
    (h : ReachesBF M m c c') :
    ∃ hist : ℕ → Config Q' Γ', hist 0 = c ∧
      (∀ i < m, StepBumpFree M (hist i) (hist (i + 1))) ∧ ∀ i, m ≤ i → hist i = c' := by
  induction m generalizing c with
  | zero =>
      have hcc : c = c' := h
      exact ⟨fun _ => c', hcc.symm, by omega, fun _ _ => rfl⟩
  | succ m ih =>
      obtain ⟨d, hstep, hd⟩ := h
      obtain ⟨hist, h0, hsteps, hlast⟩ := ih hd
      refine ⟨fun i => if i = 0 then c else hist (i - 1), by simp, ?_, ?_⟩
      · intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simpa [h0] using hstep
        · have h1 : ¬ i = 0 := by omega
          have h2 : ¬ i + 1 = 0 := by omega
          simp only [h1, h2, if_false]
          have hlt : i - 1 < m := by omega
          simpa [show i + 1 - 1 = (i - 1) + 1 by omega] using hsteps (i - 1) hlt
      · intro i hi
        have h1 : ¬ i = 0 := by omega
        simp only [h1, if_false]
        exact hlast _ (by omega)

/-- A bump-free run into a self-looping accepting configuration at the first cell is a homing,
bump-free accepting run of *any* length beyond it. -/
lemma homingRunBumpFree_of_reachesBF {Q' Γ' : Type} {M : NTM Q' Γ'} {w' : List Γ'} {m K' : ℕ}
    {c : Config Q' Γ'} (h : ReachesBF M m (M.initConfig w') c) (hm : m ≤ K')
    (hloop : StepBumpFree M c c) (hacc : c.state ∈ M.accept) (hhead : c.head = 0) :
    HomingRunBumpFree M w' K' := by
  obtain ⟨hist, h0, hsteps, hlast⟩ := exists_path_of_reachesBF h
  refine ⟨hist, h0, ?_, ?_, ?_⟩
  · intro i hi
    rcases lt_or_ge i m with h1 | h1
    · exact hsteps i h1
    · rw [hlast i h1, hlast (i + 1) (by omega)]
      exact hloop
  · rw [hlast K' hm]; exact hacc
  · rw [hlast K' hm]; exact hhead

/-! ### The simulation -/

/-- The configuration of the normalised machine that corresponds to a configuration of `N`. -/
def liftC (c : Config Q Γ) : Config (Q ⊕ Bool) (Γ × Bool) :=
  ⟨Sum.inl c.state, c.head, fun i => (c.tape i, decide (i = 0))⟩

/-- The configuration of `N` that a configuration of the normalised machine in a simulating state
stands for. -/
def unliftC (q : Q) (c : Config (Q ⊕ Bool) (Γ × Bool)) : Config Q Γ :=
  ⟨q, c.head, fun i => (c.tape i).1⟩

/-- The tape invariant: exactly the first cell is marked. -/
def Marked (c : Config (Q ⊕ Bool) (Γ × Bool)) : Prop := ∀ i, (c.tape i).2 = decide (i = 0)

lemma marked_liftC (c : Config Q Γ) : Marked (liftC c) := fun _ => rfl

lemma homeMove_apply {b : Bool} {m : Move} {n : ℕ} (h : b = true → n = 0) :
    (homeMove b m).apply n = m.apply n := by
  unfold homeMove
  by_cases hb : b = true ∧ m = Move.left
  · obtain ⟨hb1, hb2⟩ := hb
    simp [hb1, hb2, h hb1]
  · simp [hb]

lemma homeMove_ne_left {b : Bool} {m : Move} (h : homeMove b m = Move.left) : b = false := by
  cases b
  · rfl
  · cases m <;> simp [homeMove] at h

/-- Equality of configurations, componentwise. -/
lemma config_eq {Q' Γ' : Type} {c d : Config Q' Γ'} (h1 : c.state = d.state)
    (h2 : c.head = d.head) (h3 : c.tape = d.tape) : c = d := by
  cases c; cases d; simp_all

/-- The homing transition writes the symbol it read, mark included. -/
lemma homeStep_snd (x : Γ × Bool) : (homeStep Q x).2.1 = x := by
  cases hb : x.2 <;> simp [homeStep, hb]

/-- No transition of the normalised machine changes the mark of the cell it writes. -/
lemma tape_snd_of_mem_homingStep {s : Q ⊕ Bool} {x : Γ × Bool}
    {y : (Q ⊕ Bool) × (Γ × Bool) × Move} (h : y ∈ homingStep N s x) : y.2.1.2 = x.2 := by
  match s with
  | Sum.inl q =>
      rcases h with h | h
      · obtain ⟨q', a', m, -, rfl⟩ := h; rfl
      · obtain ⟨-, rfl⟩ := h; rw [homeStep_snd]
  | Sum.inr false =>
      have hy : y = homeStep Q x := h
      rw [hy, homeStep_snd]
  | Sum.inr true =>
      have hy : y = (Sum.inr true, x, Move.stay) := h
      rw [hy]

/-- One step of `N` is one bump-free step of the normalised machine. -/
lemma stepBumpFree_liftC {c d : Config Q Γ} (h : N.Step c d) :
    StepBumpFree (homingMachine N) (liftC c) (liftC d) := by
  obtain ⟨q', γ', m, hmem, rfl⟩ := h
  refine ⟨Sum.inl q', (γ', decide (c.head = 0)), homeMove (decide (c.head = 0)) m, ?_, ?_, ?_⟩
  · refine Or.inl ⟨q', γ', m, hmem, rfl⟩
  · have hhead : (homeMove (decide (c.head = 0)) m).apply c.head = m.apply c.head :=
      homeMove_apply (by intro hb; simpa using hb)
    refine config_eq ?_ ?_ ?_
    · rfl
    · simpa [liftC] using hhead.symm
    · funext i
      by_cases hi : i = c.head
      · subst hi; simp [liftC]
      · simp [liftC, Function.update_of_ne hi]
  · intro hleft
    have hb := homeMove_ne_left hleft
    have : ¬ (c.head = 0) := by simpa using hb
    simpa [liftC] using Nat.one_le_iff_ne_zero.2 this

lemma reachesBF_liftC {n : ℕ} {c d : Config Q Γ} (h : N.Reaches n c d) :
    ReachesBF (homingMachine N) n (liftC c) (liftC d) := by
  induction n generalizing c with
  | zero => cases h; rfl
  | succ n ih =>
      obtain ⟨e, hstep, he⟩ := h
      exact ⟨liftC e, stepBumpFree_liftC N hstep, ih he⟩

/-! ### The homing phase -/

/-- Walking home from the cell `p` takes `p + 1` steps and changes nothing but the state and the
head position. -/
lemma reachesBF_walk (t : ℕ → Γ × Bool) (ht : ∀ i, (t i).2 = decide (i = 0)) (p : ℕ) :
    ReachesBF (homingMachine N) (p + 1)
      ⟨Sum.inr false, p, t⟩ ⟨Sum.inr true, 0, t⟩ := by
  induction p with
  | zero =>
      refine ⟨⟨Sum.inr true, 0, t⟩, ⟨Sum.inr true, t 0, Move.stay, ?_, ?_, by simp⟩, rfl⟩
      · have h0 : (t 0).2 = true := by simp [ht 0]
        show _ ∈ homingStep N (Sum.inr false) (t 0)
        simp [homingStep, homeStep, h0]
      · refine config_eq rfl (by simp) ?_
        funext i
        by_cases hi : i = 0
        · subst hi; simp
        · simp [Function.update_of_ne hi]
  | succ p ih =>
      refine ⟨⟨Sum.inr false, p, t⟩, ⟨Sum.inr false, t (p + 1), Move.left, ?_, ?_, by simp⟩, ih⟩
      · have h0 : (t (p + 1)).2 = false := by simp [ht (p + 1)]
        show _ ∈ homingStep N (Sum.inr false) (t (p + 1))
        simp [homingStep, homeStep, h0]
      · refine config_eq rfl (by simp) ?_
        funext i
        by_cases hi : i = p + 1
        · subst hi; simp
        · simp [Function.update_of_ne hi]

/-- From an accepting state of `N` at the cell `p` the normalised machine walks home in `p + 1`
bump-free steps. -/
lemma reachesBF_enter {q : Q} (hq : q ∈ N.accept) (t : ℕ → Γ × Bool)
    (ht : ∀ i, (t i).2 = decide (i = 0)) (p : ℕ) :
    ReachesBF (homingMachine N) (p + 1) ⟨Sum.inl q, p, t⟩ ⟨Sum.inr true, 0, t⟩ := by
  cases p with
  | zero =>
      refine ⟨⟨Sum.inr true, 0, t⟩, ⟨Sum.inr true, t 0, Move.stay, ?_, ?_, by simp⟩, rfl⟩
      · have h0 : (t 0).2 = true := by simp [ht 0]
        show _ ∈ homingStep N (Sum.inl q) (t 0)
        exact Or.inr ⟨hq, by simp [homeStep, h0]⟩
      · refine config_eq rfl (by simp) ?_
        funext i
        by_cases hi : i = 0
        · subst hi; simp
        · simp [Function.update_of_ne hi]
  | succ p =>
      refine ⟨⟨Sum.inr false, p, t⟩, ⟨Sum.inr false, t (p + 1), Move.left, ?_, ?_, by simp⟩,
        reachesBF_walk N t ht p⟩
      · have h0 : (t (p + 1)).2 = false := by simp [ht (p + 1)]
        show _ ∈ homingStep N (Sum.inl q) (t (p + 1))
        exact Or.inr ⟨hq, by simp [homeStep, h0]⟩
      · refine config_eq rfl (by simp) ?_
        funext i
        by_cases hi : i = p + 1
        · subst hi; simp
        · simp [Function.update_of_ne hi]

/-- From an accepting configuration of `N` the normalised machine reaches its home configuration
in `head + 1` bump-free steps. -/
lemma reachesBF_home {c : Config Q Γ} (hacc : c.state ∈ N.accept) :
    ReachesBF (homingMachine N) (c.head + 1) (liftC c)
      ⟨Sum.inr true, 0, fun i => (c.tape i, decide (i = 0))⟩ :=
  reachesBF_enter N hacc (fun i => (c.tape i, decide (i = 0))) (fun _ => rfl) c.head


/-! ### From an accepting run of `N` to a homing bump-free run of `N⁺` -/

lemma initConfig_homingMachine {w : List Γ} (hw : w ≠ []) :
    (homingMachine N).initConfig (markInput N w) = liftC (N.initConfig w) := by
  refine config_eq rfl rfl ?_
  funext i
  simpa [NTM.initConfig, liftC, homingMachine] using markInput_getD N hw i

/-- The home configuration idles: it is a bump-free step to itself. -/
lemma stepBumpFree_home (t : ℕ → Γ × Bool) :
    StepBumpFree (homingMachine N) ⟨Sum.inr true, 0, t⟩ ⟨Sum.inr true, 0, t⟩ := by
  refine ⟨Sum.inr true, t 0, Move.stay, ?_, ?_, by simp⟩
  · show _ ∈ homingStep N (Sum.inr true) (t 0)
    simp [homingStep]
  · refine config_eq rfl (by simp) ?_
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [Function.update_of_ne hi]

/-- **The normalisation is complete**: if `N` accepts `w` within `K` steps, then the normalised
machine has a homing, bump-free accepting run of *exactly* `K'` steps for every `K' ≥ 2K + 1` —
the shape of run the encoding of Theorem 4.3.7 writes out. -/
theorem homingRunBumpFree_homingMachine {w : List Γ} {K K' : ℕ} (hw : w ≠ [])
    (hK' : 2 * K + 1 ≤ K') (hacc : N.AcceptsWithin w K) :
    HomingRunBumpFree (homingMachine N) (markInput N w) K' := by
  obtain ⟨n, hn, c, hc, hcacc⟩ := hacc
  have hhead : c.head ≤ n := by
    have := hc.head_le
    simpa [NTM.initConfig] using this
  have h₁ : ReachesBF (homingMachine N) n (liftC (N.initConfig w)) (liftC c) :=
    reachesBF_liftC N hc
  have h₂ := reachesBF_home N hcacc
  have h : ReachesBF (homingMachine N) (n + (c.head + 1))
      ((homingMachine N).initConfig (markInput N w))
      ⟨Sum.inr true, 0, fun i => (c.tape i, decide (i = 0))⟩ := by
    rw [initConfig_homingMachine N hw]
    exact h₁.trans h₂
  refine homingRunBumpFree_of_reachesBF h (by omega) (stepBumpFree_home N _) ?_ rfl
  simp [homingMachine]

/-! ### From an accepting run of `N⁺` back to one of `N` -/

lemma marked_of_step {c d : Config (Q ⊕ Bool) (Γ × Bool)}
    (hc : Marked c) (h : (homingMachine N).Step c d) : Marked d := by
  obtain ⟨q', x', m, hmem, rfl⟩ := h
  intro i
  by_cases hi : i = c.head
  · subst hi
    have hx : x'.2 = (c.tape c.head).2 :=
      tape_snd_of_mem_homingStep (N := N) (y := (q', x', m)) hmem
    simpa [hx] using hc c.head
  · simpa [Function.update_of_ne hi] using hc i

/-- **The normalisation is sound**: an accepting run of the normalised machine must pass through
an accepting state of `N`, so it exhibits an accepting run of `N` that is no longer. -/
lemma exists_accept_of_reaches_home {n : ℕ} {q : Q} {c d : Config (Q ⊕ Bool) (Γ × Bool)}
    (hinv : Marked c) (hc : c.state = Sum.inl q)
    (h : (homingMachine N).Reaches n c d) (hd : d.state = Sum.inr true) :
    ∃ m ≤ n, ∃ e, N.Reaches m (unliftC q c) e ∧ e.state ∈ N.accept := by
  induction n generalizing c q with
  | zero =>
      have : c = d := h
      rw [this, hd] at hc
      exact absurd hc (by simp)
  | succ n ih =>
      obtain ⟨x, hstep, hx⟩ := h
      obtain ⟨q', y', m, hmem, rfl⟩ := hstep
      rw [hc] at hmem
      rcases hmem with hsim | hhome
      · obtain ⟨q'', a', mv, hmemN, heq⟩ := hsim
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hq, hy, hm⟩ := heq
        subst hq; subst hy; subst hm
        have hmark : (c.tape c.head).2 = decide (c.head = 0) := hinv c.head
        have hstep' : (homingMachine N).Step c
            ⟨Sum.inl q'', (homeMove (c.tape c.head).2 mv).apply c.head,
              Function.update c.tape c.head (a', (c.tape c.head).2)⟩ := by
          refine ⟨Sum.inl q'', (a', (c.tape c.head).2),
            homeMove (c.tape c.head).2 mv, ?_, rfl⟩
          rw [hc]
          exact Or.inl ⟨q'', a', mv, hmemN, rfl⟩
        have hinv' : Marked ⟨Sum.inl q'', (homeMove (c.tape c.head).2 mv).apply c.head,
            Function.update c.tape c.head (a', (c.tape c.head).2)⟩ :=
          marked_of_step N hinv hstep'
        obtain ⟨m₀, hm₀, e, he, heacc⟩ := ih hinv' rfl hx
        refine ⟨m₀ + 1, by omega, e, ?_, heacc⟩
        refine ⟨unliftC q'' ⟨Sum.inl q'', (homeMove (c.tape c.head).2 mv).apply c.head,
            Function.update c.tape c.head (a', (c.tape c.head).2)⟩, ?_, he⟩
        refine ⟨q'', a', mv, hmemN, ?_⟩
        have hhd : (homeMove (c.tape c.head).2 mv).apply c.head = mv.apply c.head := by
          refine homeMove_apply ?_
          intro hb
          rw [hmark] at hb
          simpa using hb
        refine config_eq rfl ?_ ?_
        · simpa [unliftC] using hhd
        · funext i
          by_cases hi : i = c.head
          · subst hi; simp [unliftC]
          · simp [unliftC, Function.update_of_ne hi]
      · obtain ⟨hqacc, -⟩ := hhome
        exact ⟨0, by omega, unliftC q c, rfl, by simpa [unliftC] using hqacc⟩

/-- **Soundness of the normalisation.**  If the normalised machine accepts the marked input
within `M` steps then `N` accepts the input within `M` steps. -/
theorem acceptsWithin_of_homingMachine {w : List Γ} {M : ℕ} (hw : w ≠ [])
    (h : (homingMachine N).AcceptsWithin (markInput N w) M) : N.AcceptsWithin w M := by
  obtain ⟨n, hn, c, hc, hcacc⟩ := h
  rw [initConfig_homingMachine N hw] at hc
  have hd : c.state = Sum.inr true := by simpa [homingMachine] using hcacc
  obtain ⟨m, hm, e, he, heacc⟩ :=
    exists_accept_of_reaches_home N (marked_liftC (N.initConfig w)) rfl hc hd
  refine ⟨m, by omega, e, ?_, heacc⟩
  have : unliftC (N.initConfig w).state (liftC (N.initConfig w)) = N.initConfig w := by
    refine config_eq rfl rfl ?_
    funext i
    simp [unliftC, liftC]
  rwa [this] at he

/-! ### The encoded planning problem of the normalised machine -/

/-- **Completeness at the level of the planning problem**: if `N` accepts `w` within `K` steps
then the encoded problem of the *normalised* machine is solvable. -/
theorem solvable_problemFix_homingMachine {w : List Γ} {K K' : ℕ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ K) (hK' : 2 * K + 1 ≤ K') (hacc : N.AcceptsWithin w K) :
    (problemFix (homingMachine N) (markInput N w) K').Solvable := by
  have hw0 : w ≠ [] := by
    intro h; rw [h] at hw; simp at hw
  refine solvable_of_homingRunBumpFree (by omega) ?_ ?_
    (homingRunBumpFree_homingMachine N hw0 hK' hacc)
  · simpa using hw
  · simp only [markInput_length]
    omega

/-- **Soundness at the level of the planning problem**: a solution of the encoded problem of the
normalised machine exhibits an accepting run of `N`. -/
theorem acceptsWithin_of_solvable_homingMachine {w : List Γ} {K' : ℕ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ K') (hsol : (problemFix (homingMachine N) (markInput N w) K').Solvable) :
    N.AcceptsWithin w K' := by
  have hw0 : w ≠ [] := by
    intro h; rw [h] at hw; simp at hw
  refine acceptsWithin_of_homingMachine N hw0 ?_
  refine encodingSoundFix (N := homingMachine N) (w := markInput N w) (K := K') ?_ ?_ hsol
  · simpa using hw
  · simpa using hwK

/-- A machine is **clocked at `K`** on the input `w` if it cannot accept `w` at all without
accepting it within `K` steps.  This is the situation of the hardness argument, where `N` is a
machine that decides a language within its time bound. -/
def ClockedAt (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  ∀ n, N.AcceptsWithin w n → N.AcceptsWithin w K

/-- **The encoding of the normalised machine decides acceptance of the original one.**

For a machine that is clocked at `K` the encoded problem of the normalised machine `N⁺` on the
marked input `w⁺` with the bound `K' ≥ 2K + 1` is solvable **iff** `N` accepts `w` within `K`
steps.  This is the statement the source obtains by assuming, w.l.o.g., that an accepting machine
has a homing run of exactly `K` steps. -/
theorem solvable_problemFix_homingMachine_iff {w : List Γ} {K K' : ℕ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ K) (hK' : 2 * K + 1 ≤ K') (hclock : ClockedAt N w K) :
    (problemFix (homingMachine N) (markInput N w) K').Solvable ↔ N.AcceptsWithin w K := by
  refine ⟨fun hsol => hclock K' ?_, fun hacc => solvable_problemFix_homingMachine N hw hwK hK' hacc⟩
  exact acceptsWithin_of_solvable_homingMachine N hw (by omega) hsol

/-- The same statement in the exponential-time wording of the source: with the bound
`2 ^ (p + 2)(|w⁺|)` — note `|w⁺| = |w|` — the encoded problem of the normalised machine is
solvable exactly when `N` accepts `w` in time `2 ^ p(|w|)`. -/
theorem encodingCorrect_homingMachine {p : Polynomial ℕ} {w : List Γ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ 2 ^ p.eval w.length)
    (hclock : ClockedAt N w (2 ^ p.eval w.length)) :
    (problemFix (homingMachine N) (markInput N w)
        (2 ^ (p + Polynomial.C 2).eval (markInput N w).length)).Solvable ↔ N.AcceptsExp p w := by
  have heval : (p + Polynomial.C 2).eval (markInput N w).length = p.eval w.length + 2 := by
    simp [markInput_length]
  have hpow : (2 : ℕ) ^ (p + Polynomial.C 2).eval (markInput N w).length
      = 4 * 2 ^ p.eval w.length := by
    rw [heval, pow_add]
    ring
  have hone : 1 ≤ 2 ^ p.eval w.length := Nat.one_le_two_pow
  rw [hpow]
  exact solvable_problemFix_homingMachine_iff N hw hwK (by omega) hclock

/-! ### The normalisation repairs the counterexample

`HTN.TMEnc.idleMachine` — the machine without transitions, which accepts every input immediately
— is the counterexample that refutes the completeness statement for the encoding as it stands
(`HTN.TMEnc.not_encodingCompleteFix`): its encoded problem is unsolvable because the plan has to
spend the budget of the head counter on transitions.  Its *normalisation* accepts by walking
home, and the encoded problem of the normalised machine is solvable — so the normalisation is
exactly what the missing w.l.o.g. assumption of the source needs. -/

theorem solvable_homingMachine_idleMachine {w : List Bool} {K K' : ℕ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ K) (hK' : 2 * K + 1 ≤ K') :
    (problemFix (homingMachine idleMachine) (markInput idleMachine w) K').Solvable :=
  solvable_problemFix_homingMachine idleMachine hw hwK hK' (acceptsWithin_idleMachine w K)

/-! ### The size of the encoding of the normalised machine

The normalisation costs two states and doubles the alphabet, and it does not change the length
of the input, so the closed-form bound of `HTN.TMEnc.sizeOn_fullFragment_le_logFix` applies to
it verbatim: the encoded domain of the normalised machine is polynomial in the size of the
original machine, in the length of the input and in the *logarithm* of the time bound. -/

section Size

variable [Fintype Q] [Fintype Γ]

lemma card_states_homingMachine : Nat.card (Q ⊕ Bool) = Nat.card Q + 2 := by simp

lemma card_alphabet_homingMachine : Nat.card (Γ × Bool) = 2 * Nat.card Γ := by
  simp; ring

/-- **The encoded domain of the normalised machine is small**: the same closed-form bound as for
the machine itself, with two more states, twice the alphabet and the same input length — in
particular still polynomial in the size of the machine and logarithmic in the time bound. -/
theorem sizeOn_fullFragment_homingMachine_le (w : List Γ) (K' : ℕ) :
    (domainFix (homingMachine N) (markInput N w) K').sizeOn
        (fullFragmentFix (homingMachine N) (markInput N w) K') ≤
      sizeBound (Nat.card Q + 2) (2 * Nat.card Γ) w.length
        ((2 * Nat.log 2 K' + 2) + (2 * Nat.log 2 (K' + 1) + 2) + (2 * Nat.log 2 (K' + 2) + 2) +
          (2 * Nat.log 2 (K' - w.length) + 2)) := by
  have h := sizeOn_fullFragment_le_logFix (homingMachine N) (markInput N w) K'
  rwa [card_states_homingMachine (Q := Q), card_alphabet_homingMachine (Γ := Γ),
    markInput_length] at h

end Size

end TMEnc

end HTN
