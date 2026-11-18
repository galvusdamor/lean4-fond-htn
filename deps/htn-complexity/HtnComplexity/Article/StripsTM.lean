import HtnComplexity.Article.Strips
import ComplexityTheory.Machine.PSpace
/-!
# Turing machines in bounded space as STRIPS problems (Bylander)

The classical encoding of a space-bounded Turing machine run as a STRIPS problem.  For a machine
with states `0, …, k - 1`, transitions `trs`, accepting states `accs`, initial state `q₀`, an
input `w` and a space bound `S`, the facts are

* `q` — the machine is in state `q` (`q < k`);
* `k + i` — the head is on cell `i` (`i < S`);
* `celF i a = k + S + 3 i + code a` — cell `i` holds the symbol `a`;
* `accF = k + 4 S` — an accepting state has been reached;

and the actions are one action per transition and head position (moving the head within the
cells `0, …, S - 1`), and one action per accepting state adding `accF`.  The action names are
their positions in the list.

`HTN.Article.stripsTM_solvable_iff`: the problem has a plan iff the machine accepts `w` within the
space `S` (`TM.NTM.AcceptsInSpace`).
-/

namespace HTN

namespace Article

open TM

/-- The body of an action: `prec⁺`, `prec⁻`, `eff⁺`, `eff⁻`. -/
abbrev ABody : Type := List ℕ × List ℕ × List ℕ × List ℕ

/-- Naming action bodies by their positions, starting at `o`. -/
def namedFrom : ℕ → List ABody → List ActDesc
  | _, [] => []
  | o, b :: bs => (o, b) :: namedFrom (o + 1) bs

theorem find_namedFrom (j : ℕ) : ∀ (bs : List ABody) (o : ℕ),
    (namedFrom o bs).find? (fun x => x.name == j) =
      if o ≤ j then (bs[j - o]?).map fun b => (j, b) else none := by
  intro bs
  induction bs with
  | nil => intro o; simp [namedFrom]
  | cons b bs ih =>
    intro o
    rw [namedFrom, List.find?_cons]
    by_cases hj : o = j
    · subst hj; simp [ActDesc.name]
    · have : (ActDesc.name ((o, b) : ActDesc) == j) = false := by simp [ActDesc.name, hj]
      rw [this]
      simp only
      rw [ih]
      by_cases hoj : o ≤ j
      · rw [if_pos (by omega), if_pos hoj, show j - o = (j - (o + 1)) + 1 by omega]
        simp
      · rw [if_neg (by omega), if_neg hoj]

theorem map_name_namedFrom : ∀ (bs : List ABody) (o : ℕ),
    (namedFrom o bs).map ActDesc.name = (List.range bs.length).map (· + o) := by
  intro bs
  induction bs with
  | nil => intro o; rfl
  | cons b bs ih =>
    intro o
    simp only [namedFrom, List.map_cons, ActDesc.name, ih, List.length_cons, List.range_succ_eq_map,
      List.map_map]
    congr 1
    · omega
    · exact List.map_congr_left fun i _ => by simp; omega

/-- The code of a tape symbol. -/
def symCode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

theorem symCode_lt (a : Option Bool) : symCode a < 3 := by
  rcases a with _ | _ | _ <;> simp [symCode]

theorem symCode_inj {a b : Option Bool} (h : symCode a = symCode b) : a = b := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [symCode]

/-- A transition: state, symbol read, new state, symbol written, move (`0` left, `1` stay,
`2` right). -/
abbrev TTr : Type := ℕ × Option Bool × ℕ × Option Bool × ℕ

/-- The code of a move. -/
def moveCode : Move → ℕ
  | .left => 0
  | .stay => 1
  | .right => 2

/-- The head position after a coded move. -/
def mvApply (m i : ℕ) : ℕ := if m = 0 then i - 1 else if m = 1 then i else i + 1

theorem mvApply_moveCode (m : Move) (i : ℕ) : mvApply (moveCode m) i = m.apply i := by
  cases m <;> rfl

section Enc

variable (k S : ℕ)

/-- The fact "cell `i` holds `a`". -/
def celF (i : ℕ) (a : Option Bool) : ℕ := k + S + 3 * i + symCode a

/-- The fact "an accepting state has been reached". -/
def accF : ℕ := k + S + 3 * S

/-- The action of the transition `tr` with the head on cell `i`. -/
def trAct (tr : TTr) (i : ℕ) : ABody :=
  ([tr.1, k + i, celF k S i tr.2.1], [], [tr.2.2.1, k + mvApply tr.2.2.2.2 i, celF k S i tr.2.2.2.1],
    [tr.1, k + i, celF k S i tr.2.1])

/-- The action of the accepting state `q`. -/
def accAct (q : ℕ) : ABody := ([q], [], [accF k S], [])

/-- All action bodies. -/
def tmBodies (trs : List TTr) (accs : List ℕ) : List ABody :=
  trs.flatMap (fun tr => ((List.range S).filter fun i => decide (mvApply tr.2.2.2.2 i < S)).map
    (trAct k S tr)) ++ accs.map (accAct k S)

/-- **The STRIPS problem of a machine run on `w` in space `S`.** -/
def stripsTM (trs : List TTr) (accs : List ℕ) (q₀ : ℕ) (w : List (Option Bool)) : StripsDesc :=
  (namedFrom 0 (tmBodies k S trs accs),
    [q₀, k + 0] ++ (List.range S).map (fun i => celF k S i (w.getD i none)), [accF k S], [])

/-- The facts of a configuration. -/
def encS (q h : ℕ) (tape : ℕ → Option Bool) : Set ℕ :=
  {f | f = q ∨ f = k + h ∨ ∃ i < S, f = celF k S i (tape i)}

theorem celF_inj {i j : ℕ} {a b : Option Bool} (h : celF k S i a = celF k S j b) : i = j ∧ a = b := by
  unfold celF at h
  have ha := symCode_lt a
  have hb := symCode_lt b
  have hij : i = j := by omega
  subst hij
  exact ⟨rfl, symCode_inj (by omega)⟩

end Enc

/-! ### The actions of the problem -/

section Sem

variable {k S : ℕ} {trs : List TTr} {accs : List ℕ} {q₀ : ℕ} {w : List (Option Bool)}

/-- The action of a body. -/
def bodyAct (b : ABody) : Action ℕ := ActDesc.toAction ((0, b) : ActDesc)

theorem δ_stripsTM (j : ℕ) :
    (stripsTM k S trs accs q₀ w).toProbDesc.δ j =
      match (tmBodies k S trs accs)[j]? with
      | some b => bodyAct b
      | none => ⟨∅, ∅, ∅, ∅⟩ := by
  unfold ProbDesc.δ
  simp only [StripsDesc.toProbDesc, ProbDesc.actions, StripsDesc.actions, stripsTM]
  rw [find_namedFrom j _ 0, if_pos (Nat.zero_le _), Nat.sub_zero]
  rcases (tmBodies k S trs accs)[j]? with _ | b
  · rfl
  · rfl

theorem declared_stripsTM {j : ℕ} :
    (stripsTM k S trs accs q₀ w).toProbDesc.Declared j ↔ j < (tmBodies k S trs accs).length := by
  unfold ProbDesc.Declared
  simp only [StripsDesc.toProbDesc, ProbDesc.actions, StripsDesc.actions, stripsTM]
  rw [map_name_namedFrom]
  simp

theorem mem_tmBodies {b : ABody} :
    b ∈ tmBodies k S trs accs ↔
      (∃ tr ∈ trs, ∃ i < S, mvApply tr.2.2.2.2 i < S ∧ b = trAct k S tr i) ∨
        ∃ q ∈ accs, b = accAct k S q := by
  unfold tmBodies
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro (⟨tr, htr, i, ⟨hi, hm⟩, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact Or.inl ⟨tr, htr, i, hi, hm, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩
  · rintro (⟨tr, htr, i, hi, hm, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact Or.inl ⟨tr, htr, i, ⟨hi, hm⟩, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩

/-! ### Configurations as states -/

variable (k S)

theorem mem_encS {q h : ℕ} {tape : ℕ → Option Bool} {f : ℕ} :
    f ∈ encS k S q h tape ↔ f = q ∨ f = k + h ∨ ∃ i < S, f = celF k S i (tape i) := Iff.rfl

theorem accF_not_mem {q h : ℕ} {tape : ℕ → Option Bool} (hq : q < k) (hh : h < S) :
    accF k S ∉ encS k S q h tape := by
  rintro (h1 | h1 | ⟨i, hi, h1⟩)
  · unfold accF at h1; omega
  · unfold accF at h1; omega
  · unfold accF celF at h1; have := symCode_lt (tape i); omega

variable {k S}

/-- **An applicable transition action is a step of the machine.** -/
theorem trAct_applicable {tr : TTr} {i q h : ℕ} {tape : ℕ → Option Bool} (htr : tr.1 < k)
    (hq : q < k) (hh : h < S) (hi : i < S)
    (happ : (bodyAct (trAct k S tr i)).Applicable (encS k S q h tape)) :
    tr.1 = q ∧ i = h ∧ tr.2.1 = tape h := by
  obtain ⟨hpre, -⟩ := happ
  have h1 : tr.1 ∈ encS k S q h tape := hpre (by simp [bodyAct, ActDesc.toAction, trAct])
  have h2 : k + i ∈ encS k S q h tape := hpre (by simp [bodyAct, ActDesc.toAction, trAct])
  have h3 : celF k S i tr.2.1 ∈ encS k S q h tape := hpre (by simp [bodyAct, ActDesc.toAction, trAct])
  have e1 : tr.1 = q := by
    rcases h1 with h1 | h1 | ⟨j, hj, h1⟩
    · exact h1
    · omega
    · unfold celF at h1; omega
  have e2 : i = h := by
    rcases h2 with h2 | h2 | ⟨j, hj, h2⟩
    · omega
    · omega
    · unfold celF at h2; omega
  subst e2
  refine ⟨e1, rfl, ?_⟩
  rcases h3 with h3 | h3 | ⟨j, hj, h3⟩
  · unfold celF at h3; omega
  · unfold celF at h3; omega
  · obtain ⟨rfl, e⟩ := celF_inj k S h3
    exact e

/-- **Applying a transition action moves the configuration.** -/
theorem trAct_apply {tr : TTr} {h : ℕ} {tape : ℕ → Option Bool} (htr : tr.1 < k) (htr' : tr.2.2.1 < k)
    (hh : h < S) (hm : mvApply tr.2.2.2.2 h < S) (ha : tr.2.1 = tape h) :
    (bodyAct (trAct k S tr h)).apply (encS k S tr.1 h tape) =
      encS k S tr.2.2.1 (mvApply tr.2.2.2.2 h) (Function.update tape h tr.2.2.2.1) := by
  ext f
  simp only [bodyAct, ActDesc.toAction, trAct, Action.apply, Set.mem_union, Set.mem_diff,
    Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, mem_encS]
  constructor
  · rintro (⟨h1, h2⟩ | h2)
    · push_neg at h2
      obtain ⟨n1, n2, n3⟩ := h2
      rcases h1 with h1 | h1 | ⟨j, hj, rfl⟩
      · exact absurd h1 n1
      · exact absurd h1 n2
      · right; right
        refine ⟨j, hj, ?_⟩
        by_cases hjh : j = h
        · subst hjh; rw [← ha] at n3; exact absurd rfl n3
        · rw [Function.update_of_ne hjh]
    · rcases h2 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨h, hh, by rw [Function.update_self]⟩)
  · rintro (rfl | rfl | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · by_cases hjh : j = h
      · subst hjh; rw [Function.update_self]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [Function.update_of_ne hjh]
        refine Or.inl ⟨Or.inr (Or.inr ⟨j, hj, rfl⟩), ?_⟩
        rintro (e | e | e)
        · unfold celF at e; omega
        · unfold celF at e; omega
        · exact hjh (celF_inj k S e).1

end Sem

/-! ### The problem has a plan iff the machine accepts -/

section Machine

variable {k S : ℕ} (M : NTM (Fin k) (Option Bool)) {trs : List TTr} {accs : List ℕ} {q₀ : ℕ}
  {w : List (Option Bool)}
  (hT1 : ∀ tr ∈ trs, ∃ (hq : tr.1 < k) (hq' : tr.2.2.1 < k) (m : Move), tr.2.2.2.2 = moveCode m ∧
    ((⟨tr.2.2.1, hq'⟩ : Fin k), tr.2.2.2.1, m) ∈ M.step ⟨tr.1, hq⟩ tr.2.1)
  (hT2 : ∀ (q : Fin k) a (q' : Fin k) a' m, (q', a', m) ∈ M.step q a →
    (q.val, a, q'.val, a', moveCode m) ∈ trs)
  (hA1 : ∀ q ∈ accs, ∃ h : q < k, (⟨q, h⟩ : Fin k) ∈ M.accept)
  (hA2 : ∀ q ∈ M.accept, q.val ∈ accs)

theorem run_cons {π : List ℕ} {a : ℕ} {s s' : Set ℕ} :
    (stripsTM k S trs accs q₀ w).toProbDesc.toProblem.Run (a :: π) s s' ↔
      ((stripsTM k S trs accs q₀ w).toProbDesc.δ a).Applicable s ∧
        (stripsTM k S trs accs q₀ w).toProbDesc.toProblem.Run π
          (((stripsTM k S trs accs q₀ w).toProbDesc.δ a).apply s) s' := Iff.rfl

include hT1 hA1 in
/-- **Soundness**: a plan reaching `accF` comes from an accepting run within the space. -/
theorem stripsTM_sound : ∀ (π : List ℕ) (c : Config (Fin k) (Option Bool)) (sf : Set ℕ),
    c.head < S → (∀ a ∈ π, (stripsTM k S trs accs q₀ w).toProbDesc.Declared a) →
    (stripsTM k S trs accs q₀ w).toProbDesc.toProblem.Run π (encS k S c.state.val c.head c.tape) sf →
    accF k S ∈ sf → ∃ n c', M.ReachesSpace S n c c' ∧ c'.state ∈ M.accept := by
  intro π
  induction π with
  | nil =>
    intro c sf hh _ hr hacc
    obtain rfl : sf = _ := hr
    exact absurd hacc (accF_not_mem k S c.state.2 hh)
  | cons a π ih =>
    intro c sf hh hdec hr hacc
    rw [run_cons] at hr
    obtain ⟨happ, hr⟩ := hr
    have ha := (declared_stripsTM).1 (hdec a (by simp))
    obtain ⟨b, hb⟩ : ∃ b, (tmBodies k S trs accs)[a]? = some b := ⟨_, List.getElem?_eq_getElem ha⟩
    have hbm : b ∈ tmBodies k S trs accs := List.mem_of_getElem? hb
    rw [δ_stripsTM, hb] at happ hr
    simp only at happ hr
    rcases (mem_tmBodies).1 hbm with ⟨tr, htr, i, hi, hm, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨hq1, hq2, mv, hmv, hstep⟩ := hT1 tr htr
      obtain ⟨e1, rfl, e3⟩ := trAct_applicable hq1 c.state.2 hh hi happ
      rw [← e1, trAct_apply hq1 hq2 hh hm e3] at hr
      rw [hmv, mvApply_moveCode] at hr hm
      set c₁ : Config (Fin k) (Option Bool) := ⟨⟨tr.2.2.1, hq2⟩, mv.apply c.head,
        Function.update c.tape c.head tr.2.2.2.1⟩
      obtain ⟨n, c', hr', hc'⟩ := ih c₁ sf hm (fun a ha => hdec a (by simp [ha])) hr hacc
      have hcs : (⟨tr.1, hq1⟩ : Fin k) = c.state := Fin.ext e1
      rw [hcs, e3] at hstep
      exact ⟨n + 1, c', ⟨hh, c₁, ⟨_, _, _, hstep, rfl⟩, hr'⟩, hc'⟩
    · obtain ⟨hqk, hqa⟩ := hA1 q hq
      have hmem : q ∈ encS k S c.state.val c.head c.tape :=
        happ.1 (by simp [bodyAct, ActDesc.toAction, accAct])
      have e : q = c.state.val := by
        rcases hmem with h1 | h1 | ⟨j, hj, h1⟩
        · exact h1
        · omega
        · unfold celF at h1; omega
      have hcs : (⟨q, hqk⟩ : Fin k) = c.state := Fin.ext e
      rw [hcs] at hqa
      exact ⟨0, c, ⟨rfl, hh⟩, hqa⟩

include hT2 hA2 in
/-- **Completeness**: an accepting run within the space gives a plan reaching `accF`. -/
theorem stripsTM_complete : ∀ (n : ℕ) (c c' : Config (Fin k) (Option Bool)),
    M.ReachesSpace S n c c' → c'.state ∈ M.accept →
    ∃ π sf, (∀ a ∈ π, (stripsTM k S trs accs q₀ w).toProbDesc.Declared a) ∧
      (stripsTM k S trs accs q₀ w).toProbDesc.toProblem.Run π (encS k S c.state.val c.head c.tape) sf ∧
      accF k S ∈ sf := by
  intro n
  induction n with
  | zero =>
    intro c c' hr hacc
    obtain ⟨rfl, hh⟩ := hr
    have hmem : accAct k S c.state.val ∈ tmBodies k S trs accs :=
      (mem_tmBodies).2 (Or.inr ⟨_, hA2 _ hacc, rfl⟩)
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hmem
    refine ⟨[j], (bodyAct (accAct k S c.state.val)).apply (encS k S c.state.val c.head c.tape),
      fun a ha => ?_, ?_, ?_⟩
    · simp at ha; subst ha; exact (declared_stripsTM).2 hj
    · rw [run_cons, δ_stripsTM, List.getElem?_eq_getElem hj, hjb]
      refine ⟨⟨fun f hf => ?_, by simp [bodyAct, ActDesc.toAction, accAct]⟩, rfl⟩
      simp [bodyAct, ActDesc.toAction, accAct] at hf
      exact Or.inl hf
    · simp [bodyAct, ActDesc.toAction, accAct, Action.apply]
  | succ n ih =>
    intro c c' hr hacc
    obtain ⟨hh, d, ⟨q', a', m, hstep, rfl⟩, hr'⟩ := hr
    have hdh : m.apply c.head < S := NTM.ReachesSpace.head_lt M hr'
    obtain ⟨π, sf, hdec, hrun, hsf⟩ := ih _ c' hr' hacc
    have hmem : trAct k S (c.state.val, c.tape c.head, q'.val, a', moveCode m) c.head ∈
        tmBodies k S trs accs :=
      (mem_tmBodies).2 (Or.inl ⟨_, hT2 _ _ _ _ _ hstep, c.head, hh, by
        simp only [mvApply_moveCode]; exact hdh, rfl⟩)
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hmem
    refine ⟨j :: π, sf, fun a ha => ?_, ?_, hsf⟩
    · simp at ha
      rcases ha with rfl | ha
      · exact (declared_stripsTM).2 hj
      · exact hdec a ha
    · rw [run_cons, δ_stripsTM, List.getElem?_eq_getElem hj, hjb]
      simp only
      refine ⟨⟨fun f hf => ?_, by simp [bodyAct, ActDesc.toAction, trAct]⟩, ?_⟩
      · simp [bodyAct, ActDesc.toAction, trAct] at hf
        rcases hf with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨c.head, hh, rfl⟩)
      · rw [trAct_apply (tr := (c.state.val, c.tape c.head, q'.val, a', moveCode m)) c.state.2 q'.2 hh
          (by simp only [mvApply_moveCode]; exact hdh) rfl]
        simp only [mvApply_moveCode]
        exact hrun

/-- The initial state of the problem is the initial configuration. -/
theorem init_stripsTM (hS : 0 < S) :
    {f | f ∈ (stripsTM k S trs accs q₀ w).init} = encS k S q₀ 0 (fun i => w.getD i none) := by
  ext f
  simp only [StripsDesc.init, stripsTM, Set.mem_setOf_eq, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map, List.mem_range, mem_encS]
  constructor
  · rintro ((rfl | rfl) | ⟨i, hi, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)
  · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨i, hi, rfl⟩

include hT1 hT2 hA1 hA2 in
/-- **Bylander's encoding is correct**: the STRIPS problem of a machine run has a plan iff the
machine accepts the input within the space bound. -/
theorem stripsTM_solvable_iff (hS : 0 < S) (hblank : M.blank = none) :
    (stripsTM k S trs accs M.init.val w).Solvable ↔ M.AcceptsInSpace w S := by
  have hinit : M.initConfig w = ⟨M.init, 0, fun i => w.getD i none⟩ := by
    simp [NTM.initConfig, hblank]
  constructor
  · rintro ⟨π, hdec, s, hrun, hg⟩
    rw [init_stripsTM hS] at hrun
    have hacc : accF k S ∈ s := hg.1 (by simp [StripsDesc.toProbDesc, ProbDesc.toProblem,
      ProbDesc.goalPos, StripsDesc.goalPos, stripsTM])
    obtain ⟨n, c', hr, hc'⟩ := stripsTM_sound M hT1 hA1 π ⟨M.init, 0, fun i => w.getD i none⟩ s hS hdec
      hrun hacc
    exact ⟨n, c', by rw [hinit]; exact hr, hc'⟩
  · rintro ⟨n, c', hr, hc'⟩
    rw [hinit] at hr
    obtain ⟨π, sf, hdec, hrun, hsf⟩ := stripsTM_complete M hT2 hA2 n _ c' hr hc'
    refine ⟨π, hdec, sf, ?_, ?_, ?_⟩
    · rw [init_stripsTM hS]; exact hrun
    · intro f hf
      simp [StripsDesc.toProbDesc, ProbDesc.toProblem, ProbDesc.goalPos, StripsDesc.goalPos,
        stripsTM] at hf
      rw [hf]; exact hsf
    · simp [StripsDesc.toProbDesc, ProbDesc.toProblem, ProbDesc.goalNeg, StripsDesc.goalNeg, stripsTM]

end Machine

end Article

end HTN
