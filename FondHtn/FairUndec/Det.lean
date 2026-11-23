import ComplexityTheory.Undec.TM.Reduce
/-!
# The simulating two-stack machine is deterministic; infinite runs and divergence

For the two-stack machine `HTN.Undec.Sim.simTSM` simulating a `TM0` machine:

* **`FOND.FU.simTSM_det`** — it is deterministic: in every control state the transitions read
  one stack and pop pairwise distinct symbols;
* **`FOND.FU.simTSM_inf_iff`** — it has an infinite run from the initial configuration iff the
  Turing machine diverges.  If the Turing machine halts, the two-stack machine reaches its
  accepting state (`HTN.Undec.Sim.halts_of_dom`), which has no transitions, and by determinism
  every run is a prefix of that one.  If it diverges, every Turing step is simulated by at least
  one step;
* **`FOND.FU.undecTSM_inf_iff`** — for the machine `HTN.Undec.undecTSM`: an infinite run from
  `([0], redStack n)` iff the universal partial recursive function diverges on `n`.
-/

namespace FOND

namespace FU

open HTN.Undec HTN.Undec.Sim Turing

/-- An infinite run of a two-stack machine. -/
def Inf (M : TSM) (c : Cfg) : Prop := ∃ f : ℕ → Cfg, f 0 = c ∧ ∀ i, M.Step (f i) (f (i + 1))

section Sim

open scoped Classical

variable {Γ : Type*} [Inhabited Γ] [Fintype Γ] {Λ : Type*} [Inhabited Λ]
variable {N : TM0.Machine Γ Λ} {S : Finset Λ} {q0 : Λ}

/-- Transitions of a list in which every transition pops its own symbol. -/
theorem uniq_map {l : List ℕ} {f : ℕ → Tr} (hf : ∀ x, (f x).pop = x)
    (hstk : ∀ x y, (f x).stk = (f y).stk) :
    ∀ t ∈ l.map f, ∀ t' ∈ l.map f, t.stk = t'.stk ∧ (t.pop = t'.pop → t = t') := by
  intro t ht t' ht'
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 ht'
  refine ⟨hstk x y, fun h => ?_⟩
  rw [hf, hf] at h; rw [h]

omit [Inhabited Γ] in
theorem uniq_cons {x : Tr} {g : Γ → Tr} (hx : x.pop = 0) (hg : ∀ c, (g c).pop = symCode c)
    (hstk : ∀ c, (g c).stk = x.stk) :
    ∀ t ∈ x :: (symList Γ).map g, ∀ t' ∈ x :: (symList Γ).map g,
      t.stk = t'.stk ∧ (t.pop = t'.pop → t = t') := by
  have key : ∀ t ∈ x :: (symList Γ).map g, t = x ∨ ∃ c, t = g c := by
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact Or.inl rfl
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 ht; exact Or.inr ⟨c, rfl⟩
  intro t ht t' ht'
  rcases key t ht with rfl | ⟨c, rfl⟩ <;> rcases key t' ht' with rfl | ⟨c', rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · refine ⟨(hstk c').symm, fun h => ?_⟩
    rw [hx, hg] at h; exact absurd h.symm (symCode_ne_zero c')
  · refine ⟨hstk c, fun h => ?_⟩
    rw [hx, hg] at h; exact absurd h (symCode_ne_zero c)
  · refine ⟨(hstk c).trans (hstk c').symm, fun h => ?_⟩
    rw [hg, hg] at h; rw [symCode_injective h]

/-- **The transitions of a control state read one stack and pop distinct symbols.** -/
theorem trsOf_uniq (s : St Γ Λ) :
    ∀ t ∈ trsOf N S q0 s, ∀ t' ∈ trsOf N S q0 s, t.stk = t'.stk ∧ (t.pop = t'.pop → t = t') := by
  cases s with
  | start => exact uniq_cons rfl (fun _ => rfl) (fun _ => rfl)
  | flush1 => exact uniq_cons rfl (fun _ => rfl) (fun _ => rfl)
  | flush2 => exact uniq_cons rfl (fun _ => rfl) (fun _ => rfl)
  | acc => simp [trsOf]
  | run q a =>
      rw [trsOf]
      match hN : N q a with
      | none => exact uniq_map (fun _ => rfl) (fun _ _ => rfl)
      | some (q', TM0.Stmt.write b) => exact uniq_map (fun _ => rfl) (fun _ _ => rfl)
      | some (q', TM0.Stmt.move Dir.right) => exact uniq_cons rfl (fun _ => rfl) (fun _ => rfl)
      | some (q', TM0.Stmt.move Dir.left) => exact uniq_cons rfl (fun _ => rfl) (fun _ => rfl)
  | pl q y b => exact uniq_map (fun _ => rfl) (fun _ _ => rfl)
  | pr q y b => exact uniq_map (fun _ => rfl) (fun _ _ => rfl)

theorem mem_trsOf_src {t : Tr} (ht : t ∈ (simTSM N S q0).trans) :
    ∃ s, StOk S s ∧ t ∈ trsOf N S q0 s ∧ t.src = stCode S s := by
  obtain ⟨s, hs, ht'⟩ := List.mem_flatMap.1 ht
  exact ⟨s, stOk_of_mem_allSt hs, ht', src_of_mem_trsOf ht'⟩

/-- **The simulating machine is deterministic.** -/
theorem simTSM_det {c c₁ c₂ : Cfg} (h₁ : (simTSM N S q0).Step c c₁)
    (h₂ : (simTSM N S q0).Step c c₂) : c₁ = c₂ := by
  obtain ⟨t, ht, hs1, h1⟩ := h₁
  obtain ⟨t', ht', hs2, h2⟩ := h₂
  obtain ⟨s, hsok, hts, hsrc⟩ := mem_trsOf_src ht
  obtain ⟨s', hsok', hts', hsrc'⟩ := mem_trsOf_src ht'
  have hss : s' = s := stCode_ne_of_ne hsok' hsok (hsrc'.symm.trans (hs2.symm.trans (hs1.trans hsrc)))
  rw [hss] at hts'
  obtain ⟨hstk, hpop⟩ := trsOf_uniq s t hts t' hts'
  rcases h1 with ⟨hb, r, hr, rfl⟩ | ⟨hb, r, hr, rfl⟩ <;>
    rcases h2 with ⟨hb', r', hr', rfl⟩ | ⟨hb', r', hr', rfl⟩
  · rw [hr] at hr'
    obtain ⟨e1, rfl⟩ := List.cons.inj hr'
    rw [hpop e1]
  · rw [hb, hb'] at hstk; exact absurd hstk (by simp)
  · rw [hb, hb'] at hstk; exact absurd hstk (by simp)
  · rw [hr] at hr'
    obtain ⟨e1, rfl⟩ := List.cons.inj hr'
    rw [hpop e1]

/-- The accepting state has no transitions. -/
theorem simTSM_acc_stuck {s1 s2 : List ℕ} {c : Cfg} (h : (simTSM N S q0).Step ⟨3, s1, s2⟩ c) :
    False := by
  obtain ⟨t, ht, hsrc, -⟩ := h
  obtain ⟨s, hsok, hts, hsrc'⟩ := mem_trsOf_src ht
  have : s = St.acc := stCode_ne_of_ne hsok trivial (hsrc'.symm.trans hsrc.symm)
  subst this
  simp [trsOf] at hts

/-- A halting machine has no infinite run. -/
theorem not_inf_of_reaches {c : Cfg} (h : (simTSM N S q0).Reaches c ⟨3, [], []⟩) :
    ¬ Inf (simTSM N S q0) c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rintro ⟨f, hf0, hf⟩
    have := hf 0
    rw [hf0] at this
    exact simTSM_acc_stuck this
  | head hstep _ ih =>
    rintro ⟨f, hf0, hf⟩
    have h1 := hf 0
    rw [hf0] at h1
    obtain rfl := simTSM_det hstep h1
    exact ih ⟨fun i => f (i + 1), rfl, fun i => hf (i + 1)⟩

/-- The configurations that still reach the simulation of a reachable Turing configuration. -/
def Good (N : TM0.Machine Γ Λ) (S : Finset Λ) (q0 : Λ) (l : List Γ) (c : Cfg) : Prop :=
  ∃ q a L R, q ∈ S ∧
    Relation.ReflTransGen (fun x y => y ∈ TM0.step N x) (⟨q0, Tape.mk₁ l⟩ : TM0.Cfg Γ Λ)
      ⟨q, tapeOf a L R⟩ ∧
    (simTSM N S q0).Reaches c ⟨stCode S (St.run q a), encL L, encL R⟩

/-- **Divergence**: every reachable configuration of a diverging machine steps. -/
theorem step_of_div {l : List Γ} (hdiv : ¬ (Turing.eval (TM0.step N) ⟨q0, Tape.mk₁ l⟩).Dom)
    {x : TM0.Cfg Γ Λ}
    (hx : Relation.ReflTransGen (fun x y => y ∈ TM0.step N x) ⟨q0, Tape.mk₁ l⟩ x) :
    ∃ y, TM0.step N x = some y := by
  cases h : TM0.step N x with
  | none =>
    exfalso
    apply hdiv
    exact Part.dom_iff_mem.2 ⟨x, Turing.mem_eval.2 ⟨hx, h⟩⟩
  | some y => exact ⟨y, rfl⟩

theorem good_step
    (hcl : ∀ {q : Λ} {a : Γ} {q' : Λ} {st : TM0.Stmt Γ}, (q', st) ∈ N q a → q ∈ S → q' ∈ S)
    {l : List Γ} (hdiv : ¬ (Turing.eval (TM0.step N) ⟨q0, Tape.mk₁ l⟩).Dom) {c : Cfg}
    (hc : Good N S q0 l c) : ∃ c', (simTSM N S q0).Step c c' ∧ Good N S q0 l c' := by
  obtain ⟨q, a, L, R, hq, hreach, hc⟩ := hc
  rcases Relation.ReflTransGen.cases_head hc with rfl | ⟨c₁, h1, h2⟩
  · -- at the simulation of a Turing configuration: the Turing machine steps
    obtain ⟨y, hy⟩ := step_of_div hdiv hreach
    have hry : Relation.ReflTransGen (fun x y => y ∈ TM0.step N x)
        (⟨q0, Tape.mk₁ l⟩ : TM0.Cfg Γ Λ) y := hreach.tail hy
    have hy' := hy
    simp only [TM0.step, Option.map_eq_some_iff] at hy'
    obtain ⟨⟨q', st⟩, hN, hy₁⟩ := hy'
    have hNqa : N q a = some (q', st) := by simpa [tapeOf] using hN
    have hq' : q' ∈ S := hcl (by rw [hNqa]; rfl) hq
    cases st with
    | write bb =>
      have e : y = ⟨q', tapeOf bb L R⟩ := by
        rw [← hy₁]; exact congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_write bb a L R)
      rw [e] at hry
      exact ⟨_, step_run_write (q0 := q0) hq hNqa L (encL R), q', bb, L, R, hq', hry,
        Relation.ReflTransGen.refl⟩
    | move d =>
      cases d with
      | right =>
        have e : y = ⟨q', tapeOf R.headI (a :: L) R.tail⟩ := by
          rw [← hy₁]; exact congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_move_right a L R)
        rw [e] at hry
        exact ⟨_, step_run_right (q0 := q0) hq hNqa L R, q', R.headI, a :: L, R.tail, hq', hry,
          Relation.ReflTransGen.single (step_pl (q0 := q0) (N := N) hq' L (encL R.tail))⟩
      | left =>
        have e : y = ⟨q', tapeOf L.headI L.tail (a :: R)⟩ := by
          rw [← hy₁]; exact congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_move_left a L R)
        rw [e] at hry
        exact ⟨_, step_run_left (q0 := q0) hq hNqa L R, q', L.headI, L.tail, a :: R, hq', hry,
          Relation.ReflTransGen.single (step_pr (q0 := q0) (N := N) hq' (encL L.tail) R)⟩
  · exact ⟨c₁, h1, q, a, L, R, hq, hreach, h2⟩

/-- **Infinite runs are divergence.** -/
theorem simTSM_inf_iff
    (hcl : ∀ {q : Λ} {a : Γ} {q' : Λ} {st : TM0.Stmt Γ}, (q', st) ∈ N q a → q ∈ S → q' ∈ S)
    (hq0 : q0 ∈ S) (l : List Γ) :
    Inf (simTSM N S q0) ⟨0, encL ([] : List Γ), encL l⟩ ↔
      ¬ (Turing.eval (TM0.step N) ⟨q0, Tape.mk₁ l⟩).Dom := by
  constructor
  · intro hinf hdom
    exact not_inf_of_reaches (halts_of_dom hcl hq0 l hdom) hinf
  · intro hdiv
    have h0 : Good N S q0 l ⟨0, encL ([] : List Γ), encL l⟩ :=
      ⟨q0, l.headI, [], l.tail, hq0, by rw [← tapeOf_mk₁], start_reaches l⟩
    let g : ℕ → {c // Good N S q0 l c} := fun n =>
      Nat.rec ⟨_, h0⟩ (fun _ p => ⟨(good_step hcl hdiv p.2).choose,
        (good_step hcl hdiv p.2).choose_spec.2⟩) n
    exact ⟨fun n => (g n).1, rfl, fun n => (good_step hcl hdiv (g n).2).choose_spec.1⟩

end Sim

open HTN.Undec.TMChain Turing.PartrecToTM2 in
/-- **The undecidable two-stack machine runs forever iff the universal function diverges.** -/
theorem undecTSM_inf_iff (n : ℕ) :
    Inf undecTSM ⟨0, [0], redStack n⟩ ↔ ¬ (univFun n).Dom := by
  have h1 : encL ([] : List Gam1) = [0] := rfl
  rw [undecTSM, redStack_eq, ← h1,
    simTSM_inf_iff (supports univCode) (start_mem_supp univCode) (initTape [n]),
    dom_chain univCode [n], univCode_dom]

/-- **Recurrence**: an infinite run from `c` that enters a state satisfying `tk` infinitely
often. -/
def Rec (tk : ℕ → Bool) (M : TSM) (c : Cfg) : Prop :=
  ∃ f : ℕ → Cfg, f 0 = c ∧ (∀ i, M.Step (f i) (f (i + 1))) ∧ ∀ i, ∃ j, i ≤ j ∧ tk (f (j + 1)).st = true

/-- Recurrence for the predicate that always holds is an infinite run. -/
theorem rec_true_iff {M : TSM} {c : Cfg} : Rec (fun _ => true) M c ↔ Inf M c :=
  ⟨fun ⟨f, h0, hs, _⟩ => ⟨f, h0, hs⟩, fun ⟨f, h0, hs⟩ => ⟨f, h0, hs, fun i => ⟨i, le_rfl, rfl⟩⟩⟩

end FU

end FOND
