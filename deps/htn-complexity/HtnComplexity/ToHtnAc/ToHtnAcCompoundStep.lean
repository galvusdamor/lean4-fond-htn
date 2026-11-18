import HtnComplexity.ToHtnAc.ToHtnAcComplete
/-!
# A compound proof step proves exactly one proof tuple

This is the companion of `HtnComplexity/ToHtnAc/ToHtnAcPrimStep.lean` for the *compound* shape of a
proof step of the HTN-AC compilation (`HtnComplexity/ToHtnAc/ToHtnAcTupleShape.lean`).  A compound
step for a method `c ↦ x y` of the source domain runs

```
lock ; SEL¹ ; SEL² ; SEL³ ; (ask_R … wait_R) ; EQ^{1,4} ; EQ^{2,5} ; preC x ;
       (ask_R … wait_R) ; EQ^{2,4} ; EQ^{3,5} ; preC y ; setC c ; (ask_W … wait_W)^w ; unlock
```

(the copies are numbered `0 … 4` in the formalisation), where the two read handshakes are
answered by the read phases of two memory cells, each of which installs the triple it latched
into the copies `3`, `4` and into the stored task name (`HTN.ToAc.readPhase_spec`).

The point of this file is the *soundness* direction: whatever the two cells deliver, the
comparisons `EQ` and the two `preC` tests force the delivered triples to be
`(S, x, S'')` and `(S'', y, S')` for the very states the step guessed, so the triple
`(S, c, S')` the step then offers to a memory cell is derivable by the `two` rule of the
proof-tuple calculus of `HtnPlanning/Core/ProofTuples.lean` from the two delivered ones:

* `HTN.ToAc.compoundStep_matches` — the matching of the two delivered triples with the guesses;
* `HTN.ToAc.compoundStep_provable` — the resulting derivation step, the counterpart of
  `HTN.ToAc.primStep_provable`.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### An auxiliary fact about the read phase -/

/-- **After a read phase the stored task name is exactly the one of the answering cell.**  The
cell restores its own task name with `setC`, which deletes every other task fact. -/
lemma task_mem_transitionSeq_readPhase_iff {S S' : Set F} {t t' : A ⊕ C}
    {s : Set (AcFact F A C)} :
    (AcFact.task t' : AcFact F A C) ∈
      (domain D vars bound).transitionSeq (readPhase S S' t vars) s ↔ t' = t := by
  classical
  rw [readPhase, memRead]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    ActionModel.transitionSeq_nil]
  rw [mem_transition_waitA, mem_transition_doneA,
    unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (f := (AcFact.task t' : AcFact F A C)) (fun w _ => ⟨by simp, by simp⟩),
    unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (f := (AcFact.task t' : AcFact F A C)) (fun w _ => ⟨by simp, by simp⟩),
    mem_transition_setC]
  simp

/-! ### The compound proof step -/

/-- The part of a compound proof step that ends with the action storing the task name, with the
read phases of the two answering memory cells spliced into its read handshakes.  The first cell
delivers the triple `(S₁, t₁, S₁')`, the second one `(S₂, t₂, S₂')`; nothing is assumed about
these triples — the point of `HTN.ToAc.compoundStep_matches` is that executability determines
them. -/
noncomputable def compoundStepPrefix (c : C) (x y : A ⊕ C) (S₁ S₁' S₂ S₂' : Set F)
    (t₁ t₂ : A ⊕ C) (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)) (vars : List F) :
    List (AcAct F A C) :=
  AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ readPhase S₁ S₁' t₁ vars ++ e₁ ++ e₂ ++ [AcAct.preC x] ++
    readPhase S₂ S₂' t₂ vars ++ e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)])

/-- **What a compound proof step reads.**  If the guessing, reading and comparing part of a
compound proof step for the method `c ↦ x y` is executable, then the two memory cells that
answered its read handshakes delivered the triples `(S₁, x, S₁')` and `(S₁', y, S₂')`, and in
the state the step reaches the first copy represents `S₁`, the third copy represents `S₂'` and
the stored task name is `c`. -/
theorem compoundStep_matches (hvars : ∀ v : F, v ∈ vars) {c : C} {x y : A ⊕ C}
    {S₁ S₁' S₂ S₂' : Set F} {t₁ t₂ : A ⊕ C} {g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)}
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂)
    (he₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃)
    (he₄ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄)
    {s : Set (AcFact F A C)}
    (happ : (domain D vars bound).SeqApplicable
      (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s) :
    t₁ = x ∧ t₂ = y ∧ S₁' = S₂ ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s) 0 S₁ vars ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s) 2 S₂' vars ∧
      AcFact.task (Sum.inr c) ∈ (domain D vars bound).transitionSeq
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s := by
  classical
  have hgoal : (domain D vars bound).transitionSeq
      (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s =
      (domain D vars bound).transition (AcAct.setC (Sum.inr c))
        ((domain D vars bound).transitionSeq e₄
          ((domain D vars bound).transitionSeq e₃
            ((domain D vars bound).transitionSeq (readPhase S₂ S₂' t₂ vars)
              ((domain D vars bound).transitionSeq e₂
                ((domain D vars bound).transitionSeq e₁
                  ((domain D vars bound).transitionSeq (readPhase S₁ S₁' t₁ vars)
                    ((domain D vars bound).transitionSeq g₃
                      ((domain D vars bound).transitionSeq g₂
                        ((domain D vars bound).transitionSeq g₁
                          ((domain D vars bound).transition AcAct.lock s)))))))))) := by
    simp [compoundStepPrefix, ActionModel.transitionSeq_append]
  simp only [compoundStepPrefix, ActionModel.seqApplicable_cons,
    ActionModel.seqApplicable_append, ActionModel.transitionSeq_append,
    ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
    ActionModel.seqApplicable_nil, and_true] at happ
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, he1a⟩, he2a⟩, hpx⟩, -⟩, he3a⟩, he4a⟩, hpy, -⟩ := happ
  set s₀ := (domain D vars bound).transition AcAct.lock s with hs₀
  set s₁ := (domain D vars bound).transitionSeq g₁ s₀ with hs₁
  set s₂ := (domain D vars bound).transitionSeq g₂ s₁ with hs₂
  set s₃ := (domain D vars bound).transitionSeq g₃ s₂ with hs₃
  -- the three guesses
  obtain ⟨-, -, A₀, hA₀⟩ := yieldSeq_SEL_spec hg₁ s₀
  obtain ⟨-, hu₂, A₁, hA₁⟩ := yieldSeq_SEL_spec hg₂ s₁
  obtain ⟨-, hu₃, A₂, hA₂⟩ := yieldSeq_SEL_spec hg₃ s₂
  have hA₀₃ : RepresentsOn s₃ 0 A₀ vars :=
    representsOn_of_unchangedOutside (by decide)
      (representsOn_of_unchangedOutside (by decide) hA₀ hu₂) hu₃
  have hA₁₃ : RepresentsOn s₃ 1 A₁ vars :=
    representsOn_of_unchangedOutside (by decide) hA₁ hu₃
  have hA₂₃ : RepresentsOn s₃ 2 A₂ vars := hA₂
  -- the first read phase
  set s₄ := (domain D vars bound).transitionSeq (readPhase S₁ S₁' t₁ vars) s₃ with hs₄
  obtain ⟨-, hrep3₄, hrep4₄, -, -, -⟩ := readPhase_spec (D := D) (vars := vars) (bound := bound) S₁ S₁' t₁ s₃
  have hA₀₄ : RepresentsOn s₄ 0 A₀ vars :=
    representsOn_readPhase_other (by decide) (by decide) hA₀₃
  have hA₁₄ : RepresentsOn s₄ 1 A₁ vars :=
    representsOn_readPhase_other (by decide) (by decide) hA₁₃
  have hA₂₄ : RepresentsOn s₄ 2 A₂ vars :=
    representsOn_readPhase_other (by decide) (by decide) hA₂₃
  -- the comparisons do not change the state
  have he₁tr : (domain D vars bound).transitionSeq e₁ s₄ = s₄ := transitionSeq_yieldSeq_EQ he₁ s₄
  rw [he₁tr] at he2a hpx he3a he4a hpy hgoal
  have he₂tr : (domain D vars bound).transitionSeq e₂ s₄ = s₄ := transitionSeq_yieldSeq_EQ he₂ s₄
  rw [he₂tr] at hpx he3a he4a hpy hgoal
  rw [transition_preC] at he3a he4a hpy
  -- what the first cell delivered
  have hx : t₁ = x := by
    have := (applicable_preC_iff (D := D) (vars := vars) (bound := bound)).1 hpx
    rw [hs₄] at this
    exact ((task_mem_transitionSeq_readPhase_iff (D := D) (bound := bound)).1 this).symm
  have heq₁ : A₀ = S₁ :=
    Set.ext fun v => (eq_executable_iff hA₀₄ hrep3₄).1 ⟨e₁, he₁, he1a⟩ v (hvars v)
  have heq₂ : A₁ = S₁' :=
    Set.ext fun v => (eq_executable_iff hA₁₄ hrep4₄).1 ⟨e₂, he₂, he2a⟩ v (hvars v)
  -- the second read phase
  set s₅ := (domain D vars bound).transitionSeq (readPhase S₂ S₂' t₂ vars) s₄ with hs₅
  obtain ⟨-, hrep3₅, hrep4₅, -, -, -⟩ := readPhase_spec (D := D) (vars := vars) (bound := bound) S₂ S₂' t₂ s₄
  have hA₀₅ : RepresentsOn s₅ 0 A₀ vars :=
    representsOn_readPhase_other (by decide) (by decide) hA₀₄
  have hA₁₅ : RepresentsOn s₅ 1 A₁ vars :=
    representsOn_readPhase_other (by decide) (by decide) hA₁₄
  have hA₂₅ : RepresentsOn s₅ 2 A₂ vars :=
    representsOn_readPhase_other (by decide) (by decide) hA₂₄
  have he₃tr : (domain D vars bound).transitionSeq e₃ s₅ = s₅ := transitionSeq_yieldSeq_EQ he₃ s₅
  rw [he₃tr] at he4a hpy hgoal
  have he₄tr : (domain D vars bound).transitionSeq e₄ s₅ = s₅ := transitionSeq_yieldSeq_EQ he₄ s₅
  rw [he₄tr] at hpy hgoal
  have hy : t₂ = y := by
    have := (applicable_preC_iff (D := D) (vars := vars) (bound := bound)).1 hpy
    rw [hs₅] at this
    exact ((task_mem_transitionSeq_readPhase_iff (D := D) (bound := bound)).1 this).symm
  have heq₃ : A₁ = S₂ :=
    Set.ext fun v => (eq_executable_iff hA₁₅ hrep3₅).1 ⟨e₃, he₃, he3a⟩ v (hvars v)
  have heq₄ : A₂ = S₂' :=
    Set.ext fun v => (eq_executable_iff hA₂₅ hrep4₅).1 ⟨e₄, he₄, he4a⟩ v (hvars v)
  refine ⟨hx, hy, by rw [← heq₂, heq₃], ?_, ?_, ?_⟩
  · rw [hgoal, ← heq₁]
    exact representsOn_transition_setC hA₀₅
  · rw [hgoal, ← heq₄]
    exact representsOn_transition_setC hA₂₅
  · rw [hgoal]
    exact mem_transition_setC.2 (Or.inr rfl)

/-- **A compound proof step proves a proof tuple.**  In the situation of
`HTN.ToAc.compoundStep_matches`, if the two triples the cells delivered are derivable in the
proof-tuple calculus, then so is the triple `(S₁, c, S₂')` the step offers to the next cell. -/
theorem compoundStep_provable (hvars : ∀ v : F, v ∈ vars) {c : C} {x y : A ⊕ C}
    {S₁ S₁' S₂ S₂' : Set F} {t₁ t₂ : A ⊕ C} {g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)}
    (hmethod : D.SeqBody c [x, y])
    (hp₁ : D.Provable S₁ t₁ S₁') (hp₂ : D.Provable S₂ t₂ S₂')
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂)
    (he₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃)
    (he₄ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄)
    {s : Set (AcFact F A C)}
    (happ : (domain D vars bound).SeqApplicable
      (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s) :
    D.Provable S₁ (Sum.inr c) S₂' ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s) 0 S₁ vars ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s) 2 S₂' vars ∧
      AcFact.task (Sum.inr c) ∈ (domain D vars bound).transitionSeq
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s := by
  obtain ⟨rfl, rfl, hS, hrep₀, hrep₂, htask⟩ :=
    compoundStep_matches hvars hg₁ hg₂ hg₃ he₁ he₂ he₃ he₄ happ
  subst hS
  exact ⟨Domain.Provable.two hmethod hp₁ hp₂, hrep₀, hrep₂, htask⟩

end ToAc

end HTN
