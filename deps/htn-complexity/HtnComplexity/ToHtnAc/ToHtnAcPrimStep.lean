import HtnComplexity.ToHtnAc.ToHtnAcTupleShape
import HtnComplexity.ToHtnAc.ToHtnAcMemPhase
/-!
# A primitive proof step proves exactly one proof tuple

`HtnComplexity/ToHtnAc/ToHtnAcTupleShape.lean` determines the shape of a proof step of the HTN-AC
compilation.  For the *primitive* shape — the one belonging to an operator `o` of the source
domain — the whole step is executed in one stretch, up to the write handshakes at its very end:

```
lock ; SEL¹ ; SEL² ; SEL³ ; EQ^{1,2} ; o² ; EQ^{2,3} ; setC o ; (ask_W ; wait_W)^w ; unlock
```

This file proves what that stretch does: whatever the three guesses are, executability forces
the second copy to be the result of applying `o` to the first copy, so the triple that the step
then offers to the memory cells is exactly `(S, o, γ(S, o))` for an `o` applicable in `S` — the
`prim` rule of the proof-tuple calculus of `HtnPlanning/Core/ProofTuples.lean`.

The two hypotheses are the expected ones: `vars` lists all the facts of the source problem
(otherwise the copies say nothing about the facts outside the list), and the operator `o` does
not add and delete the same fact.  The latter is genuinely needed: the compiled action `o²` sets
`pos v 1` for the added facts and `neg v 1` for the deleted ones, so on a fact that is both added
and deleted it would make the copy inconsistent, whereas the classical transition function
`γ(s, o) = (s \ del o) ∪ add o` lets the add list win.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### The action `o²` -/

@[simp] lemma applicable_op2_iff {o : A} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.op2 o) s ↔ ∀ v ∈ D.prec o, AcFact.pos v 1 ∈ s := by
  simp [ActionModel.Applicable, domain, actionModel, prec, Set.subset_def]

/-- `o²` changes only the second copy. -/
lemma mem_transition_op2_of_ne {o : A} {s : Set (AcFact F A C)} {f : AcFact F A C}
    (hf : ∀ v : F, f ≠ AcFact.pos v 1 ∧ f ≠ AcFact.neg v 1) :
    (f ∈ (domain D vars bound).transition (AcAct.op2 o) s ↔ f ∈ s) := by
  simp only [ActionModel.transition, domain, actionModel, add, del, Set.mem_union,
    Set.mem_diff, Set.mem_image]
  constructor
  · rintro (⟨hs, -⟩ | (⟨v, -, hv⟩ | ⟨v, -, hv⟩))
    · exact hs
    · exact absurd hv.symm (hf v).1
    · exact absurd hv.symm (hf v).2
  · intro hs
    refine Or.inl ⟨hs, ?_⟩
    rintro (⟨v, -, hv⟩ | ⟨v, -, hv⟩)
    · exact (hf v).2 hv.symm
    · exact (hf v).1 hv.symm

/-- A representation of another copy survives `o²`. -/
lemma representsOn_transition_op2 {o : A} {i : Fin 5} (hi : i ≠ 1) {S : Set F}
    {s : Set (AcFact F A C)} (h : RepresentsOn s i S vars) :
    RepresentsOn ((domain D vars bound).transition (AcAct.op2 o) s) i S vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transition_op2_of_ne (fun w => ⟨by simp [hi], by simp⟩),
    mem_transition_op2_of_ne (fun w => ⟨by simp, by simp [hi]⟩)]
  exact ⟨h1, h2⟩

/-- **`o²` applies the operator `o` to the second copy.** -/
lemma representsOn_op2 {o : A} {S : Set F} {s : Set (AcFact F A C)}
    (hdisj : Disjoint (D.add o) (D.del o)) (h : RepresentsOn s 1 S vars) :
    RepresentsOn ((domain D vars bound).transition (AcAct.op2 o) s) 1 (D.transition o S) vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  have hdisj' : ∀ u : F, u ∈ D.add o → u ∉ D.del o := by
    intro u hu hu'
    exact Set.disjoint_left.1 hdisj hu hu'
  constructor
  · simp only [ActionModel.transition, domain, actionModel, add, del, Set.mem_union,
      Set.mem_diff, Set.mem_image, ActionModel.transition]
    constructor
    · rintro (⟨hs, hnot⟩ | (⟨u, hu, huv⟩ | ⟨u, hu, huv⟩))
      · refine Or.inl ⟨h1.1 hs, fun hvdel => hnot (Or.inr ⟨v, hvdel, rfl⟩)⟩
      · rw [AcFact.pos.injEq] at huv
        exact Or.inr (huv.1 ▸ hu)
      · exact absurd huv (by simp)
    · rintro (⟨hvS, hvdel⟩ | hvadd)
      · refine Or.inl ⟨h1.2 hvS, ?_⟩
        rintro (⟨u, hu, huv⟩ | ⟨u, hu, huv⟩)
        · exact absurd huv (by simp)
        · rw [AcFact.pos.injEq] at huv
          exact hvdel (huv.1 ▸ hu)
      · exact Or.inr (Or.inl ⟨v, hvadd, rfl⟩)
  · simp only [ActionModel.transition, domain, actionModel, add, del, Set.mem_union,
      Set.mem_diff, Set.mem_image, ActionModel.transition]
    constructor
    · rintro (⟨hs, hnot⟩ | (⟨u, hu, huv⟩ | ⟨u, hu, huv⟩))
      · rintro (⟨hvS, -⟩ | hvadd)
        · exact (h2.1 hs) hvS
        · exact hnot (Or.inl ⟨v, hvadd, rfl⟩)
      · exact absurd huv (by simp)
      · rw [AcFact.neg.injEq] at huv
        rintro (⟨-, hvdel⟩ | hvadd)
        · exact hvdel (huv.1 ▸ hu)
        · exact hdisj' v hvadd (huv.1 ▸ hu)
    · intro hnot
      by_cases hvdel : v ∈ D.del o
      · exact Or.inr (Or.inr ⟨v, hvdel, rfl⟩)
      · refine Or.inl ⟨h2.2 (fun hvS => hnot (Or.inl ⟨hvS, hvdel⟩)), ?_⟩
        rintro (⟨u, hu, huv⟩ | ⟨u, hu, huv⟩)
        · rw [AcFact.neg.injEq] at huv
          exact hnot (Or.inr (huv.1 ▸ hu))
        · exact absurd huv (by simp)

/-! ### Preservation of representations -/

/-- A representation of one copy survives a change confined to another copy. -/
lemma representsOn_of_unchangedOutside {i j : Fin 5} (hij : i ≠ j) {S : Set F}
    {s s' : Set (AcFact F A C)} (h : RepresentsOn s i S vars)
    (hu : UnchangedOutside s s' j vars) : RepresentsOn s' i S vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [← hu (AcFact.pos v i) (fun w _ => ⟨by simp [hij], by simp⟩),
    ← hu (AcFact.neg v i) (fun w _ => ⟨by simp, by simp [hij]⟩)]
  exact ⟨h1, h2⟩

/-- A representation survives `lock`, `unlock` and `setC`, which do not touch the copies. -/
lemma representsOn_transition_setC {i : Fin 5} {S : Set F} {t : A ⊕ C}
    {s : Set (AcFact F A C)} (h : RepresentsOn s i S vars) :
    RepresentsOn ((domain D vars bound).transition (AcAct.setC t) s) i S vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transition_setC, mem_transition_setC]
  simpa using ⟨h1, h2⟩

@[simp] lemma mem_transition_lock {s : Set (AcFact F A C)} {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition AcAct.lock s ↔ (f ∈ s ∧ f ≠ AcFact.key0) := by
  simp [ActionModel.transition, domain, actionModel, add, del]

lemma representsOn_transition_lock {i : Fin 5} {S : Set F} {s : Set (AcFact F A C)}
    (h : RepresentsOn s i S vars) :
    RepresentsOn ((domain D vars bound).transition AcAct.lock s) i S vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transition_lock, mem_transition_lock]
  simpa using ⟨h1, h2⟩

/-- An `EQ` gadget does not change the state. -/
lemma transitionSeq_yieldSeq_EQ {i j : Fin 5} {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ i j)] as)
    (s : Set (AcFact F A C)) : (domain D vars bound).transitionSeq as s = s := by
  rw [yieldSeq_EQ_iff] at h
  exact (yieldSeq_EQn_spec (le_refl vars.length) h s).1

/-! ### The primitive proof step -/

/-- The part of a primitive proof step that is executed in one stretch: everything from the
`lock` up to and including the action storing the task name. -/
def primStepPrefix (o : A) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)) : List (AcAct F A C) :=
  AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)])

/-- **A primitive proof step proves a proof tuple.**  If the guessing and comparing part of a
primitive proof step for the operator `o` is executable in `s`, then in the state it reaches the
first copy represents a source state `S`, the third copy represents `γ(S, o)`, the stored task
name is `o`, and `o` is applicable in `S` — so the triple `(S, o, γ(S, o))` that the step now
offers to the memory cells is derivable in the proof-tuple calculus. -/
theorem primStep_provable (hvars : ∀ v : F, v ∈ vars) {o : A}
    (hdisj : Disjoint (D.add o) (D.del o))
    {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)}
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂)
    {s : Set (AcFact F A C)}
    (happ : (domain D vars bound).SeqApplicable (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s) :
    ∃ S : Set F,
      D.Provable S (Sum.inl o) (D.transition o S) ∧
      RepresentsOn ((domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s)
        0 S vars ∧
      RepresentsOn ((domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s)
        2 (D.transition o S) vars ∧
      AcFact.task (Sum.inl o) ∈
        (domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s := by
  classical
  have hgoal : (domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s =
      (domain D vars bound).transition (AcAct.setC (Sum.inl o))
        ((domain D vars bound).transitionSeq e₂
          ((domain D vars bound).transition (AcAct.op2 o)
            ((domain D vars bound).transitionSeq e₁
              ((domain D vars bound).transitionSeq g₃
                ((domain D vars bound).transitionSeq g₂
                  ((domain D vars bound).transitionSeq g₁
                    ((domain D vars bound).transition AcAct.lock s))))))) := by
    simp [primStepPrefix, ActionModel.transitionSeq_append]
  simp only [primStepPrefix, ActionModel.seqApplicable_cons, ActionModel.seqApplicable_append,
    ActionModel.transitionSeq_append, ActionModel.transitionSeq_cons,
    ActionModel.transitionSeq_nil, ActionModel.seqApplicable_nil, and_true] at happ
  obtain ⟨-, ⟨⟨⟨⟨⟨-, -⟩, -⟩, he1a⟩, hopa⟩, he2a⟩, -⟩ := happ
  set s₀ := (domain D vars bound).transition AcAct.lock s with hs₀
  set s₁ := (domain D vars bound).transitionSeq g₁ s₀ with hs₁
  set s₂ := (domain D vars bound).transitionSeq g₂ s₁ with hs₂
  set s₃ := (domain D vars bound).transitionSeq g₃ s₂ with hs₃
  -- the three guesses
  obtain ⟨-, -, S₀, hrep₀⟩ := yieldSeq_SEL_spec hg₁ s₀
  obtain ⟨-, hu₂, S₁, hrep₁⟩ := yieldSeq_SEL_spec hg₂ s₁
  obtain ⟨-, hu₃, S₂, hrep₂⟩ := yieldSeq_SEL_spec hg₃ s₂
  have hrep₀₃ : RepresentsOn s₃ 0 S₀ vars :=
    representsOn_of_unchangedOutside (by decide)
      (representsOn_of_unchangedOutside (by decide) hrep₀ hu₂) hu₃
  have hrep₁₃ : RepresentsOn s₃ 1 S₁ vars :=
    representsOn_of_unchangedOutside (by decide) hrep₁ hu₃
  -- the first comparison does not change the state and forces the first two guesses to agree
  have he₁tr : (domain D vars bound).transitionSeq e₁ s₃ = s₃ := transitionSeq_yieldSeq_EQ he₁ s₃
  rw [he₁tr] at hopa he2a hgoal
  have heq₁ : S₀ = S₁ :=
    Set.ext fun v => (eq_executable_iff hrep₀₃ hrep₁₃).1 ⟨e₁, he₁, he1a⟩ v (hvars v)
  -- the operator is applicable in the guessed state and is applied to the second copy
  have happO : D.Applicable o S₀ := by
    intro v hv
    rw [heq₁]
    exact (hrep₁₃ v (hvars v)).1.1 (applicable_op2_iff.1 hopa v hv)
  set s₅ := (domain D vars bound).transition (AcAct.op2 o) s₃ with hs₅
  have hrep₁₅ : RepresentsOn s₅ 1 (D.transition o S₁) vars := representsOn_op2 hdisj hrep₁₃
  have hrep₀₅ : RepresentsOn s₅ 0 S₀ vars := representsOn_transition_op2 (by decide) hrep₀₃
  have hrep₂₅ : RepresentsOn s₅ 2 S₂ vars := representsOn_transition_op2 (by decide) hrep₂
  -- the second comparison forces the third guess to be the result of the operator
  have he₂tr : (domain D vars bound).transitionSeq e₂ s₅ = s₅ := transitionSeq_yieldSeq_EQ he₂ s₅
  have heq₂ : D.transition o S₁ = S₂ :=
    Set.ext fun v => (eq_executable_iff hrep₁₅ hrep₂₅).1 ⟨e₂, he₂, he2a⟩ v (hvars v)
  rw [he₂tr] at hgoal
  refine ⟨S₀, Domain.Provable.prim happO, ?_, ?_, ?_⟩
  · rw [hgoal]
    exact representsOn_transition_setC hrep₀₅
  · rw [hgoal, heq₁, heq₂]
    exact representsOn_transition_setC hrep₂₅
  · rw [hgoal]
    exact mem_transition_setC.2 (Or.inr rfl)

end ToAc

end HTN
