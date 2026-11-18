import HtnPlanning.Binarisation.Binarisation
/-!
# A worked example for the totally ordered normal form

A tiny totally ordered HTN planning problem, used to check that the normal form theorem
`HTN.Problem.solvable_iff_yieldSeq`, the binarisation `HTN.Bin.problem` and the proof-tuple
characterisation `HTN.Bin.solvable_iff_provable` can actually be applied.

The problem has one fact (`true`), one action `()` (no precondition, adding the fact), one
compound task `()` with the single method

```
() ↦ ⟨() () ()⟩
```

(three primitive subtasks — note that this is *not* one of the at most binary methods assumed
by the proof-tuple characterisation), the empty initial state, the goal `{true}` and the
initial task network consisting of the compound task alone.  Its solutions are exactly the
plans `⟨() () ()⟩`.
-/

namespace HTN

namespace TOExample

open TaskNetwork

/-- The three subtasks of the only method. -/
def body : List (Unit ⊕ Unit) := [Sum.inl (), Sum.inl (), Sum.inl ()]

/-- The only method of the example domain: `() ↦ ⟨() () ()⟩`. -/
def meth : Method (ℕ × ℕ) Unit Unit := ⟨(), seq body⟩

/-- The domain of the example: one action, adding the fact `true`, and one method. -/
def dom : Domain Bool Unit Unit (ℕ × ℕ) where
  prec := fun _ => ∅
  add := fun _ => {true}
  del := fun _ => ∅
  methods := {meth}

/-- The problem instance: empty initial state, goal `{true}`, and the single initial compound
task. -/
def inst : Instance Bool Unit Unit (ℕ × ℕ) where
  init := ∅
  goal := {true}
  tnI := seq [Sum.inr ()]

/-- The example planning problem. -/
def prob : Problem Bool Unit Unit (ℕ × ℕ) := dom.mkProblem inst

lemma prob_wf : prob.WF where
  tnI := seq_wf
  methods := by
    rintro m (rfl : m = meth)
    exact seq_wf

lemma prob_isTO_M : prob.IsTO_M := by
  rintro m ⟨(rfl : m = meth), -⟩
  exact seq_isTotallyOrdered

lemma prob_tnI_isSeqNet : prob.tnI.IsSeqNet (seqIds 1) [Sum.inr ()] := seq_isSeqNet _

lemma seqBody_body : prob.domain.SeqBody () body :=
  ⟨meth, rfl, rfl, hasSeqBody_seq_iff.2 rfl⟩

/-- The compound task of the example refines into the plan `⟨() () ()⟩`. -/
lemma yieldSeq_plan : prob.domain.YieldSeq [Sum.inr ()] [(), (), ()] :=
  Domain.YieldSeq.comp seqBody_body
    (Domain.YieldSeq.prim (Domain.YieldSeq.prim (Domain.YieldSeq.prim Domain.YieldSeq.nil)))

/-- **The example problem is solvable**, by the normal form theorem. -/
theorem prob_solvable : prob.Solvable := by
  refine (Problem.solvable_iff_yieldSeq prob_wf prob_isTO_M prob_tnI_isSeqNet).2
    ⟨[(), (), ()], yieldSeq_plan, ?_, ?_⟩
  · simp [ActionModel.SeqApplicable, ActionModel.Applicable, prob, dom,
      Domain.mkProblem, inst]
  · simp [Problem.GoalState, ActionModel.transitionSeq, ActionModel.transition, prob, dom,
      Domain.mkProblem, inst]

/-- **The binarisation of the example is solvable too** — all of whose methods have at most two
subtasks. -/
theorem bin_solvable : (Bin.problem prob [Sum.inr ()]).Solvable :=
  (Bin.solvable_iff prob_wf prob_isTO_M prob_tnI_isSeqNet).2 prob_solvable

/-! ### An unsolvable variant

The same problem with the unreachable goal `{false}`: no action ever makes the fact `false`
true, so the problem is unsolvable — which the normal form theorem reduces to a statement about
action sequences. -/

/-- The variant of the example with the unreachable goal `{false}`. -/
def prob' : Problem Bool Unit Unit (ℕ × ℕ) := dom.mkProblem { inst with goal := {false} }

lemma prob'_wf : prob'.WF where
  tnI := seq_wf
  methods := by
    rintro m (rfl : m = meth)
    exact seq_wf

lemma prob'_isTO_M : prob'.IsTO_M := by
  rintro m ⟨(rfl : m = meth), -⟩
  exact seq_isTotallyOrdered

lemma prob'_tnI_isSeqNet : prob'.tnI.IsSeqNet (seqIds 1) [Sum.inr ()] := seq_isSeqNet _

/-- Only the fact `true` can ever become true. -/
lemma transitionSeq_subset (as : List Unit) {s : Set Bool} (hs : s ⊆ {true}) :
    dom.transitionSeq as s ⊆ {true} := by
  induction as generalizing s with
  | nil => simpa using hs
  | cons a as ih =>
      refine ih ?_
      intro x hx
      rcases hx with ⟨hx, -⟩ | hx
      · exact hs hx
      · exact hx

/-- **The variant with the unreachable goal is unsolvable.** -/
theorem prob'_not_solvable : ¬ prob'.Solvable := by
  intro h
  obtain ⟨as, -, -, hgoal⟩ :=
    (Problem.solvable_iff_yieldSeq prob'_wf prob'_isTO_M prob'_tnI_isSeqNet).1 h
  have hmem : (false : Bool) ∈ dom.transitionSeq as ∅ := hgoal rfl
  have := transitionSeq_subset as (s := (∅ : Set Bool)) (by simp) hmem
  simp at this

/-- **A proof tuple of the binarised domain witnesses solvability of the example.** -/
theorem exists_provable :
    ∃ s' : Set Bool, (Bin.domain prob.domain).Provable prob.init
      (Sum.inr (Sum.inr [Sum.inr ()])) s' ∧ prob.GoalState s' :=
  (Bin.solvable_iff_provable prob_wf prob_isTO_M prob_tnI_isSeqNet).1 prob_solvable

end TOExample

end HTN
