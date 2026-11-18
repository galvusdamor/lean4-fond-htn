import HtnPlanning.Core.Examples
import HtnPlanning.Progression.ProgressionSound
/-!
# A worked run of progression search

A sanity check for the definitions of `HtnPlanning/Progression/Progression.lean`: the example of
Figure 2 of Höller et al. (2020) — two unordered abstract tasks `Y`, `Z` with the methods
`Y ↦ ⟨a⟩` and `Z ↦ ⟨b⟩` — is solved by an explicit run of four search steps,

```
(∅, {Y, Z}, ε) → (∅, {a, Z}, ε) → (∅, {a, b}, ε) → (∅, {b}, ⟨a⟩) → (∅, ∅, ⟨a, b⟩),
```

two decompositions followed by two progressions, ending in a goal node
(`HTN.Examples.YZ.reachable_goalNode`).  In particular the search space of a solvable problem
really does contain a goal node, so the soundness and completeness theorems are not vacuous.
-/

namespace HTN

namespace Examples

namespace YZ

open TaskNetwork

/-- The task network after progressing the action task `2`. -/
def tn₃ : TaskNetwork ℕ Act Abs := tn₂.progress 2

/-- The task network at the end of the run: no tasks are left. -/
def tn₄ : TaskNetwork ℕ Act Abs := tn₃.progress 3

lemma tnI_ord (x y : ℕ) : ¬ tnI.ord x y := by simp [tnI]

lemma tn₁_ord (x y : ℕ) : ¬ tn₁.ord x y := by
  simp [tn₁, tnI, single, decomposeWith]

/-- The first search step: decompose the unconstrained abstract task `Y`. -/
lemma searchStep₁ : problem.Step ⟨∅, tnI, []⟩ ⟨∅, tn₁, []⟩ :=
  Problem.Step.decomp ⟨by simp [tnI], fun t' _ h => (tnI_ord t' 0) h⟩ step₁

/-- The second search step: decompose the unconstrained abstract task `Z`. -/
lemma searchStep₂ : problem.Step ⟨∅, tn₁, []⟩ ⟨∅, tn₂, []⟩ :=
  Problem.Step.decomp ⟨by simp [tn₁, tnI, single], fun t' _ h => (tn₁_ord t' 1) h⟩ step₂

/-- The third search step: progress the action `a`. -/
lemma searchStep₃ :
    problem.Step ⟨∅, tn₂, []⟩ ⟨problem.transition 0 ∅, tn₃, [] ++ [0]⟩ :=
  Problem.Step.prog ⟨by rw [tn₂_T]; simp, fun t' _ h => (tn₂_ord t' 2) h⟩
    (by simp [tn₂, tn₁, tnI, single]) (by simp [ActionModel.Applicable, problem])

/-- The fourth search step: progress the action `b`. -/
lemma searchStep₄ :
    problem.Step ⟨problem.transition 0 ∅, tn₃, [0]⟩
      ⟨problem.transition 1 (problem.transition 0 ∅), tn₄, [0] ++ [1]⟩ :=
  Problem.Step.prog
    ⟨by rw [tn₃, progress_T, tn₂_T]; simp, fun t' _ h => (tn₂_ord t' 3) h.1⟩
    (by simp [tn₃, tn₂, tn₁, tnI, single]) (by simp [ActionModel.Applicable, problem])

/-- **The example is solved by progression search**: four steps lead from the initial node to a
goal node whose plan is `⟨a, b⟩`. -/
theorem reachable_goalNode :
    problem.ReachableNode ⟨problem.transition 1 (problem.transition 0 ∅), tn₄, [0, 1]⟩ ∧
      problem.IsGoalNode ⟨problem.transition 1 (problem.transition 0 ∅), tn₄, [0, 1]⟩ := by
  constructor
  · have h1 : problem.ReachableNode ⟨∅, tn₁, []⟩ :=
      Relation.ReflTransGen.single searchStep₁
    have h2 : problem.ReachableNode ⟨∅, tn₂, []⟩ := h1.tail searchStep₂
    have h3 : problem.ReachableNode ⟨problem.transition 0 ∅, tn₃, [0]⟩ :=
      h2.tail (by simpa using searchStep₃)
    exact h3.tail (by simpa using searchStep₄)
  · refine ⟨?_, by simp [Problem.GoalState, problem]⟩
    show tn₄.T = ∅
    rw [tn₄, tn₃, progress_T, progress_T, tn₂_T]
    decide

end YZ

end Examples

end HTN
