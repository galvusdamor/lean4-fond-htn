import HtnPlanning.Core.Decomposition
import HtnPlanning.Basic
/-!
# HTN planning problems and their solutions

This file formalises HTN planning problems and the solution criteria of

  D. Höller, P. Bercher, G. Behnke, S. Biundo,
  *HTN Planning as Heuristic Progression Search*, JAIR 67 (2020), Section 3.2.

An HTN planning problem is a tuple `P = (L, C, A, M, s₀, tn_I, g, δ)`.  A task network
`tn = (T, ≺, α)` is a solution iff

1. `tn_I →* tn`, i.e. `tn` can be reached by decomposing the initial task network,
2. `∀ t ∈ T : α(t) ∈ A`, i.e. all task names are primitive, and
3. there is a sequence `⟨t₁ t₂ … tₙ⟩` of the tasks in `T` that is in line with `≺` such that
   the application of `⟨α(t₁) α(t₂) … α(tₙ)⟩` in `s₀` results in a goal state.

As in `HtnPlanning.Core.Classical`, the fact set `L` is the universe of the type `F`, the
action names are the type `A`, the abstract task names are the type `C` and the task
identifiers are drawn from the type `I`.
-/

namespace HTN

universe u v w x

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

section

variable (P : Problem F A C I)

end

section

variable [DecidableEq I] (P : Problem F A C I)

/-- A *solution plan* is the action sequence induced by (a linearization of) a solution. -/
def IsSolutionPlan (as : List A) : Prop :=
  ∃ (tn : TaskNetwork I A C) (l : List I), P.Reachable tn ∧ tn.IsPrimitive ∧
    tn.IsLinearization l ∧ tn.IsActionSeq l as ∧
    P.SeqApplicable as P.init ∧ P.GoalState (P.transitionSeq as P.init)

/-- The classical planning problem underlying an HTN planning problem: it has the same actions,
initial state and goal, but no hierarchy (so any action sequence may be used). -/
def toClassicalProblem : ClassicalProblem F A where
  toActionModel := P.toActionModel
  init := P.init
  goal := P.goal

omit [DecidableEq I] in
@[simp] lemma toClassicalProblem_init : P.toClassicalProblem.init = P.init := rfl

omit [DecidableEq I] in
@[simp] lemma toClassicalProblem_goal : P.toClassicalProblem.goal = P.goal := rfl

omit [DecidableEq I] in
@[simp] lemma toClassicalProblem_toActionModel :
    P.toClassicalProblem.toActionModel = P.toActionModel := rfl

end

section

variable [DecidableEq I] {P : Problem F A C I}

/-- A problem is solvable iff it has a solution plan. -/
lemma solvable_iff_exists_solutionPlan : P.Solvable ↔ ∃ as, P.IsSolutionPlan as := by
  constructor
  · rintro ⟨tn, hreach, hprim, l, as, hlin, has, happ, hgoal⟩
    exact ⟨as, tn, l, hreach, hprim, hlin, has, happ, hgoal⟩
  · rintro ⟨as, tn, l, hreach, hprim, hlin, has, happ, hgoal⟩
    exact ⟨tn, hreach, hprim, l, as, hlin, has, happ, hgoal⟩

/-- **HTN solutions are classical plans.** The hierarchy only restricts the set of solutions:
every solution plan of an HTN planning problem is a solution of the underlying classical
planning problem. -/
theorem IsSolutionPlan.classical {as : List A} (h : P.IsSolutionPlan as) :
    P.toClassicalProblem.IsSolution as := by
  obtain ⟨tn, l, -, -, -, -, happ, hgoal⟩ := h
  exact ⟨happ, hgoal⟩

/-- Solvability of an HTN planning problem implies solvability of the underlying classical
planning problem. -/
theorem Solvable.classical (h : P.Solvable) : P.toClassicalProblem.Solvable := by
  obtain ⟨as, has⟩ := solvable_iff_exists_solutionPlan.1 h
  exact ⟨as, has.classical⟩

/-- Every solution of an HTN planning problem is well formed, provided the problem is. -/
theorem IsSolution.wf (hP : P.WF) {tn : TaskNetwork I A C} (h : P.IsSolution tn) : tn.WF :=
  HTN.DecomposesTo.wf h.1 hP.tnI

/-- If the initial task network is already primitive and well formed, then it is a solution
exactly when one of its linearizations is executable and reaches the goal. -/
theorem isSolution_tnI_iff (hprim : P.tnI.IsPrimitive) :
    P.IsSolution P.tnI ↔ P.Executable P.tnI := by
  refine ⟨fun h => h.2.2, fun h => ⟨Relation.ReflTransGen.refl, hprim, h⟩⟩

end

end Problem

end HTN
