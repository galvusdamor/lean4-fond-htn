import HtnPlanning.Computable.Relevance
import HtnComplexity.Interleave.RunsCalculus
/-!
# Solvability is monotone in the initial state and antitone in the goal

The action model of this development — like STRIPS, and unlike formalisms with negative
preconditions — tests only *positive* facts: an action is applicable in a state when its
precondition list is contained in it, and the goal is reached when the goal list is contained in
the final state.  The monotonicity of the transition functions and of executability is already
available (`HTN.ActionModel.transitionSeq_mono`, `HTN.ActionModel.seqApplicable_mono` of
`HtnComplexity/Interleave/RunsCalculus.lean`); this file draws the consequence for whole planning
problems.

* `HTN.Problem.solvable_mono` — a planning problem whose initial state is enlarged and whose
  goal is shrunk stays solvable;
* `HTN.Syn.solvable_mono`, `HTN.Syn.solvable_mono_init`, `HTN.Syn.solvable_mono_goal` — the same
  for descriptions.

Nothing in the *decomposition* part of the semantics is touched: the hierarchy is orthogonal to
the state, and only the executability condition of the solution criteria is used.  This is the
principle a **guessing gadget** rests on: a compiled problem that may replace its initial state
by a subset of itself is still sound, because a plan found from the smaller state witnesses
solvability from the original one.
-/

namespace HTN

namespace Problem

variable {F A C I : Type} [DecidableEq I] {P P' : Problem F A C I}

/-- **Solvability is monotone in the initial state and antitone in the goal.**  The two problems
share their action model, their methods and their initial task network; the second has the
larger initial state and the smaller goal. -/
theorem solvable_mono (hδ : P'.toActionModel = P.toActionModel) (hm : P'.methods = P.methods)
    (htn : P'.tnI = P.tnI) (hinit : P.init ⊆ P'.init) (hgoal : P'.goal ⊆ P.goal)
    (h : P.Solvable) : P'.Solvable := by
  obtain ⟨as, tn, l, hreach, hprim, hlin, hseq, happ, hg⟩ :=
    solvable_iff_exists_solutionPlan.1 h
  refine solvable_iff_exists_solutionPlan.2 ⟨as, tn, l, ?_, hprim, hlin, hseq, ?_, ?_⟩
  · show HTN.DecomposesTo P'.methods P'.tnI tn
    rw [hm, htn]
    exact hreach
  · show P'.toActionModel.SeqApplicable as P'.init
    rw [hδ]
    exact ActionModel.seqApplicable_mono as hinit happ
  · show P'.goal ⊆ P'.toActionModel.transitionSeq as P'.init
    rw [hδ]
    exact hgoal.trans (hg.trans (ActionModel.transitionSeq_mono as hinit))

end Problem

namespace Syn

variable {d : DomDesc} {q q' : InstDesc}

/-- **Solvability of a described problem is monotone in the initial state and antitone in the
goal.**  Only the two lists change; the domain description and the initial task network are the
same. -/
theorem solvable_mono (htn : q.tnI = q'.tnI) (hinit : ∀ f ∈ q.initList, f ∈ q'.initList)
    (hgoal : ∀ f ∈ q'.goalList, f ∈ q.goalList) (h : Solvable d q) : Solvable d q' :=
  Problem.solvable_mono (P := problem d q) (P' := problem d q') rfl (by simp) (by simp [htn])
    (fun _ hf => hinit _ hf) (fun _ hf => hgoal _ hf) h

/-- Enlarging the initial state preserves solvability. -/
theorem solvable_mono_init (htn : q.tnI = q'.tnI) (hgoal : q.goalList = q'.goalList)
    (hinit : ∀ f ∈ q.initList, f ∈ q'.initList) (h : Solvable d q) : Solvable d q' :=
  solvable_mono htn hinit (fun _ hf => by rw [hgoal]; exact hf) h

/-- Shrinking the goal preserves solvability. -/
theorem solvable_mono_goal (htn : q.tnI = q'.tnI) (hinit : q.initList = q'.initList)
    (hgoal : ∀ f ∈ q'.goalList, f ∈ q.goalList) (h : Solvable d q) : Solvable d q' :=
  solvable_mono htn (fun _ hf => by rw [← hinit]; exact hf) hgoal h

end Syn

end HTN
