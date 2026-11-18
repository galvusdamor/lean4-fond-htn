import HtnPlanning.Core.Classes
/-!
# No-op HTN planning problems

In a *no-op* problem (`HTN-NOOP`) every action has an empty precondition, add list and delete
list.  Such actions neither restrict executability nor change the state, so the only thing that
matters for solvability is whether the initial task network can be refined into a primitive
task network at all (and whether the goal already holds in the initial state).  This is the
observation used in the compilability project ("the only property that is relevant is whether
there exists a refinement into primitive tasks at all").

The main result is `Problem.IsNoop.solvable_iff`.
-/

namespace HTN

namespace Problem

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace IsNoop

variable {P : Problem F A C I} (h : P.IsNoop)
include h

/-- A no-op action does not change the state. -/
@[simp] lemma transition (a : A) (s : Set F) : P.transition a s = s := by
  obtain ⟨-, hadd, hdel⟩ := h a
  simp [ActionModel.transition, hadd, hdel]

/-- A sequence of no-op actions does not change the state. -/
@[simp] lemma transitionSeq (as : List A) (s : Set F) : P.transitionSeq as s = s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => rw [ActionModel.transitionSeq, h.transition a s, ih]

/-- Every sequence of no-op actions is applicable. -/
@[simp] lemma seqApplicable (as : List A) (s : Set F) : P.SeqApplicable as s := by
  induction as generalizing s with
  | nil => trivial
  | cons a as ih =>
    refine ⟨?_, ?_⟩
    · obtain ⟨hprec, -, -⟩ := h a
      simp [ActionModel.Applicable, hprec]
    · rw [h.transition a s]
      exact ih s

end IsNoop

variable [DecidableEq I] {P : Problem F A C I}

/-- **Solvability of no-op problems.** A well-formed no-op planning problem is solvable iff its
goal already holds in the initial state and the initial task network can be refined into a
primitive task network. -/
theorem IsNoop.solvable_iff (hnoop : P.IsNoop) (hwf : P.WF) :
    P.Solvable ↔ (P.goal ⊆ P.init ∧ ∃ tn : TaskNetwork I A C, P.Reachable tn ∧ tn.IsPrimitive) := by
  constructor
  · rintro ⟨tn, hreach, hprim, l, as, hlin, hseq, -, hgoal⟩
    rw [hnoop.transitionSeq] at hgoal
    exact ⟨hgoal, tn, hreach, hprim⟩
  · rintro ⟨hgoal, tn, hreach, hprim⟩
    obtain ⟨l, as, hlin, hseq⟩ :=
      TaskNetwork.exists_linearization_actionSeq (HTN.DecomposesTo.wf hreach hwf.tnI) hprim
    exact ⟨tn, hreach, hprim, l, as, hlin, hseq, hnoop.seqApplicable as P.init,
      by rw [hnoop.transitionSeq]; exact hgoal⟩

/-- In a no-op problem, solvability does not depend on the actions at all: it only depends on
the hierarchy and on whether the goal holds initially. -/
theorem IsNoop.solvable_iff_of_goal (hnoop : P.IsNoop) (hwf : P.WF) (hgoal : P.goal ⊆ P.init) :
    P.Solvable ↔ ∃ tn : TaskNetwork I A C, P.Reachable tn ∧ tn.IsPrimitive := by
  rw [hnoop.solvable_iff hwf]
  exact ⟨fun h => h.2, fun h => ⟨hgoal, h⟩⟩

end Problem

end HTN
