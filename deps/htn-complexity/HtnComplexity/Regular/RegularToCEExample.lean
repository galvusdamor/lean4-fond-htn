import HtnComplexity.Regular.RegularToCECorrect
import HtnPlanning.Core.ClassExamples
/-!
# The conditional-effect compilation on an example

A small worked instance of `HTN.RegularCE.ceProblem_solvable_iff`, which shows that its
hypotheses are satisfiable — the compilation is not a statement about an empty class of
problems.

The source problem is `HTN.Examples.Ptrivial` of `HtnPlanning/Core/ClassExamples.lean`: the
single compound task `()` with the single method `() ↦ ε`.  It is well formed, regular and
totally ordered, it has a single initial compound task, and it is solvable by the empty plan;
`HTN.RegularCE.ceProblem_Ptrivial_solvable` says that the compiled problem with conditional
effects is solvable too.
-/

namespace HTN

namespace RegularCE

open CE Examples

/-- The method of `Ptrivial`. -/
private def mTrivial : Method ℕ Unit Unit := ⟨(), tnEmpty⟩

private lemma isChain_tnEmpty : (mTrivial.subtasks).IsChain [] [] none where
  nodup := by simp
  memT := by intro x; simp [mTrivial, tnEmpty]
  labels := by simp
  tailLabel := by intro p hp; exact absurd hp (by simp)
  ord := by
    intro x y
    constructor
    · intro h; exact absurd h (by simp [mTrivial, tnEmpty])
    · rintro ⟨hx, -, -⟩; simp at hx

private lemma hasBody_mTrivial : mTrivial.HasBody [] none :=
  ⟨[], none, isChain_tnEmpty, rfl⟩

private lemma Ptrivial_isTO_M : Ptrivial.IsTO_M := by
  rintro m ⟨hm, -⟩
  simp only [Ptrivial, mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  intro x hx
  simp [tnEmpty] at hx

private lemma Ptrivial_solvable : Ptrivial.Solvable := by
  refine (Problem.solvable_iff_derives Ptrivial_wf Ptrivial_isRegular.2 Ptrivial_isTO_M
    (t₀ := 0) (c₀ := ()) rfl rfl).2 ⟨[], ?_, trivial, ?_⟩
  · exact Problem.Derives.last (m := mTrivial) (by simp [Ptrivial, mkProblem, mTrivial]) rfl hasBody_mTrivial
  · intro v hv
    exact absurd hv (by simp [Ptrivial, mkProblem])

/-- **The compilation on an example.**  The problem `() ↦ ε` is compiled into a solvable
STRIPS-with-conditional-effects problem; in particular the hypotheses of
`HTN.RegularCE.ceProblem_solvable_iff` are satisfiable. -/
theorem ceProblem_Ptrivial_solvable :
    (ceProblem Ptrivial.domain {mTrivial} Ptrivial.instance).Solvable := by
  refine (ceProblem_solvable_iff (D := Ptrivial.domain) (Q := Ptrivial.instance)
    (t₀ := 0) (c₀ := ()) ?_ Ptrivial_wf Ptrivial_isRegular.2 Ptrivial_isTO_M rfl rfl).2 ?_
  · ext m
    simp [Ptrivial, mkProblem, Problem.domain, mTrivial]
  · exact Ptrivial_solvable

end RegularCE

end HTN
