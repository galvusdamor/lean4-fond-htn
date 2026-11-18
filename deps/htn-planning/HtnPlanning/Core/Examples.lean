import HtnPlanning.Core.Problem
/-!
# Examples and sanity checks

Two small examples validating the definitions of `HtnPlanning.Core.Problem`:

* `HTN.Examples.YZ`: the totally unordered problem of Figure 2 of Höller et al. (2020), with two
  unordered abstract tasks `Y`, `Z` and methods `Y ↦ ⟨a⟩`, `Z ↦ ⟨b⟩`.  We show that it is
  solvable, with solution plan `⟨a, b⟩` (`HTN.Examples.YZ.solvable`).
* `HTN.Examples.noMethods`: a problem whose initial task network contains an abstract task but
  which has no methods.  It is unsolvable, although the underlying classical planning problem is
  trivially solvable — the hierarchy really does restrict the set of solutions
  (`HTN.Examples.noMethods.not_solvable`, `HTN.Examples.noMethods.classical_solvable`).
-/

namespace HTN
namespace Examples

/-! ## The unordered example of Figure 2 -/

namespace YZ

/-- Facts: the example has no state features that matter. -/
abbrev Fact := Unit
/-- Actions `a` (`0`) and `b` (`1`). -/
abbrev Act := Fin 2
/-- Abstract tasks `Y` (`0`) and `Z` (`1`). -/
abbrev Abs := Fin 2

/-- The method `Y ↦ ⟨a⟩` (a single, unordered, primitive subtask `a`). -/
def methodY : Method ℕ Act Abs where
  abstractTask := 0
  subtasks := { T := {0}, ord := fun _ _ => False, α := fun _ => Sum.inl 0 }

/-- The method `Z ↦ ⟨b⟩`. -/
def methodZ : Method ℕ Act Abs where
  abstractTask := 1
  subtasks := { T := {0}, ord := fun _ _ => False, α := fun _ => Sum.inl 1 }

/-- The initial task network: the two unordered abstract tasks `Y` and `Z`. -/
def tnI : TaskNetwork ℕ Act Abs where
  T := {0, 1}
  ord := fun _ _ => False
  α := fun x => if x = 0 then Sum.inr 0 else Sum.inr 1

/-- The example problem: no preconditions, no effects, no state-based goal. -/
def problem : Problem Fact Act Abs ℕ where
  prec := fun _ => ∅
  add := fun _ => ∅
  del := fun _ => ∅
  methods := {methodY, methodZ}
  init := ∅
  goal := ∅
  tnI := tnI

/-- A single fresh primitive task network `{i ↦ a}`. -/
def single (i : ℕ) (a : Act) : TaskNetwork ℕ Act Abs where
  T := {i}
  ord := fun _ _ => False
  α := fun _ => Sum.inl a

lemma single_wf (i : ℕ) (a : Act) : (single i a).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma single_iso_methodY (i : ℕ) : (single i 0).Iso methodY.subtasks := by
  refine ⟨fun _ => 0, ⟨?_, ?_, ?_⟩, by simp [single, methodY], by simp [single, methodY]⟩ <;>
    simp [single, methodY, Set.MapsTo, Set.InjOn, Set.SurjOn]

lemma single_iso_methodZ (i : ℕ) : (single i 1).Iso methodZ.subtasks := by
  refine ⟨fun _ => 0, ⟨?_, ?_, ?_⟩, by simp [single, methodZ], by simp [single, methodZ]⟩ <;>
    simp [single, methodZ, Set.MapsTo, Set.InjOn, Set.SurjOn]

/-- The task network after decomposing `Y` (id `0`) into the fresh action task `2`. -/
def tn₁ : TaskNetwork ℕ Act Abs := decomposeWith tnI 0 (single 2 0)

/-- The task network after additionally decomposing `Z` (id `1`) into the fresh task `3`. -/
def tn₂ : TaskNetwork ℕ Act Abs := decomposeWith tn₁ 1 (single 3 1)

lemma step₁ : DecompStep problem.methods tnI 0 methodY tn₁ :=
  ⟨by simp [problem], by simp [tnI], by simp [tnI, methodY],
    single 2 0, single_wf 2 0, single_iso_methodY 2, by simp [tnI, single], rfl⟩

lemma step₂ : DecompStep problem.methods tn₁ 1 methodZ tn₂ := by
  refine ⟨by simp [problem], ?_, ?_, single 3 1, single_wf 3 1, single_iso_methodZ 3, ?_, rfl⟩
  · simp [tn₁, tnI, single]
  · simp [tn₁, tnI, single, methodZ]
  · simp [tn₁, tnI, single, Finset.disjoint_left]

lemma tn₂_T : tn₂.T = {2, 3} := by
  ext x
  simp [tn₂, tn₁, tnI, single]

lemma tn₂_ord (x y : ℕ) : ¬ tn₂.ord x y := by
  simp [tn₂, tn₁, tnI, single, decomposeWith]

/-- The problem of Figure 2 is solvable, with solution plan `⟨a, b⟩`. -/
theorem solvable : problem.Solvable := by
  refine ⟨tn₂, ?_, ?_, [2, 3], [0, 1], ⟨by simp, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨0, methodY, step₁⟩)
      ⟨1, methodZ, step₂⟩
  · intro t ht
    rw [tn₂_T] at ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact ⟨0, by simp [tn₂, tn₁, tnI, single]⟩
    · have : t = 3 := by simpa using ht
      subst this
      exact ⟨1, by simp [tn₂, tn₁, tnI, single]⟩
  · intro t
    rw [tn₂_T]
    simp
  · simp [tn₂_ord]
  · simp [TaskNetwork.IsActionSeq, tn₂, tn₁, tnI, single]
  · exact ⟨by simp [ActionModel.Applicable, problem], by simp [ActionModel.Applicable, problem]⟩
  · simp [Problem.GoalState, problem]

end YZ

/-! ## A problem without methods -/

namespace noMethods

/-- The initial task network consisting of a single abstract task. -/
def tnI : TaskNetwork ℕ Unit Unit where
  T := {0}
  ord := fun _ _ => False
  α := fun _ => Sum.inr ()

/-- An HTN problem with an abstract initial task but no methods at all. -/
def problem : Problem Unit Unit Unit ℕ where
  prec := fun _ => ∅
  add := fun _ => ∅
  del := fun _ => ∅
  methods := ∅
  init := ∅
  goal := ∅
  tnI := tnI

/-- Without methods, no decomposition step is possible. -/
lemma reachable_iff {tn : TaskNetwork ℕ Unit Unit} (h : problem.Reachable tn) : tn = tnI := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨tn', hstep, -⟩
  · exact h.symm
  · obtain ⟨t, m, hm, -⟩ := hstep
    exact absurd hm (by simp [problem])

/-- The problem is unsolvable: its only reachable task network is not primitive. -/
theorem not_solvable : ¬ problem.Solvable := by
  rintro ⟨tn, hreach, hprim, -⟩
  have htn : tn = tnI := reachable_iff hreach
  subst htn
  obtain ⟨a, ha⟩ := hprim 0 (by simp [tnI])
  simp [tnI] at ha

/-- The underlying classical planning problem is nevertheless (trivially) solvable. -/
theorem classical_solvable : problem.toClassicalProblem.Solvable :=
  ⟨[], trivial, by simp [ClassicalProblem.GoalState, Problem.toClassicalProblem, problem]⟩

end noMethods

end Examples
end HTN
