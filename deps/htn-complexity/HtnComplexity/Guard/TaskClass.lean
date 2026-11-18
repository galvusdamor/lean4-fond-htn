import HtnComplexity.Guard.TaskExt
import HtnPlanning.Core.Classes
import HtnPlanning.Core.ClassHierarchy
import HtnPlanning.Core.Reachability
/-!
# Guard tasks and the classes of the table

Adding a guard task to every method body (`HTN.GuardTask.guardMethod`) changes the domain, so a
construction that is re-split by the method guard has to be placed in its class again.  The two
facts needed for that are proved here.

* `HTN.GuardTask.reachableName_guard_iff` — guarding changes neither the reachable compound task
  names nor which method decomposes which of them: the extra subtask is *primitive*, and its
  identifier is fresh, so it contributes no name.
* `HTN.GuardTask.isAcyclic_guard_iff` — hence the guarded domain is acyclic exactly when the
  original one is, with the same stratification.

The initial task network is untouched by the construction, so every condition on it — a totally
ordered initial network, a primitive one, a single initial abstract task — transfers by
definition; `HTN.GuardTask.isTO_tnI_guard_iff` records the first of them.

The guard task is *unordered* inside the body.  That is what the acyclic class allows; classes
whose condition constrains the ordering of a body — regular problems, where the compound subtask
must come last — are not preserved by this construction, and would need the guard task ordered in
front of the body instead.
-/

namespace HTN

namespace GuardTask

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]
variable {D Dg : Domain F A C I} {Q : Instance F A C I}
variable {gid : Method I A C → I} {gact : Method I A C → A}

/-- **Guarding does not change the reachable compound task names.** -/
theorem reachableName_guard_iff
    (hmeth : ∀ m ∈ D.methods, guardMethod gid gact m ∈ Dg.methods)
    (hmeth' : ∀ mg ∈ Dg.methods, ∃ m ∈ D.methods, mg = guardMethod gid gact m)
    (hfresh : ∀ m ∈ D.methods, gid m ∉ m.subtasks.T) (c : C) :
    (Dg.mkProblem Q).ReachableName c ↔ (D.mkProblem Q).ReachableName c := by
  constructor
  · intro h
    induction h with
    | tnI ht hc => exact Problem.ReachableName.tnI ht hc
    | @method mg t c hmg _ ht hc ih =>
        obtain ⟨m, hm, rfl⟩ := hmeth' mg hmg
        have htk : t ≠ gid m := by
          rintro rfl
          rw [guardMethod_subtasks, addTask_α_self] at hc
          exact absurd hc (by simp)
        have htT : t ∈ m.subtasks.T := by
          have := ht
          simp only [guardMethod_subtasks, addTask_T, Finset.mem_insert] at this
          exact this.resolve_left htk
        refine Problem.ReachableName.method (m := m) hm ih htT ?_
        rw [← addTask_α_of_ne m.subtasks (gact m) htk]
        exact hc
  · intro h
    induction h with
    | tnI ht hc => exact Problem.ReachableName.tnI ht hc
    | @method m t c hm _ ht hc ih =>
        have htk : t ≠ gid m := by
          rintro rfl
          exact hfresh m hm ht
        refine Problem.ReachableName.method (m := guardMethod gid gact m) (t := t)
          (hmeth m hm) ih ?_ ?_
        · simp only [guardMethod_subtasks, addTask_T, Finset.mem_insert]
          exact Or.inr ht
        · rw [guardMethod_subtasks, addTask_α_of_ne m.subtasks (gact m) htk]
          exact hc

/-- **Guarding preserves acyclicity, and reflects it**: the guarded domain is acyclic exactly
when the original one is, with the same stratification of the compound task names. -/
theorem isAcyclic_guard_iff
    (hmeth : ∀ m ∈ D.methods, guardMethod gid gact m ∈ Dg.methods)
    (hmeth' : ∀ mg ∈ Dg.methods, ∃ m ∈ D.methods, mg = guardMethod gid gact m)
    (hfresh : ∀ m ∈ D.methods, gid m ∉ m.subtasks.T) :
    (Dg.mkProblem Q).IsAcyclic ↔ (D.mkProblem Q).IsAcyclic := by
  have hname := reachableName_guard_iff (Q := Q) hmeth hmeth' hfresh
  constructor
  · rintro ⟨le, hstrat⟩
    refine ⟨le, ?_, ?_, ?_⟩
    · exact ⟨fun c hc => hstrat.strat.refl c ((hname c).2 hc),
        fun c₁ c₂ c₃ h₁ h₂ h₃ => hstrat.strat.trans c₁ c₂ c₃ ((hname c₁).2 h₁) ((hname c₂).2 h₂)
          ((hname c₃).2 h₃),
        fun c₁ c₂ h₁ h₂ => hstrat.strat.total c₁ c₂ ((hname c₁).2 h₁) ((hname c₂).2 h₂)⟩
    · exact fun c₁ c₂ h₁ h₂ => hstrat.antisymm c₁ c₂ ((hname c₁).2 h₁) ((hname c₂).2 h₂)
    · intro m hm t ht c hc
      refine hstrat.decreasing (guardMethod gid gact m) ⟨hmeth m hm.1, (hname _).2 hm.2⟩
        t ?_ c ?_
      · simp only [guardMethod_subtasks, addTask_T, Finset.mem_insert]
        exact Or.inr ht
      · have htk : t ≠ gid m := by
          rintro rfl
          exact hfresh m hm.1 ht
        rw [guardMethod_subtasks, addTask_α_of_ne m.subtasks (gact m) htk]
        exact hc
  · rintro ⟨le, hstrat⟩
    refine ⟨le, ?_, ?_, ?_⟩
    · exact ⟨fun c hc => hstrat.strat.refl c ((hname c).1 hc),
        fun c₁ c₂ c₃ h₁ h₂ h₃ => hstrat.strat.trans c₁ c₂ c₃ ((hname c₁).1 h₁) ((hname c₂).1 h₂)
          ((hname c₃).1 h₃),
        fun c₁ c₂ h₁ h₂ => hstrat.strat.total c₁ c₂ ((hname c₁).1 h₁) ((hname c₂).1 h₂)⟩
    · exact fun c₁ c₂ h₁ h₂ => hstrat.antisymm c₁ c₂ ((hname c₁).1 h₁) ((hname c₂).1 h₂)
    · intro mg hmg t ht c hc
      obtain ⟨m, hm, rfl⟩ := hmeth' mg hmg.1
      have htk : t ≠ gid m := by
        rintro rfl
        rw [guardMethod_subtasks, addTask_α_self] at hc
        exact absurd hc (by simp)
      have htT : t ∈ m.subtasks.T := by
        have := ht
        simp only [guardMethod_subtasks, addTask_T, Finset.mem_insert] at this
        exact this.resolve_left htk
      refine hstrat.decreasing m ⟨hm, (hname _).1 hmg.2⟩ t htT c ?_
      rw [← addTask_α_of_ne m.subtasks (gact m) htk]
      exact hc

/-- **A guarded acyclic domain is tail-recursive**, so the same construction serves as a source
in the acyclic and in the tail-recursive class. -/
theorem isTailRecursive_guard
    (hmeth : ∀ m ∈ D.methods, guardMethod gid gact m ∈ Dg.methods)
    (hmeth' : ∀ mg ∈ Dg.methods, ∃ m ∈ D.methods, mg = guardMethod gid gact m)
    (hfresh : ∀ m ∈ D.methods, gid m ∉ m.subtasks.T) (h : (D.mkProblem Q).IsAcyclic) :
    (Dg.mkProblem Q).IsTailRecursive :=
  ((isAcyclic_guard_iff hmeth hmeth' hfresh).2 h).isTailRecursive

omit [DecidableEq I] in
/-- The initial task network is untouched by the construction, so a condition on it transfers by
definition. -/
theorem isTO_tnI_guard_iff : (Dg.mkProblem Q).IsTO_tnI ↔ (D.mkProblem Q).IsTO_tnI := Iff.rfl

end GuardTask

end HTN
