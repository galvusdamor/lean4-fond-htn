import HtnComplexity.Computable.AcFreeTail
/-!
# The middle phase of the vocabulary-free wrapper

The second task of the initial task network of `HTN.Syn.AcFree.wrapInst` is the initial task
`tTI` of the acyclic construction, and the initial task network of the *compiled* instance
`HTN.Syn.Ac.acInstOf` is that same single task.  This file provides the bridge:

* `HTN.Syn.AcFree.netYield_single_comp_congr` — two one-task networks with the same compound
  label have the same refinements;
* `HTN.Syn.AcFree.solvable_gridSingle_iff` — solvability of a described problem whose initial
  task network is a single compound task, in terms of `HTN.Domain.NetYield`.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

/-- The initial task of the acyclic construction has the base shape. -/
lemma baseTask_tTI : BaseTask tTI := Or.inr (Or.inr (Or.inr (by norm_num [tTI])))

/-- Every method of a described domain has a well-formed subtask network. -/
lemma methods_wf (d : DomDesc) : ∀ m ∈ d.toDomain.methods, m.subtasks.WF := by
  rintro m ⟨e, -, rfl⟩
  exact e.2.toTaskNetwork_wf

/-- **Two one-task networks with the same compound label have the same refinements.** -/
theorem netYield_single_comp_congr {d : DomDesc} {tn tn' : TaskNetwork ℕ ℕ ℕ} {t t' c : ℕ}
    (h : TaskNetwork.IsSingle tn t) (hα : tn.α t = Sum.inr c)
    (h' : TaskNetwork.IsSingle tn' t') (hα' : tn'.α t' = Sum.inr c) {bs : List ℕ} :
    d.toDomain.NetYield tn bs ↔ d.toDomain.NetYield tn' bs := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨k, m, -, hm, hmt, hk⟩ :=
      (Domain.netYieldN_single_comp (D := d.toDomain) h hα (methods_wf d)).1 hn
    exact ⟨k + 1, (Domain.netYieldN_single_comp (D := d.toDomain) h' hα' (methods_wf d)).2
      ⟨k, m, rfl, hm, hmt, hk⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, m, -, hm, hmt, hk⟩ :=
      (Domain.netYieldN_single_comp (D := d.toDomain) h' hα' (methods_wf d)).1 hn
    exact ⟨k + 1, (Domain.netYieldN_single_comp (D := d.toDomain) h hα (methods_wf d)).2
      ⟨k, m, rfl, hm, hmt, hk⟩⟩

/-- A one-cell described grid is a one-task network. -/
lemma isSingle_gridSingle {p : Bool × ℕ} :
    TaskNetwork.IsSingle (gridDesc [[p]]).toTaskNetwork (Nat.pair 0 0) where
  memT := fun x => by
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridDesc_ids, cellIds_oneRow]
    simp
  ord := fun a b hab => by
    rw [gridDesc_ord] at hab
    obtain ⟨i, j, j', hi, hjj, hj', -, -⟩ := hab
    simp only [List.length_singleton] at hi
    interval_cases i
    rw [show gridRow [[p]] 0 = [p] from rfl] at hj'
    simp only [List.length_singleton] at hj'
    omega

/-- The label of a one-cell described grid. -/
lemma α_gridSingle {p : Bool × ℕ} :
    (gridDesc [[p]]).toTaskNetwork.α (Nat.pair 0 0) =
      (if p.1 then Sum.inr p.2 else Sum.inl p.2) := by
  rw [TnDesc.toTaskNetwork_α, label_oneRow (row := [p]) (by simp)]
  simp

/-- **Solvability of a described problem whose initial task network is a single compound
task.** -/
theorem solvable_gridSingle_iff {d : DomDesc} {q : InstDesc} {c : ℕ} (j : ℕ)
    (htn : q.tnI = gridDesc [[pTsk c]]) :
    Solvable d q ↔ ∃ bs, d.toDomain.NetYield (netSingle j (Sum.inr c)) bs ∧
      d.toDomain.SeqApplicable bs {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq bs {f | f ∈ q.initList} := by
  rw [Solvable, Problem.solvable_iff_netYield]
  refine exists_congr fun bs => and_congr_left fun _ => ?_
  have hα : (gridDesc [[pTsk c]]).toTaskNetwork.α (Nat.pair 0 0) = Sum.inr c := by
    rw [α_gridSingle]; rfl
  have h1 : (problem d q).tnI = (gridDesc [[pTsk c]]).toTaskNetwork := by
    rw [problem_tnI, htn]
  rw [h1]
  exact netYield_single_comp_congr isSingle_gridSingle hα isSingle_netSingle rfl

end AcFree

end Syn

end HTN
