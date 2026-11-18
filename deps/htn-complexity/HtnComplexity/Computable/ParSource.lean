import HtnComplexity.Computable.ParSplit
/-!
# The source side: an unordered initial network refines in parallel

This file combines the parallel split of `HtnComplexity/Computable/ParSplit.lean` with the
plan-level normal form theorem of `HtnPlanning/Interleave/NetYieldSeq.lean`:

* `HTN.Syn.netYield_singleTn_iff_yieldSeq` — for a totally ordered domain description the
  refinements of a single described compound task are the refinements of the one-element task
  sequence;
* `HTN.Syn.netYield_netTn_iff_parYield` — **the refinements of an unordered described network of
  compound tasks are exactly its parallel refinements** (`HTN.Domain.ParYield`), one process per
  task.

The right-hand side is the relation the compiled domain of the product construction simulates
step by step.
-/

namespace HTN

namespace Syn

/-- **`MethodsTO` is sound for the methods alone.** -/
theorem isTO_M_problem {d : DomDesc} {q : InstDesc} (hd : d.MethodsTO) :
    (problem d q).IsTO_M := by
  intro m hm
  obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
  exact hd e he

/-- **The refinements of a single described compound task are the refinements of the
corresponding one-element task sequence.** -/
theorem netYield_singleTn_iff_yieldSeq {d : DomDesc} (hTO : d.MethodsTO) {c : ℕ} {as : List ℕ} :
    d.toDomain.NetYield (singleTn c).toTaskNetwork as ↔ d.toDomain.YieldSeq [Sum.inr c] as := by
  set q : InstDesc := ([], [], singleTn c) with hq
  have hT : (problem d q).tnI.T = {0} := by
    show (singleTn c).toTaskNetwork.T = {0}
    simp [singleTn, TnDesc.toTaskNetwork, TnDesc.ids]
  have hα : (problem d q).tnI.α 0 = Sum.inr c := rfl
  have h₀ : (problem d q).tnI.IsSeqNet [0] [Sum.inr c] := by
    have := TaskNetwork.isSeqNet_singleton (tn := (problem d q).tnI) (problem_wf d q).tnI hT
    rwa [hα] at this
  exact Problem.netYield_iff_yieldSeq (P := problem d q) (problem_wf d q)
    (isTO_M_problem hTO) h₀

/-- **The refinements of an unordered described network of compound tasks are its parallel
refinements.** -/
theorem netYield_netTn_iff_parYield {d : DomDesc} (hTO : d.MethodsTO) {ws : List ℕ}
    {as : List ℕ} :
    d.toDomain.NetYield (netTn ws []).toTaskNetwork as ↔
      Domain.ParYield d.toDomain (ws.map fun c => [Sum.inr c]) as := by
  rw [netYield_netTn_iff_interleaveList, Domain.parYield_iff_interleaveList]
  refine exists_congr fun ass => and_congr_right fun _ => ?_
  rw [List.forall₂_map_left_iff]
  constructor
  · intro h
    exact h.imp fun _ _ hc => (netYield_singleTn_iff_yieldSeq hTO).1 hc
  · intro h
    exact h.imp fun _ _ hc => (netYield_singleTn_iff_yieldSeq hTO).2 hc

end Syn

end HTN
