import HtnPlanning.Core.TONormalForm
import HtnPlanning.Interleave.NetYield
/-!
# The refinements of a totally ordered initial task network, plan by plan

`HtnPlanning/Core/TONormalForm.lean` proves the normal form theorem for a totally ordered
problem at the level of **solvability**: the problem is solvable exactly when its initial task
sequence refines into an executable action sequence reaching the goal
(`HTN.Problem.solvable_iff_yieldSeq`).  A compilation that compares two problems refinement by
refinement needs the plan-level statement, which is what this file isolates:

* `HTN.Problem.netYield_iff_yieldSeq` — for a well-formed problem with totally ordered methods
  whose initial task network is the task sequence `xs₀`, the refinements of the initial task
  network are exactly the refinements of `xs₀` as a task sequence.

Both halves are already in `TONormalForm.lean`; this file only drops the executability and goal
conditions from them, as `HtnComplexity/Regular/RegularYield.lean` does for derivations.
-/

namespace HTN

namespace Problem

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}
variable [DecidableEq I] {P : Problem F A C I}

/-- **Every refinement of the initial task sequence is a refinement of the initial task
network.** -/
theorem netYield_of_yieldSeq [Infinite I] (hwf : P.WF) {l₀ : List I} {xs₀ : List (A ⊕ C)}
    (h₀ : P.tnI.IsSeqNet l₀ xs₀) {as : List A} (hy : P.domain.YieldSeq xs₀ as) :
    P.domain.NetYield P.tnI as := by
  obtain ⟨tn₂, l₂, hreach₂, hseq₂⟩ :=
    exists_reachable_isSeqNet_of_yieldSeq (done := []) (rest := []) hwf hy
      (by simpa using h₀) Relation.ReflTransGen.refl
  rw [List.nil_append, List.append_nil] at hseq₂
  exact Domain.netYield_iff.2 ⟨tn₂, hreach₂, hseq₂.isPrimitive_of_labels, l₂,
    hseq₂.isLinearization, hseq₂.isActionSeq_of_labels⟩

/-- **Every refinement of the initial task network is a refinement of the initial task
sequence.** -/
theorem yieldSeq_of_netYield (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I} {xs₀ : List (A ⊕ C)}
    (h₀ : P.tnI.IsSeqNet l₀ xs₀) {as : List A} (h : P.domain.NetYield P.tnI as) :
    P.domain.YieldSeq xs₀ as := by
  obtain ⟨tn, hreach, -, lin, hlin, hseqa⟩ := Domain.netYield_iff.1 h
  obtain ⟨l, xs, hseq, hcont⟩ :=
    exists_isSeqNet_of_reachable hwf hto h₀ (show P.Reachable tn from hreach)
  have hll : lin = l := hseq.linearization_eq hlin
  subst hll
  have hxs : xs = as.map Sum.inl := by rw [← hseq.labels]; exact hseqa
  subst hxs
  exact hcont as (Domain.yieldSeq_map_inl as)

/-- **The refinements of a totally ordered initial task network are the refinements of its task
sequence.** -/
theorem netYield_iff_yieldSeq [Infinite I] (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I}
    {xs₀ : List (A ⊕ C)} (h₀ : P.tnI.IsSeqNet l₀ xs₀) {as : List A} :
    P.domain.NetYield P.tnI as ↔ P.domain.YieldSeq xs₀ as :=
  ⟨yieldSeq_of_netYield hwf hto h₀, netYield_of_yieldSeq hwf h₀⟩

end Problem

end HTN
