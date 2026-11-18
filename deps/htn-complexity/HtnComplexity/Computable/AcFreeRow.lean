import HtnComplexity.Computable.AcFreePhases
import HtnPlanning.Core.TONormalForm
/-!
# One-row described grids

Every method body the wrapper of `HtnComplexity/Computable/AcFreeWrap.lean` adds is a
described grid with a single row, that is a **chain**.  This file collects what is needed about
such a description:

* `HTN.Syn.AcFree.rowLabels` — the labels of the row, as tasks;
* `HTN.Syn.AcFree.oneRow_isSeqNet` — a one-row described grid is a sequence network, hence
  totally ordered (`HTN.Syn.AcFree.oneRow_isTotallyOrdered`);
* `HTN.Syn.AcFree.hasSeqBody_oneRow` — its only totally ordered body is the row itself;
* `HTN.Syn.AcFree.seqBody_desc_iff` — the bodies a described domain offers for a task name.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac TaskNetwork

/-- The labels of a described row, as tasks. -/
def rowLabels (row : List (Bool × ℕ)) : List (ℕ ⊕ ℕ) :=
  row.map fun p => if p.1 then Sum.inr p.2 else Sum.inl p.2

@[simp] lemma rowLabels_nil : rowLabels [] = [] := rfl

@[simp] lemma rowLabels_cons (p : Bool × ℕ) (row : List (Bool × ℕ)) :
    rowLabels (p :: row) = (if p.1 then Sum.inr p.2 else Sum.inl p.2) :: rowLabels row := rfl

lemma rowLabels_pAct (a : ℕ) : rowLabels [pAct a] = [Sum.inl a] := rfl

lemma rowLabels_pTsk (c : ℕ) : rowLabels [pTsk c] = [Sum.inr c] := rfl

variable {row : List (Bool × ℕ)}

lemma cellIds_oneRow : cellIds [row] = (List.range row.length).map (Nat.pair 0) := by
  simp [cellIds, gridRow]

/-- **A one-row described grid is a sequence network.** -/
theorem oneRow_isSeqNet :
    (gridDesc [row]).toTaskNetwork.IsSeqNet ((List.range row.length).map (Nat.pair 0))
      (rowLabels row) := by
  have hids : (gridDesc [row]).ids = (List.range row.length).map (Nat.pair 0) := by
    rw [gridDesc_ids, cellIds_oneRow]
  have hnd : ((List.range row.length).map (Nat.pair 0)).Nodup := by
    refine List.Nodup.map (fun x y h => ?_) List.nodup_range
    exact (Nat.pair_eq_pair.1 h).2
  have hmem : ∀ t, t ∈ (gridDesc [row]).toTaskNetwork.T ↔
      t ∈ (List.range row.length).map (Nat.pair 0) := by
    intro t
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, hids]
  have hrow : gridRow [row] 0 = row := rfl
  have hpair : ((List.range row.length).map (Nat.pair 0)).Pairwise
      (gridDesc [row]).toTaskNetwork.ord := by
    rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro j j' hj hj' hlt
    have hjS : j < row.length := by simpa using hj
    have hj'S : j' < row.length := by simpa using hj'
    simp only [List.getElem_range]
    rw [gridDesc_ord]
    exact ⟨0, j, j', by simp, hlt, by rw [hrow]; exact hj'S, rfl, rfl⟩
  have hseq := TaskNetwork.isSeqNet_of_pairwise_ord (tn := (gridDesc [row]).toTaskNetwork)
    (l := (List.range row.length).map (Nat.pair 0)) (TnDesc.toTaskNetwork_wf _) hnd hmem hpair
  have hmapeq : ((List.range row.length).map (Nat.pair 0)).map
      (gridDesc [row]).toTaskNetwork.α = rowLabels row := by
    rw [List.map_map]
    refine List.ext_getElem (by simp [rowLabels]) (fun j h1 h2 => ?_)
    have hj : j < row.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply, rowLabels]
    rw [TnDesc.toTaskNetwork_α, label_oneRow hj, List.getD_eq_getElem _ _ hj]
  rwa [hmapeq] at hseq

/-- A one-row described grid is totally ordered. -/
theorem oneRow_isTotallyOrdered : (gridDesc [row]).toTaskNetwork.IsTotallyOrdered :=
  oneRow_isSeqNet.isTotallyOrdered

/-- **The only totally ordered body of a one-row described grid is the row itself.** -/
theorem hasSeqBody_oneRow {c : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    Method.HasSeqBody ⟨c, (gridDesc [row]).toTaskNetwork⟩ xs ↔ xs = rowLabels row := by
  constructor
  · rintro ⟨l, hlin, hlab, -⟩
    have hl : l = (List.range row.length).map (Nat.pair 0) :=
      oneRow_isSeqNet.linearization_eq hlin
    subst hl
    rw [← hlab]
    exact (oneRow_isSeqNet (row := row)).labels
  · rintro rfl
    exact ⟨(List.range row.length).map (Nat.pair 0), oneRow_isSeqNet.isLinearization,
      oneRow_isSeqNet.labels, oneRow_isSeqNet.pairwise_ord⟩

/-- **The bodies a described domain offers for a task name.** -/
theorem seqBody_desc_iff {d : DomDesc} {c : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    d.toDomain.SeqBody c xs ↔
      ∃ e ∈ d.methods, e.1 = c ∧ Method.HasSeqBody ⟨e.1, e.2.toTaskNetwork⟩ xs := by
  constructor
  · rintro ⟨m, ⟨e, he, rfl⟩, hc, hbody⟩
    exact ⟨e, he, hc, hbody⟩
  · rintro ⟨e, he, hc, hbody⟩
    exact ⟨e.toMethod, ⟨e, he, rfl⟩, hc, hbody⟩

end AcFree

end Syn

end HTN
