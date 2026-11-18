import HtnComplexity.Computable.BinCorrect
/-!
# Binarisation for an unrestricted totally ordered initial task network

`HtnComplexity/Computable/BinCorrect.lean` proves the binarisation `binDom d`, `binInst q`
correct for a *rooted* instance description.  The translation of instances only doubles the names
of the labels of the initial task network, so the same proof works for every totally ordered
initial task network:

> `HTN.Syn.Binarise.solvable_binTO_iff` — for a totally ordered domain description `d` and a
> totally ordered instance description `q`, `Solvable (binDom d) (binInst q) ↔ Solvable d q`.
-/

namespace HTN

namespace Syn

namespace Binarise

variable {d : DomDesc}

lemma binInst_ord (q : InstDesc) :
    (binInst q).tnI.toTaskNetwork.ord = q.tnI.toTaskNetwork.ord := rfl

lemma binInst_α (q : InstDesc) (i : ℕ) :
    (binInst q).tnI.toTaskNetwork.α i = encTask (q.tnI.toTaskNetwork.α i) :=
  binInst_label q i

/-- The translated instance description of a totally ordered one is totally ordered. -/
theorem binInst_isTO {q : InstDesc} (h : InstDesc.IsTO q) : InstDesc.IsTO (binInst q) := h

/-- The translated initial task network is the sequence of the encoded labels. -/
theorem binInst_isSeqNet {q : InstDesc} {l : List ℕ} {xs : List (ℕ ⊕ ℕ)}
    (h : q.tnI.toTaskNetwork.IsSeqNet l xs) :
    (binInst q).tnI.toTaskNetwork.IsSeqNet l (emb xs) := by
  refine ⟨h.nodup, h.memT, ?_, h.ord⟩
  rw [← h.labels, emb, List.map_map]
  exact List.map_congr_left fun i _ => binInst_α q i

/-- **The binarisation preserves and reflects solvability for every totally ordered initial task
network.** -/
theorem solvable_binTO_iff {q : InstDesc} (hTO : DomDesc.MethodsTO d) (hq : InstDesc.IsTO q) :
    Solvable (binDom d) (binInst q) ↔ Solvable d q := by
  obtain ⟨l, xs, hseq⟩ := TaskNetwork.exists_isSeqNet (problem_wf d q).tnI hq
  have hseq' : (problem (binDom d) (binInst q)).tnI.IsSeqNet l (emb xs) := binInst_isSeqNet hseq
  have hTOm : (problem d q).IsTO_M := (isTO_problem hTO hq).2
  have hTOm' : (problem (binDom d) (binInst q)).IsTO_M :=
    (isTO_problem (binDom_methodsTO d) (binInst_isTO hq)).2
  have hsrc : Solvable d q ↔ ∃ as : List ℕ, d.toDomain.YieldSeq xs as ∧
      d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList} :=
    Problem.solvable_iff_yieldSeq (problem_wf d q) hTOm hseq
  have htgt : Solvable (binDom d) (binInst q) ↔ ∃ as : List ℕ,
      (binDom d).toDomain.YieldSeq (emb xs) as ∧
      (binDom d).toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ (binDom d).toDomain.transitionSeq as {f | f ∈ q.initList} :=
    Problem.solvable_iff_yieldSeq (problem_wf (binDom d) (binInst q)) hTOm' hseq'
  rw [hsrc, htgt]
  constructor
  · rintro ⟨as', hy, happ, hgoal⟩
    refine ⟨dec as', ?_, (seqApplicable_bin d as' _).1 happ, ?_⟩
    · exact yieldSeq_of_corr hTO hy _ (corr_emb d xs)
    · rw [← transitionSeq_bin d as' {f | f ∈ q.initList}]
      exact hgoal
  · rintro ⟨as, hy, happ, hgoal⟩
    obtain ⟨as', hy', hdec⟩ := exists_yieldSeq_binDom hTO hy
    refine ⟨as', hy', ?_, ?_⟩
    · rw [seqApplicable_bin d as' _, hdec]
      exact happ
    · rw [transitionSeq_bin d as' {f | f ∈ q.initList}, hdec]
      exact hgoal

end Binarise

end Syn

end HTN
