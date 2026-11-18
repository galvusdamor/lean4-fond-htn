import HtnComplexity.Computable.AcFreePostState
/-!
# The verification phase as the tail of the wrapped problem

`HtnComplexity/Computable/AcFreePostState.lean` computes the refinements of the compound
task `tPost` and their effect.  This file turns that into a statement about *solvability*:

> `HTN.Syn.AcFree.solvable_post` — the wrapped problem, restarted in the state `s` with the
> single task `tPost`, is solvable exactly when `s` passes every check and every goal fact
> either already holds or is a receipt the state lets the phase earn.

The only work is the normal form theorem `HTN.Problem.solvable_iff_yieldSeq`, whose hypothesis
`TO-M` holds here because every method the phase can reach is one of the wrapper's, and those
are chains.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

variable {V : List ℕ} {d₀ : DomDesc}

/-! ### The labels of a one-row grid -/

/-- Every label of a one-row described grid is the label of one of its cells. -/
lemma label_mem_oneRow {row : List (Bool × ℕ)} {t : ℕ}
    (ht : t ∈ (gridDesc [row]).toTaskNetwork.T) :
    ∃ p ∈ row, (gridDesc [row]).toTaskNetwork.α t =
      (if p.1 then Sum.inr p.2 else Sum.inl p.2) := by
  rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridDesc_ids, cellIds_oneRow,
    List.mem_map] at ht
  obtain ⟨j, hj, rfl⟩ := ht
  rw [List.mem_range] at hj
  refine ⟨row.getD j (false, 0), ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  · rw [TnDesc.toTaskNetwork_α, label_oneRow hj]

/-! ### The tasks the verification phase can reach -/

/-- Every method of the wrapper is a chain. -/
lemma exists_row_of_mem_wrapMeths {e : MethodDesc} (he : e ∈ wrapMeths V) :
    ∃ row, e.2 = gridDesc [row] := by
  rcases mem_wrapMeths_iff.1 he with rfl | ⟨v, -, hv⟩
  · exact ⟨postBody V, rfl⟩
  · rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨[pAct (aChkN v)], rfl⟩
    · exact ⟨[pAct (aChkP v)], rfl⟩
    · exact ⟨[pAct (aEarn v)], rfl⟩
    · exact ⟨[pAct aSkip], rfl⟩

/-- No subtask of a method of the wrapper has a base-shaped name. -/
lemma not_baseTask_of_label_wrapMeths {e : MethodDesc} (he : e ∈ wrapMeths V) {t c : ℕ}
    (ht : t ∈ e.2.toTaskNetwork.T) (hc : e.2.toTaskNetwork.α t = Sum.inr c) : ¬ BaseTask c := by
  rcases mem_wrapMeths_iff.1 he with rfl | ⟨v, -, hv⟩
  · obtain ⟨p, hp, hα⟩ := label_mem_oneRow ht
    rw [hα] at hc
    rcases List.mem_append.1 hp with hp' | hp' <;>
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hp'
    · have : c = tChk w := by simpa [pTsk] using hc.symm
      exact this ▸ not_baseTask_tChk w
    · have : c = tEarn w := by simpa [pTsk] using hc.symm
      exact this ▸ not_baseTask_tEarn w
  · rcases hv with rfl | rfl | rfl | rfl <;>
    · obtain ⟨p, hp, hα⟩ := label_mem_oneRow ht
      rw [hα] at hc
      simp only [List.mem_singleton] at hp
      subst hp
      simp [pAct] at hc

/-- **Only the tasks of the verification phase are reachable from `tPost`.** -/
lemma not_baseTask_of_reachable (hshape : BaseShaped d₀) {q : InstDesc} {s : Set ℕ} {i : ℕ}
    {c : ℕ}
    (h : ((problem (wrapDom V d₀) q).restart s (netSingle i (Sum.inr tPost))).ReachableName c) :
    ¬ BaseTask c := by
  induction h with
  | @tnI t c' _ hc =>
      have hcp : c' = tPost := by simpa [netSingle] using hc.symm
      exact hcp ▸ not_baseTask_tPost
  | @method m t c hm _ ht hc ih =>
      obtain ⟨e, he, rfl⟩ := hm
      exact not_baseTask_of_label_wrapMeths
        (mem_wrapMeths_of_not_baseTask hshape he ih) ht hc

/-! ### Solvability of the verification phase -/

/-- **The verification phase, as the tail of the wrapped problem.** -/
theorem solvable_post (hshape : BaseShaped d₀) (q : InstDesc) (s : Set ℕ) (i : ℕ) :
    ((problem (wrapDom V d₀) q).restart s (netSingle i (Sum.inr tPost))).Solvable ↔
      (∀ v ∈ V, fNeg v 0 ∈ s ∨ (fPos v 0 ∈ s ∧ fLic v ∈ s)) ∧
        {f | f ∈ q.goalList} ⊆ s ∪ earned V s := by
  set PP := (problem (wrapDom V d₀) q).restart s (netSingle i (Sum.inr tPost)) with hPP
  have hwf : PP.WF := ⟨netSingle_wf, (problem_wf (wrapDom V d₀) q).methods⟩
  have hto : PP.IsTO_M := by
    rintro m ⟨hm, hr⟩
    obtain ⟨e, he, rfl⟩ := hm
    obtain ⟨row, hrow⟩ :=
      exists_row_of_mem_wrapMeths (mem_wrapMeths_of_not_baseTask hshape he
        (not_baseTask_of_reachable hshape hr))
    rw [MethodDesc.toMethod_subtasks, hrow]
    exact oneRow_isTotallyOrdered
  have h₀ : PP.tnI.IsSeqNet [i] [Sum.inr tPost] :=
    TaskNetwork.isSeqNet_singleton netSingle_wf (t₀ := i) rfl
  rw [Problem.solvable_iff_yieldSeq hwf hto h₀]
  exact post_iff hshape

end AcFree

end Syn

end HTN
