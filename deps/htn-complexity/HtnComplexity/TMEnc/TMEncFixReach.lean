import HtnComplexity.TMEnc.TMEncFixSize
import HtnPlanning.Core.Reachability
/-!
# The compound tasks the repaired encoding can reach

`HtnComplexity/TMEnc/TMEncodingFinset.lean` lists the compound tasks the *printed* construction
uses (`HTN.TMEnc.taskFinset`) and proves that list closed under the method bodies
(`HTN.TMEnc.mem_taskFinset_of_mem_bodies`) and under the initial method
(`HTN.TMEnc.mem_taskFinset_of_mem_initNet`).  Two things were missing, and this file supplies
them.

* **The repaired construction reaches one task the printed one does not.**  The repaired head
  chain `HTN.TMEnc.headChainFix` ends in `C^{K-1}_noHead` where the printed one ends in
  `C^K_noHead`, and `K - 1` is not in `HTN.TMEnc.countFinset`.  `HTN.TMEnc.taskFinsetFix` adds
  the counting tasks of `noHeadCell` with the halving closure of `K - 1`, and that is the only
  addition needed: `HTN.TMEnc.mem_taskFinsetFix_of_mem_bodiesFix`.
* **The reachability statement itself.**  `HTN.TMEnc.mem_taskFinsetFix_of_reachableName` — every
  compound task name reachable from the initial task network of `HTN.TMEnc.problemFix` is in
  that list.  This is what a *description* of the construction needs: the description lists
  finitely many methods, and `HTN.Syn.Rendering` (`HtnComplexity/Computable/Render.lean`)
  asks precisely that the unlisted ones be unreachable.

`HTN.TMEnc.card_taskFinsetFix_le` bounds the number of tasks: the bound of the printed
construction plus the halving closure of `K - 1`, so still logarithmic in the time bound.
-/

namespace HTN

namespace TMEnc

open scoped Classical

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The list of tasks of the repaired construction -/

/-- **The compound tasks the repaired construction uses**: those of the printed one, together
with the counting tasks of `noHeadCell` for the halving closure of `K - 1`, which the repaired
head chain introduces. -/
noncomputable def taskFinsetFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Finset (TMTask Q Γ) :=
  taskFinset N w K ∪ (halvingClosure (K - 1)).image (TMTask.cSeq TMTask.noHeadCell)

lemma mem_taskFinsetFix_of_mem_taskFinset {t : TMTask Q Γ} (h : t ∈ taskFinset N w K) :
    t ∈ taskFinsetFix N w K := Finset.mem_union_left _ h

lemma cSeq_noHeadCell_mem_taskFinsetFix {k : ℕ} (hk : k ∈ halvingClosure (K - 1)) :
    TMTask.cSeq TMTask.noHeadCell k ∈ taskFinsetFix (N := N) (w := w) (K := K) :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

/-- The number of tasks of the repaired construction is the one of the printed construction plus
the halving closure of `K - 1`. -/
lemma card_taskFinsetFix_le (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    (taskFinsetFix N w K).card ≤ (taskFinset N w K).card + (2 * Nat.log 2 (K - 1) + 2) := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  exact le_trans Finset.card_image_le (card_halvingClosure_le _)

/-! ### Closure under the bodies -/

/-- The bodies of a counting task of `noHeadCell` stay inside the list. -/
lemma mem_taskFinsetFix_of_mem_bodies_cSeq_noHeadCell {k : ℕ} (hk : k ∈ halvingClosure (K - 1))
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K (TMTask.cSeq TMTask.noHeadCell k))
    {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) : c ∈ taskFinsetFix N w K := by
  have hchild : ∀ j, 2 ≤ j → j ∈ halvingClosure (K - 1) →
      halvingChild j ∈ halvingClosure (K - 1) := fun j hj hmem =>
    halvingClosure_subset_of_mem hmem (halvingChild_mem_halvingClosure hj)
  simp only [bodies] at hls
  by_cases h0 : k = 0
  · subst h0
    subst hls
    simp at hc
  · by_cases h1 : k = 1
    · subst h1
      simp only [if_neg (by omega : ¬ (1 : ℕ) = 0)] at hls
      subst hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      subst hc
      exact mem_taskFinsetFix_of_mem_taskFinset noHeadCell_mem_taskFinset
    · have hk2 : 2 ≤ k := by omega
      by_cases heven : k % 2 = 0
      · simp only [if_neg h0, if_neg h1, if_pos heven, Set.mem_singleton_iff] at hls
        subst hls
        have hhalf : k / 2 ∈ halvingClosure (K - 1) := by
          have := hchild k hk2 hk
          simpa [halvingChild, heven] using this
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        rcases hc with rfl | rfl <;> exact cSeq_noHeadCell_mem_taskFinsetFix hhalf
      · simp only [if_neg h0, if_neg h1, if_neg heven, Set.mem_singleton_iff] at hls
        subst hls
        have hpred : k - 1 ∈ halvingClosure (K - 1) := by
          have := hchild k hk2 hk
          simpa [halvingChild, heven] using this
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        rcases hc with rfl | rfl
        · exact mem_taskFinsetFix_of_mem_taskFinset noHeadCell_mem_taskFinset
        · exact cSeq_noHeadCell_mem_taskFinsetFix hpred

/-- **No decomposition of the repaired construction leaves `taskFinsetFix`.** -/
lemma mem_taskFinsetFix_of_mem_bodiesFix {t : TMTask Q Γ} (ht : t ∈ taskFinsetFix N w K)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodiesFix N w K t)
    {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) : c ∈ taskFinsetFix N w K := by
  have hK : K ∈ countFinset K w.length :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (self_mem_halvingClosure _)))
  rcases Finset.mem_union.1 ht with ht' | ht'
  · -- a task of the printed construction
    rcases bodiesFix_eq_or (N := N) (w := w) (K := K) t with heq | ⟨rfl, heq⟩
    · rw [heq] at hls
      exact mem_taskFinsetFix_of_mem_taskFinset (mem_taskFinset_of_mem_bodies ht' hls hc)
    · rw [heq] at hls
      simp only [Set.mem_singleton_iff] at hls
      subst hls
      simp only [checkerBodyFix, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      rcases hc with rfl | rfl | rfl
      · exact mem_taskFinsetFix_of_mem_taskFinset (release_mem_taskFinset _)
      · exact mem_taskFinsetFix_of_mem_taskFinset
          (cSeq_mem_taskFinset (by simp [cSeqBase]) hK)
      · exact mem_taskFinsetFix_of_mem_taskFinset (release_mem_taskFinset _)
  · -- one of the new counting tasks
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ht'
    exact mem_taskFinsetFix_of_mem_bodies_cSeq_noHeadCell hk hls hc

/-- The compound tasks of the repaired initial method are in the list. -/
lemma mem_taskFinsetFix_of_mem_initNetFix {c : TMTask Q Γ} {p : ℕ × ℕ}
    (hp : p ∈ (initNetFix (Q := Q) (Γ := Γ) K).T)
    (hc : (initNetFix (Q := Q) (Γ := Γ) K).α p = Sum.inr c) : c ∈ taskFinsetFix N w K := by
  have hK : K ∈ countFinset K w.length :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (self_mem_halvingClosure _)))
  have hmem := TaskNetwork.gridTail_α_mem_flatten (ls := initChainsFix (Q := Q) (Γ := Γ) K)
    (tl := [Sum.inr TMTask.done]) hp
  rw [show (initNetFix (Q := Q) (Γ := Γ) K) =
    TaskNetwork.gridTail (initChainsFix (Q := Q) (Γ := Γ) K) [Sum.inr TMTask.done] from rfl] at hc
  rw [hc] at hmem
  simp only [initChainsFix, headChainFix, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    Sum.inr.injEq] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_taskFinsetFix_of_mem_taskFinset (cSeq_mem_taskFinset (by simp [cSeqBase]) hK)
  · exact mem_taskFinsetFix_of_mem_taskFinset noHeadCell_mem_taskFinset
  · exact mem_taskFinsetFix_of_mem_taskFinset headCell_mem_taskFinset
  · exact cSeq_noHeadCell_mem_taskFinsetFix (self_mem_halvingClosure _)
  · exact mem_taskFinsetFix_of_mem_taskFinset (checkers_mem_taskFinset
      (halvingClosure_succ_subset_checkerFinset (self_mem_halvingClosure _)))
  · exact mem_taskFinsetFix_of_mem_taskFinset produceInit_mem_taskFinset
  · exact mem_taskFinsetFix_of_mem_taskFinset (cSeq_mem_taskFinset (by simp [cSeqBase]) hK)
  · exact mem_taskFinsetFix_of_mem_taskFinset done_mem_taskFinset

/-! ### Reachability -/

/-- **Every compound task name the repaired problem can reach is in `taskFinsetFix`.** -/
theorem mem_taskFinsetFix_of_reachableName {t : TMTask Q Γ}
    (h : (problemFix N w K).ReachableName t) : t ∈ taskFinsetFix N w K := by
  induction h with
  | @tnI x nm hx hα =>
      have hx' : x ∈ (TaskNetwork.seq [(Sum.inr TMTask.sI : TMAct Q Γ ⊕ TMTask Q Γ)]).T := hx
      rw [TaskNetwork.mem_seq_T] at hx'
      have hx0 : x = (0, 0) := by
        obtain ⟨i, j⟩ := x
        simp only [List.length_singleton] at hx'
        exact Prod.ext hx'.1 (by omega)
      subst hx0
      have hα0 : (TaskNetwork.seq [(Sum.inr TMTask.sI : TMAct Q Γ ⊕ TMTask Q Γ)]).α (0, 0) =
          Sum.inr TMTask.sI := TaskNetwork.seq_α (by simp)
      have : (Sum.inr TMTask.sI : TMAct Q Γ ⊕ TMTask Q Γ) = Sum.inr nm := by
        rw [← hα0]; exact hα
      have hnm : (TMTask.sI : TMTask Q Γ) = nm := by simpa using this
      subst hnm
      exact mem_taskFinsetFix_of_mem_taskFinset sI_mem_taskFinset
  | @method m x c hm _ hxT hxα ih =>
      rcases hm with ⟨ls, hls, hsub⟩ | hsI
      · have hmem : m.subtasks.α x ∈ ls.flatten := by
          rw [hsub] at hxT ⊢
          exact TaskNetwork.grid_α_mem_flatten hxT
        rw [hxα] at hmem
        exact mem_taskFinsetFix_of_mem_bodiesFix ih hls hmem
      · have hm' : m = ⟨TMTask.sI, initNetFix K⟩ := hsI
        subst hm'
        exact mem_taskFinsetFix_of_mem_initNetFix hxT hxα

end TMEnc

end HTN
