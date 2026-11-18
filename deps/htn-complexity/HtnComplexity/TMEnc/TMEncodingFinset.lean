import HtnComplexity.TMEnc.EncodingSize
/-!
# A `Finset` presentation of the Turing-machine encoding

`HtnComplexity/TMEnc/TMEncoding.lean` defines the translation of an exponential-time Turing
machine into an acyclic HTN problem by giving, for every compound task, the *set* of its method
bodies (`HTN.TMEnc.bodies`).  As for the HTN-AC compilation, the compound tasks form an infinite
type (the counting tasks `C^k_t` and the waiting tasks `wait^i` are indexed by `k, i : ℕ`) and
several body families are indexed by the machine, so only per-method size bounds were available
(`HTN.TMEnc.method_size_le`, `HTN.TMEnc.sizeOn_le`).

This file gives the missing `Finset` presentation of the used part of the encoded domain, in
exactly the same shape as `HtnComplexity/ToHtnAc/ToHtnAcFinset.lean`:

* `HTN.TMEnc.taskFinset` — the finitely many compound tasks the encoding uses; it is closed
  under the method bodies and contains the tasks of the initial method
  (`HTN.TMEnc.mem_taskFinset_of_mem_bodies`, `HTN.TMEnc.mem_taskFinset_of_mem_initNet`);
* `HTN.TMEnc.bodyFinset`, `HTN.TMEnc.methodFinset`, `HTN.TMEnc.fragment` — the bodies, the
  methods and the fragment, with `HTN.TMEnc.methodFinset_subset_methods` and its converse;
* **`HTN.TMEnc.sizeOn_fullFragment_le_log`** — a closed-form bound on `HTN.Domain.sizeOn` of the
  encoded domain, polynomial in the size of the machine and the input and *logarithmic* in the
  time bound `K`; since `K` is exponential in the input, this is the polynomial size statement
  of the encoding.
-/

namespace HTN

namespace TMEnc

open scoped Classical

open TM

variable {Q Γ : Type}

/-! ### The compound tasks that are used -/

/-- The three synchronisation channels. -/
noncomputable def syncFinset : Finset SyncKind := {.head, .check, .sync}

@[simp] lemma mem_syncFinset (x : SyncKind) : x ∈ syncFinset := by
  cases x <;> simp [syncFinset]

/-- The three head movements. -/
noncomputable def moveFinset : Finset Move := {.left, .stay, .right}

@[simp] lemma mem_moveFinset (m : Move) : m ∈ moveFinset := by
  cases m <;> simp [moveFinset]

/-- The counts occurring in the counting tasks of the encoding: `K`, `K+1`, `K+2` and
`K - |w|`, together with all counts reachable from them by halving. -/
noncomputable def countFinset (K n : ℕ) : Finset ℕ :=
  halvingClosure K ∪ halvingClosure (K + 1) ∪ halvingClosure (K + 2) ∪ halvingClosure (K - n)

lemma card_countFinset_le (K n : ℕ) :
    (countFinset K n).card ≤ (2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) +
      (2 * Nat.log 2 (K + 2) + 2) + (2 * Nat.log 2 (K - n) + 2) := by
  have h1 := card_halvingClosure_le K
  have h2 := card_halvingClosure_le (K + 1)
  have h3 := card_halvingClosure_le (K + 2)
  have h4 := card_halvingClosure_le (K - n)
  have hu : (countFinset K n).card ≤ (halvingClosure K).card + (halvingClosure (K + 1)).card +
      (halvingClosure (K + 2)).card + (halvingClosure (K - n)).card := by
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ le_rfl)
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ le_rfl)
    exact Finset.card_union_le _ _
  omega

/-- The counts are closed under halving. -/
lemma halvingChild_mem_countFinset {K n k : ℕ} (hk : k ∈ countFinset K n) (hk2 : 2 ≤ k) :
    halvingChild k ∈ countFinset K n := by
  simp only [countFinset, Finset.mem_union] at hk ⊢
  rcases hk with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (halvingClosure_subset_of_mem h
      (halvingChild_mem_halvingClosure hk2))))
  · exact Or.inl (Or.inl (Or.inr (halvingClosure_subset_of_mem h
      (halvingChild_mem_halvingClosure hk2))))
  · exact Or.inl (Or.inr (halvingClosure_subset_of_mem h
      (halvingChild_mem_halvingClosure hk2)))
  · exact Or.inr (halvingClosure_subset_of_mem h (halvingChild_mem_halvingClosure hk2))

/-- The indices of the waiting tasks `wait^i` that the encoding uses: `K` (the counting cycle of
`check`), `1` (the one-cell delay of the odd rule for `checkers^i`) and every index reachable
from `K + 1` by halving (the delays `i/2` and `i - 1` of the two rules for `checkers^i`). -/
noncomputable def waitNFinset (K : ℕ) : Finset ℕ :=
  insert K (insert 1 (halvingClosure (K + 1)))

/-- The indices of the checker tasks `checkers^i` that the encoding uses. -/
noncomputable def checkerFinset (K : ℕ) : Finset ℕ := insert 0 (insert 1 (halvingClosure (K + 1)))

/-- The tape symbols the encoding writes: the separator `#`, the blank and the input symbols. -/
noncomputable def symFinset (N : NTM Q Γ) (w : List Γ) : Finset (Option Γ) :=
  insert none ((insert N.blank w.toFinset).image some)

/-- The tasks that are counted by the counting tasks `C^k_t` of the encoding. -/
noncomputable def cSeqBase (N : NTM Q Γ) : Finset (TMTask Q Γ) :=
  {TMTask.acquire .check, TMTask.acquire .sync, TMTask.produce, TMTask.waitCell,
   TMTask.noHeadCell, TMTask.heads, TMTask.transitionAndCheck, TMTask.tapeProduce,
   TMTask.produceSym (some N.blank)}

/-- The compound tasks of the encoded domain that the construction uses. -/
noncomputable def taskFinset (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Finset (TMTask Q Γ) :=
  syncFinset.image TMTask.acquire ∪
  syncFinset.image TMTask.release ∪
  ({TMTask.produce, TMTask.tapeProduce, TMTask.waitCell, TMTask.chk, TMTask.headCell,
    TMTask.noHeadCell, TMTask.heads, TMTask.transition, TMTask.transitionAndCheck,
    TMTask.produceInit, TMTask.done, TMTask.sI} : Finset (TMTask Q Γ)) ∪
  (symFinset N w).image TMTask.produceSym ∪
  (waitNFinset K).image TMTask.waitN ∪
  (checkerFinset K).image TMTask.checkers ∪
  (Finset.range (w.length + 1)).image TMTask.produceWord ∪
  ((cSeqBase N) ×ˢ (countFinset K w.length)).image (fun p => TMTask.cSeq p.1 p.2) ∪
  ((waitNFinset K) ×ˢ (countFinset K w.length)).image
    (fun p => TMTask.cPar (TMTask.waitN p.1) p.2)

section Membership

variable {N : NTM Q Γ} {w : List Γ} {K : ℕ}

@[simp] lemma acquire_mem_taskFinset (x : SyncKind) :
    TMTask.acquire x ∈ taskFinset N w K := by simp [taskFinset]

@[simp] lemma release_mem_taskFinset (x : SyncKind) :
    TMTask.release x ∈ taskFinset N w K := by simp [taskFinset]

@[simp] lemma produce_mem_taskFinset : TMTask.produce ∈ taskFinset N w K := by simp [taskFinset]

@[simp] lemma tapeProduce_mem_taskFinset : TMTask.tapeProduce ∈ taskFinset N w K := by
  simp [taskFinset]

@[simp] lemma waitCell_mem_taskFinset : TMTask.waitCell ∈ taskFinset N w K := by
  simp [taskFinset]

@[simp] lemma chk_mem_taskFinset : TMTask.chk ∈ taskFinset N w K := by simp [taskFinset]

@[simp] lemma headCell_mem_taskFinset : TMTask.headCell ∈ taskFinset N w K := by
  simp [taskFinset]

@[simp] lemma noHeadCell_mem_taskFinset : TMTask.noHeadCell ∈ taskFinset N w K := by
  simp [taskFinset]

@[simp] lemma heads_mem_taskFinset : TMTask.heads ∈ taskFinset N w K := by simp [taskFinset]

@[simp] lemma transition_mem_taskFinset : TMTask.transition ∈ taskFinset N w K := by
  simp [taskFinset]

@[simp] lemma transitionAndCheck_mem_taskFinset :
    TMTask.transitionAndCheck ∈ taskFinset N w K := by simp [taskFinset]

@[simp] lemma produceInit_mem_taskFinset : TMTask.produceInit ∈ taskFinset N w K := by
  simp [taskFinset]

@[simp] lemma done_mem_taskFinset : TMTask.done ∈ taskFinset N w K := by simp [taskFinset]

@[simp] lemma sI_mem_taskFinset : TMTask.sI ∈ taskFinset N w K := by simp [taskFinset]

lemma produceSym_mem_taskFinset {c : Option Γ} (hc : c ∈ symFinset N w) :
    TMTask.produceSym c ∈ taskFinset N w K := by simp [taskFinset, hc]

@[simp] lemma produceSym_none_mem_taskFinset :
    TMTask.produceSym none ∈ taskFinset N w K :=
  produceSym_mem_taskFinset (by simp [symFinset])

@[simp] lemma produceSym_blank_mem_taskFinset :
    TMTask.produceSym (some N.blank) ∈ taskFinset N w K :=
  produceSym_mem_taskFinset (by simp [symFinset])

lemma waitN_mem_taskFinset {i : ℕ} (hi : i ∈ waitNFinset K) :
    TMTask.waitN i ∈ taskFinset N w K := by simp [taskFinset, hi]

lemma checkers_mem_taskFinset {i : ℕ} (hi : i ∈ checkerFinset K) :
    TMTask.checkers i ∈ taskFinset N w K := by simp [taskFinset, hi]

lemma produceWord_mem_taskFinset {i : ℕ} (hi : i ≤ w.length) :
    TMTask.produceWord i ∈ taskFinset N w K := by
  simp only [taskFinset, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  simp
  omega

lemma cSeq_mem_taskFinset {t : TMTask Q Γ} {k : ℕ} (ht : t ∈ cSeqBase N)
    (hk : k ∈ countFinset K w.length) : TMTask.cSeq t k ∈ taskFinset N w K :=
  Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, hk⟩, rfl⟩))

/-- The unordered counting tasks that the encoding uses are the parallel blocks of waiting
chains of the two recursive rules for `checkers^i`. -/
lemma cPar_waitN_mem_taskFinset {m k : ℕ} (hm : m ∈ waitNFinset K)
    (hk : k ∈ countFinset K w.length) :
    TMTask.cPar (TMTask.waitN m) k ∈ taskFinset N w K :=
  Finset.mem_union_right _ (Finset.mem_image.2 ⟨(m, k), Finset.mem_product.2 ⟨hm, hk⟩, rfl⟩)

lemma of_cSeq_mem_taskFinset {t : TMTask Q Γ} {k : ℕ} (h : TMTask.cSeq t k ∈ taskFinset N w K) :
    t ∈ cSeqBase N ∧ k ∈ countFinset K w.length := by
  simp only [taskFinset, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_range, Prod.exists] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h)) | h <;>
    first
      | (exfalso; revert h; simp; done)
      | (obtain ⟨a, b, hab, hq⟩ := h
         cases hq
         exact hab)

lemma of_waitN_mem_taskFinset {i : ℕ} (h : TMTask.waitN i ∈ taskFinset N w K) :
    i ∈ waitNFinset K := by
  simp only [taskFinset, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_range, Prod.exists] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h)) | h <;>
    first
      | (exfalso; revert h; simp; done)
      | (obtain ⟨a, ha, hq⟩ := h
         cases hq
         exact ha)

lemma of_checkers_mem_taskFinset {i : ℕ} (h : TMTask.checkers i ∈ taskFinset N w K) :
    i ∈ checkerFinset K := by
  simp only [taskFinset, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_range, Prod.exists] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h)) | h <;>
    first
      | (exfalso; revert h; simp; done)
      | (obtain ⟨a, ha, hq⟩ := h
         cases hq
         exact ha)

lemma of_produceWord_mem_taskFinset {i : ℕ} (h : TMTask.produceWord i ∈ taskFinset N w K) :
    i ≤ w.length := by
  simp only [taskFinset, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_range, Prod.exists] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h)) | h <;>
    first
      | (exfalso; revert h; simp; done)
      | (obtain ⟨a, ha, hq⟩ := h
         cases hq
         omega)

end Membership

/-! ### The set of used tasks is closed under the method bodies -/

section Closure

variable {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- Halving any positive number eventually reaches `1`. -/
lemma one_mem_halvingClosure : ∀ {k : ℕ}, 1 ≤ k → 1 ∈ halvingClosure k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      match k with
      | 0 => intro h; omega
      | 1 => intro _; simp
      | (j + 2) =>
          intro _
          rw [halvingClosure_succ_succ]
          refine Finset.mem_insert_of_mem ?_
          split_ifs with he
          · exact ih ((j + 2) / 2) (by omega) (by omega)
          · exact ih (j + 1) (by omega) (by omega)

lemma waitNFinset_subset_countFinset (n : ℕ) :
    waitNFinset K ⊆ countFinset K n := by
  intro i hi
  simp only [waitNFinset, Finset.mem_insert] at hi
  rcases hi with rfl | rfl | hi
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (self_mem_halvingClosure _)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (one_mem_halvingClosure (by omega))))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hi))

lemma halvingClosure_succ_subset_checkerFinset :
    halvingClosure (K + 1) ⊆ checkerFinset K := fun _ hi =>
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)

lemma halvingClosure_succ_subset_countFinset (n : ℕ) :
    halvingClosure (K + 1) ⊆ countFinset K n := fun _ hi =>
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hi))

/-- The only unordered counting tasks the encoding uses count waiting chains. -/
lemma of_cPar_mem_taskFinset {t : TMTask Q Γ} {k : ℕ} (h : TMTask.cPar t k ∈ taskFinset N w K) :
    ∃ m ∈ waitNFinset K, t = TMTask.waitN m ∧ k ∈ countFinset K w.length := by
  simp only [taskFinset, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_range, Prod.exists] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h)) | h
  all_goals first
    | (exfalso; revert h; simp; done)
    | (obtain ⟨a, b, ⟨ha, hb⟩, hq⟩ := h
       cases hq
       exact ⟨a, ha, rfl, hb⟩)

lemma getD_mem_symFinset (i : ℕ) :
    (some (w.getD i N.blank) : Option Γ) ∈ symFinset N w := by
  have hmem : w.getD i N.blank ∈ insert N.blank w.toFinset := by
    rcases lt_or_ge i w.length with hi | hi
    · refine Finset.mem_insert_of_mem ?_
      rw [List.getD_eq_getElem _ _ hi]
      simp
    · rw [List.getD_eq_default _ _ hi]
      exact Finset.mem_insert_self _ _
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hmem)

/-- **No decomposition leaves `taskFinset`**: every compound task occurring in the body of a
method of a task of `taskFinset` is again in `taskFinset`. -/
lemma mem_taskFinset_of_mem_bodies {t : TMTask Q Γ} (ht : t ∈ taskFinset N w K)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodies N w K t)
    {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) : c ∈ taskFinset N w K := by
  have hK : K ∈ countFinset K w.length :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (self_mem_halvingClosure _)))
  have hK1 : K + 1 ∈ countFinset K w.length :=
    halvingClosure_succ_subset_countFinset _ (self_mem_halvingClosure _)
  have hK2 : K + 2 ∈ countFinset K w.length :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (self_mem_halvingClosure _))
  have hKw : K - w.length ∈ countFinset K w.length :=
    Finset.mem_union_right _ (self_mem_halvingClosure _)
  cases t with
  | acquire x =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      revert hc; simp
  | release x =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      revert hc; simp
  | produce =>
      obtain ⟨d, rfl⟩ := hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, false_or, reduceCtorEq, Sum.inr.injEq] at hc
      try casesm* _ ∨ _
      all_goals subst_vars
      · exact acquire_mem_taskFinset _
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK1
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK1
  | produceSym d =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, false_or, reduceCtorEq, Sum.inr.injEq] at hc
      try casesm* _ ∨ _
      all_goals subst_vars
      · exact acquire_mem_taskFinset _
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK1
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK1
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      try casesm* _ ∨ _
      all_goals subst_vars
      · exact produceSym_none_mem_taskFinset
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      try casesm* _ ∨ _
      all_goals subst_vars
      all_goals exact release_mem_taskFinset _
  | waitN i =>
      have hi := of_waitN_mem_taskFinset ht
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      subst hc
      exact cSeq_mem_taskFinset (by simp [cSeqBase])
        (waitNFinset_subset_countFinset (K := K) w.length hi)
  | chk =>
      obtain ⟨d, rfl⟩ := hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, false_or, reduceCtorEq, Sum.inr.injEq] at hc
      try casesm* _ ∨ _
      all_goals subst_vars
      · exact release_mem_taskFinset _
      · exact waitN_mem_taskFinset (Finset.mem_insert_self _ _)
      · exact release_mem_taskFinset _
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      revert hc; simp
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      revert hc; simp
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      try casesm* _ ∨ _
      all_goals subst_vars
      · exact noHeadCell_mem_taskFinset
      · exact headCell_mem_taskFinset
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK
  | transition =>
      obtain ⟨q, q', c₁, c₂, mv, -, rfl⟩ := hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.mem_replicate, false_or, reduceCtorEq,
        Sum.inr.injEq] at hc
      try casesm* _ ∧ _, _ ∨ _
      all_goals subst_vars
      all_goals exact acquire_mem_taskFinset _
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;>
        (simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, false_or, reduceCtorEq, Sum.inr.injEq] at hc
         try casesm* _ ∨ _
         all_goals subst_vars
         all_goals first
           | exact transition_mem_taskFinset
           | exact chk_mem_taskFinset)
  | checkers i =>
      have hi := of_checkers_mem_taskFinset ht
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst hls; revert hc; simp
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        try casesm* _ ∨ _
        all_goals subst_vars
        · exact release_mem_taskFinset _
        · exact chk_mem_taskFinset
        · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK
        · exact release_mem_taskFinset _
      · -- `i` even and at least two
        have h2 : 2 ≤ i := by omega
        have hmem : i ∈ halvingClosure (K + 1) := by
          simp only [checkerFinset, Finset.mem_insert] at hi
          rcases hi with rfl | rfl | hi
          · omega
          · omega
          · exact hi
        have hchild : halvingChild i = i / 2 := by simp [halvingChild, he]
        have hhalf : i / 2 ∈ halvingClosure (K + 1) :=
          hchild ▸ halvingClosure_subset_of_mem hmem (halvingChild_mem_halvingClosure h2)
        simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        try casesm* _ ∨ _
        all_goals subst_vars
        all_goals first
          | exact cPar_waitN_mem_taskFinset
              (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hhalf))
              (halvingClosure_succ_subset_countFinset _ hhalf)
          | exact checkers_mem_taskFinset (halvingClosure_succ_subset_checkerFinset hhalf)
      · -- `i` odd and at least three
        have h2 : 2 ≤ i := by omega
        have hmem : i ∈ halvingClosure (K + 1) := by
          simp only [checkerFinset, Finset.mem_insert] at hi
          rcases hi with rfl | rfl | hi
          · omega
          · omega
          · exact hi
        have hchild : halvingChild i = i - 1 := by simp [halvingChild, he]
        have hpred : i - 1 ∈ halvingClosure (K + 1) :=
          hchild ▸ halvingClosure_subset_of_mem hmem (halvingChild_mem_halvingClosure h2)
        have hwait : i - 1 ∈ waitNFinset K :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hpred)
        simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        try casesm* _ ∨ _
        all_goals subst_vars
        all_goals first
          | exact cPar_waitN_mem_taskFinset
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
              (halvingClosure_succ_subset_countFinset _ hpred)
          | exact checkers_mem_taskFinset (halvingClosure_succ_subset_checkerFinset hpred)
          | exact checkers_mem_taskFinset (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          | exact waitN_mem_taskFinset hwait
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      try casesm* _ ∨ _
      all_goals subst_vars
      · exact produceSym_none_mem_taskFinset
      · exact produceWord_mem_taskFinset (Nat.zero_le _)
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hKw
  | produceWord i =>
      have hi := of_produceWord_mem_taskFinset ht
      simp only [bodies] at hls
      split_ifs at hls with hlt <;>
        (simp only [Set.mem_singleton_iff] at hls; subst hls
         simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
           List.not_mem_nil, or_false, Sum.inr.injEq] at hc
         try casesm* _ ∨ _
         all_goals subst_vars
         all_goals first
           | exact produceSym_mem_taskFinset (getD_mem_symFinset _)
           | exact produceWord_mem_taskFinset (by omega))
  | done =>
      obtain ⟨f, -, rfl⟩ := hls
      revert hc; simp
  | cSeq t k =>
      obtain ⟨htb, hk⟩ := of_cSeq_mem_taskFinset ht
      have hbase' : t ∈ taskFinset N w K := by
        simp only [cSeqBase, Finset.mem_insert, Finset.mem_singleton] at htb
        rcases htb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst hls; revert hc; simp
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        subst hc
        exact hbase'
      · have h2 : 2 ≤ k := by omega
        have hchild : halvingChild k = k / 2 := by simp [halvingChild, he]
        have hhalf : k / 2 ∈ countFinset K w.length :=
          hchild ▸ halvingChild_mem_countFinset hk h2
        simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        try casesm* _ ∨ _
        all_goals subst_vars
        all_goals exact cSeq_mem_taskFinset htb hhalf
      · have h2 : 2 ≤ k := by omega
        have hchild : halvingChild k = k - 1 := by simp [halvingChild, he]
        have hpred : k - 1 ∈ countFinset K w.length :=
          hchild ▸ halvingChild_mem_countFinset hk h2
        simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        try casesm* _ ∨ _
        all_goals subst_vars
        all_goals first
          | exact hbase'
          | exact cSeq_mem_taskFinset htb hpred
  | cPar t k =>
      obtain ⟨m, hm, rfl, hk⟩ := of_cPar_mem_taskFinset ht
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst hls; revert hc; simp
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        subst hc
        exact waitN_mem_taskFinset hm
      · have h2 : 2 ≤ k := by omega
        have hchild : halvingChild k = k / 2 := by simp [halvingChild, he]
        have hhalf : k / 2 ∈ countFinset K w.length :=
          hchild ▸ halvingChild_mem_countFinset hk h2
        simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        try casesm* _ ∨ _
        all_goals subst_vars
        all_goals exact cPar_waitN_mem_taskFinset hm hhalf
      · have h2 : 2 ≤ k := by omega
        have hchild : halvingChild k = k - 1 := by simp [halvingChild, he]
        have hpred : k - 1 ∈ countFinset K w.length :=
          hchild ▸ halvingChild_mem_countFinset hk h2
        simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
        try casesm* _ ∨ _
        all_goals subst_vars
        all_goals first
          | exact waitN_mem_taskFinset hm
          | exact cPar_waitN_mem_taskFinset hm hpred
  | sI => exact absurd hls (Set.notMem_empty _)

/-- The tasks of the initial method (the one for `sI`) are used tasks as well. -/
lemma mem_taskFinset_of_mem_initNet {c : TMTask Q Γ} {p : ℕ × ℕ}
    (hp : p ∈ (initNet (Q := Q) (Γ := Γ) K).T)
    (hc : (initNet (Q := Q) (Γ := Γ) K).α p = Sum.inr c) : c ∈ taskFinset N w K := by
  have hK : K ∈ countFinset K w.length :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (self_mem_halvingClosure _)))
  have hmem := TaskNetwork.gridTail_α_mem_flatten (ls := initChains (Q := Q) (Γ := Γ) K)
    (tl := [Sum.inr TMTask.done]) hp
  rw [show (initNet (Q := Q) (Γ := Γ) K) =
    TaskNetwork.gridTail (initChains (Q := Q) (Γ := Γ) K) [Sum.inr TMTask.done] from rfl] at hc
  rw [hc] at hmem
  simp only [initChains, List.cons_append, List.nil_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false, false_or,
    reduceCtorEq, Sum.inr.injEq] at hmem
  try casesm* _ ∨ _
  all_goals subst_vars
  all_goals first
    | exact headCell_mem_taskFinset
    | exact produceInit_mem_taskFinset
    | exact done_mem_taskFinset
    | exact checkers_mem_taskFinset (halvingClosure_succ_subset_checkerFinset
        (self_mem_halvingClosure _))
    | exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK

end Closure

/-! ### The method bodies as `Finset`s -/

section Bodies

variable (N : NTM Q Γ) (qs : Finset Q) (gs : Finset Γ) (w : List Γ) (K : ℕ)

/-- The tape symbols of the fragment (including the separator `#`). -/
noncomputable def symsOf : Finset (Option Γ) := insert none (gs.image some)

lemma card_symsOf_le : (symsOf gs).card ≤ gs.card + 1 :=
  le_trans (Finset.card_insert_le _ _) (by simpa using Nat.add_le_add_right Finset.card_image_le 1)

/-- The transitions of the machine, restricted to the given states and symbols. -/
noncomputable def transFinset : Finset (Q × Γ × Q × Γ × Move) :=
  (qs ×ˢ gs ×ˢ qs ×ˢ gs ×ˢ moveFinset).filter
    (fun p => (p.2.2.1, p.2.2.2.1, p.2.2.2.2) ∈ N.step p.1 p.2.1)

lemma card_transFinset_le :
    (transFinset N qs gs).card ≤ qs.card * (gs.card * (qs.card * (gs.card * 3))) := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp only [Finset.card_product]
  have : moveFinset.card ≤ 3 := le_trans (Finset.card_insert_le _ _)
    (by simp)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_left _ this)))

/-- The bodies of one compound task of the encoded domain, as a `Finset`; it mirrors
`HTN.TMEnc.bodies`, with the families indexed by the machine restricted to the given states and
symbols. -/
noncomputable def bodyFinset :
    TMTask Q Γ → Finset (List (List (TMAct Q Γ ⊕ TMTask Q Γ)))
  | .acquire x => {[[Sum.inl (.call x), Sum.inl (.wait x)]]}
  | .release x => {[[Sum.inl (.start x), Sum.inl (.respond x)]]}
  | .produce => (symsOf gs).image fun c =>
      [[Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire .head),
        Sum.inr (TMTask.cSeq (.acquire .check) (K + 1)),
        Sum.inr (TMTask.cSeq (.acquire .sync) (K + 1))]]
  | .produceSym c => {[[Sum.inl (.assert c), Sum.inr (.acquire .head),
      Sum.inr (.cSeq (.acquire .check) (K + 1)), Sum.inr (.cSeq (.acquire .sync) (K + 1))]]}
  | .tapeProduce => {[[Sum.inr (.produceSym none), Sum.inr (.cSeq .produce K)]]}
  | .waitCell => {[[Sum.inr (.release .check), Sum.inr (.release .sync)]]}
  | .waitN i => {[[Sum.inr (.cSeq .waitCell i)]]}
  | .chk => (symsOf gs).image fun c =>
      [[Sum.inl (TMAct.check (.sym c)), Sum.inr (TMTask.release .sync),
        Sum.inr (TMTask.waitN K), Sum.inr (TMTask.release .check),
        Sum.inl (TMAct.check (.sym c))]]
  | .headCell => {[[Sum.inl (.start .head), Sum.inl .assertHead, Sum.inl (.respond .head)]]}
  | .noHeadCell => {[[Sum.inl (.start .head), Sum.inl .retractHead, Sum.inl (.respond .head)]]}
  | .heads => {[[Sum.inr .noHeadCell, Sum.inr .headCell, Sum.inr (.cSeq .noHeadCell K)]]}
  | .transition => (transFinset N qs gs).image fun p =>
      [Sum.inl (TMAct.step p.1 (some p.2.1) p.2.2.1 (some p.2.2.2.1)) ::
        List.replicate (moveExtra p.2.2.2.2) (Sum.inr (TMTask.acquire .head))]
  | .transitionAndCheck => {[[Sum.inr .transition, Sum.inr .chk]],
      [[Sum.inl (.check .noHead), Sum.inr .chk]]}
  | .checkers i =>
      if i = 0 then {[]}
      else if i = 1 then {[[Sum.inr (.release .check), Sum.inr .chk,
        Sum.inr (.cSeq .transitionAndCheck K), Sum.inr (.release .sync)]]}
      else if i % 2 = 0 then
        {[[Sum.inr (.cPar (.waitN (i / 2)) (i / 2)), Sum.inr (.checkers (i / 2))],
          [Sum.inr (.checkers (i / 2)), Sum.inr (.cPar (.waitN (i / 2)) (i / 2))]]}
      else
        {[[Sum.inr (.cPar (.waitN 1) (i - 1)), Sum.inr (.checkers (i - 1))],
          [Sum.inr (.checkers 1), Sum.inr (.waitN (i - 1))]]}
  | .produceInit => {[[Sum.inr (.produceSym none), Sum.inr (.produceWord 0),
      Sum.inr (.cSeq (.produceSym (some N.blank)) (K - w.length))]]}
  | .produceWord i =>
      if i + 1 < w.length then
        {[[Sum.inr (.produceSym (some (w.getD i N.blank))), Sum.inr (.produceWord (i + 1))]]}
      else {[[Sum.inr (.produceSym (some (w.getD i N.blank)))]]}
  | .done => (qs.filter (fun f => f ∈ N.accept)).image fun f =>
      [[Sum.inl (TMAct.check (.st f))]]
  | .cSeq t k =>
      if k = 0 then {[]}
      else if k = 1 then {[[Sum.inr t]]}
      else if k % 2 = 0 then {[[Sum.inr (.cSeq t (k / 2)), Sum.inr (.cSeq t (k / 2))]]}
      else {[[Sum.inr t, Sum.inr (.cSeq t (k - 1))]]}
  | .cPar t k =>
      if k = 0 then {[]}
      else if k = 1 then {[[Sum.inr t]]}
      else if k % 2 = 0 then {[[Sum.inr (.cPar t (k / 2))], [Sum.inr (.cPar t (k / 2))]]}
      else {[[Sum.inr t], [Sum.inr (.cPar t (k - 1))]]}
  | .sI => ∅

variable {N qs gs w K}

/-- Every element of `HTN.TMEnc.bodyFinset` really is a method body of the encoded domain. -/
lemma bodyFinset_subset_bodies (t : TMTask Q Γ) :
    ↑(bodyFinset N qs gs w K t) ⊆ bodies N w K t := by
  intro ls hls
  simp only [Finset.mem_coe] at hls
  cases t with
  | acquire x => simpa [bodyFinset, bodies] using hls
  | release x => simpa [bodyFinset, bodies] using hls
  | produce =>
      simp only [bodyFinset, Finset.mem_image] at hls
      obtain ⟨c, -, rfl⟩ := hls
      exact ⟨c, rfl⟩
  | produceSym c => simpa [bodyFinset, bodies] using hls
  | tapeProduce => simpa [bodyFinset, bodies] using hls
  | waitCell => simpa [bodyFinset, bodies] using hls
  | waitN i => simpa [bodyFinset, bodies] using hls
  | chk =>
      simp only [bodyFinset, Finset.mem_image] at hls
      obtain ⟨c, -, rfl⟩ := hls
      exact ⟨c, rfl⟩
  | headCell => simpa [bodyFinset, bodies] using hls
  | noHeadCell => simpa [bodyFinset, bodies] using hls
  | heads => simpa [bodyFinset, bodies] using hls
  | transition =>
      simp only [bodyFinset, Finset.mem_image] at hls
      obtain ⟨p, hp, rfl⟩ := hls
      simp only [transFinset, Finset.mem_filter] at hp
      exact ⟨p.1, p.2.2.1, p.2.1, p.2.2.2.1, p.2.2.2.2, hp.2, rfl⟩
  | transitionAndCheck => simpa [bodyFinset, bodies] using hls
  | checkers i =>
      simp only [bodyFinset, bodies] at hls ⊢
      split_ifs at hls ⊢ <;> simpa using hls
  | produceInit => simpa [bodyFinset, bodies] using hls
  | produceWord i =>
      simp only [bodyFinset, bodies] at hls ⊢
      split_ifs at hls ⊢ <;> simpa using hls
  | done =>
      simp only [bodyFinset, Finset.mem_image, Finset.mem_filter] at hls
      obtain ⟨f, ⟨-, hf⟩, rfl⟩ := hls
      exact ⟨f, hf, rfl⟩
  | cSeq t k =>
      simp only [bodyFinset, bodies] at hls ⊢
      split_ifs at hls ⊢ <;> simpa using hls
  | cPar t k =>
      simp only [bodyFinset, bodies] at hls ⊢
      split_ifs at hls ⊢ <;> simpa using hls
  | sI => simp only [bodyFinset, Finset.notMem_empty] at hls

/-- If the machine's states and symbols are covered, `HTN.TMEnc.bodyFinset` contains *all*
method bodies of the encoded domain. -/
lemma bodies_subset_bodyFinset (hqs : ∀ q : Q, q ∈ qs) (hgs : ∀ c : Γ, c ∈ gs)
    (t : TMTask Q Γ) : bodies N w K t ⊆ ↑(bodyFinset N qs gs w K t) := by
  have hsym : ∀ c : Option Γ, c ∈ symsOf gs := by
    intro c
    cases c with
    | none => exact Finset.mem_insert_self _ _
    | some c => exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hgs c))
  intro ls hls
  simp only [Finset.mem_coe]
  cases t with
  | acquire x => simpa [bodyFinset] using hls
  | release x => simpa [bodyFinset] using hls
  | produce =>
      obtain ⟨c, rfl⟩ := hls
      exact Finset.mem_image_of_mem _ (hsym c)
  | produceSym c => simpa [bodyFinset] using hls
  | tapeProduce => simpa [bodyFinset] using hls
  | waitCell => simpa [bodyFinset] using hls
  | waitN i => simpa [bodyFinset] using hls
  | chk =>
      obtain ⟨c, rfl⟩ := hls
      exact Finset.mem_image_of_mem _ (hsym c)
  | headCell => simpa [bodyFinset] using hls
  | noHeadCell => simpa [bodyFinset] using hls
  | heads => simpa [bodyFinset] using hls
  | transition =>
      obtain ⟨q, q', c₁, c₂, mv, hstep, rfl⟩ := hls
      have hmem : (q, c₁, q', c₂, mv) ∈ transFinset N qs gs := by
        simp only [transFinset, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hqs q, hgs c₁, hqs q', hgs c₂, mem_moveFinset mv⟩, hstep⟩
      exact Finset.mem_image_of_mem _ hmem
  | transitionAndCheck => simpa [bodyFinset] using hls
  | checkers i =>
      simp only [bodies] at hls
      simp only [bodyFinset]
      split_ifs at hls ⊢ <;> simpa using hls
  | produceInit => simpa [bodyFinset] using hls
  | produceWord i =>
      simp only [bodies] at hls
      simp only [bodyFinset]
      split_ifs at hls ⊢ <;> simpa using hls
  | done =>
      obtain ⟨f, hf, rfl⟩ := hls
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hqs f, hf⟩)
  | cSeq t k =>
      simp only [bodies] at hls
      simp only [bodyFinset]
      split_ifs at hls ⊢ <;> simpa using hls
  | cPar t k =>
      simp only [bodies] at hls
      simp only [bodyFinset]
      split_ifs at hls ⊢ <;> simpa using hls
  | sI => exact absurd hls (Set.notMem_empty _)

/-- Every compound task of the encoded domain has at most `B` bodies, where `B` counts the
transitions, the tape symbols and the accepting states of the machine. -/
lemma card_bodyFinset_le (t : TMTask Q Γ) :
    (bodyFinset N qs gs w K t).card ≤
      (gs.card + 1) + qs.card * (gs.card * (qs.card * (gs.card * 3))) + qs.card + 2 := by
  have hpair : ∀ x y : List (List (TMAct Q Γ ⊕ TMTask Q Γ)),
      ({x, y} : Finset _).card ≤ 2 :=
    fun x y => le_trans (Finset.card_insert_le _ _) (by simp)
  cases t with
  | acquire x => simp only [bodyFinset]; simp
  | release x => simp only [bodyFinset]; simp
  | produce =>
      exact le_trans (le_trans Finset.card_image_le (card_symsOf_le gs)) (by omega)
  | produceSym c => simp only [bodyFinset]; simp
  | tapeProduce => simp only [bodyFinset]; simp
  | waitCell => simp only [bodyFinset]; simp
  | waitN i => simp only [bodyFinset]; simp
  | chk => exact le_trans (le_trans Finset.card_image_le (card_symsOf_le gs)) (by omega)
  | headCell => simp only [bodyFinset]; simp
  | noHeadCell => simp only [bodyFinset]; simp
  | heads => simp only [bodyFinset]; simp
  | transition =>
      exact le_trans (le_trans Finset.card_image_le (card_transFinset_le N qs gs)) (by omega)
  | transitionAndCheck =>
      simp only [bodyFinset]
      exact le_trans (hpair _ _) (by omega)
  | checkers i =>
      simp only [bodyFinset]
      split_ifs <;> simp
  | produceInit => simp only [bodyFinset]; simp
  | produceWord i => simp only [bodyFinset]; split_ifs <;> simp
  | done =>
      refine le_trans Finset.card_image_le ?_
      exact le_trans (Finset.card_filter_le _ _) (by omega)
  | cSeq t k => simp only [bodyFinset]; split_ifs <;> simp
  | cPar t k =>
      simp only [bodyFinset]
      split_ifs <;> simp
  | sI => simp only [bodyFinset]; simp

end Bodies

/-! ### The methods, the facts and the operators of the encoded domain -/

section Fragment

variable (N : NTM Q Γ) (qs : Finset Q) (gs : Finset Γ) (w : List Γ) (K : ℕ)

/-- Auxiliary: cardinality bounds add along unions. -/
private lemma card_union_le_of_le {α : Type*} [DecidableEq α] {s t : Finset α} {m n : ℕ}
    (hs : s.card ≤ m) (ht : t.card ≤ n) : (s ∪ t).card ≤ m + n :=
  le_trans (Finset.card_union_le _ _) (Nat.add_le_add hs ht)

private lemma card_pair_le {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 :=
  le_trans (Finset.card_insert_le _ _) (by simp)

lemma card_syncFinset_le : syncFinset.card ≤ 3 := by
  simp [syncFinset]

lemma card_symFinset_le : (symFinset N w).card ≤ w.length + 2 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h1 : ((insert N.blank w.toFinset).image (some : Γ → Option Γ)).card ≤ w.length + 1 :=
    le_trans Finset.card_image_le
      (le_trans (Finset.card_insert_le _ _)
        (Nat.add_le_add_right (List.toFinset_card_le w) 1))
  omega

lemma card_cSeqBase_le : (cSeqBase N).card ≤ 9 := by
  simp [cSeqBase]

lemma card_waitNFinset_le : (waitNFinset K).card ≤ (halvingClosure (K + 1)).card + 2 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  have := Finset.card_insert_le (1 : ℕ) (halvingClosure (K + 1))
  omega

lemma card_checkerFinset_le : (checkerFinset K).card ≤ (halvingClosure (K + 1)).card + 2 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  have := Finset.card_insert_le (1 : ℕ) (halvingClosure (K + 1))
  omega

/-- **The encoding uses at most `25 + 2·|w| + 13·|counts| + |counts|²` compound tasks**, where
`|counts|` is logarithmic in the time bound `K` (`HTN.TMEnc.card_countFinset_le`); the quadratic
term counts the parallel waiting blocks `C_k^{wait^m}` of the rules for `checkers^i`. -/
lemma card_taskFinset_le :
    (taskFinset N w K).card ≤
      25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card := by
  have hcnt : (halvingClosure (K + 1)).card ≤ (countFinset K w.length).card :=
    Finset.card_le_card (halvingClosure_succ_subset_countFinset _)
  have hbase : ({TMTask.produce, TMTask.tapeProduce, TMTask.waitCell, TMTask.chk,
      TMTask.headCell, TMTask.noHeadCell, TMTask.heads, TMTask.transition,
      TMTask.transitionAndCheck, TMTask.produceInit, TMTask.done, TMTask.sI} :
      Finset (TMTask Q Γ)).card ≤ 12 := by
    simp
  have H : (taskFinset N w K).card ≤
      3 + 3 + 12 + (w.length + 2) + ((halvingClosure (K + 1)).card + 2) +
        ((halvingClosure (K + 1)).card + 2) + (w.length + 1) +
        (cSeqBase N).card * (countFinset K w.length).card +
        (waitNFinset K).card * (countFinset K w.length).card := by
    simp only [taskFinset]
    repeat refine card_union_le_of_le ?_ ?_
    · exact le_trans Finset.card_image_le card_syncFinset_le
    · exact le_trans Finset.card_image_le card_syncFinset_le
    · exact hbase
    · exact le_trans Finset.card_image_le (card_symFinset_le N w)
    · exact le_trans Finset.card_image_le (card_waitNFinset_le K)
    · exact le_trans Finset.card_image_le (card_checkerFinset_le K)
    · exact le_trans Finset.card_image_le (by simp)
    · exact le_trans Finset.card_image_le (by simp [Finset.card_product])
    · exact le_trans Finset.card_image_le (by simp [Finset.card_product])
  have h9 := card_cSeqBase_le N
  have hmul : (cSeqBase N).card * (countFinset K w.length).card ≤
      9 * (countFinset K w.length).card := Nat.mul_le_mul_right _ h9
  have hwait : (waitNFinset K).card ≤ (countFinset K w.length).card + 2 :=
    le_trans (card_waitNFinset_le K) (by omega)
  have hmul2 : (waitNFinset K).card * (countFinset K w.length).card ≤
      ((countFinset K w.length).card + 2) * (countFinset K w.length).card :=
    Nat.mul_le_mul_right _ hwait
  nlinarith [H, hmul, hmul2, hcnt]

/-- The methods of the encoded domain that the construction uses. -/
noncomputable def methodFinset : Finset (Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)) :=
  ((taskFinset N w K).biUnion fun t =>
    (bodyFinset N qs gs w K t).image fun ls => ⟨t, TaskNetwork.grid ls⟩) ∪
  {⟨TMTask.sI, initNet K⟩}

/-- The facts of the encoded signature. -/
noncomputable def factFinset : Finset (TMFact Q Γ) :=
  (symsOf gs).image TMFact.sym ∪
  qs.image TMFact.st ∪
  ({TMFact.head, TMFact.noHead} : Finset (TMFact Q Γ)) ∪
  syncFinset.image TMFact.stepF ∪
  syncFinset.image TMFact.steppedF

/-- The operators of the encoded signature. -/
noncomputable def opFinset : Finset (TMAct Q Γ) :=
  (symsOf gs).image TMAct.assert ∪
  (factFinset qs gs).image TMAct.check ∪
  syncFinset.image TMAct.call ∪
  syncFinset.image TMAct.start ∪
  syncFinset.image TMAct.respond ∪
  syncFinset.image TMAct.wait ∪
  ({TMAct.assertHead, TMAct.retractHead} : Finset (TMAct Q Γ)) ∪
  ((qs ×ˢ symsOf gs ×ˢ qs ×ˢ symsOf gs).image fun p => TMAct.step p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- The fragment of the encoded signature that the construction uses. -/
noncomputable def fragment : Fragment (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  facts := factFinset qs gs
  ops := opFinset qs gs
  tasks := taskFinset N w K
  methods := methodFinset N qs gs w K

variable {N qs gs w K}

/-- **The methods of the fragment really are methods of the encoded domain.** -/
lemma methodFinset_subset_methods :
    ↑(methodFinset N qs gs w K) ⊆ methods N w K := by
  intro m hm
  simp only [Finset.mem_coe, methodFinset, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_singleton] at hm
  rcases hm with ⟨t, -, ls, hls, rfl⟩ | rfl
  · exact Or.inl ⟨ls, bodyFinset_subset_bodies t hls, rfl⟩
  · exact Or.inr rfl

/-- **Conversely, if the machine is covered, every method of the encoded domain whose decomposed
task is used belongs to the fragment.** -/
lemma mem_methodFinset_of_mem_methods (hqs : ∀ q : Q, q ∈ qs) (hgs : ∀ c : Γ, c ∈ gs)
    {m : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)} (hm : m ∈ methods N w K)
    (ht : m.abstractTask ∈ taskFinset N w K) : m ∈ methodFinset N qs gs w K := by
  rcases hm with ⟨ls, hls, hsub⟩ | hsI
  · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨m.abstractTask, ht, ?_⟩)
    refine Finset.mem_image.2 ⟨ls, bodies_subset_bodyFinset hqs hgs _ hls, ?_⟩
    cases m
    simpa using hsub.symm
  · simp only [Set.mem_singleton_iff] at hsI
    exact Finset.mem_union_right _ (Finset.mem_singleton.2 hsI)

/-- The number of methods used. -/
lemma card_methodFinset_le :
    (methodFinset N qs gs w K).card ≤
      (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) *
        ((gs.card + 1) + qs.card * (gs.card * (qs.card * (gs.card * 3))) + qs.card + 2) + 1 := by
  set B := (gs.card + 1) + qs.card * (gs.card * (qs.card * (gs.card * 3))) + qs.card + 2 with hB
  have hbi : ((taskFinset N w K).biUnion fun t =>
      (bodyFinset N qs gs w K t).image fun ls =>
        (⟨t, TaskNetwork.grid ls⟩ : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ))).card ≤
      (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) * B := by
    calc ((taskFinset N w K).biUnion fun t =>
          (bodyFinset N qs gs w K t).image fun ls =>
            (⟨t, TaskNetwork.grid ls⟩ : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ))).card
        ≤ ∑ t ∈ taskFinset N w K, ((bodyFinset N qs gs w K t).image fun ls =>
            (⟨t, TaskNetwork.grid ls⟩ : Method (ℕ × ℕ) (TMAct Q Γ)
              (TMTask Q Γ))).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ taskFinset N w K, B :=
          Finset.sum_le_sum fun t _ => le_trans Finset.card_image_le (card_bodyFinset_le t)
      _ = (taskFinset N w K).card * B := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) * B :=
          Nat.mul_le_mul_right _ (card_taskFinset_le N w K)
  refine le_trans (Finset.card_union_le _ _) ?_
  simpa using Nat.add_le_add hbi (le_refl 1)

lemma card_factFinset_le :
    (factFinset (Q := Q) qs gs).card ≤ gs.card + qs.card + 9 := by
  have H : (factFinset (Q := Q) qs gs).card ≤
      (gs.card + 1) + qs.card + 2 + 3 + 3 := by
    simp only [factFinset]
    repeat refine card_union_le_of_le ?_ ?_
    · exact le_trans Finset.card_image_le (card_symsOf_le gs)
    · exact Finset.card_image_le
    · exact card_pair_le _ _
    · exact le_trans Finset.card_image_le card_syncFinset_le
    · exact le_trans Finset.card_image_le card_syncFinset_le
  omega

lemma card_opFinset_le :
    (opFinset (Q := Q) qs gs).card ≤
      (gs.card + 1) + (gs.card + qs.card + 9) + 12 + 2 +
        qs.card * ((gs.card + 1) * (qs.card * (gs.card + 1))) := by
  have H : (opFinset (Q := Q) qs gs).card ≤
      (gs.card + 1) + (gs.card + qs.card + 9) + 3 + 3 + 3 + 3 + 2 +
        qs.card * ((symsOf gs).card * (qs.card * (symsOf gs).card)) := by
    simp only [opFinset]
    repeat refine card_union_le_of_le ?_ ?_
    · exact le_trans Finset.card_image_le (card_symsOf_le gs)
    · exact le_trans Finset.card_image_le (card_factFinset_le (qs := qs) (gs := gs))
    · exact le_trans Finset.card_image_le card_syncFinset_le
    · exact le_trans Finset.card_image_le card_syncFinset_le
    · exact le_trans Finset.card_image_le card_syncFinset_le
    · exact le_trans Finset.card_image_le card_syncFinset_le
    · exact card_pair_le _ _
    · exact le_trans Finset.card_image_le (by simp [Finset.card_product])
  have hs := card_symsOf_le gs
  have hmul : qs.card * ((symsOf gs).card * (qs.card * (symsOf gs).card)) ≤
      qs.card * ((gs.card + 1) * (qs.card * (gs.card + 1))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hs (Nat.mul_le_mul_left _ hs))
  omega

end Fragment

/-! ### A closed-form polynomial size bound -/

section Size

variable {Q Γ : Type} [Fintype Q] [Fintype Γ]

omit [Fintype Q] in
private lemma ncard_symSet_le (c : Option Γ) :
    ({f : TMFact Q Γ | ∃ d, f = TMFact.sym d ∧ d ≠ c}).ncard ≤ Nat.card Γ + 1 := by
  have h : {f : TMFact Q Γ | ∃ d, f = TMFact.sym d ∧ d ≠ c} = TMFact.sym '' {d | d ≠ c} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨d, rfl, hne⟩; exact ⟨d, hne, rfl⟩
    · rintro ⟨d, hne, rfl⟩; exact ⟨d, rfl, hne⟩
  rw [h]
  refine le_trans (Set.ncard_image_le (Set.toFinite _)) ?_
  rw [← Set.ncard_univ]
  refine le_trans (Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ) ?_
  rw [Set.ncard_univ]
  simp [Nat.card_eq_fintype_card]

omit [Fintype Q] in
/-- **Every action of the encoded domain has size at most `|Γ| + 9`.** -/
lemma actionSize_le (N : NTM Q Γ) (w : List Γ) (K : ℕ) (a : TMAct Q Γ) :
    (domain N w K).actionSize a ≤ Nat.card Γ + 9 := by
  have htriple : ∀ x y z : TMFact Q Γ, ({x, y, z} : Set (TMFact Q Γ)).ncard ≤ 3 := by
    intro x y z
    refine le_trans (Set.ncard_insert_le _ _) ?_
    have := Set.ncard_insert_le y ({z} : Set (TMFact Q Γ))
    simp only [Set.ncard_singleton] at this
    omega
  simp only [ActionModel.actionSize, domain, actionModel]
  cases a with
  | assert c =>
      simp only [prec, add, del, Set.ncard_empty, Set.ncard_singleton]
      have := ncard_symSet_le (Q := Q) c
      omega
  | check f => simp [prec, add, del]
  | call x => simp [prec, add, del]
  | start x => simp [prec, add, del]
  | respond x => simp [prec, add, del]
  | wait x => simp [prec, add, del]
  | assertHead => simp [prec, add, del]
  | retractHead => simp [prec, add, del]
  | step q c q' c' =>
      simp only [prec, add, del]
      have h1 := htriple (TMFact.head) (TMFact.sym c) (TMFact.st q)
      have h2 : ({TMFact.sym c', TMFact.st q'} : Set (TMFact Q Γ)).ncard ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        simp
      have h3 : ({TMFact.sym c, TMFact.st q} : Set (TMFact Q Γ)).ncard ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        simp
      omega

/-- The fragment of the encoded signature for the whole (finite) machine. -/
noncomputable def fullFragment (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    Fragment (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) :=
  fragment N Finset.univ Finset.univ w K

/-- The closed-form size bound of the Turing-machine encoding: a polynomial in the number `nq`
of states, `ng` of tape symbols, the length `nw` of the input and the number `cnt` of counting
tasks (which is logarithmic in the time bound). -/
def sizeBound (nq ng nw cnt : ℕ) : ℕ :=
  (ng + nq + 9) + (25 + 2 * nw + 13 * cnt + cnt * cnt) +
    ((ng + 1) + (ng + nq + 9) + 12 + 2 + nq * ((ng + 1) * (nq * (ng + 1)))) * (ng + 9) +
    421 * ((25 + 2 * nw + 13 * cnt + cnt * cnt) *
      ((ng + 1) + nq * (ng * (nq * (ng * 3))) + nq + 2) + 1)

/-- **Closed-form polynomial size bound for the Turing-machine encoding.**  The size of the
encoded domain, measured on the part of its signature that the construction uses, is bounded by
`HTN.TMEnc.sizeBound` applied to the size of the machine, the length of the input and the
number of counting tasks; the latter is logarithmic in the time bound `K`
(`HTN.TMEnc.card_countFinset_le`), which is what makes the encoding of an *exponential* time
bound polynomial. -/
theorem sizeOn_fullFragment_le (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    (domain N w K).sizeOn (fullFragment N w K) ≤
      sizeBound (Nat.card Q) (Nat.card Γ) w.length (countFinset K w.length).card := by
  have hcardQ : (Finset.univ : Finset Q).card = Nat.card Q := by simp [Nat.card_eq_fintype_card]
  have hcardG : (Finset.univ : Finset Γ).card = Nat.card Γ := by simp [Nat.card_eq_fintype_card]
  have hfacts : (factFinset (Q := Q) (Γ := Γ) Finset.univ Finset.univ).card ≤
      Nat.card Γ + Nat.card Q + 9 := by
    have := card_factFinset_le (Q := Q) (qs := (Finset.univ : Finset Q))
      (gs := (Finset.univ : Finset Γ))
    rwa [hcardQ, hcardG] at this
  have htasks : (taskFinset N w K).card ≤ 25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card :=
    card_taskFinset_le N w K
  have hops : (opFinset (Q := Q) (Γ := Γ) Finset.univ Finset.univ).card ≤
      (Nat.card Γ + 1) + (Nat.card Γ + Nat.card Q + 9) + 12 + 2 +
        Nat.card Q * ((Nat.card Γ + 1) * (Nat.card Q * (Nat.card Γ + 1))) := by
    have := card_opFinset_le (Q := Q) (qs := (Finset.univ : Finset Q))
      (gs := (Finset.univ : Finset Γ))
    rwa [hcardQ, hcardG] at this
  have hmeth : (methodFinset N Finset.univ Finset.univ w K).card ≤
      (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) *
        ((Nat.card Γ + 1) + Nat.card Q * (Nat.card Γ * (Nat.card Q * (Nat.card Γ * 3))) +
          Nat.card Q + 2) + 1 := by
    have := card_methodFinset_le (N := N) (qs := (Finset.univ : Finset Q))
      (gs := (Finset.univ : Finset Γ)) (w := w) (K := K)
    rwa [hcardQ, hcardG] at this
  have hsumops : ∑ a ∈ opFinset (Q := Q) (Γ := Γ) Finset.univ Finset.univ,
      (domain N w K).actionSize a ≤
      ((Nat.card Γ + 1) + (Nat.card Γ + Nat.card Q + 9) + 12 + 2 +
        Nat.card Q * ((Nat.card Γ + 1) * (Nat.card Q * (Nat.card Γ + 1)))) *
        (Nat.card Γ + 9) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun a _ => actionSize_le N w K a)) ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ hops
  have hsummeth : ∑ m ∈ methodFinset N Finset.univ Finset.univ w K, m.size ≤
      421 * ((25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) *
        ((Nat.card Γ + 1) + Nat.card Q * (Nat.card Γ * (Nat.card Q * (Nat.card Γ * 3))) +
          Nat.card Q + 2) + 1) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 421 (fun m hm => method_size_le
      (methodFinset_subset_methods (Finset.mem_coe.2 hm)))) ?_
    rw [smul_eq_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hmeth
  simp only [Domain.sizeOn, fullFragment, fragment, sizeBound]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hfacts htasks) hsumops) hsummeth

/-- The same bound with the number of counting tasks replaced by its logarithmic estimate. -/
theorem sizeOn_fullFragment_le_log (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    (domain N w K).sizeOn (fullFragment N w K) ≤
      sizeBound (Nat.card Q) (Nat.card Γ) w.length
        ((2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
          (2 * Nat.log 2 (K - w.length) + 2)) := by
  refine le_trans (sizeOn_fullFragment_le N w K) ?_
  have hL := card_countFinset_le K w.length
  unfold sizeBound
  set L := (2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
    (2 * Nat.log 2 (K - w.length) + 2) with hLdef
  have h1 : 25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card ≤
      25 + 2 * w.length + 13 * L + L * L := by
    have hsq : (countFinset K w.length).card * (countFinset K w.length).card ≤ L * L :=
      Nat.mul_le_mul hL hL
    omega
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl h1) le_rfl)
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ h1) le_rfl))

end Size

end TMEnc

end HTN
