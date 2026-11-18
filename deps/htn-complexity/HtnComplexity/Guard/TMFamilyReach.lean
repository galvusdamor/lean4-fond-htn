import HtnComplexity.Guard.TMFamily
import HtnComplexity.Guard.TaskClass
import HtnComplexity.TMEnc.TMEncFixReach
/-!
# The compound tasks the family construction can reach

`HtnComplexity/TMEnc/TMEncFixReach.lean` lists the compound tasks the repaired encoding can reach.
The re-split construction of `HtnComplexity/Guard/TMFamily.lean` differs from it in two
ways, and both enlarge the list:

* the domain is read at the canonical word `HTN.TMEnc.Fam.wpad N n`, and at each position
  `i < n` the task `produceWord i` has **one method per letter** of the alphabet, so every
  `produceSym (some c)` is reachable, not only the ones of one word;
* every body carries a guard task, which is primitive and therefore contributes no name
  (`HTN.GuardTask.reachableName_guard_iff`).

`HTN.TMEnc.Fam.taskFinsetFam` is the enlarged list and

> `HTN.TMEnc.Fam.mem_taskFinsetFam_of_reachableName_famDomain` — every compound task name the
> family problem can reach is in it,

which is the condition `HTN.Syn.Rendering` (`HtnComplexity/Computable/Render.lean`) puts on
the methods a description may leave out.  The list has `|Γ|` more tasks than the one of the
repaired encoding (`HTN.TMEnc.Fam.card_taskFinsetFam_le`), so it is still of polynomial size.
-/

namespace HTN

namespace TMEnc

namespace Fam

open scoped Classical

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {n K : ℕ}

/-! ### The list -/

/-- **The compound tasks the family construction uses**: those of the repaired encoding at the
canonical word, together with the production of every letter of the alphabet. -/
noncomputable def taskFinsetFam [Fintype Γ] (N : NTM Q Γ) (n K : ℕ) : Finset (TMTask Q Γ) :=
  taskFinsetFix N (wpad N n) K ∪
    (Finset.univ.image fun c : Γ => TMTask.produceSym (some c))

variable [Fintype Γ]

lemma mem_taskFinsetFam_of_mem_taskFinsetFix {t : TMTask Q Γ}
    (h : t ∈ taskFinsetFix N (wpad N n) K) : t ∈ taskFinsetFam N n K :=
  Finset.mem_union_left _ h

lemma produceSym_mem_taskFinsetFam (c : Γ) :
    TMTask.produceSym (some c) ∈ taskFinsetFam (Q := Q) N n K :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ c))

/-- The family construction uses at most `|Γ|` compound tasks more than the repaired
encoding. -/
lemma card_taskFinsetFam_le (N : NTM Q Γ) (n K : ℕ) :
    (taskFinsetFam N n K).card ≤ (taskFinsetFix N (wpad N n) K).card + Fintype.card Γ := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  exact le_trans Finset.card_image_le (le_of_eq (Finset.card_univ))

/-! ### Closure under the bodies -/

/-- **No decomposition of the family construction leaves `taskFinsetFam`.** -/
lemma mem_taskFinsetFam_of_mem_bodiesAll {t : TMTask Q Γ} (ht : t ∈ taskFinsetFam N n K)
    {ls : List (List (GAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodiesAll N n K t)
    {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) : c ∈ taskFinsetFam N n K := by
  by_cases hw : ∃ i, t = TMTask.produceWord i
  · obtain ⟨i, rfl⟩ := hw
    rw [bodiesAll_produceWord] at hls
    have hex : ∃ c', ls = liftBody (bodyWord n i c') := by
      by_cases hlt : i < n
      · rw [if_pos hlt] at hls; exact hls
      · rw [if_neg hlt] at hls; exact ⟨N.blank, hls⟩
    obtain ⟨c', rfl⟩ := hex
    rw [mem_flatten_liftBody] at hc
    by_cases hlt : i + 1 < n
    · simp only [bodyWord, if_pos hlt, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      rcases hc with rfl | rfl
      · exact produceSym_mem_taskFinsetFam _
      · refine mem_taskFinsetFam_of_mem_taskFinsetFix
          (mem_taskFinsetFix_of_mem_taskFinset (produceWord_mem_taskFinset ?_))
        rw [length_wpad]
        omega
    · simp only [bodyWord, if_neg hlt, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      subst hc
      exact produceSym_mem_taskFinsetFam _
  · push_neg at hw
    rw [bodiesAll_eq_image hw] at hls
    obtain ⟨ls₀, hls₀, rfl⟩ := hls
    rw [mem_flatten_liftBody] at hc
    rcases Finset.mem_union.1 ht with ht' | ht'
    · exact mem_taskFinsetFam_of_mem_taskFinsetFix
        (mem_taskFinsetFix_of_mem_bodiesFix ht' hls₀ hc)
    · -- the production of a letter that the canonical word does not contain
      obtain ⟨c₀, -, rfl⟩ := Finset.mem_image.1 ht'
      have hK1 : K + 1 ∈ countFinset K (wpad N n).length :=
        halvingClosure_succ_subset_countFinset _ (self_mem_halvingClosure _)
      have hb : ls₀ = [[Sum.inl (TMAct.assert (some c₀)),
          Sum.inr (TMTask.acquire SyncKind.head),
          Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
          Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))]] := by
        have hls' : ls₀ ∈ bodies N (wpad N n) K (TMTask.produceSym (some c₀)) := hls₀
        simpa [bodies] using hls'
      subst hb
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, false_or, Sum.inr.injEq] at hc
      refine mem_taskFinsetFam_of_mem_taskFinsetFix (mem_taskFinsetFix_of_mem_taskFinset ?_)
      rcases hc with rfl | rfl | rfl
      · exact acquire_mem_taskFinset _
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK1
      · exact cSeq_mem_taskFinset (by simp [cSeqBase]) hK1

/-- The compound tasks of the initial method of the family construction are in the list. -/
lemma mem_taskFinsetFam_of_mem_initNetG {p : ℕ × ℕ}
    (hp : p ∈ (initNetG (Q := Q) (Γ := Γ) K).T) {c : TMTask Q Γ}
    (hc : (initNetG (Q := Q) (Γ := Γ) K).α p = Sum.inr c) : c ∈ taskFinsetFam N n K := by
  have hrel := relabel_initNetFix (Q := Q) (Γ := Γ) K
  have hT : p ∈ (initNetFix (Q := Q) (Γ := Γ) K).T := by
    have hTe : (initNetG (Q := Q) (Γ := Γ) K).T
        = (initNetFix (Q := Q) (Γ := Γ) K).T.image (Equiv.refl (ℕ × ℕ)) := by
      rw [← hrel]; rfl
    rw [hTe] at hp
    simpa using hp
  have hα : (initNetFix (Q := Q) (Γ := Γ) K).α p = Sum.inr c := by
    have hmap : Sum.map (Sum.inr : TMAct Q Γ → GAct Q Γ) id
        ((initNetFix (Q := Q) (Γ := Γ) K).α p) = Sum.inr c := by
      rw [← hc, ← hrel]; rfl
    cases hx : (initNetFix (Q := Q) (Γ := Γ) K).α p with
    | inl a => rw [hx] at hmap; exact absurd hmap (by simp)
    | inr d => rw [hx] at hmap; simpa using hmap
  exact mem_taskFinsetFam_of_mem_taskFinsetFix
    (mem_taskFinsetFix_of_mem_initNetFix (N := N) (w := wpad N n) hT hα)

/-! ### Reachability -/

/-- **Every compound task name the unguarded family problem can reach is in
`taskFinsetFam`.** -/
theorem mem_taskFinsetFam_of_reachableName_allDomain (w : List Γ) {t : TMTask Q Γ}
    (h : ((allDomain N n K).mkProblem (famInstance N w)).ReachableName t) :
    t ∈ taskFinsetFam N n K := by
  induction h with
  | @tnI x nm hx hα =>
      have hx' : x ∈ (seq [(Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ)]).T := hx
      rw [TaskNetwork.mem_seq_T] at hx'
      have hx0 : x = (0, 0) := by
        obtain ⟨i, j⟩ := x
        simp only [List.length_singleton] at hx'
        exact Prod.ext hx'.1 (by omega)
      subst hx0
      have hα0 : (seq [(Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ)]).α (0, 0) =
          Sum.inr TMTask.sI := TaskNetwork.seq_α (by simp)
      have heq : (Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ) = Sum.inr nm := by
        rw [← hα0]; exact hα
      have hnm : (TMTask.sI : TMTask Q Γ) = nm := by simpa using heq
      subst hnm
      exact mem_taskFinsetFam_of_mem_taskFinsetFix
        (mem_taskFinsetFix_of_mem_taskFinset sI_mem_taskFinset)
  | @method m x c hm _ hxT hxα ih =>
      rcases hm with ⟨ls, hls, hsub⟩ | hsI
      · have hmem : m.subtasks.α x ∈ ls.flatten := by
          rw [hsub] at hxT ⊢
          exact TaskNetwork.grid_α_mem_flatten hxT
        rw [hxα] at hmem
        exact mem_taskFinsetFam_of_mem_bodiesAll ih hls hmem
      · have hsI' : m = ⟨TMTask.sI, initNetG K⟩ := hsI
        subst hsI'
        exact mem_taskFinsetFam_of_mem_initNetG hxT hxα

/-- **Every compound task name the family problem can reach is in `taskFinsetFam`** — the guard
tasks are primitive, so they contribute no name. -/
theorem mem_taskFinsetFam_of_reachableName_famDomain (w : List Γ) {t : TMTask Q Γ}
    (h : ((famDomain N n K).mkProblem (famInstance N w)).ReachableName t) :
    t ∈ taskFinsetFam N n K := by
  refine mem_taskFinsetFam_of_reachableName_allDomain w ?_
  refine (GuardTask.reachableName_guard_iff (D := allDomain N n K) (Dg := famDomain N n K)
    (Q := famInstance N w) (fun m hm => ⟨m, hm, rfl⟩)
    (by rintro mg ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩) (fun m _ => gid_not_mem m) t).1 h

end Fam

end TMEnc

end HTN
