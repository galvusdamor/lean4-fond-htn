import HtnComplexity.AcVerify.VerComplete
import HtnComplexity.Computable.PoRank
/-!
# Short certificates for acyclic domains

For an **acyclic** domain description, the paths of a path witness are short (at most
`R + 2` steps, `R` the number of compound names, by the rank function `rkD`), and the paths of
the entries are pairwise distinct lists over the finite list `allSteps d q` of steps.  Hence a
path witness has at most `(|allSteps| + 1) ^ (R + 2)` entries:

* `HTN.Syn.AcVer.length_path_le` — the length of the path of an entry;
* `HTN.Syn.AcVer.mem_allSteps` — every step of an entry is in `allSteps d q`;
* `HTN.Syn.AcVer.length_witness_le` — the number of entries.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

/-! ### Short paths -/

theorem methodAt_mem {k : ℕ} (h2 : k - 1 < d.methods.length) :
    methodAt d k ∈ d.methods := by
  unfold methodAt
  rw [List.getD_eq_getElem _ _ h2]
  exact List.getElem_mem h2

/-- **Along a chain of links, the ranks of the decomposed compound names decrease.** -/
theorem chain_length_le (hd : d.IsAcyclic) : ∀ (rest : List PStep) (y : PStep),
    (y :: rest).IsChain (Link d q) → (∀ z ∈ (y :: rest).dropLast, StepIn d q z) →
    1 ≤ y.1 → y.1 - 1 < d.methods.length →
    (y :: rest).length ≤ rkD d (methodAt d y.1).1 + 1
  | [], y, _, _, _, _ => by simp
  | z :: rest, y, hc, hs, h1, h2 => by
    have hl : Link d q y z := (List.isChain_cons_cons.1 hc).1
    have hc' : (z :: rest).IsChain (Link d q) := (List.isChain_cons_cons.1 hc).2
    have hsy : StepIn d q y := hs y (by simp)
    have hs' : ∀ w ∈ (z :: rest).dropLast, StepIn d q w := fun w hw =>
      hs w (by rw [List.dropLast_cons₂]; exact List.mem_cons_of_mem _ hw)
    have ih := chain_length_le hd rest z hc' hs' hl.1 hl.2.1
    have hedge : ((methodAt d y.1).1, (methodAt d z.1).1) ∈ compEdges d := by
      refine mem_compEdges.2 ⟨methodAt d y.1, methodAt_mem h2, rfl, y.2, ?_, ?_⟩
      · have := hsy
        unfold StepIn netOf at this
        rwa [if_neg (by omega)] at this
      · have := hl.2.2
        unfold stepLabel netOf at this
        rwa [if_neg (by omega)] at this
    have := rkD_lt_of_mem_compEdges hd hedge
    simp only [List.length_cons] at ih ⊢
    omega

theorem length_compEdges_le (d : DomDesc) : (compEdges d).length ≤ d.size := by
  unfold compEdges
  rw [List.length_flatMap]
  calc _ ≤ (d.methods.map MethodDesc.size).sum := List.sum_le_sum fun e _ =>
        ((List.length_filterMap_le _ _).trans (List.dedup_sublist _).length_le).trans
          (by simp only [MethodDesc.size, TnDesc.size]; omega)
    _ ≤ d.size := by simp only [DomDesc.size]; omega

theorem rkD_le_size (d : DomDesc) (c : ℕ) : rkD d c ≤ 2 * d.size := by
  refine (rkD_le d c).trans ?_
  refine (List.dedup_sublist _).length_le.trans ?_
  have : (compNames d).length = 2 * (compEdges d).length := by
    simp [compNames, List.length_flatMap, List.map_const', List.sum_replicate, mul_comm]
  have := length_compEdges_le d
  omega

/-- **The path of an entry of a well-formed entry is short.** -/
theorem length_path_le (hd : d.IsAcyclic) {u : Entry} (hu : EntryOK d q u) :
    u.1.length ≤ 2 * d.size + 2 := by
  have hc := isChain_of_entryOK hu
  obtain ⟨i, s, hs⟩ := first_of_entryOK hu
  have hstep : ∀ z ∈ u.1.dropLast, StepIn d q z := by
    unfold EntryOK at hu
    split_ifs at hu
    · obtain ⟨p, y, hp, -, hn, -, -⟩ := hu
      rw [hp, List.dropLast_concat]
      exact hn.2.2
    · exact fun z hz => hu.1.2.2 z (List.dropLast_subset _ hz)
  rcases s with _ | ⟨y, rest⟩
  · rw [hs]; simp
  · rw [hs] at hc hstep ⊢
    have hl : Link d q (0, i) y := (List.isChain_cons_cons.1 hc).1
    have h1 := chain_length_le hd rest y (List.isChain_cons_cons.1 hc).2
      (fun z hz => hstep z (by rw [List.dropLast_cons₂]; exact List.mem_cons_of_mem _ hz))
      hl.1 hl.2.1
    have h2 := rkD_le_size d (methodAt d y.1).1
    simp only [List.length_cons] at h1 ⊢
    omega

/-! ### The steps -/

/-- All steps a well-formed entry can use. -/
def allSteps (d : DomDesc) (q : InstDesc) : List PStep :=
  q.tnI.ids.map (fun i => (0, i)) ++
    (mIdx d).flatMap fun k => (0 :: (methodAt d k).2.ids).map fun j => (k, j)

theorem stepIn_dropLast {u : Entry} (hu : EntryOK d q u) : ∀ z ∈ u.1.dropLast, StepIn d q z := by
  unfold EntryOK at hu
  split_ifs at hu
  · obtain ⟨p, y, hp, -, hn, -, -⟩ := hu
    rw [hp, List.dropLast_concat]
    exact hn.2.2
  · exact fun z hz => hu.1.2.2 z (List.dropLast_subset _ hz)

theorem mem_dropLast_of_split {l₁ l₂ : List PStep} {z : PStep} (h : l₂ ≠ []) :
    z ∈ (l₁ ++ z :: l₂).dropLast := by
  rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil h]
  simp

theorem mem_allSteps {u : Entry} (hu : EntryOK d q u)
    (h0 : u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) : ∀ z ∈ u.1, z ∈ allSteps d q := by
  intro z hz
  have hc := isChain_of_entryOK hu
  have hstep := stepIn_dropLast hu
  obtain ⟨i, s, hs⟩ := first_of_entryOK hu
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hz
  -- `z` names a task of its network, unless it is the dummy step of an empty leaf
  have hin : StepIn d q z ∨ z.2 = 0 := by
    by_cases hl₂ : l₂ = []
    · subst hl₂
      rcases hf : u.2
      · have hu' := hu
        unfold EntryOK at hu'
        simp only [hf, Bool.false_eq_true, if_false] at hu'
        exact Or.inl (hu'.1.2.2 z hz)
      · obtain ⟨p, k, hp⟩ := h0 hf
        rw [hp] at hsplit
        have := (List.append_inj' hsplit rfl).2
        simp only [List.cons.injEq] at this
        right; rw [← this.1]
    · exact Or.inl (hstep z (by rw [hsplit]; exact mem_dropLast_of_split hl₂))
  rcases (List.eq_nil_or_concat l₁) with rfl | ⟨l₁', x, rfl⟩
  · -- the root step
    rw [hs] at hsplit
    simp only [List.nil_append, List.cons.injEq] at hsplit
    obtain ⟨rfl, rfl⟩ := hsplit
    have hi : StepIn d q (0, i) := by
      rcases hin with h | h
      · exact h
      · rcases s with _ | ⟨y, s⟩
        · rcases hf : u.2
          · have hu' := hu
            unfold EntryOK at hu'
            simp only [hf, Bool.false_eq_true, if_false] at hu'
            exact hu'.1.2.2 _ (by rw [hs]; simp)
          · obtain ⟨p, k, hp⟩ := h0 hf
            have hu' := hu
            unfold EntryOK at hu'
            simp only [hf, if_true] at hu'
            obtain ⟨p', y', hp', hne, -⟩ := hu'
            rw [hs] at hp'
            rcases p' with _ | ⟨a, p'⟩
            · exact absurd rfl hne
            · simp at hp'
        · exact hstep _ (by rw [hs]; simp)
    have : i ∈ q.tnI.ids := by simpa [StepIn, netOf] using hi
    simp [allSteps, this]
  · -- a later step
    have hl : Link d q x z := splits_of_isChain hc l₁' x z l₂ (by rw [hsplit]; simp)
    have hk := mIdx_of_link hl
    have hk0 := mIdx_ne_zero hk
    simp only [allSteps, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons]
    right
    refine ⟨z.1, hk, z.2, ?_, rfl⟩
    rcases hin with h | h
    · right
      have := h
      unfold StepIn at this
      rwa [netOf_of_ne hk0] at this
    · exact Or.inl h

theorem map_methodAt_mIdx (d : DomDesc) : (mIdx d).map (methodAt d) = d.methods := by
  refine List.ext_getElem (by simp [mIdx]) fun i h1 h2 => ?_
  simp [mIdx, methodAt, List.getElem?_eq_getElem h2]

theorem length_allSteps_le (d : DomDesc) (q : InstDesc) :
    (allSteps d q).length ≤ q.size + d.size := by
  simp only [allSteps, List.length_append, List.length_map, List.length_flatMap,
    List.length_cons]
  have h1 : ((mIdx d).map fun k => (methodAt d k).2.ids.length + 1) =
      d.methods.map fun e => e.2.ids.length + 1 := by
    rw [← map_methodAt_mIdx d, List.map_map]; rfl
  have h2 : (d.methods.map fun e => e.2.ids.length + 1).sum ≤
      (d.methods.map MethodDesc.size).sum :=
    List.sum_le_sum fun e _ => by simp only [MethodDesc.size, TnDesc.size]; omega
  have h3 : q.tnI.ids.length ≤ q.size := by
    simp only [InstDesc.size, TnDesc.size]; omega
  rw [h1]
  simp only [DomDesc.size]
  omega

/-! ### Counting distinct short lists -/

/-- The lists of length at most `m` over `S`. -/
noncomputable def listsUpTo (S : Finset PStep) : ℕ → Finset (List PStep)
  | 0 => {[]}
  | m + 1 => insert [] ((S ×ˢ listsUpTo S m).image fun p => p.1 :: p.2)

theorem mem_listsUpTo {S : Finset PStep} : ∀ {m : ℕ} {l : List PStep}, l.length ≤ m →
    (∀ x ∈ l, x ∈ S) → l ∈ listsUpTo S m
  | 0, l, hl, _ => by
    obtain rfl : l = [] := List.length_eq_zero_iff.1 (by omega)
    simp [listsUpTo]
  | m + 1, [], _, _ => by simp [listsUpTo]
  | m + 1, x :: l, hl, hS => by
    simp only [listsUpTo, Finset.mem_insert, Finset.mem_image, Finset.mem_product]
    refine Or.inr ⟨(x, l), ⟨hS x (by simp), mem_listsUpTo (by simp at hl; omega)
      fun y hy => hS y (by simp [hy])⟩, rfl⟩

theorem card_listsUpTo_le (S : Finset PStep) : ∀ m, (listsUpTo S m).card ≤ (S.card + 1) ^ m
  | 0 => by simp [listsUpTo]
  | m + 1 => by
    simp only [listsUpTo]
    refine (Finset.card_insert_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := S ×ˢ listsUpTo S m) (f := fun p => p.1 :: p.2)
    rw [Finset.card_product] at h1
    have h2 := card_listsUpTo_le S m
    have h3 : S.card * (listsUpTo S m).card ≤ S.card * (S.card + 1) ^ m :=
      Nat.mul_le_mul_left _ h2
    have h4 : 1 ≤ (S.card + 1) ^ m := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    nlinarith

theorem PathOK.nodup_paths {W : List Entry} (hW : PathOK d q W) : (W.map (·.1)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  refine hW.pairs.imp fun {u v} h => ?_
  obtain ⟨x, y, ⟨P, su, sv, hu, hv, hxy⟩, -⟩ := h
  intro he
  rw [hu, hv] at he
  exact hxy (List.cons.inj (List.append_cancel_left he)).1

/-- **A path witness of an acyclic problem has few entries.** -/
theorem length_witness_le (hd : d.IsAcyclic) {W : List Entry} (hW : PathOK d q W)
    (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) :
    W.length ≤ (q.size + d.size + 1) ^ (2 * d.size + 2) := by
  have hsub : (W.map (·.1)).toFinset ⊆ listsUpTo (allSteps d q).toFinset (2 * d.size + 2) := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hl)
    exact mem_listsUpTo (length_path_le hd (hW.entries u hu))
      fun z hz => List.mem_toFinset.2 (mem_allSteps (hW.entries u hu) (h0 u hu) z hz)
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hW.nodup_paths, List.length_map] at h1
  have h2 := card_listsUpTo_le (allSteps d q).toFinset (2 * d.size + 2)
  have h3 : (allSteps d q).toFinset.card ≤ q.size + d.size :=
    (List.toFinset_card_le _).trans (length_allSteps_le d q)
  exact h1.trans (h2.trans (Nat.pow_le_pow_left (by omega) _))

end AcVer

end Syn

end HTN
