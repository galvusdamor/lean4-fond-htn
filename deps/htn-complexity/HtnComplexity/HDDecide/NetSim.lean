import HtnComplexity.HDDecide.NetLemmas
/-!
# The rule system simulates the search on pieces
-/

namespace HTN

namespace HD

open Syn Syn.ToDec Petri

variable {d : DomDesc} {q : InstDesc}

@[simp] theorem pcL_fst (p : Piece) : (pcL d q p).1 = p.1 := rfl

theorem singleton_le_map {M : Multiset Piece} {p : Piece} (hp : p ∈ M) :
    (((Option.some (pcL d q p)).toList : List Tok) : Multiset Tok) ≤ M.map (pcL d q) := by
  simpa using Multiset.mem_map_of_mem (pcL d q) hp

theorem valid_after {sf sb : Finset ℕ} {M : Multiset Piece} {k : ℕ} {S : Finset ℕ} (x : ℕ)
    (N : Multiset Piece) (hsf : sf ⊆ facts d q) (hsb : sb ⊆ facts d q)
    (hM : ∀ p ∈ M, p.1 < d.methods.length + 1 ∧ p.2 ⊆ (net d q p.1).ids.toFinset)
    (hp : (k, S) ∈ M)
    (hN : ∀ p ∈ N, p.1 < d.methods.length + 1 ∧ p.2 ⊆ (net d q p.1).ids.toFinset) :
    Valid d q (sf, sb, M.erase (k, S) + piece k (S.erase x) + N) := by
  refine ⟨hsf, hsb, fun p hp' => ?_⟩
  rcases Multiset.mem_add.1 hp' with hp' | hp'
  · rcases Multiset.mem_add.1 hp' with hp' | hp'
    · exact hM p (Multiset.mem_of_mem_erase hp')
    · obtain rfl := (mem_piece.1 hp').2
      obtain ⟨hk, hS⟩ := hM _ hp
      exact ⟨hk, (Finset.erase_subset _ _).trans hS⟩
  · exact hN p hp'

/-- **The rule system simulates a step of the search on pieces.** -/
theorem sim_step {c c' : HCfg} (hv : Valid d q c) (h : HStep d q c c') :
    RStep (hdRules d q) (enc d q c) (enc d q c') ∧ Valid d q c' := by
  obtain ⟨hsf, hsb, hM⟩ := hv
  cases h with
  | prog sf sb M k S x a hp hx hmin hlab happ =>
    obtain ⟨hk, hS⟩ := hM _ hp
    have hlp : (net d q k).lblPair x = (false, a) := lblPair_eq_inl.2 hlab
    refine ⟨⟨((1, stL d q sf, stL d q sb), some (pcL d q (k, S)),
      (1, nrmF d q (stepL d (stL d q sf) a), stL d q sb),
      tokOf k ((pcL d q (k, S)).2.filter (fun y => y != x))), ?_, rfl, singleton_le_map hp, ?_⟩,
      ?_⟩
    · rw [mem_hdRules]
      refine Or.inr (Or.inl ⟨_, stL_mem_subsets sf, _, stL_mem_subsets sb, _, pcL_mem_allToks hk,
        x, mem_pcL.2 ⟨List.mem_toFinset.1 (hS hx), hx⟩, Or.inl ?_⟩)
      simp only [progR, pcL_fst, hlp, mem_cond_nil]
      refine ⟨?_, rfl⟩
      simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, applB_iff_appF, toFinset_stL hsf]
      refine ⟨fun y hy => ?_, happ⟩
      rw [← Bool.not_eq_true, ordB_iff_ordK]
      exact hmin y (mem_pcL.1 hy).2
    · simp only [enc]
      rw [nrmF_stepL, toFinset_stL hsf, filter_pcL_erase, coe_tokOf _ _
        ((Finset.erase_subset _ _).trans hS)]
      simp only [Option.toList_some]
      rw [map_sub_singleton hp, Multiset.map_add]
    · simpa using valid_after x 0 (nxtF_subset hsf a) hsb hM hp (by simp)
  | regr sf sb s M k S x a hp hx hmax hlab hs happ hnxt =>
    obtain ⟨hk, hS⟩ := hM _ hp
    have hlp : (net d q k).lblPair x = (false, a) := lblPair_eq_inl.2 hlab
    refine ⟨⟨((1, stL d q sf, stL d q sb), some (pcL d q (k, S)),
      (1, stL d q sf, nrmF d q (stL d q s)),
      tokOf k ((pcL d q (k, S)).2.filter (fun y => y != x))), ?_, rfl, singleton_le_map hp, ?_⟩,
      ?_⟩
    · rw [mem_hdRules]
      refine Or.inr (Or.inl ⟨_, stL_mem_subsets sf, _, stL_mem_subsets sb, _, pcL_mem_allToks hk,
        x, mem_pcL.2 ⟨List.mem_toFinset.1 (hS hx), hx⟩, Or.inr (Or.inl ?_)⟩)
      simp only [regrR, pcL_fst, hlp, List.mem_flatMap, mem_cond_nil]
      refine ⟨stL d q s, stL_mem_subsets s, ?_, rfl⟩
      simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, applB_iff_appF, toFinset_stL hs, beq_iff_eq,
        nrmF_stepL, hnxt]
      refine ⟨⟨fun y hy => ?_, happ⟩, trivial⟩
      rw [← Bool.not_eq_true, ordB_iff_ordK]
      exact hmax y (mem_pcL.1 hy).2
    · simp only [enc]
      rw [nrmF_eq, toFinset_stL hs, filter_pcL_erase, coe_tokOf _ _
        ((Finset.erase_subset _ _).trans hS)]
      simp only [Option.toList_some]
      rw [map_sub_singleton hp, Multiset.map_add]
    · simpa using valid_after x 0 hsf hs hM hp (by simp)
  | dec sf sb M k S x c j hp hx hiso hlab hj hc =>
    obtain ⟨hk, hS⟩ := hM _ hp
    have hlp : (net d q k).lblPair x = (true, c) := lblPair_eq_inr.2 hlab
    refine ⟨⟨((1, stL d q sf, stL d q sb), some (pcL d q (k, S)), (1, stL d q sf, stL d q sb),
      tokOf k ((pcL d q (k, S)).2.filter (fun y => y != x)) ++ tokOf (j + 1) (net d q (j + 1)).ids),
      ?_, rfl, singleton_le_map hp, ?_⟩, ?_⟩
    · rw [mem_hdRules]
      refine Or.inr (Or.inl ⟨_, stL_mem_subsets sf, _, stL_mem_subsets sb, _, pcL_mem_allToks hk,
        x, mem_pcL.2 ⟨List.mem_toFinset.1 (hS hx), hx⟩, Or.inr (Or.inr ?_)⟩)
      simp only [decR, pcL_fst, hlp, List.mem_flatMap, List.mem_range, mem_cond_nil]
      refine ⟨j, hj, ?_, rfl⟩
      simp only [Bool.true_and, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, beq_iff_eq, hc, and_true]
      intro y hy
      rw [← Bool.not_eq_true, ← Bool.not_eq_true, ordB_iff_ordK, ordB_iff_ordK]
      exact hiso y (mem_pcL.1 hy).2
    · simp only [enc]
      have h2 := coe_tokOf (d := d) (q := q) (j + 1) _ (subset_refl _)
      rw [pcL_full] at h2
      rw [filter_pcL_erase, ← Multiset.coe_add, coe_tokOf _ _
        ((Finset.erase_subset _ _).trans hS), h2]
      simp only [Option.toList_some]
      rw [map_sub_singleton hp, Multiset.map_add, Multiset.map_add, add_assoc]
    · refine valid_after x _ hsf hsb hM hp fun p hp' => ?_
      obtain rfl := (mem_piece.1 hp').2
      exact ⟨by simpa using hj, subset_refl _⟩

theorem mem_of_le_map {M : Multiset Piece} {p : Tok}
    (h : (((Option.some (p.1, p.2)).toList : List Tok) : Multiset Tok) ≤ M.map (pcL d q)) :
    ∃ k S, (k, S) ∈ M ∧ p = pcL d q (k, S) := by
  have hm : p ∈ M.map (pcL d q) := Multiset.mem_of_le h (by simp)
  obtain ⟨⟨k, S⟩, hp, rfl⟩ := Multiset.mem_map.1 hm
  exact ⟨k, S, hp, rfl⟩

/-- **A step of the rule system from an encoded configuration is a step of the search on
pieces, or the end step.** -/
theorem decode_step {c : HCfg} {y : Ctl × Multiset Tok} (hv : Valid d q c)
    (h : RStep (hdRules d q) (enc d q c) y) :
    (∃ c', HStep d q c c' ∧ y = enc d q c') ∨ (c.1 = c.2.1 ∧ y = (doneC, c.2.2.map (pcL d q))) := by
  obtain ⟨sf, sb, M⟩ := c
  obtain ⟨hsf, hsb, hM⟩ := hv
  obtain ⟨r, hr, hc, hle, rfl⟩ := h
  rw [mem_hdRules] at hr
  rcases hr with ⟨s, -, -, rfl⟩ | ⟨lf, -, lb, -, p, -, x, hx, hr⟩ | ⟨l, -, rfl⟩
  · simp [startC, enc] at hc
  · rcases hr with hr | hr | hr
    · simp only [progR, mem_cond_nil] at hr
      obtain ⟨hcond, rfl⟩ := hr
      simp only [enc, Prod.mk.injEq, true_and] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨k, S, hp, rfl⟩ := mem_of_le_map hle
      simp only [Prod.mk.eta]
      obtain ⟨hk, hS⟩ := hM _ hp
      simp only [pcL_fst, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.all_eq_true, applB_iff_appF, toFinset_stL hsf] at hcond
      obtain ⟨⟨hb, hmin⟩, happ⟩ := hcond
      have hlp : (net d q k).lblPair x = (false, ((net d q k).lblPair x).2) := Prod.ext hb rfl
      have hxS : x ∈ S := (mem_pcL.1 hx).2
      refine Or.inl ⟨_, HStep.prog sf sb M k S x _ hp hxS (fun y hy => ?_) (lblPair_eq_inl.1 hlp)
        happ, ?_⟩
      · rw [← ordB_iff_ordK, hmin y (mem_pcL.2 ⟨List.mem_toFinset.1 (hS hy), hy⟩)]
        simp
      · simp only [enc, pcL_fst]
        rw [nrmF_stepL, toFinset_stL hsf, filter_pcL_erase, coe_tokOf _ _
          ((Finset.erase_subset _ _).trans hS)]
        simp only [Option.toList_some]
        rw [map_sub_singleton hp, Multiset.map_add]
    · simp only [regrR, List.mem_flatMap, mem_cond_nil] at hr
      obtain ⟨s, hs, hcond, rfl⟩ := hr
      simp only [enc, Prod.mk.injEq, true_and] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨k, S, hp, rfl⟩ := mem_of_le_map hle
      simp only [Prod.mk.eta]
      obtain ⟨hk, hS⟩ := hM _ hp
      have hs' := toFinset_subset_facts hs
      simp only [pcL_fst, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.all_eq_true, applB_iff_appF, beq_iff_eq, nrmF_stepL] at hcond
      obtain ⟨⟨⟨hb, hmax⟩, happ⟩, hnxt⟩ := hcond
      have hlp : (net d q k).lblPair x = (false, ((net d q k).lblPair x).2) := Prod.ext hb rfl
      have hxS : x ∈ S := (mem_pcL.1 hx).2
      refine Or.inl ⟨_, HStep.regr sf sb s.toFinset M k S x _ hp hxS (fun y hy => ?_)
        (lblPair_eq_inl.1 hlp) hs' happ (stL_inj (nxtF_subset hs' _) hsb hnxt), ?_⟩
      · rw [← ordB_iff_ordK, hmax y (mem_pcL.2 ⟨List.mem_toFinset.1 (hS hy), hy⟩)]
        simp
      · simp only [enc, pcL_fst]
        rw [nrmF_eq, filter_pcL_erase, coe_tokOf _ _ ((Finset.erase_subset _ _).trans hS)]
        simp only [Option.toList_some]
        rw [map_sub_singleton hp, Multiset.map_add]
    · simp only [decR, List.mem_flatMap, List.mem_range, mem_cond_nil] at hr
      obtain ⟨j, hj, hcond, rfl⟩ := hr
      simp only [enc, Prod.mk.injEq, true_and] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨k, S, hp, rfl⟩ := mem_of_le_map hle
      simp only [Prod.mk.eta]
      obtain ⟨hk, hS⟩ := hM _ hp
      simp only [pcL_fst, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.all_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨hb, hiso⟩, hc⟩ := hcond
      have hlp : (net d q k).lblPair x = (true, ((net d q k).lblPair x).2) := Prod.ext hb rfl
      have hxS : x ∈ S := (mem_pcL.1 hx).2
      refine Or.inl ⟨_, HStep.dec sf sb M k S x _ j hp hxS (fun y hy => ?_)
        (lblPair_eq_inr.1 hlp) hj hc, ?_⟩
      · obtain ⟨h1, h2⟩ := hiso y (mem_pcL.2 ⟨List.mem_toFinset.1 (hS hy), hy⟩)
        rw [← ordB_iff_ordK, ← ordB_iff_ordK, h1, h2]
        simp
      · simp only [enc, pcL_fst]
        have h2 := coe_tokOf (d := d) (q := q) (j + 1) _ (subset_refl _)
        rw [pcL_full] at h2
        rw [filter_pcL_erase, ← Multiset.coe_add, coe_tokOf _ _
          ((Finset.erase_subset _ _).trans hS), h2]
        simp only [Option.toList_some]
        rw [map_sub_singleton hp, Multiset.map_add, Multiset.map_add, add_assoc]
  · simp only [enc, Prod.mk.injEq, true_and] at hc
    obtain ⟨rfl, he⟩ := hc
    refine Or.inr ⟨stL_inj hsf hsb he, ?_⟩
    simp [enc]

end HD

end HTN
