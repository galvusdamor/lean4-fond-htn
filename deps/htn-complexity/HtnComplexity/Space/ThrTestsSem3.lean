import HtnComplexity.Space.ThrTestsSem2
/-!
# Soundness of the initial test of the thread machine

`HTN.Space.Thr.thrInitOk_of_thrInitB`: a configuration of canonical numerals that passes the
initial test `thrInitB` (against the code of the instance and an advice whose table starts with
the two marker rows of P-TR) satisfies the local conditions `HTN.Space.Thr.ThrInitOk`.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

section Presence

variable {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row} {S : List (List Bool)}

/-! ### Entries recognised by their tags -/

theorem entry_witR (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) {f : ℕ} (hf : f ∈ decSt S) (hpre : kp tWit <+: entN f) :
    ∃ p a, a ∈ wnodes q.tnI ∧ f = cfG (.wit p a) := by
  rcases classifyR hS hK hall hf with ⟨v, -, rfl⟩ | rfl | h | ⟨p, i, -, -, rfl⟩ |
      ⟨p, a0, -, -, rfl⟩ | ⟨k, -, -, rfl⟩ | ⟨x, y, -, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, -, rfl⟩
  · rw [entN, bitsOfNat_cfI] at hpre; exact absurd hpre (kp_not_inst _ _)
  · rw [kp_ent_cfG] at hpre; simp [gbits, tWit, unary] at hpre
  · exact h
  · rw [kp_ent_cfG] at hpre; simp [gbits, tWit] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tWit] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tWit] at hpre
  all_goals rw [kp_entN_cfN_iff rfl] at hpre; simp only [ntag] at hpre; exact absurd hpre (by decide)

theorem entry_edgeR (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) {f : ℕ} (hf : f ∈ decSt S) (hpre : kp tE3 <+: entN f) :
    ∃ x y, f = cfN (.edge x y) := by
  rcases classifyR hS hK hall hf with ⟨v, -, rfl⟩ | rfl | ⟨p, a, -, rfl⟩ | ⟨p, i, -, -, rfl⟩ |
      ⟨p, a0, -, -, rfl⟩ | ⟨k, -, -, rfl⟩ | ⟨x, y, -, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, -, rfl⟩
  · rw [entN, bitsOfNat_cfI] at hpre; exact absurd hpre (kp_not_inst _ _)
  · rw [kp_ent_cfG] at hpre; simp [gbits, tE3, unary] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tE3] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tE3] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tE3] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tE3] at hpre
  · exact ⟨x, y, rfl⟩
  all_goals rw [kp_entN_cfN_iff rfl] at hpre; simp only [ntag] at hpre; exact absurd hpre (by decide)

theorem entry_clR (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) {f : ℕ} (hf : f ∈ decSt S) (hpre : kp tC3 <+: entN f) :
    ∃ x y, f = cfN (.cl x y) := by
  rcases classifyR hS hK hall hf with ⟨v, -, rfl⟩ | rfl | ⟨p, a, -, rfl⟩ | ⟨p, i, -, -, rfl⟩ |
      ⟨p, a0, -, -, rfl⟩ | ⟨k, -, -, rfl⟩ | ⟨x, y, -, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, -, rfl⟩
  · rw [entN, bitsOfNat_cfI] at hpre; exact absurd hpre (kp_not_inst _ _)
  · rw [kp_ent_cfG] at hpre; simp [gbits, tC3, unary] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tC3] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tC3] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tC3] at hpre
  · rw [kp_ent_cfG] at hpre; simp [gbits, tC3] at hpre
  · rw [kp_entN_cfN_iff rfl] at hpre; simp only [ntag] at hpre; exact absurd hpre (by decide)
  · exact ⟨x, y, rfl⟩
  · rw [kp_entN_cfN_iff rfl] at hpre; simp only [ntag] at hpre; exact absurd hpre (by decide)

/-! ### The new presence conditions -/

theorem pInjAll_sound (hS : ∀ w ∈ S, IsCanon w) (h : pInjAll (blist S) = true) {p a a' : ℕ}
    (h1 : cfG (.wit p a) ∈ decSt S) (h2 : cfG (.wit p a') ∈ decSt S) : a = a' := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  rw [pInjAllBody1] at h3
  have h4 := (allE_S hS _ _ _ _).1 h3 _ h2
  rw [pInjAllBody2, decide_eq_true (kp_entG_wit p a), decide_eq_true (kp_entG_wit p a'),
    (samePos_iff (drop_entG_wit p a) (drop_entG_wit p a')).2 rfl] at h4
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h4
  exact (GF.wit.inj (cfG_injective (entN_injective h4))).2

theorem pDownAll_sound (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) (h : pDownAll (blist S) = true) {p a : ℕ}
    (h1 : cfG (.wit (p + 1) a) ∈ decSt S) : ∃ a', cfG (.wit p a') ∈ decSt S := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  rw [pDownAllBody1, decide_eq_true (kp_entG_wit _ a)] at h3
  have hz : posZero (entN (cfG (.wit (p + 1) a))) = false := by
    rw [Bool.eq_false_iff]; intro hz
    exact absurd ((posZero_iff (drop_entG_wit _ a)).1 hz) (by omega)
  rw [hz] at h3; simp only [Bool.not_true, Bool.false_or] at h3
  obtain ⟨f, hf, h4⟩ := (anyE_S hS _ _ _ _).1 h3
  rw [pDownAllBody2, Bool.and_eq_true, decide_eq_true_eq] at h4
  obtain ⟨p', a', -, rfl⟩ := entry_witR hS hK hall hf h4.1
  rw [succPos_iff (drop_entG_wit p' a') (drop_entG_wit _ a)] at h4
  obtain rfl : p' = p := by omega
  exact ⟨a', hf⟩

theorem pEdge_sound (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) (h : pEdge (blist S) (instSer q) = true)
    {e : ℕ × ℕ} (he : e ∈ q.tnI.ordList) {x y : ℕ}
    (h1 : cfG (.wit x e.1) ∈ decSt S) (h2 : cfG (.wit y e.2) ∈ decSt S) :
    cfN (.edge x y) ∈ decSt S := by
  have h3 := (atL_ord_all _ q _ _ _).1 h e he
  rw [pEdgeBody0] at h3
  have h4 := (allE_S hS _ _ _ _).1 h3 _ h1
  rw [pEdgeBody1] at h4
  have h5 := (allE_S hS _ _ _ _).1 h4 _ h2
  rw [pEdgeBody2, (witFst_iff _ e).2 ((witNode_entN _ _).2 ⟨x, rfl⟩),
    (witSnd_iff _ e).2 ((witNode_entN _ _).2 ⟨y, rfl⟩)] at h5
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h5
  obtain ⟨f, hf, h6⟩ := (anyE_S hS _ _ _ _).1 h5
  simp only [pEdgeBody3, Bool.and_eq_true, decide_eq_true_eq] at h6
  obtain ⟨⟨hpre, hs⟩, hp⟩ := h6
  obtain ⟨x', y', rfl⟩ := entry_edgeR hS hK hall hf hpre
  rw [samePos_iff (drop_entG_wit x e.1) (drop_edge x' y')] at hs
  rw [pos21_iff (drop_edge x' y') (drop_entG_wit y e.2)] at hp
  subst hs hp
  exact hf

theorem pCl1_sound (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) (h : pCl1 (blist S) = true) {x y : ℕ}
    (h1 : cfN (.edge x y) ∈ decSt S) : cfN (.cl x y) ∈ decSt S := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  have hk : kp tE3 <+: entN (cfN (.edge x y)) := kp_entN_cfN (.edge x y)
  rw [pCl1Body1, decide_eq_true hk] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  obtain ⟨f, hf, h4⟩ := (anyE_S hS _ _ _ _).1 h3
  simp only [pCl1Body2, Bool.and_eq_true, decide_eq_true_eq] at h4
  obtain ⟨hpre, hs⟩ := h4
  obtain ⟨x', y', rfl⟩ := entry_clR hS hK hall hf hpre
  obtain ⟨rfl, rfl⟩ := (samePair_iff (drop_edge x y) (drop_cl x' y')).1 hs
  exact hf

theorem pCl2_sound (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) (h : pCl2 (blist S) = true) {x y z : ℕ}
    (h1 : cfN (.cl x y) ∈ decSt S) (h2 : cfN (.edge y z) ∈ decSt S) :
    cfN (.cl x z) ∈ decSt S := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  have hk : kp tC3 <+: entN (cfN (.cl x y)) := kp_entN_cfN (.cl x y)
  rw [pCl2Body1, decide_eq_true hk] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  have h4 := (allE_S hS _ _ _ _).1 h3 _ h2
  have hk' : kp tE3 <+: entN (cfN (.edge y z)) := kp_entN_cfN (.edge y z)
  rw [pCl2Body2, decide_eq_true hk', (pos21_iff (drop_cl x y) (drop_edge y z)).2 rfl] at h4
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h4
  obtain ⟨f, hf, h5⟩ := (anyE_S hS _ _ _ _).1 h4
  simp only [pCl2Body3, Bool.and_eq_true, decide_eq_true_eq] at h5
  obtain ⟨⟨hpre, hs⟩, hp⟩ := h5
  obtain ⟨x', z', rfl⟩ := entry_clR hS hK hall hf hpre
  rw [samePos_iff (drop_cl x y) (drop_cl x' z')] at hs
  rw [pos22_iff (drop_edge y z) (drop_cl x' z')] at hp
  subst hs hp
  exact hf

theorem pPos_sound (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) (h : pPos (blist S) = true) {e : NF} (he : ¬ ∃ x y, e = .edge x y)
    (h1 : cfN e ∈ decSt S) :
    (∃ a, cfG (.wit (npos1 e) a) ∈ decSt S) ∧ (∃ a, cfG (.wit (npos2 e) a) ∈ decSt S) := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  have hk : (decide (kp tC3 <+: entN (cfN e)) || decide (kp tN3 <+: entN (cfN e))) = true := by
    cases e with
    | edge x y => exact absurd ⟨x, y, rfl⟩ he
    | cl x y =>
      simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (kp_entN_cfN (.cl x y))
    | nc x y =>
      simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr (kp_entN_cfN (.nc x y))
  rw [pPosBody, hk] at h3
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h3
  obtain ⟨h4, h5⟩ := h3
  obtain ⟨f, hf, h4⟩ := (anyE_S hS _ _ _ _).1 h4
  obtain ⟨f', hf', h5⟩ := (anyE_S hS _ _ _ _).1 h5
  simp only [pPosW1, Bool.and_eq_true, decide_eq_true_eq] at h4
  simp only [pPosW2, Bool.and_eq_true, decide_eq_true_eq] at h5
  obtain ⟨p, a, -, rfl⟩ := entry_witR hS hK hall hf h4.1
  obtain ⟨p', a', -, rfl⟩ := entry_witR hS hK hall hf' h5.1
  have hd := drop_entN_cfN e
  rw [samePos_iff (drop_entG_wit p a) hd] at h4
  rw [pos21_iff hd (drop_entG_wit p' a')] at h5
  rw [← h4.2, h5.2]
  exact ⟨⟨a, hf⟩, ⟨a', hf'⟩⟩

/-! ### Soundness -/

/-- The classification, for gadget facts. -/
theorem classifyR_cfG (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) {g : GF} (hg : cfG g ∈ decSt S) :
    g = .cur 0 ∨ (∃ p a, a ∈ wnodes q.tnI ∧ g = .wit p a) ∨
      (∃ p i, i ∈ q.tnI.ids ∧ cfG (.wit p i) ∈ decSt S ∧ g = .lab p (q.tnI.label i)) ∨
      (∃ p a0, cfG (.lab p (Sum.inl a0)) ∈ decSt S ∧ a0 ∉ vocA d ∧ g = .nop p) ∨
      (∃ k, (∀ p y, cfG (.lab p y) ∈ decSt S → p ≠ k) ∧
        (k = 0 ∨ ∃ y, cfG (.lab (k - 1) y) ∈ decSt S) ∧ g = .len k) := by
  rcases classifyR hS hK hall hg with ⟨v, -, he⟩ | he | ⟨p, a, ha, he⟩ | ⟨p, i, hi, hw, he⟩ |
      ⟨p, a0, hl, ha, he⟩ | ⟨k, h1, h2, he⟩ | ⟨x, y, -, he⟩ | ⟨x, y, he⟩ | ⟨x, y, -, he⟩
  · exact absurd he.symm (cfI_ne_cfG v g)
  · exact Or.inl (cfG_injective he)
  · exact Or.inr (Or.inl ⟨p, a, ha, cfG_injective he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, i, hi, hw, cfG_injective he⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, a0, hl, ha, cfG_injective he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, h1, h2, cfG_injective he⟩)))
  all_goals exact absurd he.symm (cfN_ne_cfG _ _)

/-- The classification, for pair facts. -/
theorem classifyR_cfN (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) {e : NF} (he : cfN e ∈ decSt S) :
    (∃ x y, (∃ o ∈ q.tnI.ordList, cfG (.wit x o.1) ∈ decSt S ∧ cfG (.wit y o.2) ∈ decSt S) ∧
        e = .edge x y) ∨
      (∃ x y, e = .cl x y) ∨ (∃ x y, cfN (.cl x y) ∉ decSt S ∧ e = .nc x y) := by
  rcases classifyR hS hK hall he with ⟨v, -, h⟩ | h | ⟨p, a, -, h⟩ | ⟨p, i, -, -, h⟩ |
      ⟨p, a0, -, -, h⟩ | ⟨k, -, -, h⟩ | ⟨x, y, ho, h⟩ | ⟨x, y, h⟩ | ⟨x, y, hc, h⟩
  · exact absurd h (cfN_ne_cfI _ _)
  all_goals first
    | exact absurd h (cfN_ne_cfG _ _)
    | exact Or.inl ⟨x, y, ho, cfN_injective h⟩
    | exact Or.inr (Or.inl ⟨x, y, cfN_injective h⟩)
    | exact Or.inr (Or.inr ⟨x, y, hc, cfN_injective h⟩)

theorem WitR_len_eq {t : TnDesc} {ws : List (ℕ × ℕ)} (h : WitR t ws) {k : ℕ}
    (h1 : ∀ i ∈ t.ids, (k, i) ∉ ws) (h2 : k = 0 ∨ ∃ i ∈ t.ids, (k - 1, i) ∈ ws) :
    k = t.ids.toFinset.card := by
  have hlt : ¬ k < t.ids.toFinset.card := by
    intro hk
    obtain ⟨i, hi, hw⟩ := h.exists_id_iff.2 hk
    exact h1 i hi hw
  rcases h2 with rfl | h2
  · omega
  · have := h.exists_id_iff.1 h2
    omega

/-- **Soundness of the initial test of the thread machine.** -/
theorem thrInitOk_of_thrInitB (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (h : thrInitB (blist S) (instSer q) (tblAdv b (markRows d K ++ T)) = true) :
    ThrInitOk d q (decSt S) := by
  simp only [thrInitB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hI⟩, hC⟩, hT⟩, hE⟩, hF⟩, hJ⟩, hD⟩, hDA⟩, hL⟩, hN⟩, hLen⟩, hEd⟩,
    hC1⟩, hC2⟩, hP⟩ := h
  have hall : AllOkR d K q b T S := (allE_S hS _ _ _ _).1 hA
  have hwit : WitR q.tnI (witList (decSt S)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨p, hp⟩ := pTotal_sound hS hT i hi
      exact ⟨p, mem_witList.2 hp⟩
    · intro e he
      obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := pEndp_sound hS hE e he
      exact ⟨⟨p, mem_witList.2 hp⟩, ⟨p', mem_witList.2 hp'⟩⟩
    · intro p a hpa
      have hf := mem_witList.1 hpa
      obtain ⟨p', a', ha', he⟩ := entry_witR hS hK hall hf (kp_entG_wit p a)
      obtain ⟨-, rfl⟩ := GF.wit.inj (cfG_injective he)
      exact ha'
    · intro p p' a h1 h2
      exact pFunc_sound hS hF (mem_witList.1 h1) (mem_witList.1 h2)
    · intro p a a' h1 h2
      exact pInjAll_sound hS hJ (mem_witList.1 h1) (mem_witList.1 h2)
    · intro p i hi h1
      obtain ⟨j, hj, hw⟩ := pDown_sound hS hD hi (mem_witList.1 h1)
      exact ⟨j, hj, mem_witList.2 hw⟩
    · intro p a h1
      obtain ⟨a', hw⟩ := pDownAll_sound hS hK hall hDA (mem_witList.1 h1)
      exact ⟨a', mem_witList.2 hw⟩
  have hlab : ∀ p x, cfG (.lab p x) ∈ decSt S ↔
      ∃ i ∈ q.tnI.ids, cfG (.wit p i) ∈ decSt S ∧ q.tnI.label i = x := by
    intro p x
    constructor
    · intro hg
      rcases classifyR_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨p', i, hi, hw, he⟩ |
          ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
      exact ⟨i, hi, hw, rfl⟩
    · rintro ⟨i, hi, hw, rfl⟩
      exact pLab_sound hS hL hi hw
  have hlen1 : ∀ k, cfG (.len k) ∈ decSt S →
      (∀ i ∈ q.tnI.ids, cfG (.wit k i) ∉ decSt S) ∧
        (k = 0 ∨ ∃ i ∈ q.tnI.ids, cfG (.wit (k - 1) i) ∈ decSt S) := by
    intro k hg
    rcases classifyR_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
        ⟨_, _, _, _, he⟩ | ⟨k', h1, h2, he⟩ <;> cases he
    refine ⟨fun i hi hw => h1 k _ (pLab_sound hS hL hi hw) rfl, ?_⟩
    rcases h2 with h2 | ⟨y, hy⟩
    · exact Or.inl h2
    · obtain ⟨i, hi, hw, -⟩ := (hlab _ _).1 hy
      exact Or.inr ⟨i, hi, hw⟩
  refine ⟨?_, ?_, ?_, ?_, hwit, hlab, ?_, ?_, ?_, fun x y => pCl1_sound hS hK hall hC1,
    fun x y z => pCl2_sound hS hK hall hC2, ?_, ?_, ?_⟩
  · intro f hf
    rcases classifyR hS hK hall hf with ⟨v, -, he⟩ | he | ⟨p, a, -, he⟩ | ⟨p, i, -, -, he⟩ |
        ⟨p, a0, -, -, he⟩ | ⟨k, -, -, he⟩ | ⟨x, y, -, he⟩ | ⟨x, y, he⟩ | ⟨x, y, -, he⟩
    · exact Or.inl ⟨v, he⟩
    · exact Or.inr (Or.inl ⟨_, he⟩)
    · exact Or.inr (Or.inl ⟨_, he⟩)
    · exact Or.inr (Or.inl ⟨_, he⟩)
    · exact Or.inr (Or.inl ⟨_, he⟩)
    · exact Or.inr (Or.inl ⟨_, he⟩)
    all_goals exact Or.inr (Or.inr ⟨_, he⟩)
  · intro v
    constructor
    · intro hv
      rcases classifyR hS hK hall hv with ⟨v', hv', he⟩ | he | ⟨p, a, -, he⟩ |
          ⟨p, i, -, -, he⟩ | ⟨p, a0, -, -, he⟩ | ⟨k, -, -, he⟩ | ⟨x, y, -, he⟩ | ⟨x, y, he⟩ |
          ⟨x, y, -, he⟩
      · rwa [cfI_injective he]
      · exact absurd he (cfI_ne_cfG _ _)
      · exact absurd he (cfI_ne_cfG _ _)
      · exact absurd he (cfI_ne_cfG _ _)
      · exact absurd he (cfI_ne_cfG _ _)
      · exact absurd he (cfI_ne_cfG _ _)
      all_goals exact absurd he.symm (cfN_ne_cfI _ _)
    · exact pInst_sound hS hI
  · intro p
    constructor
    · intro hg
      rcases classifyR_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
          ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
      rfl
    · rintro rfl; exact pCur_sound hS hC
  · intro hg
    rcases classifyR_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
        ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
  · intro p
    constructor
    · intro hg
      rcases classifyR_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
          ⟨p', a0, hl, ha, he⟩ | ⟨_, _, _, he⟩ <;> cases he
      obtain ⟨i, hi, hw, hli⟩ := (hlab _ _).1 hl
      exact ⟨i, hi, hw, by rw [hli]; simp [unknownPrimB, ha]⟩
    · rintro ⟨i, hi, hw, hu⟩
      exact pNop_sound hS hN (pLab_sound hS hL hi hw) hu
  · intro k
    constructor
    · exact hlen1 k
    · rintro ⟨h1, h2⟩
      obtain ⟨k0, hk0⟩ := pLen_sound hS hLen
      obtain ⟨h1', h2'⟩ := hlen1 k0 hk0
      have e1 := WitR_len_eq hwit (k := k) (fun i hi hw => h1 i hi (mem_witList.1 hw))
        (h2.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, mem_witList.2 hw⟩)
      have e2 := WitR_len_eq hwit (k := k0) (fun i hi hw => h1' i hi (mem_witList.1 hw))
        (h2'.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, mem_witList.2 hw⟩)
      rwa [e1, ← e2]
  · intro x y
    constructor
    · intro he
      rcases classifyR_cfN hS hK hall he with ⟨x', y', ho, he'⟩ | ⟨_, _, he'⟩ |
          ⟨_, _, _, he'⟩ <;> cases he'
      exact ho
    · rintro ⟨o, ho, h1, h2⟩
      exact pEdge_sound hS hK hall hEd ho h1 h2
  · intro x y hn
    rcases classifyR_cfN hS hK hall hn with ⟨_, _, _, he'⟩ | ⟨_, _, he'⟩ |
        ⟨x', y', hc, he'⟩ <;> cases he'
    exact hc
  · intro x y hc
    exact pPos_sound hS hK hall hP (e := .cl x y) (by rintro ⟨_, _, h⟩; cases h) hc
  · intro x y hn
    exact pPos_sound hS hK hall hP (e := .nc x y) (by rintro ⟨_, _, h⟩; cases h) hn

end Presence

end Thr

end Space

end HTN
