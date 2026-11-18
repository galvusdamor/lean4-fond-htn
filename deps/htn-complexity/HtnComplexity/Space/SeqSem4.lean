import HtnComplexity.Space.SeqSem3
/-!
# Soundness of the initial test of the gadget machine (the presence conditions)

`HTN.Space.SeqM.initOk_of_seqInitB`: a configuration of canonical numerals that passes the
initial test `seqInitB` (against the code of the instance and an advice whose table starts with
the two marker rows) satisfies the local conditions `HTN.Space.SeqM.InitOk`.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

section Presence

variable {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row} {S : List (List Bool)}

theorem entN_tail (i : ℕ) : (entN i).tail = serNat i := rfl

theorem entCur0_eq : entCur0 = entN (cfG (.cur 0)) := by rw [entCur0, entN, bitsOfNat_cfG]

theorem pRoot_sound (hS : ∀ w ∈ S, IsCanon w)
    (h : pRoot (blist S) (tblAdv b (markRows d K ++ T)) = true) : cRoot d ∈ decSt S := by
  obtain ⟨f, hf, h⟩ := (anyE_S hS _ _ _ _).1 h
  rw [pRootBody, entN, kRoot_iff d K b T (isCanon_bitsOfNat f), natOfBits_bitsOfNat] at h
  rwa [← h]

theorem pInst_sound (hS : ∀ w ∈ S, IsCanon w) (h : pInst (blist S) (instSer q) = true) {v : ℕ}
    (hv : v ∈ q.initList) : cfI v ∈ decSt S := by
  rw [mem_S_iff hS, bitsOfNat_cfI]; exact (pInst_iff S q).1 h v hv

theorem pCur_sound (hS : ∀ w ∈ S, IsCanon w) (h : pCur (blist S) = true) :
    cfG (.cur 0) ∈ decSt S := by
  rw [pCur, entCur0_eq, occB_S hS] at h; exact h

theorem pTotal_sound (hS : ∀ w ∈ S, IsCanon w) (h : pTotal (blist S) (instSer q) = true) :
    ∀ i ∈ q.tnI.ids, ∃ p, cfG (.wit p i) ∈ decSt S := by
  intro i hi
  have h1 := (atL_ids_all _ q _ _ _).1 h i hi
  rw [pTotalBody1] at h1
  obtain ⟨f, hf, h2⟩ := (anyE_S hS _ _ _ _).1 h1
  rw [pTotalBody2, entN_tail, witNode_entN] at h2
  obtain ⟨p, rfl⟩ := h2; exact ⟨p, hf⟩

theorem pEndp_sound (hS : ∀ w ∈ S, IsCanon w) (h : pEndp (blist S) (instSer q) = true) :
    ∀ e ∈ q.tnI.ordList,
      (∃ p, cfG (.wit p e.1) ∈ decSt S) ∧ (∃ p, cfG (.wit p e.2) ∈ decSt S) := by
  intro e he
  have h0 := (atL_ord_all _ q _ _ _).1 h e he
  simp only [pEndpBody, Bool.and_eq_true] at h0
  obtain ⟨h1, h2⟩ := h0
  obtain ⟨f, hf, h1⟩ := (anyE_S hS _ _ _ _).1 h1
  obtain ⟨f', hf', h2⟩ := (anyE_S hS _ _ _ _).1 h2
  rw [pEndpFst, witFst_iff, witNode_entN] at h1
  rw [pEndpSnd, witSnd_iff, witNode_entN] at h2
  obtain ⟨p, rfl⟩ := h1; obtain ⟨p', rfl⟩ := h2
  exact ⟨⟨p, hf⟩, ⟨p', hf'⟩⟩

theorem pFunc_sound (hS : ∀ w ∈ S, IsCanon w) (h : pFunc (blist S) = true) {p p' a : ℕ}
    (h1 : cfG (.wit p a) ∈ decSt S) (h2 : cfG (.wit p' a) ∈ decSt S) : p = p' := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  rw [pFuncBody1] at h3
  have h4 := (allE_S hS _ _ _ _).1 h3 _ h2
  rw [pFuncBody2] at h4
  have hs : sameNode (entN (cfG (.wit p a))) (entN (cfG (.wit p' a))) = true :=
    (sameNode_iff (drop_entG_wit p a) (drop_entG_wit p' a)).2 rfl
  rw [hs, decide_eq_true (kp_entG_wit p a), decide_eq_true (kp_entG_wit p' a)] at h4
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h4
  exact (GF.wit.inj (cfG_injective (entN_injective h4))).1

theorem pInj_sound (hS : ∀ w ∈ S, IsCanon w) (h : pInj (blist S) (instSer q) = true)
    {p i j : ℕ} (hi : i ∈ q.tnI.ids) (hj : j ∈ q.tnI.ids)
    (h1 : cfG (.wit p i) ∈ decSt S) (h2 : cfG (.wit p j) ∈ decSt S) : i = j := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  rw [pInjBody1] at h3
  have h4 := (allE_S hS _ _ _ _).1 h3 _ h2
  rw [pInjBody2] at h4
  rw [(witId_entN _ q).2 ⟨p, i, hi, rfl⟩, (witId_entN _ q).2 ⟨p, j, hj, rfl⟩,
    (samePos_iff (drop_entG_wit p i) (drop_entG_wit p j)).2 rfl] at h4
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h4
  exact (GF.wit.inj (cfG_injective (entN_injective h4))).2

theorem pDown_sound (hS : ∀ w ∈ S, IsCanon w) (h : pDown (blist S) (instSer q) = true)
    {p i : ℕ} (hi : i ∈ q.tnI.ids) (h1 : cfG (.wit (p + 1) i) ∈ decSt S) :
    ∃ j ∈ q.tnI.ids, cfG (.wit p j) ∈ decSt S := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  rw [pDownBody1, (witId_entN _ q).2 ⟨p + 1, i, hi, rfl⟩] at h3
  have hz : posZero (entN (cfG (.wit (p + 1) i))) = false := by
    rw [Bool.eq_false_iff]; intro hz
    exact absurd ((posZero_iff (drop_entG_wit _ i)).1 hz) (by omega)
  rw [hz] at h3; simp only [Bool.not_true, Bool.false_or] at h3
  obtain ⟨f, hf, h4⟩ := (anyE_S hS _ _ _ _).1 h3
  rw [pDownBody2, Bool.and_eq_true, witId_entN] at h4
  obtain ⟨⟨p', j, hj, rfl⟩, h5⟩ := h4
  rw [succPos_iff (drop_entG_wit p' j) (drop_entG_wit _ i)] at h5
  obtain rfl : p' = p := by omega
  exact ⟨j, hj, hf⟩

theorem pMono_sound (hS : ∀ w ∈ S, IsCanon w) (h : pMono (blist S) (instSer q) = true)
    {e : ℕ × ℕ} (he : e ∈ q.tnI.ordList) {p p' : ℕ}
    (h1 : cfG (.wit p e.1) ∈ decSt S) (h2 : cfG (.wit p' e.2) ∈ decSt S) : p ≤ p' := by
  have h3 := (atL_ord_all _ q _ _ _).1 h e he
  rw [pMonoBody1] at h3
  have h4 := (allE_S hS _ _ _ _).1 h3 _ h1
  rw [pMonoBody2] at h4
  have h5 := (allE_S hS _ _ _ _).1 h4 _ h2
  rw [pMonoBody3, (witFst_iff _ e).2 ((witNode_entN _ _).2 ⟨p, rfl⟩),
    (witSnd_iff _ e).2 ((witNode_entN _ _).2 ⟨p', rfl⟩)] at h5
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h5
  exact (lePos_iff (drop_entG_wit p e.1) (drop_entG_wit p' e.2)).1 h5

theorem pLab_sound (hS : ∀ w ∈ S, IsCanon w) (h : pLab (blist S) (instSer q) = true)
    {p i : ℕ} (hi : i ∈ q.tnI.ids) (h1 : cfG (.wit p i) ∈ decSt S) :
    cfG (.lab p (q.tnI.label i)) ∈ decSt S := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  rw [pLabBody1, atL_ids_all] at h3
  have h4 := h3 i hi
  rw [pLabBody2, entN_tail, (witNode_entN _ _).2 ⟨p, rfl⟩] at h4
  simp only [Bool.not_true, Bool.false_or] at h4
  obtain ⟨f, hf, h5⟩ := (anyE_S hS _ _ _ _).1 h4
  rw [labOkX_eq, labOk_iff] at h5
  rwa [entN_injective h5] at hf

theorem pNop_sound (hS : ∀ w ∈ S, IsCanon w) (h : pNop (blist S) (tblAdv b (markRows d K ++ T)) = true)
    {p : ℕ} {x : ℕ ⊕ ℕ} (h1 : cfG (.lab p x) ∈ decSt S) (hx : unknownPrimB d x = true) :
    cfG (.nop p) ∈ decSt S := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  have hu : unknownD (entN (cfG (.lab p x))) (tblAdv b (markRows d K ++ T)) = true := by
    rw [unknownD_iff]
    cases x with
    | inl a0 => exact ⟨a0, rfl, fun hm => (by simpa [unknownPrimB] using hx : a0 ∉ vocA d) hm.1⟩
    | inr c => simp [unknownPrimB] at hx
  rw [pNopBody1, hu, decide_eq_true (kp_entG_lab p x)] at h3
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h3
  obtain ⟨f, hf, h4⟩ := (anyE_S hS _ _ _ _).1 h3
  simp only [pNopBody2, Bool.and_eq_true, decide_eq_true_eq] at h4
  obtain ⟨⟨hpre, hend⟩, hsame⟩ := h4
  obtain ⟨p', hp'⟩ := posEnd_split rfl hpre hend
  have hfp : f = cfG (.nop p') := entN_injective (hp'.trans (entG_nop p').symm)
  subst hfp
  rw [samePos_iff (drop_entG_lab p x) (drop_entG_nop p')] at hsame
  rwa [hsame]

theorem pLen_sound (hS : ∀ w ∈ S, IsCanon w) (h : pLen (blist S) = true) :
    ∃ k, cfG (.len k) ∈ decSt S := by
  obtain ⟨f, hf, h4⟩ := (anyE_S hS _ _ _ _).1 h
  simp only [pLenBody, Bool.and_eq_true, decide_eq_true_eq] at h4
  obtain ⟨k, hk⟩ := posEnd_split rfl h4.1 h4.2
  exact ⟨k, entN_injective (hk.trans (entG_len k).symm) ▸ hf⟩

/-- The classification, for gadget facts. -/
theorem classify_cfG (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOk d K q b T S) {g : GF} (hg : cfG g ∈ decSt S) :
    g = .cur 0 ∨ (∃ p a, a ∈ wnodes q.tnI ∧ g = .wit p a) ∨
      (∃ p i, i ∈ q.tnI.ids ∧ cfG (.wit p i) ∈ decSt S ∧ g = .lab p (q.tnI.label i)) ∨
      (∃ p a0, cfG (.lab p (Sum.inl a0)) ∈ decSt S ∧ a0 ∉ vocA d ∧ g = .nop p) ∨
      (∃ k, (∀ p y, cfG (.lab p y) ∈ decSt S → p ≠ k) ∧
        (k = 0 ∨ ∃ y, cfG (.lab (k - 1) y) ∈ decSt S) ∧ g = .len k) := by
  rcases classify hS hK hall hg with ⟨v, -, he⟩ | he | he | ⟨p, a, ha, he⟩ | ⟨p, i, hi, hw, he⟩ |
      ⟨p, a0, hl, ha, he⟩ | ⟨k, h1, h2, he⟩
  · exact absurd he.symm (cfI_ne_cfG v g)
  · exact absurd he (cfG_ne_cRoot g d)
  · exact Or.inl (cfG_injective he)
  · exact Or.inr (Or.inl ⟨p, a, ha, cfG_injective he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, i, hi, hw, cfG_injective he⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, a0, hl, ha, cfG_injective he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, h1, h2, cfG_injective he⟩)))

/-- A witness position `k` without witness whose predecessor has one is the number of nodes. -/
theorem WitOk_len_eq {t : TnDesc} {ws : List (ℕ × ℕ)} (h : WitOk t ws) {k : ℕ}
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

/-- **Soundness of the initial test.** -/
theorem initOk_of_seqInitB (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (h : seqInitB (blist S) (instSer q) (tblAdv b (markRows d K ++ T)) = true) :
    InitOk d q (decSt S) := by
  simp only [seqInitB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hI⟩, hR⟩, hC⟩, hT⟩, hE⟩, hF⟩, hJ⟩, hD⟩, hM⟩, hL⟩, hN⟩, hLen⟩, -⟩ := h
  have hall : AllOk d K q b T S := (allE_S hS _ _ _ _).1 hA
  have hwit : WitOk q.tnI (witList (decSt S)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨p, hp⟩ := pTotal_sound hS hT i hi
      exact ⟨p, mem_witList.2 hp⟩
    · intro e he
      obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := pEndp_sound hS hE e he
      exact ⟨⟨p, mem_witList.2 hp⟩, ⟨p', mem_witList.2 hp'⟩⟩
    · intro p p' a h1 h2
      exact pFunc_sound hS hF (mem_witList.1 h1) (mem_witList.1 h2)
    · intro p i j hi hj h1 h2
      exact pInj_sound hS hJ hi hj (mem_witList.1 h1) (mem_witList.1 h2)
    · intro p i hi h1
      obtain ⟨j, hj, hw⟩ := pDown_sound hS hD hi (mem_witList.1 h1)
      exact ⟨j, hj, mem_witList.2 hw⟩
    · intro e he p p' h1 h2
      exact pMono_sound hS hM he (mem_witList.1 h1) (mem_witList.1 h2)
  have hlab : ∀ p x, cfG (.lab p x) ∈ decSt S ↔
      ∃ i ∈ q.tnI.ids, cfG (.wit p i) ∈ decSt S ∧ q.tnI.label i = x := by
    intro p x
    constructor
    · intro hg
      rcases classify_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨p', i, hi, hw, he⟩ |
          ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
      exact ⟨i, hi, hw, rfl⟩
    · rintro ⟨i, hi, hw, rfl⟩
      exact pLab_sound hS hL hi hw
  have hlen1 : ∀ k, cfG (.len k) ∈ decSt S →
      (∀ i ∈ q.tnI.ids, cfG (.wit k i) ∉ decSt S) ∧
        (k = 0 ∨ ∃ i ∈ q.tnI.ids, cfG (.wit (k - 1) i) ∈ decSt S) := by
    intro k hg
    rcases classify_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
        ⟨_, _, _, _, he⟩ | ⟨k', h1, h2, he⟩ <;> cases he
    refine ⟨fun i hi hw => h1 k _ (pLab_sound hS hL hi hw) rfl, ?_⟩
    rcases h2 with h2 | ⟨y, hy⟩
    · exact Or.inl h2
    · obtain ⟨i, hi, hw, -⟩ := (hlab _ _).1 hy
      exact Or.inr ⟨i, hi, hw⟩
  refine ⟨?_, pRoot_sound hS hR, ?_, ?_, ?_, hwit, hlab, ?_, ?_⟩
  · intro f hf
    rcases classify hS hK hall hf with ⟨v, -, he⟩ | he | he | ⟨p, a, -, he⟩ | ⟨p, i, -, -, he⟩ |
        ⟨p, a0, -, -, he⟩ | ⟨k, -, -, he⟩
    · exact Or.inl ⟨v, he⟩
    · exact Or.inr (Or.inr he)
    all_goals exact Or.inr (Or.inl ⟨_, he⟩)
  · intro v
    constructor
    · intro hv
      rcases classify hS hK hall hv with ⟨v', hv', he⟩ | he | he | ⟨p, a, -, he⟩ | ⟨p, i, -, -, he⟩ |
          ⟨p, a0, -, -, he⟩ | ⟨k, -, -, he⟩
      · rwa [cfI_injective he]
      · exact absurd he (cfI_ne_cRoot v d)
      all_goals exact absurd he (cfI_ne_cfG _ _)
    · exact pInst_sound hS hI
  · intro p
    constructor
    · intro hg
      rcases classify_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
          ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
      rfl
    · rintro rfl; exact pCur_sound hS hC
  · intro hg
    rcases classify_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
        ⟨_, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he
  · intro p
    constructor
    · intro hg
      rcases classify_cfG hS hK hall hg with he | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
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
      have e1 := WitOk_len_eq hwit (k := k) (fun i hi hw => h1 i hi (mem_witList.1 hw))
        (h2.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, mem_witList.2 hw⟩)
      have e2 := WitOk_len_eq hwit (k := k0) (fun i hi hw => h1' i hi (mem_witList.1 hw))
        (h2'.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, mem_witList.2 hw⟩)
      rwa [e1, ← e2]

end Presence

end SeqM

end Space

end HTN
