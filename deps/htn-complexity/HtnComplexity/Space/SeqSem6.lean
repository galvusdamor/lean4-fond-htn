import HtnComplexity.Space.SeqSem5
/-!
# Completeness of the initial test of the gadget machine

`HTN.Space.SeqM.seqInitB_of_initOk`: a configuration of canonical numerals that satisfies the
local conditions `HTN.Space.SeqM.InitOk`, whose witness facts name nodes of the network and
positions at most the number of identifiers, passes the initial test `seqInitB`.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

theorem bimp {P Q : Bool} (h : P = true → Q = true) : (!P || Q) = true := by
  cases P <;> simp_all

section Complete

variable {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row} {S : List (List Bool)}

theorem entN_cfI (v : ℕ) : entN (cfI v) = true :: bstr (tagI3 ++ bitsOfNat v) := by
  rw [entN, bitsOfNat_cfI]

theorem kp_entG_nop (p : ℕ) : kp tNop <+: entN (cfG (.nop p)) := by
  unfold entN; rw [entG_nop]; exact List.prefix_append _ _

theorem kp_entG_len (p : ℕ) : kp tLen <+: entN (cfG (.len p)) := by
  unfold entN; rw [entG_len]; exact List.prefix_append _ _

theorem prefix_gadget (hI : InitOk d q (decSt S)) {t : List Bool} {f : ℕ} (hf : f ∈ decSt S)
    (h : kp t <+: entN f) : ∃ g, f = cfG g ∧ t <+: gbits g := by
  rcases hI.shape f hf with ⟨v, rfl⟩ | ⟨g, rfl⟩ | rfl
  · rw [entN_cfI] at h; exact absurd h (kp_not_inst _ _)
  · exact ⟨g, rfl, (kp_ent_cfG g).1 h⟩
  · exact absurd h (kp_not_root _ _)

theorem gbits_lab {g : GF} (h : tLab <+: gbits g) : ∃ p y, g = .lab p y := by
  cases g <;> simp [gbits, tLab, List.cons_prefix_cons] at h ⊢

theorem gbits_wit {g : GF} (h : tWit <+: gbits g) : ∃ p a, g = .wit p a := by
  cases g <;> simp [gbits, tWit, List.cons_prefix_cons] at h ⊢

theorem gbits_len {g : GF} (h : tLen <+: gbits g) : ∃ k, g = .len k := by
  cases g <;> simp [gbits, tLen, List.cons_prefix_cons] at h ⊢

theorem lab_of_prefix (hI : InitOk d q (decSt S)) {f : ℕ} (hf : f ∈ decSt S)
    (h : kp tLab <+: entN f) : ∃ p y, f = cfG (.lab p y) := by
  obtain ⟨g, rfl, hg⟩ := prefix_gadget hI hf h
  obtain ⟨p, y, rfl⟩ := gbits_lab hg
  exact ⟨p, y, rfl⟩

theorem wit_of_prefix (hI : InitOk d q (decSt S)) {f : ℕ} (hf : f ∈ decSt S)
    (h : kp tWit <+: entN f) : ∃ p a, f = cfG (.wit p a) := by
  obtain ⟨g, rfl, hg⟩ := prefix_gadget hI hf h
  obtain ⟨p, a, rfl⟩ := gbits_wit hg
  exact ⟨p, a, rfl⟩

theorem len_of_prefix (hI : InitOk d q (decSt S)) {f : ℕ} (hf : f ∈ decSt S)
    (h : kp tLen <+: entN f) : ∃ k, f = cfG (.len k) := by
  obtain ⟨g, rfl, hg⟩ := prefix_gadget hI hf h
  obtain ⟨k, rfl⟩ := gbits_len hg
  exact ⟨k, rfl⟩

theorem unknown_of_prim {x : ℕ ⊕ ℕ} (hu : unknownPrimB d x = true) :
    ∃ a0, x = Sum.inl a0 ∧ a0 ∉ vocA d := by
  cases x with
  | inl a0 => exact ⟨a0, rfl, by simpa [unknownPrimB] using hu⟩
  | inr c => simp [unknownPrimB] at hu

theorem len_card_of_initOk (hI : InitOk d q (decSt S)) {k : ℕ} (hk : cfG (.len k) ∈ decSt S) :
    k = q.tnI.ids.toFinset.card := by
  obtain ⟨h1, h2⟩ := (hI.len k).1 hk
  exact WitOk_len_eq hI.wit (fun i hi hw => h1 i hi (mem_witList.1 hw))
    (h2.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, mem_witList.2 hw⟩)

theorem len_mem_of_initOk (hI : InitOk d q (decSt S)) :
    cfG (.len q.tnI.ids.toFinset.card) ∈ decSt S := by
  refine (hI.len _).2 ⟨fun i hi hw => lt_irrefl _ (hI.wit.exists_id_iff.1 ⟨i, hi, mem_witList.2 hw⟩),
    ?_⟩
  rcases Nat.eq_zero_or_pos q.tnI.ids.toFinset.card with h0 | h0
  · exact Or.inl h0
  · obtain ⟨i, hi, hw⟩ := hI.wit.exists_id_iff.2 (Nat.sub_lt h0 Nat.one_pos)
    exact Or.inr ⟨i, hi, mem_witList.1 hw⟩

/-- Every fact of a configuration satisfying the local conditions passes the entry test. -/
theorem entryOk_of_initOk (hS : ∀ w ∈ S, IsCanon w) (hI : InitOk d q (decSt S))
    (hW : ∀ p a, cfG (.wit p a) ∈ decSt S → a ∈ wnodes q.tnI) {f : ℕ} (hf : f ∈ decSt S) :
    entryOk (entN f) (blist S) (instSer q) (tblAdv b (markRows d K ++ T)) = true := by
  simp only [entryOk, Bool.or_eq_true]
  rcases hI.shape f hf with ⟨v, rfl⟩ | ⟨g, rfl⟩ | rfl
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_)))))
    exact (kInst_iff _ q).2 ⟨v, (hI.inst v).1 hf, entN_cfI v⟩
  · cases g with
    | cur p =>
      obtain rfl := (hI.cur p).1 hf
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
      rw [kCur, entCur0_eq, decide_eq_true_eq]
    | fin => exact absurd hf hI.fin
    | wit p a =>
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      exact (witAny_iff _ q).2 ⟨a, hW p a hf, (witNode_entN _ _).2 ⟨p, rfl⟩⟩
    | lab p x =>
      refine Or.inl (Or.inl (Or.inr ?_))
      obtain ⟨i, hi, hw, rfl⟩ := (hI.lab p x).1 hf
      simp only [kLab, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨kp_entG_lab p _, (anyE_S hS _ _ _ _).2 ⟨_, hw, ?_⟩⟩
      rw [kLabBody1, atL_ids_any]
      refine ⟨i, hi, ?_⟩
      simp only [kLabBody2, Bool.and_eq_true]
      refine ⟨by rw [entN_tail]; exact (witNode_entN _ _).2 ⟨p, rfl⟩, ?_⟩
      rw [labOkX_eq, labOk_iff]
    | nop p =>
      refine Or.inl (Or.inr ?_)
      obtain ⟨i, hi, hw, hu⟩ := (hI.nop p).1 hf
      have hl := (hI.lab p _).2 ⟨i, hi, hw, rfl⟩
      simp only [kNop, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨kp_entG_nop p, (posEnd_iff _).2 ⟨p, drop_entG_nop p⟩⟩,
        (anyE_S hS _ _ _ _).2 ⟨_, hl, ?_⟩⟩
      simp only [kNopBody, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨kp_entG_lab p _, (samePos_iff (drop_entG_nop p) (drop_entG_lab p _)).2 rfl⟩, ?_⟩
      obtain ⟨a0, ha0, hna⟩ := unknown_of_prim hu
      exact (unknownD_iff d K b T p _).2 ⟨a0, ha0, fun hm => hna hm.1⟩
    | len k =>
      refine Or.inr ?_
      obtain ⟨h1, h2⟩ := (hI.len k).1 hf
      simp only [kLen, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      refine ⟨⟨⟨kp_entG_len k, (posEnd_iff _).2 ⟨k, drop_entG_len k⟩⟩, ?_⟩, ?_⟩
      · refine (allE_S hS _ _ _ _).2 fun f' hf' => ?_
        by_cases hp : kp tLab <+: entN f'
        · obtain ⟨p', y, rfl⟩ := lab_of_prefix hI hf' hp
          have hs : samePos (entN (cfG (.len k))) (entN (cfG (.lab p' y))) = false := by
            rw [Bool.eq_false_iff]; intro hs
            rw [samePos_iff (drop_entG_len k) (drop_entG_lab p' y)] at hs
            subst hs
            obtain ⟨i, hi, hw, -⟩ := (hI.lab _ _).1 hf'
            exact h1 i hi hw
          simp [kLenBody1, hs]
        · simp [kLenBody1, hp]
      · rcases h2 with rfl | ⟨i, hi, hw⟩
        · exact Or.inl ((posZero_iff (drop_entG_len 0)).2 rfl)
        · refine Or.inr ((anyE_S hS _ _ _ _).2 ⟨_, (hI.lab _ _).2 ⟨i, hi, hw, rfl⟩, ?_⟩)
          simp only [kLenBody2, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨kp_entG_lab _ _, (succPos_iff (drop_entG_lab _ _) (drop_entG_len k)).2 ?_⟩
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · exact absurd hw (h1 i hi)
          · omega
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))
    rw [entN, kRoot_iff d K b T (isCanon_bitsOfNat _), natOfBits_bitsOfNat]

/-- **Completeness of the initial test.** -/
theorem seqInitB_of_initOk (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hI : InitOk d q (decSt S))
    (hW : ∀ p a, cfG (.wit p a) ∈ decSt S → a ∈ wnodes q.tnI ∧ p ≤ q.tnI.ids.toFinset.card) :
    seqInitB (blist S) (instSer q) (tblAdv b (markRows d K ++ T)) = true := by
  have hwit : ∀ p a, cfG (.wit p a) ∈ decSt S ↔ (p, a) ∈ witList (decSt S) :=
    fun p a => mem_witList.symm
  simp only [seqInitB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- entries
    exact (allE_S hS _ _ _ _).2 fun f hf =>
      entryOk_of_initOk hS hI (fun p a h => (hW p a h).1) hf
  · -- instance facts
    refine (pInst_iff S q).2 fun v hv => ?_
    rw [← bitsOfNat_cfI, ← mem_S_iff hS]
    exact (hI.inst v).2 hv
  · -- root
    refine (anyE_S hS _ _ _ _).2 ⟨_, hI.root, ?_⟩
    rw [pRootBody, entN, kRoot_iff d K b T (isCanon_bitsOfNat _), natOfBits_bitsOfNat]
  · -- cur
    rw [pCur, entCur0_eq, occB_S hS]
    exact (hI.cur 0).2 rfl
  · -- total
    refine (atL_ids_all _ q _ _ _).2 fun i hi => ?_
    obtain ⟨p, hp⟩ := hI.wit.total i hi
    rw [pTotalBody1]
    refine (anyE_S hS _ _ _ _).2 ⟨_, (hwit p i).2 hp, ?_⟩
    rw [pTotalBody2, entN_tail]
    exact (witNode_entN _ _).2 ⟨p, rfl⟩
  · -- endpoints
    refine (atL_ord_all _ q _ _ _).2 fun e he => ?_
    obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := hI.wit.endp e he
    simp only [pEndpBody, Bool.and_eq_true]
    refine ⟨(anyE_S hS _ _ _ _).2 ⟨_, (hwit p _).2 hp, ?_⟩,
      (anyE_S hS _ _ _ _).2 ⟨_, (hwit p' _).2 hp', ?_⟩⟩
    · rw [pEndpFst, witFst_iff]; exact (witNode_entN _ _).2 ⟨p, rfl⟩
    · rw [pEndpSnd, witSnd_iff]; exact (witNode_entN _ _).2 ⟨p', rfl⟩
  · -- functionality
    refine (allE_S hS _ _ _ _).2 fun f hf => ?_
    rw [pFuncBody1]
    refine (allE_S hS _ _ _ _).2 fun f' hf' => ?_
    rw [pFuncBody2]
    refine bimp fun hc => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    obtain ⟨p, a, rfl⟩ := wit_of_prefix hI hf h1
    obtain ⟨p', a', rfl⟩ := wit_of_prefix hI hf' h2
    rw [sameNode_iff (drop_entG_wit p a) (drop_entG_wit p' a'), List.append_cancel_right_eq]
      at h3
    have ha : a = a' := bitsOfNat_injective (ent_inj (congrArg (true :: ·) (dbl_injective h3)))
    subst ha
    have := hI.wit.func p p' a ((hwit _ _).1 hf) ((hwit _ _).1 hf')
    subst this
    simp
  · -- injectivity
    refine (allE_S hS _ _ _ _).2 fun f hf => ?_
    rw [pInjBody1]
    refine (allE_S hS _ _ _ _).2 fun f' hf' => ?_
    rw [pInjBody2]
    refine bimp fun hc => ?_
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    obtain ⟨p, i, hi, rfl⟩ := (witId_entN _ q).1 h1
    obtain ⟨p', j, hj, rfl⟩ := (witId_entN _ q).1 h2
    rw [samePos_iff (drop_entG_wit p i) (drop_entG_wit p' j)] at h3
    subst h3
    have := hI.wit.inj p i j hi hj ((hwit _ _).1 hf) ((hwit _ _).1 hf')
    subst this
    simp
  · -- downward closure
    refine (allE_S hS _ _ _ _).2 fun f hf => ?_
    rw [pDownBody1, Bool.or_assoc]
    refine bimp fun hc => ?_
    obtain ⟨p, i, hi, rfl⟩ := (witId_entN _ q).1 hc
    rw [Bool.or_eq_true]
    rcases p with _ | p
    · exact Or.inl ((posZero_iff (drop_entG_wit 0 i)).2 rfl)
    · obtain ⟨j, hj, hw⟩ := hI.wit.down p i hi ((hwit _ _).1 hf)
      refine Or.inr ((anyE_S hS _ _ _ _).2 ⟨_, (hwit _ _).2 hw, ?_⟩)
      rw [pDownBody2, Bool.and_eq_true]
      exact ⟨(witId_entN _ q).2 ⟨p, j, hj, rfl⟩,
        (succPos_iff (drop_entG_wit p j) (drop_entG_wit _ i)).2 rfl⟩
  · -- monotonicity
    refine (atL_ord_all _ q _ _ _).2 fun e he => ?_
    rw [pMonoBody1]
    refine (allE_S hS _ _ _ _).2 fun f hf => ?_
    rw [pMonoBody2]
    refine (allE_S hS _ _ _ _).2 fun f' hf' => ?_
    rw [pMonoBody3]
    refine bimp fun hc => ?_
    rw [Bool.and_eq_true, witFst_iff, witSnd_iff, witNode_entN, witNode_entN] at hc
    obtain ⟨⟨p, rfl⟩, ⟨p', rfl⟩⟩ := hc
    exact (lePos_iff (drop_entG_wit p e.1) (drop_entG_wit p' e.2)).2
      (hI.wit.mono e he p p' ((hwit _ _).1 hf) ((hwit _ _).1 hf'))
  · -- labels
    refine (allE_S hS _ _ _ _).2 fun f hf => ?_
    rw [pLabBody1, atL_ids_all]
    intro i hi
    rw [pLabBody2]
    refine bimp fun hc => ?_
    rw [entN_tail, witNode_entN] at hc
    obtain ⟨p, rfl⟩ := hc
    refine (anyE_S hS _ _ _ _).2 ⟨_, (hI.lab p _).2 ⟨i, hi, hf, rfl⟩, ?_⟩
    rw [labOkX_eq, labOk_iff]
  · -- nop
    refine (allE_S hS _ _ _ _).2 fun f hf => ?_
    rw [pNopBody1]
    refine bimp fun hc => ?_
    rw [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨p, y, rfl⟩ := lab_of_prefix hI hf h1
    obtain ⟨a0, rfl, ha0⟩ := (unknownD_iff d K b T p _).1 h2
    obtain ⟨i, hi, hw, hli⟩ := (hI.lab _ _).1 hf
    have ha0' : a0 ∉ vocA d := fun hm => ha0 ⟨hm, (bits_le_of_label hli).trans hK⟩
    have hn : cfG (.nop p) ∈ decSt S :=
      (hI.nop p).2 ⟨i, hi, hw, by rw [hli]; simp [unknownPrimB, ha0']⟩
    refine (anyE_S hS _ _ _ _).2 ⟨_, hn, ?_⟩
    simp only [pNopBody2, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨kp_entG_nop p, (posEnd_iff _).2 ⟨p, drop_entG_nop p⟩⟩,
      (samePos_iff (drop_entG_lab p _) (drop_entG_nop p)).2 rfl⟩
  · -- len
    refine (anyE_S hS _ _ _ _).2 ⟨_, len_mem_of_initOk hI, ?_⟩
    simp only [pLenBody, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨kp_entG_len _, (posEnd_iff _).2 ⟨_, drop_entG_len _⟩⟩
  · -- bound
    refine (allE_S hS _ _ _ _).2 fun f hf => ?_
    rw [pBndBody1]
    refine bimp fun hc => ?_
    rw [decide_eq_true_eq] at hc
    obtain ⟨p, a, rfl⟩ := wit_of_prefix hI hf hc
    refine (allE_S hS _ _ _ _).2 fun f' hf' => ?_
    rw [pBndBody2]
    refine bimp fun hc' => ?_
    rw [decide_eq_true_eq] at hc'
    obtain ⟨k, rfl⟩ := len_of_prefix hI hf' hc'
    rw [lePos_iff (drop_entG_wit p a) (drop_entG_len k), len_card_of_initOk hI hf']
    exact (hW p a hf).2

end Complete

end SeqM

end Space

end HTN
