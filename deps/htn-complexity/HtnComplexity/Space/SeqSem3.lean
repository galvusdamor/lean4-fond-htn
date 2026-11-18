import HtnComplexity.Space.SeqSem2
/-!
# Soundness of the initial test of the gadget machine

`HTN.Space.SeqM.initOk_of_seqInitB`: a configuration of canonical numerals that passes the
initial test `seqInitB` (against the code of the instance and an advice whose table starts with
the two marker rows) satisfies the local conditions `HTN.Space.SeqM.InitOk`.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### Entries of numerals -/

/-- The encoded entry of the numeral of `f`. -/
abbrev entN (f : ℕ) : List Bool := true :: bstr (bitsOfNat f)

theorem ent_inj {w w' : List Bool} (h : true :: bstr w = true :: bstr w') : w = w' :=
  (bstr_parse (r := []) (s := []) (by simpa using h)).1

theorem entN_injective : Function.Injective entN := fun _ _ h => bitsOfNat_injective (ent_inj h)

theorem ent_canon {w : List Bool} (hw : IsCanon w) : true :: bstr w = entN (natOfBits w) := by
  rw [entN, hw]

theorem natOfBits_of_ent {w : List Bool} {f : ℕ} (h : true :: bstr w = entN f) : natOfBits w = f := by
  rw [ent_inj h, natOfBits_bitsOfNat]

theorem kp_eq_of_prefix {t t' E : List Bool} (ht : t.length = 3) (ht' : t'.length = 3)
    (h : kp t <+: E) (h' : kp t' <+: E) : t = t' := by
  have hp := List.prefix_of_prefix_length_le h h' (by simp [length_kp ht, length_kp ht'])
  have heq : kp t = kp t' := hp.eq_of_length (by simp [length_kp ht, length_kp ht'])
  simp only [kp, List.cons.injEq, true_and] at heq
  exact List.append_cancel_left (dbl_injective heq)

theorem kp_split {t E : List Bool} (ht : t.length = 3) (h : kp t <+: E) : E = kp t ++ E.drop 13 := by
  obtain ⟨s, rfl⟩ := h; rw [drop_kp ht]

theorem kp_not_inst (t : List Bool) (v : ℕ) : ¬ kp t <+: true :: bstr (tagI3 ++ bitsOfNat v) := by
  rw [kp_prefix_iff]; rintro ⟨s, hs⟩; simp [gT, tagI3] at hs

theorem kp_not_root (t : List Bool) (d : DomDesc) : ¬ kp t <+: entN (cRoot d) := by
  rw [entN, bitsOfNat_cRoot, kp_prefix_iff]; rintro ⟨s, hs⟩; simp [gT] at hs

theorem kp_ent_cfG {t : List Bool} (g : GF) : kp t <+: entN (cfG g) ↔ t <+: gbits g := by
  rw [entN, bitsOfNat_cfG, kp_prefix_iff, List.prefix_append_right_inj]

theorem kp_entG_wit (p a : ℕ) : kp tWit <+: entN (cfG (.wit p a)) := by
  unfold entN; rw [entG_wit]; exact List.prefix_append _ _

theorem kp_entG_lab (p : ℕ) (x : ℕ ⊕ ℕ) : kp tLab <+: entN (cfG (.lab p x)) := by
  unfold entN; rw [entG_lab]; exact List.prefix_append _ _

theorem drop_entG_wit (p a : ℕ) :
    (entN (cfG (.wit p a))).drop 13 = dbl (unary p) ++ (dbl (serNat a) ++ ttf) := by
  unfold entN; rw [entG_wit, drop_kp rfl]

theorem drop_entG_lab (p : ℕ) (x : ℕ ⊕ ℕ) :
    (entN (cfG (.lab p x))).drop 13 = dbl (unary p) ++ (dbl (lblBits x) ++ ttf) := by
  unfold entN; rw [entG_lab, drop_kp rfl]

theorem drop_entG_nop (p : ℕ) : (entN (cfG (.nop p))).drop 13 = dbl (unary p) ++ [false] := by
  unfold entN; rw [entG_nop, drop_kp rfl]

theorem drop_entG_len (p : ℕ) : (entN (cfG (.len p))).drop 13 = dbl (unary p) ++ [false] := by
  unfold entN; rw [entG_len, drop_kp rfl]

theorem witNode_entN (f a : ℕ) :
    witNode (entN f) (dbl (serNat a)) = true ↔ ∃ p, f = cfG (.wit p a) := witNode_ent_iff f a

theorem witId_entN (f : ℕ) (q : InstDesc) :
    witId (entN f) (instSer q) = true ↔ ∃ p, ∃ i ∈ q.tnI.ids, f = cfG (.wit p i) := by
  rw [witId_iff]
  simp only [witNode_entN]
  constructor
  · rintro ⟨i, hi, p, rfl⟩; exact ⟨p, i, hi, rfl⟩
  · rintro ⟨p, i, hi, rfl⟩; exact ⟨i, hi, p, rfl⟩

theorem length_lblBits_label_le {q : InstDesc} (i : ℕ) :
    (lblBits (q.tnI.label i)).length ≤ (instSer q).length + 2 := by
  rw [lblBits_label]
  rcases hl : q.tnI.lbl.lookup i with _ | ⟨b, n⟩
  · simp
  · have hmem := mem_of_lookup_eq_some hl
    have h1 := le_length_blist_of_mem (List.mem_map_of_mem (f := serLbl) hmem)
    have hx := congrArg List.length (instSer_split q)
    simp only [List.length_append] at hx
    simp only [serLbl, List.length_append, List.length_cons] at h1 ⊢
    omega

/-- A primitive task of a label of the instance has a numeral no longer than the code. -/
theorem bits_le_of_label {q : InstDesc} {i a0 : ℕ} (h : q.tnI.label i = Sum.inl a0) :
    (bitsOfNat a0).length ≤ (instSer q).length := by
  have := length_lblBits_label_le (q := q) i
  rw [h] at this
  simp [lblBits, serNat] at this
  omega

/-! ### Quantifiers over the code -/

theorem atL_ids_any (P : List Bool → List Bool → List Bool → List Bool → Bool) (q : InstDesc)
    (v₁ v₂ v₃ : List Bool) :
    atL 2 (anyE P) (instSer q) v₁ v₂ v₃ = true ↔ ∃ i ∈ q.tnI.ids, P (entN i) v₁ v₂ v₃ = true := by
  rw [instSer_split, atL_succ, atL_succ, atL_zero, anyE_iff]; simp

theorem atL_ids_all (P : List Bool → List Bool → List Bool → List Bool → Bool) (q : InstDesc)
    (v₁ v₂ v₃ : List Bool) :
    atL 2 (allE P) (instSer q) v₁ v₂ v₃ = true ↔ ∀ i ∈ q.tnI.ids, P (entN i) v₁ v₂ v₃ = true := by
  rw [instSer_split, atL_succ, atL_succ, atL_zero, allE_iff]; simp

theorem atL_ord_all (P : List Bool → List Bool → List Bool → List Bool → Bool) (q : InstDesc)
    (v₁ v₂ v₃ : List Bool) :
    atL 3 (allE P) (instSer q) v₁ v₂ v₃ = true ↔
      ∀ e ∈ q.tnI.ordList, P (true :: bstr (serPair e)) v₁ v₂ v₃ = true := by
  rw [instSer_split, atL_succ, atL_succ, atL_succ, atL_zero, allE_iff]; simp
  constructor
  · intro h a b hab; exact h _ a b hab rfl
  · rintro h w a b hab rfl; exact h a b hab

/-! ### The configuration -/

section Config

variable {S : List (List Bool)}

theorem mem_S_iff (hS : ∀ w ∈ S, IsCanon w) (f : ℕ) : f ∈ decSt S ↔ bitsOfNat f ∈ S :=
  mem_decSt_iff hS f

theorem anyE_S (hS : ∀ w ∈ S, IsCanon w) (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (v₁ v₂ v₃ : List Bool) :
    anyE P (blist S) v₁ v₂ v₃ = true ↔ ∃ f ∈ decSt S, P (entN f) v₁ v₂ v₃ = true := by
  rw [anyE_blist_iff]
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨natOfBits w, (mem_S_iff hS _).2 (by rw [hS w hw]; exact hw), ?_⟩
    rwa [← ent_canon (hS w hw)]
  · rintro ⟨f, hf, h⟩
    exact ⟨bitsOfNat f, (mem_S_iff hS f).1 hf, h⟩

theorem allE_S (hS : ∀ w ∈ S, IsCanon w) (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (v₁ v₂ v₃ : List Bool) :
    allE P (blist S) v₁ v₂ v₃ = true ↔ ∀ f ∈ decSt S, P (entN f) v₁ v₂ v₃ = true := by
  rw [allE_blist_iff]
  constructor
  · intro h f hf
    exact h _ ((mem_S_iff hS f).1 hf)
  · intro h w hw
    rw [ent_canon (hS w hw)]
    exact h _ ((mem_S_iff hS _).2 (by rw [hS w hw]; exact hw))

theorem occB_S (hS : ∀ w ∈ S, IsCanon w) (f : ℕ) : occB (blist S) (entN f) = true ↔ f ∈ decSt S := by
  rw [entN, occB_blist, mem_S_iff hS]

end Config

/-! ### Classifying the entries -/

section Classify

variable {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row} {S : List (List Bool)}

/-- Every entry of the configuration is of an admitted kind. -/
def AllOk (d : DomDesc) (K : ℕ) (q : InstDesc) (b : Bool) (T : List Row) (S : List (List Bool)) : Prop :=
  ∀ f ∈ decSt S, entryOk (entN f) (blist S) (instSer q) (tblAdv b (markRows d K ++ T)) = true

theorem kLab_sound (hS : ∀ w ∈ S, IsCanon w) {f : ℕ}
    (h : kLab (entN f) (blist S) (instSer q) = true) :
    ∃ p i, i ∈ q.tnI.ids ∧ cfG (.wit p i) ∈ decSt S ∧ f = cfG (.lab p (q.tnI.label i)) := by
  simp only [kLab, Bool.and_eq_true] at h
  obtain ⟨f', hf', h⟩ := (anyE_S hS _ _ _ _).1 h.2
  rw [kLabBody1, atL_ids_any] at h
  obtain ⟨i, hi, h⟩ := h
  simp only [kLabBody2, Bool.and_eq_true, List.tail_cons] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨p, rfl⟩ := (witNode_entN f' i).1 h1
  rw [labOkX_eq, labOk_iff] at h2
  exact ⟨p, i, hi, hf', entN_injective h2⟩

theorem entry_lab (hS : ∀ w ∈ S, IsCanon w) (hall : AllOk d K q b T S) {f : ℕ} (hf : f ∈ decSt S)
    (hpre : kp tLab <+: entN f) :
    ∃ p i, i ∈ q.tnI.ids ∧ cfG (.wit p i) ∈ decSt S ∧ f = cfG (.lab p (q.tnI.label i)) := by
  have h := hall f hf
  simp only [entryOk, Bool.or_eq_true] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · obtain ⟨v, -, hE⟩ := (kInst_iff _ q).1 h
    rw [hE] at hpre; exact absurd hpre (kp_not_inst _ _)
  · rw [entN, kRoot_iff d K b T (isCanon_bitsOfNat f), natOfBits_bitsOfNat] at h
    rw [h] at hpre; exact absurd hpre (kp_not_root _ _)
  · rw [kCur, decide_eq_true_eq] at h
    rw [h, entCur0, kp_prefix_iff] at hpre; obtain ⟨s, hs⟩ := hpre
    simp [gT, tLab, gbits, unary] at hs
  · obtain ⟨a, -, hn⟩ := (witAny_iff _ q).1 h
    simp only [witNode, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact absurd (kp_eq_of_prefix rfl rfl hpre hn.1.1) (by decide)
  · exact kLab_sound hS h
  · simp only [kNop, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd (kp_eq_of_prefix rfl rfl hpre h.1.1) (by decide)
  · simp only [kLen, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd (kp_eq_of_prefix rfl rfl hpre h.1.1.1) (by decide)

theorem posEnd_split {t E : List Bool} (ht : t.length = 3) (hpre : kp t <+: E)
    (h : posEnd E = true) : ∃ p, E = kp t ++ (dbl (unary p) ++ [false]) := by
  obtain ⟨p, hp⟩ := (posEnd_iff E).1 h
  exact ⟨p, by rw [kp_split ht hpre, hp]⟩

/-- **The classification of the facts of a configuration that passes the entry test.** -/
theorem classify (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K) (hall : AllOk d K q b T S)
    {f : ℕ} (hf : f ∈ decSt S) :
    (∃ v ∈ q.initList, f = cfI v) ∨ f = cRoot d ∨ f = cfG (.cur 0) ∨
      (∃ p a, a ∈ wnodes q.tnI ∧ f = cfG (.wit p a)) ∨
      (∃ p i, i ∈ q.tnI.ids ∧ cfG (.wit p i) ∈ decSt S ∧ f = cfG (.lab p (q.tnI.label i))) ∨
      (∃ p a0, cfG (.lab p (Sum.inl a0)) ∈ decSt S ∧ a0 ∉ vocA d ∧ f = cfG (.nop p)) ∨
      (∃ k, (∀ p y, cfG (.lab p y) ∈ decSt S → p ≠ k) ∧
        (k = 0 ∨ ∃ y, cfG (.lab (k - 1) y) ∈ decSt S) ∧ f = cfG (.len k)) := by
  have h := hall f hf
  simp only [entryOk, Bool.or_eq_true] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · obtain ⟨v, hv, hE⟩ := (kInst_iff _ q).1 h
    refine Or.inl ⟨v, hv, ?_⟩
    rw [← bitsOfNat_cfI] at hE
    exact entN_injective hE
  · rw [entN, kRoot_iff d K b T (isCanon_bitsOfNat f), natOfBits_bitsOfNat] at h
    exact Or.inr (Or.inl h)
  · rw [kCur, decide_eq_true_eq, entCur0, ← bitsOfNat_cfG] at h
    exact Or.inr (Or.inr (Or.inl (entN_injective h)))
  · obtain ⟨a, ha, hn⟩ := (witAny_iff _ q).1 h
    obtain ⟨p, rfl⟩ := (witNode_entN f a).1 hn
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, a, ha, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (kLab_sound hS h)))))
  · simp only [kNop, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpre, hend⟩, h⟩ := h
    obtain ⟨p, hp⟩ := posEnd_split rfl hpre hend
    have hfp : f = cfG (.nop p) := entN_injective (hp.trans (entG_nop p).symm)
    subst hfp
    obtain ⟨f', hf', h⟩ := (anyE_S hS _ _ _ _).1 h
    simp only [kNopBody, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpre', hsame⟩, hunk⟩ := h
    obtain ⟨p', i, -, -, rfl⟩ := entry_lab hS hall hf' hpre'
    rw [samePos_iff (drop_entG_nop p) (drop_entG_lab p' _)] at hsame
    subst hsame
    obtain ⟨a0, ha0, hna⟩ := (unknownD_iff d K b T p _).1 hunk
    have hna' : a0 ∉ vocA d := fun hm => hna ⟨hm, (bits_le_of_label ha0).trans hK⟩
    rw [ha0] at hf'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, a0, hf', hna', rfl⟩)))))
  · simp only [kLen, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hpre, hend⟩, hall1⟩, hz⟩ := h
    obtain ⟨k, hk⟩ := posEnd_split rfl hpre hend
    have hfk : f = cfG (.len k) := entN_injective (hk.trans (entG_len k).symm)
    subst hfk
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, ?_, ?_, rfl⟩)))))
    · intro p y hpy hpk
      subst hpk
      have := (allE_S hS _ _ _ _).1 hall1 _ hpy
      simp only [kLenBody1, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      rcases this with h1 | h1
      · exact h1 (kp_entG_lab _ _)
      · have h2 := (samePos_iff (drop_entG_len p) (drop_entG_lab p y)).2 rfl
        rw [h1] at h2; exact Bool.false_ne_true h2
    · rcases hz with hz | hz
      · exact Or.inl ((posZero_iff (drop_entG_len k)).1 hz)
      · obtain ⟨f', hf', h⟩ := (anyE_S hS _ _ _ _).1 hz
        simp only [kLenBody2, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨p', i, -, -, rfl⟩ := entry_lab hS hall hf' h.1
        rw [succPos_iff (drop_entG_lab p' _) (drop_entG_len k)] at h
        refine Or.inr ⟨q.tnI.label i, ?_⟩
        rw [h.2, Nat.add_sub_cancel]; exact hf'

end Classify

end SeqM

end Space

end HTN
