import HtnComplexity.AcVerify.Verifier
/-!
# Records: their fields, and the record tests of the verifier

* `HTN.Syn.AcVer.enc_recOf` and `kat_recOf_*` — the encoded record of a step and its four fields;
* `HTN.Syn.AcVer.recOf_injective` — a record determines its step;
* `HTN.Syn.AcVer.rootRecB_iff` — the root test accepts exactly the records of the root steps;
* membership in the tables of method steps, dummy steps and heads.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space

/-! ### Keys -/

theorem key_parse {a b : ℕ} {r s : List Bool} (h : key a ++ r = key b ++ s) : a = b ∧ r = s := by
  rw [key_eq, key_eq] at h
  obtain ⟨h1, h2⟩ := dbl_bstr_parse h
  exact ⟨bitsOfNat_injective h1, h2⟩

theorem key_prefix_iff {a b : ℕ} {r s : List Bool} :
    key a ++ r <+: key b ++ s ↔ a = b ∧ r <+: s := by
  constructor
  · rintro ⟨t, ht⟩
    rw [List.append_assoc] at ht
    obtain ⟨h1, h2⟩ := key_parse ht
    exact ⟨h1, ⟨t, h2⟩⟩
  · rintro ⟨rfl, t, ht⟩
    exact ⟨t, by rw [List.append_assoc, ht]⟩

theorem key_ne_nil (a : ℕ) : key a ≠ [] := by
  rw [key_eq, bstr_eq_dbl, dbl_append]; simp [dbl]

theorem key_head (a : ℕ) : ∃ t, key a = true :: t := by
  rw [key_eq]
  rcases h : bstr (bitsOfNat a) with _ | ⟨c, r⟩
  · rw [bstr_eq_dbl] at h; simp at h
  · exact ⟨c :: dbl r, by rw [dbl_cons]⟩

/-! ### Labels and records -/

/-- The tag of a label: `0` for an action, `1` for a compound task. -/
def lTag : ℕ ⊕ ℕ → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The name of a label. -/
def lVal : ℕ ⊕ ℕ → ℕ
  | Sum.inl a => a
  | Sum.inr c => c

theorem lblSer_eq (l : ℕ ⊕ ℕ) : lblSer l = serNat (lTag l) ++ serNat (lVal l) := by
  cases l <;> rfl

theorem label_eq_of_tag_val {l l' : ℕ ⊕ ℕ} (h1 : lTag l = lTag l') (h2 : lVal l = lVal l') :
    l = l' := by
  cases l <;> cases l' <;> simp_all [lTag, lVal]

/-- A record of four numerals. -/
def rec4 (k j t v : ℕ) : List Bool := serNat k ++ serNat j ++ (serNat t ++ serNat v)

theorem enc_rec4 (k j t v : ℕ) :
    true :: bstr (rec4 k j t v) = true :: (key k ++ (key j ++ (key t ++ (key v ++ [false])))) := by
  simp only [rec4, List.append_assoc, bstr_serNat_append]
  rw [bstr_eq_dbl]; rfl

theorem recOf_eq_rec4 (d : DomDesc) (q : InstDesc) (x : PStep) :
    recOf d q x = rec4 x.1 x.2 (lTag (stepLabel d q x)) (lVal (stepLabel d q x)) := by
  simp [recOf, rec4, lblSer_eq]

theorem recM_eq_rec4 (d : DomDesc) (x : PStep) :
    recM d x = rec4 x.1 x.2 (lTag ((methodAt d x.1).2.label x.2))
      (lVal ((methodAt d x.1).2.label x.2)) := by
  simp [recM, rec4, lblSer_eq]

section
variable (k j t v : ℕ)
@[simp] theorem kat0_rec4 : kat 0 (true :: bstr (rec4 k j t v)) = key k := by
  rw [enc_rec4, kat_zero]
@[simp] theorem kat1_rec4 : kat 1 (true :: bstr (rec4 k j t v)) = key j := by
  rw [enc_rec4, kat_succ, kat_zero]
@[simp] theorem kat2_rec4 : kat 2 (true :: bstr (rec4 k j t v)) = key t := by
  rw [enc_rec4, kat_succ, kat_succ, kat_zero]
@[simp] theorem kat3_rec4 : kat 3 (true :: bstr (rec4 k j t v)) = key v := by
  rw [enc_rec4, kat_succ, kat_succ, kat_succ, kat_zero]
end

theorem rec4_parse {k j t v k' j' t' v' : ℕ} (h : rec4 k j t v = rec4 k' j' t' v') :
    k = k' ∧ j = j' ∧ t = t' ∧ v = v' := by
  simp only [rec4, List.append_assoc] at h
  obtain ⟨h1, h⟩ := serNat_parse h
  obtain ⟨h2, h⟩ := serNat_parse h
  obtain ⟨h3, h⟩ := serNat_parse h
  obtain ⟨h4, -⟩ := serNat_parse (r := []) (s := []) (by simpa using h)
  exact ⟨h1, h2, h3, h4⟩

theorem recOf_injective (d : DomDesc) (q : InstDesc) : Function.Injective (recOf d q) := by
  intro x y h
  rw [recOf_eq_rec4, recOf_eq_rec4] at h
  obtain ⟨h1, h2, -, -⟩ := rec4_parse h
  exact Prod.ext h1 h2

/-- The record of a step in the instance-independent form. -/
theorem recOf_eq_rec4_of {d : DomDesc} {q : InstDesc} {x : PStep} :
    true :: bstr (recOf d q x) = true :: (key x.1 ++ (key x.2 ++
      (key (lTag (stepLabel d q x)) ++ (key (lVal (stepLabel d q x)) ++ [false])))) := by
  rw [recOf_eq_rec4, enc_rec4]

/-! ### The root test -/

theorem undbl_dbl_bstr (v : List Bool) : undbl (dbl (bstr v)) = bstr v := undbl_dbl _

theorem prefix_bstr_iff {v u : List Bool} : bstr v <+: bstr u ↔ v = u := by
  have := bstr_prefix_iff v u []
  simpa using this

theorem kat2_recOf {d : DomDesc} {q : InstDesc} {x : PStep} :
    kat 2 (true :: bstr (recOf d q x)) = key (lTag (stepLabel d q x)) := by
  rw [recOf_eq_rec4, kat2_rec4]

theorem kat3_recOf {d : DomDesc} {q : InstDesc} {x : PStep} :
    kat 3 (true :: bstr (recOf d q x)) = key (lVal (stepLabel d q x)) := by
  rw [recOf_eq_rec4, kat3_rec4]

theorem kat0_recOf {d : DomDesc} {q : InstDesc} {x : PStep} :
    kat 0 (true :: bstr (recOf d q x)) = key x.1 := by
  rw [recOf_eq_rec4, kat0_rec4]

theorem kat1_recOf {d : DomDesc} {q : InstDesc} {x : PStep} :
    kat 1 (true :: bstr (recOf d q x)) = key x.2 := by
  rw [recOf_eq_rec4, kat1_rec4]

/-- The label part of the root test, on the instance. -/
theorem rootLbl_iff (q : InstDesc) {s : List Bool} {u : ℕ} (hnv : nvAt s = serNat u)
    {K2 K3 : List Bool} (hbd : isBDs K3 = true) :
    ((K2 = key 0 ∧ (lblB (false :: undbl K3) (instSer q) s = true ∨
        (K3 = key 0 ∧ lblB [] (instSer q) s = false))) ∨
      (K2 = key 1 ∧ lblB (true :: undbl K3) (instSer q) s = true)) ↔
    K2 = key (lTag (q.tnI.label u)) ∧ K3 = key (lVal (q.tnI.label u)) := by
  obtain ⟨v, rfl⟩ := (isBDs_iff _).1 hbd
  rw [show lblB [] (instSer q) s = false ↔ ¬ lblB [] (instSer q) s = true by simp]
  rw [undbl_dbl_bstr, lblB_iff q hnv, lblB_iff q hnv, lblB_iff q hnv]
  simp only [TnDesc.label]
  rcases hlk : q.tnI.lbl.lookup u with _ | ⟨b, n⟩
  · simp only [lTag, lVal, key_eq]
    constructor
    · rintro (⟨h2, h | ⟨h3, -⟩⟩ | ⟨-, h⟩)
      · exact h.elim
      · exact ⟨h2, h3⟩
      · exact h.elim
    · rintro ⟨h2, h3⟩
      exact Or.inl ⟨h2, Or.inr ⟨h3, by simp⟩⟩
  · have hkey : ∀ a b' : ℕ, (key a = key b') ↔ a = b' := fun a b' =>
      ⟨fun h => key_injective h, fun h => h ▸ rfl⟩
    have hdb : ∀ m : ℕ, (dbl (bstr v) = key m) ↔ v = bitsOfNat m := fun m => by
      constructor
      · intro h
        exact (dbl_bstr_parse (r := []) (r' := []) (by simpa [key_eq] using h)).1
      · rintro rfl; rfl
    have h01 : key 0 ≠ key 1 := fun h => absurd (key_injective h) (by norm_num)
    cases b
    · simp [lTag, lVal, List.cons_prefix_cons, prefix_bstr_iff, hdb]
    · simp [lTag, lVal, List.cons_prefix_cons, prefix_bstr_iff, hdb]

/-- **The root test accepts exactly the records of the root steps.** -/
theorem rootRecB_iff (d : DomDesc) (q : InstDesc) (R : List Bool) :
    rootRecB (instSer q) R = true ↔ ∃ i ∈ q.tnI.ids, R = true :: bstr (recOf d q (0, i)) := by
  have hlab : ∀ i, stepLabel d q (0, i) = q.tnI.label i := fun i => by
    simp [stepLabel, netOf]
  unfold rootRecB
  simp only [List.any_eq_true, List.mem_tails, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨s, -, ⟨⟨hid, hR⟩, hbd⟩, hl⟩
    obtain ⟨u, hu, hnv⟩ := idPos_val hid
    obtain ⟨h2, h3⟩ := (rootLbl_iff q hnv hbd).1 hl
    refine ⟨u, hu, ?_⟩
    rw [hR, h2, h3, hnv, recOf_eq_rec4_of, hlab]
    rfl
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨s, hs, hid, hnv⟩ := exists_idPos_of_mem hi
    have hbd : isBDs (kat 3 (true :: bstr (recOf d q (0, i)))) = true := by
      rw [kat3_recOf, key_eq]; exact (isBDs_iff _).2 ⟨_, rfl⟩
    refine ⟨s, hs, ⟨⟨hid, ?_⟩, hbd⟩, (rootLbl_iff q hnv hbd).2 ?_⟩
    · rw [kat2_recOf, kat3_recOf, hnv]
      exact recOf_eq_rec4_of
    · rw [kat2_recOf, kat3_recOf, hlab]
      exact ⟨rfl, rfl⟩

/-! ### The tables -/

theorem mem_mIdx {d : DomDesc} {k : ℕ} : k ∈ mIdx d ↔ 1 ≤ k ∧ k - 1 < d.methods.length := by
  simp only [mIdx, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨k - 1, h2, by omega⟩

theorem mem_mstepT {d : DomDesc} {R : List Bool} :
    R ∈ mstepT d ↔ ∃ k ∈ mIdx d, ∃ j ∈ (methodAt d k).2.ids, R = recM d (k, j) := by
  simp only [mstepT, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨k, hk, j, hj, rfl⟩; exact ⟨k, hk, j, hj, rfl⟩
  · rintro ⟨k, hk, j, hj, rfl⟩; exact ⟨k, hk, j, hj, rfl⟩

theorem mem_dummyT {d : DomDesc} {R : List Bool} :
    R ∈ dummyT d ↔ ∃ k ∈ mIdx d, (methodAt d k).2.ids = [] ∧ R = recM d (k, 0) := by
  simp only [dummyT, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨hk, he⟩, rfl⟩; exact ⟨k, hk, he, rfl⟩
  · rintro ⟨k, hk, he, rfl⟩; exact ⟨k, ⟨hk, he⟩, rfl⟩

theorem mem_headT {d : DomDesc} {k c : ℕ} :
    serNat k ++ serNat c ∈ headT d ↔ k ∈ mIdx d ∧ c = (methodAt d k).1 := by
  simp only [headT, List.mem_map]
  constructor
  · rintro ⟨k', hk', h⟩
    obtain ⟨h1, h2⟩ := serNat_parse h
    subst h1
    exact ⟨hk', (serNat_parse (r := []) (s := []) (by simpa using h2)).1.symm⟩
  · rintro ⟨hk, rfl⟩; exact ⟨k, hk, rfl⟩

theorem mem_ordT {d : DomDesc} {k a b : ℕ} :
    serNat k ++ serNat a ++ serNat b ∈ ordT d ↔ k ∈ mIdx d ∧ (methodAt d k).2.ordOf a b := by
  simp only [ordT, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_product,
    decide_eq_true_eq]
  constructor
  · rintro ⟨k', hk', ⟨a', b'⟩, ⟨-, hord⟩, h⟩
    simp only [List.append_assoc] at h
    obtain ⟨h1, h⟩ := serNat_parse h
    obtain ⟨h2, h⟩ := serNat_parse h
    obtain ⟨h3, -⟩ := serNat_parse (r := []) (s := []) (by simpa using h)
    subst h1 h2 h3
    exact ⟨hk', hord⟩
  · rintro ⟨hk, hord⟩
    exact ⟨k, hk, (a, b), ⟨by simp [hord.1, hord.2.1], hord⟩, rfl⟩

theorem mem_actT {d : DomDesc} {a : ℕ} {P : List Bool} :
    serNat a ++ P ∈ actT d ↔ a ∈ d.actions.map (·.1) ∧ P = actSer d a := by
  unfold actT
  constructor
  · intro h
    obtain ⟨a', ha', h⟩ := List.mem_map.1 h
    obtain ⟨h1, h2⟩ := serNat_parse h
    subst h1
    exact ⟨ha', h2.symm⟩
  · rintro ⟨ha, rfl⟩
    exact List.mem_map.2 ⟨a, ha, rfl⟩

theorem bstr_key2 (k c : ℕ) : bstr (serNat k ++ serNat c) = key k ++ (key c ++ [false]) := by
  rw [bstr_serNat_append, bstr_eq_dbl]; rfl

theorem bstr_key3 (k a b : ℕ) :
    bstr (serNat k ++ serNat a ++ serNat b) = key k ++ (key a ++ (key b ++ [false])) := by
  rw [List.append_assoc, bstr_serNat_append, bstr_key2]

/-! ### The link test -/

theorem recOf_mem_of_mIdx {d : DomDesc} {q : InstDesc} {x : PStep} (hx : x.1 ∈ mIdx d) :
    recOf d q x = recM d x :=
  recOf_eq_recM (by have := (mem_mIdx.1 hx).1; omega)

/-- **The link test decides `Link` between the steps of two records.** -/
theorem linkB_iff (d : DomDesc) (q : InstDesc) (x y : PStep) :
    linkB (advOf d) (true :: bstr (recOf d q x)) (true :: bstr (recOf d q y)) = true ↔
      Link d q x y := by
  rw [linkB, kat2_recOf, kat0_recOf, kat3_recOf, tH_advOf, List.append_assoc,
    ← bstr_key2]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [occB_iff, mem_headT, mem_mIdx, Link]
  constructor
  · rintro ⟨h1, ⟨hk1, hk2⟩, hc⟩
    refine ⟨hk1, hk2, ?_⟩
    have ht := key_injective h1
    rcases hl : stepLabel d q x with a | c
    · rw [hl] at ht; simp [lTag] at ht
    · rw [hl] at hc; simp only [lVal] at hc; rw [hc]
  · rintro ⟨hk1, hk2, hl⟩
    rw [hl]
    exact ⟨rfl, ⟨hk1, hk2⟩, rfl⟩

end AcVer

end Syn

end HTN
