import HtnComplexity.Space.SeqSem4
/-!
# The facts of a configuration that passes the initial test are small

`HTN.Space.SeqM.bits_le_of_seqInitB`: every numeral of a configuration of canonical numerals that
passes the initial test `seqInitB` has at most `seqBnd d q` bits — a bound linear in the length of
the code of the instance, plus the length of the root numeral of the domain.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-- The bound on the bit length of the facts of a configuration passing the initial test. -/
def seqBnd (d : DomDesc) (q : InstDesc) : ℕ :=
  2 * (instSer q).length + (bitsOfNat (cRoot d)).length + 10

/-! ### Lengths read off the code of the instance -/

section Lengths

variable {q : InstDesc}

theorem length_ids_le (q : InstDesc) : q.tnI.ids.length ≤ (instSer q).length := by
  have h1 := length_succ_le_length_blist (q.tnI.ids.map bitsOfNat)
  rw [List.length_map] at h1
  have := congrArg List.length (instSer_split q)
  simp only [List.length_append] at this
  omega

theorem card_ids_le (q : InstDesc) : q.tnI.ids.toFinset.card ≤ (instSer q).length :=
  (List.toFinset_card_le _).trans (length_ids_le q)

theorem length_serNat_le_of_mem_wnodes {a : ℕ} (ha : a ∈ wnodes q.tnI) :
    (serNat a).length ≤ (instSer q).length := by
  have hx := congrArg List.length (instSer_split q)
  simp only [List.length_append] at hx
  rw [wnodes, List.mem_append] at ha
  rcases ha with ha | ha
  · have h1 := le_length_blist_of_mem (List.mem_map_of_mem (f := bitsOfNat) ha)
    rw [serNat, length_bstr]
    omega
  · obtain ⟨e, he, hae⟩ := List.mem_flatMap.1 ha
    have h1 := le_length_blist_of_mem (List.mem_map_of_mem (f := serPair) he)
    have h2 : (serNat a).length ≤ (serPair e).length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hae
      rcases hae with rfl | rfl <;> simp [serPair]
    omega

end Lengths

/-! ### The bound -/

section Bound

variable {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row} {S : List (List Bool)}

theorem pBnd_sound (hS : ∀ w ∈ S, IsCanon w) (h : pBnd (blist S) = true) {p a k : ℕ}
    (h1 : cfG (.wit p a) ∈ decSt S) (h2 : cfG (.len k) ∈ decSt S) : p ≤ k := by
  have h3 := (allE_S hS _ _ _ _).1 h _ h1
  rw [pBndBody1, decide_eq_true (kp_entG_wit p a)] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  have h4 := (allE_S hS _ _ _ _).1 h3 _ h2
  have hk : kp tLen <+: entN (cfG (.len k)) := by
    unfold entN; rw [entG_len]; exact List.prefix_append _ _
  rw [pBndBody2, decide_eq_true hk] at h4
  simp only [Bool.not_true, Bool.false_or] at h4
  exact (lePos_iff (drop_entG_wit p a) (drop_entG_len k)).1 h4

theorem length_bitsOfNat_cfG (g : GF) : (bitsOfNat (cfG g)).length = 3 + (gbits g).length := by
  rw [bitsOfNat_cfG]; simp [gT]; omega

/-- **The facts of a configuration passing the initial test have at most `seqBnd d q` bits.** -/
theorem bits_le_of_seqInitB (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (h : seqInitB (blist S) (instSer q) (tblAdv b (markRows d K ++ T)) = true) :
    ∀ f ∈ decSt S, (bitsOfNat f).length ≤ seqBnd d q := by
  have hI := initOk_of_seqInitB hS hK h
  simp only [seqInitB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hLen⟩, hB⟩ := h
  have hall : AllOk d K q b T S := (allE_S hS _ _ _ _).1 hA
  obtain ⟨k0, hk0⟩ := pLen_sound hS hLen
  have hk0c : k0 ≤ (instSer q).length := by
    obtain ⟨h1, h2⟩ := (hI.len k0).1 hk0
    have := WitOk_len_eq hI.wit (k := k0) (fun i hi hw => h1 i hi (mem_witList.1 hw))
      (h2.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, mem_witList.2 hw⟩)
    rw [this]; exact card_ids_le q
  have hpos : ∀ p a, cfG (.wit p a) ∈ decSt S → p ≤ (instSer q).length := fun p a hw =>
    (pBnd_sound hS hB hw hk0).trans hk0c
  have hx2 := two_le_length_instSer q
  intro f hf
  unfold seqBnd
  rcases classify hS hK hall hf with ⟨v, hv, rfl⟩ | rfl | rfl | ⟨p, a, ha, rfl⟩ |
      ⟨p, i, hi, hw, rfl⟩ | ⟨p, a0, hl, -, rfl⟩ | ⟨k, -, -, rfl⟩
  · have := length_bitsOfNat_add_two_le_of_mem_initList hv
    rw [bitsOfNat_cfI]; simp [tagI3]; omega
  · omega
  · rw [length_bitsOfNat_cfG]; simp [gbits, unary]
  · have h1 := hpos p a hf
    have h2 := length_serNat_le_of_mem_wnodes ha
    rw [length_bitsOfNat_cfG]; simp [gbits, unary]; omega
  · have h1 := hpos p i hw
    have h2 := length_lblBits_label_le (q := q) i
    rw [length_bitsOfNat_cfG]; simp [gbits, unary]; omega
  · obtain ⟨i, -, hw, -⟩ := (hI.lab _ _).1 hl
    have h1 := hpos p i hw
    rw [length_bitsOfNat_cfG]; simp [gbits, unary]; omega
  · obtain ⟨h1, h2⟩ := (hI.len k).1 hf
    have := WitOk_len_eq hI.wit (k := k) (fun i hi hw => h1 i hi (mem_witList.1 hw))
      (h2.imp id fun ⟨i, hi, hw⟩ => ⟨i, hi, mem_witList.2 hw⟩)
    have := card_ids_le q
    rw [length_bitsOfNat_cfG]; simp [gbits, unary]; omega

end Bound

end SeqM

end Space

end HTN
