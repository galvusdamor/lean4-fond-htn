import HtnComplexity.TMEnc.TMEncFixPlan
/-!
# The head counter of the plan marks the right cells

The head counter of the repaired construction is a fixed chain: it runs `K` cycles of `K + 2`
units in which only the second one reports the head as present, and then a last, truncated cycle
— that is the function `HTN.TMEnc.headMark`, the units `u ≡ 1 (mod K + 2)` reporting the head.

In the plan of a witness the unit `u` answers the request of the very cell it is executed in, so
the head fact that holds while the cell `n` takes its decision is the mark of the unit
`HTN.TMEnc.headBase K hd mv n`.  This file proves that this mark is right:

`HTN.TMEnc.headMark_headBase` — the mark of that unit reports the head as present exactly when
the cell `n` is the cell of the head of the machine, i.e. when `n % (K+1) = hd (n / (K+1)) + 1`.

The computation behind it is the one that makes the whole construction work: a transition eats
up `1 - δ` units of the head counter, where `δ` is the displacement of its head movement, so the
unit index of the head cell of the block `i` is `i * (K + 2) + 1` — which is exactly where the
chain puts its marks.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {K : ℕ}

/-! ### The extras of the cells before a given one -/

/-- The extra requests of the cells before the cell `n = t (K+1) + c`: those of the transitions
of the blocks before `t`, and — if the transition of the block `t` has already been taken — the
ones of that transition. -/
lemma sum_extraCnt_lt {hd : ℕ → ℕ} {mv : ℕ → Move} (hdlt : ∀ i ≤ K, hd i < K) {t c : ℕ}
    (ht : t ≤ K) (hc : c < K + 1) :
    ∑ m ∈ Finset.range (t * (K + 1) + c), extraCnt K hd mv m =
      (∑ i ∈ Finset.range t, moveExtra (mv i)) +
        (if t < K ∧ hd t + 1 < c then moveExtra (mv t) else 0) := by
  rw [Finset.sum_range_add, sum_range_mul t (K + 1) (extraCnt K hd mv)]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := by have := Finset.mem_range.1 hi; omega
    rw [sum_extraCnt_block hdlt i, if_pos hiK]
  · by_cases hcase : t < K ∧ hd t + 1 < c
    · obtain ⟨htK, hlt⟩ := hcase
      rw [if_pos ⟨htK, hlt⟩, Finset.sum_eq_single (hd t + 1)]
      · have h := div_mod_cell (K := K) (t := t) (j := hd t + 1) (by have := hdlt t (by omega); omega)
        rw [extraCnt, if_pos ⟨by rw [h.1]; exact htK, by rw [h.2, h.1]⟩, h.1]
      · intro j hj hne
        have hjK : j < K + 1 := by have := Finset.mem_range.1 hj; omega
        have h := div_mod_cell (K := K) (t := t) (j := j) hjK
        rw [extraCnt, if_neg ?_]
        rintro ⟨-, heq⟩
        rw [h.2, h.1] at heq
        exact hne heq
      · intro hmem
        exact absurd (Finset.mem_range.2 hlt) hmem
    · rw [if_neg hcase]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjc : j < c := Finset.mem_range.1 hj
      have hjK : j < K + 1 := by omega
      have h := div_mod_cell (K := K) (t := t) (j := j) hjK
      rw [extraCnt, if_neg ?_]
      rintro ⟨hlt, heq⟩
      rw [h.1] at hlt
      rw [h.2, h.1] at heq
      exact hcase ⟨hlt, by omega⟩

/-! ### The index of the unit that sets the head fact of a cell -/

variable {hd : ℕ → ℕ} {mv : ℕ → Move}

/-- **The unit index of a cell whose transition has not been taken yet.** -/
lemma headBase_add_hd (hd0 : hd 0 = 0) (hdlt : ∀ i ≤ K, hd i < K)
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) {t c : ℕ} (ht : t ≤ K) (hc : c < K + 1)
    (hcase : ¬ (t < K ∧ hd t + 1 < c)) :
    headBase K hd mv (t * (K + 1) + c) + hd t = t * (K + 2) + c := by
  have hsum : ∑ m ∈ Finset.range (t * (K + 1) + c), extraCnt K hd mv m =
      ∑ i ∈ Finset.range t, moveExtra (mv i) := by
    rw [sum_extraCnt_lt hdlt ht hc, if_neg hcase, Nat.add_zero]
  have hExt := sum_moveExtra_add_head (K := K) hd0 hmove hbump t ht
  have hbase : headBase K hd mv (t * (K + 1) + c) =
      t * (K + 1) + c + ∑ i ∈ Finset.range t, moveExtra (mv i) := by
    unfold headBase headCnt
    rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one, Nat.add_comm]
  have hmul : t * (K + 2) = t * (K + 1) + t := by ring
  omega

/-- **The unit index of a cell whose transition has already been taken.** -/
lemma headBase_add_hd_succ (hd0 : hd 0 = 0) (hdlt : ∀ i ≤ K, hd i < K)
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) {t c : ℕ} (hc : c < K + 1)
    (htK : t < K) (hlt : hd t + 1 < c) :
    headBase K hd mv (t * (K + 1) + c) + hd (t + 1) = t * (K + 2) + c + 1 := by
  have hsum : ∑ m ∈ Finset.range (t * (K + 1) + c), extraCnt K hd mv m =
      ∑ i ∈ Finset.range (t + 1), moveExtra (mv i) := by
    rw [sum_extraCnt_lt hdlt (by omega) hc, if_pos ⟨htK, hlt⟩, Finset.sum_range_succ]
  have hExt := sum_moveExtra_add_head (K := K) hd0 hmove hbump (t + 1) (by omega)
  have hbase : headBase K hd mv (t * (K + 1) + c) =
      t * (K + 1) + c + ∑ i ∈ Finset.range (t + 1), moveExtra (mv i) := by
    unfold headBase headCnt
    rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one, Nat.add_comm]
  have hmul : t * (K + 2) = t * (K + 1) + t := by ring
  omega

/-! ### The mark of that unit -/

lemma headMark_mul_add_one {t : ℕ} : headMark K (t * (K + 2) + 1) = true := by
  have h1 : (t * (K + 2) + 1) % (K + 2) = 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  simp [headMark, h1]

lemma headMark_add {t e : ℕ} (he1 : e ≠ 1) (he2 : e < K + 2) :
    headMark K (t * (K + 2) + e) = false := by
  have h1 : (t * (K + 2) + e) % (K + 2) = e := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he2]
  simp [headMark, h1, he1]

/-- **The mark of the unit that sets the head fact of the cell `n`.**

The head is reported as present exactly at the cells that carry the head of the machine. -/
theorem headMark_headBase (hd0 : hd 0 = 0) (hdK : hd K = 0)
    (hdlt : ∀ i ≤ K, hd i < K)
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) {n : ℕ}
    (hnR : n < (K + 1) * (K + 1)) :
    headMark K (headBase K hd mv n) = decide (n % (K + 1) = hd (n / (K + 1)) + 1) := by
  obtain ⟨t, c, hc, rfl⟩ : ∃ t c, c < K + 1 ∧ n = t * (K + 1) + c :=
    ⟨n / (K + 1), n % (K + 1), Nat.mod_lt _ (by omega), (Nat.div_add_mod' n (K + 1)).symm⟩
  obtain ⟨hdiv, hmod⟩ := div_mod_cell (K := K) (t := t) hc
  rw [hdiv, hmod]
  have htK : t ≤ K := by
    by_contra hcon
    have : (K + 1) * (K + 1) ≤ t * (K + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hhdt : hd t < K := hdlt t htK
  by_cases hcase : t < K ∧ hd t + 1 < c
  · -- the transition of this block has already been taken: the mark is `false`
    obtain ⟨htlt, hgt⟩ := hcase
    have hbase := headBase_add_hd_succ hd0 hdlt hmove hbump (t := t) (c := c) hc htlt hgt
    have hle : hd (t + 1) ≤ hd t + 1 := by
      rw [hmove t htlt]; exact Move.apply_le _ _
    have hbase' : headBase K hd mv (t * (K + 1) + c) =
        t * (K + 2) + (c + 1 - hd (t + 1)) := by omega
    have hne : ¬ (c = hd t + 1) := by omega
    rw [hbase', headMark_add (by omega) (by omega)]
    simp [hne]
  · have hbase := headBase_add_hd hd0 hdlt hmove hbump (t := t) (c := c) htK hc hcase
    by_cases hhead : c = hd t + 1
    · -- the head cell of the block: the mark is `true`
      have hbase' : headBase K hd mv (t * (K + 1) + c) = t * (K + 2) + 1 := by omega
      rw [hbase', headMark_mul_add_one]
      simp [hhead]
    · rcases Nat.lt_or_ge c (hd t + 1) with hclt | hcge
      · -- at or before the head cell of the block: the mark is `false`
        rcases Nat.eq_or_lt_of_le (show c ≤ hd t by omega) with hceq | hcltt
        · have hbase' : headBase K hd mv (t * (K + 1) + c) = t * (K + 2) + 0 := by omega
          rw [hbase', headMark_add (by omega) (by omega)]
          simp [hhead]
        · have ht1 : 1 ≤ t := by
            rcases Nat.eq_zero_or_pos t with rfl | h
            · rw [hd0] at hcltt
              omega
            · exact h
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          have hmul : (t' + 1) * (K + 2) = t' * (K + 2) + (K + 2) := by ring
          have hbase' : headBase K hd mv ((t' + 1) * (K + 1) + c) =
              t' * (K + 2) + (K + 2 - (hd (t' + 1) - c)) := by omega
          rw [hbase', headMark_add (by omega) (by omega)]
          simp [hhead]
      · -- after the head cell of the last block: the mark is `false`
        have hcgt : hd t + 1 < c := by omega
        have htEq : t = K := by
          by_contra hne'
          exact hcase ⟨by omega, hcgt⟩
        have hdt0 : hd t = 0 := by rw [htEq]; exact hdK
        rw [hdt0] at hbase hcgt
        have hbase' : headBase K hd mv (t * (K + 1) + c) = t * (K + 2) + c := by
          omega
        rw [hbase', headMark_add (by omega) (by omega)]
        simp [hhead]

end TMEnc

end HTN
