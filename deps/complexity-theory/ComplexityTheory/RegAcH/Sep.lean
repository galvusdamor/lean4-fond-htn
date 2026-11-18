import Mathlib

/-!
# A small modulus separating finitely many numbers

For the advice of the conditional refutation of (`HTN-REGM`, `HTN-AC`) (`PROOFIDEAS.md`, 8e)
the names of a compiled domain are written as residues modulo a small number `t` that separates
them from all names of the instances of one block.

* `HTN.RegAcH.centralBinom_dvd_lcmUpTo` — `C(2n, n)` divides `lcm(1, …, 2n)` (every prime power
  in `C(2n, n)` is at most `2n`);
* `HTN.RegAcH.exists_not_dvd_of_prod_lt` — if the product of finitely many positive numbers is
  below `2 ^ B`, some `t ≤ 2B + 6` divides none of them;
* `HTN.RegAcH.exists_sep` — for lists `X`, `Y` of numbers below `2 ^ b` there is `t ≤
  2 b |X| |Y| + 6` such that `x ≡ y (mod t)` implies `x = y` for `x ∈ X`, `y ∈ Y`.
-/

namespace HTN

namespace RegAcH

/-- `lcm(1, …, n)`. -/
def lcmUpTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

theorem dvd_lcmUpTo {t n : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ n) : t ∣ lcmUpTo n :=
  Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) (Finset.mem_Icc.2 ⟨h1, h2⟩)

theorem lcmUpTo_ne_zero (n : ℕ) : lcmUpTo n ≠ 0 := by
  unfold lcmUpTo
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

/-- **`C(2n, n)` divides `lcm(1, …, 2n)`.** -/
theorem centralBinom_dvd_lcmUpTo (n : ℕ) : n.centralBinom ∣ lcmUpTo (2 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hC : n.centralBinom ≠ 0 := (Nat.centralBinom_pos n).ne'
  rw [← Nat.factorization_le_iff_dvd hC (lcmUpTo_ne_zero _)]
  intro p
  by_cases hp : p.Prime
  · set e := n.centralBinom.factorization p
    have he : e ≤ Nat.log p (2 * n) := by
      simp only [e, Nat.centralBinom_eq_two_mul_choose]
      exact Nat.factorization_choose_le_log
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    have hpe : p ^ e ≤ 2 * n :=
      (Nat.pow_le_pow_right hp.pos he).trans (Nat.pow_log_le_self p (by omega))
    have hdvd : p ^ e ∣ lcmUpTo (2 * n) :=
      dvd_lcmUpTo (Nat.one_le_pow _ _ hp.pos) hpe
    have := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) (lcmUpTo_ne_zero _)).2
      hdvd p
    rwa [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- `lcm(1, …, 2n) ≥ 4 ^ n / (2n + 1)`. -/
theorem four_pow_le_lcmUpTo (n : ℕ) : 4 ^ n ≤ (2 * n + 1) * lcmUpTo (2 * n) :=
  (Nat.four_pow_le_two_mul_add_one_mul_central_binom n).trans
    (Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero (lcmUpTo_ne_zero _))
      (centralBinom_dvd_lcmUpTo n)))

theorem two_pow_lt_lcmUpTo (B : ℕ) : 2 ^ B < lcmUpTo (2 * B + 6) := by
  have h := four_pow_le_lcmUpTo (B + 3)
  rw [show 2 * (B + 3) = 2 * B + 6 by ring] at h
  have h1 : 4 ^ (B + 3) = 2 ^ B * 2 ^ (B + 6) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; ring_nf
  have h2 : 2 * B + 7 < 2 ^ (B + 6) := by
    have : B + 6 < 2 ^ (B + 6) := Nat.lt_two_pow_self
    have h64 : 64 ≤ 2 ^ (B + 6) := by
      rw [pow_add]; have := Nat.one_le_two_pow (n := B); nlinarith
    rw [pow_add] at h64 ⊢
    nlinarith [Nat.lt_two_pow_self (n := B)]
  by_contra hcon
  push_neg at hcon
  have h3 : (2 * B + 6 + 1) * lcmUpTo (2 * B + 6) ≤ (2 * B + 7) * 2 ^ B :=
    Nat.mul_le_mul (by omega) hcon
  have h4 : (2 * B + 7) * 2 ^ B < 2 ^ B * 2 ^ (B + 6) := by
    rw [mul_comm]; exact Nat.mul_lt_mul_of_pos_left h2 (Nat.one_le_two_pow)
  omega

/-- If every number of `[1, n]` divides `P ≠ 0`, then `lcm(1, …, n) ≤ P`. -/
theorem exists_not_dvd {P n : ℕ} (hP : 0 < P) (h : P < lcmUpTo n) :
    ∃ t, 1 ≤ t ∧ t ≤ n ∧ ¬ t ∣ P := by
  by_contra hcon
  push_neg at hcon
  have : lcmUpTo n ∣ P := Finset.lcm_dvd fun t ht => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
    exact hcon t h1 h2
  exact absurd (Nat.le_of_dvd hP this) (by omega)

/-- **A small number dividing none of finitely many positive numbers.** -/
theorem exists_not_dvd_of_prod_lt {Ds : List ℕ} (hD : ∀ D ∈ Ds, 0 < D) {B : ℕ}
    (hB : Ds.prod < 2 ^ B) : ∃ t, 1 ≤ t ∧ t ≤ 2 * B + 6 ∧ ∀ D ∈ Ds, ¬ t ∣ D := by
  have hP : 0 < Ds.prod := List.prod_pos hD
  obtain ⟨t, h1, h2, h3⟩ := exists_not_dvd hP (hB.trans (two_pow_lt_lcmUpTo B))
  exact ⟨t, h1, h2, fun D hD' hdvd => h3 (hdvd.trans (List.dvd_prod hD'))⟩

theorem prod_lt_of_forall_lt {Ds : List ℕ} {b : ℕ} (h : ∀ D ∈ Ds, D < 2 ^ b) :
    Ds.prod < 2 ^ (b * Ds.length + 1) := by
  have : Ds.prod ≤ (2 ^ b) ^ Ds.length := by
    induction Ds with
    | nil => simp
    | cons D Ds ih =>
      simp only [List.prod_cons, List.length_cons, pow_succ]
      rw [mul_comm ((2 ^ b) ^ Ds.length)]
      exact Nat.mul_le_mul (h D (by simp)).le (ih fun E hE => h E (by simp [hE]))
  rw [← pow_mul] at this
  exact this.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- The positive differences of two lists. -/
def diffs (X Y : List ℕ) : List ℕ :=
  (X.flatMap fun x => Y.map fun y => if x < y then y - x else x - y).filter (0 < ·)

theorem length_diffs_le (X Y : List ℕ) : (diffs X Y).length ≤ X.length * Y.length := by
  unfold diffs
  refine (List.length_filter_le _ _).trans (le_of_eq ?_)
  simp [List.length_flatMap, List.sum_replicate, List.map_const']

/-- **A modulus separating two lists of names.** -/
theorem exists_sep (X Y : List ℕ) {b : ℕ} (hX : ∀ x ∈ X, x < 2 ^ b) (hY : ∀ y ∈ Y, y < 2 ^ b) :
    ∃ t, 1 ≤ t ∧ t ≤ 2 * (b * (X.length * Y.length) + 1) + 6 ∧
      ∀ x ∈ X, ∀ y ∈ Y, x % t = y % t → x = y := by
  have hlt : ∀ D ∈ diffs X Y, D < 2 ^ b := by
    intro D hD
    simp only [diffs, List.mem_filter, List.mem_flatMap, List.mem_map] at hD
    obtain ⟨⟨x, hx, y, hy, rfl⟩, -⟩ := hD
    have := hX x hx; have := hY y hy
    split_ifs <;> omega
  have hpos : ∀ D ∈ diffs X Y, 0 < D := fun D hD => by
    simp only [diffs, List.mem_filter] at hD; simpa using hD.2
  have hprod := prod_lt_of_forall_lt hlt
  have hB : (diffs X Y).prod < 2 ^ (b * (X.length * Y.length) + 1) :=
    hprod.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by have := Nat.mul_le_mul_left b (length_diffs_le X Y); omega))
  obtain ⟨t, h1, h2, h3⟩ := exists_not_dvd_of_prod_lt hpos hB
  refine ⟨t, h1, h2, fun x hx y hy hxy => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt' | hgt
  · have hmem : y - x ∈ diffs X Y := by
      simp only [diffs, List.mem_filter, List.mem_flatMap, List.mem_map]
      exact ⟨⟨x, hx, y, hy, by simp [hlt']⟩, by simp; omega⟩
    exact h3 _ hmem ((Nat.modEq_iff_dvd' hlt'.le).1 hxy)
  · have hmem : x - y ∈ diffs X Y := by
      simp only [diffs, List.mem_filter, List.mem_flatMap, List.mem_map]
      exact ⟨⟨x, hx, y, hy, by simp [show ¬ x < y by omega]⟩, by simp; omega⟩
    exact h3 _ hmem ((Nat.modEq_iff_dvd' hgt.le).1 hxy.symm)

end RegAcH

end HTN
