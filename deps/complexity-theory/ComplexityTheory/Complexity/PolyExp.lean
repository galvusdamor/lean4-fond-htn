import Mathlib

/-!
# Polynomials are eventually smaller than `2 ^ n`

Two elementary growth facts the counting argument of
`HtnComplexity/Complexity/AdviceCount.lean` needs.

* `HTN.exists_poly_lt_two_pow` — for all `c` and `k` there is an `N` beyond which
  `c * (n + 1) ^ k < 2 ^ n`;
* `HTN.exists_pow_bound` — every polynomial over `ℕ` is dominated by `k * (n + 1) ^ k` for
  some `k`, so a single natural number may stand for the polynomial size bound of a
  compilation.
-/

namespace HTN

/-- **A polynomial is eventually smaller than `2 ^ n`.** -/
theorem exists_poly_lt_two_pow (c k : ℕ) : ∃ N, ∀ n ≥ N, c * (n + 1) ^ k < 2 ^ n := by
  have hbo : (fun n : ℕ => ((n : ℝ) + 1) ^ k) =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ k := by
    refine Asymptotics.IsBigO.of_bound (2 ^ k) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h1 : ((n:ℝ) + 1) ≤ 2 * n := by linarith
    have h2 : ((n:ℝ) + 1) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by positivity) h1 k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    calc ((n:ℝ) + 1) ^ k ≤ (2 * n) ^ k := h2
      _ = 2 ^ k * (n:ℝ) ^ k := by rw [mul_pow]
  have hlo : (fun n : ℕ => ((n : ℝ) + 1) ^ k) =o[Filter.atTop] fun n : ℕ => (2:ℝ) ^ n :=
    hbo.trans_isLittleO (isLittleO_pow_const_const_pow_of_one_lt k (by norm_num))
  have hc : (0:ℝ) < 1 / (c + 1) := by positivity
  have hev := hlo.def hc
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at h
  have hcast : (c : ℝ) * ((n:ℝ) + 1) ^ k < 2 ^ n := by
    have h2 : (c:ℝ) * ((n:ℝ)+1)^k ≤ (c:ℝ) * (1 / (c+1) * 2 ^ n) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : (c:ℝ) * (1 / (c+1) * 2 ^ n) < 2 ^ n := by
      rw [← mul_assoc]
      refine mul_lt_of_lt_one_left (by positivity) ?_
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    linarith
  have hfin : ((c * (n + 1) ^ k : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    push_cast
    exact_mod_cast hcast
  exact_mod_cast hfin

/-- **Every polynomial over `ℕ` is dominated by one of the polynomials `k * (n + 1) ^ k`.** -/
theorem exists_pow_bound (p : Polynomial ℕ) : ∃ k, ∀ n, p.eval n ≤ k * (n + 1) ^ k := by
  classical
  refine ⟨max (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) p.natDegree, fun n => ?_⟩
  set K := max (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) p.natDegree with hK
  have h1 : p.eval n = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i :=
    Polynomial.eval_eq_sum_range n
  have h2 : ∀ i ∈ Finset.range (p.natDegree + 1),
      p.coeff i * n ^ i ≤ p.coeff i * (n + 1) ^ K := by
    intro i hi
    refine Nat.mul_le_mul_left _ ?_
    calc n ^ i ≤ (n+1) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (n+1) ^ K := Nat.pow_le_pow_right (by omega)
          (le_trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (le_max_right _ _))
  calc p.eval n = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i := h1
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (n + 1) ^ K := Finset.sum_le_sum h2
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * (n + 1) ^ K := by rw [← Finset.sum_mul]
    _ ≤ K * (n + 1) ^ K := Nat.mul_le_mul_right _ (le_max_left _ _)

end HTN
