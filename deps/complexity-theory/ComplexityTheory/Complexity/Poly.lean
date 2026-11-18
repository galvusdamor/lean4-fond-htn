import Mathlib

/-!
# Polynomials with natural coefficients

Evaluation of a polynomial with natural number coefficients is monotone.
-/

namespace HTN

/-- Evaluation of a polynomial with natural number coefficients is monotone. -/
lemma Polynomial.eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using Nat.add_le_add hp hq
  | monomial n c =>
      simpa [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

end HTN
