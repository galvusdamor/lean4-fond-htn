import Mathlib
/-!
# Numbers given by their binary digits

`FOND.TOHard2.ofB g n` is the number with binary digits `g 0, …, g (n - 1)` (little endian).
The hardness construction of `FondHtn/TOHard2/` never stores the numbers it talks about (they
have `2 ^ b` digits): a number is a *digit function* `ℕ → Bool`, and only one digit (the
challenged one) is ever present in a state.  This file provides the arithmetic of digit
functions:

* `FOND.TOHard2.testBit_ofB`, `FOND.TOHard2.ofB_testBit` — digits and numbers correspond;
* `FOND.TOHard2.ofB_inj` — two digit functions with the same number agree below `n`;
* `FOND.TOHard2.ofB_succ_true`, `ofB_succ_false` — the step lemmas used by the automata of
  `FondHtn/TOHard2/Auto.lean`.
-/

namespace FOND

namespace TOHard2

/-- **The number with binary digits `g 0, …, g (n - 1)`.** -/
def ofB (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ofB g n + (g n).toNat * 2 ^ n

@[simp] theorem ofB_zero (g : ℕ → Bool) : ofB g 0 = 0 := rfl

theorem ofB_succ (g : ℕ → Bool) (n : ℕ) : ofB g (n + 1) = ofB g n + (g n).toNat * 2 ^ n := rfl

theorem ofB_succ_true {g : ℕ → Bool} {n : ℕ} (h : g n = true) : ofB g (n + 1) = ofB g n + 2 ^ n := by
  simp [ofB_succ, h]

theorem ofB_succ_false {g : ℕ → Bool} {n : ℕ} (h : g n = false) : ofB g (n + 1) = ofB g n := by
  simp [ofB_succ, h]

theorem ofB_lt (g : ℕ → Bool) : ∀ n, ofB g n < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    have := ofB_lt g n
    rw [ofB_succ, pow_succ]
    cases g n <;> simp <;> omega

theorem ofB_congr {g g' : ℕ → Bool} {n : ℕ} (h : ∀ r < n, g r = g' r) : ofB g n = ofB g' n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ofB_succ, ofB_succ, ih (fun r hr => h r (by omega)), h n (by omega)]

theorem testBit_ofB (g : ℕ → Bool) : ∀ n r, (ofB g n).testBit r = (decide (r < n) && g r)
  | 0, r => by simp
  | n + 1, r => by
    have hlt := ofB_lt g n
    have ih := testBit_ofB g n
    cases hg : g n
    · rw [ofB_succ_false hg, ih]
      by_cases hr : r < n
      · simp [hr, show r < n + 1 by omega]
      · by_cases hrn : r = n
        · subst hrn; simp [hg]
        · simp [hr, show ¬ r < n + 1 by omega]
    · rw [ofB_succ_true hg, add_comm]
      by_cases hr : r < n
      · rw [Nat.testBit_two_pow_add_gt hr, ih]; simp [hr, show r < n + 1 by omega]
      · by_cases hrn : r = n
        · subst hrn
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; simp [hg]
        · have h2 : 2 ^ n + ofB g n < 2 ^ r := by
            have : 2 ^ (n + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
            rw [pow_succ] at this; omega
          rw [Nat.testBit_lt_two_pow h2]; simp [show ¬ r < n + 1 by omega]

theorem testBit_ofB_of_lt (g : ℕ → Bool) {n r : ℕ} (h : r < n) : (ofB g n).testBit r = g r := by
  simp [testBit_ofB, h]

theorem ofB_testBit {x n : ℕ} (h : x < 2 ^ n) : ofB x.testBit n = x := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_ofB]
  by_cases hr : r < n
  · simp [hr]
  · simp only [hr, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem ofB_inj {g g' : ℕ → Bool} {n : ℕ} (h : ofB g n = ofB g' n) : ∀ r < n, g r = g' r := by
  intro r hr
  have := congrArg (fun x => x.testBit r) h
  simpa [testBit_ofB, hr] using this

theorem ofB_eq_iff {g : ℕ → Bool} {n x : ℕ} (hx : x < 2 ^ n) :
    ofB g n = x ↔ ∀ r < n, g r = x.testBit r := by
  constructor
  · rintro rfl r hr; rw [testBit_ofB_of_lt _ hr]
  · intro h; rw [← ofB_testBit hx]; exact ofB_congr h

/-- All digits set. -/
theorem ofB_all_true {g : ℕ → Bool} : ∀ {n : ℕ}, (∀ r < n, g r = true) → ofB g n + 1 = 2 ^ n
  | 0, _ => by simp
  | n + 1, h => by
    rw [ofB_succ_true (h n (by omega)), pow_succ]
    have := ofB_all_true (n := n) (fun r hr => h r (by omega))
    omega

theorem ofB_le_of_le_digits {g : ℕ → Bool} {n : ℕ} : ofB g n ≤ 2 ^ n - 1 := by
  have := ofB_lt g n; omega

end TOHard2

end FOND
