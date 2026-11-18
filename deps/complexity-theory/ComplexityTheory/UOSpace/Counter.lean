import Mathlib

/-!
# Binary counters, bit by bit

The polynomial-space simulation of an unordered HTN problem keeps, for every task label, the
number of open tasks with that label in a binary counter of `W` bits, each bit `i` being
represented by one of two facts ("bit `i` is one", "bit `i` is zero").  Incrementing a counter
flips its trailing ones and its lowest zero bit; decrementing flips its trailing zeros and its
lowest one bit.  This file proves the arithmetic behind that:

* `HTN.Counter.exists_low_zero`, `HTN.Counter.testBit_succ_of_low_zero` — the increment;
* `HTN.Counter.exists_low_one`, `HTN.Counter.testBit_pred_of_low_one` — the decrement;
* `HTN.Counter.eq_of_testBit_lt` — numbers below `2^W` are determined by their first `W` bits.
-/

namespace HTN

namespace Counter

theorem testBit_two_mul_add_one_zero (m : ℕ) : (2 * m + 1).testBit 0 = true := by
  simp [Nat.testBit_zero]

theorem testBit_two_mul_zero (m : ℕ) : (2 * m).testBit 0 = false := by
  simp [Nat.testBit_zero]

theorem testBit_two_mul_add_one_succ (m j : ℕ) : (2 * m + 1).testBit (j + 1) = m.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  omega

theorem testBit_two_mul_succ (m j : ℕ) : (2 * m).testBit (j + 1) = m.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  omega

/-- The value of an incremented counter, bit by bit. -/
theorem testBit_succ_of_low_zero : ∀ (i n : ℕ), (∀ j < i, n.testBit j = true) →
    n.testBit i = false →
    ∀ j, (n + 1).testBit j = if j < i then false else if j = i then true else n.testBit j := by
  intro i
  induction i with
  | zero =>
    intro n _ h0 j
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · cases j with
      | zero => simp [testBit_two_mul_add_one_zero]
      | succ j =>
        rw [testBit_two_mul_add_one_succ, testBit_two_mul_succ]
        simp
    · rw [testBit_two_mul_add_one_zero] at h0
      cases h0
  | succ i ih =>
    intro n hlow hi j
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have := hlow 0 (by omega)
      rw [testBit_two_mul_zero] at this
      cases this
    · have hlow' : ∀ j < i, m.testBit j = true := fun j hj => by
        have := hlow (j + 1) (by omega)
        rwa [testBit_two_mul_add_one_succ] at this
      have hi' : m.testBit i = false := by rwa [testBit_two_mul_add_one_succ] at hi
      have e : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
      rw [e]
      cases j with
      | zero => simp [testBit_two_mul_zero]
      | succ j =>
        rw [testBit_two_mul_succ, ih m hlow' hi' j, testBit_two_mul_add_one_succ]
        by_cases h1 : j < i
        · simp [h1]
        · by_cases h2 : j = i
          · simp [h2]
          · have : ¬ j + 1 < i + 1 := by omega
            have : j + 1 ≠ i + 1 := by omega
            simp [h1, h2, *]

/-- The value of a decremented counter, bit by bit. -/
theorem testBit_pred_of_low_one : ∀ (i n : ℕ), (∀ j < i, n.testBit j = false) →
    n.testBit i = true →
    ∀ j, (n - 1).testBit j = if j < i then true else if j = i then false else n.testBit j := by
  intro i n hlow hi j
  -- `n - 1` has trailing ones below `i` and a zero at `i`
  have hpos : n ≠ 0 := by rintro rfl; simp at hi
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- the bits of `k` below `i` are ones and bit `i` is zero, by the increment lemma read backwards
  have key : (∀ j < i, k.testBit j = true) ∧ k.testBit i = false := by
    by_contra hno
    -- otherwise let `i'` be the lowest zero bit of `k`; then `k+1` has a one at `i' ≠ i`
    have hex : ∃ i', k.testBit i' = false := by
      refine ⟨k, Nat.testBit_eq_false_of_lt ?_⟩
      exact Nat.lt_two_pow_self
    classical
    let i' := Nat.find hex
    have hi'f : k.testBit i' = false := Nat.find_spec hex
    have hi'low : ∀ j < i', k.testBit j = true := fun j hj => by
      have := Nat.find_min hex hj
      simpa using this
    have hsucc := testBit_succ_of_low_zero i' k hi'low hi'f
    rcases lt_trichotomy i' i with h | h | h
    · have := hlow i' h
      rw [hsucc i'] at this
      simp at this
    · apply hno
      exact ⟨h ▸ hi'low, h ▸ hi'f⟩
    · have := hsucc i
      rw [hi] at this
      simp [h, Nat.ne_of_lt h] at this
  have := testBit_succ_of_low_zero i k key.1 key.2
  by_cases h1 : j < i
  · simp [h1, key.1 j h1]
  · by_cases h2 : j = i
    · simp [h2, key.2]
    · rw [this j]
      simp [h1, h2]

/-- A number whose first `W` bits are ones is at least `2^W - 1`. -/
theorem pow_sub_one_le_of_testBit : ∀ (W n : ℕ), (∀ j < W, n.testBit j = true) → 2 ^ W - 1 ≤ n
  | 0, _, _ => by simp
  | W + 1, n, hb => by
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have := hb 0 (by omega)
      rw [testBit_two_mul_zero] at this
      cases this
    · have hm : ∀ j < W, m.testBit j = true := fun j hj => by
        have := hb (j + 1) (by omega)
        rwa [testBit_two_mul_add_one_succ] at this
      have := pow_sub_one_le_of_testBit W m hm
      rw [pow_succ]
      omega

/-- A counter below `2^W - 1` has a zero bit below `W`; take the lowest. -/
theorem exists_low_zero {n W : ℕ} (h : n + 1 < 2 ^ W) :
    ∃ i < W, (∀ j < i, n.testBit j = true) ∧ n.testBit i = false := by
  classical
  have hex : ∃ i, n.testBit i = false :=
    ⟨n, Nat.testBit_eq_false_of_lt Nat.lt_two_pow_self⟩
  refine ⟨Nat.find hex, ?_, fun j hj => by simpa using Nat.find_min hex hj, Nat.find_spec hex⟩
  by_contra hW
  push_neg at hW
  have hall : ∀ j < W, n.testBit j = true := fun j hj => by
    simpa using Nat.find_min hex (lt_of_lt_of_le hj hW)
  have := pow_sub_one_le_of_testBit W n hall
  omega

/-- A positive counter below `2^W` has a one bit below `W`; take the lowest. -/
theorem exists_low_one {n W : ℕ} (hpos : 0 < n) (h : n < 2 ^ W) :
    ∃ i < W, (∀ j < i, n.testBit j = false) ∧ n.testBit i = true := by
  classical
  have hex : ∃ i, n.testBit i = true := by
    by_contra hno
    push_neg at hno
    have : n = 0 := Nat.eq_of_testBit_eq fun i => by simpa using hno i
    omega
  refine ⟨Nat.find hex, ?_, fun j hj => by simpa using Nat.find_min hex hj, Nat.find_spec hex⟩
  by_contra hW
  push_neg at hW
  have := Nat.find_spec hex
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hW))]
    at this
  cases this

/-- Numbers below `2^W` are determined by their first `W` bits. -/
theorem eq_of_testBit_lt {n m W : ℕ} (hn : n < 2 ^ W) (hm : m < 2 ^ W)
    (h : ∀ i < W, n.testBit i = m.testBit i) : n = m := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < W
  · exact h i hi
  · push_neg at hi
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hi))]

/-- The bits of a number below `2^W` vanish from `W` on. -/
theorem testBit_eq_false_of_lt_pow {n W i : ℕ} (hn : n < 2 ^ W) (hi : W ≤ i) :
    n.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hi))

end Counter

end HTN
