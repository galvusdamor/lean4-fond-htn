import Mathlib

/-!
# Arrays of digits stored in one number

An array `A : ℕ → ℕ` of digits `< K` with support below `B` is stored as
`val K A B = Σ_{i < B} A i · K^i`.

* `HTN.TRSim.val_mono` — the value does not depend on the bound once it covers the support;
* `HTN.TRSim.digit_val` — `val K A B / K^i % K = A i` for every `i`;
* `HTN.TRSim.val_update` — writing a digit adds `(c' − A i)·K^i`.
-/

namespace HTN

namespace TRSim

open Finset

/-- The number of an array of digits. -/
def val (K : ℕ) (A : ℕ → ℕ) (B : ℕ) : ℕ := ∑ i ∈ range B, A i * K ^ i

theorem val_succ (K : ℕ) (A : ℕ → ℕ) (B : ℕ) : val K A (B + 1) = val K A B + A B * K ^ B := by
  simp [val, sum_range_succ]

theorem val_mono {K : ℕ} {A : ℕ → ℕ} {B : ℕ} (hA : ∀ i ≥ B, A i = 0) :
    ∀ B', B ≤ B' → val K A B' = val K A B
  | B', h => by
    induction B' with
    | zero => rw [Nat.le_zero.1 h]
    | succ B' ih =>
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [h']
      · rw [val_succ, ih (by omega), hA B' (by omega), zero_mul, add_zero]

theorem val_lt {K : ℕ} {A : ℕ → ℕ} (hA : ∀ i, A i < K) : ∀ B, val K A B < K ^ B
  | 0 => by simp [val]
  | B + 1 => by
    rw [val_succ, pow_succ]
    have h1 := val_lt hA B
    have h2 : A B ≤ K - 1 := by have := hA B; omega
    have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) (hA 0)
    calc val K A B + A B * K ^ B < K ^ B + A B * K ^ B := by omega
      _ ≤ K ^ B + (K - 1) * K ^ B := by have := Nat.mul_le_mul_right (K ^ B) h2; omega
      _ = K ^ B * K := by
        rw [Nat.sub_mul, one_mul, mul_comm (K ^ B) K]
        have : K ^ B ≤ K * K ^ B := Nat.le_mul_of_pos_left _ hK
        omega

/-- The upper part of an array, shifted down by `i + 1`. -/
def shiftA (A : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := fun j => A (i + 1 + j)

theorem val_split (K : ℕ) (A : ℕ → ℕ) {i : ℕ} :
    ∀ B, i < B → val K A B = val K A i + A i * K ^ i + K ^ (i + 1) * val K (shiftA A i) (B - i - 1)
  | 0, h => absurd h (by omega)
  | B + 1, h => by
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.1 h) with rfl | h'
    · rw [val_succ]; simp [val]
    · rw [val_succ, val_split K A B h', show B + 1 - i - 1 = (B - i - 1) + 1 by omega, val_succ]
      simp only [shiftA, show i + 1 + (B - i - 1) = B by omega]
      rw [show K ^ B = K ^ (i + 1) * K ^ (B - i - 1) by rw [← pow_add]; congr 1; omega]
      ring

/-- **Reading a digit.** -/
theorem digit_val {K : ℕ} {A : ℕ → ℕ} {B : ℕ} (hA : ∀ i, A i < K) (hsupp : ∀ i ≥ B, A i = 0)
    (i : ℕ) : val K A B / K ^ i % K = A i := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) (hA 0)
  have hB : val K A B = val K A (max B (i + 1)) := (val_mono hsupp _ (le_max_left _ _)).symm
  rw [hB, val_split K A (i := i) (max B (i + 1)) (by omega)]
  have hlow := val_lt hA i
  have hKi : 0 < K ^ i := pow_pos hK i
  rw [show val K A i + A i * K ^ i + K ^ (i + 1) * val K (shiftA A i) (max B (i + 1) - i - 1) =
      val K A i + K ^ i * (A i + K * val K (shiftA A i) (max B (i + 1) - i - 1)) by ring]
  rw [Nat.add_mul_div_left _ _ hKi, Nat.div_eq_of_lt hlow, zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hA i)]

/-- **Writing a digit.** -/
theorem val_update {K : ℕ} (A : ℕ → ℕ) {B i : ℕ} (hi : i < B) (c : ℕ) :
    val K (Function.update A i c) B + A i * K ^ i = val K A B + c * K ^ i := by
  rw [val_split K A B hi, val_split K (Function.update A i c) B hi]
  have h1 : val K (Function.update A i c) i = val K A i := by
    simp only [val]
    refine sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (by simp at hj; omega)]
  have h2 : shiftA (Function.update A i c) i = shiftA A i := by
    funext j
    simp only [shiftA]
    rw [Function.update_of_ne (by omega)]
  rw [h1, h2, Function.update_self]
  ring

theorem update_lt {K : ℕ} {A : ℕ → ℕ} (hA : ∀ i, A i < K) {i c : ℕ} (hc : c < K) :
    ∀ j, Function.update A i c j < K := by
  intro j
  rw [Function.update_apply]
  split_ifs
  · exact hc
  · exact hA j

end TRSim

end HTN
