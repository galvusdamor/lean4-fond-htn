import Mathlib

/-!
# Linear equations over binary digits, column by column

For vectors `v j : ι → ℤ` (`j : J`), an offset `c : ι → ℤ` and a vector of naturals `n`, the
equation

    n = c + Σ_j k_j · v_j      (k : J → ℕ)

is checked by a machine that reads `n` in binary, least significant digit first, one *column*
(digit `i` of every coordinate) at a time.  It keeps one integer carry per coordinate, guesses
digit `i` of every `k_j` and updates

    2 · γ_{i+1} = γ_i + Σ_j κ_{i,j} · v_j − ν_i      (ν_i = digit i of n).

* `HTN.UOStream.colRun_sound` — an accepting run (carries start at `c`, end at `0`) gives a
  solution `k`.
* `HTN.UOStream.colRun_complete` — a solution gives an accepting run whose carries stay below
  `|c| + Σ_j |v_j| + 1` in every coordinate, **whatever the size of `n` and `k`**: the numbers
  themselves are never stored, only their digits are read or guessed.
-/

namespace HTN

namespace UOStream

open Finset

variable {ι J : Type} [Fintype J]

/-- Digit `i` of `n` in binary. -/
def bitN (n i : ℕ) : ℕ := n / 2 ^ i % 2

theorem bitN_le_one (n i : ℕ) : bitN n i ≤ 1 := by
  unfold bitN; omega

/-- One column step. -/
def ColStep (v : J → ι → ℤ) (γ γ' : ι → ℤ) (ν : ι → ℕ) (κ : J → ℕ) : Prop :=
  ∀ x, 2 * γ' x = γ x + ∑ j, (κ j : ℤ) * v j x - ν x

/-- An accepting run over `L` columns. -/
def ColRun (v : J → ι → ℤ) (c : ι → ℤ) (n : ι → ℕ) (L : ℕ) (κs : ℕ → J → ℕ)
    (γs : ℕ → ι → ℤ) : Prop :=
  γs 0 = c ∧ γs L = 0 ∧
    ∀ i < L, (∀ j, κs i j ≤ 1) ∧ ColStep v (γs i) (γs (i + 1)) (fun x => bitN (n x) i) (κs i)

/-- The number whose digits are `κs i j`, `i < L`. -/
def numOf (κs : ℕ → J → ℕ) (L : ℕ) (j : J) : ℕ := ∑ i ∈ range L, κs i j * 2 ^ i

theorem mod_two_pow_succ (n i : ℕ) : n % 2 ^ (i + 1) = n % 2 ^ i + 2 ^ i * bitN n i :=
  Nat.mod_pow_succ

/-- **Soundness**: an accepting run solves the equation. -/
theorem colRun_sound {v : J → ι → ℤ} {c : ι → ℤ} {n : ι → ℕ} {L : ℕ} {κs : ℕ → J → ℕ}
    {γs : ℕ → ι → ℤ} (h : ColRun v c n L κs γs) (hn : ∀ x, n x < 2 ^ L) :
    ∀ x, (n x : ℤ) = c x + ∑ j, (numOf κs L j : ℤ) * v j x := by
  obtain ⟨h0, hL, hstep⟩ := h
  have inv : ∀ i ≤ L, ∀ x, (2 : ℤ) ^ i * γs i x =
      c x + ∑ j, (numOf κs i j : ℤ) * v j x - ((n x % 2 ^ i : ℕ) : ℤ) := by
    intro i
    induction i with
    | zero =>
      intro _ x
      simp [h0, numOf]
    | succ i ih =>
      intro hi x
      have h1 := ih (by omega) x
      have h2 := (hstep i (by omega)).2 x
      have hnum : ∀ j, (numOf κs (i + 1) j : ℤ) = numOf κs i j + κs i j * 2 ^ i := by
        intro j; simp [numOf, sum_range_succ]
      have hmod : ((n x % 2 ^ (i + 1) : ℕ) : ℤ) = ((n x % 2 ^ i : ℕ) : ℤ) + 2 ^ i * bitN (n x) i := by
        rw [mod_two_pow_succ]; push_cast; ring
      simp only [hnum, hmod, add_mul, sum_add_distrib]
      have e : (2 : ℤ) ^ (i + 1) * γs (i + 1) x = 2 ^ i * (2 * γs (i + 1) x) := by ring
      rw [e, h2, mul_sub, mul_add, h1]
      have : (2 : ℤ) ^ i * ∑ j, (κs i j : ℤ) * v j x = ∑ j, (κs i j : ℤ) * 2 ^ i * v j x := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      rw [this]
      ring
  intro x
  have := inv L le_rfl x
  rw [hL, Nat.mod_eq_of_lt (hn x)] at this
  simp only [Pi.zero_apply, mul_zero] at this
  linarith

/-- **Completeness**: a solution gives an accepting run with small carries. -/
theorem colRun_complete {v : J → ι → ℤ} {c : ι → ℤ} {n : ι → ℕ} {k : J → ℕ}
    (hk : ∀ x, (n x : ℤ) = c x + ∑ j, (k j : ℤ) * v j x) {L : ℕ} (hn : ∀ x, n x < 2 ^ L)
    (hkL : ∀ j, k j < 2 ^ L) :
    ∃ κs γs, ColRun v c n L κs γs ∧
      ∀ i, ∀ x, |γs i x| ≤ |c x| + ∑ j, |v j x| + 1 := by
  refine ⟨fun i j => bitN (k j) i,
    fun i x => ((n x / 2 ^ i : ℕ) : ℤ) - ∑ j, ((k j / 2 ^ i : ℕ) : ℤ) * v j x, ⟨?_, ?_, ?_⟩, ?_⟩
  · funext x
    simp only [pow_zero, Nat.div_one]
    have := hk x
    linarith
  · funext x
    simp [Nat.div_eq_of_lt (hn x), Nat.div_eq_of_lt (hkL _)]
  · intro i _
    refine ⟨fun j => bitN_le_one _ _, fun x => ?_⟩
    have hdiv : ∀ m : ℕ, ((m / 2 ^ i : ℕ) : ℤ) = 2 * ((m / 2 ^ (i + 1) : ℕ) : ℤ) + bitN m i := by
      intro m
      have : m / 2 ^ i = 2 * (m / 2 ^ (i + 1)) + m / 2 ^ i % 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega
      unfold bitN; exact_mod_cast this
    simp only [hdiv, add_mul, sum_add_distrib, mul_sub, mul_sum]
    have : ∀ j, (2 : ℤ) * (((k j / 2 ^ (i + 1) : ℕ) : ℤ) * v j x) =
        2 * ((k j / 2 ^ (i + 1) : ℕ) : ℤ) * v j x := fun j => by ring
    simp only [this]
    ring
  · intro i x
    -- `2^i γ_i = c − (n mod 2^i) + Σ (k_j mod 2^i) v_j`
    have hid : (2 : ℤ) ^ i * (((n x / 2 ^ i : ℕ) : ℤ) - ∑ j, ((k j / 2 ^ i : ℕ) : ℤ) * v j x) =
        c x - ((n x % 2 ^ i : ℕ) : ℤ) + ∑ j, ((k j % 2 ^ i : ℕ) : ℤ) * v j x := by
      have hn' : (n x : ℤ) = 2 ^ i * ((n x / 2 ^ i : ℕ) : ℤ) + ((n x % 2 ^ i : ℕ) : ℤ) := by
        have := Nat.div_add_mod (n x) (2 ^ i); exact_mod_cast this.symm
      have hk' : ∀ j, (k j : ℤ) = 2 ^ i * ((k j / 2 ^ i : ℕ) : ℤ) + ((k j % 2 ^ i : ℕ) : ℤ) := by
        intro j; have := Nat.div_add_mod (k j) (2 ^ i); exact_mod_cast this.symm
      have e := hk x
      rw [hn'] at e
      simp only [hk', add_mul, sum_add_distrib] at e
      rw [mul_sub, mul_sum]
      have : ∀ j, (2 : ℤ) ^ i * (((k j / 2 ^ i : ℕ) : ℤ) * v j x) =
          2 ^ i * ((k j / 2 ^ i : ℕ) : ℤ) * v j x := fun j => by ring
      simp only [this]
      linarith
    set γ := ((n x / 2 ^ i : ℕ) : ℤ) - ∑ j, ((k j / 2 ^ i : ℕ) : ℤ) * v j x
    have hp : (0 : ℤ) < 2 ^ i := by positivity
    have hmodn : ((n x % 2 ^ i : ℕ) : ℤ) < 2 ^ i := by
      have := Nat.mod_lt (n x) (Nat.two_pow_pos i); exact_mod_cast this
    have hmodk : ∀ j, |((k j % 2 ^ i : ℕ) : ℤ) * v j x| ≤ 2 ^ i * |v j x| := by
      intro j
      rw [abs_mul]
      have h1 : |((k j % 2 ^ i : ℕ) : ℤ)| ≤ 2 ^ i := by
        rw [abs_of_nonneg (by positivity)]
        have := Nat.mod_lt (k j) (Nat.two_pow_pos i); exact_mod_cast this.le
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have hsum : |∑ j, ((k j % 2 ^ i : ℕ) : ℤ) * v j x| ≤ 2 ^ i * ∑ j, |v j x| := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]; exact sum_le_sum fun j _ => hmodk j
    have hc : |c x| ≤ 2 ^ i * |c x| := le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ (by norm_num))
    have hmn : |((n x % 2 ^ i : ℕ) : ℤ)| ≤ 2 ^ i := by
      rw [abs_of_nonneg (by positivity)]; exact hmodn.le
    have htot : |(2 : ℤ) ^ i * γ| ≤ 2 ^ i * (|c x| + ∑ j, |v j x| + 1) := by
      rw [hid]
      calc |c x - ((n x % 2 ^ i : ℕ) : ℤ) + ∑ j, ((k j % 2 ^ i : ℕ) : ℤ) * v j x|
          ≤ |c x| + |((n x % 2 ^ i : ℕ) : ℤ)| + |∑ j, ((k j % 2 ^ i : ℕ) : ℤ) * v j x| := by
            have e1 := abs_add_le (c x - ((n x % 2 ^ i : ℕ) : ℤ))
              (∑ j, ((k j % 2 ^ i : ℕ) : ℤ) * v j x)
            have e2 : |c x - ((n x % 2 ^ i : ℕ) : ℤ)| ≤ |c x| + |((n x % 2 ^ i : ℕ) : ℤ)| :=
              abs_sub _ _
            linarith
        _ ≤ 2 ^ i * |c x| + 2 ^ i + 2 ^ i * ∑ j, |v j x| := by linarith
        _ = 2 ^ i * (|c x| + ∑ j, |v j x| + 1) := by ring
    rw [abs_mul, abs_of_pos hp] at htot
    exact le_of_mul_le_mul_left htot hp

end UOStream

end HTN
