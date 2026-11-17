import Mathlib
/-!
# Bit vectors: values, increment and decrement patterns

`FOND.DB.bval n β = Σ_{i<n} β(i)·2^i`.  Incrementing flips a block of trailing ones and the
following zero (`FOND.DB.bval_incSet`, `FOND.DB.exists_inc`), decrementing a block of trailing zeros
and the following one (`FOND.DB.bval_decSet`, `FOND.DB.exists_dec`).
-/

namespace FOND

namespace DB

/-- The value of the first `n` bits of `β`. -/
def bval : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, β => bval n β + (β n).toNat * 2 ^ n

theorem bval_lt : ∀ (n : ℕ) (β : ℕ → Bool), bval n β < 2 ^ n
  | 0, _ => by simp [bval]
  | n + 1, β => by
    have := bval_lt n β
    have : (β n).toNat ≤ 1 := Bool.toNat_le _
    rw [bval, pow_succ]; nlinarith

theorem bval_congr : ∀ (n : ℕ) {β β' : ℕ → Bool}, (∀ i < n, β i = β' i) → bval n β = bval n β'
  | 0, _, _, _ => rfl
  | n + 1, β, β', h => by
    rw [bval, bval, bval_congr n fun i hi => h i (by omega), h n (by omega)]

theorem bval_inj : ∀ (n : ℕ) {β β' : ℕ → Bool}, bval n β = bval n β' → ∀ i < n, β i = β' i
  | 0, _, _, _ => fun i hi => absurd hi (by omega)
  | n + 1, β, β', h => by
    have h1 := bval_lt n β
    have h2 := bval_lt n β'
    rw [bval, bval] at h
    have hn : β n = β' n := by
      cases hb : β n <;> cases hb' : β' n <;> simp_all <;> omega
    rw [hn] at h
    have := bval_inj n (by omega : bval n β = bval n β')
    intro i hi
    rcases Nat.lt_or_ge i n with h' | h'
    · exact this i h'
    · rw [show i = n by omega]; exact hn

theorem bval_eq_iff (n : ℕ) {β β' : ℕ → Bool} : bval n β = bval n β' ↔ ∀ i < n, β i = β' i :=
  ⟨bval_inj n, bval_congr n⟩

theorem exists_bval : ∀ (n x : ℕ), x < 2 ^ n → ∃ β : ℕ → Bool, bval n β = x
  | 0, x, h => ⟨fun _ => false, by simp at h; simp [bval, h]⟩
  | n + 1, x, h => by
    by_cases hx : x < 2 ^ n
    · obtain ⟨β, hβ⟩ := exists_bval n x hx
      refine ⟨Function.update β n false, ?_⟩
      rw [bval, bval_congr n (β' := β) fun i hi => by rw [Function.update_of_ne (by omega)]]
      simp [hβ]
    · obtain ⟨β, hβ⟩ := exists_bval n (x - 2 ^ n) (by rw [pow_succ] at h; omega)
      refine ⟨Function.update β n true, ?_⟩
      rw [bval, bval_congr n (β' := β) fun i hi => by rw [Function.update_of_ne (by omega)]]
      simp [hβ]; omega

theorem bval_zero_iff : ∀ (n : ℕ) (β : ℕ → Bool), bval n β = 0 ↔ ∀ i < n, β i = false
  | 0, _ => by simp [bval]
  | n + 1, β => by
    rw [bval, Nat.add_eq_zero_iff, bval_zero_iff n β]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact h1 i h
      · rw [show i = n by omega]; cases hb : β n <;> simp_all
    · intro h; exact ⟨fun i hi => h i (by omega), by simp [h n (by omega)]⟩

theorem bval_allTrue : ∀ (n : ℕ) (β : ℕ → Bool), (∀ i < n, β i = true) → bval n β + 1 = 2 ^ n
  | 0, _, _ => by simp [bval]
  | n + 1, β, h => by
    rw [bval, h n (by omega)]
    have := bval_allTrue n β fun i hi => h i (by omega)
    simp; rw [pow_succ]; omega

/-- Increment with the carry ending at `j`. -/
def incSet (β : ℕ → Bool) (j : ℕ) : ℕ → Bool := fun i => if i < j then false else if i = j then true else β i

/-- Decrement with the borrow ending at `j`. -/
def decSet (β : ℕ → Bool) (j : ℕ) : ℕ → Bool := fun i => if i < j then true else if i = j then false else β i

theorem bval_incSet : ∀ (n : ℕ) (β : ℕ → Bool) (j : ℕ), j < n → (∀ i < j, β i = true) →
    β j = false → bval n (incSet β j) = bval n β + 1
  | 0, _, _, h, _, _ => absurd h (by omega)
  | n + 1, β, j, hj, h1, h2 => by
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [bval, bval, bval_incSet n β j hjn h1 h2]
      simp [incSet, show ¬ n < j by omega, show n ≠ j by omega]; omega
    · have hjn' : j = n := by omega
      subst hjn'
      rw [bval, bval, h2]
      have hz : bval j (incSet β j) = 0 :=
        (bval_zero_iff j _).2 fun i hi => by simp [incSet, hi]
      have := bval_allTrue j β h1
      simp [hz, incSet]; omega

theorem bval_decSet : ∀ (n : ℕ) (β : ℕ → Bool) (j : ℕ), j < n → (∀ i < j, β i = false) →
    β j = true → bval n (decSet β j) + 1 = bval n β
  | 0, _, _, h, _, _ => absurd h (by omega)
  | n + 1, β, j, hj, h1, h2 => by
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [bval, bval, ← bval_decSet n β j hjn h1 h2]
      simp [decSet, show ¬ n < j by omega, show n ≠ j by omega]; omega
    · have hjn' : j = n := by omega
      subst hjn'
      rw [bval, bval, h2]
      have hz : bval j β = 0 := (bval_zero_iff j _).2 h1
      have := bval_allTrue j (decSet β j) fun i hi => by simp [decSet, hi]
      simp [hz, decSet]; omega

theorem exists_inc : ∀ (n : ℕ) (β : ℕ → Bool), bval n β + 1 < 2 ^ n →
    ∃ j < n, (∀ i < j, β i = true) ∧ β j = false := by
  intro n β h
  by_contra hne
  push_neg at hne
  have : ∀ i < n, β i = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_contra hb
      exact hb (hne i hi (fun k hk => ih k hk (by omega)) |> fun h => by simpa using h)
  have := bval_allTrue n β this
  omega

theorem exists_dec : ∀ (n : ℕ) (β : ℕ → Bool), 0 < bval n β →
    ∃ j < n, (∀ i < j, β i = false) ∧ β j = true := by
  intro n β h
  by_contra hne
  push_neg at hne
  have : ∀ i < n, β i = false := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_contra hb
      exact hb (hne i hi (fun k hk => ih k hk (by omega)) |> fun h => by simpa using h)
  have := (bval_zero_iff n β).2 this
  omega

theorem bval_testBit_mod (x : ℕ) : ∀ n, bval n x.testBit = x % 2 ^ n
  | 0 => by simp [bval, Nat.mod_one]
  | n + 1 => by
    rw [bval, bval_testBit_mod x n, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ n) with h | h <;> simp [h] <;> ring

theorem bval_testBit {n x : ℕ} (hx : x < 2 ^ n) : bval n x.testBit = x := by
  rw [bval_testBit_mod, Nat.mod_eq_of_lt hx]

end DB

end FOND
