import FondHtn.HardTR.Tab
/-!
# CB22 Thm 5, P3a: the intervals of the first row

The first row of the tableau on the padded input `padExp2 q x` (length `A = 2 n + 2 + 2 ^ p`,
`n = |x|`, `p = 2 ^ q(n)`) is constant on the intervals

* `[ℓ, ℓ + 1)` for `ℓ ≤ 2 n` (the doubled input and its end marker),
* `[2 n + 1, A)` (the padding ones),
* `[A, 2 ^ (B + 1))` (blanks; every index reached by the game is `< 2 ^ B + 2 ^ B`).

`FOND.HardTR.TT.rowSpec` is the corresponding parameter set of the tableau transducer, with the
special positions `P = [0, n + 2) ++ ext ++ [B + 1]` (`ext`: the position of the high one-bit of
`A`), and **`FOND.HardTR.TT.rowSpec_valid`** checks its hypotheses `Spec.Valid`, given only that
the first row is constant on the two long intervals.
-/

namespace FOND

namespace HardTR

namespace TT

/-- The end of the padded input. -/
def rA (n p : ℕ) : ℕ := 2 * n + 2 + 2 ^ p

/-- The lower bounds of the intervals. -/
def rlo (n p ℓ : ℕ) : ℕ := if ℓ ≤ 2 * n + 1 then ℓ else rA n p

/-- The upper bounds of the intervals. -/
def rhi (n p e ℓ : ℕ) : ℕ :=
  if ℓ ≤ 2 * n then ℓ + 1 else if ℓ = 2 * n + 1 then rA n p else 2 ^ (2 ^ e + 1)

/-- The positions `≥ n + 2` of one-bits of `A`, except `B + 1`. -/
def rext (n p : ℕ) : List ℕ :=
  if n + 2 ≤ p then [p] else if (rA n p).testBit (n + 2) then [n + 2] else []

/-- The special positions. -/
def rP (n p e : ℕ) : List ℕ := List.range (n + 2) ++ rext n p ++ [2 ^ e + 1]

/-- **The parameters of the tableau transducer for the padded input.** -/
def rowSpec {S : Type} (F : Option S → S → S → S) (row0 : ℕ → S) (acc : Set S) (e n p : ℕ) :
    Spec S where
  e := e
  F := F
  row0 := row0
  acc := acc
  no := 2 * n + 3
  sg ℓ := row0 (rlo n p ℓ)
  lo := rlo n p
  hi := rhi n p e
  P := rP n p e

theorem two_mul_add_lt_two_pow (n : ℕ) : 2 * n + 2 < 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem mem_rP_of_lt {n p e j : ℕ} (h : j < n + 2) : j ∈ rP n p e := by
  simp [rP, h]

theorem bit_small {n p e v j : ℕ} (hv : v < 2 ^ (n + 2)) (h : v.testBit j = true) :
    j ∈ rP n p e := by
  apply mem_rP_of_lt
  by_contra hj
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
    (by omega)))] at h
  exact absurd h (by simp)

theorem bit_A {n p e j : ℕ} (h : (rA n p).testBit j = true) : j ∈ rP n p e := by
  have ha := two_mul_add_lt_two_pow n
  by_cases hp : n + 2 ≤ p
  · have hA : rA n p = 2 ^ p + (2 * n + 2) := by unfold rA; ring
    rcases lt_trichotomy j p with hj | rfl | hj
    · rw [hA, Nat.testBit_two_pow_add_gt hj] at h
      exact bit_small ha h
    · simp [rP, rext, hp]
    · have : rA n p < 2 ^ j := by
        rw [hA]
        have : 2 ^ (n + 2) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
        have : 2 ^ (p + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        rw [pow_succ] at this; omega
      rw [Nat.testBit_eq_false_of_lt this] at h; exact absurd h (by simp)
  · have hA : rA n p < 2 ^ (n + 3) := by
      unfold rA
      have : 2 ^ p ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ]; omega
    rcases lt_trichotomy j (n + 2) with hj | rfl | hj
    · exact mem_rP_of_lt hj
    · simp [rP, rext, hp, h]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num)
        (by omega)))] at h
      exact absurd h (by simp)

theorem bit_pow {n p e j : ℕ} (h : (2 ^ (2 ^ e + 1)).testBit j = true) : j ∈ rP n p e := by
  rw [Nat.testBit_two_pow] at h
  simp at h; subst h; simp [rP]

/-- **The hypotheses of the transducer hold** for the intervals of the padded input, provided
`B = 2 ^ e` is large enough and the first row is constant on the two long intervals. -/
theorem rowSpec_valid {S : Type} {F : Option S → S → S → S} {row0 : ℕ → S} {acc : Set S}
    {e n p : ℕ} (hB : p + n + 3 ≤ 2 ^ e)
    (hrow1 : ∀ i, 2 * n + 1 ≤ i → i < rA n p → row0 i = row0 (2 * n + 1))
    (hrow2 : ∀ i, rA n p ≤ i → row0 i = row0 (rA n p)) :
    (rowSpec F row0 acc e n p).Valid := by
  have ha := two_mul_add_lt_two_pow n
  have hpB : 2 ^ p < 2 ^ (2 ^ e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnB : 2 ^ (n + 2) ≤ 2 ^ (2 ^ e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAB : rA n p < 2 ^ (2 ^ e + 1) := by unfold rA; rw [pow_succ]; omega
  have hB2 : 2 ^ (2 ^ e + 1) < 2 ^ (2 * 2 ^ e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- all bounds
  have hbits : ∀ ℓ < 2 * n + 3, ∀ j, ((rlo n p ℓ).testBit j = true ∨
      (rhi n p e ℓ).testBit j = true) → j ∈ rP n p e := by
    intro ℓ hℓ j h
    unfold rlo rhi at h
    rcases h with h | h
    · split_ifs at h with h1
      · exact bit_small (by omega) h
      · exact bit_A h
    · split_ifs at h with h1 h2
      · exact bit_small (by omega) h
      · exact bit_A h
      · exact bit_pow h
  have hlt : ∀ ℓ < 2 * n + 3, rlo n p ℓ ≤ 2 ^ (2 ^ e + 1) ∧ rhi n p e ℓ ≤ 2 ^ (2 ^ e + 1) := by
    intro ℓ hℓ
    unfold rlo rhi
    constructor
    · split_ifs <;> omega
    · split_ifs <;> omega
  refine ⟨?_, ?_, fun ℓ hℓ j h => hbits ℓ hℓ j (Or.inl h), fun ℓ hℓ j h => hbits ℓ hℓ j (Or.inr h),
    fun ℓ hℓ => lt_of_le_of_lt (hlt ℓ hℓ).1 hB2, fun ℓ hℓ => lt_of_le_of_lt (hlt ℓ hℓ).2 hB2,
    fun ℓ hℓ i h1 h2 => ?_⟩
  · simp only [rowSpec, rP, rext]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨List.pairwise_lt_range, ?_, ?_⟩, by simp, ?_⟩
    · split_ifs <;> simp
    · intro a ha b hb
      simp only [List.mem_range] at ha
      split_ifs at hb with h1 h2 <;> simp at hb <;> omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_range] at ha
      simp only [List.mem_singleton] at hb
      subst hb
      rcases ha with ha | ha
      · omega
      · split_ifs at ha with h1 h2 <;> simp at ha <;> omega
  · intro j hj
    simp only [rowSpec, rP, rext, List.mem_append, List.mem_range, List.mem_singleton] at hj
    rcases hj with (hj | hj) | hj
    · simp only [Spec.B, rowSpec]; omega
    · split_ifs at hj with h1 h2 <;> simp at hj <;> simp only [Spec.B, rowSpec] <;> omega
    · simp only [Spec.B, rowSpec]; omega
  · show row0 (rlo n p ℓ) = row0 i
    change rlo n p ℓ ≤ i at h1
    change i < rhi n p e ℓ at h2
    unfold rlo at h1 ⊢
    unfold rhi at h2
    by_cases ha : ℓ ≤ 2 * n
    · rw [if_pos (by omega)] at h1 ⊢; rw [if_pos ha] at h2; congr 1; omega
    · by_cases hb : ℓ = 2 * n + 1
      · subst hb; rw [if_pos le_rfl] at h1 ⊢; rw [if_neg ha, if_pos rfl] at h2
        exact (hrow1 i h1 h2).symm
      · rw [if_neg (by omega)] at h1 ⊢; exact (hrow2 i h1).symm

end TT

end HardTR

end FOND
