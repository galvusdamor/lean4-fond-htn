import Mathlib

/-!
# Binary counters bit by bit

The encoding of `HtnComplexity/SpaceEnc/` keeps two `m`-bit numbers (the position counter and
the head) as one fact per bit, and increments or decrements them by actions that look at the
lowest bits only.  This file proves the arithmetic behind those actions.
-/

namespace HTN

namespace SpaceEnc

/-- **Incrementing**: if the bits below `k` are set and bit `k` is clear, adding one clears the
bits below `k`, sets bit `k` and keeps the others. -/
theorem testBit_succ_of {k c : ℕ} (hk : c.testBit k = false) (hlow : ∀ j < k, c.testBit j = true)
    (j : ℕ) : (c + 1).testBit j = if j < k then false else if j = k then true else c.testBit j := by
  induction k generalizing c j with
  | zero =>
    have hc : c % 2 = 0 := by
      have := Nat.testBit_zero c
      rw [hk] at this
      simp at this
      omega
    rcases j with _ | j
    · simp [Nat.testBit_zero]
      omega
    · simp only [Nat.not_lt_zero, if_false, Nat.add_one_ne_zero]
      rw [Nat.testBit_succ, Nat.testBit_succ]
      congr 1
      omega
  | succ k ih =>
    have h0 := hlow 0 (by omega)
    have hc : c % 2 = 1 := by
      have := Nat.testBit_zero c
      rw [h0] at this
      simpa using this.symm
    have hk' : (c / 2).testBit k = false := by rw [← Nat.testBit_succ]; exact hk
    have hlow' : ∀ j < k, (c / 2).testBit j = true := fun j hj => by
      rw [← Nat.testBit_succ]; exact hlow _ (by omega)
    rcases j with _ | j
    · simp [Nat.testBit_zero]
      omega
    · rw [Nat.testBit_succ, show (c + 1) / 2 = c / 2 + 1 by omega, ih hk' hlow' j,
        Nat.testBit_succ]
      by_cases h1 : j < k
      · simp [h1]
      · by_cases h2 : j = k
        · subst h2; simp
        · simp [h1, h2]

/-- **Decrementing**: if the bits below `k` are clear and bit `k` is set, subtracting one sets
the bits below `k`, clears bit `k` and keeps the others. -/
theorem testBit_pred_of {k c : ℕ} (hk : c.testBit k = true) (hlow : ∀ j < k, c.testBit j = false)
    (j : ℕ) : (c - 1).testBit j = if j < k then true else if j = k then false else c.testBit j := by
  have hpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · simp at hk
    · exact h
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- the bits of `d` below `k` are set and bit `k` is clear
  have hd : ∀ j ≤ k, d.testBit j = decide (j < k) := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | _ j ihj =>
      by_contra hne
      -- take the lowest position where the claim fails
      have key : ∀ i < j, d.testBit i = true := fun i hi => by
        rw [ihj i hi (by omega)]; simp [show i < k by omega]
      by_cases hjk : j < k
      · have hdj : d.testBit j = false := by simpa [hjk] using hne
        have := testBit_succ_of hdj key j
        rw [hlow j hjk] at this
        simp at this
      · have hjk' : j = k := by omega
        subst hjk'
        have hdj : d.testBit j = true := by simpa using hne
        -- then `d + 1` has bit `j` clear by the lowest clear bit of `d` above `j`
        have : (d + 1).testBit j = false := by
          by_cases hall : ∀ i, d.testBit i = true
          · exfalso
            have := Nat.testBit_lt_two_pow (x := d) (i := d) Nat.lt_two_pow_self
            rw [hall d] at this
            simp at this
          · push_neg at hall
            obtain ⟨i₀, hi₀⟩ := hall
            -- the least clear bit
            classical
            let i := Nat.find (⟨i₀, hi₀⟩ : ∃ i, d.testBit i ≠ true)
            have hi : d.testBit i ≠ true := Nat.find_spec (⟨i₀, hi₀⟩ : ∃ i, d.testBit i ≠ true)
            have hlt : ∀ i' < i, d.testBit i' = true := fun i' h' => by
              have := Nat.find_min (⟨i₀, hi₀⟩ : ∃ i, d.testBit i ≠ true) h'
              simpa using this
            have hji : j < i := by
              by_contra hji
              rcases Nat.lt_or_ge i j with h | h
              · exact hi (key i h)
              · exact hi (by rwa [show i = j by omega])
            have := testBit_succ_of (Bool.eq_false_iff.2 hi) hlt j
            rw [this]; simp [hji]
        rw [hk] at this; simp at this
  have hdk : d.testBit k = false := by simpa using hd k le_rfl
  have hdlow : ∀ j < k, d.testBit j = true := fun j hj => by simpa [hj] using hd j hj.le
  have hsucc := testBit_succ_of hdk hdlow
  by_cases h1 : j < k
  · simp [h1, hdlow j h1]
  · by_cases h2 : j = k
    · subst h2; simp [hdk]
    · have := hsucc j
      simp only [h1, h2, if_false] at this
      simp [h1, h2, this]

/-- Two numbers below `2 ^ m` with the same lowest `m` bits are equal. -/
theorem eq_of_testBit_lt {m a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : ∀ i < m, a.testBit i = b.testBit i) : a = b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < m
  · exact h i hi
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- A number below `2 ^ m` with a clear bit below `m` stays below `2 ^ m` when incremented. -/
theorem succ_lt_of_testBit {m k c : ℕ} (hc : c < 2 ^ m) (hkm : k < m) (hk : c.testBit k = false)
    (hlow : ∀ j < k, c.testBit j = true) : c + 1 < 2 ^ m := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [testBit_succ_of hk hlow i]
  simp only [show ¬ i < k by omega, show i ≠ k by omega, if_false]
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi))

/-- A number below `2 ^ m` with all bits below `m` set is `2 ^ m - 1`. -/
theorem eq_of_all_testBit {m c : ℕ} (hc : c < 2 ^ m) (h : ∀ j < m, c.testBit j = true) :
    c = 2 ^ m - 1 :=
  eq_of_testBit_lt hc (by have := Nat.one_le_two_pow (n := m); omega)
    fun i hi => by rw [h i hi, Nat.testBit_two_pow_sub_one]; simp [hi]

/-- A number below `2 ^ m` with all bits below `m` clear is `0`. -/
theorem eq_zero_of_all_testBit {m c : ℕ} (hc : c < 2 ^ m) (h : ∀ j < m, c.testBit j = false) :
    c = 0 :=
  eq_of_testBit_lt hc (Nat.two_pow_pos m) fun i hi => by rw [h i hi]; simp

end SpaceEnc

end HTN
