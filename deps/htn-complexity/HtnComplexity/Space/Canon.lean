import HtnComplexity.Space.TblSolver
/-!
# Canonical numerals, and reading a state off a bit string

A configuration of the target-side machine of `HtnComplexity/Space/TblMachine.lean` is a
state of the transition system of `HtnComplexity/Space/StripsSystem.lean`, written as the
serialised list of the binary numerals of its facts (`HTN.Space.encState`).  The machine's tests
compare *strings*, so two entries carrying the same number by different strings would count as
two different facts; the machine therefore insists that every entry of a configuration is a
**canonical** numeral, i.e. the numeral `HTN.PTime.bitsOfNat` produces.

This file collects what is needed about that notion:

* `HTN.Space.IsCanon` and its characterisation `HTN.Space.isCanon_iff_getLast`, which is what a
  test on the *encoded* entry can see (the last bit of the numeral is written out in the entry);
* `HTN.Space.decSt` — the state a list of entries carries — with
  `HTN.Space.encState_decSt` and `HTN.Space.mem_decSt_iff` inverting `HTN.Space.encState` on
  canonical entries;
* `HTN.Space.length_bitsOfNat_le_of_lt_two_pow`, the converse of
  `HTN.Space.lt_two_pow_of_length_bitsOfNat_le` of `HtnComplexity/Space/InstBound.lean`.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### The length of a numeral -/

theorem bitsOfNat_eq_ite (n : ℕ) :
    bitsOfNat n = if n = 0 then [] else decide (n % 2 = 1) :: bitsOfNat (n / 2) := by
  cases n with
  | zero => simp
  | succ m => rw [bitsOfNat_succ]; simp

/-- **A number below `2 ^ k` has a numeral of at most `k` bits.** -/
theorem length_bitsOfNat_le_of_lt_two_pow : ∀ {k n : ℕ}, n < 2 ^ k → (bitsOfNat n).length ≤ k := by
  intro k
  induction k with
  | zero => intro n h; interval_cases n; simp
  | succ k ih =>
    intro n h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [bitsOfNat_eq_ite, if_neg (by omega)]
      have : n / 2 < 2 ^ k := by
        rw [pow_succ] at h
        omega
      simpa using ih this

/-! ### Canonical numerals -/

/-- A bit string is **canonical** when it is the numeral of the number it codes. -/
def IsCanon (w : List Bool) : Prop := bitsOfNat (natOfBits w) = w

theorem isCanon_bitsOfNat (n : ℕ) : IsCanon (bitsOfNat n) := by
  rw [IsCanon, natOfBits_bitsOfNat]

theorem natOfBits_ne_zero_of_isCanon {w : List Bool} (hc : IsCanon w) (hw : w ≠ []) :
    natOfBits w ≠ 0 := by
  intro h
  apply hw
  rw [← hc, h, bitsOfNat_zero]

theorem getLast?_bitsOfNat : ∀ {n : ℕ}, n ≠ 0 → (bitsOfNat n).getLast? = some true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [bitsOfNat_eq_ite, if_neg hn]
    rcases Nat.eq_zero_or_pos (n / 2) with h2 | h2
    · have hone : n = 1 := by omega
      subst hone
      simp
    · have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      rw [List.getLast?_cons, ih _ hlt (by omega)]
      rfl

theorem isCanon_of_getLast : ∀ {w : List Bool}, (w = [] ∨ w.getLast? = some true) → IsCanon w := by
  intro w
  induction w with
  | nil => intro _; simp [IsCanon]
  | cons b w ih =>
    intro h
    rcases h with h | h
    · simp at h
    · rw [List.getLast?_cons] at h
      rcases eq_or_ne w [] with rfl | hw
      · simp only [List.getLast?_nil, Option.getD_none, Option.some.injEq] at h
        subst h
        simp [IsCanon, natOfBits_cons]
      · have hlast : w.getLast? = some true := by
          rcases hg : w.getLast? with _ | x
          · exact absurd (List.getLast?_eq_none_iff.1 hg) hw
          · rw [hg] at h; simp only [Option.getD_some, Option.some.injEq] at h; simp [h]
        have hc := ih (Or.inr hlast)
        have hne : natOfBits w ≠ 0 := natOfBits_ne_zero_of_isCanon hc hw
        rw [IsCanon, natOfBits_cons, bitsOfNat_eq_ite, if_neg (by cases b <;> simp <;> omega)]
        have h1 : ((if b then 1 else 0) + 2 * natOfBits w) % 2 = (if b then 1 else 0) := by
          cases b <;> simp <;> omega
        have h2 : ((if b then 1 else 0) + 2 * natOfBits w) / 2 = natOfBits w := by
          cases b <;> simp <;> omega
        rw [h1, h2, hc]
        cases b <;> simp

/-- **A string is canonical exactly when it is empty or ends with a one bit.** -/
theorem isCanon_iff_getLast (w : List Bool) : IsCanon w ↔ w = [] ∨ w.getLast? = some true := by
  refine ⟨fun h => ?_, isCanon_of_getLast⟩
  rcases eq_or_ne w [] with rfl | hw
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [← h]
    exact getLast?_bitsOfNat (natOfBits_ne_zero_of_isCanon h hw)

/-! ### Reading a state off a list of entries -/

/-- The state a list of entries carries. -/
def decSt (l : List (List Bool)) : List ℕ := l.map natOfBits

theorem encState_decSt {l : List (List Bool)} (hc : ∀ w ∈ l, IsCanon w) :
    encState (decSt l) = blist l := by
  rw [encState, decSt, List.map_map]
  exact congrArg blist ((List.map_congr_left fun w hw => hc w hw).trans (List.map_id l))

theorem mem_decSt_iff {l : List (List Bool)} (hc : ∀ w ∈ l, IsCanon w) (f : ℕ) :
    f ∈ decSt l ↔ bitsOfNat f ∈ l := by
  constructor
  · rintro hf
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hf
    rwa [hc w hw]
  · intro hf
    exact List.mem_map.2 ⟨bitsOfNat f, hf, natOfBits_bitsOfNat f⟩

theorem decSt_length (l : List (List Bool)) : (decSt l).length = l.length := by
  simp [decSt]

end Space

end HTN
