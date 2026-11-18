import Mathlib

/-!
# Triples as a replacement for zero tests: the invariant

Czerwiński, Jecker, Lasota, Leroux, Orlikowski (FSTTCS 2023, Section 4) replace the zero tests of a
counter program by gadgets of a program *without* zero tests, controlled by three counters
`a`, `b`, `c` started in a *triple* `a = A`, `b = B`, `c = A·(4^B − 1)`.  With `S` the sum of the
"working" counters (`a`, the simulated counters and the temporaries), the gadgets keep

* the invariant `S·4^b = S + c` (`Holds`), or
* the broken invariant `S·4^b < S + c` (`Broken`), which can never be repaired.

A zero-test gadget decrements `b` and moves `S' − S` units from `c` into the working counters,
with `S ≤ S' ≤ 4·S`; it keeps the invariant iff `S' = 4·S`, which the gadget achieves only for an
honest test (`Zero.lean`).  At the end (`b = c = 0`) the invariant holds, so no test was dishonest.

* `holds_test_iff`, `broken_test_of_holds`, `broken_test` — one test;
* `holds_end`, `not_broken_end` — the final configuration.
-/

namespace HTN

namespace Triple

/-- **The invariant.** -/
def Holds (S b c : ℕ) : Prop := S * 4 ^ b = S + c

/-- **The broken invariant.** -/
def Broken (S b c : ℕ) : Prop := S * 4 ^ b < S + c

/-- A triple satisfies the invariant (all working counters but `a` empty). -/
theorem holds_triple (A B : ℕ) : Holds A B (A * (4 ^ B - 1)) := by
  unfold Holds
  have h : 1 ≤ 4 ^ B := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.mul_sub, mul_one]
  have : A ≤ A * 4 ^ B := Nat.le_mul_of_pos_right _ h
  omega

theorem holds_or_broken_of_le {S b c : ℕ} (h : S + c ≥ S * 4 ^ b) : Holds S b c ∨ Broken S b c := by
  unfold Holds Broken; omega

/-- **An honest test keeps the invariant, a dishonest one breaks it.** -/
theorem holds_test_iff {S b c S' c' : ℕ} (hb : 1 ≤ b) (hle : S' ≤ 4 * S)
    (hsum : S' + c' = S + c) (h : Holds S b c) : Holds S' (b - 1) c' ↔ S' = 4 * S := by
  unfold Holds at *
  have e : 4 ^ b = 4 * 4 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e] at h
  have hp : 0 < 4 ^ (b - 1) := by positivity
  constructor
  · intro h'
    have : S' * 4 ^ (b - 1) = (4 * S) * 4 ^ (b - 1) := by
      rw [h', hsum, ← h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp this
  · intro h'
    subst h'
    have : 4 * S * 4 ^ (b - 1) = S * (4 * 4 ^ (b - 1)) := by ring
    omega

theorem broken_test_of_holds {S b c S' c' : ℕ} (hb : 1 ≤ b) (hle : S' ≤ 4 * S)
    (hsum : S' + c' = S + c) (h : Holds S b c) (hne : S' ≠ 4 * S) : Broken S' (b - 1) c' := by
  unfold Holds Broken at *
  have e : 4 ^ b = 4 * 4 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e] at h
  have hp : 0 < 4 ^ (b - 1) := by positivity
  have hlt : S' < 4 * S := lt_of_le_of_ne hle hne
  have : S' * 4 ^ (b - 1) < (4 * S) * 4 ^ (b - 1) := Nat.mul_lt_mul_of_pos_right hlt hp
  rw [hsum, ← h]; nlinarith

/-- **A broken invariant stays broken through a test.** -/
theorem broken_test {S b c S' c' : ℕ} (hb : 1 ≤ b) (hle : S' ≤ 4 * S)
    (hsum : S' + c' = S + c) (h : Broken S b c) : Broken S' (b - 1) c' := by
  unfold Broken at *
  have e : 4 ^ b = 4 * 4 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e] at h
  have : S' * 4 ^ (b - 1) ≤ (4 * S) * 4 ^ (b - 1) := Nat.mul_le_mul_right _ hle
  rw [hsum]; nlinarith

theorem holds_end (S : ℕ) : Holds S 0 0 := by simp [Holds]

theorem not_broken_end (S : ℕ) : ¬ Broken S 0 0 := by simp [Broken]

theorem not_holds_and_broken {S b c : ℕ} (h : Holds S b c) : ¬ Broken S b c := by
  unfold Holds Broken at *; omega

end Triple

end HTN
