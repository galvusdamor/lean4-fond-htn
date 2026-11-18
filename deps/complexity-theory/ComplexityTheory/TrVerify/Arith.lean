import Mathlib

/-!
# Arithmetic for the doubly exponential bound of `HTN-TR`

Two inequalities between natural numbers, used in `HtnCompilability/TrVerify/N2Exp.lean`:

* `HTN.Syn.TrVer.cfg_arith` — the number of normal forms of configurations of the progression
  search (`HTN.Syn.cfgBound`) with an exponential bound `B ≤ 2 ^ (X (X + 1))` on the number of
  open tasks is at most `2 ^ 2 ^ (3 X (X + 1) + 2)`;
* `HTN.Syn.TrVer.cert_arith` — the certificate bound of a path witness whose paths have at most
  `V + 1` steps and with at most `(Z + 1) (V + 1)` entries is at most `2 ^ 2 ^ (T + 3 Z + 9)` when
  `V ≤ 2 ^ 2 ^ T`.
-/

namespace HTN

namespace Syn

namespace TrVer

/-- The bound on the content of one entry whose path has at most `m` steps. -/
def entBoundG (sq sd B m : ℕ) : ℕ :=
  1 + (1 + m * (2 * (8 * B + 4) + 2)) + (1 + (sq + sd) * (2 * B + 2)) +
    3 * (1 + sd * (2 * B + 2))

/-- The bound on the certificate of a path witness with paths of at most `m` steps and at most
`N` entries. -/
def certBoundG (sq sd B m N : ℕ) : ℕ := 1 + N * (2 * entBoundG sq sd B m + 2)

theorem two_pow_add_le (k c : ℕ) : 2 ^ k + c ≤ 2 ^ (k + c) := by
  have h1 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_add]; nlinarith

/-- `X (X + 1) ^ X ≤ 2 ^ (X (X + 1))`, the shape of the bound `HTN.Syn.trBnd`. -/
theorem trBnd_arith {X a b c : ℕ} (ha : a ≤ X) (hb : b ≤ X) (hc : c ≤ X) :
    a * (b + 1) ^ c ≤ 2 ^ (X * (X + 1)) := by
  have h1 : X + 1 ≤ 2 ^ X := Nat.lt_two_pow_self
  calc a * (b + 1) ^ c ≤ (X + 1) * (X + 1) ^ X := by
        refine Nat.mul_le_mul (by omega) ?_
        exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hc)
    _ = (X + 1) ^ (X + 1) := by rw [pow_succ, mul_comm]
    _ ≤ (2 ^ X) ^ (X + 1) := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (X * (X + 1)) := by rw [← pow_mul]

/-- **The number of normal forms is doubly exponential.** -/
theorem cfg_arith {X Fa Lb B : ℕ} (hX : 1 ≤ X) (hFa : Fa ≤ X) (hLb : Lb ≤ X)
    (hB : B ≤ 2 ^ (X * (X + 1))) :
    2 ^ Fa * (B * (Lb * (B + 1) ^ B) + 1) ^ B ≤ 2 ^ 2 ^ (3 * (X * (X + 1)) + 2) := by
  set E := X * (X + 1) with hEdef
  have hE1 : 1 ≤ E := by nlinarith
  have hXE : X ≤ E := by nlinarith
  have hEpow : E + 1 ≤ 2 ^ E := Nat.lt_two_pow_self
  set B' := 2 ^ E with hB'def
  have hX1 : X + 1 ≤ B' := by omega
  have hB'2 : B' + 2 ≤ 2 ^ (E + 1) := by
    have : 2 ≤ 2 ^ E := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hE1
    rw [pow_succ]; omega
  have step1 : 2 ^ Fa * (B * (Lb * (B + 1) ^ B) + 1) ^ B ≤
      B' * (B' * (X * (B' + 1) ^ B') + 1) ^ B' := by
    have h1 : 2 ^ Fa ≤ B' := Nat.pow_le_pow_right (by norm_num) (hFa.trans hXE)
    have h2 : B * (Lb * (B + 1) ^ B) + 1 ≤ B' * (X * (B' + 1) ^ B') + 1 := by
      have : (B + 1) ^ B ≤ (B' + 1) ^ B' :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hB)
      gcongr
    have h3 : (B * (Lb * (B + 1) ^ B) + 1) ^ B ≤ (B' * (X * (B' + 1) ^ B') + 1) ^ B' :=
      (Nat.pow_le_pow_left h2 _).trans (Nat.pow_le_pow_right (by omega) hB)
    exact Nat.mul_le_mul h1 h3
  have step2 : B' * (X * (B' + 1) ^ B') + 1 ≤ (B' + 1) ^ (B' + 2) := by
    have hp : 1 ≤ (B' + 1) ^ B' := Nat.one_le_pow _ _ (by omega)
    rw [pow_add]
    have : B' * X ≤ B' * (B' + 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have step3 : B' * (B' * (X * (B' + 1) ^ B') + 1) ^ B' ≤ (B' + 1) ^ ((B' + 2) ^ 2) := by
    calc B' * (B' * (X * (B' + 1) ^ B') + 1) ^ B'
        ≤ (B' + 1) * ((B' + 1) ^ (B' + 2)) ^ B' :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left step2 _)
      _ = (B' + 1) ^ (1 + (B' + 2) * B') := by rw [← pow_mul, pow_add, pow_one]
      _ ≤ (B' + 1) ^ ((B' + 2) ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have step4 : (B' + 1) ^ ((B' + 2) ^ 2) ≤ 2 ^ 2 ^ (3 * E + 2) := by
    calc (B' + 1) ^ ((B' + 2) ^ 2) ≤ (2 ^ (E + 1)) ^ ((B' + 2) ^ 2) :=
          Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ ((E + 1) * (B' + 2) ^ 2) := by rw [← pow_mul]
      _ ≤ 2 ^ (2 ^ E * (2 ^ (E + 1)) ^ 2) := by
          apply Nat.pow_le_pow_right (by norm_num)
          exact Nat.mul_le_mul hEpow (Nat.pow_le_pow_left hB'2 _)
      _ = 2 ^ 2 ^ (3 * E + 2) := by
          congr 1; rw [← pow_mul, ← pow_add]; congr 1; ring
  exact step1.trans (step3.trans step4)

/-- **The certificate bound is doubly exponential.** -/
theorem cert_arith {Z V T sq sd B m N : ℕ} (hsq : sq ≤ Z) (hsd : sd ≤ Z) (hB : B ≤ Z)
    (hm : m ≤ V + 1) (hN : N ≤ (Z + 1) * (V + 1)) (hV : V ≤ 2 ^ 2 ^ T) :
    certBoundG sq sd B m N ≤ 2 ^ 2 ^ (T + 3 * Z + 9) := by
  have hent : entBoundG sq sd B m ≤ (V + 1) * (16 * (Z + 1) ^ 2) := by
    unfold entBoundG
    have h1 : m * (2 * (8 * B + 4) + 2) ≤ (V + 1) * (16 * Z + 10) :=
      Nat.mul_le_mul hm (by omega)
    have h2 : (sq + sd) * (2 * B + 2) ≤ 2 * Z * (2 * Z + 2) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : sd * (2 * B + 2) ≤ Z * (2 * Z + 2) := Nat.mul_le_mul hsd (by omega)
    have h4 : 16 * Z * Z + 16 * Z + 6 ≤ (V + 1) * (16 * Z * Z + 16 * Z + 6) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h5 : (V + 1) * (16 * (Z + 1) ^ 2) =
        (V + 1) * (16 * Z + 10) + (V + 1) * (16 * Z * Z + 16 * Z + 6) := by ring
    rw [h5]
    nlinarith
  have hc : certBoundG sq sd B m N ≤ (V + 1) ^ 2 * (64 * (Z + 1) ^ 3) := by
    unfold certBoundG
    have h1 : N * (2 * entBoundG sq sd B m + 2) ≤
        ((Z + 1) * (V + 1)) * (2 * ((V + 1) * (16 * (Z + 1) ^ 2)) + 2) :=
      Nat.mul_le_mul hN (by omega)
    have h2 : ((Z + 1) * (V + 1)) * (2 * ((V + 1) * (16 * (Z + 1) ^ 2)) + 2) + 1 ≤
        (V + 1) ^ 2 * (64 * (Z + 1) ^ 3) := by
      set a := V + 1
      set b := Z + 1
      have ha : 1 ≤ a := by omega
      have hb : 1 ≤ b := by omega
      have : 1 ≤ a * a * (b * b * b) := Nat.one_le_iff_ne_zero.2 (by positivity)
      have e : (b * a) * (2 * (a * (16 * b ^ 2)) + 2) =
          32 * (a * a * (b * b * b)) + 2 * (b * a) := by ring
      have e2 : a ^ 2 * (64 * b ^ 3) = 64 * (a * a * (b * b * b)) := by ring
      have : b * a ≤ a * a * (b * b * b) := by nlinarith
      rw [e, e2]; omega
    omega
  have hV1 : V + 1 ≤ 2 ^ (2 ^ T + 1) := by
    have := Nat.one_le_two_pow (n := 2 ^ T); rw [pow_succ]; omega
  have hZ : (Z + 1) ^ 3 ≤ 2 ^ (3 * Z) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self _
  calc certBoundG sq sd B m N ≤ (V + 1) ^ 2 * (64 * (Z + 1) ^ 3) := hc
    _ ≤ (2 ^ (2 ^ T + 1)) ^ 2 * (2 ^ 6 * 2 ^ (3 * Z)) := by gcongr; norm_num
    _ = 2 ^ (2 ^ (T + 1) + (3 * Z + 8)) := by
        rw [← pow_mul, ← pow_add, ← pow_add, pow_succ 2 T]; congr 1; ring
    _ ≤ 2 ^ 2 ^ (T + 1 + (3 * Z + 8)) := Nat.pow_le_pow_right (by norm_num) (two_pow_add_le _ _)
    _ = 2 ^ 2 ^ (T + 3 * Z + 9) := by congr 2; ring

end TrVer

end Syn

end HTN
