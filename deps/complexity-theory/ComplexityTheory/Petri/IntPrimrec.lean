import Mathlib

/-!
# Primitive recursive integer arithmetic

Mathlib's `Primcodable ℤ` instance comes from `Denumerable ℤ`, which codes `n` as `2 n` and
`-(n+1)` as `2 n + 1`.  We prove that the positive and negative parts and the difference of two
natural numbers are primitive recursive, and derive addition, negation, subtraction,
multiplication, the cast from `ℕ`, and the order relation.
-/

namespace HTN

namespace Petri

namespace IntPR

open Primrec

theorem encode_ofNat (n : ℕ) : @Encodable.encode ℤ Primcodable.toEncodable (n : ℤ) = 2 * n := rfl

theorem encode_negSucc (n : ℕ) :
    @Encodable.encode ℤ Primcodable.toEncodable (Int.negSucc n) = 2 * n + 1 := rfl

theorem toNat_eq (z : ℤ) : z.toNat =
    cond (@Encodable.encode ℤ Primcodable.toEncodable z).bodd 0
      (@Encodable.encode ℤ Primcodable.toEncodable z).div2 := by
  cases z with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, encode_ofNat]
    simp [Nat.bodd_mul, Nat.div2_val]
  | negSucc n =>
    rw [encode_negSucc]
    simp [Nat.bodd_mul]

theorem negToNat_eq (z : ℤ) : (-z).toNat =
    cond (@Encodable.encode ℤ Primcodable.toEncodable z).bodd
      ((@Encodable.encode ℤ Primcodable.toEncodable z).div2 + 1) 0 := by
  cases z with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, encode_ofNat]
    simp [Nat.bodd_mul]
  | negSucc n =>
    rw [encode_negSucc]
    simp only [Nat.bodd_mul, Nat.bodd_succ, Nat.bodd_zero, Bool.not_false]
    rw [Nat.div2_val]
    rw [Int.neg_negSucc]
    simp
    omega

/-- The positive part is primitive recursive. -/
theorem toNat : Primrec fun z : ℤ => z.toNat :=
  (Primrec.cond (Primrec.nat_bodd.comp Primrec.encode) (Primrec.const 0)
    (Primrec.nat_div2.comp Primrec.encode)).of_eq fun z => (toNat_eq z).symm

/-- The negative part is primitive recursive. -/
theorem negToNat : Primrec fun z : ℤ => (-z).toNat :=
  (Primrec.cond (Primrec.nat_bodd.comp Primrec.encode)
    (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode)) (Primrec.const 0)).of_eq
      fun z => (negToNat_eq z).symm

theorem sub_eq (a b : ℕ) : (a : ℤ) - b =
    Denumerable.ofNat ℤ (if b ≤ a then 2 * (a - b) else 2 * (b - a - 1) + 1) := by
  split_ifs with h
  · rw [← encode_ofNat]
    rw [Denumerable.ofNat_encode]
    omega
  · rw [← encode_negSucc, Denumerable.ofNat_encode, Int.negSucc_eq]
    omega

/-- The difference of two natural numbers, as an integer, is primitive recursive. -/
theorem natSub : Primrec₂ fun a b : ℕ => (a : ℤ) - b := by
  have hg : Primrec fun p : ℕ × ℕ =>
      if p.2 ≤ p.1 then 2 * (p.1 - p.2) else 2 * (p.2 - p.1 - 1) + 1 :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1))))
  exact ((Primrec.ofNat ℤ).comp hg).of_eq fun p => (sub_eq p.1 p.2).symm

theorem decomp (z : ℤ) : z = (z.toNat : ℤ) - ((-z).toNat : ℤ) := by omega

/-- The cast from `ℕ`. -/
theorem natCast : Primrec fun n : ℕ => (n : ℤ) :=
  (natSub.comp Primrec.id (Primrec.const 0)).of_eq fun n => by simp

/-- Addition. -/
theorem add : Primrec₂ fun a b : ℤ => a + b :=
  Primrec₂.mk ((natSub.comp (Primrec.nat_add.comp (toNat.comp Primrec.fst) (toNat.comp Primrec.snd))
    (Primrec.nat_add.comp (negToNat.comp Primrec.fst) (negToNat.comp Primrec.snd))).of_eq
      fun p => by push_cast; omega)

/-- Negation. -/
theorem neg : Primrec fun a : ℤ => -a :=
  (natSub.comp negToNat toNat).of_eq fun a => by omega

/-- Subtraction. -/
theorem sub : Primrec₂ fun a b : ℤ => a - b :=
  Primrec₂.mk ((add.comp Primrec.fst (neg.comp Primrec.snd)).of_eq fun p => by ring)

/-- Multiplication. -/
theorem mul : Primrec₂ fun a b : ℤ => a * b := by
  refine Primrec₂.mk ((natSub.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (toNat.comp Primrec.fst) (toNat.comp Primrec.snd))
      (Primrec.nat_mul.comp (negToNat.comp Primrec.fst) (negToNat.comp Primrec.snd)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (toNat.comp Primrec.fst) (negToNat.comp Primrec.snd))
      (Primrec.nat_mul.comp (negToNat.comp Primrec.fst) (toNat.comp Primrec.snd)))).of_eq
        fun p => ?_)
  push_cast
  conv_rhs => rw [decomp p.1, decomp p.2]
  ring

/-- The order. -/
theorem le : PrimrecRel fun a b : ℤ => a ≤ b := by
  refine (Primrec.nat_le.comp (Primrec.nat_add.comp (toNat.comp Primrec.fst)
    (negToNat.comp Primrec.snd)) (Primrec.nat_add.comp (toNat.comp Primrec.snd)
      (negToNat.comp Primrec.fst))).of_eq fun p => ?_
  omega

end IntPR

end Petri

end HTN
