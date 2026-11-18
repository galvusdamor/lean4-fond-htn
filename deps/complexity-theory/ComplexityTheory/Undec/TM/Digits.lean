import ComplexityTheory.Undec.TM.Chain
import Mathlib.Tactic

/-!
# The binary encoding of a natural number is primitive recursive

`Turing.PartrecToTM2.trNat` writes a natural number on the tape in binary, least significant
digit first, with no trailing zero digit.  The reduction of
`ComplexityTheory/Undec/TM/Reduce.lean` has to produce that word, so it has to be a primitive
recursive function of the number.  This file proves it, after recording the recursion
`trNat n = digit n :: trNat (n / 2)` that `trNat` satisfies.
-/

namespace HTN

namespace Undec

namespace TMChain

open Turing Turing.PartrecToTM2

/-! ### The recursion satisfied by `trNat` -/

theorem trNum_bit0 (x : Num) (hx : x ≠ 0) : trNum (Num.bit0 x) = Γ'.bit0 :: trNum x := by
  cases x with
  | zero => exact absurd rfl hx
  | pos p => rfl

theorem trNum_bit1 (x : Num) : trNum (Num.bit1 x) = Γ'.bit1 :: trNum x := by
  cases x with
  | zero => rfl
  | pos p => rfl

theorem trNat_rec (n : ℕ) (hn : n ≠ 0) :
    trNat n = (if n % 2 = 1 then Γ'.bit1 else Γ'.bit0) :: trNat (n / 2) := by
  have hcast : ∀ m : ℕ, trNat m = trNum (Num.ofNat' m) := fun m => by rw [trNat, Num.ofNat'_eq]
  have hd : Nat.bit n.bodd n.div2 = n := Nat.bit_bodd_div2 n
  have key : trNat n = trNum ((cond n.bodd Num.bit1 Num.bit0) (Num.ofNat' n.div2)) := by
    conv_lhs => rw [← hd]
    rw [hcast, Num.ofNat'_bit]
  have hdiv : trNat (n / 2) = trNum (Num.ofNat' n.div2) := by
    rw [← Nat.div2_val, hcast]
  rw [key, hdiv, Nat.mod_two_of_bodd]
  cases hb : n.bodd with
  | true => simpa using trNum_bit1 (Num.ofNat' n.div2)
  | false =>
      have hne : Num.ofNat' n.div2 ≠ 0 := by
        intro h
        have hz : n.div2 = 0 := by
          have := congrArg (fun x : Num => (x : ℕ)) h
          simpa using this
        rw [hb, hz] at hd
        exact hn (by simpa using hd.symm)
      simpa using trNum_bit0 _ hne

/-! ### Primitive recursiveness -/

/-- The binary digits of `n`, each mapped to a natural number by `f`. -/
def digs (f : Γ' → ℕ) (n : ℕ) : List ℕ := (trNat n).map f

theorem digs_zero (f : Γ' → ℕ) : digs f 0 = [] := by simp [digs]

theorem digs_rec (f : Γ' → ℕ) (n : ℕ) (hn : n ≠ 0) :
    digs f n = (if n % 2 = 1 then f Γ'.bit1 else f Γ'.bit0) :: digs f (n / 2) := by
  rw [digs, trNat_rec n hn]
  by_cases h : n % 2 = 1 <;> simp [h, digs]

/-- **The binary encoding is primitive recursive.** -/
theorem primrec_digs (f : Γ' → ℕ) : Primrec (digs f) := by
  set d0 := f Γ'.bit0 with hd0
  set d1 := f Γ'.bit1 with hd1
  have hlen : Primrec (fun p : Unit × List (List ℕ) => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hcond : PrimrecPred (fun p : Unit × List (List ℕ) => p.2.length = 0) :=
    Primrec.eq.comp hlen (Primrec.const 0)
  have hget : Primrec (fun p : Unit × List (List ℕ) => p.2[p.2.length / 2]?) :=
    Primrec.list_getElem?.comp Primrec.snd (Primrec.nat_div.comp hlen (Primrec.const 2))
  have hd : Primrec (fun p : Unit × List (List ℕ) => if p.2.length % 2 = 1 then d1 else d0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hlen (Primrec.const 2))
      (Primrec.const 1)) (Primrec.const d1) (Primrec.const d0)
  have hmap : Primrec (fun p : Unit × List (List ℕ) =>
      (p.2[p.2.length / 2]?).map fun r => (if p.2.length % 2 = 1 then d1 else d0) :: r) :=
    Primrec.option_map hget (Primrec.list_cons.comp (hd.comp Primrec.fst) Primrec.snd)
  have hgg : Primrec₂ (fun (_ : Unit) (L : List (List ℕ)) =>
      if L.length = 0 then some ([] : List ℕ)
      else (L[L.length / 2]?).map fun r => (if L.length % 2 = 1 then d1 else d0) :: r) :=
    Primrec.ite hcond (Primrec.const (some [])) hmap
  have H : ∀ (a : Unit) (n : ℕ),
      (fun (_ : Unit) (L : List (List ℕ)) =>
        if L.length = 0 then some ([] : List ℕ)
        else (L[L.length / 2]?).map fun r => (if L.length % 2 = 1 then d1 else d0) :: r)
          a ((List.range n).map (digs f)) = some (digs f n) := by
    intro a n
    simp only [List.length_map, List.length_range]
    cases n with
    | zero => simp [digs_zero]
    | succ m =>
        have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
        rw [if_neg (by omega), List.getElem?_map, List.getElem?_range hlt]
        simp only [Option.map_some]
        rw [digs_rec f (m + 1) (by omega)]
  have key := Primrec.nat_strong_rec (fun (_ : Unit) n => digs f n) hgg H
  have hfin :=
    @Primrec₂.comp ℕ Unit ℕ (List ℕ) _ _ _ _ (fun _ m => digs f m) (fun _ => ()) id key
      (Primrec.const ()) Primrec.id
  exact hfin

end TMChain

end Undec

end HTN
