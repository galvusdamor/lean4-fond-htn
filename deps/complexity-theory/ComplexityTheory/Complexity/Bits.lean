import ComplexityTheory.Complexity.Cobham
import ComplexityTheory.Complexity.Basic
/-!
# Binary coding of natural numbers

`ComplexityTheory/Complexity/Cobham.lean` defines polynomial time for functions on bit
strings.  To use it on descriptions one needs a binary coding of natural numbers; this file
provides one, little-endian, with everything the transfer needs:

* `HTN.PTime.bitsOfNat` and `HTN.PTime.natOfBits`, inverse to each other
  (`HTN.PTime.natOfBits_bitsOfNat`), so `bitsOfNat` is injective;
* both are primitive recursive (`HTN.PTime.primrec_bitsOfNat`,
  `HTN.PTime.primrec_natOfBits`), which is what makes a polynomial-time function on bit strings
  induce a computable function on descriptions.

The length of `bitsOfNat n` is the number of binary digits of `n`, so this is the coding with
respect to which "polynomial time" is the usual notion.
-/

namespace HTN

namespace PTime

/-- The number coded by a bit string, least significant bit first. -/
def natOfBits : List Bool → ℕ
  | [] => 0
  | b :: x => (if b then 1 else 0) + 2 * natOfBits x

@[simp] theorem natOfBits_nil : natOfBits [] = 0 := rfl

theorem natOfBits_cons (b : Bool) (x : List Bool) :
    natOfBits (b :: x) = (if b then 1 else 0) + 2 * natOfBits x := rfl

@[simp] theorem bitsOfNat_zero : bitsOfNat 0 = [] := by rw [bitsOfNat]

theorem bitsOfNat_succ (n : ℕ) :
    bitsOfNat (n + 1) = decide ((n + 1) % 2 = 1) :: bitsOfNat ((n + 1) / 2) := by
  rw [bitsOfNat]

/-- The two codings are inverse to each other. -/
theorem natOfBits_bitsOfNat : ∀ n : ℕ, natOfBits (bitsOfNat n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [bitsOfNat_zero, natOfBits_nil]
    | m + 1 =>
      have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
      rw [bitsOfNat_succ, natOfBits_cons, ih _ hlt]
      by_cases h : (m + 1) % 2 = 1 <;> simp [h] <;> omega

@[simp] theorem bitsOfNat_one : bitsOfNat 1 = [true] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, bitsOfNat_succ]
  norm_num

theorem bitsOfNat_injective : Function.Injective bitsOfNat := by
  intro m n h
  have := congrArg natOfBits h
  rwa [natOfBits_bitsOfNat, natOfBits_bitsOfNat] at this

/-! ### Both codings are primitive recursive -/

theorem natOfBits_eq_foldr (x : List Bool) :
    natOfBits x = x.foldr (fun b s => (if b then 1 else 0) + 2 * s) 0 := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [natOfBits_cons, ih, List.foldr_cons]

theorem primrec_natOfBits : Primrec natOfBits := by
  have h : Primrec (fun x : List Bool =>
      x.foldr (fun b s => (if b then 1 else 0) + 2 * s) 0) := by
    refine Primrec.list_foldr (f := fun x : List Bool => x) (g := fun _ => (0 : ℕ))
      (h := fun _ p => (if p.1 then 1 else 0) + 2 * p.2) Primrec.id (Primrec.const 0) ?_
    have hb : Primrec (fun p : List Bool × (Bool × ℕ) => if p.2.1 then 1 else 0) :=
      Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0)
    have hs : Primrec (fun p : List Bool × (Bool × ℕ) => 2 * p.2.2) :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp (Primrec.snd))
    exact (Primrec.nat_add.comp hb hs).to₂
  exact h.of_eq fun x => (natOfBits_eq_foldr x).symm

theorem getD_map_range {α : Type} [Inhabited α] (f : ℕ → α) {i n : ℕ} (h : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  have hlen : ((List.range n).map f).length = n := by simp
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp

theorem primrec_bitsOfNat : Primrec bitsOfNat := by
  have hg : Primrec₂ (fun (_ : Unit) (l : List (List Bool)) =>
      (some (if l.length = 0 then [] else
        decide (l.length % 2 = 1) :: l.getD (l.length / 2) []) : Option (List Bool))) := by
    have hlen : Primrec (fun p : Unit × List (List Bool) => p.2.length) :=
      Primrec.list_length.comp Primrec.snd
    have hpred : PrimrecPred (fun p : Unit × List (List Bool) => p.2.length % 2 = 1) :=
      Primrec.eq.comp (Primrec.nat_mod.comp hlen (Primrec.const 2)) (Primrec.const 1)
    have hbit : Primrec (fun p : Unit × List (List Bool) => decide (p.2.length % 2 = 1)) :=
      (Primrec.ite hpred (Primrec.const true) (Primrec.const false)).of_eq fun p => by
        by_cases h : p.2.length % 2 = 1 <;> simp [h]
    have hrec : Primrec (fun p : Unit × List (List Bool) =>
        p.2.getD (p.2.length / 2) []) :=
      (Primrec.list_getD []).comp Primrec.snd (Primrec.nat_div.comp hlen (Primrec.const 2))
    have : Primrec (fun p : Unit × List (List Bool) =>
        (some (if p.2.length = 0 then [] else
          decide (p.2.length % 2 = 1) :: p.2.getD (p.2.length / 2) []) : Option (List Bool))) :=
      Primrec.option_some.comp
        (Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const [])
          (Primrec.list_cons.comp hbit hrec))
    exact this.to₂
  have hstrong := Primrec.nat_strong_rec (fun (_ : Unit) n => bitsOfNat n) hg ?_
  · exact (hstrong.comp (Primrec.const ()) Primrec.id).of_eq fun n => rfl
  · intro _ n
    have hlen : ((List.range n).map bitsOfNat).length = n := by simp
    cases n with
    | zero => simp
    | succ m =>
      have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
      simp only [hlen, Nat.succ_ne_zero, if_false]
      rw [getD_map_range bitsOfNat hlt, ← bitsOfNat_succ]

theorem computable_natOfBits : Computable natOfBits := primrec_natOfBits.to_comp

theorem computable_bitsOfNat : Computable bitsOfNat := primrec_bitsOfNat.to_comp

end PTime

end HTN
