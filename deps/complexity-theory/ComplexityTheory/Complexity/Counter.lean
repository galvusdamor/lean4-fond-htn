import ComplexityTheory.Complexity.Blocks
import ComplexityTheory.Complexity.Bits
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Counting in Cobham's class: the binary successor and the length of a word

The concrete polynomial-time encodings of descriptions need more than the block code of
`ComplexityTheory/Complexity/Blocks.lean`: an encoding that mentions a numeral depending on
the *length* of the input word — a fresh fact per position, a bound written into the
description, the index of a state — has to compute that numeral in binary.  This file supplies
the two functions that do it, and proves that both belong to Cobham's class:

* `HTN.PTime.incFn` — the binary successor, a bounded recursion on notation whose step either
  sets the last bit or carries: `HTN.PTime.natOfBits_incFn` and `HTN.PTime.incFn_bitsOfNat`
  identify it with `n ↦ n + 1` on the binary coding of
  `ComplexityTheory/Complexity/Bits.lean`;
* `HTN.PTime.lenFn` — the length of the input word, in binary: the recursion applies the
  successor once per bit.  `HTN.PTime.polyTimeFun_binLength` states the consequence,
  `PolyTimeFun fun w => bitsOfNat w.length`.

Both are bounded by the input itself (one extra bit for the successor), so the bounded
recursion rule applies with a bound as simple as the projection.
-/

namespace HTN

namespace PTime

/-! ### The binary successor -/

/-- The step of the successor at a `false` bit: set it and keep the rest. -/
def incRecFalse : Fn := compFn (consFn true) [proj 0]

/-- The step of the successor at a `true` bit: clear it and carry. -/
def incRecTrue : Fn := compFn (consFn false) [proj 1]

theorem incRecFalse_apply (args : Args) : incRecFalse args = true :: args.getD 0 [] := by
  simp [incRecFalse, compFn, consFn, proj]

theorem incRecTrue_apply (args : Args) : incRecTrue args = false :: args.getD 1 [] := by
  simp [incRecTrue, compFn, consFn, proj]

theorem cobham_incRecFalse : Cobham incRecFalse :=
  Cobham.comp (Cobham.cons true) (by
    intro k hk
    rw [List.mem_singleton.1 hk]
    exact Cobham.proj 0)

theorem cobham_incRecTrue : Cobham incRecTrue :=
  Cobham.comp (Cobham.cons false) (by
    intro k hk
    rw [List.mem_singleton.1 hk]
    exact Cobham.proj 1)

/-- The binary successor, before the arguments are fixed. -/
def incFnArgs : Fn := brnFn (fun _ => [true]) incRecFalse incRecTrue

/-- The binary successor of a bit string, least significant bit first. -/
def incFn (x : List Bool) : List Bool := incFnArgs [x]

theorem brnAux_inc (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => [true]) incRecFalse incRecTrue x v = incFn x := by
  have key : ∀ (x : List Bool) (v : Args),
      brnAux (fun _ => [true]) incRecFalse incRecTrue x v =
        brnAux (fun _ => [true]) incRecFalse incRecTrue x [] := by
    intro x
    induction x with
    | nil => intro v; rfl
    | cons b x ih =>
      intro v
      cases b <;> simp [brnAux, incRecFalse_apply, incRecTrue_apply, ih v]
  intro x
  rw [key x v, incFn, incFnArgs, brnFn]
  simp

@[simp] theorem incFn_nil : incFn [] = [true] := rfl

@[simp] theorem incFn_cons_false (x : List Bool) : incFn (false :: x) = true :: x := by
  rw [incFn, incFnArgs, brnFn]
  simp [brnAux, incRecFalse_apply]

@[simp] theorem incFn_cons_true (x : List Bool) : incFn (true :: x) = false :: incFn x := by
  rw [incFn, incFnArgs, brnFn]
  simp only [List.getD_cons_zero, brnAux, cond_true, incRecTrue_apply]
  rw [brnAux_inc]
  simp

theorem length_incFn_le (x : List Bool) : (incFn x).length ≤ x.length + 1 := by
  induction x with
  | nil => simp
  | cons b x ih =>
    cases b
    · simp
    · simp only [incFn_cons_true, List.length_cons]
      omega

theorem cobham_incFnArgs : Cobham incFnArgs := by
  refine Cobham.brn (bd := compFn (consFn false) [proj 0]) (cobham_const [true])
    cobham_incRecFalse cobham_incRecTrue (Cobham.comp (Cobham.cons false) ?_) ?_
  · intro k hk
    rw [List.mem_singleton.1 hk]
    exact Cobham.proj 0
  · intro args
    have h : brnFn (fun _ => [true]) incRecFalse incRecTrue args = incFn (args.getD 0 []) := by
      rw [brnFn, brnAux_inc]
    rw [h]
    simpa [consFn, compFn, proj] using length_incFn_le (args.getD 0 [])

/-- **The binary successor is polynomial time.** -/
theorem polyTimeFun_incFn : PolyTimeFun incFn :=
  CobhamFun.polyTimeFun ⟨incFnArgs, cobham_incFnArgs, fun _ => rfl⟩

/-- The successor on bit strings computes the successor of the number they code. -/
theorem natOfBits_incFn (x : List Bool) : natOfBits (incFn x) = natOfBits x + 1 := by
  induction x with
  | nil => simp [natOfBits_cons]
  | cons b x ih => cases b <;> simp [natOfBits_cons, ih] <;> omega

/-- The successor takes the canonical code of `n` to the canonical code of `n + 1`. -/
theorem incFn_bitsOfNat : ∀ n : ℕ, incFn (bitsOfNat n) = bitsOfNat (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | m + 1 =>
      have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
      rw [bitsOfNat_succ, show m + 1 + 1 = m + 2 from rfl, bitsOfNat_succ (m + 1)]
      by_cases h : (m + 1) % 2 = 1
      · have h2 : ¬ ((m + 2) % 2 = 1) := by omega
        have h3 : (m + 2) / 2 = (m + 1) / 2 + 1 := by omega
        simp only [h, h2, decide_true, decide_false, incFn_cons_true, h3, ih _ hlt]
      · have h2 : (m + 2) % 2 = 1 := by omega
        have h3 : (m + 2) / 2 = (m + 1) / 2 := by omega
        simp only [h, h2, decide_true, decide_false, incFn_cons_false, h3]

/-! ### The length of a word, in binary -/

/-- The step of the length recursion: apply the successor to the recursive value. -/
def lenRec : Fn := compFn incFnArgs [proj 1]

theorem lenRec_apply (args : Args) : lenRec args = incFn (args.getD 1 []) := by
  simp [lenRec, compFn, proj, incFn]

theorem cobham_lenRec : Cobham lenRec :=
  Cobham.comp cobham_incFnArgs (by
    intro k hk
    rw [List.mem_singleton.1 hk]
    exact Cobham.proj 1)

/-- The length of the first argument, in binary, before the arguments are fixed. -/
def lenFnArgs : Fn := brnFn (fun _ => []) lenRec lenRec

/-- The length of a bit string, written in binary (least significant bit first). -/
def lenFn (x : List Bool) : List Bool := lenFnArgs [x]

theorem brnAux_len (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => []) lenRec lenRec x v = lenFn x := by
  have key : ∀ (x : List Bool) (v : Args),
      brnAux (fun _ => []) lenRec lenRec x v = brnAux (fun _ => []) lenRec lenRec x [] := by
    intro x
    induction x with
    | nil => intro v; rfl
    | cons b x ih =>
      intro v
      cases b <;> simp [brnAux, lenRec_apply, ih v]
  intro x
  rw [key x v, lenFn, lenFnArgs, brnFn]
  simp

@[simp] theorem lenFn_nil : lenFn [] = [] := rfl

theorem lenFn_cons (b : Bool) (x : List Bool) : lenFn (b :: x) = incFn (lenFn x) := by
  rw [lenFn, lenFnArgs, brnFn]
  cases b <;>
    simp only [List.getD_cons_zero, brnAux, cond_true, cond_false, lenRec_apply] <;>
    rw [brnAux_len] <;> simp

/-- **The length recursion computes the binary code of the length.** -/
theorem lenFn_eq (x : List Bool) : lenFn x = bitsOfNat x.length := by
  induction x with
  | nil => simp
  | cons b x ih => rw [lenFn_cons, ih, incFn_bitsOfNat, List.length_cons]

theorem length_bitsOfNat_le : ∀ n : ℕ, (bitsOfNat n).length ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | m + 1 =>
      have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
      have hle : (m + 1) / 2 ≤ m := by omega
      rw [bitsOfNat_succ]
      have := ih _ hlt
      simp only [List.length_cons]
      omega

theorem cobham_lenFnArgs : Cobham lenFnArgs := by
  refine Cobham.brn Cobham.empty cobham_lenRec cobham_lenRec (Cobham.proj 0) ?_
  intro args
  have h : brnFn (fun _ => []) lenRec lenRec args = lenFn (args.getD 0 []) := by
    rw [brnFn, brnAux_len]
  rw [h, lenFn_eq]
  simpa [proj] using length_bitsOfNat_le (args.getD 0 []).length

/-- **The length of a word, in binary, is a polynomial-time function of the word.**  This is
what an encoding needs in order to write a numeral that depends on the input length into a
description. -/
theorem polyTimeFun_binLength : PolyTimeFun (fun w : List Bool => bitsOfNat w.length) :=
  CobhamFun.polyTimeFun ⟨lenFnArgs, cobham_lenFnArgs, fun x => (lenFn_eq x).symm⟩

end PTime

end HTN
