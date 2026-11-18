import ComplexityTheory.Complexity.CobhamExamples
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# A block code belongs to Cobham's class

The concrete polynomial-time encodings of this development all have the same shape: each bit of
the input word is replaced by a fixed block of bits, and a fixed string is appended at the end.
This file proves that every function of that shape belongs to Cobham's class:

    HTN.PTime.polyTimeFun_blockMap :
      PolyTimeFun fun w => (w.flatMap fun b => bif b then A else B) ++ C

The proof follows the pattern of `HTN.PTime.cobham_append`: a bounded recursion on notation
whose step prefixes the recursive value with a constant block, bounded by the smash of the
input with a constant string of the length of the longer block.  It is the first function of
the class here that is *used* rather than exhibited, namely in
`HtnComplexity/Complexity/GuardFamily.lean`, where it computes the serialisation of the
instance description coding a word.
-/

namespace HTN

namespace PTime

variable (A B : List Bool)

/-- Prefixing the recursive value of a recursion on notation with a fixed block. -/
def blockRec (A : List Bool) : Fn :=
  compFn (fun args => args.getD 0 [] ++ args.getD 1 []) [fun _ => A, proj 1]

theorem blockRec_apply (args : Args) : blockRec A args = A ++ args.getD 1 [] := by
  simp [blockRec, compFn, proj]

theorem cobham_blockRec : Cobham (blockRec A) := by
  refine Cobham.comp cobham_append ?_
  intro h hh
  rcases List.mem_cons.1 hh with rfl | hh
  · exact cobham_const A
  · rw [List.mem_singleton.1 hh]
    exact Cobham.proj 1

/-- The bound for the block code: the smash of the input (lengthened by one bit) with a constant
string of the length of the longer block, concatenated with the second argument. -/
def blockBound (A B : List Bool) : Fn :=
  compFn (fun args => args.getD 0 [] ++ args.getD 1 [])
    [compFn smashFn [compFn (consFn false) [proj 0],
      fun _ => List.replicate (max A.length B.length) false], proj 1]

theorem length_blockBound (args : Args) :
    (blockBound A B args).length =
      ((args.getD 0 []).length + 1) * max A.length B.length + (args.getD 1 []).length := by
  simp [blockBound, compFn, smashFn, consFn, proj]

theorem cobham_blockBound : Cobham (blockBound A B) := by
  refine Cobham.comp cobham_append ?_
  intro h hh
  rcases List.mem_cons.1 hh with rfl | hh
  · refine Cobham.comp Cobham.smash ?_
    intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Cobham.comp (Cobham.cons false) (by
        intro j hj
        rw [List.mem_singleton.1 hj]
        exact Cobham.proj 0)
    · rw [List.mem_singleton.1 hk]
      exact cobham_const _
  · rw [List.mem_singleton.1 hh]
    exact Cobham.proj 1

/-- The block code, before the arguments are fixed. -/
def blockFn (A B : List Bool) : Fn := brnFn (proj 0) (blockRec B) (blockRec A)

theorem brnAux_block (v : Args) : ∀ x : List Bool,
    brnAux (proj 0) (blockRec B) (blockRec A) x v =
      (x.flatMap fun b => bif b then A else B) ++ v.getD 0 [] := by
  intro x
  induction x with
  | nil => simp [brnAux, proj]
  | cons b x ih =>
    cases b <;> simp [brnAux, blockRec_apply, ih, List.flatMap_cons]

theorem blockFn_apply (args : Args) :
    blockFn A B args =
      ((args.getD 0 []).flatMap fun b => bif b then A else B) ++ args.getD 1 [] := by
  rw [blockFn, brnFn, brnAux_block]
  cases args with
  | nil => simp
  | cons x xs => simp

theorem length_blockFn_le (args : Args) :
    (blockFn A B args).length ≤ (blockBound A B args).length := by
  rw [blockFn_apply, length_blockBound, List.length_append]
  have hflat : ∀ x : List Bool,
      (x.flatMap fun b => bif b then A else B).length ≤ x.length * max A.length B.length := by
    intro x
    induction x with
    | nil => simp
    | cons b x ih =>
      have hb : ((bif b then A else B) : List Bool).length ≤ max A.length B.length := by
        cases b <;> simp
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      calc ((bif b then A else B) : List Bool).length +
            (x.flatMap fun b => bif b then A else B).length
          ≤ max A.length B.length + x.length * max A.length B.length := by omega
        _ = (x.length + 1) * max A.length B.length := by ring
  have := hflat (args.getD 0 [])
  have hmono : (args.getD 0 []).length * max A.length B.length ≤
      ((args.getD 0 []).length + 1) * max A.length B.length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The block code belongs to Cobham's class.** -/
theorem cobham_blockFn : Cobham (blockFn A B) :=
  Cobham.brn (Cobham.proj 0) (cobham_blockRec B) (cobham_blockRec A) (cobham_blockBound A B)
    (length_blockFn_le A B)

/-- **Replacing every bit of a word by a fixed block and appending a fixed string is polynomial
time.** -/
theorem polyTimeFun_blockMap (A B C : List Bool) :
    PolyTimeFun (fun w : List Bool => (w.flatMap fun b => bif b then A else B) ++ C) := by
  refine CobhamFun.polyTimeFun ⟨compFn (blockFn A B) [proj 0, fun _ => C], Cobham.comp (cobham_blockFn A B) ?_,
    fun w => ?_⟩
  · intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Cobham.proj 0
    · rw [List.mem_singleton.1 hk]
      exact cobham_const C
  · simp [compFn, blockFn_apply, proj]

end PTime

end HTN
