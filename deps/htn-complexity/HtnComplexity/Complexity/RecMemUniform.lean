import HtnComplexity.Complexity.RecMemFamily
import HtnComplexity.Complexity.AltMemUniform
/-!
# Uniform families of *recursive* alternating machines with a memory

`HtnComplexity/Complexity/AltMemUniform.lean` builds a polynomial-time hardness family out
of a uniform family of alternating machines with a memory.  Those machines consume one input bit
per step, so a *padding* of the input fixes how long they may compute, and the computation is
polynomially long in the length of the word.

This file does the same for the **recursive** encoding of
`HtnComplexity/Complexity/RecMemDom.lean`, and the difference is exactly the one §30.3 of
`NOTES.md` asks for:

* no padding is needed — the input word is encoded as it stands (`HTN.Syn.posEnc`);
* the number of steps is bounded by nothing in the description.  The machine of the family for
  the words of length `n` has `mem n` memory bits and finitely many transitions, and it may run
  for as long as it likes: the language of the family is *alternating computation in polynomial
  space*, not alternating computation in polynomial time.

The family is

    HTN.Syn.UniRecMem.family F :
      Coded.HardFamilyPT codingSer SynClass.TO_HTN_root F.L

— in `TO-HTN` with a rooted instance, that is in `TO-HTN-1`.  It is **not** claimed to be in
`TO-HTN-AC-1` or in `TO-HTN-TR-1`, and it is not: a configuration task decomposes into a
configuration task, so the hierarchy is recursive.  That is what
`HtnCompilability/Complexity/RecAdvice.lean` uses.
-/

namespace HTN

namespace Syn

open PTime

/-- **A uniform family of recursive alternating machines with a memory**: one machine per input
length, with primitive recursive components, reading no position beyond the end of the word, and
whose description is of polynomial size.  Nothing bounds the number of steps its machines
make. -/
structure UniRecMem where
  /-- The machine used for the inputs of a given length. -/
  mach : ℕ → RecAltMem
  /-- The polynomial bounding the size of the descriptions. -/
  bound : Polynomial ℕ
  /-- The machines are produced by an algorithm, uniformly in the input length. -/
  mach_primrec : RecMachFamPrimrec mach
  /-- The machine for the words of length `n` reads no position beyond the end of the word. -/
  pos_below : ∀ n, (mach n).PosBelow n
  /-- The encoding has size polynomial in the input length. -/
  dom_size : ∀ n, rmConst (mach n) ≤ bound.eval n

namespace UniRecMem

variable (F : UniRecMem)

/-- **The language of a uniform family**: the machine for the length of the word accepts it. -/
def L (w : List Bool) : Prop := (F.mach w.length).Accepts w

/-- The domain description of the family. -/
def dom (n : ℕ) : DomDesc := rmDom (F.mach n) n

theorem computable_dom : Computable F.dom := computable_rmDom_fam F.mach_primrec

theorem solvable_dom_iff (w : List Bool) : Solvable (F.dom w.length) (posEnc w) ↔ F.L w :=
  solvable_rmDom_iff (F.pos_below w.length)

/-- **The polynomial-time hardness family of a uniform family of recursive alternating machines
with a memory**, in `TO-HTN` with a rooted instance. -/
noncomputable def family : Coded.HardFamilyPT codingSer SynClass.TO_HTN_root F.L where
  dom := F.dom
  inst := posEnc
  bound := F.bound + Polynomial.X + Polynomial.C 2
  dom_size := fun n => by
    have h := size_rmDom_le (M := F.mach n) n
    have h2 := F.dom_size n
    simp only [dom, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    omega
  inst_size := fun w => by
    rw [size_posEnc]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    omega
  dom_ok := fun n => rmDom_domOk (M := F.mach n) n
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := posEnc_injective
  correct := F.solvable_dom_iff
  dom_computable := F.computable_dom
  inst_polyTime := polyTimeCode_posEnc

/-- … and hence in the unrestricted class `TO-HTN`. -/
theorem nonempty_hardFamilyPT_TO_HTN :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN F.L) :=
  ⟨F.family.mono (S' := SynClass.TO_HTN) ⟨fun _ h => h, fun _ h => h.isTO⟩⟩

end UniRecMem

end Syn

end HTN
