import HtnComplexity.Complexity.Coding
import ComplexityTheory.Complexity.CobhamTable
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# A polynomial-time resource for the rooting schema

`HtnCompilability/Computable/RootedEff.lean` reduces the whole block "unrestricted source →
rooted target" to a **resource** (`HTN.Syn.Resource`): a class `Eff` of admissible instance
translations, a class `Dec` of predicates on descriptions the resource can decide, and the one
closure property

    Eff f  →  Dec (fun q => decide (profB d (f q) ∈ L))          (`dec_profB_mem`)

("translate, read the bounded profile the fixed compiled domain description sees, look the
result up in a fixed finite table").  The only instance so far was computability
(`HTN.Syn.computableResource`), at which the hardness hypotheses of
`HtnCompilability/Computable/MergePartHard.lean` are *false* — the equal-sum partition problem
is decidable.  The intended reading has always been **polynomial time**, and §22.5 of `NOTES.md`
records what stood in the way: `dec_profB_mem` at polynomial time asks for an *algorithm*,
namely that reading the profile off the code of a description and looking it up in a fixed table
is polynomial time.

This file supplies the polynomial-time resources, relative to a bit coding of descriptions
(`HTN.Syn.BitCoding`, `HtnComplexity/Complexity/Coding.lean`; the intended coding is the
serialisation `HTN.Syn.codingSer`, whose length is linear in the size of a description).  Two of
them, which bracket the missing algorithm from both sides.

## The window resource — unconditional

`HTN.Syn.WindowDec c` is the class of predicates that a *polynomial-time translation followed by
a constant-window read* decides:

    WindowDec c g  ↔  ∃ f d L, PolyTimeMap c f ∧ ∀ q, g q = decide (profB d (f q) ∈ L).

It satisfies `dec_profB_mem` by construction, so `HTN.Syn.windowResource c` is a resource with
`Eff` the genuine polynomial-time translations of Cobham's class — no hypothesis anywhere.  Its
members are computable (`HTN.Syn.WindowDec.computable`), so the class is not everything, and the
four rows of the block are refuted at it (`HTN.Merge.not_compSynEffInst_*_window`) on the
hypothesis `HTN.Merge.PartitionHardFor (windowResource c)`, which unfolds to the concrete
statement

> no polynomial-time translation of descriptions, followed by reading finitely many facts of a
> fixed domain description and a fixed table lookup, decides the equal-sum partition problem.

## The polynomial-time resource — on the readability hypothesis

`HTN.Syn.PolyTimePred c` is the honest notion: `g` is decided by a function of Cobham's class
acting on the codes.  For it, `dec_profB_mem` is exactly

    HTN.Syn.ProfileReadable c :
      ∀ d L, PolyTimePred c (fun q => decide (profB d q ∈ L))

— the missing algorithm, isolated as a single hypothesis, and `HTN.Syn.polyTimeResource c h` is
the resource it buys.  Since `WindowDec c ⊆ PolyTimePred c` under that hypothesis
(`HTN.Syn.WindowDec.polyTimePred`), hardness of the partition problem *for polynomial time* —
the classical `3-Partition ∉ P` — implies the hypothesis of the window resource
(`HTN.Merge.partitionHardFor_windowResource_of_polyTime`).  So the chain

    3-Partition ∉ P  +  profile reading is polynomial time
        ⟹  no rooting compilation with a polynomial-time instance translation

is now a theorem with exactly one algorithmic ingredient left open, and the *unconditional* form
of the refutation (the window resource) needs no such ingredient at all.

Nothing here claims that `ProfileReadable` is true; it visibly is (the profile is finitely many
membership tests and one list inclusion, all quadratic in the length of the serialisation), but
exhibiting the algorithm *inside Cobham's class* is a library of bit-string operations this
development does not yet have.
-/

namespace HTN

namespace Syn

open PTime Table

variable (c : BitCoding InstDesc)

/-! ### Predicates decided in polynomial time -/

/-- **A predicate on descriptions decided in polynomial time**, relative to the coding `c`: a
function computed in polynomial time by a Turing machine (`HTN.PTime.PolyTimeFun`, i.e. Mathlib's
`Turing.TM2ComputableInPolyTime` on bit strings) turns the code of a description into the one-bit string holding the
answer. -/
def PolyTimePred (g : InstDesc → Bool) : Prop :=
  ∃ G : List Bool → List Bool, PolyTimeFun G ∧ ∀ q, G (c.code q) = [g q]

variable {c}

/-- A predicate decided in polynomial time is computable. -/
theorem PolyTimePred.computable {g : InstDesc → Bool} (h : PolyTimePred c g) : Computable g := by
  obtain ⟨G, hG, hGg⟩ := h
  have hlist : Computable fun q => G (c.code q) := hG.computable.comp c.computable
  refine (((Primrec.list_getD false).to_comp.comp hlist (Computable.const 0)).of_eq fun q => ?_)
  rw [hGg q]
  rfl

/-- Polynomial-time decidability only depends on the predicate. -/
theorem PolyTimePred.of_eq {g g' : InstDesc → Bool} (h : PolyTimePred c g)
    (hgg : ∀ q, g' q = g q) : PolyTimePred c g' := by
  obtain ⟨G, hG, hGg⟩ := h
  exact ⟨G, hG, fun q => by rw [hGg q, hgg q]⟩

/-- Precomposing a polynomial-time predicate with a polynomial-time translation. -/
theorem PolyTimePred.compMap {g : InstDesc → Bool} {f : InstDesc → InstDesc}
    (hg : PolyTimePred c g) (hf : PolyTimeMap c f) : PolyTimePred c (fun q => g (f q)) := by
  obtain ⟨G, hG, hGg⟩ := hg
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => G (F x), hG.comp hF, fun q => ?_⟩
  show G (F (c.code q)) = _
  rw [hFf q, hGg (f q)]

/-- **Polynomial-time predicates are closed under Boolean operations.** -/
theorem PolyTimePred.comb {g h : InstDesc → Bool} (hg : PolyTimePred c g)
    (hh : PolyTimePred c h) (op : Bool → Bool → Bool) :
    PolyTimePred c (fun q => op (g q) (h q)) := by
  obtain ⟨G, hG, hGg⟩ := hg
  obtain ⟨H, hH, hHh⟩ := hh
  refine ⟨fun x => [op (([(G x).getD 0 false]).getD 0 false)
      (([(H x).getD 0 false]).getD 0 false)],
    PolyTimeFun.comb hG.firstBit hH.firstBit (fun _ => rfl) (fun _ => rfl) op, fun q => ?_⟩
  show [op ([(G (c.code q)).getD 0 false].getD 0 false)
      ([(H (c.code q)).getD 0 false].getD 0 false)] = [op (g q) (h q)]
  rw [hGg q, hHh q]
  rfl

/-- Constant predicates are decided in polynomial time, so the notion is not empty. -/
theorem polyTimePred_const (b : Bool) : PolyTimePred c (fun _ => b) :=
  ⟨fun _ => [b], CobhamFun.polyTimeFun ⟨compFn (consFn b) [fun _ => []], Cobham.comp (Cobham.cons b)
    (by intro h hh; rw [List.mem_singleton.1 hh]; exact Cobham.empty),
    fun _ => by simp [compFn, consFn]⟩, fun _ => rfl⟩

variable (c)

end Syn

end HTN
