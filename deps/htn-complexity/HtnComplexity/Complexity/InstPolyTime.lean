import ComplexityTheory.Complexity.Bits
import HtnPlanning.Computable.Syntax
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Polynomial-time instance translations, and the eight cells in that reading

`HtnCompilability/Computable/PaperKarpLipton.lean` reduces the eight cells of the paper's
table that are still open to a Karp–Lipton bundle, and shows that the argument is *empty*
unless the instance translation is required to be efficient — computability, which is all
`HTN.Syn.CompSyn` asks, is not enough, because the translation may read the answer off the
encoded instance.  Efficiency had to stay a parameter

    Eff : (InstDesc → InstDesc) → Prop

for want of a formalised notion of polynomial time.  This file supplies one and instantiates
the parameter with it.

## The notion

A problem-instance description is coded as a bit string by `HTN.Syn.instBits`: the binary
digits of its `Encodable` code (`ComplexityTheory/Complexity/Bits.lean`).  A translation of
descriptions is **polynomial time** (`HTN.Syn.PolyTimeInst`) when the induced function on bit
strings belongs to Cobham's class (`ComplexityTheory/Complexity/Cobham.lean`), the standard
machine-independent description of the polynomial-time computable functions.

What is proved about it here:

* `HTN.Syn.PolyTimeInst.computable` — a polynomial-time translation is computable.  Hence
  (`HTN.Syn.compSyn_of_compSynEff_polyTime`) a compilation in the sense of the literature is
  one in the sense of `HTN.Syn.CompSyn`, so `¬ CompSynEff PolyTimeInst` is the *weaker* of the
  two impossibility statements — it is the statement the complexity-theoretic arguments of the
  literature actually establish;
* `HTN.Syn.polyTimeInst_id`, `HTN.Syn.PolyTimeInst.comp` — the identity is polynomial time and
  polynomial time is closed under composition, so the notion behaves as an efficiency notion
  must (in particular `HTN.Syn.not_karpLiptonSyn_of_sub` applies to it, keeping the bundles
  honest for pairs of classes that do compile);
* `HTN.Syn.not_polyTimeInst_answerReader` — and this is the point of the exercise: the gadget
  translation that makes the unrestricted bundle contradictory
  (`HTN.Syn.hasAdviceDeciders_of_bitTarget`) is **not** polynomial time when the language is
  undecidable, and undecidable languages of bit strings exist
  (`HTN.Syn.exists_not_computablePred`).  The vacuity objection to the Karp–Lipton bundle
  therefore does not apply to `PolyTimeInst`: `HTN.Syn.not_karpLiptonSyn_unrestricted`, which
  refutes the bundle for `Eff = fun _ => True`, has no analogue here;
* the eight cells, in this reading, as `HTN.Syn.Paper.cellPT_<row>_to_<column>_of_karpLipton`.

What is still assumed, and why: the bundles themselves — a hardness family for the source class
together with the Karp–Lipton implication for the target class, and the non-collapse.  Those are
the complexity-theoretic results of the literature (Alford et al.'s hardness constructions and
the separations); the present file removes the *notion* of polynomial time from the list of
missing ingredients, not the results.

A caveat on the size measure.  Time is measured here in the length of the binary code of a
description, whereas the table's size bound `HTN.Syn.InstDesc.size` counts symbols.  The two are
polynomially related exactly when the numerals occurring in a description are polynomially
bounded in its symbol count, which is the case for every construction of this development but
is not forced by the definitions.
-/

namespace HTN

namespace Syn

open PTime Table

/-! ### Descriptions as bit strings -/

/-- The bit string coding a problem-instance description: the binary digits of its code. -/
def instBits (q : InstDesc) : List Bool := bitsOfNat (Encodable.encode q)

/-- The description coded by a bit string, if any; a string that codes nothing reads as a
default description. -/
def instOfBits (l : List Bool) : InstDesc :=
  (Encodable.decode (α := InstDesc) (natOfBits l)).getD default

@[simp] theorem instOfBits_instBits (q : InstDesc) : instOfBits (instBits q) = q := by
  simp [instOfBits, instBits, natOfBits_bitsOfNat]

theorem instBits_injective : Function.Injective instBits := by
  intro q q' h
  have := congrArg instOfBits h
  simpa using this

theorem computable_instBits : Computable instBits :=
  computable_bitsOfNat.comp Computable.encode

theorem computable_instOfBits : Computable instOfBits :=
  (Primrec.option_getD.to_comp.comp
    (Computable.decode.comp computable_natOfBits) (Computable.const default))

/-! ### Polynomial-time translations of descriptions -/

/-- **A polynomial-time translation of problem-instance descriptions**: one that acts on the
binary codes of descriptions as a function computed in polynomial time by a Turing machine (`HTN.PTime.PolyTimeFun`, i.e. Mathlib's
`Turing.TM2ComputableInPolyTime` on bit strings). -/
def PolyTimeInst (f : InstDesc → InstDesc) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeFun F ∧ ∀ q, F (instBits q) = instBits (f q)

/-- **A polynomial-time translation is computable.** -/
theorem PolyTimeInst.computable {f : InstDesc → InstDesc} (hf : PolyTimeInst f) :
    Computable f := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ((computable_instOfBits.comp (hF.computable.comp computable_instBits)).of_eq
    fun q => ?_)
  rw [hFf q, instOfBits_instBits]

/-- The identity translation is polynomial time. -/
theorem polyTimeInst_id : PolyTimeInst _root_.id :=
  ⟨_root_.id, polyTimeFun_id, fun _ => rfl⟩

/-- Polynomial-time translations are closed under composition. -/
theorem PolyTimeInst.comp {f g : InstDesc → InstDesc} (hf : PolyTimeInst f)
    (hg : PolyTimeInst g) : PolyTimeInst (fun q => f (g q)) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨fun x => F (G x), hF.comp hG, fun q => ?_⟩
  show F (G (instBits q)) = instBits (f (g q))
  rw [hGg q, hFf (g q)]

end Syn

end HTN
