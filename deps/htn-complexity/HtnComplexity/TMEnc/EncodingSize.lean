import HtnPlanning.Core.SizeOn
import HtnComplexity.TMEnc.TMEncoding
import HtnComplexity.ToHtnAc.ToHtnAc
/-!
# The sizes of the two large constructions, measured on a fragment

The translation of exponential-time Turing machines (`HtnComplexity/TMEnc/TMEncoding.lean`) and
the compilation of totally ordered problems into acyclic ones
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`) both build domains whose signature is much larger than the
input, and whose method sets are given by explicit — but large — families.  Their per-method
size bounds are proved there (`HTN.TMEnc.method_size_le`, `HTN.ToAc.method_size_le`).

This file combines them with the fragment-relative size measure of
`HtnPlanning/Core/SizeOn.lean`: the size of either domain, measured on any fragment of its
signature, is bounded by the size of the fragment's signature and operators plus a *constant*
per method — `421` for the machine encoding and `931` for the HTN-AC compilation, in both cases
independently of the exponential parameter of the construction.  What is still missing for a
closed-form polynomial bound is a `Finset` presentation of the method sets themselves, i.e. a
bound on the *number* of methods of the constructions.
-/

namespace HTN

namespace TMEnc

variable {Q Γ : Type} (N : TM.NTM Q Γ) (w : List Γ) (K : ℕ)

/-- **The size of the encoded domain on a fragment**: at most `421` per method, independently
of the time bound `K`. -/
theorem sizeOn_le (fr : Fragment (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ))
    (hfr : ∀ m ∈ fr.methods, m ∈ methods N w K) :
    (domain N w K).sizeOn fr ≤ fr.facts.card + fr.tasks.card +
      (∑ a ∈ fr.ops, (domain N w K).actionSize a) + 421 * fr.methods.card :=
  Domain.sizeOn_le_of_method_size_le _ _ fun m hm => method_size_le (hfr m hm)

end TMEnc

namespace ToAc

variable {F A C : Type} {I : Type} (D : Domain F A C I) (vars : List F) (bound : ℕ)

/-- **The size of the compiled domain on a fragment**: at most `931` per method, independently
of the (exponential) number of memory cells. -/
theorem sizeOn_le (fr : Fragment (AcFact F A C) (AcAct F A C) (AcTask F A C) (ℕ × ℕ))
    (hfr : ∀ m ∈ fr.methods, m ∈ methods D vars bound) :
    (domain D vars bound).sizeOn fr ≤ fr.facts.card + fr.tasks.card +
      (∑ a ∈ fr.ops, (domain D vars bound).actionSize a) + 931 * fr.methods.card :=
  Domain.sizeOn_le_of_method_size_le _ _ fun m hm => method_size_le (hfr m hm)

end ToAc

end HTN
