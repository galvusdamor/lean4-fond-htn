import ComplexityTheory.Complexity.Basic
import HtnComplexity.Complexity.Serial
/-!
# Bit-string codings of descriptions, and polynomial time on descriptions

**Definitions only.**  A coding `HTN.Syn.BitCoding` of descriptions as bit strings (injective and
computable), the serialisation `HTN.Syn.codingSer` as one, and polynomial time relative to a
coding: `HTN.Syn.PolyTimeMap` (translations of instance descriptions) and `HTN.Syn.PolyTimeCode`
(encodings of words as instance descriptions).
-/

/-! ## Bit-string codings and polynomial-time translations -/

namespace HTN

namespace Syn

open PTime

/-- **A coding of descriptions as bit strings**: injective, and computable.  These are the two
properties the compilability argument uses; the notion of polynomial time on descriptions is
defined relative to such a coding. -/
structure BitCoding (α : Type) [Primcodable α] where
  /-- The bit string coding an object. -/
  code : α → List Bool
  /-- Distinct objects have distinct codes. -/
  injective : Function.Injective code
  /-- The coding is computable. -/
  computable : Computable code

/-- The serialisation of `HtnComplexity/Complexity/Serial.lean`, as a coding. -/
def codingSer : BitCoding InstDesc :=
  ⟨instSer, instSer_injective, computable_instSer⟩

variable (c : BitCoding InstDesc)

/-- **A polynomial-time translation of descriptions, relative to a coding**: one that acts on
the codes as a function computed in polynomial time by a Turing machine (`HTN.PTime.PolyTimeFun`, i.e. Mathlib's
`Turing.TM2ComputableInPolyTime` on bit strings).  Equivalently
(`HTN.Syn.polyTimeMap_iff_tm2`), `f` is `Turing.TM2ComputableInPolyTime` with respect to the
encoding `c.finEncoding` of descriptions on both sides. -/
def PolyTimeMap (f : InstDesc → InstDesc) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeFun F ∧ ∀ q, F (c.code q) = c.code (f q)

/-- **A polynomial-time encoding of words as descriptions, relative to a coding**: the code of
the description is computed in polynomial time by a Turing machine (`HTN.PTime.PolyTimeFun`, i.e. Mathlib's
`Turing.TM2ComputableInPolyTime` on bit strings) of the word (`HTN.Syn.polyTimeCode_iff_tm2`). -/
def PolyTimeCode (enc : List Bool → InstDesc) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeFun F ∧ ∀ w, F w = c.code (enc w)

end Syn

end HTN

