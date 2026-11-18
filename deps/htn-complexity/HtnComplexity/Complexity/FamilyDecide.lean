import HtnComplexity.Complexity.Coding
import HtnComplexity.Hypotheses.Planning
import HtnComplexity.Computable.Decider
/-!
# Hardness families and decidable classes

A polynomial-time hardness family lifts to every larger class, and a class with a decision
procedure has one only for decidable languages.  Split out of `HTN.Complexity.CodedKarpLipton`.
-/

namespace HTN

namespace Syn

namespace Coded

open PTime Table

variable {𝒟 ℰ : Family} {S : SynClass 𝒟} {T : SynClass ℰ}

variable {L : List Bool → Prop} {Collapse : Prop} {c : BitCoding InstDesc}

/-- A hardness family in a class is one in every larger class. -/
def HardFamilyPT.mono {S' : SynClass ℰ} (F : HardFamilyPT c S L) (h : SynSub S S') :
    HardFamilyPT c S' L :=
  { F.toHardFamily.mono h with
    dom_computable := F.dom_computable
    inst_polyTime := F.inst_polyTime }

/-- **A class with a decision procedure has a polynomial-time hardness family only for
decidable languages.** -/
theorem computablePred_of_hardFamilyPT (hS : S.Decider) (F : HardFamilyPT c S L) :
    ComputablePred L := by
  obtain ⟨f, hf, hcorr⟩ := hS
  refine computablePred_of_decider
    (d := fun w => f (F.dom w.length) (F.inst w))
    (hf.comp (F.dom_computable.comp Computable.list_length) F.inst_polyTime.computable)
    fun w => ?_
  rw [hcorr _ _ (F.dom_ok w.length) (F.inst_ok w)]
  exact F.correct w

end Coded

end Syn

end HTN
