import HtnComplexity.Computable.StripsDecide
import HtnComplexity.Computable.Decider
/-!
# Plan existence is decidable for the class STRIPS: the cell hypothesis

Split out of `HTN.Computable.StripsDecide`.
-/

namespace HTN
namespace Syn

open Primrec

/-! ### The cell hypothesis -/

/-- **Plan existence is decidable for the class `STRIPS`** — the decision procedure is even
primitive recursive.  This is the hypothesis `h₂` of the cells of the row `HTN` of the
compilability table, for the target `STRIPS`. -/
theorem decider_STRIPS : SynClass.STRIPS.Decider :=
  ⟨stripsSolvableB, primrec_stripsSolvableB.to_comp,
    fun _ _ hd hq => stripsSolvableB_iff hd hq⟩

/-! ### Sanity checks

The canonical STRIPS description `stripsDom [(7, [3], [4], [])]` offers the single action `7`,
with precondition `{3}` and add list `{4}`. -/

/-- One action, with precondition `{3}`, adding `4`. -/
def exDecActs : List ActionDesc := [(7, [3], [4], [])]

example : stripsSolvableB (stripsDom exDecActs) (stripsInst [3] [4]) = true := by decide

example : stripsSolvableB (stripsDom exDecActs) (stripsInst [] [4]) = false := by decide

example : stripsSolvableB (stripsDom exDecActs) (stripsInst [3] []) = true := by decide


end Syn
end HTN
