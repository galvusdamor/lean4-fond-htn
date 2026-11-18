import HtnComplexity.Undec.Cell
import ComplexityTheory.Undec.TM.Reduce
/-!
# Plan existence for HTN descriptions is undecidable, unconditionally

`HTN.Undec.not_decider_HTN` (`HtnComplexity/Undec/Cell.lean`) is stated relative to a
two-stack machine with an undecidable halting problem.  That machine is
`HTN.Undec.undecTSM`, with `HTN.Undec.not_computablePred_undecTSM`, so the statement is
unconditional:

* `HTN.Undec.Row.not_deciderAt_htnDom` — one *fixed* finite HTN domain description for which no
  algorithm decides, given an initial state, a goal and an initial task network, whether the
  problem has a solution;
* `HTN.Undec.Row.not_decider_HTN` — plan existence is undecidable for the class `HTN`.
-/

namespace HTN

namespace Undec

namespace Row

open Syn

/-- **The fixed HTN domain description with an undecidable plan existence problem.** -/
noncomputable def htnDom : DomDesc := tsmDom undecTSM

/-- **Plan existence for the fixed domain description `htnDom` is undecidable.** -/
theorem not_deciderAt_htnDom : ¬ SynClass.HTN.DeciderAt htnDom :=
  not_deciderAt_tsmDom undecTSM not_computablePred_undecTSM

/-- **Plan existence is undecidable for the class `HTN` of descriptions.** -/
theorem not_decider_HTN : ¬ SynClass.HTN.Decider :=
  Undec.not_decider_HTN undecTSM not_computablePred_undecTSM

end Row

end Undec

end HTN
