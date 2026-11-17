import FondHtn.StrongOD.Prim
import FondHtn.QBF.Hard
/-! **CB21 Thm 5.1** (repaired): strong OD plan existence of primitive (partially ordered)
problems is PSPACE-complete. Hardness is from TQBF (`FondHtn/QBF/`), not from the k-in-a-row
games of the paper, whose reduction is wrong (catalogue G9). -/

namespace FOND

open HTN

theorem strongOD_PRIM_complete : Cx.Complete Cx.PSPACE (PlanExFM .strongOD FClass.PRIM) :=
  ⟨strongOD_PRIM_mem, strongOD_PRIM_pspaceHard⟩

end FOND
