import FondHtn.DB25.Hard
import FondHtn.StrongOD.Reg
/-! **CB21 Thm 5.3 + DB25 Thm 4/5**: strong OD plan existence of regular problems (CB21's
definition, `tn_I` regular) is EXPSPACE-complete. For Bercher-style regular problems it is
EXPSPACE-hard; membership is open (`doc/notes_reg_strongOD.md`). -/

namespace FOND

open HTN

theorem strongOD_REGtn_complete : Cx.Complete Cx.EXPSPACE (PlanExFM .strongOD FClass.REGtn) :=
  ⟨strongOD_REGtn_mem, strongOD_REGtn_expspaceHard⟩

end FOND
