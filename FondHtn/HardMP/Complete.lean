import FondHtn.HardMP.Final
import FondHtn.MPStrong.Mem
import FondHtn.MPStrong.CyclicAcyc
/-! **CB22 Thms 1, 3, 4 (strong policies): EXPTIME-completeness.** Membership by the progression
AND-OR game (`FondHtn/MPStrong/`), hardness by the new reduction from totally ordered HTN
planning (`FondHtn/HardMP/`). For acyclic classes the fair strong cyclic reading coincides with
strong solutions, so Thm 1 also holds for it. -/

namespace FOND

open HTN

theorem strongMP_ACYC_TO_complete :
    Cx.Complete Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.ACYC FClass.TO)) :=
  ⟨strongMP_ACYC_TO_mem, hard_ACYC_TO_mpStrong⟩

theorem strongMP_TR_TO_complete :
    Cx.Complete Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.TR FClass.TO)) :=
  ⟨strongMP_TR_TO_mem, hard_TR_TO_mpStrong⟩

theorem strongMP_REG_complete : Cx.Complete Cx.EXPTIME (PlanExMP .strong FClass.REG) :=
  ⟨strongMP_REG_mem, hard_REG_mpStrong⟩

theorem strongMP_REG_TO_complete :
    Cx.Complete Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.REG FClass.TO)) :=
  ⟨strongMP_REG_TO_mem, hard_REG_TO_mpStrong⟩

theorem fairMP_ACYC_TO_complete :
    Cx.Complete Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.ACYC FClass.TO)) := by
  rw [planExMPFair_eq_strong fun _ h => h.1]; exact strongMP_ACYC_TO_complete

end FOND
