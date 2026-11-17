import FondHtn.MP.WeakComplexity
import FondHtn.Weak.Reg
/-! Weak method-based policies for regular problems: PSPACE-complete (CB22 Prop 2 + CB21 Cor 4.5). -/

namespace FOND

theorem weakMP_REG_complete : Cx.Complete Cx.PSPACE (PlanExMP .weak FClass.REG) := by
  rw [planExMP_weak_eq]; exact weakLD_REG_complete

theorem weakMP_REG_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExMP .weak (FClass.inter FClass.REG FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_REG_TO_complete

end FOND
