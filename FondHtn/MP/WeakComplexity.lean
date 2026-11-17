import FondHtn.MP.Weak
import FondHtn.Weak.Mem
import FondHtn.Prim.WeakHard
/-!
# Complexity of weak plan existence with method-based policies ([CB22, Prop. 2])

By [CB22, Prop. 2] (`FOND.Problem.mpWeakSolvable_iff_weakLDSolvable`) the languages of weak
method-based plan existence and weak LD plan existence coincide for every class
(`FOND.planExMP_weak_eq`), so the completeness results of [CB21] for weak LD carry over:

| class | complexity | here |
| --- | --- | --- |
| PRIM, PRIM ∩ TO | NP-complete | `weakMP_PRIM_complete`, `weakMP_PRIM_TO_complete` |
| ACYC | NEXPTIME-complete | `weakMP_ACYC_complete` |
| ACYC ∩ TO, TR ∩ TO | PSPACE-complete | `weakMP_ACYC_TO_complete`, `weakMP_TR_TO_complete` |
| TR | EXPSPACE-complete | `weakMP_TR_complete` |
| TO | EXPTIME-complete | `weakMP_TO_complete` |
-/

namespace FOND

open HTN

/-- **[CB22, Prop. 2], language level**: weak method-based plan existence and weak LD plan
existence are the same language for every class. -/
theorem planExMP_weak_eq (Y : FClass) : PlanExMP .weak Y = PlanExFM .weakLD Y := by
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy,
      (Problem.mpWeakSolvable_iff_weakLDSolvable (FProbDesc.toProblem_wf hp)).1 hs⟩
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy,
      (Problem.mpWeakSolvable_iff_weakLDSolvable (FProbDesc.toProblem_wf hp)).2 hs⟩

/-! ## Memberships -/

theorem weakMP_PRIM_mem : Cx.NP (PlanExMP .weak FClass.PRIM) := by
  rw [planExMP_weak_eq]; exact weakLD_PRIM_mem

theorem weakMP_PRIM_TO_mem : Cx.NP (PlanExMP .weak (FClass.inter FClass.PRIM FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_PRIM_TO_mem

theorem weakMP_ACYC_mem : Cx.NEXPTIME (PlanExMP .weak FClass.ACYC) := by
  rw [planExMP_weak_eq]; exact weakLD_ACYC_mem

theorem weakMP_ACYC_TO_mem : Cx.PSPACE (PlanExMP .weak (FClass.inter FClass.ACYC FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_ACYC_TO_mem

theorem weakMP_TR_mem : Cx.EXPSPACE (PlanExMP .weak FClass.TR) := by
  rw [planExMP_weak_eq]; exact weakLD_TR_mem

theorem weakMP_TR_TO_mem : Cx.PSPACE (PlanExMP .weak (FClass.inter FClass.TR FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_TR_TO_mem

theorem weakMP_TO_mem : Cx.EXPTIME (PlanExMP .weak FClass.TO) := by
  rw [planExMP_weak_eq]; exact weakLD_TO_mem

/-! ## Completeness -/

/-- Weak MP plan existence of primitive problems is NP-complete. -/
theorem weakMP_PRIM_complete : Cx.Complete Cx.NP (PlanExMP .weak FClass.PRIM) := by
  rw [planExMP_weak_eq]; exact weakLD_PRIM_complete

/-- Weak MP plan existence of primitive totally ordered problems is NP-complete. -/
theorem weakMP_PRIM_TO_complete :
    Cx.Complete Cx.NP (PlanExMP .weak (FClass.inter FClass.PRIM FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_PRIM_TO_complete

/-- Weak MP plan existence of acyclic problems is NEXPTIME-complete. -/
theorem weakMP_ACYC_complete : Cx.Complete Cx.NEXPTIME (PlanExMP .weak FClass.ACYC) := by
  rw [planExMP_weak_eq]; exact weakLD_ACYC_complete

/-- Weak MP plan existence of acyclic totally ordered problems is PSPACE-complete. -/
theorem weakMP_ACYC_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExMP .weak (FClass.inter FClass.ACYC FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_ACYC_TO_complete

/-- Weak MP plan existence of tail-recursive problems is EXPSPACE-complete. -/
theorem weakMP_TR_complete : Cx.Complete Cx.EXPSPACE (PlanExMP .weak FClass.TR) := by
  rw [planExMP_weak_eq]; exact weakLD_TR_complete

/-- Weak MP plan existence of tail-recursive totally ordered problems is PSPACE-complete. -/
theorem weakMP_TR_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExMP .weak (FClass.inter FClass.TR FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_TR_TO_complete

/-- Weak MP plan existence of totally ordered problems is EXPTIME-complete. -/
theorem weakMP_TO_complete : Cx.Complete Cx.EXPTIME (PlanExMP .weak FClass.TO) := by
  rw [planExMP_weak_eq]; exact weakLD_TO_complete

end FOND
