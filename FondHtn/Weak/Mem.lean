import FondHtn.Weak.Classes
import FondHtn.Upper.StrongMem
import FondHtn.Prim.WeakMem
/-!
# Weak plan existence: memberships and completeness ([CB21, Thm. 4.4])

Weak LD plan existence of an acyclic, tail-recursive or totally ordered class reduces to
deterministic plan existence of the same class (`FOND.redP_weakLD`, by the weak compilation), so
it has the same complexity as deterministic HTN planning; weak OD is the same language
([CB21, Prop. 2.12], `FOND.planExFM_weakOD_eq`).  Regular problems are not covered: the
compilation does not preserve regularity ([CB21, Cor. 4.5] needs a different argument).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-- The FOND class `Y'` and the deterministic class `Y` agree on weak translations. -/
def WMatches (Y' : FClass) (Y : PClass) : Prop :=
  ∀ p : FProbDesc, p.Valid → (Y' p.toProblem ↔ Y (weakDesc p).toProblem)

theorem WMatches.inter {Y' Z' : FClass} {Y Z : PClass} (h₁ : WMatches Y' Y) (h₂ : WMatches Z' Z) :
    WMatches (FClass.inter Y' Z') (fun P => Y P ∧ Z P) :=
  fun p hp => and_congr (h₁ p hp) (h₂ p hp)

theorem wMatches_ACYC : WMatches FClass.ACYC (fun P => P.IsACYC) :=
  fun _ hp => (weak_isACYC_iff hp).symm
theorem wMatches_TR : WMatches FClass.TR (fun P => P.IsTailREC) :=
  fun _ hp => (weak_isTailREC_iff hp).symm
theorem wMatches_TO : WMatches FClass.TO (fun P => P.IsTO) :=
  fun _ hp => (weak_isTO_iff hp).symm
theorem wMatches_UNRES : WMatches FClass.UNRES UNRES := fun _ _ => Iff.rfl

/-- The reduction. -/
def weakRed (p : FProbDesc) : ProbDesc := if p.Valid then weakDesc p else badPDesc

theorem pt_weakRed : PT weakRed := by
  refine (PT.cond FProbDesc.pt_validB pt_weakDesc (PT.const badPDesc)).of_eq fun p => ?_
  simp only [weakRed]
  by_cases hp : p.Valid
  · rw [if_pos hp, (FProbDesc.validB_iff p).2 hp]; rfl
  · rw [if_neg hp]
    have : p.validB = false := by
      cases h : p.validB
      · rfl
      · exact absurd ((FProbDesc.validB_iff p).1 h) hp
    rw [this]; rfl

/-- **Weak LD plan existence reduces to deterministic plan existence** (class by class). -/
theorem redP_weakLD {Y' : FClass} {Y : PClass} (hY : WMatches Y' Y) :
    Cx.RedP (PlanExFM .weakLD Y') (PlanEx Y) := by
  refine redP_codeLang pt_weakRed (fun p => ?_) badPDesc (fun h => badPDesc_not_valid h.1)
  by_cases hp : p.Valid
  · simp only [weakRed, if_pos hp]
    exact ⟨fun ⟨_, hy, hs⟩ => ⟨weakDesc_valid hp, (hY p hp).1 hy, (weakLD_iff_weakDesc hp).1 hs⟩,
      fun ⟨_, hy, hs⟩ => ⟨hp, (hY p hp).2 hy, (weakLD_iff_weakDesc hp).2 hs⟩⟩
  · simp only [weakRed, if_neg hp]
    exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badPDesc_not_valid⟩

/-! ## Memberships -/

theorem weakLD_ACYC_mem : Cx.NEXPTIME (PlanExFM .weakLD FClass.ACYC) :=
  Cx.NEXPTIME.of_redP (redP_weakLD wMatches_ACYC) thm_4_2_5

theorem weakLD_ACYC_TO_mem : Cx.PSPACE (PlanExFM .weakLD (FClass.inter FClass.ACYC FClass.TO)) :=
  Cx.PSPACE.of_redP (redP_weakLD (wMatches_ACYC.inter wMatches_TO)) cor_4_2_20_acyc

theorem weakLD_TR_mem : Cx.EXPSPACE (PlanExFM .weakLD FClass.TR) :=
  Cx.EXPSPACE.of_redP (redP_weakLD wMatches_TR) cor_4_2_16

theorem weakLD_TR_TO_mem : Cx.PSPACE (PlanExFM .weakLD (FClass.inter FClass.TR FClass.TO)) :=
  Cx.PSPACE.of_redP (redP_weakLD (wMatches_TR.inter wMatches_TO)) cor_4_2_20

theorem weakLD_TO_mem : Cx.EXPTIME (PlanExFM .weakLD FClass.TO) :=
  Cx.EXPTIME.of_redP (redP_weakLD wMatches_TO) thm_4_2_1

/-! ## Completeness [CB21, Thm. 4.4] -/

theorem weakLD_ACYC_complete : Cx.Complete Cx.NEXPTIME (PlanExFM .weakLD FClass.ACYC) :=
  ⟨weakLD_ACYC_mem,
    (hard_ACYC_fm .weakLD).of_redP (redP_filterFM pt_fToB fun _ hp => fToB_iff hp)⟩

theorem weakLD_ACYC_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakLD (FClass.inter FClass.ACYC FClass.TO)) :=
  ⟨weakLD_ACYC_TO_mem, hard_ACYC_TO_fm .weakLD⟩

theorem weakLD_TR_complete : Cx.Complete Cx.EXPSPACE (PlanExFM .weakLD FClass.TR) :=
  ⟨weakLD_TR_mem, (hard_TR_fm .weakLD).of_redP (redP_filterFM pt_fToB fun _ hp => fToB_iff hp)⟩

theorem weakLD_TR_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakLD (FClass.inter FClass.TR FClass.TO)) :=
  ⟨weakLD_TR_TO_mem, hard_TR_TO_fm .weakLD⟩

theorem weakLD_TO_complete : Cx.Complete Cx.EXPTIME (PlanExFM .weakLD FClass.TO) :=
  ⟨weakLD_TO_mem, hard_TO_fm .weakLD⟩

theorem weakOD_ACYC_complete : Cx.Complete Cx.NEXPTIME (PlanExFM .weakOD FClass.ACYC) := by
  rw [planExFM_weakOD_eq]; exact weakLD_ACYC_complete

theorem weakOD_ACYC_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakOD (FClass.inter FClass.ACYC FClass.TO)) := by
  rw [planExFM_weakOD_eq]; exact weakLD_ACYC_TO_complete

theorem weakOD_TR_complete : Cx.Complete Cx.EXPSPACE (PlanExFM .weakOD FClass.TR) := by
  rw [planExFM_weakOD_eq]; exact weakLD_TR_complete

theorem weakOD_TR_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakOD (FClass.inter FClass.TR FClass.TO)) := by
  rw [planExFM_weakOD_eq]; exact weakLD_TR_TO_complete

theorem weakOD_TO_complete : Cx.Complete Cx.EXPTIME (PlanExFM .weakOD FClass.TO) := by
  rw [planExFM_weakOD_eq]; exact weakLD_TO_complete

end FOND
