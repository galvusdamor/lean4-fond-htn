import FondHtn.Upper.StrongDesc
/-!
# Strong LD (and TO strong OD) plan existence: memberships and completeness
([CB21, Thm. 4.7, Cor. 4.8])

Strong LD plan existence of a FOND class reduces to deterministic plan existence of the same class
(`FOND.redP_strongLD`), so every deterministic upper bound of the library transfers along the
closure of the complexity classes under `≤ₚ`.  With the inherited lower bounds
(`FondHtn/Hardness/FromDet.lean`) we obtain completeness.  For totally ordered problems strong
OD and strong LD solvability coincide ([CB21, Prop. 2.15], `FOND.planExFM_strongOD_TO`).

Class filters (`FOND.redP_filter`, `FOND.redP_filterFM`) drop a restriction that is decidable in
polynomial time (total order of `tn_I` or of the whole problem), to move between e.g. `REG ∩ TO`
and `REG`.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-! ## Class filters -/

theorem planEx_congr {Y Z : PClass} (h : ∀ P, Y P ↔ Z P) : PlanEx Y = PlanEx Z := by
  have : Y = Z := funext fun P => propext (h P)
  rw [this]

theorem planExFM_congr {c : FMCrit} {Y Z : FClass} (h : ∀ P, Y P ↔ Z P) :
    PlanExFM c Y = PlanExFM c Z := by
  have : Y = Z := funext fun P => propext (h P)
  rw [this]

/-- Dropping a restriction decided in polynomial time (deterministic descriptions). -/
theorem redP_filter {Y Z : PClass} {b : ProbDesc → Bool} (hb : PT b)
    (hbZ : ∀ p : ProbDesc, p.Valid → (b p = true ↔ Z p.toProblem)) :
    Cx.RedP (PlanEx fun P => Y P ∧ Z P) (PlanEx Y) := by
  refine redP_codeLang (f := fun p => bif b p then p else badPDesc)
    (PT.cond hb PT.id (PT.const badPDesc)) (fun p => ?_) badPDesc
    (fun h => badPDesc_not_valid h.1)
  by_cases hp : p.Valid
  · by_cases hz : b p = true
    · simp only [hz, cond_true]
      exact ⟨fun ⟨hv, ⟨hy, _⟩, hs⟩ => ⟨hv, hy, hs⟩,
        fun ⟨hv, hy, hs⟩ => ⟨hv, ⟨hy, (hbZ p hp).1 hz⟩, hs⟩⟩
    · simp only [Bool.not_eq_true] at hz
      simp only [hz, cond_false]
      exact ⟨fun ⟨_, ⟨_, hz'⟩, _⟩ => absurd ((hbZ p hp).2 hz') (by simp [hz]),
        fun h => absurd h.1 badPDesc_not_valid⟩
  · cases hz : b p
    · simp only [hz, cond_false]
      exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badPDesc_not_valid⟩
    · simp only [hz, cond_true]
      exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 hp⟩

/-- Dropping a restriction decided in polynomial time (FOND descriptions). -/
theorem redP_filterFM {c : FMCrit} {Y Z : FClass} {b : FProbDesc → Bool} (hb : PT b)
    (hbZ : ∀ p : FProbDesc, p.Valid → (b p = true ↔ Z p.toProblem)) :
    Cx.RedP (PlanExFM c (FClass.inter Y Z)) (PlanExFM c Y) := by
  refine redP_codeLang (f := fun p => bif b p then p else badDesc)
    (PT.cond hb PT.id (PT.const badDesc)) (fun p => ?_) badDesc
    (fun h => badDesc_not_valid h.1)
  by_cases hp : p.Valid
  · by_cases hz : b p = true
    · simp only [hz, cond_true]
      exact ⟨fun ⟨hv, ⟨hy, _⟩, hs⟩ => ⟨hv, hy, hs⟩,
        fun ⟨hv, hy, hs⟩ => ⟨hv, ⟨hy, (hbZ p hp).1 hz⟩, hs⟩⟩
    · simp only [Bool.not_eq_true] at hz
      simp only [hz, cond_false]
      exact ⟨fun ⟨_, ⟨_, hz'⟩, _⟩ => absurd ((hbZ p hp).2 hz') (by simp [hz]),
        fun h => absurd h.1 badDesc_not_valid⟩
  · cases hz : b p
    · simp only [hz, cond_false]
      exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badDesc_not_valid⟩
    · simp only [hz, cond_true]
      exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 hp⟩

theorem pt_classTOB : PT classTOB :=
  (PT.and (pt_toB.comp (PT.fst.comp (PT.snd.comp PT.snd)))
    (pt_methodsRB pt_toB PT.id pt_reachSetB)).of_eq fun _ => rfl

/-- Total order of `tn_I` of a FOND description, decided in polynomial time. -/
def fToB (p : FProbDesc) : Bool := toB p.tnI

theorem pt_fToB : PT fToB := pt_toB.comp (PT.snd.comp PT.snd)

theorem fToB_iff {p : FProbDesc} (hp : p.Valid) : fToB p = true ↔ FClass.TOtn p.toProblem :=
  toB_iff hp.tnI

/-- Total order of a FOND description, decided in polynomial time. -/
def fTOB (p : FProbDesc) : Bool := classTOB (strongDesc p)

theorem pt_fTOB : PT fTOB := pt_classTOB.comp pt_strongDesc

theorem fTOB_iff {p : FProbDesc} (hp : p.Valid) : fTOB p = true ↔ FClass.TO p.toProblem :=
  (classTOB_iff (strongDesc_valid hp)).trans (sMatches_TO p hp).symm

/-! ## Memberships: strong LD -/

theorem strongLD_PRIM_mem : Cx.NP (PlanExFM .strongLD FClass.PRIM) :=
  Cx.NP.of_redP (redP_strongLD sMatches_PRIM) cor_4_2_9

theorem strongLD_REG_ACYC_TO_mem :
    Cx.NP (PlanExFM .strongLD (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO))) := by
  refine Cx.NP.of_redP (redP_strongLD (sMatches_REG.inter (sMatches_ACYC.inter sMatches_TO))) ?_
  rw [planEx_congr (Z := fun P => P.IsACYC ∧ P.IsREG ∧ P.IsTO) (fun P => by tauto)]
  exact lem_4_2_11_TO

theorem strongLD_ACYC_mem : Cx.NEXPTIME (PlanExFM .strongLD FClass.ACYC) :=
  Cx.NEXPTIME.of_redP (redP_strongLD sMatches_ACYC) thm_4_2_5

theorem strongLD_ACYC_TO_mem : Cx.PSPACE (PlanExFM .strongLD (FClass.inter FClass.ACYC FClass.TO)) :=
  Cx.PSPACE.of_redP (redP_strongLD (sMatches_ACYC.inter sMatches_TO)) cor_4_2_20_acyc

theorem strongLD_REG_mem : Cx.PSPACE (PlanExFM .strongLD FClass.REG) :=
  Cx.PSPACE.of_redP (redP_strongLD sMatches_REG) cor_4_2_18

theorem strongLD_REG_TO_mem : Cx.PSPACE (PlanExFM .strongLD (FClass.inter FClass.REG FClass.TO)) :=
  Cx.PSPACE.of_redP (redP_filterFM pt_fTOB fun _ hp => fTOB_iff hp) strongLD_REG_mem

theorem strongLD_TR_mem : Cx.EXPSPACE (PlanExFM .strongLD FClass.TR) :=
  Cx.EXPSPACE.of_redP (redP_strongLD sMatches_TR) cor_4_2_16

theorem strongLD_TR_TO_mem : Cx.PSPACE (PlanExFM .strongLD (FClass.inter FClass.TR FClass.TO)) :=
  Cx.PSPACE.of_redP (redP_strongLD (sMatches_TR.inter sMatches_TO)) cor_4_2_20

theorem strongLD_TO_mem : Cx.EXPTIME (PlanExFM .strongLD FClass.TO) :=
  Cx.EXPTIME.of_redP (redP_strongLD sMatches_TO) thm_4_2_1

/-! ## Completeness: strong LD [CB21, Thm. 4.7] -/

/-- Primitive problems: strong LD is NP-complete. -/
theorem strongLD_PRIM_complete : Cx.Complete Cx.NP (PlanExFM .strongLD FClass.PRIM) :=
  ⟨strongLD_PRIM_mem, (hard_PRIM_fm .strongLD)⟩

theorem strongLD_REG_ACYC_TO_complete : Cx.Complete Cx.NP
    (PlanExFM .strongLD (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO))) :=
  ⟨strongLD_REG_ACYC_TO_mem, (hard_REG_ACYC_TO_fm .strongLD)⟩

theorem strongLD_ACYC_TOtn_complete :
    Cx.Complete Cx.NEXPTIME (PlanExFM .strongLD (FClass.inter FClass.ACYC FClass.TOtn)) :=
  ⟨Cx.NEXPTIME.of_redP (redP_filterFM pt_fToB fun _ hp => fToB_iff hp) strongLD_ACYC_mem,
    (hard_ACYC_fm .strongLD)⟩

/-- Acyclic problems: strong LD is NEXPTIME-complete. -/
theorem strongLD_ACYC_complete : Cx.Complete Cx.NEXPTIME (PlanExFM .strongLD FClass.ACYC) :=
  ⟨strongLD_ACYC_mem, (hard_ACYC_fm .strongLD).of_redP (redP_filterFM pt_fToB fun _ hp => fToB_iff hp)⟩

theorem strongLD_ACYC_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .strongLD (FClass.inter FClass.ACYC FClass.TO)) :=
  ⟨strongLD_ACYC_TO_mem, (hard_ACYC_TO_fm .strongLD)⟩

/-- Regular problems: strong LD is PSPACE-complete. -/
theorem strongLD_REG_complete : Cx.Complete Cx.PSPACE (PlanExFM .strongLD FClass.REG) :=
  ⟨strongLD_REG_mem, (hard_REG_TO_fm .strongLD).of_redP (redP_filterFM pt_fTOB fun _ hp => fTOB_iff hp)⟩

theorem strongLD_REG_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .strongLD (FClass.inter FClass.REG FClass.TO)) :=
  ⟨strongLD_REG_TO_mem, (hard_REG_TO_fm .strongLD)⟩

/-- Tail-recursive problems: strong LD is EXPSPACE-complete. -/
theorem strongLD_TR_complete : Cx.Complete Cx.EXPSPACE (PlanExFM .strongLD FClass.TR) :=
  ⟨strongLD_TR_mem, (hard_TR_fm .strongLD).of_redP (redP_filterFM pt_fToB fun _ hp => fToB_iff hp)⟩

theorem strongLD_TR_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .strongLD (FClass.inter FClass.TR FClass.TO)) :=
  ⟨strongLD_TR_TO_mem, (hard_TR_TO_fm .strongLD)⟩

/-- Totally ordered problems: strong LD is EXPTIME-complete. -/
theorem strongLD_TO_complete : Cx.Complete Cx.EXPTIME (PlanExFM .strongLD FClass.TO) :=
  ⟨strongLD_TO_mem, (hard_TO_fm .strongLD)⟩

/-! ## Completeness: strong OD for totally ordered problems [CB21, Cor. 4.8] -/

theorem strongOD_eq_strongLD {Y : FClass} :
    PlanExFM .strongOD (FClass.inter Y FClass.TO) = PlanExFM .strongLD (FClass.inter Y FClass.TO) :=
  planExFM_strongOD_TO fun _ h => h.2

theorem strongOD_REG_ACYC_TO_complete : Cx.Complete Cx.NP
    (PlanExFM .strongOD (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO))) := by
  have : PlanExFM .strongOD (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO)) =
      PlanExFM .strongLD (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO)) :=
    planExFM_strongOD_TO fun _ h => h.2.2
  rw [this]; exact strongLD_REG_ACYC_TO_complete

theorem strongOD_ACYC_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .strongOD (FClass.inter FClass.ACYC FClass.TO)) := by
  rw [strongOD_eq_strongLD]; exact strongLD_ACYC_TO_complete

theorem strongOD_REG_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .strongOD (FClass.inter FClass.REG FClass.TO)) := by
  rw [strongOD_eq_strongLD]; exact strongLD_REG_TO_complete

theorem strongOD_TR_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .strongOD (FClass.inter FClass.TR FClass.TO)) := by
  rw [strongOD_eq_strongLD]; exact strongLD_TR_TO_complete

theorem strongOD_TO_complete : Cx.Complete Cx.EXPTIME (PlanExFM .strongOD FClass.TO) := by
  rw [planExFM_strongOD_TO fun _ h => h]; exact strongLD_TO_complete

end FOND
