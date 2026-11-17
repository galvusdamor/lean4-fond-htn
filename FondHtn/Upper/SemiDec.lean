import FondHtn.Weak.Mem
import FondHtn.MP.WeakComplexity
import HtnComplexity.Article.SemiDec
/-!
# Semi-decidability ([CB21, Thm. 3.1], partly)

Semi-decidability is closed under computable many-one reductions; weak LD and strong LD plan
existence reduce (in polynomial time, hence computably) to deterministic plan existence, which is
semi-decidable (`HTN.Article.thm_4_1_4`).  Weak OD and weak method-based plan existence are the
same languages as weak LD.  Strong OD plan existence of partially ordered problems is not covered
here.
-/

namespace FOND

open HTN HTN.Article

theorem semiDecidable_of_redC {L L' : Cx.Language} (h : Cx.RedC L L') (h' : Cx.SemiDecidable L') :
    Cx.SemiDecidable L := by
  obtain ⟨f, hf, hff⟩ := h
  have : Partrec fun a => Part.assert (L' (f a)) fun _ => Part.some () :=
    (h'.comp hf : Partrec fun a => Part.assert (L' (f a)) fun _ => Part.some ())
  exact (REPred.of_eq this fun a => (hff a).symm)

theorem weakLD_semiDecidable : Cx.SemiDecidable (PlanExFM .weakLD FClass.UNRES) :=
  semiDecidable_of_redC (redP_weakLD wMatches_UNRES).redC thm_4_1_4

theorem strongLD_semiDecidable : Cx.SemiDecidable (PlanExFM .strongLD FClass.UNRES) :=
  semiDecidable_of_redC (redP_strongLD sMatches_UNRES).redC thm_4_1_4

theorem weakOD_semiDecidable : Cx.SemiDecidable (PlanExFM .weakOD FClass.UNRES) := by
  rw [planExFM_weakOD_eq]; exact weakLD_semiDecidable

theorem weakMP_semiDecidable : Cx.SemiDecidable (PlanExMP .weak FClass.UNRES) := by
  rw [planExMP_weak_eq]; exact weakLD_semiDecidable

/-- **[CB21, Thm. 3.1]** for weak and strong LD, weak OD: semi-decidable but undecidable. -/
theorem thm_3_1 :
    (Cx.SemiDecidable (PlanExFM .weakLD FClass.UNRES) ∧ ¬ Cx.Decidable (PlanExFM .weakLD FClass.UNRES)) ∧
    (Cx.SemiDecidable (PlanExFM .strongLD FClass.UNRES) ∧ ¬ Cx.Decidable (PlanExFM .strongLD FClass.UNRES)) ∧
    (Cx.SemiDecidable (PlanExFM .weakOD FClass.UNRES) ∧ ¬ Cx.Decidable (PlanExFM .weakOD FClass.UNRES)) :=
  ⟨⟨weakLD_semiDecidable, undecidable_fm .weakLD⟩, ⟨strongLD_semiDecidable, undecidable_fm .strongLD⟩,
    ⟨weakOD_semiDecidable, undecidable_fm .weakOD⟩⟩

end FOND
