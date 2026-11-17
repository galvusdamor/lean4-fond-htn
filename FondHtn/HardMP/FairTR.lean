import FondHtn.HardMP.Complete
import FondHtn.MPStrong.CyclicDesc
/-!
# Fair strong cyclic method-based policies: tail-recursive totally ordered problems

The acyclic instances `FOND.HardMP.descA` of the reduction from totally ordered HTN planning are
also tail-recursive; for acyclic problems the fair strong cyclic reading coincides with strong
solutions (`FOND.MPS.fair_iff_strong_ACYC`), so the reduction also shows EXPTIME-hardness of
`PlanExMPFair (TR ∩ TO)` ([CB22, Thm. 4], strong cyclic column, fair reading).
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn HTN.Syn.PolyDom PTime

/-- The reduction from totally ordered HTN planning, for the fair reading. -/
theorem redP_TO_fair {d : ProbDesc → FProbDesc} (hd : PT d) {Y : FClass}
    (hv : ∀ p, (d p).Valid) (hY : ∀ p, Y (d p).toProblem)
    (hs : ∀ p, p.Valid → p.toProblem.IsTO →
      ((d p).toProblem.MPStrongCyclicFairSolvable ↔ p.toProblem.Solvable)) :
    Cx.RedP (PlanEx fun P => P.IsTO) (PlanExMPFair Y) := by
  refine redP_codeLang (pt_redTO hd) (fun p => ?_) badDesc (fun h => badDesc_not_valid h.1)
  cases hb : (validB p && classTOB p)
  · have hn : ¬ (p.Valid ∧ p.toProblem.IsTO) := fun h => by
      rw [← validB_classTOB_iff] at h; rw [h] at hb; exact Bool.false_ne_true hb.symm
    simp only [redTO, hb, cond_false]
    exact ⟨fun h => absurd ⟨h.1, h.2.1⟩ hn, fun h => absurd h.1 badDesc_not_valid⟩
  · obtain ⟨hp, hto⟩ := (validB_classTOB_iff p).1 hb
    simp only [redTO, hb, cond_true]
    exact ⟨fun ⟨_, _, h⟩ => ⟨hv p, hY p, (hs p hp hto).2 h⟩,
      fun ⟨_, _, h⟩ => ⟨hp, hto, (hs p hp hto).1 h⟩⟩

theorem descA_fair_iff {p : ProbDesc} (hp : p.Valid) (hto : p.toProblem.IsTO) :
    (descA p).toProblem.MPStrongCyclicFairSolvable ↔ p.toProblem.Solvable :=
  (MPS.fair_iff_strong_ACYC (descA_valid p) (descA_ACYC p)).trans (descA_solvable_iff hp hto)

end HardMP

open HardMP HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-- **[CB22, Thm. 4], strong cyclic (fair reading), hardness.** -/
theorem hardFair_TR_TO_exp :
    Cx.Hard Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.TR FClass.TO)) :=
  HTN.Article.thm_4_3_6.of_redP (redP_TO_fair pt_descA descA_valid
    (fun p => ⟨descA_TR p, descA_TO p⟩) fun _ hp hto => descA_fair_iff hp hto)

/-- **[CB22, Thm. 4], strong cyclic (fair reading): EXPTIME-complete.** -/
theorem fairMP_TR_TO_complete :
    Cx.Complete Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.TR FClass.TO)) :=
  ⟨fairMP_TR_TO_mem, hardFair_TR_TO_exp⟩

end FOND
