import FondHtn.MP.Weak
import FondHtn.MP.StrongCyclic
import FondHtn.Hardness.FromDet
/-!
# Fair strong cyclic solutions collapse to plan existence on deterministic problems

For the *fair* reading of strong cyclic solutions (Cimatti et al.: a goal node stays reachable
from every reachable node, `FOND.Problem.IsMPStrongCyclicFairSolution`):

* a fair strong cyclic solution yields a weak LD solution (a path from the initial node to a
  goal node is a weak plan);
* a strong solution is a fair strong cyclic solution (`IsMPStrongSolution.fair`);

so on deterministic problems, where weak and strong solvability coincide, fair strong cyclic
solvability is plan existence.  Consequently **every deterministic lower bound transfers to the
fair strong cyclic criterion** (`FOND.hardFair_*`), which is what [CB22]'s claims for strong
cyclic solutions need.  Under the literal definition this fails
(`FOND.LoopEx.literal_not_planExistence`).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

namespace Problem

variable {F A C I : Type} {P : Problem F A C I} [DecidableEq I]

/-- The problem has a fair strong cyclic solution. -/
def MPStrongCyclicFairSolvable (P : Problem F A C I) : Prop :=
  ∃ π, P.IsMPStrongCyclicFairSolution π

theorem weakLDSolvable_of_fair [Infinite I] (hwf : P.tnI.WF) (h : P.MPStrongCyclicFairSolvable) :
    P.WeakLDSolvable := by
  obtain ⟨π, -, hfair⟩ := h
  obtain ⟨y, hy, hg⟩ := hfair P.mpInit Relation.ReflTransGen.refl
  obtain ⟨n, hn⟩ := exists_wPathN_of_mpStep_star hy hg
  obtain ⟨tn, hd, hprim, hwb⟩ := hn.toWeakBelief hwf
  obtain ⟨l, as, hl, has, hex⟩ := weakExec_of_weakBelief hwb
  exact ⟨tn, l, ⟨hd, hprim⟩, hl, as, has, hex⟩

theorem fair_of_mpStrongSolvable [Nonempty I] (h : P.MPStrongSolvable) :
    P.MPStrongCyclicFairSolvable :=
  let ⟨π, hπ⟩ := h; ⟨π, hπ.fair⟩

end Problem

/-! ## Deterministic problems -/

theorem detDesc_fair_iff {p : ProbDesc} (hp : p.Valid) :
    (detDesc p).toProblem.MPStrongCyclicFairSolvable ↔ p.toProblem.Solvable := by
  obtain ⟨h1, -, -, -, -, h6⟩ := detDesc_solvable_iff hp
  constructor
  · intro h
    exact h1.1 (Problem.weakLDSolvable_of_fair (FProbDesc.toProblem_wf (detDesc_valid hp)).tnI h)
  · intro h
    exact Problem.fair_of_mpStrongSolvable (h6.2 h)

/-- Plan existence with fair strong cyclic method-based policies. -/
def PlanExMPFair (Y : FClass) : Cx.Language := fun w =>
  ∃ p : FProbDesc, enc p = w ∧ p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongCyclicFairSolvable

theorem redP_planExMPFair {Y : PClass} {Y' : FClass} (hY : Matches Y Y') :
    Cx.RedP (PlanEx Y) (PlanExMPFair Y') := by
  refine redP_codeLang pt_detRed (fun p => ?_) badDesc (fun h => badDesc_not_valid h.1)
  by_cases hp : p.Valid
  · simp only [detRed, if_pos hp]
    exact ⟨fun ⟨_, hy, hs⟩ => ⟨detDesc_valid hp, (hY p hp).1 hy, (detDesc_fair_iff hp).2 hs⟩,
      fun ⟨_, hy, hs⟩ => ⟨hp, (hY p hp).2 hy, (detDesc_fair_iff hp).1 hs⟩⟩
  · simp only [detRed, if_neg hp]
    exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badDesc_not_valid⟩

/-! ## Inherited lower bounds for fair strong cyclic solutions -/

theorem hardFair_PRIM : Cx.Hard Cx.NP (PlanExMPFair FClass.PRIM) :=
  thm_4_3_8.of_redP (redP_planExMPFair matches_PRIM)

theorem hardFair_REG_ACYC_TO :
    Cx.Hard Cx.NP (PlanExMPFair (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO))) :=
  thm_4_3_12_TO.of_redP (redP_planExMPFair (matches_REG.inter (matches_ACYC.inter matches_TO)))

theorem hardFair_REG_TO : Cx.Hard Cx.PSPACE (PlanExMPFair (FClass.inter FClass.REG FClass.TO)) :=
  thm_4_3_1.1.of_redP (redP_planExMPFair (matches_REG.inter matches_TO))

theorem hardFair_TR_TO : Cx.Hard Cx.PSPACE (PlanExMPFair (FClass.inter FClass.TR FClass.TO)) :=
  cor_4_3_2.1.of_redP (redP_planExMPFair (matches_TR.inter matches_TO))

theorem hardFair_ACYC_TO : Cx.Hard Cx.PSPACE (PlanExMPFair (FClass.inter FClass.ACYC FClass.TO)) :=
  thm_4_3_4.1.of_redP (redP_planExMPFair (matches_ACYC.inter matches_TO))

theorem hardFair_TO : Cx.Hard Cx.EXPTIME (PlanExMPFair FClass.TO) :=
  thm_4_3_6.of_redP (redP_planExMPFair matches_TO)

theorem hardFair_ACYC :
    Cx.Hard Cx.NEXPTIME (PlanExMPFair (FClass.inter FClass.ACYC FClass.TOtn)) :=
  thm_4_3_7_acyc.of_redP (redP_planExMPFair (matches_ACYC.inter matches_TOtn))

theorem hardFair_TR : Cx.Hard Cx.EXPSPACE (PlanExMPFair (FClass.inter FClass.TR FClass.TOtn)) :=
  thm_4_3_7_tr.of_redP (redP_planExMPFair (matches_TR.inter matches_TOtn))

theorem undecidableFair : ¬ Cx.Decidable (PlanExMPFair FClass.UNRES) := fun h =>
  thm_4_1_1 (ComputablePred.computable_of_manyOneReducible
    (redP_planExMPFair matches_UNRES).redC h)

end FOND
