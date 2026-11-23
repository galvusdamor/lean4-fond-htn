import FondHtn.FairUndec.Main
import HtnComplexity.Article.Undecidability
/-!
# Fair strong cyclic MP plan existence is neither RE nor co-RE

**`FOND.FU.fairMP_compl_not_semiDecidable`**: the complement of `PlanExMPFair FClass.UNRES` is
not semi-decidable either.  The reduction is the one of the article's Thm. 4.1.1 (halting of
`undecTSM` → intersection of context-free grammars → deterministic plan existence), followed by
the polynomial-time embedding `FOND.redP_planExMPFair` of deterministic into fair strong cyclic
plan existence: the code `c` halts on `0` iff the image is fairly solvable.  Since halting is not
co-RE (`ComputablePred.halting_problem_not_re`), neither is the fair language.

Together with `FOND.FU.fairMP_not_semiDecidable`: **`FOND.FU.fairMP_not_RE_not_coRE`**.
-/

namespace FOND

namespace FU

open HTN HTN.Article HTN.Undec CFG CFGEnc PTime HTN.Syn.PolyDom

/-- Halting of `c` on `0`, as a deterministic plan-existence instance (Thm. 4.1.1). -/
noncomputable def redH (c : Nat.Partrec.Code) : List Bool :=
  enc (cfgProb gram₁ (gram undecTSM true (Sim.redStack (Encodable.encode c))))

theorem computable_redH : Computable redH :=
  (primrec_enc_probDesc.comp (primrec_cfgProb.comp (Primrec.const gram₁)
    ((primrec_gram undecTSM true).comp (Sim.primrec_redStack.comp Primrec.encode)))).to_comp

theorem redH_iff (c : Nat.Partrec.Code) :
    PlanEx UNRES (redH c) ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  have hu := undecTSM_halts_iff (Encodable.encode c)
  rw [TMChain.univFun, Denumerable.ofNat_encode] at hu
  rw [redH, planEx_enc_iff, ← hu, ← inter_gram_iff, ← solvable_cfgProb_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨valid_cfgProb, trivial, h⟩⟩

/-- **The complement of fair strong cyclic MP plan existence is not semi-decidable.** -/
theorem fairMP_compl_not_semiDecidable :
    ¬ Cx.SemiDecidable fun w => ¬ PlanExMPFair FClass.UNRES w := by
  intro h
  obtain ⟨g, hg, hge⟩ := redP_planExMPFair matches_UNRES
  apply ComputablePred.halting_problem_not_re 0
  have hc : Computable fun c => g (redH c) := hg.computable.comp computable_redH
  have h' : REPred fun c : Nat.Partrec.Code => ¬ PlanExMPFair FClass.UNRES (g (redH c)) :=
    Partrec.comp h hc
  refine h'.of_eq fun c => ?_
  rw [← hge, redH_iff]

/-- **Fair strong cyclic MP plan existence is neither RE nor co-RE.** -/
theorem fairMP_not_RE_not_coRE :
    ¬ Cx.SemiDecidable (PlanExMPFair FClass.UNRES) ∧
      ¬ Cx.SemiDecidable fun w => ¬ PlanExMPFair FClass.UNRES w :=
  ⟨fairMP_not_semiDecidable, fairMP_compl_not_semiDecidable⟩

end FU

end FOND
