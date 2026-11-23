import FondHtn.FairUndec.Complete
import FondHtn.HardTR.TFair
import FondHtn.TOHard2.PT
/-!
# Fair strong cyclic MP plan existence is not semi-decidable

**`FOND.FU.fairMP_not_semiDecidable`**: `PlanExMPFair FClass.UNRES` is not semi-decidable.  In
particular the "semi-decidable" entry of [CB22] does not hold for strong cyclic solutions in the
fair reading.  (Undecidability, `FOND.undecidableFair`, is inherited from deterministic plan
existence.)

The reduction maps the code `c` of a partial recursive function to the description of the
two-stack machine `HTN.Undec.undecTSM` started with `([0], redStack c)`: fair solvability is an
infinite run (`FOND.FU.fair_iff_inf`), i.e. the divergence of `c` on `0`
(`FOND.FU.undecTSM_inf_iff`).  Divergence is not RE (`ComputablePred.halting_problem_not_re`).
-/

namespace FOND

namespace FU

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime HTN.Undec AcycHard.Sav TOHard2

/-- The description depends on the second stack in polynomial time. -/
theorem pt_desc_s₂ (M : TSM) (s₁ : List ℕ) (tk : ℕ → Bool) : PT fun s₂ : List ℕ => desc M s₁ s₂ tk := by
  have halph : PT fun s₂ : List ℕ => alph M s₁ s₂ :=
    PT.append (PT.append (PT.const s₁) PT.id) (PT.const _)
  have hsym : ∀ b : Bool, PT₂ fun (_ : List ℕ) (a : ℕ) => sym b a :=
    fun b => PT.natPair (PT.const 0) (PT.natPair (PT.const _) PT.snd)
  have hdrain : PT fun s₂ : List ℕ => [false, true].flatMap fun b =>
      (alph M s₁ s₂).map fun a => (sym b a, seqTn [(false, aD)]) :=
    pt_flatMap_const _ fun b _ => PT.map halph (PT.pair (hsym b) (PT.const _))
  have hstk : ∀ b : Bool, PT fun s₂ : List ℕ => stk0 s₁ s₂ b := by
    intro b; cases b
    · exact (PT.const s₁).of_eq fun _ => rfl
    · exact PT.id.of_eq fun _ => rfl
  have hroot : PT fun s₂ : List ℕ => [false, true].map fun b =>
      (root b, seqTn (symL b (stk0 s₁ s₂ b) ++ [(true, bot b)])) :=
    pt_map_const _ fun b _ => PT.pair (PT.const _) (pt_seqTn (PT.append
      (PT.map (g := fun _ a => (true, sym b a)) (hstk b) (PT.pair (PT.const true) (hsym b)))
      (PT.const _)))
  have hmeths : PT fun s₂ : List ℕ => meths M s₁ s₂ :=
    PT.append (PT.append (PT.append (PT.append (PT.const _) hdrain) (PT.const _)) hroot) (PT.const _)
  exact PT.pair (PT.pair (PT.const _) hmeths) (PT.const _)

/-- The reduction from divergence. -/
noncomputable def redF (n : ℕ) : List Bool := enc (desc undecTSM [0] (Sim.redStack n) fun _ => true)

theorem computable_redF : Computable redF := by
  obtain ⟨F, hF, hFe⟩ := pt_desc_s₂ undecTSM [0] fun _ => true
  have hc : Computable fun s₂ : List ℕ => F (enc s₂) :=
    (polyTimeFun_of_uc hF).computable.comp PEnc.primrec_enc.to_comp
  refine (hc.comp Sim.primrec_redStack.to_comp).of_eq fun n => ?_
  simp only [redF, Function.comp_apply]
  exact hFe _

theorem redF_iff (n : ℕ) : PlanExMPFair FClass.UNRES (redF n) ↔ ¬ (TMChain.univFun n).Dom := by
  rw [redF, HardTR.planExMPFair_enc_iff, ← undecTSM_inf_iff]
  constructor
  · rintro ⟨-, -, h⟩
    exact inf_of_fair h
  · intro h
    exact ⟨valid _ _ _ _, trivial, fair_of_inf h⟩

/-- **Fair strong cyclic method-based plan existence is not semi-decidable** (unrestricted
problems). -/
theorem fairMP_not_semiDecidable : ¬ Cx.SemiDecidable (PlanExMPFair FClass.UNRES) := by
  intro h
  apply ComputablePred.halting_problem_not_re 0
  have hg : Computable fun c : Nat.Partrec.Code => redF (Encodable.encode c) :=
    computable_redF.comp Computable.encode
  have h' : REPred fun c : Nat.Partrec.Code => PlanExMPFair FClass.UNRES (redF (Encodable.encode c)) :=
    Partrec.comp h hg
  refine h'.of_eq fun c => ?_
  rw [redF_iff, TMChain.univFun, Denumerable.ofNat_encode]

end FU

end FOND
