import FondHtn.HardTR.TMain
import FondHtn.HardTR.WSafe
import FondHtn.MPStrong.CyclicDesc
/-!
# Tail-recursive fair strong cyclic MP plan existence is 2-EXPTIME-hard (CB22 Thm 5, fair)

The reduction of `FondHtn/HardTR/TMain.lean` also works for the fair reading of strong cyclic
solutions.  Completeness: a strong solution is a fair one.  Soundness
(`FOND.HardTR.TD.sound_fair`): a fair policy gives the progression fair game
(`FOND.Problem.mpStrongCyclicFairSolvable_iff_prog`), hence the *safe* word game on the
refinements of the initial network (`FOND.HardTR.lsafe_of_fairWin`), on records
(`FOND.HardTR.lsafe_pull`) and on the configurations of the transducer
(`FOND.HardTR.swin_of_lsafe`).  The transducer soundness (`FOND.HardTR.TT.Spec.boot_win`) only
needs the safe game: termination comes from the time of the tableau, which decreases in every
round.

* **`FOND.HardTR.hard_TR_mpFair`**, **`FOND.HardTR.complete_TR_mpFair`** — with
  `FOND.fairMP_TR_mem`, `PlanExMPFair FClass.TR` is 2-EXPTIME-complete.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TD

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav

variable {S : Type} {cS : S → ℕ} {X : Spec S} {allS : List S} {ops : List Op} {ens : List (En S)}
  {σ₀ : S}

/-- **Soundness for fair policies.** -/
theorem sound_fair (hS : Function.Injective cS) (hall : ∀ s, s ∈ allS) (hX : X.Valid)
    (h : (desc cS X allS ops ens σ₀).toProblem.MPStrongCyclicFairSolvable) :
    X.mach.Win {TL.cfg true 0 0} (r₀ σ₀) := by
  set d := desc cS X allS ops ens σ₀ with hd
  have hv := valid cS X allS ops ens σ₀ hS
  have hP := FProbDesc.toProblem_wf hv
  have hfw := (Problem.mpStrongCyclicFairSolvable_iff_prog hP.tnI).1 h
  have hL := lsafe_of_fairWin hP hfw
  have hD : (skelAt d.toProblem d.toProblem.tnI).domain.methods =
      {m | ∃ e ∈ meths cS X ops ens, e.toMethod = m} := by
    simp only [skelAt, Problem.skeleton, Problem.domain, FProbDesc.toProblem, hd, methods_desc]
  have hmwf : ∀ m ∈ (skelAt d.toProblem d.toProblem.tnI).domain.methods, m.subtasks.WF := by
    rw [hD]; rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _
  have htn : d.toProblem.tnI = (seqTn [lN .main]).toTaskNetwork := by
    simp only [FProbDesc.toProblem, hd, tnI_desc]
  have hgw : ∀ as ∈ {as | (skelAt d.toProblem d.toProblem.tnI).domain.NetYield d.toProblem.tnI as},
      GW cS X ops ens .main as := by
    intro as has
    rw [Set.mem_setOf_eq, htn] at has
    exact netYield_gen hmwf hD has
  have hpull := lsafe_pull (appB := X.mach.app) (outsB := X.mach.outs) (nmA cS)
    (fun r => (toCfg cS r).enc) (Good X) (· ∈ acts X ops ens)
    (fun x s hx => outcomes_ne hv x s hx)
    (fun b t hb hG => by
      rw [δ_desc hS hb, applicable_enc, app_iff hS hX hG])
    (fun b t hb hG happ => by
      rw [δ_desc hS hb, outcomes_enc _ (aspec_wf b) ((app_iff hS hX hG b).2 happ),
        out_eq hall hG happ, Set.image_image])
    (fun b t t' hG happ ht' => good_out hX hG happ ht')
    hL (fun w hw x hx => by
      obtain ⟨u, -, rfl, hu⟩ := hgw w hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      exact ⟨b, hu b hb, rfl⟩)
    good_r₀ (init_enc (allS := allS) (ops := ops) (ens := ens))
  have hC : (⟨fun _ => 0, true⟩ : TL.Cfg) = TL.cfg true 0 0 := by
    unfold TL.cfg; congr 1; funext q; split_ifs <;> rfl
  refine swin_of_lsafe hpull ?_
  intro w hw
  obtain ⟨u, hu, hwu, -⟩ := hgw _ hw
  have : w = u := List.map_injective_iff.2 (nmA_inj hS) hwu
  subst this
  exact ⟨_, hC ▸ rfl, Mach.gen_main_acc (by simp [Spec.mach]) hu⟩

end TD

open TL TT TE TD TI TP HardMP HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime TOHard2 ATM TM

/-- **Correctness of the reduction for fair policies.** -/
theorem TI.red_iff_fair {k : ℕ} {M : NTM (Fin k) (Option Bool)} {q e : Polynomial ℕ}
    {L : Cx.Language} (hb : M.blank = none)
    (hB : ∀ n, 2 ^ q.eval n + n + 3 ≤ 2 ^ e.eval n)
    (hL : ∀ x, L x ↔ ∃ i < 2 ^ 2 ^ e.eval x.length, ∃ qa ∈ M.accept, ∃ γ,
      TabWin M.F (row0 M q x) (2 ^ 2 ^ e.eval x.length - 1) i (some qa, γ)) (x : List Bool) :
    L x ↔ (red M q e x).toProblem.MPStrongCyclicFairSolvable := by
  refine ⟨fun hx => Problem.fair_of_mpStrongSolvable ((red_iff hb hB hL x).1 hx), fun h => ?_⟩
  exact src_sound hb hB (hL x)
    (sound_fair cSym_inj mem_allSym (srcSpec_valid (M := M) (q := q) (x := x) hb hB) h)

theorem planExMPFair_enc_iff {Y : FClass} {p : FProbDesc} :
    PlanExMPFair Y (enc p) ↔ p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongCyclicFairSolvable := by
  constructor
  · rintro ⟨p', hp', h⟩
    rwa [BEnc.inj hp'] at h
  · exact fun h => ⟨p, rfl, h⟩

/-- **Tail-recursive fair strong cyclic MP plan existence is 2-EXPTIME-hard** [CB22 Thm 5]. -/
theorem hard_TR_mpFair : Cx.Hard Cx.EXPTIME2 (PlanExMPFair FClass.TR) := by
  intro L hL
  obtain ⟨k, M, q, e, hb, -, hB, hLx⟩ := exptime2_tabWin_pow' hL
  have hf : PT (red M q e) := pt_red M q e hb
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun x => ?_⟩
  show L x ↔ PlanExMPFair FClass.TR (enc (red M q e x))
  rw [planExMPFair_enc_iff]
  exact ⟨fun hx => ⟨valid _ _ _ _ _ _ cSym_inj, red_TR x, (TI.red_iff_fair hb hB hLx x).1 hx⟩,
    fun ⟨_, _, h⟩ => (TI.red_iff_fair hb hB hLx x).2 h⟩

/-- **Tail-recursive fair strong cyclic MP plan existence is 2-EXPTIME-complete** [CB22 Thm 5]. -/
theorem complete_TR_mpFair : Cx.Complete Cx.EXPTIME2 (PlanExMPFair FClass.TR) :=
  ⟨fairMP_TR_mem, hard_TR_mpFair⟩

end HardTR

end FOND
