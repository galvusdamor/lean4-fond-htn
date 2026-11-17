import FondHtn.RegTn.Desc
import FondHtn.Upper.StrongMem
import FondHtn.Weak.Reg
import FondHtn.MP.WeakReg
/-!
# Regular problems in the sense of [CB21] (`REGtn`): PSPACE-hardness and completeness

The inherited lower bounds only cover regularity in the sense of Bercher et al. (`FClass.REG`),
because goal elimination appends a task after `tn_I`.  The direct encoding
`FOND.RegTn.fondReg` of STRIPS (goal checked by the terminal method `c → g`) is deterministic,
in `REGtn ∩ TO`, and weak LD solvable iff the STRIPS problem has a plan; deterministic problems
collapse all criteria (`FOND.Problem.det_fm_iff`, `det_mpWeak_iff`, `det_mpStrong_iff`, and the
fair reading of strong cyclic, `FondHtn/MP/Fair.lean`).

Hardness (`c` any fixed-method criterion):

* `FOND.hard_REGtn_TO_fm c` — `PlanExFM c (REGtn ∩ TO)` is PSPACE-hard;
* `FOND.hard_REGtn_TO_mp` — `PlanExMP d (REGtn ∩ TO)` is PSPACE-hard for `d ∈ {weak, strong}`;
* `FOND.hardFair_REGtn_TO` — the fair strong cyclic language `PlanExMPFair (REGtn ∩ TO)`;
* `FOND.hard_REGtn_fm`, `FOND.hard_REGtn_mp`, `FOND.hardFair_REGtn` — the same without `TO`.

Completeness (memberships for `REG` via the class filter "`tn_I` regular", tested by
`HTN.Article.regB`):

* `FOND.weakLD_REGtn_complete`, `weakOD_REGtn_complete`, `strongLD_REGtn_complete`,
  `weakMP_REGtn_complete`, and the `REGtn ∩ TO` versions.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article RegTn

/-- Problems whose initial task network is regular. -/
def FClass.RT : FClass := fun P => P.tnI.IsRegular

/-! ## Hardness -/

theorem hard_of_fondReg {S : Problem ℕ ℕ ℕ ℕ → Prop}
    (hS : ∀ d : StripsDesc, d.Valid → (S (fondReg d).toProblem ↔ d.Solvable)) :
    Cx.Hard Cx.PSPACE (codeLang FProbDesc fun p =>
      p.Valid ∧ FClass.inter FClass.REGtn FClass.TO p.toProblem ∧ S p.toProblem) :=
  fun L hL => (strips_pspaceHard L hL).trans (redP_codeLang (α := StripsDesc) (β := FProbDesc)
    pt_fondReg (fun d => ⟨fun h => ⟨(fondReg_valid_iff d).2 h.1, fondReg_class d, (hS d h.1).2 h.2⟩,
      fun h => ⟨(fondReg_valid_iff d).1 h.1, (hS d ((fondReg_valid_iff d).1 h.1)).1 h.2.2⟩⟩)
    badDesc (fun h => badDesc_not_valid h.1))

theorem fondReg_wf {d : StripsDesc} (hv : d.Valid) : (fondReg d).toProblem.WF :=
  FProbDesc.toProblem_wf ((fondReg_valid_iff d).2 hv)

theorem fondReg_fm_iff (c : FMCrit) {d : StripsDesc} (hv : d.Valid) :
    c.Solvable (fondReg d).toProblem ↔ d.Solvable := by
  obtain ⟨h1, h2, h3⟩ := Problem.det_fm_iff (fond_isDeterministic d) (fondReg_wf hv).tnI
  cases c
  · exact weakLD_iff d
  · exact h1.trans (weakLD_iff d)
  · exact h2.trans (weakLD_iff d)
  · exact h3.trans (weakLD_iff d)

theorem fondReg_mpStrong_iff {d : StripsDesc} (hv : d.Valid) :
    (fondReg d).toProblem.MPStrongSolvable ↔ d.Solvable :=
  (Problem.det_mpStrong_iff (fond_isDeterministic d) (fondReg_wf hv)).trans (weakLD_iff d)

theorem fondReg_mpWeak_iff {d : StripsDesc} (hv : d.Valid) :
    (fondReg d).toProblem.MPWeakSolvable ↔ d.Solvable :=
  (Problem.det_mpWeak_iff (fond_isDeterministic d) (fondReg_wf hv)).trans (weakLD_iff d)

theorem fondReg_fair_iff {d : StripsDesc} (hv : d.Valid) :
    (fondReg d).toProblem.MPStrongCyclicFairSolvable ↔ d.Solvable :=
  ⟨fun h => (weakLD_iff d).1 (Problem.weakLDSolvable_of_fair (fondReg_wf hv).tnI h),
    fun h => Problem.fair_of_mpStrongSolvable ((fondReg_mpStrong_iff hv).2 h)⟩

/-- **`REGtn ∩ TO`, fixed methods: PSPACE-hard for every criterion.** -/
theorem hard_REGtn_TO_fm (c : FMCrit) :
    Cx.Hard Cx.PSPACE (PlanExFM c (FClass.inter FClass.REGtn FClass.TO)) :=
  hard_of_fondReg fun _ hv => fondReg_fm_iff c hv

/-- **`REGtn ∩ TO`, method-based policies (weak, strong): PSPACE-hard.** -/
theorem hard_REGtn_TO_mp (d : MPCrit) (hd : d ≠ .strongCyclic) :
    Cx.Hard Cx.PSPACE (PlanExMP d (FClass.inter FClass.REGtn FClass.TO)) := by
  cases d
  · exact hard_of_fondReg fun _ hv => fondReg_mpWeak_iff hv
  · exact absurd rfl hd
  · exact hard_of_fondReg fun _ hv => fondReg_mpStrong_iff hv

/-- **`REGtn ∩ TO`, fair strong cyclic: PSPACE-hard.** -/
theorem hardFair_REGtn_TO : Cx.Hard Cx.PSPACE (PlanExMPFair (FClass.inter FClass.REGtn FClass.TO)) :=
  hard_of_fondReg fun _ hv => fondReg_fair_iff hv

/-! ### Dropping `TO` -/

theorem redP_dropTO_fm (c : FMCrit) {Y : FClass} :
    Cx.RedP (PlanExFM c (FClass.inter Y FClass.TO)) (PlanExFM c Y) :=
  redP_filterFM pt_fTOB fun _ hp => fTOB_iff hp

/-- The class filter for the method-based and fair languages. -/
theorem redP_filterGen {Y Z : FClass} {S : Problem ℕ ℕ ℕ ℕ → Prop} {b : FProbDesc → Bool}
    (hb : PT b) (hbZ : ∀ p : FProbDesc, p.Valid → (b p = true ↔ Z p.toProblem)) :
    Cx.RedP (codeLang FProbDesc fun p => p.Valid ∧ FClass.inter Y Z p.toProblem ∧ S p.toProblem)
      (codeLang FProbDesc fun p => p.Valid ∧ Y p.toProblem ∧ S p.toProblem) := by
  refine redP_codeLang (f := fun p => bif b p then p else badDesc)
    (PT.cond hb PT.id (PT.const badDesc)) (fun p => ?_) badDesc (fun h => badDesc_not_valid h.1)
  by_cases hp : p.Valid
  · by_cases hz : b p = true
    · simp only [hz, cond_true]
      exact ⟨fun h => ⟨h.1, h.2.1.1, h.2.2⟩, fun h => ⟨h.1, ⟨h.2.1, (hbZ p hp).1 hz⟩, h.2.2⟩⟩
    · simp only [Bool.not_eq_true] at hz
      simp only [hz, cond_false]
      exact ⟨fun h => absurd ((hbZ p hp).2 h.2.1.2) (by rw [hz]; simp),
        fun h => absurd h.1 badDesc_not_valid⟩
  · simp only
    exact ⟨fun h => absurd h.1 hp, fun h => by
      cases hb' : b p
      · rw [hb'] at h; exact absurd h.1 badDesc_not_valid
      · rw [hb'] at h; exact absurd h.1 hp⟩

theorem hard_REGtn_fm (c : FMCrit) : Cx.Hard Cx.PSPACE (PlanExFM c FClass.REGtn) :=
  (hard_REGtn_TO_fm c).of_redP (redP_dropTO_fm c)

theorem hard_REGtn_mp (d : MPCrit) (hd : d ≠ .strongCyclic) :
    Cx.Hard Cx.PSPACE (PlanExMP d FClass.REGtn) :=
  (hard_REGtn_TO_mp d hd).of_redP (redP_filterGen pt_fTOB fun _ hp => fTOB_iff hp)

theorem hardFair_REGtn : Cx.Hard Cx.PSPACE (PlanExMPFair FClass.REGtn) :=
  hardFair_REGtn_TO.of_redP (redP_filterGen pt_fTOB fun _ hp => fTOB_iff hp)

/-! ## Completeness -/

/-- The test "`tn_I` is regular". -/
def rtB (p : FProbDesc) : Bool := regB p.tnI

theorem pt_rtB : PT rtB := pt_regB.comp (PT.snd.comp PT.snd)

theorem rtB_iff {p : FProbDesc} (hp : p.Valid) : rtB p = true ↔ FClass.RT p.toProblem :=
  regB_iff hp.tnI

theorem REGtn_eq : FClass.REGtn = FClass.inter FClass.REG FClass.RT := rfl

theorem REGtn_TO_eq :
    FClass.inter FClass.REGtn FClass.TO = FClass.inter (FClass.inter FClass.REG FClass.TO) FClass.RT := by
  funext P
  simp only [FClass.inter, FClass.REGtn, FClass.REG, FClass.RT, eq_iff_iff]
  tauto

theorem redP_REGtn_fm (c : FMCrit) : Cx.RedP (PlanExFM c FClass.REGtn) (PlanExFM c FClass.REG) := by
  rw [REGtn_eq]; exact redP_filterFM pt_rtB fun _ hp => rtB_iff hp

theorem redP_REGtn_TO_fm (c : FMCrit) :
    Cx.RedP (PlanExFM c (FClass.inter FClass.REGtn FClass.TO))
      (PlanExFM c (FClass.inter FClass.REG FClass.TO)) := by
  rw [REGtn_TO_eq]; exact redP_filterFM pt_rtB fun _ hp => rtB_iff hp

theorem weakLD_REGtn_complete : Cx.Complete Cx.PSPACE (PlanExFM .weakLD FClass.REGtn) :=
  ⟨Cx.PSPACE.of_redP (redP_REGtn_fm _) weakLD_REG_mem, hard_REGtn_fm _⟩

theorem weakLD_REGtn_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakLD (FClass.inter FClass.REGtn FClass.TO)) :=
  ⟨Cx.PSPACE.of_redP (redP_REGtn_TO_fm _) weakLD_REG_TO_mem, hard_REGtn_TO_fm _⟩

theorem weakOD_REGtn_complete : Cx.Complete Cx.PSPACE (PlanExFM .weakOD FClass.REGtn) := by
  rw [planExFM_weakOD_eq]; exact weakLD_REGtn_complete

theorem weakOD_REGtn_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakOD (FClass.inter FClass.REGtn FClass.TO)) := by
  rw [planExFM_weakOD_eq]; exact weakLD_REGtn_TO_complete

theorem strongLD_REGtn_complete : Cx.Complete Cx.PSPACE (PlanExFM .strongLD FClass.REGtn) :=
  ⟨Cx.PSPACE.of_redP (redP_REGtn_fm _) strongLD_REG_mem, hard_REGtn_fm _⟩

theorem strongLD_REGtn_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .strongLD (FClass.inter FClass.REGtn FClass.TO)) :=
  ⟨Cx.PSPACE.of_redP (redP_REGtn_TO_fm _) strongLD_REG_TO_mem, hard_REGtn_TO_fm _⟩

theorem weakMP_REGtn_complete : Cx.Complete Cx.PSPACE (PlanExMP .weak FClass.REGtn) := by
  rw [planExMP_weak_eq]; exact weakLD_REGtn_complete

theorem weakMP_REGtn_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExMP .weak (FClass.inter FClass.REGtn FClass.TO)) := by
  rw [planExMP_weak_eq]; exact weakLD_REGtn_TO_complete

end FOND
