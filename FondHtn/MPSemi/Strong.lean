import FondHtn.StrongOD.SemiDec
import FondHtn.MPStrong.Acyc
/-!
# Strong method-based plan existence is semi-decidable ([CB22], unrestricted problems)

Strong method-based solvability is the progression game `FOND.Problem.MPProg` from
`(tn_I, s_I)` (`FOND.Problem.mpStrongSolvable_iff_mpProg`); every winning strategy has a finite
height (`FOND.Problem.MPProg.toH`), and a strategy of height `n` wins the description game of
`FondHtn/MPStrong/Game.lean` within `2 n` (`FOND.MPS.gameVal_complete`, conversely
`FOND.MPS.gameVal_sound`).  A certificate is an accepting run of the nondeterministic
depth-first evaluation (`HTN.Syn.PolyDom.dfsStep`) of that game from the initial node; its
check is polynomial time, hence computable.

* **`FOND.strongMP_semiDecidable`** — `PlanExMP strong UNRES` is semi-decidable;
* **`FOND.strongMP_semi_undec`** — semi-decidable and undecidable (`FOND.undecidable_mp`).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS SOD

namespace MPSemi

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-- The initial node (with the trivial certificate `false`). -/
def root (p : FProbDesc) : Bool × GNode := (false, ((false, 0), initF p))

/-- A certificate: a run of stacks. -/
abbrev MCert : Type := List (List (ℕ × (Bool × GNode)))

/-- **The certificate check.** -/
def mCheck (x : FProbDesc × MCert) : Bool :=
  x.1.validB && !x.2.isEmpty && decide (x.2.headI.length = 1) &&
    decide (x.2.headI.headI.2 = root x.1) && decide (x.2.getI x.2.tail.length = []) &&
    (List.range x.2.tail.length).all fun i =>
      dfsStep gAcc gUni succsG (x.1, x.2.getI i, x.2.getI (i + 1))

theorem pt_root : PT root := by
  unfold root
  exact PT.pair (PT.const false) (PT.pair (PT.const _) pt_initF)

theorem pt_mCheck : PT mCheck := by
  have hp : PT fun x : FProbDesc × MCert => x.1 := PT.fst
  have hR : PT fun x : FProbDesc × MCert => x.2 := PT.snd
  unfold mCheck
  exact PT.and (PT.and (PT.and (PT.and (PT.and (FProbDesc.pt_validB.comp hp)
    (PT.not (PT.isEmpty hR))) (PT.eq (PT.length (PT.headI hR)) (PT.const 1)))
    (PT.eq (PT.snd.comp (PT.headI (PT.headI hR))) (pt_root.comp hp)))
    (PT.eq (PT.getI hR (PT.length (PT.tail hR))) (PT.const [])))
    (PT.all (PT.rangeLength (PT.tail hR)) ((pt_dfsStep pt_gAcc pt_gUni pt_succsG).comp
      (PT.pair (hp.comp PT.fst) (PT.pair (PT.getI (hR.comp PT.fst) PT.snd)
        (PT.getI (hR.comp PT.fst) (PT.succ PT.snd))))))

theorem eq_single_of_length {β : Type} [Inhabited β] {l : List β} (h : l.length = 1) :
    l = [l.headI] := by
  match l, h with
  | [a], _ => rfl

/-- **Strong method-based solvability by certificates.** -/
theorem strongMP_iff_cert (p : FProbDesc) :
    (p.Valid ∧ p.toProblem.MPStrongSolvable) ↔ ∃ c : MCert, mCheck (p, c) = true := by
  constructor
  · rintro ⟨hp, hs⟩
    have hprog := (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).1 hs
    obtain ⟨n, hn⟩ := hprog.toH (FProbDesc.toProblem_wf hp).actions
    have hw := gameVal_complete hp hn (b := false) (g := root p) .refl rfl (init_state p)
      (FProbDesc.toProblem_wf hp).tnI (isoVia_art (isoVia_id_of_agree (agree_initF hp)))
    obtain ⟨B, hB⟩ := exists_bound (succs := succsG) (a := p)
      (fun c => sz (succsG (p, c))) (2 * n) (root p)
    have hrun := dfs_complete (acc := gAcc) (uni := gUni) (succs := succsG) (a := p) (B := B)
      (K := 2 * (2 * n) + 1) (N := sz ([] : List (ℕ × (Bool × GNode))) + 2 * n *
        dfsCost B (2 * (2 * n) + 1)) _ _ [] hw
      (fun k' hk' => (sz_nat_le k').trans (by omega)) hB le_rfl
    obtain ⟨Rn, hRn, hRh, hRl, hRs⟩ := exists_chain_list (hrun.mono fun _ _ h => h.1)
    refine ⟨Rn, ?_⟩
    simp only [mCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true', List.isEmpty_eq_false_iff]
    refine ⟨⟨⟨⟨⟨(FProbDesc.validB_iff p).2 hp, hRn⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hRh]; rfl
    · rw [hRh]; rfl
    · rw [List.length_tail]; exact hRl
    · intro i hi
      rw [List.length_tail] at hi
      exact hRs i (by omega)
  · rintro ⟨Rn, hc⟩
    simp only [mCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨⟨⟨⟨hv, hRn⟩, hlen⟩, hroot⟩, hlast⟩, hruns⟩ := hc
    have hp := (FProbDesc.validB_iff p).1 hv
    have hrun := chain_of_list (R := fun A B => dfsStep gAcc gUni succsG (p, A, B) = true) Rn
      Rn.tail.length (by rw [List.length_tail]; have := List.length_pos_of_ne_nil hRn; omega)
      fun i hi => hruns i (by rw [List.length_tail]; omega)
    rw [hlast, getI_zero_eq, eq_single_of_length hlen] at hrun
    have hwon := dfs_sound (fun _ _ h => h) hrun _ (List.mem_singleton_self _)
    rw [hroot] at hwon
    have h := (gameVal_sound hp (b := false) _ hwon .refl).1 rfl
    have hinv := (gInv_init hp false).inv
    simp only [root] at h
    rw [← init_state] at h
    exact ⟨hp, (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).2
      (h.isoVia hinv.wf (FProbDesc.toProblem_wf hp).tnI
        (isoVia_art (isoVia_id_of_agree (agree_initF hp).symm)))⟩

/-- The check on raw strings. -/
def mCheckRaw (x : List Bool × List Bool) : Bool :=
  isCode FProbDesc x.1 && isCode MCert x.2 &&
    mCheck ((decR x.1 : FProbDesc × List Bool).1, (decR x.2 : MCert × List Bool).1)

theorem pt_mCheckRaw : PT mCheckRaw := by
  unfold mCheckRaw
  exact PT.and (PT.and ((pt_isCode FProbDesc).comp PT.fst) ((pt_isCode MCert).comp PT.snd))
    (pt_mCheck.comp (PT.pair (PT.fst.comp (BDec.pt_decR.comp PT.fst))
      (PT.fst.comp (BDec.pt_decR.comp PT.snd))))

theorem planExMP_strong_iff (w : List Bool) :
    PlanExMP .strong FClass.UNRES w ↔ ∃ b, mCheckRaw (w, b) = true := by
  constructor
  · rintro ⟨p, rfl, hp, -, hs⟩
    obtain ⟨c, hc⟩ := (strongMP_iff_cert p).1 ⟨hp, hs⟩
    refine ⟨enc c, ?_⟩
    simp only [mCheckRaw, Bool.and_eq_true, (isCode_iff _).2 ⟨p, rfl⟩, (isCode_iff _).2 ⟨c, rfl⟩,
      decR_enc', hc, and_self]
  · rintro ⟨b, hb⟩
    simp only [mCheckRaw, Bool.and_eq_true] at hb
    obtain ⟨⟨hw, hbc⟩, hc⟩ := hb
    obtain ⟨p, rfl⟩ := (isCode_iff _).1 hw
    obtain ⟨c, rfl⟩ := (isCode_iff _).1 hbc
    rw [decR_enc', decR_enc'] at hc
    obtain ⟨hp, hs⟩ := (strongMP_iff_cert p).2 ⟨c, hc⟩
    exact ⟨p, rfl, hp, trivial, hs⟩

end MPSemi

open MPSemi in
/-- **[CB22], unrestricted problems**: strong method-based plan existence is semi-decidable. -/
theorem strongMP_semiDecidable : Cx.SemiDecidable (PlanExMP .strong FClass.UNRES) :=
  (rePred_exists (computable₂_of_pt pt_mCheckRaw)).of_eq fun w => (planExMP_strong_iff w).symm

/-- **Strong method-based plan existence of unrestricted problems: semi-decidable but
undecidable.** -/
theorem strongMP_semi_undec : Cx.SemiDecidable (PlanExMP .strong FClass.UNRES) ∧
    ¬ Cx.Decidable (PlanExMP .strong FClass.UNRES) :=
  ⟨strongMP_semiDecidable, undecidable_mp .strong (by decide)⟩

/-- **[CB22] Table, unrestricted (partially ordered) problems**: weak and strong method-based
plan existence are semi-decidable but undecidable. -/
theorem mp_weak_strong_semi_undec :
    (Cx.SemiDecidable (PlanExMP .weak FClass.UNRES) ∧
      ¬ Cx.Decidable (PlanExMP .weak FClass.UNRES)) ∧
    (Cx.SemiDecidable (PlanExMP .strong FClass.UNRES) ∧
      ¬ Cx.Decidable (PlanExMP .strong FClass.UNRES)) :=
  ⟨⟨weakMP_semiDecidable, undecidable_mp .weak (by decide)⟩, strongMP_semi_undec⟩

end FOND
