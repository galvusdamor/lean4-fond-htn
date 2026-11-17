import FondHtn.StrongOD.RegChar
/-!
# The block game: solvability with leaves in an explicit list of states

The play positions of `FondHtn/StrongOD/Play.lean` with a different acceptance: a position
with no tasks left accepts iff its state (as a set) is one of the states of the list `W`
(`FOND.SOD.bacc`).  The block game from `(0, y, s, d)` is won (with budget `2·|ids|`) iff
`(cfgNet d, s)` is solvable with all leaves in `W` (`FOND.SOD.block_sound`,
`FOND.SOD.block_complete`).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false

/-- Two lists of facts denote the same state. -/
def sameB (w s : List ℕ) : Bool := w.all (fun f => decide (f ∈ s)) && s.all fun f => decide (f ∈ w)

theorem sameB_iff (w s : List ℕ) : sameB w s = true ↔ {f | f ∈ w} = {f | f ∈ s} := by
  simp only [sameB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Set.ext_iff,
    Set.mem_setOf_eq]
  exact ⟨fun h f => ⟨h.1 f, h.2 f⟩, fun h => ⟨fun f => (h f).1, fun f => (h f).2⟩⟩

/-- The states of a list of states. -/
def setW (W : List (List ℕ)) : Set (Set ℕ) := {S | ∃ w ∈ W, S = {f | f ∈ w}}

/-- Accepting block positions. -/
def bacc (y : (FProbDesc × List (List ℕ)) × GCfg) : Bool :=
  y.2.1 == 0 && y.2.2.2.2.ids.isEmpty && y.1.2.any fun w => sameB w y.2.2.2.1

/-- Universal block positions. -/
def buni (y : (FProbDesc × List (List ℕ)) × GCfg) : Bool := y.2.1 == 1

/-- The block moves. -/
def bsuccs (y : (FProbDesc × List (List ℕ)) × GCfg) : List GCfg := gsuccs (y.1.1, y.2)

theorem pt_sameB : PT fun z : List ℕ × List ℕ => sameB z.1 z.2 := by
  unfold sameB
  exact PT.and (PT.all PT.fst (PT.elem (PT.snd.comp PT.fst) PT.snd))
    (PT.all PT.snd (PT.elem (PT.fst.comp PT.fst) PT.snd))

theorem pt_bacc : PT bacc := by
  unfold bacc
  exact PT.and (PT.and (PT.beq (PT.fst.comp PT.snd) (PT.const 0))
    (PT.isEmpty (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))))))
    (PT.any (PT.snd.comp PT.fst) (pt_sameB.comp (PT.pair PT.snd
      (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.fst)))))))

theorem pt_buni : PT buni := PT.beq (PT.fst.comp PT.snd) (PT.const 1)

theorem pt_bsuccs : PT bsuccs := pt_gsuccs.comp (PT.pair (PT.fst.comp PT.fst) PT.snd)

variable {p : FProbDesc} {W : List (List ℕ)}

theorem bgameVal_succ (k : ℕ) (c : GCfg) : gameVal bacc buni bsuccs (p, W) (k + 1) c =
    (bacc ((p, W), c) || bif buni ((p, W), c) then
      (gsuccs (p, c)).all (gameVal bacc buni bsuccs (p, W) k)
      else (gsuccs (p, c)).any (gameVal bacc buni bsuccs (p, W) k)) := rfl

theorem bgameVal_zero (c : GCfg) : gameVal bacc buni bsuccs (p, W) 0 c = bacc ((p, W), c) := rfl

theorem mem_setW_of {s : List ℕ} (h : (W.any fun w => sameB w s) = true) :
    {f | f ∈ s} ∈ setW W := by
  obtain ⟨w, hw, hs⟩ := List.any_eq_true.1 h
  exact ⟨w, hw, ((sameB_iff w s).1 hs).symm⟩

/-- **Soundness of the block game.** -/
theorem block_sound : ∀ k y s d, CfgInv (s, d) →
    gameVal bacc buni bsuccs (p, W) k (0, y, s, d) = true →
      BSW p.toProblem (setW W) (cfgNet d) {f | f ∈ s} := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro y s d hc hw
    by_cases hacc : bacc ((p, W), ((0 : ℕ), y, s, d)) = true
    · simp only [bacc, Bool.and_eq_true, List.isEmpty_iff, beq_self_eq_true, true_and] at hacc
      exact .empty (by simp [cfgNet, hacc.1]) (mem_setW_of hacc.2)
    rw [Bool.not_eq_true] at hacc
    rcases k with _ | k
    · rw [bgameVal_zero, hacc] at hw; cases hw
    rw [bgameVal_succ, hacc] at hw
    simp only [buni, gsuccs, Bool.false_or, beq_self_eq_true, cond_true,
      show ((0 : ℕ) == 1) = false from rfl, cond_false, List.any_eq_true] at hw
    obtain ⟨c, hcm, hw⟩ := hw
    simp only [playMoves, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hcm
    obtain ⟨x, ⟨hx, ⟨hr, hprim⟩, happ⟩, rfl⟩ := hcm
    rcases k with _ | k
    · rw [bgameVal_zero] at hw; simp [bacc] at hw
    rw [bgameVal_succ] at hw
    simp only [bacc, buni, gsuccs, show ((1 : ℕ) == 0) = false from rfl, Bool.false_and,
      Bool.false_or, cond_false, beq_self_eq_true, cond_true, List.all_eq_true] at hw
    have hu := (unconstrained_iff hc x).2 ⟨hx, hr⟩
    have hr' := (readyB_iff d x).1 hr
    refine .step hu (cfgNet_α_of_lbl hprim) ((appB_iff _ _).1 happ) fun S' hS' => ?_
    obtain ⟨e, he, rfl⟩ := (mem_outcomes_iff _ _ _).1 hS'
    have h := ih k (by omega) 0 _ _ (inv_progDesc hc hx hr' (List.nodup_dedup _))
      (hw _ (List.mem_map.2 ⟨e, he, rfl⟩))
    rw [setOf_mem_dedup] at h
    exact h.congr (sameOn_of_agree (agree_progDesc hr').symm)

/-- **Completeness of the block game.** -/
theorem block_complete {tn : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ}
    (h : BSW p.toProblem (setW W) tn S) : ∀ k y s d, FOND.TaskNetwork.SameOn tn (cfgNet d) →
      S = {f | f ∈ s} → CfgInv (s, d) → 2 * d.ids.length ≤ k →
        gameVal bacc buni bsuccs (p, W) k (0, y, s, d) = true := by
  induction h with
  | empty hT hs =>
    intro k y s d hS hSs _ _
    have hd : d.ids = [] := by
      have := hS.1 ▸ hT
      simpa [cfgNet] using this
    obtain ⟨w, hw, hws⟩ := hs
    refine gameVal_of_acc (acc := bacc) (uni := buni) (succs := bsuccs) (a := (p, W))
      (c := ((0 : ℕ), y, s, d)) ?_ k
    simp only [bacc, Bool.and_eq_true, beq_self_eq_true, List.isEmpty_iff, hd, true_and,
      List.any_eq_true]
    exact ⟨w, hw, (sameB_iff w s).2 (hws.symm.trans hSs)⟩
  | @step tn S t a hu hα happ _ ih =>
    intro k y s d hS hSs hc hk
    subst hSs
    have hu' := (unconstrained_iff hc t).1 (hS.unconstrained hu)
    have hα' : (cfgNet d).α t = Sum.inl a := (hS.2.2 t hu.1).symm.trans hα
    have hl := lblOf_eq_of_α hα'
    have hlen := List.length_pos_of_mem hu'.1
    have hk' : 2 * d.ids.length ≤ k := hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    rw [bgameVal_succ]
    simp only [buni, gsuccs, Bool.or_eq_true, beq_self_eq_true, cond_true,
      show ((0 : ℕ) == 1) = false from rfl, cond_false, List.any_eq_true]
    refine Or.inr ⟨(1, t, s, d), ?_, ?_⟩
    · simp only [playMoves, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨t, ⟨hu'.1, ⟨hu'.2, by rw [hl]⟩, by rw [hl]; exact (appB_iff _ _).2 happ⟩, rfl⟩
    rw [bgameVal_succ]
    simp only [bacc, buni, gsuccs, show ((1 : ℕ) == 0) = false from rfl, Bool.false_and,
      Bool.false_or, cond_false, beq_self_eq_true, cond_true, List.all_eq_true, outMoves, hl,
      List.mem_map]
    rintro _ ⟨e, he, rfl⟩
    have hr' := (readyB_iff d t).1 hu'.2
    have hlen' := length_progDesc_ids (d := d) hc.ids_nodup hu'.1
    refine ih {f | f ∈ nextL s e} ((mem_outcomes_iff _ _ _).2 ⟨e, he, rfl⟩) k 0 _ _
      (sameOn_trans (hS.progress t) (sameOn_of_agree (agree_progDesc hr')))
      (setOf_mem_dedup _).symm (inv_progDesc hc hu'.1 hr' (List.nodup_dedup _)) (by omega)

end SOD

end FOND
