import FondHtn.MPStrong.Game
import FondHtn.Upper.StrongMem
/-!
# Strong method-based plan existence: memberships in `EXPTIME` ([CB22, Thms. 1, 3, 4])

The membership halves of [CB22, Thms. 1, 3, 4] for **strong** method-based policies:

| class | here |
| --- | --- |
| `ACYC ∩ TO` [Thm. 1] | `FOND.strongMP_ACYC_TO_mem` |
| `REG` (Bercher et al.) [Thm. 3] | `FOND.strongMP_REG_mem`, also `REG ∩ TO`: `strongMP_REG_TO_mem` |
| `TR ∩ TO` [Thm. 4] | `FOND.strongMP_TR_TO_mem` |

All three are instances of `FOND.MPS.inExpTime_planExMP_strong`: the alternating progression
search of [CB22, Alg. 2] (an AND-OR game decided in exponential time, `APSPACE ⊆ EXPTIME`) over
configurations of polynomial size.  The class is certified as in the deterministic library
(certificates of `HtnComplexity/Article/ProgCors.lean`, checked on the skeleton description
`FOND.MPS.skDesc`), and the polynomial progression bounds are the deterministic ones
(Lemma 4.2.15 with `REG = TAIL-REC_1`, Thm. 3.0.1; Lemma 4.2.19 for `TAIL-REC ∩ TO`).

**Deviations from the paper.**

* [CB22] justifies the memberships by the progression algorithms, which only decompose tasks
  without predecessors, while their policies may decompose any task (gap G8).  Here this is
  closed by `FOND.Problem.mpStrongSolvable_iff_mpProg` (`FondHtn/MPStrong/Prog.lean`).
* Thm. 3 (`REG`) is proved with the *same* AND-OR progression search as Thms. 1 and 4 (the
  progression bound of regular problems is polynomial), not with the bounded graph search of
  [CB22] (explicit state graph + Cimatti et al.); both give `EXPTIME`.
* Only strong policies are treated.  The strong cyclic halves are not covered (gap G7 and the
  strong cyclic definition, G6).
* Completeness ([CB22]: EXPTIME-complete) is **not** obtained: only PSPACE-hardness is inherited
  from deterministic HTN planning (`FondHtn/Hardness/FromDet.lean`); the FOND-specific
  EXPTIME-hardness proofs are open (catalogue §4.6, §4.8, §4.9).  The theorems
  `strongMP_*_bounds` record membership together with the available lower bound.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

/-! ## The skeleton description: polynomial time and classes -/

theorem pt_skDesc : PT skDesc := by
  unfold skDesc skAct
  exact PT.pair (PT.pair (PT.map (PT.fst.comp PT.fst)
      (PT.pair (PT.fst.comp PT.snd) (PT.const (([], [], [], []) :
        List ℕ × List ℕ × List ℕ × List ℕ))))
    (PT.snd.comp PT.fst))
    (PT.pair (PT.const ([] : List ℕ)) (PT.pair (PT.snd.comp PT.snd)
      (PT.const (([], []) : List ℕ × List ℕ))))

theorem sameShape_skDesc (p : FProbDesc) :
    HTN.Problem.SameShape p.toProblem.toArt.toPos (skDesc p).toProblem.toPos :=
  ⟨rfl, fun _ => ⟨HTN.Problem.reachableName_of (P := p.toProblem.toArt.toPos)
      (P' := (skDesc p).toProblem.toPos) rfl (fun t ht _ hc => ⟨t, ht, hc⟩),
    HTN.Problem.reachableName_of (P := (skDesc p).toProblem.toPos)
      (P' := p.toProblem.toArt.toPos) rfl (fun t ht _ hc => ⟨t, ht, hc⟩)⟩⟩

theorem skDesc_TO (p : FProbDesc) : FClass.TO p.toProblem ↔ (skDesc p).toProblem.IsTO :=
  and_congr Iff.rfl (sameShape_skDesc p).isTO_M

/-! ## Memberships -/

/-- **[CB22, Thm. 3], membership (strong)**: strong method-based plan existence for regular
problems (Bercher et al.) is in `EXPTIME`. -/
theorem strongMP_REG_mem : Cx.EXPTIME (PlanExMP .strong FClass.REG) := by
  let r : Polynomial ℕ := 50 * (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 50 * (n + 1) ^ 2 := fun n => by simp [r]
  refine inExpTime_planExMP_strong (β := List ℕ × List (ℕ × ℕ))
    (cB := fun x => trB 1 (skDesc x.1, x.2)) ((pt_trB 1).comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r fun p hp hY => ?_
  · obtain ⟨R, rkL⟩ := b
    have hq := skDesc_valid hp
    exact (sameShape_skDesc p).isRegularM.2 (((skDesc p).toProblem.thm_3_0_1
      (wf_toProblem _)).2 (((trB_iff 1 (skDesc p) R rkL).1 hb).isTailREC_h hq))
  · have hq := skDesc_valid hp
    have hY' := ((skDesc p).toProblem.thm_3_0_1 (wf_toProblem _)).1
      ((sameShape_skDesc p).isRegularM.1 hY)
    have hS := sz_skDesc_le p
    obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -⟩ := exists_trCert hq hY'
    refine ⟨⟨(R, rkL), hb, ?_⟩, ?_⟩
    · have h1 : sz (R, rkL) ≤ 10 * (sz (skDesc p) + 1 + 1) ^ 2 := sz_rcert_le hRN hRl hrkN hrkl
      have h2 : (sz (skDesc p) + 1 + 1) ^ 2 ≤ (2 * (sz p + 1)) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      rw [hr]
      nlinarith
    · have hb := ((skDesc p).toProblem.lem_4_2_15 (wf_toProblem _) hY' (tnI_card_le _)
        (one_le_S _) (meth_card_le _)).1
      refine IsHTNProgBound.mono hb ?_
      rw [hr]
      nlinarith

/-- **[CB22, Thm. 4], membership (strong)**: strong method-based plan existence for
tail-recursive totally ordered problems is in `EXPTIME`. -/
theorem strongMP_TR_TO_mem : Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.TR FClass.TO)) := by
  let r : Polynomial ℕ := 200 * (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 200 * (n + 1) ^ 2 := fun n => by simp [r]
  refine inExpTime_planExMP_strong (β := ℕ × (List ℕ × List (ℕ × ℕ)))
    (cB := fun x => trTOB (skDesc x.1, x.2)) (pt_trTOB.comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r fun p hp hY => ?_
  · have hq := skDesc_valid hp
    simp only [trTOB, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    obtain ⟨htr, hcl⟩ := trHB_sound hq h1
    exact ⟨(sameShape_skDesc p).isTailRecursive.2 htr, (skDesc_TO p).2
      ⟨(toB_iff hq.tnI).1 h2, methodsRB_sound hq hcl (fun ht => toB_iff ht) h3⟩⟩
  · have hq := skDesc_valid hp
    have hS := sz_skDesc_le p
    have htr := (sameShape_skDesc p).isTailRecursive.1 hY.1
    have hto := (skDesc_TO p).1 hY.2
    obtain ⟨b, hb, hsz, hRr⟩ := exists_trHB hq htr
    refine ⟨⟨b, ?_, ?_⟩, ?_⟩
    · simp only [trTOB, Bool.and_eq_true]
      exact ⟨⟨hb, (toB_iff hq.tnI).2 hto.1⟩, methodsRB_complete hq hRr (fun ht => toB_iff ht) hto.2⟩
    · have h2 : (2 * sz (skDesc p) + 1) ^ 2 ≤ (4 * (sz p + 1)) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      rw [hr]
      nlinarith
    · have hb := ((skDesc p).toProblem.lem_4_2_19 (wf_toProblem _)
        (isTailREC_h_of_isTailREC hq htr) hto (tnI_card_le _) (meth_card_le _)).1
      refine IsHTNProgBound.mono hb ?_
      rw [hr]
      have hK : (numsOf (skDesc p)).length ≤ sz (skDesc p) := length_numsOf_le _
      have : (sz (skDesc p) - 1) * (numsOf (skDesc p)).length ≤ sz (skDesc p) * sz (skDesc p) :=
        Nat.mul_le_mul (Nat.sub_le _ _) hK
      nlinarith

/-- **[CB22, Thm. 1], membership (strong)**: strong method-based plan existence for acyclic
totally ordered problems is in `EXPTIME`. -/
theorem strongMP_ACYC_TO_mem :
    Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.ACYC FClass.TO)) := by
  let r : Polynomial ℕ := 200 * (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 200 * (n + 1) ^ 2 := fun n => by simp [r]
  refine inExpTime_planExMP_strong (β := List ℕ × List (ℕ × ℕ))
    (cB := fun x => acTOB (skDesc x.1, x.2)) (pt_acTOB.comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r fun p hp hY => ?_
  · have hq := skDesc_valid hp
    obtain ⟨R, rkL⟩ := b
    simp only [acTOB, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hc := (acycB_iff (skDesc p) R rkL).1 h1
    exact ⟨(sameShape_skDesc p).isAcyclic.2 hc.isACYC, (skDesc_TO p).2
      ⟨(toB_iff hq.tnI).1 h2, methodsRB_sound hq (fun _ hr => hc.reach_mem hr)
        (fun ht => toB_iff ht) h3⟩⟩
  · have hq := skDesc_valid hp
    have hS := sz_skDesc_le p
    have hac := (sameShape_skDesc p).isAcyclic.1 hY.1
    have hto := (skDesc_TO p).1 hY.2
    obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -, hRr, -⟩ := exists_acycCert hq hac
    have hK : (numsOf (skDesc p)).length ≤ sz (skDesc p) := length_numsOf_le _
    refine ⟨⟨(R, rkL), ?_, ?_⟩, ?_⟩
    · simp only [acTOB, Bool.and_eq_true]
      exact ⟨⟨hb, (toB_iff hq.tnI).2 hto.1⟩, methodsRB_complete hq hRr (fun ht => toB_iff ht) hto.2⟩
    · have h1 := sz_rcert_le (H := (numsOf (skDesc p)).length + 1) hRN hRl
        (fun q hq => ⟨(hrkN q hq).1, Nat.lt_succ_of_le (hrkN q hq).2⟩) hrkl
      have h2 : (sz (skDesc p) + ((numsOf (skDesc p)).length + 1) + 1) ^ 2 ≤
          (4 * (sz p + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [hr]
      nlinarith
    · have hb := ((skDesc p).toProblem.lem_4_2_19 (wf_toProblem _)
        (isTailREC_h_of_isTailREC hq (isTailREC_of_isACYC hac)) hto (tnI_card_le _)
        (meth_card_le _)).1
      refine IsHTNProgBound.mono hb ?_
      rw [hr]
      have : (sz (skDesc p) - 1) * (numsOf (skDesc p)).length ≤ sz (skDesc p) * sz (skDesc p) :=
        Nat.mul_le_mul (Nat.sub_le _ _) hK
      nlinarith

/-! ## A class filter for method-based policies -/

/-- Dropping a restriction decided in polynomial time (method-based policies). -/
theorem redP_filterMP {c : MPCrit} {Y Z : FClass} {b : FProbDesc → Bool} (hb : PT b)
    (hbZ : ∀ p : FProbDesc, p.Valid → (b p = true ↔ Z p.toProblem)) :
    Cx.RedP (PlanExMP c (FClass.inter Y Z)) (PlanExMP c Y) := by
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

/-- **[CB22, Thm. 3] for totally ordered problems, membership (strong).** -/
theorem strongMP_REG_TO_mem :
    Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.REG FClass.TO)) :=
  Cx.EXPTIME.of_redP (redP_filterMP pt_fTOB fun _ hp => fTOB_iff hp) strongMP_REG_mem

/-! ## Membership with the available lower bounds

[CB22] claims EXPTIME-completeness; only PSPACE-hardness is inherited from deterministic HTN
planning, so the gap between the bounds remains (FOND-specific hardness is open). -/

theorem strongMP_ACYC_TO_bounds :
    Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.ACYC FClass.TO)) ∧
      Cx.Hard Cx.PSPACE (PlanExMP .strong (FClass.inter FClass.ACYC FClass.TO)) :=
  ⟨strongMP_ACYC_TO_mem, hard_ACYC_TO_mp .strong (by decide)⟩

theorem strongMP_REG_TO_bounds :
    Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.REG FClass.TO)) ∧
      Cx.Hard Cx.PSPACE (PlanExMP .strong (FClass.inter FClass.REG FClass.TO)) :=
  ⟨strongMP_REG_TO_mem, hard_REG_TO_mp .strong (by decide)⟩

theorem strongMP_REG_bounds :
    Cx.EXPTIME (PlanExMP .strong FClass.REG) ∧ Cx.Hard Cx.PSPACE (PlanExMP .strong FClass.REG) :=
  ⟨strongMP_REG_mem, (hard_REG_TO_mp .strong (by decide)).of_redP
    (redP_filterMP pt_fTOB fun _ hp => fTOB_iff hp)⟩

theorem strongMP_TR_TO_bounds :
    Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.TR FClass.TO)) ∧
      Cx.Hard Cx.PSPACE (PlanExMP .strong (FClass.inter FClass.TR FClass.TO)) :=
  ⟨strongMP_TR_TO_mem, hard_TR_TO_mp .strong (by decide)⟩

end FOND
