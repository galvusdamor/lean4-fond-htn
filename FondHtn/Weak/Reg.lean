import FondHtn.Weak.Mem
import HtnComplexity.Article.ProgCors
/-!
# Weak plan existence of regular problems ([CB21, Cor. 4.5], with a different proof)

The weak compilation does not preserve regularity, and the argument of [CB21, Cor. 4.5] for
regular problems is only sketched (catalogue G13).  We use instead that regular problems are the
tail-recursive problems of height 1 (`HTN.Article.Problem.thm_3_0_1`) and that the compilation of
a tail-recursive problem of height `1` is tail-recursive of height `2`: the new compound tasks
form a stratum below all original ones.  Plan existence of tail-recursive problems of bounded
height is in PSPACE (`HTN.Article.cor_4_2_17`).  Regularity is decided in polynomial time, so the
reduction can filter out non-regular inputs.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.TaskNetwork

variable {p : FProbDesc}

/-- The stratification of the compilation of a regular problem. -/
def le2 (le : ℕ → ℕ → Prop) (x y : ℕ) : Prop := x % 2 = 1 ∨ (y % 2 = 0 ∧ le (x / 2) (y / 2))

theorem le2_even {le : ℕ → ℕ → Prop} (c d : ℕ) : le2 le (2 * c) (2 * d) ↔ le c d := by
  simp [le2]

theorem le2_odd {le : ℕ → ℕ → Prop} {x : ℕ} (hx : x % 2 = 1) (y : ℕ) : le2 le x y := Or.inl hx

theorem not_le2_even_odd {le : ℕ → ℕ → Prop} {x : ℕ} (hx : x % 2 = 1) (c : ℕ) :
    ¬ le2 le (2 * c) x := by
  simp [le2]; omega

theorem weak_tr2_of_reg (hp : p.Valid) (hY : FClass.REG p.toProblem) :
    (weakDesc p).toProblem.IsTailREC_h 2 := by
  have h1 : (strongDesc p).toProblem.IsTailREC_h 1 :=
    ((strongDesc p).toProblem.thm_3_0_1 (wf_toProblem _)).1 ((sMatches_REG p hp).1 hY)
  obtain ⟨le, hs, f, hf, hle⟩ := h1
  have hsh := sameShape_strongDesc p
  have hstrat : (PP p).IsStratification le := hsh.symm.strat hs.strat
  have hlast := fun m hm => hs.last m ((hsh.rm m).1 hm)
  have hnonlast := fun m hm => hs.nonlast m ((hsh.rm m).1 hm)
  have hall : ∀ c d, (PP p).ReachableName c → (PP p).ReachableName d → le c d := by
    intro c d hc hd
    have hc' := (hsh.rn c).1 hc
    have hd' := (hsh.rn d).1 hd
    exact (hle c d hc' hd').2 (by have := hf c hc'; have := hf d hd'; omega)
  -- the methods of the compilation, with reachable decomposed names
  have key : ∀ m', (QP p).ReachableMethod m' → ∀ t ∈ m'.subtasks.T, ∀ x,
      m'.subtasks.α t = Sum.inr x → ∃ e ∈ p.methods, m' = (wrapMD e).toMethod ∧
        (PP p).ReachableMethod e.toMethod ∧
        ((∃ d, e.toMethod.subtasks.α t = Sum.inr d ∧ x = 2 * d) ∨ x % 2 = 1) := by
    rintro m' ⟨hm, hr⟩ t ht x hx
    rcases mem_weakDesc_methods hm with ⟨e, he, rfl⟩ | ⟨y, -, j, -, rfl⟩
    · rcases reach_Q hp hr with ⟨c, hc, hrc⟩ | hodd
      · have hc' : e.1 = c := by simp [wrapMD, MethodDesc.toMethod] at hc; omega
        rw [← hc'] at hrc
        refine ⟨e, he, rfl, ⟨⟨e, he, rfl⟩, hrc⟩, ?_⟩
        rw [wrapMD_label hp he ht] at hx
        rcases wE_inr hx with ⟨d, hd, rfl⟩ | ⟨a, -, rfl⟩
        · exact Or.inl ⟨d, hd, rfl⟩
        · right; omega
      · simp [wrapMD, MethodDesc.toMethod] at hodd <;> omega
    · rw [leaf_label] at hx; cases hx
  refine ⟨le2 le, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, fun x => if x % 2 = 1 then 0 else 1, ?_, ?_⟩
  · intro x hx
    rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hodd
    · exact (le2_even c c).2 (hstrat.refl c hc)
    · exact le2_odd hodd _
  · intro x y z hx hy hz hxy hyz
    rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hx'
    · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
      · rcases reach_Q hp hz with ⟨e, rfl, he⟩ | hz'
        · exact (le2_even c e).2 (hstrat.trans c d e hc hd he ((le2_even c d).1 hxy)
            ((le2_even d e).1 hyz))
        · exact absurd hyz (not_le2_even_odd hz' d)
      · exact absurd hxy (not_le2_even_odd hy' c)
    · exact le2_odd hx' _
  · intro x y hx hy
    rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hx'
    · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
      · rcases hstrat.total c d hc hd with h | h
        · exact Or.inl ((le2_even c d).2 h)
        · exact Or.inr ((le2_even d c).2 h)
      · exact Or.inr (le2_odd hy' _)
    · exact Or.inl (le2_odd hx' _)
  · intro m' hr t ht hl x hx
    obtain ⟨e, he, rfl, hre, hd | hodd⟩ := key m' hr t ht x hx
    · obtain ⟨d, hd, rfl⟩ := hd
      exact (le2_even d e.1).2 (hlast e.toMethod hre t ht hl d hd)
    · exact le2_odd hodd _
  · intro m' hr t ht hl x hx
    obtain ⟨e, he, rfl, hre, hd | hodd⟩ := key m' hr t ht x hx
    · obtain ⟨d, hd, rfl⟩ := hd
      have := hnonlast e.toMethod hre t ht hl d hd
      exact ⟨(le2_even d e.1).2 this.1, fun h => this.2 ((le2_even e.1 d).1 h)⟩
    · exact ⟨le2_odd hodd _, not_le2_even_odd hodd e.1⟩
  · intro x _; show (if x % 2 = 1 then 0 else 1) < 2; split_ifs <;> omega
  · intro x y hx hy
    rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hx'
    · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
      · have h2 : ¬ (2 * c) % 2 = 1 := by omega
        have h3 : ¬ (2 * d) % 2 = 1 := by omega
        simp only [h2, h3, if_false, le_refl, iff_true]
        exact (le2_even c d).2 (hall c d hc hd)
      · have h2 : ¬ (2 * c) % 2 = 1 := by omega
        simp only [h2, hy', if_false, if_true]
        exact ⟨fun h => absurd h (not_le2_even_odd hy' c), fun h => by omega⟩
    · simp only [hx', if_true, zero_le, iff_true]
      exact le2_odd hx' _

/-! ## The reduction -/

/-- Regularity of a FOND description, decided in polynomial time. -/
def fREGB (p : FProbDesc) : Bool := methodsRB regB (strongDesc p) (reachSetB (strongDesc p))

theorem pt_fREGB : PT fREGB := pt_methodsRB pt_regB pt_strongDesc (pt_reachSetB.comp pt_strongDesc)

theorem fREGB_iff {p : FProbDesc} (hp : p.Valid) : fREGB p = true ↔ FClass.REG p.toProblem := by
  have hv := strongDesc_valid hp
  rw [sMatches_REG p hp]
  exact ⟨methodsRB_sound hv (fun c hc => (mem_reachSetB hv).2 hc) (fun ht => regB_iff ht),
    methodsRB_complete hv (fun c hc => (mem_reachSetB hv).1 hc) (fun ht => regB_iff ht)⟩

/-- The reduction: well-formed regular descriptions are compiled. -/
def regRed (p : FProbDesc) : ProbDesc := bif p.validB && fREGB p then weakDesc p else badPDesc

theorem redP_weakLD_REG : Cx.RedP (PlanExFM .weakLD FClass.REG) (PlanEx fun P => P.IsTailREC_h 2) := by
  refine redP_codeLang (f := regRed) (PT.cond (PT.and FProbDesc.pt_validB pt_fREGB) pt_weakDesc
    (PT.const badPDesc)) (fun p => ?_) badPDesc (fun h => badPDesc_not_valid h.1)
  by_cases hc : (p.validB && fREGB p) = true
  · simp only [Bool.and_eq_true] at hc
    have hp := (FProbDesc.validB_iff p).1 hc.1
    have hY := (fREGB_iff hp).1 hc.2
    simp only [regRed, hc.1, hc.2, Bool.and_self, cond_true]
    exact ⟨fun ⟨_, _, hs⟩ => ⟨weakDesc_valid hp, weak_tr2_of_reg hp hY, (weakLD_iff_weakDesc hp).1 hs⟩,
      fun ⟨_, _, hs⟩ => ⟨hp, hY, (weakLD_iff_weakDesc hp).2 hs⟩⟩
  · simp only [Bool.not_eq_true] at hc
    simp only [regRed, hc, cond_false]
    refine ⟨fun ⟨hp, hY, _⟩ => ?_, fun h => absurd h.1 badPDesc_not_valid⟩
    have : (p.validB && fREGB p) = true := by
      simp [(FProbDesc.validB_iff p).2 hp, (fREGB_iff hp).2 hY]
    rw [hc] at this; cases this

theorem weakLD_REG_mem : Cx.PSPACE (PlanExFM .weakLD FClass.REG) :=
  Cx.PSPACE.of_redP redP_weakLD_REG (cor_4_2_17 2)

theorem weakLD_REG_TO_mem : Cx.PSPACE (PlanExFM .weakLD (FClass.inter FClass.REG FClass.TO)) :=
  Cx.PSPACE.of_redP (redP_filterFM pt_fTOB fun _ hp => fTOB_iff hp) weakLD_REG_mem

/-- **[CB21, Cor. 4.5]**: weak plan existence of regular problems is PSPACE-complete. -/
theorem weakLD_REG_complete : Cx.Complete Cx.PSPACE (PlanExFM .weakLD FClass.REG) :=
  ⟨weakLD_REG_mem, (hard_REG_TO_fm .weakLD).of_redP (redP_filterFM pt_fTOB fun _ hp => fTOB_iff hp)⟩

theorem weakLD_REG_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakLD (FClass.inter FClass.REG FClass.TO)) :=
  ⟨weakLD_REG_TO_mem, hard_REG_TO_fm .weakLD⟩

theorem weakOD_REG_complete : Cx.Complete Cx.PSPACE (PlanExFM .weakOD FClass.REG) := by
  rw [planExFM_weakOD_eq]; exact weakLD_REG_complete

theorem weakOD_REG_TO_complete :
    Cx.Complete Cx.PSPACE (PlanExFM .weakOD (FClass.inter FClass.REG FClass.TO)) := by
  rw [planExFM_weakOD_eq]; exact weakLD_REG_TO_complete

end FOND
