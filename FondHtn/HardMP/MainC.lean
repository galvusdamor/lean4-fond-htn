import FondHtn.HardMP.SemC
import FondHtn.HardMP.ClassesC
import FondHtn.HardMP.FairBridge
/-!
# Correctness of the counter construction (strong and fair readings)
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

section C

variable (p : ProbDesc)

theorem descC_methods : (descC p).methods =
    chainMeths (prgsC p) [(true, roundN)] ++ (roundMeths (prgsC p) ++ [meth roundN [(false, finN)]]) := by
  simp [descC, FProbDesc.methods, List.append_assoc]

theorem descC_hO : ∀ e ∈ roundMeths (prgsC p) ++ [meth roundN [(false, finN)]], ∀ r pc,
    e.1 ≠ cN r pc := by
  intro e he r pc h
  rcases List.mem_append.1 he with he | he
  · exact cN_ne_roundN r pc (h.symm.trans (head_roundMeths he))
  · rw [List.mem_singleton] at he; subst he
    exact cN_ne_roundN r pc h.symm

theorem mem_roundMethsC {ls : List (Bool × ℕ)} :
    meth roundN ls ∈ roundMeths (prgsC p) ↔ ∃ r < (rulesC p).length, ls = [(true, cN (r + 1) 0)] := by
  simp only [roundMeths, List.mem_map, List.mem_range, meth_injS, true_and, prgsC,
    List.length_cons, Nat.add_sub_cancel]
  exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩

theorem descC_hR (ls : List (Bool × ℕ)) : meth roundN ls ∈ (descC p).methods ↔
    (∃ r < (rulesC p).length, ls = [(true, cN (r + 1) 0)]) ∨ ls ∈ [[(false, finN)]] := by
  rw [descC_methods, List.mem_append, List.mem_append, ← mem_roundMethsC]
  simp only [List.mem_singleton, meth_injS, true_and]
  exact ⟨fun h => h.resolve_left not_mem_chain_round, fun h => Or.inr h⟩

theorem hspecC : ∀ r < (prgsC p).length, ∀ pc < ((prgsC p).getI r).length,
    ∀ alt < (((prgsC p).getI r).getI pc).length, ((((prgsC p).getI r).getI pc).getI alt).WF :=
  fun _ hr _ hpc _ halt =>
    (prgsC_spec p _ (getI_memS hr) _ (getI_memS hpc) _ (getI_memS halt)).1

/-- The round programs keep the counter. -/
theorem rules_frame {r : List (List ASpec)} (hr : r ∈ rules p) {Ψ : Set Cfg} {c : Cfg}
    (h : c ∈ wpP r Ψ) : c ∈ wpP r {c' | c' ∈ Ψ ∧ ctrC p c' = ctrC p c} := by
  have := wpP_frame (G := fun f => ∃ j, f = fSlot (cslot p) j) (fun ins hins a ha e he f hf => by
    obtain ⟨j, rfl⟩ := hf
    exact frame_prgs p r (List.mem_cons_of_mem _ hr) ins hins a ha e he j) h
  refine wpP_mono _ (fun c' hc' => ?_) this
  obtain ⟨h1, h2⟩ := hc'
  exact ⟨h1, bitsum_congr fun j _ => h2 _ ⟨j, rfl⟩⟩

variable {p} {allV : List (List Bool)} (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length)
include hall

/-- **Soundness of the loop with a counter.** -/
theorem loop_soundC : ∀ n {c : Cfg},
    (descC p).toProblem.LRunH n [Sum.inr roundN] c.enc Set.univ → Good p allV c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c h
    rcases n with _ | n
    · exact absurd h Problem.not_lrunH_zero_cons
    rcases round_sound_LC (descC_valid p) rfl (descC_methods p) (descC_hO p) (seqMeths_descC p)
      (hspecC p) (descC_hR p) h with ⟨r, hr, hc⟩ | h
    · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
      obtain ⟨i, -, -, -, hi⟩ := mem_wpI_inc.1 hc
      exact incCfg_good.1 (round_sound hall (fun c' hc' => ih n (by omega) hc') hr₀ hi)
    · rcases n with _ | n
      · exact absurd h Problem.not_lrunH_zero_cons
      exact Or.inl ((lrunH_finN (descC_valid p) rfl).1 h).1

/-- **Completeness of the loop with a counter.** -/
theorem loop_completeC : ∀ m {c : Cfg}, GoodK p allV m c → ctrC p c + m < 2 ^ Nc p →
    (descC p).toProblem.LRunH ((m + 1) * (2 * LrC p + 2)) [Sum.inr roundN] c.enc Set.univ := by
  intro m
  induction m with
  | zero =>
    intro c hc _
    have hd := goodK_zero hc
    have h2 : (descC p).toProblem.LRunH 2 [Sum.inr roundN] c.enc Set.univ := by
      refine .comp ((seqBodyF_iff (seqMeths_descC p)).2 ⟨[(false, finN)],
        (descC_hR p _).2 (Or.inr (by simp)), rfl⟩) ?_
      simpa [toLab] using (lrunH_finN (descC_valid p) rfl).2 ⟨hd, .nil (Set.mem_univ _)⟩
    exact h2.mono (by nlinarith) le_rfl
  | succ m ih =>
    intro c hc hctr
    obtain ⟨i, hi, hlo, hb⟩ := exists_inc (b := fun j => c.val (fSlot (cslot p) j))
      (N := Nc p) (by unfold ctrC at hctr; omega)
    have hctr' := ctrC_inc hi hlo hb
    obtain ⟨r₀, hr₀, hc'⟩ := round_complete hall (incCfg_goodK.2 hc)
    have hfr := rules_frame p hr₀ hc'
    have hin : c ∈ wpP (incI p :: r₀)
        {c' | (descC p).toProblem.LRunH ((m + 1) * (2 * LrC p + 2)) [Sum.inr roundN]
          c'.enc Set.univ} := by
      rw [wpP_cons]
      refine mem_wpI_inc.2 ⟨i, hi, hlo, hb, wpP_mono _ (fun c'' hc'' => ?_) hfr⟩
      exact ih hc''.1 (by rw [hc''.2, hctr']; omega)
    have := round_complete_LC (descC_valid p) rfl (descC_methods p) (descC_hO p)
      (seqMeths_descC p) (hspecC p) (descC_hR p) (List.mem_map.2 ⟨r₀, hr₀, rfl⟩) hin
    exact this.mono (by ring_nf; omega) le_rfl

end C

theorem ctrC_cfg1 (p : ProbDesc) (g : ℕ → Bool) : ctrC p (cfg1 p g) = 0 := by
  unfold ctrC bitsum
  refine Finset.sum_eq_zero fun j _ => ?_
  have hK := cslot_ge p
  have : (cfg1 p g).val (fSlot (cslot p) j) = false := by
    rw [cfg1, sets_eFields_val_ne fun j' h => by simp only [fSlot_inj] at h; omega]
    simp only [cfgInit, fSlot_inj, decide_eq_false_iff_not, not_exists, not_and]
    intro j' _ h; omega
  simp only [this, Bool.false_eq_true, if_false]

/-- **The counter description is strongly solvable iff the dynamic program accepts.** -/
theorem descC_iff (p : ProbDesc) {allV : List (List Bool)}
    (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length)
    (hN : (cand p allV).length + 2 < 2 ^ Nc p) :
    (descC p).toProblem.MPStrongSolvable ↔ DPAcc p allV := by
  have hv := descC_valid p
  have hA : (descC p).actions = acts (prgsC p) := rfl
  have hM := descC_methods p
  have hO := descC_hO p
  have hmeth := seqMeths_descC p
  have hspec := hspecC p
  have hinit : {f | f ∈ (descC p).init} = (cfgInit p).enc := enc_cfgInit p
  have h0 : (0 : ℕ) < (prgsC p).length := by simp [prgsC]
  rw [mpStrong_iff_lrun hv hmeth (rfl : (descC p).tnI = _), hinit]
  simp only [List.map_cons, List.map_nil, toLab, if_true]
  constructor
  · rintro ⟨n, h⟩
    have h1 := chain_sound hv hA hM hO hmeth hspec h0 _ 0 (Nat.zero_add _).symm h
    simp only [List.drop_zero, prgsC, List.getI_cons_zero, List.map_cons, List.map_nil, toLab,
      if_true, List.cons_append, List.nil_append] at h1
    obtain ⟨g, hg, h2⟩ := mem_wpP_init.1 h1
    exact acc_of_good hg (loop_soundC hall _ h2)
  · intro hacc
    obtain ⟨g, hg, hG⟩ := good_of_acc hall hacc
    have hl := loop_completeC hall _ hG (by rw [ctrC_cfg1]; omega)
    refine ⟨_, chain_complete hv hA hM hO hmeth hspec h0 _ 0 (Nat.zero_add _).symm (xs := [])
      (m := ((cand p allV).length + 2 + 1) * (2 * LrC p + 2)) ?_⟩
    simp only [List.drop_zero, prgsC, List.getI_cons_zero, List.map_cons, List.map_nil, toLab,
      if_true, List.cons_append, List.nil_append]
    exact mem_wpP_init.2 ⟨g, hg, hl⟩

theorem cand_boundC (p : ProbDesc) : (cand p (allVp p)).length + 2 < 2 ^ Nc p := by
  have := cand_bound p
  have h1 : 2 ^ Nclk p < 2 ^ Nc p := Nat.pow_lt_pow_right (by norm_num) (by simp [Nc])
  omega

theorem descC_solvable_iff {p : ProbDesc} (hp : p.Valid) (hto : p.toProblem.IsTO) :
    (descC p).toProblem.MPStrongSolvable ↔ p.toProblem.Solvable := by
  rw [solvable_iff_dpAcc hp hto]
  exact descC_iff p (fun _ => mem_allVp) (cand_boundC p)

end HardMP

end FOND
