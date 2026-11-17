import FondHtn.HardMP.Main
import FondHtn.HardMP.Classes
import FondHtn.HardMP.PT
import FondHtn.Hardness.FromDet
import HtnComplexity.Article.TOHard
import HtnComplexity.Article.TOExp
/-!
# EXPTIME-hardness of strong method-based plan existence

Instantiation of the semantics (`FondHtn/HardMP/Main.lean`) for the two descriptions, and the
reductions from totally ordered deterministic HTN planning (`HTN.Article.thm_4_3_6`).

* `FOND.hard_ACYC_TO_mpStrong` — [CB22, Thm. 1] (hardness part);
* `FOND.hard_TR_TO_mpStrong` — [CB22, Thm. 4] (hardness part);
* `FOND.hard_REG_mpStrong`, `FOND.hard_REG_TO_mpStrong` — [CB22, Thm. 3] (hardness part).

**Deviations from [CB22].**  The published proofs are incomplete (catalogue G11, G17); these are
new reductions from totally ordered deterministic HTN planning (a path game down a derivation
tree of the dynamic program of Thm. 4.2.1).  The constructed problems use **negative
preconditions** (`preNeg`), which [CB21, CB22] do not allow; actions have up to `k` outcomes
(`k` the largest number of subtasks of a source method).  The regular construction is in the
class `REG` of Bercher et al. (and totally ordered).
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn HTN.Syn.PolyDom PTime

/-! ## The shape of the descriptions -/

theorem cN_ne_roundN (r pc : ℕ) : cN r pc ≠ roundN := by unfold cN roundN; omega
theorem cN_ne_clkN (r pc j : ℕ) : cN r pc ≠ clkN j := by unfold cN clkN; omega
theorem clkN_ne_roundN (j : ℕ) : clkN j ≠ roundN := by unfold clkN roundN; omega
theorem clkN_inj {j j' : ℕ} : clkN j = clkN j' ↔ j = j' := by unfold clkN; omega

theorem hspec_of (p : ProbDesc) : ∀ r < (prgs p).length, ∀ pc < ((prgs p).getI r).length,
    ∀ alt < (((prgs p).getI r).getI pc).length, ((((prgs p).getI r).getI pc).getI alt).WF :=
  fun _ hr _ hpc _ halt =>
    (prgs_spec p _ (getI_memS hr) _ (getI_memS hpc) _ (getI_memS halt)).1

theorem head_roundMeths {P : List (List (List ASpec))} {e : MethodDesc} (he : e ∈ roundMeths P) :
    e.1 = roundN := by
  simp only [roundMeths, List.mem_map] at he
  obtain ⟨r, -, rfl⟩ := he; rfl

theorem head_clockMeths {N : ℕ} {e : MethodDesc} (he : e ∈ clockMeths N) : ∃ j, e.1 = clkN j := by
  simp only [clockMeths, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨j, -, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨j + 1, rfl⟩

theorem head_chainMeths {P : List (List (List ASpec))} {ex : List (Bool × ℕ)} {c : ℕ}
    {ls : List (Bool × ℕ)} (he : meth c ls ∈ chainMeths P ex) : ∃ r pc, c = cN r pc := by
  obtain ⟨r, -, ⟨pc, -, alt, -, rfl, -⟩ | ⟨rfl, -⟩⟩ := mem_chainMethsS.1 he
  · exact ⟨r, pc, rfl⟩
  · exact ⟨r, _, rfl⟩

theorem mem_roundMeths {p : ProbDesc} {ls : List (Bool × ℕ)} :
    meth roundN ls ∈ roundMeths (prgs p) ↔ ∃ r < (rules p).length, ls = [(true, cN (r + 1) 0)] := by
  simp only [roundMeths, List.mem_map, List.mem_range, meth_injS, true_and, prgs,
    List.length_cons, Nat.add_sub_cancel]
  exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩

theorem not_mem_roundMeths_clk {P : List (List (List ASpec))} {j : ℕ} {ls : List (Bool × ℕ)} :
    meth (clkN j) ls ∉ roundMeths P := fun h => clkN_ne_roundN j (head_roundMeths h)

theorem not_mem_chain_round {P : List (List (List ASpec))} {ex : List (Bool × ℕ)}
    {ls : List (Bool × ℕ)} : meth roundN ls ∉ chainMeths P ex := fun h => by
  obtain ⟨r, pc, he⟩ := head_chainMeths h
  exact cN_ne_roundN r pc he.symm

theorem not_mem_chain_clk {P : List (List (List ASpec))} {ex : List (Bool × ℕ)} {j : ℕ}
    {ls : List (Bool × ℕ)} : meth (clkN j) ls ∉ chainMeths P ex := fun h => by
  obtain ⟨r, pc, he⟩ := head_chainMeths h
  exact cN_ne_clkN r pc j he.symm

theorem mem_clockMeths {N j : ℕ} {ls : List (Bool × ℕ)} :
    meth (clkN j) ls ∈ clockMeths N ↔ (j = 0 ∧ ls = [(true, roundN)]) ∨
      ∃ j' < N, j = j' + 1 ∧ ls = [(true, clkN j'), (true, clkN j')] := by
  simp only [clockMeths, List.mem_cons, List.mem_map, List.mem_range, meth_injS, clkN_inj]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨j', hj', rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨j', hj', rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨j', hj', rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨j', hj', rfl, rfl⟩

theorem roundN_ne_clkN_meth {N : ℕ} {ls : List (Bool × ℕ)} : meth roundN ls ∉ clockMeths N :=
  fun h => by
    obtain ⟨j, hj⟩ := head_clockMeths h
    exact clkN_ne_roundN j hj.symm

section A

variable (p : ProbDesc)

theorem descA_methods : (descA p).methods =
    chainMeths (prgs p) [] ++ (roundMeths (prgs p) ++ clockMeths (Nclk p)) := by
  simp [descA, FProbDesc.methods, List.append_assoc]

theorem descA_hO : ∀ e ∈ roundMeths (prgs p) ++ clockMeths (Nclk p), ∀ r pc, e.1 ≠ cN r pc := by
  intro e he r pc h
  rcases List.mem_append.1 he with he | he
  · exact cN_ne_roundN r pc (h.symm.trans (head_roundMeths he))
  · obtain ⟨j, hj⟩ := head_clockMeths he
    exact cN_ne_clkN r pc j (h.symm.trans hj)

theorem descA_hR (ls : List (Bool × ℕ)) : meth roundN ls ∈ (descA p).methods ↔
    ∃ r < (rules p).length, ls = [(true, cN (r + 1) 0)] := by
  rw [descA_methods, List.mem_append, List.mem_append, ← mem_roundMeths]
  exact ⟨fun h => (h.resolve_left not_mem_chain_round).resolve_right roundN_ne_clkN_meth,
    fun h => Or.inr (Or.inl h)⟩

theorem descA_hC (j : ℕ) (ls : List (Bool × ℕ)) : meth (clkN j) ls ∈ (descA p).methods ↔
    (j = 0 ∧ ls = [(true, roundN)]) ∨
      ∃ j' < Nclk p, j = j' + 1 ∧ ls = [(true, clkN j'), (true, clkN j')] := by
  rw [descA_methods, List.mem_append, List.mem_append, ← mem_clockMeths]
  exact ⟨fun h => (h.resolve_left not_mem_chain_clk).resolve_left not_mem_roundMeths_clk,
    fun h => Or.inr (Or.inr h)⟩

end A

section R

variable (p : ProbDesc)

theorem descR_methods : (descR p).methods =
    chainMeths (prgs p) [(true, roundN)] ++ (roundMeths (prgs p) ++ [meth roundN [(false, finN)]]) := by
  simp [descR, FProbDesc.methods, List.append_assoc]

theorem descR_hO : ∀ e ∈ roundMeths (prgs p) ++ [meth roundN [(false, finN)]], ∀ r pc,
    e.1 ≠ cN r pc := by
  intro e he r pc h
  rcases List.mem_append.1 he with he | he
  · exact cN_ne_roundN r pc (h.symm.trans (head_roundMeths he))
  · rw [List.mem_singleton] at he; subst he
    exact cN_ne_roundN r pc h.symm

theorem descR_hR (ls : List (Bool × ℕ)) : meth roundN ls ∈ (descR p).methods ↔
    (∃ r < (rules p).length, ls = [(true, cN (r + 1) 0)]) ∨ ls ∈ [[(false, finN)]] := by
  rw [descR_methods, List.mem_append, List.mem_append, ← mem_roundMeths]
  simp only [List.mem_singleton, meth_injS, true_and]
  exact ⟨fun h => h.resolve_left not_mem_chain_round, fun h => Or.inr h⟩

end R

/-! ## Acceptance of the dynamic program -/

/-- The dynamic program of Thm. 4.2.1 accepts. -/
def DPAcc (p : ProbDesc) (allV : List (List Bool)) : Prop :=
  (chainSet allV (dpTab p allV) p.tnI [vecOf (pfacts p) p.init]).any
    (fun w => goalB p (sv (pfacts p) w)) = true

/-- The configuration after the initial guesses. -/
def cfg1 (p : ProbDesc) (g : ℕ → Bool) : Cfg := (cfgInit p).sets (eFields (pfacts p).length) g

theorem cfg1_done (p : ProbDesc) (g : ℕ → Bool) : (cfg1 p g).val fDone = false := by
  rw [cfg1, sets_eFields_val_ne fun j => fDone_ne_fSlot 1 j]
  simp [cfgInit]

@[simp] theorem cfg1_cur (p : ProbDesc) (g : ℕ → Bool) : (cfg1 p g).cur = none := by
  simp [cfg1, cfgInit]

theorem cfg1_vec0 (p : ProbDesc) (g : ℕ → Bool) :
    vecC (pfacts p).length (cfg1 p g) 0 = vecOf (pfacts p) p.init := by
  rw [← vecC_cfgInit]
  exact vecC_congr fun j _ => sets_eFields_val_ne fun j' h => by simp at h

theorem acc_of_good {p : ProbDesc} {allV : List (List Bool)} {g : ℕ → Bool}
    (hg : goalB p (sv (pfacts p) (vecC (pfacts p).length (cfg1 p g) 1)) = true)
    (hG : Good p allV (cfg1 p g)) : DPAcc p allV := by
  rcases hG with hd | ⟨-, hc⟩ | ⟨x, hx, -⟩
  · rw [cfg1_done] at hd; exact absurd hd (by simp)
  · rw [cfg1_vec0] at hc
    exact List.any_eq_true.2 ⟨_, hc, hg⟩
  · simp at hx

theorem length_of_chainX {X : List Trip} {allV : List (List Bool)} {lab : ℕ → Bool × ℕ} {n : ℕ}
    (hall : ∀ v ∈ allV, v.length = n) {l : List ℕ} {u w : List Bool}
    (h : ChainX X allV lab l u w) (hu : u.length = n) : w.length = n := by
  induction h with
  | nil => exact hu
  | cons _ h₁ _ ih => exact ih (hall _ h₁)

theorem good_of_acc {p : ProbDesc} {allV : List (List Bool)}
    (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length) (hacc : DPAcc p allV) :
    ∃ g, goalB p (sv (pfacts p) (vecC (pfacts p).length (cfg1 p g) 1)) = true ∧
      GoodK p allV ((cand p allV).length + 2) (cfg1 p g) := by
  obtain ⟨w, hw, hg⟩ := List.any_eq_true.1 hacc
  have hwl : w.length = (pfacts p).length := by
    obtain ⟨u, hu, hcx⟩ := mem_chainSet.1 hw
    rw [List.mem_singleton] at hu
    exact length_of_chainX (fun v hv => (hall v).1 hv) hcx (by rw [hu, length_vecOf])
  let g : ℕ → Bool := fun x => w.getI (Nat.unpair ((x - 2) / 2)).2
  have hv1 : vecC (pfacts p).length (cfg1 p g) 1 = w := by
    have : vecC (pfacts p).length (cfg1 p g) 1 = (List.range (pfacts p).length).map w.getI := by
      refine List.map_congr_left fun j hj => ?_
      rw [cfg1, Cfg.sets_val, if_pos (show fSlot 1 j ∈ eFields _ from List.mem_map.2 ⟨j, hj, rfl⟩)]
      simp only [g, fSlot]
      rw [show (2 * Nat.pair 1 j + 2 - 2) / 2 = Nat.pair 1 j by omega, Nat.unpair_pair]
    rw [this, HTN.Syn.PolyDom.range_map_getI _ hwl.le, hwl, Nat.sub_self, List.replicate_zero,
      List.append_nil]
  refine ⟨g, by rw [hv1]; exact hg, Or.inr (Or.inl ⟨(cand p allV).length + 1, rfl, by simp, ?_⟩)⟩
  rw [hv1, cfg1_vec0, dpIt, ← dpTab_eq]
  exact hw

/-! ## The descriptions and the list game -/

theorem methods_TO {D : FProbDesc} (hD : SeqMeths D) :
    ∀ m ∈ D.toProblem.methods, m.subtasks.IsTotallyOrdered := by
  rintro m ⟨e, he, rfl⟩
  obtain ⟨c, ls, rfl⟩ := hD e he
  exact seqTn_isTO ls

theorem mpStrong_iff_lrun {D : FProbDesc} (hv : D.Valid) (hD : SeqMeths D)
    {ls : List (Bool × ℕ)} (htn : D.tnI = seqTn ls) :
    D.toProblem.MPStrongSolvable ↔
      ∃ n, D.toProblem.LRunH n (ls.map toLab) {f | f ∈ D.init} Set.univ := by
  have hseq : D.toProblem.tnI.IsSeqNet (List.range ls.length) (ls.map toLab) := by
    have : D.toProblem.tnI = (seqTn ls).toTaskNetwork := by
      simp [FProbDesc.toProblem, htn]
    rw [this]; exact isSeqNet_seqTn ls
  exact Problem.mpStrongSolvable_iff_lrunH (FProbDesc.toProblem_wf hv) (methods_TO hD) hseq

/-- **The acyclic description is strongly solvable iff the dynamic program accepts.** -/
theorem descA_iff (p : ProbDesc) {allV : List (List Bool)}
    (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length)
    (hN : (cand p allV).length + 2 ≤ 2 ^ Nclk p) :
    (descA p).toProblem.MPStrongSolvable ↔ DPAcc p allV := by
  have hv := descA_valid p
  have hA : (descA p).actions = acts (prgs p) := rfl
  have hM := descA_methods p
  have hO := descA_hO p
  have hmeth := seqMeths_descA p
  have hspec := hspec_of p
  have hR := descA_hR p
  have hC := descA_hC p
  have hinit : {f | f ∈ (descA p).init} = (cfgInit p).enc := enc_cfgInit p
  have h0 : (0 : ℕ) < (prgs p).length := by simp [prgs]
  rw [mpStrong_iff_lrun hv hmeth (rfl : (descA p).tnI = _), hinit]
  simp only [List.map_cons, List.map_nil, toLab, if_true, Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨n, h⟩
    have h1 := chain_sound hv hA hM hO hmeth hspec h0 _ 0 (Nat.zero_add _).symm h
    simp only [List.drop_zero, prgs, List.getI_cons_zero, List.map_nil, List.nil_append] at h1
    obtain ⟨g, hg, h2⟩ := mem_wpP_init.1 h1
    refine acc_of_good hg (clk_sound hv hA hM hO hmeth hspec hR hC hall _ le_rfl h2 ?_)
    intro m c' hc'
    rcases m with _ | m
    · exact absurd hc' Problem.not_lrunH_zero_cons
    exact Or.inl ((lrunH_finN hv hA).1 hc').1
  · intro hacc
    obtain ⟨g, hg, hG⟩ := good_of_acc hall hacc
    have hclk := clk_complete hv hA hM hO hmeth hspec hR hC hall (Nclk p) le_rfl (h₀ := 1)
      (xs := [Sum.inl finN]) (Φ := Set.univ)
      (fun c' hc' => (lrunH_finN hv hA).2 ⟨goodK_zero (by
        rwa [show (cand p allV).length + 2 - 2 ^ Nclk p = 0 by omega] at hc'), .nil trivial⟩) hG
    refine ⟨_, chain_complete hv hA hM hO hmeth hspec h0 _ 0 (Nat.zero_add _).symm
      (m := 1 + (2 ^ (Nclk p + 1) - 1) * (2 * Lr p + 4)) ?_⟩
    simp only [List.drop_zero, prgs, List.getI_cons_zero, List.map_nil, List.nil_append]
    exact mem_wpP_init.2 ⟨g, hg, hclk⟩

/-- **The regular description is strongly solvable iff the dynamic program accepts.** -/
theorem descR_iff (p : ProbDesc) {allV : List (List Bool)}
    (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length) :
    (descR p).toProblem.MPStrongSolvable ↔ DPAcc p allV := by
  have hv := descR_valid p
  have hA : (descR p).actions = acts (prgs p) := rfl
  have hM := descR_methods p
  have hO := descR_hO p
  have hmeth := seqMeths_descR p
  have hspec := hspec_of p
  have hR := descR_hR p
  have hinit : {f | f ∈ (descR p).init} = (cfgInit p).enc := enc_cfgInit p
  have h0 : (0 : ℕ) < (prgs p).length := by simp [prgs]
  rw [mpStrong_iff_lrun hv hmeth (rfl : (descR p).tnI = _), hinit]
  simp only [List.map_cons, List.map_nil, toLab, if_true]
  constructor
  · rintro ⟨n, h⟩
    have h1 := chain_sound hv hA hM hO hmeth hspec h0 _ 0 (Nat.zero_add _).symm h
    simp only [List.drop_zero, prgs, List.getI_cons_zero, List.map_cons, List.map_nil, toLab,
      if_true, List.cons_append, List.nil_append] at h1
    obtain ⟨g, hg, h2⟩ := mem_wpP_init.1 h1
    exact acc_of_good hg (loop_sound hv hA hM hO hmeth hspec hR hall _ h2)
  · intro hacc
    obtain ⟨g, hg, hG⟩ := good_of_acc hall hacc
    have hl := loop_complete hv hA hM hO hmeth hspec hR hall _ hG
    refine ⟨_, chain_complete hv hA hM hO hmeth hspec h0 _ 0 (Nat.zero_add _).symm (xs := [])
      (m := ((cand p allV).length + 2 + 1) * (2 * Lr p + 2)) ?_⟩
    simp only [List.drop_zero, prgs, List.getI_cons_zero, List.map_cons, List.map_nil, toLab,
      if_true, List.cons_append, List.nil_append]
    exact mem_wpP_init.2 ⟨g, hg, hl⟩

/-! ## The vectors and the size of the clock -/

/-- All vectors of length `|pfacts p|`. -/
def allVp (p : ProbDesc) : List (List Bool) :=
  allVecs (pfacts p) (List.replicate (2 ^ (pfacts p).length) true)

theorem mem_allVp {p : ProbDesc} {v : List Bool} : v ∈ allVp p ↔ v.length = (pfacts p).length :=
  mem_allVecs (by simp)

theorem length_allVp_le (p : ProbDesc) : (allVp p).length ≤ 2 ^ (pfacts p).length := by
  unfold allVp allVecs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem length_cand (p : ProbDesc) (allV : List (List Bool)) :
    (cand p allV).length = allV.length * (2 * (numsOf p).length * allV.length) := by
  simp [cand, namesB, List.length_flatMap, List.map_const', List.sum_replicate, mul_comm]

theorem cand_bound (p : ProbDesc) : (cand p (allVp p)).length + 2 ≤ 2 ^ Nclk p := by
  rw [length_cand]
  have ha := length_allVp_le p
  set a := (allVp p).length
  set n := (pfacts p).length
  set b := (numsOf p).length
  have hb : 2 * b ≤ 2 ^ (2 * b) := by
    have := Nat.lt_two_pow_self (n := b)
    have h2 : 2 ^ (2 * b) = 2 ^ b * 2 ^ b := by rw [two_mul, pow_add]
    rw [h2]; nlinarith [Nat.one_le_two_pow (n := b)]
  have hN : 2 ^ Nclk p = 2 ^ n * 2 ^ n * 2 ^ (2 * b) * 4 := by
    simp only [Nclk]
    rw [show 2 * n + 2 * b + 2 = n + n + 2 * b + 2 by ring, pow_add, pow_add, pow_add]
    norm_num
  rw [hN]
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h3 : 1 ≤ 2 ^ (2 * b) := Nat.one_le_two_pow
  have : a * (2 * b * a) ≤ 2 ^ n * 2 ^ n * 2 ^ (2 * b) := by
    calc a * (2 * b * a) = (a * a) * (2 * b) := by ring
      _ ≤ (2 ^ n * 2 ^ n) * 2 ^ (2 * b) := Nat.mul_le_mul (Nat.mul_le_mul ha ha) hb
  nlinarith [Nat.mul_le_mul h1 h1]

/-! ## Correctness of the reductions -/

theorem hTO_of_isTO {p : ProbDesc} (hto : p.toProblem.IsTO) :
    ∀ e ∈ p.methods, p.toProblem.toPos.ReachableName e.1 → e.2.toTaskNetwork.IsTotallyOrdered :=
  fun e he hr => hto.2 _ ⟨(⟨e, he, rfl⟩ : ∃ e' ∈ p.methods, e'.toMethod = e.toMethod), hr⟩

theorem solvable_iff_dpAcc {p : ProbDesc} (hp : p.Valid) (hto : p.toProblem.IsTO) :
    p.toProblem.Solvable ↔ DPAcc p (allVp p) :=
  dp_iff hp (fun _ => mem_allVp) (hTO_of_isTO hto) hto.1

/-- **Correctness, acyclic construction.** -/
theorem descA_solvable_iff {p : ProbDesc} (hp : p.Valid) (hto : p.toProblem.IsTO) :
    (descA p).toProblem.MPStrongSolvable ↔ p.toProblem.Solvable := by
  rw [solvable_iff_dpAcc hp hto]
  exact descA_iff p (fun _ => mem_allVp) (cand_bound p)

/-- **Correctness, regular construction.** -/
theorem descR_solvable_iff {p : ProbDesc} (hp : p.Valid) (hto : p.toProblem.IsTO) :
    (descR p).toProblem.MPStrongSolvable ↔ p.toProblem.Solvable := by
  rw [solvable_iff_dpAcc hp hto]
  exact descR_iff p (fun _ => mem_allVp)

/-! ## The reductions -/

theorem pt_classTOB : PT classTOB :=
  (PT.and (pt_toB.comp (PT.fst.comp (PT.snd.comp PT.snd)))
    (pt_methodsRB pt_toB PT.id pt_reachSetB)).of_eq fun _ => rfl

theorem validB_classTOB_iff (p : ProbDesc) :
    (validB p && classTOB p) = true ↔ p.Valid ∧ p.toProblem.IsTO := by
  rw [Bool.and_eq_true, validB_iff]
  exact ⟨fun ⟨hp, hc⟩ => ⟨hp, (classTOB_iff hp).1 hc⟩, fun ⟨hp, hc⟩ => ⟨hp, (classTOB_iff hp).2 hc⟩⟩

/-- The reduction: totally ordered well-formed descriptions are translated by `d`, the others
mapped to `badDesc`. -/
def redTO (d : ProbDesc → FProbDesc) (p : ProbDesc) : FProbDesc :=
  bif validB p && classTOB p then d p else badDesc

theorem pt_redTO {d : ProbDesc → FProbDesc} (hd : PT d) : PT (redTO d) :=
  PT.cond (PT.and pt_validB pt_classTOB) hd (PT.const badDesc)

theorem redP_TO {d : ProbDesc → FProbDesc} (hd : PT d) {Y : FClass}
    (hv : ∀ p, (d p).Valid) (hY : ∀ p, Y (d p).toProblem)
    (hs : ∀ p, p.Valid → p.toProblem.IsTO →
      ((d p).toProblem.MPStrongSolvable ↔ p.toProblem.Solvable)) :
    Cx.RedP (PlanEx fun P => P.IsTO) (PlanExMP .strong Y) := by
  refine redP_codeLang (pt_redTO hd) (fun p => ?_) badDesc (fun h => badDesc_not_valid h.1)
  cases hb : (validB p && classTOB p)
  · have hn : ¬ (p.Valid ∧ p.toProblem.IsTO) := fun h => by
      rw [← validB_classTOB_iff] at h; rw [h] at hb; exact Bool.false_ne_true hb.symm
    simp only [redTO, hb, cond_false]
    exact ⟨fun h => absurd ⟨h.1, h.2.1⟩ hn, fun h => absurd h.1 badDesc_not_valid⟩
  · obtain ⟨hp, hto⟩ := (validB_classTOB_iff p).1 hb
    simp only [redTO, hb, cond_true]
    exact ⟨fun ⟨_, _, h⟩ => ⟨hv p, hY p, (hs p hp hto).2 h⟩,
      fun ⟨_, _, h⟩ => ⟨hp, hto, (hs p hp hto).1 h⟩⟩

end HardMP

/-! ## The theorems -/

open HardMP HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-- **[CB22, Thm. 1], hardness**: strong method-based plan existence of acyclic totally ordered
problems is EXPTIME-hard (new reduction from totally ordered HTN planning). -/
theorem hard_ACYC_TO_mpStrong :
    Cx.Hard Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.ACYC FClass.TO)) :=
  HTN.Article.thm_4_3_6.of_redP (redP_TO pt_descA descA_valid
    (fun p => ⟨descA_ACYC p, descA_TO p⟩) fun _ hp hto => descA_solvable_iff hp hto)

/-- **[CB22, Thm. 4], hardness**: tail-recursive totally ordered problems. -/
theorem hard_TR_TO_mpStrong :
    Cx.Hard Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.TR FClass.TO)) :=
  HTN.Article.thm_4_3_6.of_redP (redP_TO pt_descA descA_valid
    (fun p => ⟨descA_TR p, descA_TO p⟩) fun _ hp hto => descA_solvable_iff hp hto)

/-- **[CB22, Thm. 3], hardness**: strong method-based plan existence of regular problems is
EXPTIME-hard (even for totally ordered ones). -/
theorem hard_REG_TO_mpStrong :
    Cx.Hard Cx.EXPTIME (PlanExMP .strong (FClass.inter FClass.REG FClass.TO)) :=
  HTN.Article.thm_4_3_6.of_redP (redP_TO pt_descR descR_valid
    (fun p => ⟨descR_REG p, descR_TO p⟩) fun _ hp hto => descR_solvable_iff hp hto)

/-- **[CB22, Thm. 3], hardness.** -/
theorem hard_REG_mpStrong : Cx.Hard Cx.EXPTIME (PlanExMP .strong FClass.REG) :=
  HTN.Article.thm_4_3_6.of_redP (redP_TO pt_descR descR_valid descR_REG
    fun _ hp hto => descR_solvable_iff hp hto)

end FOND
