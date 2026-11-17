import FondHtn.StrongOD.RegComplete
/-!
# Strong OD plan existence of regular problems is in EXPSPACE ([CB21, Thm. 5.3], membership)

For the class `REGtn` of [CB21, Def. 3.3] (the initial task network is regular too):

* **`FOND.strongOD_REGtn_mem`** — `PlanExFM strongOD REGtn ∈ EXPSPACE`.

Proof: strong OD solvability is the existence of a belief-set sequence
(`FOND.SOD.strongOD_iff_nw`, built on the sequential composition `FOND.SOD.bsw_comp`).  The
nondeterministic exponential-space search of `FondHtn/StrongOD/RegSearch.lean` guesses the
methods and the belief sets (explicit lists of states) and checks every block state by state by
a depth-first evaluation of the block game; `HTN.Syn.PolyDom.inExpSpace_codeLang_of_search`
(Savitch) gives the bound.  Soundness: `FOND.SOD.rsearch_sound`; completeness:
`FOND.SOD.nw_run`, `FOND.SOD.block_run`.

**Remark (Bercher's `REG` without a regular initial network).**  For `FClass.REG` the initial
task network may contain several compound tasks, each the root of its own regular chain.  An OD
policy may then interleave the blocks of different chains, so the solution is no longer a
sequence of blocks `B₀ ≺ B₁ ≺ …` and belief-set sequences do not describe it; e.g. with
`tn_I = {c₁, c₂}` unordered, the chains of `c₁` and `c₂` progress independently, and a
strategy may have to react in the chain of `c₂` to an outcome observed in the chain of `c₁`.
A configuration would have to record one belief *relation* over the tuple of current chain
positions instead of a single name and belief set, which is not covered by the argument here.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Article.NoHTN PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

variable {p : FProbDesc}

/-! ## The certificate -/

theorem reach_strongDesc {c : ℕ} (h : Reach p c) :
    (strongDesc p).toProblem.toPos.ReachableName c := by
  induction h with
  | tnI ht hc => exact .tnI ht hc
  | method hm _ ht hc ih => exact .method hm ih ht hc

theorem hREG_of (hp : p.Valid) (hM : FClass.REG p.toProblem) :
    ∀ e ∈ p.methods, Reach p e.1 → regB e.2 = true :=
  fun e he hr => (regB_iff (hp.methods e he)).2 (hM e.toMethod ⟨⟨e, he, rfl⟩, hr⟩)

theorem exists_regCert (hp : p.Valid) (hM : FClass.REG p.toProblem) :
    ∃ R, regCertB p R = true ∧ sz R ≤ (sz p + 4) * (2 * (sz p + 4) + 2) + 1 := by
  classical
  have hREG := hREG_of hp hM
  have hsv := strongDesc_valid hp
  let R := (numsOf (skel p)).dedup.filter fun c => decide (Reach p c)
  have hR : ∀ c, Reach p c → c ∈ R := fun c hc =>
    List.mem_filter.2 ⟨List.mem_dedup.2 (reach_numsOf hsv (reach_strongDesc hc)), by simpa using hc⟩
  have hRr : ∀ c ∈ R, Reach p c := fun c hc => by simpa using (List.mem_filter.1 hc).2
  have hRN : ∀ c ∈ R, c ∈ numsOf (skel p) := fun c hc =>
    List.mem_dedup.1 (List.mem_filter.1 hc).1
  have hRl : R.length ≤ (numsOf (skel p)).length :=
    (List.length_filter_le _ _).trans (List.dedup_sublist _).length_le
  refine ⟨R, ?_, ?_⟩
  · simp only [regCertB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨⟨⟨fun x hx => ?_, fun e he => ?_⟩, hRN⟩, hRl⟩
    · cases hb : (lblOf p.tnI x).1
      · exact Or.inl rfl
      · exact Or.inr (hR _ (reach_compL_d₀ (mem_compL.2 ⟨x, hx, lblOf_eq_of_fst hb⟩)))
    · by_cases he1 : e.1 ∈ R
      · refine Or.inr ⟨hREG e he (hRr _ he1), fun z hz => ?_⟩
        cases hb : (lblOf e.2 z).1
        · exact Or.inl rfl
        · exact Or.inr (hR _ (reach_compL_method he (hRr _ he1)
            (mem_compL.2 ⟨z, hz, lblOf_eq_of_fst hb⟩)))
      · exact Or.inl he1
  · have hsk := sz_skel_le p
    have hN := length_numsOf_le (skel p)
    have h := sz_list_le R (sz (skel p)) fun c hc => sz_le_of_mem_numsOf (hRN c hc)
    have := Nat.mul_le_mul (show R.length ≤ sz p + 4 by omega)
      (show 2 * sz (skel p) + 2 ≤ 2 * (sz p + 4) + 2 by omega)
    omega

/-! ## The size bound -/

/-- The exponent. -/
noncomputable def qR : Polynomial ℕ := 6 * Polynomial.X + 20

theorem eval_qR (n : ℕ) : qR.eval n = 6 * n + 20 := by simp [qR]

theorem sz_sublists_le (U : List ℕ) : sz U.sublists ≤ 2 ^ U.length * (2 * sz U + 2) + 1 := by
  have h := sz_list_le U.sublists (sz U) fun w hw =>
    sz_le_of_sublist' (List.mem_sublists.1 hw)
  rw [List.length_sublists] at h
  exact h

theorem cfgB_lt {R : List ℕ} (hR : sz R ≤ (sz p + 4) * (2 * (sz p + 4) + 2) + 1) :
    cfgB p R < 2 ^ qR.eval (sz p) := by
  rw [eval_qR]
  set n := sz p with hn
  set M := n + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hU := sz_factsU_le p
  have hUl : (factsU p).length ≤ 2 * n := (length_le_sz _).trans hU
  have hsub := sz_sublists_le (factsU p)
  have hpow : 2 ^ (factsU p).length ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) hUl
  have hls : lsB p ≤ 2 ^ (2 * n) * (12 * M) := by
    unfold lsB
    have h1 : 2 ^ (factsU p).length * (2 * sz (factsU p) + 2) ≤ 2 ^ (2 * n) * (4 * M) :=
      Nat.mul_le_mul hpow (by omega)
    have h2 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have h3 : 8 * M ≤ 2 ^ (2 * n) * (8 * M) := Nat.le_mul_of_pos_left _ h2
    linarith
  have hcfg : cfgBound n ≤ 20 * M ^ 2 := by unfold cfgBound; nlinarith
  have hB' : n * (2 * cfgBound n + 2) + 1 ≤ 43 * M ^ 3 := by
    have : n * (2 * cfgBound n + 2) ≤ M * (40 * M ^ 2 + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hdc : dfsCost (n * (2 * cfgBound n + 2) + 1) (4 * n + 1) ≤ 483 * M ^ 4 := by
    unfold dfsCost
    have h1 : (n * (2 * cfgBound n + 2) + 1) * (4 * n + 1) ≤ 43 * M ^ 3 * (4 * M) :=
      Nat.mul_le_mul hB' (by omega)
    have h2 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by norm_num)
    have h3 : M ≤ M ^ 4 := by
      calc M = M ^ 1 := (pow_one M).symm
        _ ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by norm_num)
    have h4 : 1 ≤ M ^ 4 := Nat.one_le_pow _ _ hM1
    have e : 43 * M ^ 3 * (4 * M) = 172 * M ^ 4 := by ring
    nlinarith
  have hst : stackBound n ≤ 1000 * M ^ 5 := by
    unfold stackBound
    have h1 : 2 * n * dfsCost (n * (2 * cfgBound n + 2) + 1) (4 * n + 1) ≤ 2 * M * (483 * M ^ 4) :=
      Nat.mul_le_mul (by omega) hdc
    have e : 2 * M * (483 * M ^ 4) = 966 * M ^ 5 := by ring
    have h2 : M ^ 2 ≤ M ^ 5 := Nat.pow_le_pow_right hM1 (by norm_num)
    have h3 : M ≤ M ^ 5 := by
      calc M = M ^ 1 := (pow_one M).symm
        _ ≤ M ^ 5 := Nat.pow_le_pow_right hM1 (by norm_num)
    have h4 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ hM1
    nlinarith
  have hcc : ccB n ≤ 5 * M ^ 2 := by unfold ccB; nlinarith
  have hR' : sz R ≤ 61 * M ^ 2 := by nlinarith
  have hM25 : M ^ 2 ≤ M ^ 5 := Nat.pow_le_pow_right hM1 (by norm_num)
  have hM5 : M ^ 5 ≤ 2 ^ (5 * M) := by
    have := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := M)).le 5
    rw [← pow_mul, mul_comm] at this; exact this
  have hMp : M ≤ 2 ^ M := (Nat.lt_two_pow_self).le
  have hA : 1100 * M ^ 5 ≤ 2 ^ (5 * n + 16) := by
    have : 2 ^ (5 * n + 16) = 2 ^ 11 * 2 ^ (5 * M) := by rw [← pow_add]; congr 1; omega
    rw [this]
    exact Nat.mul_le_mul (by norm_num) hM5
  have hB2 : 36 * M * 2 ^ (2 * n) ≤ 2 ^ (5 * n + 16) := by
    have h1 : 36 * M * 2 ^ (2 * n) ≤ 2 ^ 6 * 2 ^ M * 2 ^ (2 * n) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (by norm_num) hMp)
    have : 2 ^ 6 * 2 ^ M * 2 ^ (2 * n) = 2 ^ (3 * n + 7) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this] at h1
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfin : 2 ^ (5 * n + 16) + 2 ^ (5 * n + 16) < 2 ^ (6 * n + 20) := by
    have : 2 ^ (5 * n + 16) + 2 ^ (5 * n + 16) = 2 ^ (5 * n + 17) := by rw [pow_succ]; ring
    rw [this]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold cfgB
  have e1 : 3 * (2 ^ (2 * n) * (12 * M)) = 36 * M * 2 ^ (2 * n) := by ring
  nlinarith

end SOD

open SOD in
/-- **[CB21, Thm. 5.3], membership**: strong OD plan existence of regular problems (with a
regular initial task network) is in EXPSPACE. -/
theorem strongOD_REGtn_mem : Cx.EXPSPACE (PlanExFM .strongOD FClass.REGtn) := by
  refine inExpSpace_codeLang_of_search (α := FProbDesc) (σ := RCfg)
    (Q := fun p => p.Valid ∧ FClass.REGtn p.toProblem ∧ FMCrit.Solvable .strongOD p.toProblem)
    pt_rinit pt_rstep pt_racc qR fun p => ⟨?_, ?_⟩
  · rintro ⟨hp, ⟨hM, hreg0⟩, hs⟩
    have hreg0' : regB p.tnI = true := (regB_iff hp.tnI).2 hreg0
    have hREG := hREG_of hp hM
    obtain ⟨R, hcert, hRsz⟩ := exists_regCert hp hM
    have hL := cfgB_lt hRsz
    obtain ⟨S', hS', hn⟩ := (strongOD_iff_nw hp hREG hreg0').1 hs
    set S₁ := S' ∩ PU p with hS₁
    have hS₁U : S₁ ⊆ PU p := Set.inter_subset_right
    have hd0 : sz (primD (d₀ p)) ≤ sz p := (sz_primD_le _).trans (sz_d₀_le p)
    have hc0 : sz (compL (d₀ p)) ≤ ccB (sz p) := (sz_compL_le _).trans (ccB_mono (sz_d₀_le p))
    have hS₁sz : sz (rep p S₁) ≤ lsB p := (sz_rep_le S₁).trans (by unfold lsB; omega)
    have hnil : sz ([] : List (List ℕ)) ≤ lsB p := by rw [sz_nil]; unfold lsB; omega
    have hnilc : sz ([] : List ℕ) ≤ ccB (sz p) := by rw [sz_nil]; unfold ccB; omega
    have hnil' : sz ([] : List (ℕ × GCfg)) ≤ stackBound (sz p) := by
      rw [sz_nil]; unfold stackBound; omega
    have hinit : sz [p.init.dedup] ≤ lsB p := by
      rw [sz_cons, sz_nil]
      have := (sz_dedup_le p.init).trans (sz_init_le p)
      unfold lsB; omega
    have hU0 : ∀ f ∈ p.init.dedup, f ∈ factsU p := fun f hf =>
      List.mem_append_left _ (List.mem_dedup.1 hf)
    obtain ⟨z, hz, hza⟩ := nw_run hL hp hn S₁ Set.inter_subset_left hS₁U (primD (d₀ p)) hd0 hc0
    refine ⟨(R, (1, [], [], primD (d₀ p), compL (d₀ p), rep p S₁, [p.init.dedup], [])), z,
      lt_of_le_of_lt (sz_cfg_le (Nat.le_refl 1) hnilc hnil hd0 hc0 hS₁sz hinit hnil') hL,
      (rinit_iff p _).2 ⟨hp, hreg0', hcert, rfl⟩, ?_, hza⟩
    refine (block_run hL hnilc hnil hd0 hc0 hS₁sz (fun s hs => inv_primD (inv_d₀ hp) hs) _
      (fun w hw => ?_) hinit).trans ?_
    · rw [List.mem_singleton] at hw
      subst hw
      refine ⟨hU0, ?_⟩
      have h1 := bsw_restrictU hS' (fun f hf => List.mem_append_left _ hf)
      rw [setW_rep hS₁U, setOf_mem_dedup]
      exact h1
    · have hfin : finB (1, [], [], primD (d₀ p), compL (d₀ p), rep p S₁, [], [])
          (0, compL (d₀ p), rep p S₁, primD (d₀ p), compL (d₀ p), rep p S₁, [], []) = true := by
        simp [finB]
      exact Relation.ReflTransGen.head ⟨lt_of_le_of_lt (sz_cfg_le (Nat.zero_le 1) hc0 hS₁sz hd0
        hc0 hS₁sz hnil hnil') hL, by simp [rstep, hfin]⟩ hz
  · rintro ⟨c₀, c, -, hi, hr, ha⟩
    exact rsearch_sound (Rel := fun c c' => sz c' < 2 ^ qR.eval (sz p) ∧ rstep (p, c, c') = true)
      (fun _ _ h => h.2) hi hr ha
end FOND
