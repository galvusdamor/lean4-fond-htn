import HtnComplexity.Article.AcycNExp
/-!
# Acyclic problems of bounded height, and acyclic regular problems, are in NP

* **`HTN.Article.cor_4_2_8`** (Cor. 4.2.8) — for a fixed `h`, `PlanEx^{ACYC_h}_htn ∈ NP`.  A
  `≤₀`-stratification is a total order of the reachable names, so height `≤ h` means at most `h`
  reachable compound names; ranks are below `h` and trees have at most `(B + 1) ^ h` nodes, a
  polynomial.  The certificate of Thm. 4.2.5 is checked together with `|R| ≤ h` for a duplicate-free
  list `R` of names.
* **`HTN.Article.lem_4_2_11`**, **`HTN.Article.lem_4_2_11_TO`** (Lem. 4.2.11) —
  `PlanEx^{ACYC ∩ REG}_htn ∈ NP` and `PlanEx^{ACYC ∩ REG ∩ TO}_htn ∈ NP`.  **The article's proof
  does not work**: it claims that an acyclic regular problem has a `≤₀`-stratification of height
  one (via Thm. 3.0.1, which is about `≤_r`-stratifications) and applies Cor. 4.2.8 — but a
  `≤₀`-stratification orders the reachable names totally, so its height is the number of reachable
  names (the regular chain `A₁ → a A₂ → … → a Aₙ` has height `n`).  The claim holds anyway: in a
  regular problem every method has at most one compound task, so a decomposition tree is a
  *caterpillar* — a path of compound nodes with primitive leaves hanging off — of at most
  `(r + 1)(B + 1) + 1` nodes for a root of rank `r` (`HTN.Article.size_le_of_reg`), a polynomial.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-! ### Polynomial bounds -/

theorem one_le_sz_list {β : Type} [BEnc β] (l : List β) : 1 ≤ sz l := by
  cases l with
  | nil => simp [sz_nil]
  | cons a l => rw [sz_cons]; omega

theorem one_le_sz_probDesc (p : ProbDesc) : 1 ≤ sz p := by
  have := sz_probDesc p
  have := one_le_sz_list p.actions
  omega

theorem kidOf_lt {l : List (ℕ × ℕ)} {K : ℕ} (h : ∀ q ∈ l, q.2 < K) (hK : 0 < K) (x : ℕ) :
    kidOf l x < K := by
  unfold kidOf
  rcases hl : l.lookup x with _ | k
  · simpa using hK
  · exact h _ (mem_of_lookup_eq_some hl)

/-- The size of a certificate of polynomially many tree nodes. -/
theorem sz_acycTreeCert_le {p : ProbDesc} {R : List ℕ} {rkL : List (ℕ × ℕ)} {c : TCert} {Y T : ℕ}
    (hRN : ∀ c ∈ R, c ∈ numsOf p) (hRl : R.length ≤ (numsOf p).length)
    (hrkN : ∀ q ∈ rkL, q.1 ∈ numsOf p ∧ q.2 ≤ (numsOf p).length)
    (hrkl : rkL.length ≤ (numsOf p).length)
    (hc : sz c ≤ 64 * (c.1.length + Y + sz p + 1) ^ 3) (hY : Y ≤ c.1.length) (hN : c.1.length ≤ T)
    {j : ℕ} (hj : 1 ≤ j) (hT : T ≤ (sz p + 1) ^ j) :
    sz ((R, rkL), c) ≤ (sz p + 1) ^ (3 * j + 13) := by
  set S := sz p with hS
  have hS1 : 1 ≤ S := one_le_sz_probDesc p
  have hK : (numsOf p).length ≤ S := length_numsOf_le p
  set Z := (S + 1) ^ j with hZ
  have hZ1 : S + 1 ≤ Z := by
    calc S + 1 = (S + 1) ^ 1 := (pow_one _).symm
      _ ≤ Z := Nat.pow_le_pow_right (by omega) hj
  have hR : sz R ≤ R.length * (2 * S + 2) + 1 := sz_list_le fun a ha => sz_le_of_mem_numsOf (hRN a ha)
  have hrkS : sz rkL ≤ rkL.length * (2 * (S + (2 * (S + 1) + 1)) + 2) + 1 :=
    sz_list_le fun q hq => by
      rw [sz_prod]
      have := sz_le_of_mem_numsOf (hrkN q hq).1
      have := sz_nat_le_of_lt' (show q.2 < S + 1 by have := (hrkN q hq).2; omega)
      omega
  have e1 : R.length * (2 * S + 2) ≤ Z * (2 * Z) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : rkL.length * (2 * (S + (2 * (S + 1) + 1)) + 2) ≤ Z * (8 * Z) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hM : c.1.length + Y + sz p + 1 ≤ 4 * Z := by rw [← hS]; omega
  have hM3 : (c.1.length + Y + sz p + 1) ^ 3 ≤ 64 * Z ^ 3 :=
    (Nat.pow_le_pow_left hM 3).trans_eq (by ring)
  have hZ3 : Z * Z ≤ Z ^ 3 := by
    rw [show Z ^ 3 = Z * Z * Z by ring]; exact Nat.le_mul_of_pos_right _ (by omega)
  have htot : sz ((R, rkL), c) ≤ 8192 * Z ^ 3 := by
    rw [sz_prod, sz_prod]
    have : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h13 : 8192 ≤ (S + 1) ^ 13 :=
    calc 8192 = 2 ^ 13 := by norm_num
      _ ≤ (S + 1) ^ 13 := Nat.pow_le_pow_left (by omega) 13
  calc sz ((R, rkL), c) ≤ 8192 * Z ^ 3 := htot
    _ ≤ (S + 1) ^ 13 * Z ^ 3 := Nat.mul_le_mul_right _ h13
    _ = (S + 1) ^ (3 * j + 13) := by rw [hZ, ← pow_mul, ← pow_add]; ring_nf

/-! ### Corollary 4.2.8 -/

/-- The strict order of a certificate. -/
def certLt (rk : ℕ → ℕ) (c c' : ℕ) : Prop := certLe rk c c' ∧ c ≠ c'

theorem certLe_antisymm {rk : ℕ → ℕ} {a b : ℕ} (h₁ : certLe rk a b) (h₂ : certLe rk b a) : a = b := by
  unfold certLe at h₁ h₂; omega

theorem certLe_trans {rk : ℕ → ℕ} {a b c : ℕ} (h₁ : certLe rk a b) (h₂ : certLe rk b c) :
    certLe rk a c := by
  unfold certLe at *; omega

theorem certLe_total (rk : ℕ → ℕ) (a b : ℕ) : certLe rk a b ∨ certLe rk b a := by
  unfold certLe; omega

open Classical in
/-- **A certificate with at most `h` names gives a stratification of height at most `h`.** -/
theorem AcycCert.isACYC_h {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} (h : AcycCert p R rk)
    (hnd : R.Nodup) {k : ℕ} (hk : R.length ≤ k) : p.toProblem.IsACYC_h k := by
  refine ⟨certLe rk, h.strat0, fun c => (R.toFinset.filter fun c' => certLt rk c' c).card,
    fun c hc => ?_, fun c c' hc hc' => ?_⟩
  · have hcR := h.reach_mem hc
    refine lt_of_lt_of_le (Finset.card_lt_card ((Finset.ssubset_iff_of_subset
      (Finset.filter_subset _ _)).2 ⟨c, List.mem_toFinset.2 hcR, fun h' => ?_⟩)) ?_
    · exact (Finset.mem_filter.1 h').2.2 rfl
    · rw [List.toFinset_card_of_nodup hnd]; exact hk
  · constructor
    · intro hle
      refine Finset.card_le_card fun c'' hc'' => ?_
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hc''
      refine Finset.mem_filter.2 ⟨h1, certLe_trans h2 hle, fun e => h3 ?_⟩
      subst e
      exact certLe_antisymm h2 hle
    · intro hf
      by_contra hle
      have hlt : certLt rk c' c := ⟨(certLe_total rk c c').resolve_left hle,
        fun e => hle (e ▸ Or.inr ⟨rfl, le_rfl⟩)⟩
      have : (R.toFinset.filter fun c'' => certLt rk c'' c') ⊂
          (R.toFinset.filter fun c'' => certLt rk c'' c) := by
        refine (Finset.ssubset_iff_of_subset fun c'' hc'' => ?_).2
          ⟨c', Finset.mem_filter.2 ⟨List.mem_toFinset.2 (h.reach_mem hc'), hlt⟩,
            fun h' => (Finset.mem_filter.1 h').2.2 rfl⟩
        obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hc''
        refine Finset.mem_filter.2 ⟨h1, certLe_trans h2 hlt.1, fun e => h3 ?_⟩
        subst e
        exact certLe_antisymm h2 hlt.1
      have := Finset.card_lt_card this
      beta_reduce at hf
      omega

open Classical in
/-- At most `h` names are reachable in a problem of height at most `h`. -/
theorem length_le_of_isACYC_h {p : ProbDesc} {R : List ℕ} (hnd : R.Nodup)
    (hR : ∀ c ∈ R, p.toProblem.toPos.ReachableName c) {k : ℕ} (h : p.toProblem.IsACYC_h k) :
    R.length ≤ k := by
  obtain ⟨le, hle, f, hf, hfle⟩ := h
  rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_range k]
  refine Finset.card_le_card_of_injOn f (fun c hc => ?_) (fun c hc c' hc' e => ?_)
  · exact Finset.mem_range.2 (hf c (hR c (List.mem_toFinset.1 hc)))
  · have h1 := hR c (List.mem_toFinset.1 hc)
    have h2 := hR c' (List.mem_toFinset.1 hc')
    exact hle.antisymm c c' h1 h2 ((hfle c c' h1 h2).2 e.le) ((hfle c' c h2 h1).2 e.ge)

/-- **The check of Cor. 4.2.8.** -/
def acycHB (k : ℕ) (x : ProbDesc × AcycTreeCert) : Bool :=
  acycTreeB x && nodupB x.2.1.1 && decide (x.2.1.1.length ≤ k)

theorem pt_acycHB (k : ℕ) : PT (acycHB k) := by
  have hR : PT fun x : ProbDesc × AcycTreeCert => x.2.1.1 := PT.fst.comp (PT.fst.comp PT.snd)
  refine (PT.and (PT.and pt_acycTreeB (pt_nodupB hR)) (PT.le (PT.length hR) (PT.const k))).of_eq
    fun x => ?_
  rfl

/-- **Corollary 4.2.8.** For a fixed height `h`, `PlanEx^{ACYC_h}_htn ∈ NP`. -/
theorem cor_4_2_8 (k : ℕ) : Cx.NP (PlanEx fun P => P.IsACYC_h k) := by
  have h := inNP_codeLang (α := ProbDesc) (β := AcycTreeCert)
    (Q := fun p => p.Valid ∧ p.toProblem.IsACYC_h k ∧ p.toProblem.Solvable) (pt_acycHB k) (3 * (k + 1) + 13)
    fun p => ⟨fun ⟨hp, hac, hsol⟩ => ?_, fun ⟨b, _, hb⟩ => ?_⟩
  · exact h
  · -- completeness
    obtain ⟨trees, π, s, hTY, hrun, hg⟩ :=
      (Problem.solvable_iff_trees p.toProblem (wf_toProblem p)).1 hsol
    obtain ⟨R, rkL, hab, hRN, hRl, hrkN, hrkl, hnd, hRr, hrR, hrkR⟩ :=
      exists_acycCert hp (by obtain ⟨le, hle, -⟩ := hac; exact ⟨le, hle⟩)
    have hRk := length_le_of_isACYC_h hnd hRr hac
    have hcert := (acycB_iff p R rkL).1 hab
    obtain ⟨c, hcB, hcπ, hclen, hnodes, hroots, hrl, hw, hwl, hπN⟩ := exists_certB hp hTY
    set S := sz p with hS
    refine ⟨((R, rkL), c), ?_, ?_⟩
    · have htree : ∀ x ∈ p.tnI.ids, (trees x).size ≤ (S + 1) ^ k := by
        intro x hx
        have hxT : x ∈ p.toProblem.tnI.T := by
          simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
        have := size_le_of_acycCert hcert methods_ids_le (trees x) _ (hTY.1 x hxT) (fun c hc =>
          hcert.reach_mem (HTN.Problem.ReachableName.tnI (P := p.toProblem.toPos) hxT hc))
        refine this.trans (Nat.pow_le_pow_right (by omega) ?_)
        rcases hα : p.toProblem.tnI.α x with a | c'
        · simp
        · have hc'R : c' ∈ R := hrR c' (HTN.Problem.ReachableName.tnI hxT hα)
          have := kidOf_lt hrkR (List.length_pos_of_mem hc'R) c'
          simp only [Sum.elim_inr]; omega
      have hids : p.tnI.ids.length ≤ S := (ids_length_le_sz _).trans (by
        have := sz_probDesc p
        omega)
      have hN : c.1.length ≤ (S + 1) ^ (k + 1) := by
        rw [hclen]
        have := List.sum_le_card_nsmul (p.tnI.ids.map fun x => (trees x).size) ((S + 1) ^ k)
          (fun n hn => by
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
            exact htree x hx)
        rw [List.length_map, smul_eq_mul] at this
        rw [pow_succ]
        refine this.trans ((Nat.mul_le_mul_right _ hids).trans ?_)
        rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      have hY : π.length ≤ c.1.length := by
        have := length_le_of_treesYield hTY
        rw [show p.toProblem.tnI.T = p.tnI.ids.toFinset from rfl,
          List.sum_toFinset _ hp.tnI.nodup] at this
        rw [hclen]; exact this
      have hc := sz_cert_le (Y := π.length) hnodes hroots hrl hw hwl (by rw [hcπ])
        (by rw [hcπ]; exact hπN)
      exact sz_acycTreeCert_le hRN hRl hrkN hrkl hc hY hN (by omega) le_rfl
    · simp only [acycHB, acycTreeB, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨(validB_iff p).2 hp, hab⟩, hcB⟩, ?_⟩, (nodupB_iff _).2 hnd⟩, hRk⟩
      rw [hcπ]
      exact (runB_iff p π).2 ⟨s, hrun, hg⟩
  · -- soundness
    simp only [acycHB, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hb1, hnd⟩, hk⟩ := hb
    obtain ⟨hv, -, hsol⟩ := of_acycTreeB hb1
    obtain ⟨⟨⟨-, ha⟩, -⟩, -⟩ := by simpa only [acycTreeB, Bool.and_eq_true] using hb1
    obtain ⟨R, rkL⟩ := b.1
    exact ⟨hv, ((acycB_iff p _ _).1 ha).isACYC_h ((nodupB_iff _).1 hnd) hk, hsol⟩

end Article

end HTN
