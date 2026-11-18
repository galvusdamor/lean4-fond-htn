import HtnComplexity.Article.AcycCert
import HtnComplexity.Article.RunCheck
import HtnComplexity.Article.Valid
import HtnPlanning.Article.ToSyn
/-!
# Acyclic HTN planning is in NEXPTIME (Thm. 4.2.5)

The proof of the article guesses a decomposition: in an acyclic problem every decomposition tree
has height at most the number of compound names, hence at most exponentially many nodes
(Lem. 4.2.4), and a guessed tree certificate can be checked in time polynomial in its size.

Here the certificate is a pair: an acyclicity certificate (`HTN.Article.AcycCert`: the reachable
names and their ranks, deciding the class membership `ACYC`) and a tree certificate
(`HTN.Article.TCert`: the trees, the plan and the merge witnesses).  The check
`HTN.Article.acycTreeB` — well-formedness, acyclicity, trees, execution — is polynomial time, and a
problem in the language has a certificate whose code is shorter than `2 ^ q(|p|)`,
`q(n) = 3n² + 9n + 19`: the trees have at most `|p| · (|p| + 1) ^ (|p| + 1)` nodes
(`HTN.Article.size_le_of_acycCert`), the plan is not longer, and a certificate of `N` nodes for a
plan of length `Y` has a code of length at most `64 (N + Y + |p| + 1)³`.

* **`HTN.Article.thm_4_2_5`** — `PlanEx^ACYC_htn ∈ NEXPTIME`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- A certificate for `PlanEx^ACYC_htn`: an acyclicity certificate and a tree certificate. -/
abbrev AcycTreeCert : Type := (List ℕ × List (ℕ × ℕ)) × TCert

/-- **The check of Thm. 4.2.5.** -/
def acycTreeB (x : ProbDesc × AcycTreeCert) : Bool :=
  validB x.1 && acycB x.1 x.2.1 && certB x.1 x.2.2 && runB x.1 x.2.2.2.2.1

theorem pt_acycTreeB : PT acycTreeB := by
  have h1 : PT fun x : ProbDesc × AcycTreeCert => validB x.1 := pt_validB.comp PT.fst
  have h2 : PT fun x : ProbDesc × AcycTreeCert => acycB x.1 x.2.1 :=
    pt_acycB.comp (PT.pair PT.fst (PT.fst.comp PT.snd))
  have hc : PT fun x : ProbDesc × AcycTreeCert => x.2.2 := PT.snd.comp PT.snd
  have h3 : PT fun x : ProbDesc × AcycTreeCert => certB x.1 x.2.2 := pt_certB.comp (PT.pair PT.fst hc)
  have hr : PT fun x : ProbDesc × AcycTreeCert => x.2.2.2 := PT.snd.comp hc
  have hr2 : PT fun x : ProbDesc × AcycTreeCert => x.2.2.2.2 := PT.snd.comp hr
  have hπ : PT fun x : ProbDesc × AcycTreeCert => x.2.2.2.2.1 := PT.fst.comp hr2
  have hp : PT fun x : ProbDesc × AcycTreeCert => ((x.1, x.2.2.2.2.1) : ProbDesc × List ℕ) :=
    PT.pair PT.fst hπ
  have h4 := pt_runB.comp hp
  refine (PT.and (PT.and (PT.and h1 h2) h3) h4).of_eq fun x => ?_
  rfl

/-- **Soundness of the check.** -/
theorem of_acycTreeB {p : ProbDesc} {b : AcycTreeCert} (h : acycTreeB (p, b) = true) :
    p.Valid ∧ p.toProblem.IsACYC ∧ p.toProblem.Solvable := by
  obtain ⟨⟨⟨hv, ha⟩, hc⟩, hr⟩ := by simpa only [acycTreeB, Bool.and_eq_true] using h
  have hp := (validB_iff p).1 hv
  obtain ⟨R, rkL⟩ := b.1
  refine ⟨hp, ((acycB_iff p _ _).1 ha).isACYC, ?_⟩
  obtain ⟨trees, htr⟩ := treesYield_of_certB hp hc
  obtain ⟨s, hs, hg⟩ := (runB_iff p _).1 hr
  exact (Problem.solvable_iff_trees p.toProblem (wf_toProblem p)).2 ⟨trees, _, s, htr, hs, hg⟩

theorem ids_length_le_sz (t : TnDesc) : t.ids.length ≤ sz t := by
  have := length_le_sz t.ids
  rw [sz_tnDesc]; omega

theorem methods_ids_le {p : ProbDesc} : ∀ e ∈ p.methods, e.2.ids.length ≤ sz p := by
  intro e he
  have h1 := ids_length_le_sz e.2
  have h2 := sz_le_of_mem he
  have h3 := sz_methodDesc e
  have h4 := sz_probDesc p
  omega

theorem kidOf_le {l : List (ℕ × ℕ)} {K : ℕ} (h : ∀ q ∈ l, q.2 ≤ K) (x : ℕ) : kidOf l x ≤ K := by
  unfold kidOf
  rcases hl : l.lookup x with _ | k
  · simp
  · exact h _ (mem_of_lookup_eq_some hl)

/-- The exponent of the certificate bound. -/
noncomputable def qAcyc : Polynomial ℕ := 3 * Polynomial.X ^ 2 + 9 * Polynomial.X + 19

theorem eval_qAcyc (n : ℕ) : qAcyc.eval n = 3 * n ^ 2 + 9 * n + 19 := by
  simp [qAcyc]

/-- **Completeness of the check, with the size of the certificate.** -/
theorem exists_acycTreeB {p : ProbDesc} (h : p.Valid ∧ p.toProblem.IsACYC ∧ p.toProblem.Solvable) :
    ∃ b : AcycTreeCert, sz b < 2 ^ qAcyc.eval (sz p) ∧ acycTreeB (p, b) = true := by
  obtain ⟨hp, hac, hsol⟩ := h
  obtain ⟨trees, π, s, hTY, hrun, hg⟩ :=
    (Problem.solvable_iff_trees p.toProblem (wf_toProblem p)).1 hsol
  obtain ⟨R, rkL, hab, hRN, hRl, hrkN, hrkl⟩ := exists_acycCert hp hac
  have hcert := (acycB_iff p R rkL).1 hab
  obtain ⟨c, hcB, hcπ, hclen, hnodes, hroots, hrl, hw, hwl, hπN⟩ := exists_certB hp hTY
  set S := sz p with hS
  refine ⟨((R, rkL), c), ?_, ?_⟩
  swap
  · simp only [acycTreeB, Bool.and_eq_true]
    refine ⟨⟨⟨(validB_iff p).2 hp, hab⟩, hcB⟩, ?_⟩
    rw [hcπ]
    exact (runB_iff p π).2 ⟨s, hrun, hg⟩
  -- the number of nodes
  have hK : (numsOf p).length ≤ S := length_numsOf_le p
  have hrk : ∀ x, kidOf rkL x ≤ S := fun x => (kidOf_le (fun q hq => (hrkN q hq).2) x).trans hK
  have htree : ∀ x ∈ p.tnI.ids, (trees x).size ≤ (S + 1) ^ (S + 1) := by
    intro x hx
    have hxT : x ∈ p.toProblem.tnI.T := by
      simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
    have := size_le_of_acycCert hcert methods_ids_le (trees x) _ (hTY.1 x hxT) (fun c hc =>
      hcert.reach_mem (HTN.Problem.ReachableName.tnI (P := p.toProblem.toPos) hxT hc))
    refine this.trans (Nat.pow_le_pow_right (by omega) ?_)
    rcases p.toProblem.tnI.α x with a | c'
    · simp
    · simpa using hrk c'
  have hids : p.tnI.ids.length ≤ S := (ids_length_le_sz _).trans (by
    have := sz_probDesc p
    omega)
  have hN : c.1.length ≤ S * (S + 1) ^ (S + 1) := by
    rw [hclen]
    have := List.sum_le_card_nsmul (p.tnI.ids.map fun x => (trees x).size) ((S + 1) ^ (S + 1))
      (fun n hn => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
        exact htree x hx)
    rw [List.length_map, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hids)
  have hY : π.length ≤ c.1.length := by
    have := length_le_of_treesYield hTY
    rw [show p.toProblem.tnI.T = p.tnI.ids.toFinset from rfl, List.sum_toFinset _ hp.tnI.nodup] at this
    rw [hclen]; exact this
  -- the size of the certificate
  have hc := sz_cert_le (Y := π.length) hnodes hroots hrl hw hwl (by rw [hcπ])
    (by rw [hcπ]; exact hπN)
  set X := (S + 1) ^ (S + 2) with hXdef
  have hX1 : S + 1 ≤ X := Nat.le_self_pow (by omega) _
  have hXpos : 1 ≤ X := by omega
  have hNX : c.1.length ≤ X := hN.trans (by
    show S * (S + 1) ^ (S + 1) ≤ (S + 1) ^ (S + 1 + 1)
    calc S * (S + 1) ^ (S + 1) ≤ (S + 1) * (S + 1) ^ (S + 1) := Nat.mul_le_mul (by omega) le_rfl
      _ = (S + 1) ^ (S + 1 + 1) := by ring)
  have hM : c.1.length + π.length + sz p + 1 ≤ 3 * X := by rw [← hS]; omega
  have hM3 : (c.1.length + π.length + sz p + 1) ^ 3 ≤ 27 * X ^ 3 :=
    (Nat.pow_le_pow_left hM 3).trans_eq (by ring)
  have hR : sz R ≤ R.length * (2 * S + 2) + 1 := sz_list_le fun a ha => sz_le_of_mem_numsOf (hRN a ha)
  have hrkS : sz rkL ≤ rkL.length * (2 * (S + (2 * (S + 1) + 1)) + 2) + 1 := sz_list_le fun q hq => by
    rw [sz_prod]
    have := sz_le_of_mem_numsOf (hrkN q hq).1
    have := sz_nat_le_of_lt' (show q.2 < S + 1 by have := (hrkN q hq).2; omega)
    omega
  have e1 : R.length * (2 * S + 2) ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : rkL.length * (2 * (S + (2 * (S + 1) + 1)) + 2) ≤ X * (8 * X) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hX23 : X * X ≤ X ^ 3 := by
    rw [show X ^ 3 = X * X * X by ring]; exact Nat.le_mul_of_pos_right _ (by omega)
  have htot : sz ((R, rkL), c) ≤ 2 ^ 11 * X ^ 3 := by
    rw [sz_prod, sz_prod]
    nlinarith
  have hX : X ^ 3 ≤ 2 ^ (3 * ((S + 1) * (S + 2))) := by
    rw [pow_mul']
    refine Nat.pow_le_pow_left ?_ 3
    rw [hXdef, pow_mul]
    exact Nat.pow_le_pow_left (lt_two_pow' (S + 1)).le _
  rw [eval_qAcyc, show 3 * S ^ 2 + 9 * S + 19 = 11 + 3 * ((S + 1) * (S + 2)) + 2 by ring, pow_add,
    pow_add]
  have : 2 ^ 11 * X ^ 3 ≤ 2 ^ 11 * 2 ^ (3 * ((S + 1) * (S + 2))) := Nat.mul_le_mul_left _ hX
  have hpos : 0 < 2 ^ 11 * 2 ^ (3 * ((S + 1) * (S + 2))) := by positivity
  omega

/-- **Theorem 4.2.5.** `PlanEx^ACYC_htn ∈ NEXPTIME`. -/
theorem thm_4_2_5 : Cx.NEXPTIME (PlanEx fun P => P.IsACYC) := by
  have h := inNExp_codeLang (α := ProbDesc) (β := AcycTreeCert)
    (Q := fun p => p.Valid ∧ p.toProblem.IsACYC ∧ p.toProblem.Solvable) pt_acycTreeB qAcyc
    fun p => ⟨fun hp => exists_acycTreeB hp, fun ⟨b, _, hb⟩ => of_acycTreeB hb⟩
  exact h

end Article

end HTN
