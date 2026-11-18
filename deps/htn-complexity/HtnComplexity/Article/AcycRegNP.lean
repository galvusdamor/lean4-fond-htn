import HtnComplexity.Article.AcycNP
/-!
# Acyclic regular problems are in NP (Lem. 4.2.11)

See `HtnComplexity/Article/AcycNP.lean` for why the article's proof does not apply; the route
here bounds the trees directly: in a regular problem every reachable method has at most one
compound task, so a tree is a caterpillar with at most `(r + 1)(B + 1) + 1` nodes for a root of
rank `r` (`HTN.Article.size_le_of_reg`).  The certificate of Thm. 4.2.5 is checked together with
the regularity (`HTN.Article.regB`) — and for the TO variant the total order
(`HTN.Article.toB`) — of the methods of the certified reachable names.

* **`HTN.Article.lem_4_2_11`** — `PlanEx^{ACYC ∩ REG}_htn ∈ NP`;
* **`HTN.Article.lem_4_2_11_TO`** — `PlanEx^{ACYC ∩ REG ∩ TO}_htn ∈ NP`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-! ### Regular and totally ordered descriptions -/

/-- **Regularity of a network description**: a compound task is preceded by all other tasks,
which are primitive. -/
def regB (t : TnDesc) : Bool :=
  t.ids.all fun x => !(lblOf t x).1 ||
    t.ids.all fun y => (x == y) || (!(lblOf t y).1 && decide ((y, x) ∈ t.ordList))

/-- **Total order of a network description.** -/
def toB (t : TnDesc) : Bool :=
  t.ids.all fun x => t.ids.all fun y =>
    (x == y) || decide ((x, y) ∈ t.ordList) || decide ((y, x) ∈ t.ordList)

theorem isAbstractId_iff {t : TnDesc} {x : ℕ} :
    t.toTaskNetwork.IsAbstractId x ↔ (lblOf t x).1 = true := by
  constructor
  · rintro ⟨c, hc⟩
    rw [label_eq_inr.1 hc]
  · intro h
    exact ⟨(lblOf t x).2, label_eq_inr.2 (Prod.ext h rfl)⟩

theorem mem_T_iff {t : TnDesc} {x : ℕ} : x ∈ t.toTaskNetwork.T ↔ x ∈ t.ids := by
  simp [TnDesc.toTaskNetwork]

theorem regB_iff {prim : ℕ → Prop} {t : TnDesc} (ht : TnValid prim t) :
    regB t = true ↔ t.toTaskNetwork.IsRegular := by
  unfold regB TaskNetwork.IsRegular
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq, mem_T_iff, isAbstractId_iff]
  constructor
  · intro h
    refine ⟨fun x hx y hy hxa hya => ?_, fun x hx hxa y hy hyx => ?_⟩
    · rcases h x hx with h1 | h1
      · rw [h1] at hxa; cases hxa
      · rcases h1 y hy with h2 | h2
        · exact h2
        · rw [h2.1] at hya; cases hya
    · rcases h x hx with h1 | h1
      · rw [h1] at hxa; cases hxa
      · rcases h1 y hy with h2 | h2
        · exact absurd h2.symm hyx
        · exact (ht.ordOf_iff).2 h2.2
  · rintro ⟨h1, h2⟩ x hx
    cases hxa : (lblOf t x).1
    · exact Or.inl rfl
    · refine Or.inr fun y hy => ?_
      by_cases hxy : x = y
      · exact Or.inl hxy
      · refine Or.inr ⟨?_, (ht.ordOf_iff).1 (h2 x hx hxa y hy (Ne.symm hxy))⟩
        cases hya : (lblOf t y).1
        · rfl
        · exact absurd (h1 x hx y hy hxa hya) hxy

theorem toB_iff {prim : ℕ → Prop} {t : TnDesc} (ht : TnValid prim t) :
    toB t = true ↔ t.toTaskNetwork.IsTotallyOrdered := by
  unfold toB TaskNetwork.IsTotallyOrdered
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, mem_T_iff]
  constructor
  · intro h x hx y hy hxy
    rcases h x hx y hy with (h1 | h1) | h1
    · exact absurd h1 hxy
    · exact Or.inl ((ht.ordOf_iff).2 h1)
    · exact Or.inr ((ht.ordOf_iff).2 h1)
  · intro h x hx y hy
    by_cases hxy : x = y
    · exact Or.inl (Or.inl hxy)
    · rcases h x hx y hy hxy with h1 | h1
      · exact Or.inl (Or.inr ((ht.ordOf_iff).1 h1))
      · exact Or.inr ((ht.ordOf_iff).1 h1)

theorem pt_regB : PT regB := by
  have hl := pt_lblOf (α := TnDesc × ℕ) PT.fst PT.snd
  have hl2 := pt_lblOf (α := (TnDesc × ℕ) × ℕ) (PT.fst.comp PT.fst) PT.snd
  have hin : PT fun r : (TnDesc × ℕ) × ℕ =>
      (r.1.2 == r.2) || (!(lblOf r.1.1 r.2).1 && decide ((r.2, r.1.2) ∈ r.1.1.ordList)) :=
    PT.or (PT.beqL (PT.snd.comp PT.fst) PT.snd) (PT.and (PT.not (PT.fst.comp hl2))
      (PT.elemL (PT.fst.comp (PT.snd.comp (PT.fst.comp PT.fst))) (PT.pair PT.snd (PT.snd.comp PT.fst))))
  have hout : PT fun q : TnDesc × ℕ => !(lblOf q.1 q.2).1 ||
      q.1.ids.all fun y => (q.2 == y) || (!(lblOf q.1 y).1 && decide ((y, q.2) ∈ q.1.ordList)) :=
    PT.or (PT.not (PT.fst.comp hl)) (PT.all (p := fun (q : TnDesc × ℕ) (y : ℕ) => (q.2 == y) ||
      (!(lblOf q.1 y).1 && decide ((y, q.2) ∈ q.1.ordList))) (PT.fst.comp PT.fst) hin)
  exact (PT.all (f := fun t : TnDesc => t.ids) (p := fun (t : TnDesc) (x : ℕ) => !(lblOf t x).1 ||
    t.ids.all fun y => (x == y) || (!(lblOf t y).1 && decide ((y, x) ∈ t.ordList))) PT.fst
    hout).of_eq fun t => rfl

theorem pt_toB : PT toB := by
  have hin : PT fun r : (TnDesc × ℕ) × ℕ =>
      (r.1.2 == r.2) || decide ((r.1.2, r.2) ∈ r.1.1.ordList) ||
        decide ((r.2, r.1.2) ∈ r.1.1.ordList) :=
    PT.or (PT.or (PT.beqL (PT.snd.comp PT.fst) PT.snd)
      (PT.elemL (PT.fst.comp (PT.snd.comp (PT.fst.comp PT.fst))) (PT.pair (PT.snd.comp PT.fst) PT.snd)))
      (PT.elemL (PT.fst.comp (PT.snd.comp (PT.fst.comp PT.fst))) (PT.pair PT.snd (PT.snd.comp PT.fst)))
  exact (PT.all (f := fun t : TnDesc => t.ids) (p := fun (t : TnDesc) (x : ℕ) => t.ids.all fun y =>
    (x == y) || decide ((x, y) ∈ t.ordList) || decide ((y, x) ∈ t.ordList)) PT.fst
    (PT.all (p := fun (q : TnDesc × ℕ) (y : ℕ) => (q.2 == y) || decide ((q.2, y) ∈ q.1.ordList) ||
      decide ((y, q.2) ∈ q.1.ordList)) (PT.fst.comp PT.fst) hin)).of_eq fun t => rfl

/-! ### Caterpillars -/

/-- **The trees of a certified regular description are caterpillars**: at most
`(r + 1)(B + 1) + 1` nodes for a root of rank `r`. -/
theorem size_le_of_reg {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} (h : AcycCert p R rk)
    (hreg : ∀ e ∈ p.methods, e.1 ∈ R → e.2.toTaskNetwork.IsRegular) {B : ℕ}
    (hB : ∀ e ∈ p.methods, e.2.ids.length ≤ B) : ∀ (dt : DTree ℕ ℕ ℕ) (s : ℕ ⊕ ℕ),
    dt.Valid p.toProblem.methods s → (∀ c, s = Sum.inr c → c ∈ R) →
    dt.size ≤ Sum.elim (fun _ => 0) (fun c => rk c + 1) s * (B + 1) + 1 := by
  intro dt
  induction dt with
  | leaf a => intro s hv _; cases hv; simp [DTree.size]
  | node c m ch ih =>
    intro s hv hs
    cases hv with
    | node hm hc hch =>
    obtain ⟨e, he, rfl⟩ := hm
    have hcR : c ∈ R := hs c rfl
    subst hc
    have hR : e.1 ∈ R := hcR
    set T := (MethodDesc.toMethod e).subtasks.T with hTdef
    set r := rk e.1 with hr
    -- the bound of each child
    have hchild : ∀ t ∈ T, (ch t).size ≤ Sum.elim (fun _ => 0) (fun c => rk c + 1) (e.2.label t) *
        (B + 1) + 1 := fun t ht => by
      have ht' : t ∈ e.2.ids := by simpa [hTdef, MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
      exact ih t _ (hch t ht) (fun c' hc' => (h.step e he hR t ht' c' (label_eq_inr.1 hc')).1)
    have hprim : ∀ t ∈ T, ¬ e.2.toTaskNetwork.IsAbstractId t → (ch t).size ≤ 1 := by
      intro t ht hna
      have := hchild t ht
      rcases hl : e.2.label t with a | c'
      · rw [hl] at this; simpa using this
      · exact absurd ⟨c', hl⟩ hna
    have hcomp : ∀ t ∈ T, (ch t).size ≤ r * (B + 1) + 1 := by
      intro t ht
      have ht' : t ∈ e.2.ids := by simpa [hTdef, MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
      have := hchild t ht
      rcases hl : e.2.label t with a | c'
      · rw [hl] at this; simp at this; omega
      · rw [hl] at this
        have hlt := (h.step e he hR t ht' c' (label_eq_inr.1 hl)).2
        simp only [Sum.elim_inr] at this
        have : (rk c' + 1) * (B + 1) ≤ r * (B + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
    have hT : T.card ≤ B := (List.toFinset_card_le _).trans (hB e he)
    have hsum : ∑ t ∈ T, (ch t).size ≤ T.card + r * (B + 1) := by
      by_cases hex : ∃ t₀ ∈ T, e.2.toTaskNetwork.IsAbstractId t₀
      · obtain ⟨t₀, ht₀, ha₀⟩ := hex
        rw [← Finset.add_sum_erase T _ ht₀]
        have h1 : ∑ t ∈ T.erase t₀, (ch t).size ≤ (T.erase t₀).card * 1 := by
          have := Finset.sum_le_card_nsmul (T.erase t₀) (fun t => (ch t).size) 1 fun t ht => by
            obtain ⟨hne, ht⟩ := Finset.mem_erase.1 ht
            refine hprim t ht fun ha => hne ?_
            exact (hreg e he hR).1 t ht t₀ ht₀ ha ha₀
          simpa using this
        have h2 := Finset.card_erase_add_one ht₀
        have h3 := hcomp t₀ ht₀
        omega
      · push_neg at hex
        have := Finset.sum_le_card_nsmul T (fun t => (ch t).size) 1 fun t ht => hprim t ht (hex t ht)
        simp only [smul_eq_mul, mul_one] at this
        omega
    simp only [DTree.size, Sum.elim_inr]
    show 1 + _ ≤ (r + 1) * (B + 1) + 1
    nlinarith

/-! ### The checks -/

/-- **The check of Lem. 4.2.11.** -/
def acycRegB (x : ProbDesc × AcycTreeCert) : Bool :=
  acycTreeB x && x.1.methods.all fun e => !decide (e.1 ∈ x.2.1.1) || regB e.2

/-- **The check of Lem. 4.2.11, TO variant.** -/
def acycRegTOB (x : ProbDesc × AcycTreeCert) : Bool :=
  acycRegB x && toB x.1.tnI && x.1.methods.all fun e => !decide (e.1 ∈ x.2.1.1) || toB e.2

theorem pt_methodsR {g : TnDesc → Bool} (hg : PT g) :
    PT fun x : ProbDesc × AcycTreeCert => x.1.methods.all fun e => !decide (e.1 ∈ x.2.1.1) || g e.2 :=
  PT.all (PT.snd.comp (PT.fst.comp PT.fst)) (PT.or (PT.not (PT.elem
    (PT.fst.comp (PT.fst.comp (PT.snd.comp PT.fst))) (PT.fst.comp PT.snd)))
    (hg.comp (PT.snd.comp PT.snd)))

theorem pt_acycRegB : PT acycRegB :=
  (PT.and pt_acycTreeB (pt_methodsR pt_regB)).of_eq fun _ => rfl

theorem pt_acycRegTOB : PT acycRegTOB :=
  (PT.and (PT.and pt_acycRegB (pt_toB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst)))))
    (pt_methodsR pt_toB)).of_eq fun _ => rfl

/-- The class conditions of the methods of certified names. -/
theorem methodsR_iff {p : ProbDesc} (hp : p.Valid) {R : List ℕ} {rk : ℕ → ℕ} (h : AcycCert p R rk)
    (hRr : ∀ c ∈ R, p.toProblem.toPos.ReachableName c) {g : TnDesc → Bool}
    {Pm : TaskNetwork ℕ ℕ ℕ → Prop}
    (hg : ∀ {t : TnDesc}, TnValid p.Declared t → (g t = true ↔ Pm t.toTaskNetwork)) :
    (p.methods.all fun e => !decide (e.1 ∈ R) || g e.2) = true ↔
      ∀ m, p.toProblem.toPos.ReachableMethod m → Pm m.subtasks := by
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro hm m ⟨⟨e, he, rfl⟩, hr⟩
    rcases hm e he with h1 | h1
    · exact absurd (h.reach_mem hr) h1
    · exact (hg (hp.methods e he)).1 h1
  · intro hm e he
    by_cases hR : e.1 ∈ R
    · exact Or.inr ((hg (hp.methods e he)).2
        (hm _ ⟨(⟨e, he, rfl⟩ : ∃ e' ∈ p.methods, e'.toMethod = e.toMethod), hRr _ hR⟩))
    · exact Or.inl hR

/-- **Completeness for acyclic regular descriptions, with the size of the certificate.** -/
theorem exists_acycRegCert {p : ProbDesc} (hp : p.Valid) (hac : p.toProblem.IsACYC)
    (hreg : p.toProblem.IsREG) (hsol : p.toProblem.Solvable) :
    ∃ b : AcycTreeCert, sz b ≤ (sz p + 1) ^ 22 ∧ acycTreeB (p, b) = true ∧
      (∀ c ∈ b.1.1, p.toProblem.toPos.ReachableName c) ∧ AcycCert p b.1.1 (kidOf b.1.2) := by
  obtain ⟨trees, π, s, hTY, hrun, hg⟩ :=
    (Problem.solvable_iff_trees p.toProblem (wf_toProblem p)).1 hsol
  obtain ⟨R, rkL, hab, hRN, hRl, hrkN, hrkl, hnd, hRr, hrR, hrkR⟩ := exists_acycCert hp hac
  have hcert := (acycB_iff p R rkL).1 hab
  obtain ⟨c, hcB, hcπ, hclen, hnodes, hroots, hrl, hw, hwl, hπN⟩ := exists_certB hp hTY
  have hregR : ∀ e ∈ p.methods, e.1 ∈ R → e.2.toTaskNetwork.IsRegular := fun e he hR =>
    hreg _ ⟨(⟨e, he, rfl⟩ : ∃ e' ∈ p.methods, e'.toMethod = e.toMethod), hRr _ hR⟩
  set S := sz p with hS
  refine ⟨((R, rkL), c), ?_, ?_, hRr, hcert⟩
  · have hK : (numsOf p).length ≤ S := length_numsOf_le p
    have hrk : ∀ x, kidOf rkL x ≤ S := fun x =>
      (kidOf_le (fun q hq => (hrkN q hq).2) x).trans hK
    have htree : ∀ x ∈ p.tnI.ids, (trees x).size ≤ (S + 1) * (S + 1) + 1 := by
      intro x hx
      have hxT : x ∈ p.toProblem.tnI.T := by
        simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
      have := size_le_of_reg hcert hregR methods_ids_le (trees x) _ (hTY.1 x hxT) (fun c hc =>
        hcert.reach_mem (HTN.Problem.ReachableName.tnI (P := p.toProblem.toPos) hxT hc))
      refine this.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _)
      rcases p.toProblem.tnI.α x with a | c'
      · simp
      · simpa using hrk c'
    have hids : p.tnI.ids.length ≤ S := (ids_length_le_sz _).trans (by
      have := sz_probDesc p
      omega)
    have hN : c.1.length ≤ (S + 1) ^ 3 := by
      rw [hclen]
      have := List.sum_le_card_nsmul (p.tnI.ids.map fun x => (trees x).size) ((S + 1) * (S + 1) + 1)
        (fun n hn => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
          exact htree x hx)
      rw [List.length_map, smul_eq_mul] at this
      refine this.trans ((Nat.mul_le_mul_right _ hids).trans ?_)
      nlinarith
    have hY : π.length ≤ c.1.length := by
      have := length_le_of_treesYield hTY
      rw [show p.toProblem.tnI.T = p.tnI.ids.toFinset from rfl,
        List.sum_toFinset _ hp.tnI.nodup] at this
      rw [hclen]; exact this
    have hc := sz_cert_le (Y := π.length) hnodes hroots hrl hw hwl (by rw [hcπ])
      (by rw [hcπ]; exact hπN)
    have := sz_acycTreeCert_le (j := 3) hRN hRl hrkN hrkl hc hY hN (by omega) le_rfl
    rwa [show 3 * 3 + 13 = 22 from rfl] at this
  · simp only [acycTreeB, Bool.and_eq_true]
    refine ⟨⟨⟨(validB_iff p).2 hp, hab⟩, hcB⟩, ?_⟩
    rw [hcπ]
    exact (runB_iff p π).2 ⟨s, hrun, hg⟩

/-- **Lemma 4.2.11.** `PlanEx^{ACYC ∩ REG}_htn ∈ NP`. -/
theorem lem_4_2_11 : Cx.NP (PlanEx fun P => P.IsACYC ∧ P.IsREG) := by
  have h := inNP_codeLang (α := ProbDesc) (β := AcycTreeCert)
    (Q := fun p => p.Valid ∧ (p.toProblem.IsACYC ∧ p.toProblem.IsREG) ∧ p.toProblem.Solvable)
    pt_acycRegB 22 fun p => ⟨fun ⟨hp, ⟨hac, hreg⟩, hsol⟩ => ?_, fun ⟨b, _, hb⟩ => ?_⟩
  · exact h
  · obtain ⟨b, hsz, hb, hRr, hcert⟩ := exists_acycRegCert hp hac hreg hsol
    refine ⟨b, hsz, ?_⟩
    simp only [acycRegB, hb, Bool.true_and]
    exact (methodsR_iff hp hcert hRr (fun ht => regB_iff ht)).2 hreg
  · simp only [acycRegB, Bool.and_eq_true] at hb
    obtain ⟨hv, hac, hsol⟩ := of_acycTreeB hb.1
    obtain ⟨⟨⟨-, ha⟩, -⟩, -⟩ := by simpa only [acycTreeB, Bool.and_eq_true] using hb.1
    have hcert := (acycB_iff p _ _).1 ha
    refine ⟨hv, ⟨hac, fun m hm => ?_⟩, hsol⟩
    obtain ⟨⟨e, he, rfl⟩, hr⟩ := hm
    have := List.all_eq_true.1 hb.2 e he
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
    rcases this with h1 | h1
    · exact absurd (hcert.reach_mem hr) h1
    · exact (regB_iff (hv.methods e he)).1 h1

/-- **Lemma 4.2.11, TO variant.** `PlanEx^{ACYC ∩ REG ∩ TO}_htn ∈ NP`. -/
theorem lem_4_2_11_TO : Cx.NP (PlanEx fun P => P.IsACYC ∧ P.IsREG ∧ P.IsTO) := by
  have h := inNP_codeLang (α := ProbDesc) (β := AcycTreeCert)
    (Q := fun p => p.Valid ∧ (p.toProblem.IsACYC ∧ p.toProblem.IsREG ∧ p.toProblem.IsTO) ∧
      p.toProblem.Solvable)
    pt_acycRegTOB 22 fun p => ⟨fun ⟨hp, ⟨hac, hreg, hto⟩, hsol⟩ => ?_, fun ⟨b, _, hb⟩ => ?_⟩
  · exact h
  · obtain ⟨b, hsz, hb, hRr, hcert⟩ := exists_acycRegCert hp hac hreg hsol
    refine ⟨b, hsz, ?_⟩
    simp only [acycRegTOB, acycRegB, hb, Bool.true_and, Bool.and_eq_true]
    exact ⟨⟨(methodsR_iff hp hcert hRr (fun ht => regB_iff ht)).2 hreg, (toB_iff hp.tnI).2 hto.1⟩,
      (methodsR_iff hp hcert hRr (fun ht => toB_iff ht)).2 hto.2⟩
  · simp only [acycRegTOB, acycRegB, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hb1, hreg⟩, hto⟩, htoM⟩ := hb
    obtain ⟨hv, hac, hsol⟩ := of_acycTreeB hb1
    obtain ⟨⟨⟨-, ha⟩, -⟩, -⟩ := by simpa only [acycTreeB, Bool.and_eq_true] using hb1
    have hcert := (acycB_iff p _ _).1 ha
    have hM : ∀ {g : TnDesc → Bool} {Pm : TaskNetwork ℕ ℕ ℕ → Prop},
        (∀ {t : TnDesc}, TnValid p.Declared t → (g t = true ↔ Pm t.toTaskNetwork)) →
        (p.methods.all fun e => !decide (e.1 ∈ b.1.1) || g e.2) = true →
        ∀ m, p.toProblem.toPos.ReachableMethod m → Pm m.subtasks := by
      intro g Pm hg hall m hm
      obtain ⟨⟨e, he, rfl⟩, hr⟩ := hm
      have := List.all_eq_true.1 hall e he
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
      rcases this with h1 | h1
      · exact absurd (hcert.reach_mem hr) h1
      · exact (hg (hv.methods e he)).1 h1
    exact ⟨hv, ⟨hac, hM (fun ht => regB_iff ht) hreg,
      (toB_iff hv.tnI).1 hto, hM (fun ht => toB_iff ht) htoM⟩, hsol⟩

end Article

end HTN
