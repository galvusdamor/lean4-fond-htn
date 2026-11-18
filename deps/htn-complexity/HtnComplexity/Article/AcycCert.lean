import HtnComplexity.Article.TreeCertSize
import HtnComplexity.Article.TreeCertPT
/-!
# Certificates of acyclicity

A description denotes an `ACYC` problem (Def. 3.6) iff its reachable compound names can be ranked
so that every method of a reachable name decreases the rank.  The certificate
(`HTN.Article.AcycCert`) lists a set `R` of names, closed under reachability, and ranks; its check
`HTN.Article.acycB` is polynomial time (`HTN.Article.pt_acycB`).

* `HTN.Article.AcycCert.isACYC` — a certificate gives a `≤₀`-stratification (by rank, then by
  name);
* `HTN.Article.exists_acycCert` — conversely, for a well-formed `ACYC` description, the reachable
  names among the numbers of the description, ranked by the number of reachable names strictly
  below them, form a certificate;
* `HTN.Article.size_le_of_acycCert` — the trees of a certified description are small: a tree
  rooted in a name of rank `k` has at most `(B + 1) ^ (k + 1)` nodes, `B` the largest number of
  tasks of a method (the bound of Thm. 4.2.5's proof);
* `HTN.Article.length_le_size` — a yield is not longer than its tree.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

theorem toSum_eq_inr {l : Bool × ℕ} {c : ℕ} : toSum l = Sum.inr c ↔ l = (true, c) := by
  obtain ⟨_ | _, n⟩ := l <;> simp [toSum]

theorem label_eq_inr {t : TnDesc} {x c : ℕ} : t.label x = Sum.inr c ↔ lblOf t x = (true, c) := by
  rw [label_eq_toSum, toSum_eq_inr]

/-- **An acyclicity certificate**: a list `R` of compound names containing those of `tn_I` and
closed under the methods of its names, and ranks decreasing along these methods. -/
structure AcycCert (p : ProbDesc) (R : List ℕ) (rk : ℕ → ℕ) : Prop where
  init : ∀ x ∈ p.tnI.ids, ∀ c, lblOf p.tnI x = (true, c) → c ∈ R
  step : ∀ e ∈ p.methods, e.1 ∈ R → ∀ x ∈ e.2.ids, ∀ c, lblOf e.2 x = (true, c) →
    c ∈ R ∧ rk c < rk e.1

/-- **The check of an acyclicity certificate** (ranks as a list, looked up by `kidOf`). -/
def acycB (p : ProbDesc) (a : List ℕ × List (ℕ × ℕ)) : Bool :=
  p.tnI.ids.all (fun x => !(lblOf p.tnI x).1 || decide ((lblOf p.tnI x).2 ∈ a.1)) &&
    p.methods.all fun e => !decide (e.1 ∈ a.1) || e.2.ids.all fun x => !(lblOf e.2 x).1 ||
      (decide ((lblOf e.2 x).2 ∈ a.1) && decide (kidOf a.2 (lblOf e.2 x).2 < kidOf a.2 e.1))

theorem acycB_iff (p : ProbDesc) (R : List ℕ) (rkL : List (ℕ × ℕ)) :
    acycB p (R, rkL) = true ↔ AcycCert p R (kidOf rkL) := by
  unfold acycB
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx c hc => ?_, fun e he hR x hx c hc => ?_⟩
    · rcases h1 x hx with h | h
      · rw [hc] at h; cases h
      · rw [hc] at h; exact h
    · rcases h2 e he with h | h
      · exact absurd hR h
      · rcases h x hx with h' | h'
        · rw [hc] at h'; cases h'
        · rw [hc] at h'; exact h'
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun e he => ?_⟩
    · rcases h : lblOf p.tnI x with ⟨_ | _, c⟩
      · exact Or.inl rfl
      · exact Or.inr (h1 x hx c h)
    · by_cases hR : e.1 ∈ R
      · refine Or.inr fun x hx => ?_
        rcases h : lblOf e.2 x with ⟨_ | _, c⟩
        · exact Or.inl rfl
        · exact Or.inr (h2 e he hR x hx c h)
      · exact Or.inl hR

theorem pt_acycB : PT fun x : ProbDesc × List ℕ × List (ℕ × ℕ) => acycB x.1 x.2 := by
  have htn : PT fun x : ProbDesc × List ℕ × List (ℕ × ℕ) => x.1.tnI :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))
  have hR : PT fun x : ProbDesc × List ℕ × List (ℕ × ℕ) => x.2.1 := PT.fst.comp PT.snd
  have hrk : PT fun x : ProbDesc × List ℕ × List (ℕ × ℕ) => x.2.2 := PT.snd.comp PT.snd
  unfold acycB
  refine PT.and (PT.all (PT.fst.comp htn) (PT.or (PT.not (PT.fst.comp (pt_lblOf (htn.comp PT.fst)
    PT.snd))) (PT.elem (hR.comp PT.fst) (PT.snd.comp (pt_lblOf (htn.comp PT.fst) PT.snd)))))
    (PT.all (PT.snd.comp (PT.fst.comp PT.fst)) (PT.or (PT.not (PT.elem (hR.comp PT.fst)
      (PT.fst.comp PT.snd))) (PT.all (PT.fst.comp (PT.snd.comp PT.snd)) ?_)))
  -- context `((x, e), y)`
  have hT : PT fun q : ((ProbDesc × List ℕ × List (ℕ × ℕ)) × MethodDesc) × ℕ => q.1.2.2 :=
    PT.snd.comp (PT.snd.comp PT.fst)
  have hl := pt_lblOf hT PT.snd
  exact PT.or (PT.not (PT.fst.comp hl)) (PT.and (PT.elem (hR.comp (PT.fst.comp PT.fst))
    (PT.snd.comp hl)) (PT.lt (pt_kidOf (hrk.comp (PT.fst.comp PT.fst)) (PT.snd.comp hl))
      (pt_kidOf (hrk.comp (PT.fst.comp PT.fst)) (PT.fst.comp (PT.snd.comp PT.fst)))))

/-! ### Soundness -/

theorem AcycCert.reach_mem {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} (h : AcycCert p R rk)
    {c : ℕ} (hc : p.toProblem.toPos.ReachableName c) : c ∈ R := by
  induction hc with
  | @tnI t c ht hc =>
    have ht' : t ∈ p.tnI.ids := by
      simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using ht
    exact h.init _ ht' _ (label_eq_inr.1 hc)
  | @method m t c hm hr ht hc ih =>
    obtain ⟨e, he, rfl⟩ := hm
    have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
    exact (h.step e he ih _ ht' _ (label_eq_inr.1 hc)).1

/-- The order of a certificate: by rank, then by name. -/
def certLe (rk : ℕ → ℕ) (c c' : ℕ) : Prop := rk c < rk c' ∨ (rk c = rk c' ∧ c ≤ c')

/-- **A certificate gives a `≤₀`-stratification.** -/
theorem AcycCert.strat0 {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} (h : AcycCert p R rk) :
    p.toProblem.toPos.IsStrat0 (certLe rk) := by
  refine ⟨⟨fun c _ => Or.inr ⟨rfl, le_rfl⟩, fun c₁ c₂ c₃ _ _ _ h₁ h₂ => ?_, fun c₁ c₂ _ _ => ?_⟩,
    fun c₁ c₂ _ _ h₁ h₂ => ?_, fun m hm t ht c hc => ?_⟩
  · unfold certLe at *; omega
  · unfold certLe; omega
  · unfold certLe at *; omega
  · obtain ⟨⟨e, he, rfl⟩, hr⟩ := hm
    have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
    have := (h.step e he (h.reach_mem hr) t ht' c (label_eq_inr.1 hc)).2
    show certLe rk c e.1 ∧ ¬ certLe rk e.1 c
    unfold certLe; omega

theorem AcycCert.isACYC {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} (h : AcycCert p R rk) :
    p.toProblem.IsACYC :=
  ⟨_, h.strat0⟩

/-! ### Completeness -/

theorem reach_numsOf {p : ProbDesc} (hp : p.Valid) {c : ℕ}
    (hc : p.toProblem.toPos.ReachableName c) : c ∈ numsOf p := by
  induction hc with
  | @tnI t c ht hc =>
    have ht' : t ∈ p.tnI.ids := by
      simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using ht
    have := lblOf_mem hp.tnI ht'
    rw [label_eq_inr.1 hc] at this
    exact mem_numsOf_tnI (List.mem_append_right _ this)
  | @method m t c hm hr ht hc ih =>
    obtain ⟨e, he, rfl⟩ := hm
    have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
    have := lblOf_mem (hp.methods e he) ht'
    rw [label_eq_inr.1 hc] at this
    exact mem_numsOf_method he (List.mem_cons_of_mem _ (List.mem_append_right _ this))

open Classical in
/-- **Completeness of acyclicity certificates**, with their size. -/
theorem exists_acycCert {p : ProbDesc} (hp : p.Valid) (h : p.toProblem.IsACYC) :
    ∃ (R : List ℕ) (rkL : List (ℕ × ℕ)), acycB p (R, rkL) = true ∧ (∀ c ∈ R, c ∈ numsOf p) ∧
      R.length ≤ (numsOf p).length ∧
      (∀ q ∈ rkL, q.1 ∈ numsOf p ∧ q.2 ≤ (numsOf p).length) ∧ rkL.length ≤ (numsOf p).length ∧
      R.Nodup ∧ (∀ c ∈ R, p.toProblem.toPos.ReachableName c) ∧
      (∀ c, p.toProblem.toPos.ReachableName c → c ∈ R) ∧ (∀ q ∈ rkL, q.2 < R.length) := by
  obtain ⟨le, hle⟩ := h
  let Rch := p.toProblem.toPos.ReachableName
  let R := (numsOf p).dedup.filter fun c => decide (Rch c)
  let rk : ℕ → ℕ := fun c =>
    ((numsOf p).toFinset.filter fun c' => Rch c' ∧ le c' c ∧ ¬ le c c').card
  have hRmem : ∀ c, Rch c → c ∈ R := fun c h1 =>
    List.mem_filter.2 ⟨List.mem_dedup.2 (reach_numsOf hp h1), by simpa using h1⟩
  have hRnd : R.Nodup := (List.nodup_dedup _).filter _
  have hRch : ∀ c ∈ R, Rch c := fun c hc => by simpa using (List.mem_filter.1 hc).2
  have hrk : ∀ c, rk c ≤ (numsOf p).length := fun c =>
    (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
  have hstep : ∀ e ∈ p.methods, Rch e.1 → ∀ x ∈ e.2.ids, ∀ c, lblOf e.2 x = (true, c) →
      Rch c ∧ rk c < rk e.1 := by
    intro e he hr x hx c hc
    have hα : (MethodDesc.toMethod e).subtasks.α x = Sum.inr c := label_eq_inr.2 hc
    have hxT : x ∈ (MethodDesc.toMethod e).subtasks.T := by
      simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hx
    have hrc : Rch c := HTN.Problem.ReachableName.method
      (show MethodDesc.toMethod e ∈ p.toProblem.methods from ⟨e, he, rfl⟩) hr hxT hα
    obtain ⟨hd1, hd2⟩ := hle.decreasing _
      ⟨show MethodDesc.toMethod e ∈ p.toProblem.methods from ⟨e, he, rfl⟩, hr⟩ x hxT c hα
    refine ⟨hrc, Finset.card_lt_card ?_⟩
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨c, Finset.mem_filter.2 ⟨List.mem_toFinset.2 (reach_numsOf hp hrc), hrc, hd1, hd2⟩,
        fun hc' => ?_⟩
      have := (Finset.mem_filter.1 hc').2
      exact this.2.2 this.2.1
    · intro c' hc'
      obtain ⟨hc'N, hr', h1, h2⟩ := Finset.mem_filter.1 hc'
      refine Finset.mem_filter.2 ⟨hc'N, hr', hle.strat.trans _ _ _ hr' hrc hr h1 hd1,
        fun h3 => h2 ?_⟩
      exact hle.strat.trans _ _ _ hrc hr hr' hd1 h3
  have hrkR : ∀ c ∈ R, rk c < R.length := by
    intro c hc
    rw [← List.toFinset_card_of_nodup hRnd]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun c' hc' => ?_).2
      ⟨c, List.mem_toFinset.2 hc, fun hc' => ?_⟩)
    · obtain ⟨-, hr', -⟩ := Finset.mem_filter.1 hc'
      exact List.mem_toFinset.2 (hRmem c' hr')
    · have := (Finset.mem_filter.1 hc').2
      exact this.2.2 this.2.1
  have hRlen : R.length ≤ (numsOf p).length :=
    (List.length_filter_le _ _).trans (List.dedup_sublist _).length_le
  refine ⟨R, R.map fun c => (c, rk c), (acycB_iff _ _ _).2 ⟨fun x hx c hc => ?_,
    fun e he hR x hx c hc => ?_⟩, fun c hc => List.mem_dedup.1 (List.mem_filter.1 hc).1, hRlen,
    fun q hq => ?_, by rw [List.length_map]; exact hRlen, hRnd, hRch, hRmem, fun q hq => ?_⟩
  · have hxT : x ∈ p.toProblem.toPos.tnI.T := by
      simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
    exact hRmem c (HTN.Problem.ReachableName.tnI hxT (label_eq_inr.2 hc))
  · obtain ⟨h1, h2⟩ := hstep e he (hRch _ hR) x hx c hc
    refine ⟨hRmem c h1, ?_⟩
    rw [kidOf_map_pair _ (hRmem c h1), kidOf_map_pair _ hR]
    exact h2
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
    exact ⟨List.mem_dedup.1 (List.mem_filter.1 hc).1, hrk c⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
    exact hrkR c hc

/-! ### Small trees -/

/-- **The trees of a certified description are small.** -/
theorem size_le_of_acycCert {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} (h : AcycCert p R rk)
    {B : ℕ} (hB : ∀ e ∈ p.methods, e.2.ids.length ≤ B) : ∀ (dt : DTree ℕ ℕ ℕ) (s : ℕ ⊕ ℕ),
    dt.Valid p.toProblem.methods s → (∀ c, s = Sum.inr c → c ∈ R) →
    dt.size ≤ (B + 1) ^ (Sum.elim (fun _ => 0) (fun c => rk c + 1) s) := by
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
    simp only [DTree.size, Sum.elim_inr]
    have hchild : ∀ t ∈ (MethodDesc.toMethod e).subtasks.T, (ch t).size ≤ (B + 1) ^ rk e.1 := by
      intro t ht
      have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
      have := ih t _ (hch t ht) (fun c' hc' => (h.step e he hcR t ht' c' (label_eq_inr.1 hc')).1)
      change (ch t).size ≤ (B + 1) ^ Sum.elim (fun _ => 0) (fun c => rk c + 1) (e.2.label t) at this
      rcases hl : e.2.label t with a | c'
      · rw [hl] at this
        exact this.trans (Nat.one_le_pow _ _ (by omega))
      · rw [hl] at this
        have hlt := (h.step e he hcR t ht' c' (label_eq_inr.1 hl)).2
        exact this.trans (Nat.pow_le_pow_right (by omega) (by simpa using hlt))
    have hcard : (MethodDesc.toMethod e).subtasks.T.card ≤ B :=
      (List.toFinset_card_le _).trans (hB e he)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hchild
    rw [smul_eq_mul] at hsum
    have h1 : (MethodDesc.toMethod e).subtasks.T.card * (B + 1) ^ rk e.1 ≤ B * (B + 1) ^ rk e.1 :=
      Nat.mul_le_mul_right _ hcard
    have h2 : 1 ≤ (B + 1) ^ rk e.1 := Nat.one_le_pow _ _ (by omega)
    show 1 + _ ≤ (B + 1) ^ (rk e.1 + 1)
    rw [pow_succ]
    nlinarith

/-- A list of pairs whose keys lie in `T` is as long as its parts by key together. -/
theorem length_eq_sum_filter {T : Finset ℕ} : ∀ (w : List (ℕ × ℕ)), (∀ e ∈ w, e.1 ∈ T) →
    w.length = ∑ t ∈ T, (w.filter fun e => decide (e.1 = t)).length
  | [], _ => by simp
  | e :: w, h => by
    rw [List.length_cons, length_eq_sum_filter w (fun e' he' => h e' (by simp [he']))]
    have : ∀ t ∈ T, ((e :: w).filter fun e' => decide (e'.1 = t)).length =
        (w.filter fun e' => decide (e'.1 = t)).length + if e.1 = t then 1 else 0 := by
      intro t _
      by_cases het : e.1 = t <;> simp [List.filter_cons, het]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [h e (by simp)]

/-- **A yield is not longer than its tree.** -/
theorem length_le_size : ∀ (dt : DTree ℕ ℕ ℕ) (ys : List ℕ), dt.Yield ys → ys.length ≤ dt.size := by
  intro dt
  induction dt with
  | leaf a => intro ys hy; cases hy; simp [DTree.size]
  | node c m ch ih =>
    intro ys hy
    cases hy with
    | node yf hch hm =>
    obtain ⟨w, hw1, hw2, hw3, -⟩ := hm
    rw [← hw1, List.length_map, length_eq_sum_filter w hw2, DTree.size]
    have : ∑ t ∈ m.subtasks.T, (w.filter fun e => decide (e.1 = t)).length ≤
        ∑ t ∈ m.subtasks.T, (ch t).size := by
      apply Finset.sum_le_sum
      intro t ht
      have := ih t _ (hch t ht)
      rw [← hw3 t ht, List.length_map] at this
      exact this
    omega

/-- The merged yield of trees is not longer than the trees together. -/
theorem length_le_of_treesYield {M : Set (Method ℕ ℕ ℕ)} {tn : TaskNetwork ℕ ℕ ℕ}
    {trees : ℕ → DTree ℕ ℕ ℕ} {π : List ℕ} (h : TreesYield M tn trees π) :
    π.length ≤ ∑ t ∈ tn.T, (trees t).size := by
  obtain ⟨-, ys, hy, w, hw1, hw2, hw3, -⟩ := h
  rw [← hw1, List.length_map, length_eq_sum_filter w hw2]
  apply Finset.sum_le_sum
  intro t ht
  have := length_le_size _ _ (hy t ht)
  rw [← hw3 t ht, List.length_map] at this
  exact this

end Article

end HTN
