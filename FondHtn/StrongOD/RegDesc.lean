import FondHtn.StrongOD.Comp
import FondHtn.StrongOD.AcycPot
import HtnComplexity.Article.AcycRegNP
/-!
# Decomposition sequences on descriptions, and regular descriptions

* `FOND.SOD.DStep p` — one decomposition step on descriptions (`HTN.Article.decDesc`);
  `FOND.SOD.strongOD_iff_desc`: strong OD solvability is the existence of a description
  decomposition sequence from `tn_I` to a primitive description whose belief state is solvable.
* For a description with at most one compound task, ordered after all others
  (`HTN.Article.regB`): its primitive part `FOND.SOD.primD`, the list `FOND.SOD.compL` of the
  names of its compound tasks (at most one), and the structure of a decomposition step by a
  regular method: the old primitive tasks form a prefix of the new primitive part, and the
  new primitive tasks are an isomorphic copy of the method's primitive part.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false

variable {p : FProbDesc}

/-! ## Decomposition sequences on descriptions -/

/-- One decomposition step on descriptions. -/
def DStep (p : FProbDesc) (d d₁ : TnDesc) : Prop :=
  ∃ x e, x ∈ d.ids ∧ lblOf d x = (true, e.1) ∧ e ∈ p.methods ∧ d₁ = decDesc d x e

theorem dreach_sound (hp : p.Valid) {d d' : TnDesc} (h : Relation.ReflTransGen (DStep p) d d') :
    ∀ s, CfgInv (s, d) → ∀ tn₁ : TaskNetwork ℕ ℕ ℕ, tn₁.Agree (cfgNet d) →
      ∃ tn, HTN.DecomposesTo p.toProblem.methods tn₁ tn ∧ tn.Agree (cfgNet d') ∧
        CfgInv (s, d') := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun s hc tn₁ hag => ⟨tn₁, Relation.ReflTransGen.refl, hag, hc⟩
  | head h12 _ ih =>
    intro s hc tn₁ hag
    obtain ⟨x, e, hx, hl, he, rfl⟩ := h12
    obtain ⟨tn₂, hst, hag₂, hc₂⟩ := decStep_sound hp hc hx hl he hag
    obtain ⟨tn, hdec, hag', hc'⟩ := ih s hc₂ tn₂ hag₂
    exact ⟨tn, Relation.ReflTransGen.head ⟨x, _, hst⟩ hdec, hag', hc'⟩

theorem dreach_complete (hp : p.Valid) {tn₁ tn : TaskNetwork ℕ ℕ ℕ}
    (hdec : HTN.DecomposesTo p.toProblem.methods tn₁ tn) :
    tn₁.WF → ∀ σ s d, HTN.TaskNetwork.IsoVia σ tn₁ (cfgNet d) → CfgInv (s, d) →
      ∃ d' σ', Relation.ReflTransGen (DStep p) d d' ∧
        HTN.TaskNetwork.IsoVia σ' tn (cfgNet d') := by
  induction hdec using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ σ s d hσ _ => ⟨d, σ, Relation.ReflTransGen.refl, hσ⟩
  | @head tn₁ tn₂ h12 _ ih =>
    intro hwf σ s d hσ hc
    obtain ⟨t, m, hst⟩ := h12
    have hst0 := hst
    obtain ⟨⟨e, he, rfl⟩, htT, hαt, -⟩ := hst0
    have hxd : σ t ∈ d.ids := by simpa [cfgNet] using hσ.mem htT
    have hl : lblOf d (σ t) = (true, e.1) := by
      have h1 := (hσ.α_eq htT).trans hαt
      rw [cfgNet_label] at h1
      exact toSum_eq_inr.1 h1
    obtain ⟨tn₂', hst', hag', hc'⟩ := decStep_sound hp hc hxd hl he
      (HTN.TaskNetwork.Agree.refl (cfgNet d))
    obtain ⟨σ', hσ'⟩ := DecompStep.iso_of_isoVia hst hst' rfl hwf hc.wf hσ
    obtain ⟨d', σ'', hr, hiso⟩ := ih (hst.wf hwf) σ' s _ (IsoVia.of_agree hσ' hag') hc'
    exact ⟨d', σ'', Relation.ReflTransGen.head ⟨σ t, e, hxd, hl, he, rfl⟩ hr, hiso⟩

/-- **Strong OD solvability via description decomposition sequences.** -/
theorem strongOD_iff_desc (hp : p.Valid) :
    p.toProblem.StrongODSolvable ↔ ∃ d', Relation.ReflTransGen (DStep p) (d₀ p) d' ∧
      (∀ x ∈ d'.ids, (lblOf d' x).1 = false) ∧
      p.toProblem.BeliefSolvable (cfgNet d') {f | f ∈ p.init} := by
  rw [Problem.strongODSolvable_iff_fmSolvableDB]
  constructor
  · rintro ⟨tn, ⟨hdec, hprim⟩, hbs⟩
    obtain ⟨d', σ', hr, hσ⟩ := dreach_complete hp hdec (TnDesc.toTaskNetwork_wf _) id
      p.init.dedup (d₀ p) (isoVia_id_of_agree (agree_d₀ hp)) (inv_d₀ hp)
    refine ⟨d', hr, fun x hx => ?_, beliefSolvable_isoVia hbs hσ⟩
    have hxT : x ∈ (cfgNet d').T := by simpa [cfgNet] using hx
    obtain ⟨t, ht, rfl⟩ := hσ.surj hxT
    obtain ⟨a, ha⟩ := hprim t ht
    rw [lblOf_eq_of_α ((hσ.α_eq ht).trans ha)]
  · rintro ⟨d', hr, hprim, hbs⟩
    obtain ⟨tn, hdec, hag, -⟩ := dreach_sound hp hr _ (inv_d₀ hp) _ (agree_d₀ hp)
    refine ⟨tn, ⟨hdec, fun t ht => ?_⟩, Problem.BeliefSolvable.congr _ hbs (sameOn_of_agree hag.symm)⟩
    have htd : t ∈ d'.ids := by rw [hag.1] at ht; simpa [cfgNet] using ht
    exact ⟨_, (hag.2.2 t ht).trans (cfgNet_α_of_lbl (hprim t htd))⟩

/-! ## Primitive parts and compound names -/

/-- `x` is primitive in `t`. -/
def primB (t : TnDesc) (x : ℕ) : Bool := !(lblOf t x).1

/-- **The primitive part** of a description. -/
def primD (t : TnDesc) : TnDesc :=
  (t.ids.filter (primB t), (t.ordList.filter fun q => primB t q.1 && primB t q.2).dedup,
    t.lbl.filter fun q => !q.2.1)

/-- **The names of the compound tasks** of a description. -/
def compL (t : TnDesc) : List ℕ := (t.ids.filter fun x => (lblOf t x).1).map fun x => (lblOf t x).2

theorem lblOf_none {d : TnDesc} {x : ℕ} (h : d.lbl.lookup x = none) : lblOf d x = (false, 0) := by
  unfold lblOf; rw [h]; rfl

theorem lblOf_some {d : TnDesc} {x : ℕ} {v : Bool × ℕ} (h : d.lbl.lookup x = some v) :
    lblOf d x = v := by
  unfold lblOf; rw [h]; rfl

theorem lookup_eq_none_of_lookup_filter {l : List (ℕ × Bool × ℕ)} {f : ℕ × Bool × ℕ → Bool}
    {x : ℕ} (h : l.lookup x = none) : (l.filter f).lookup x = none := by
  rw [List.lookup_eq_none_iff] at h ⊢
  intro q hq
  exact h q (List.mem_filter.1 hq).1

/-- Primitive labels are kept in the primitive part. -/
theorem lblOf_primD {t : TnDesc} (hn : (t.lbl.map Prod.fst).Nodup) {x : ℕ}
    (hx : (lblOf t x).1 = false) : lblOf (primD t) x = lblOf t x := by
  cases hl : t.lbl.lookup x with
  | none =>
    rw [lblOf_none hl]
    exact lblOf_none (lookup_eq_none_of_lookup_filter hl)
  | some v =>
    rw [lblOf_some hl] at hx ⊢
    have hm := mem_of_lookup_eq_some hl
    have hm' : (x, v) ∈ (primD t).lbl := List.mem_filter.2 ⟨hm, by simp [hx]⟩
    have hn' : ((primD t).lbl.map Prod.fst).Nodup :=
      hn.sublist (List.filter_sublist.map _)
    exact lblOf_some (lookup_of_mem_nodup hn' hm')

theorem primB_primD {t : TnDesc} (hn : (t.lbl.map Prod.fst).Nodup) {x : ℕ}
    (hx : primB t x = true) : primB (primD t) x = true := by
  unfold primB at hx ⊢
  have hx' : (lblOf t x).1 = false := by simpa using hx
  rw [lblOf_primD hn hx', hx']; rfl

theorem mem_ordList_primD {t : TnDesc} {a b : ℕ} :
    (a, b) ∈ (primD t).ordList ↔ (a, b) ∈ t.ordList ∧ primB t a = true ∧ primB t b = true := by
  simp [primD, TnDesc.ordList]

theorem mem_ids_primD {t : TnDesc} {x : ℕ} :
    x ∈ (primD t).ids ↔ x ∈ t.ids ∧ primB t x = true := by
  simp [primD, TnDesc.ids]

/-- The primitive part is a well-behaved description. -/
theorem inv_primD {s₀ : List ℕ} {t : TnDesc} (hc : CfgInv (s₀, t)) {s : List ℕ} (hs : s.Nodup) :
    CfgInv (s, primD t) := by
  have hn : (t.lbl.map Prod.fst).Nodup := hc.lbl_nodup
  refine ⟨hc.ids_nodup.filter _, fun q hq => ?_, hn.sublist (List.filter_sublist.map _),
    List.nodup_dedup _, hs, ?_⟩
  · obtain ⟨hq, hq2⟩ := List.mem_filter.1 hq
    refine mem_ids_primD.2 ⟨hc.lbl_mem q hq, ?_⟩
    unfold primB
    rw [lblOf_of_mem hn hq]
    simpa using hq2
  · have hwf := hc.wf
    refine ⟨fun {a b} hab => ?_, fun {a b} hab => ?_, fun a haa => ?_, fun {a b c} hab hbc => ?_⟩
    · have hab' := mem_ordList_primD.1 hab
      exact List.mem_toFinset.2 (mem_ids_primD.2 ⟨List.mem_toFinset.1
        (hwf.mem_left (t := a) (t' := b) hab'.1), hab'.2.1⟩)
    · have hab' := mem_ordList_primD.1 hab
      exact List.mem_toFinset.2 (mem_ids_primD.2 ⟨List.mem_toFinset.1
        (hwf.mem_right (t := a) (t' := b) hab'.1), hab'.2.2⟩)
    · exact hwf.irrefl a (mem_ordList_primD.1 haa).1
    · have h1 := mem_ordList_primD.1 hab
      have h2 := mem_ordList_primD.1 hbc
      exact mem_ordList_primD.2 ⟨hwf.trans (show (cfgNet t).ord a b from h1.1)
        (show (cfgNet t).ord b c from h2.1), h1.2.1, h2.2.2⟩

/-- A primitive description agrees with its primitive part. -/
theorem sameOn_primD {s₀ : List ℕ} {t : TnDesc} (hc : CfgInv (s₀, t))
    (hprim : ∀ x ∈ t.ids, (lblOf t x).1 = false) :
    FOND.TaskNetwork.SameOn (cfgNet t) (cfgNet (primD t)) := by
  have hn : (t.lbl.map Prod.fst).Nodup := hc.lbl_nodup
  have hpB : ∀ x ∈ t.ids, primB t x = true := fun x hx => by simp [primB, hprim x hx]
  refine ⟨?_, fun a ha b hb => ?_, fun a ha => ?_⟩
  · ext x
    simp only [cfgNet, List.mem_toFinset, mem_ids_primD]
    exact ⟨fun h => ⟨h, hpB x h⟩, fun h => h.1⟩
  · have ha' : a ∈ t.ids := by simpa [cfgNet] using ha
    have hb' : b ∈ t.ids := by simpa [cfgNet] using hb
    show (a, b) ∈ t.ordList ↔ (a, b) ∈ (primD t).ordList
    rw [mem_ordList_primD]
    exact ⟨fun h => ⟨h, hpB a ha', hpB b hb'⟩, fun h => h.1⟩
  · have ha' : a ∈ t.ids := by simpa [cfgNet] using ha
    rw [cfgNet_label, cfgNet_label, lblOf_primD hn (hprim a ha')]

/-! ## Compound names of regular descriptions -/

theorem regB_iff' {t : TnDesc} : regB t = true ↔ ∀ x ∈ t.ids, (lblOf t x).1 = true →
    ∀ y ∈ t.ids, x = y ∨ ((lblOf t y).1 = false ∧ (y, x) ∈ t.ordList) := by
  simp only [regB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  cases (lblOf t x).1 <;> simp

theorem eq_singleton_of_nodup {l : List ℕ} (hn : l.Nodup) {x : ℕ} (hx : x ∈ l)
    (h : ∀ y ∈ l, y = x) : l = [x] := by
  cases l with
  | nil => simp at hx
  | cons a l =>
    have ha := h a List.mem_cons_self
    subst ha
    cases l with
    | nil => rfl
    | cons b l =>
      have hb := h b (by simp)
      subst hb
      simp at hn

theorem compL_eq_single {t : TnDesc} (hn : t.ids.Nodup) (hreg : regB t = true) {x c : ℕ}
    (hx : x ∈ t.ids) (hl : lblOf t x = (true, c)) : compL t = [c] := by
  have hfl : (t.ids.filter fun y => (lblOf t y).1) = [x] := by
    refine eq_singleton_of_nodup (hn.filter _) (List.mem_filter.2 ⟨hx, by rw [hl]⟩) ?_
    intro y hy
    obtain ⟨hy, hyc⟩ := List.mem_filter.1 hy
    rcases regB_iff'.1 hreg x hx (by rw [hl]) y hy with h | h
    · exact h.symm
    · rw [h.1] at hyc; cases hyc
  simp [compL, hfl, hl]

theorem compL_eq_nil {t : TnDesc} (h : ∀ x ∈ t.ids, (lblOf t x).1 = false) : compL t = [] := by
  simp only [compL, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx; simp [h x hx]

theorem compL_cases {t : TnDesc} (hn : t.ids.Nodup) (hreg : regB t = true) :
    (compL t = [] ∧ ∀ x ∈ t.ids, (lblOf t x).1 = false) ∨
      ∃ x ∈ t.ids, compL t = [(lblOf t x).2] ∧ (lblOf t x).1 = true := by
  by_cases h : ∃ x ∈ t.ids, (lblOf t x).1 = true
  · obtain ⟨x, hx, hc⟩ := h
    exact Or.inr ⟨x, hx, compL_eq_single hn hreg hx (lblOf_eq_of_fst hc), hc⟩
  · push_neg at h
    have h' : ∀ x ∈ t.ids, (lblOf t x).1 = false := fun x hx => by simpa using h x hx
    exact Or.inl ⟨compL_eq_nil h', h'⟩

end SOD

end FOND
