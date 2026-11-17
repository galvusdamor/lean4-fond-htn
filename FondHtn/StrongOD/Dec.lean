import FondHtn.StrongOD.Prim
import FondHtn.IsoLemmas
/-!
# The decomposition positions of the strong OD game

A decomposition position `(2, y, s, d)` (`FOND.SOD.decMoves`) decomposes some compound task of
`d` by some method of its name (`HTN.Article.decDesc`), or, if `d` is primitive, starts the play
(`FondHtn/StrongOD/Play.lean`).

* `FOND.SOD.dec_sound` — a won decomposition position yields an achievable primitive network
  (from any network agreeing with `cfgNet d`) whose belief state is solvable;
* `FOND.SOD.dec_complete` — conversely, a decomposition sequence to a primitive network with a
  solvable belief state is replayed on descriptions, up to isomorphism; the depth budget is
  controlled by a potential `Φ` that decreases along description decompositions.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

/-! ## Transport of solvable belief states -/

theorem beliefSolvable_isoVia {P : Problem ℕ ℕ ℕ ℕ} {tn : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ}
    (h : P.BeliefSolvable tn S) : ∀ {σ : ℕ → ℕ} {tn' : TaskNetwork ℕ ℕ ℕ},
      HTN.TaskNetwork.IsoVia σ tn tn' → P.BeliefSolvable tn' S := by
  induction h with
  | empty he => exact fun hσ => .empty (hσ.empty he)
  | step hu hα happ _ ih =>
    intro σ tn' hσ
    exact .step (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ
      fun s' hs' => ih s' hs' (hσ.progress hu.1)

theorem decomposeWith_agree {tn u : TaskNetwork ℕ ℕ ℕ} (h : tn.Agree u) (x : ℕ)
    (c : TaskNetwork ℕ ℕ ℕ) : (decomposeWith tn x c).Agree (decomposeWith u x c) := by
  obtain ⟨hT, ho, hα⟩ := h
  refine ⟨by simp [decomposeWith, hT], by simp [decomposeWith, ho], fun y hy => ?_⟩
  simp only [decomposeWith]
  split_ifs with hyc
  · rfl
  · simp only [decomposeWith, Finset.mem_union, Finset.mem_erase] at hy
    rcases hy with ⟨-, hy⟩ | hy
    · exact hα y hy
    · exact absurd hy hyc

/-! ## One decomposition step on descriptions -/

variable {p : FProbDesc}

theorem lblOf_eq_of_fst {d : TnDesc} {x : ℕ} (h : (lblOf d x).1 = true) :
    lblOf d x = (true, (lblOf d x).2) := by
  rw [← h]

/-- A description decomposition step is a semantic decomposition step of any network agreeing
with the description. -/
theorem decStep_sound (hp : p.Valid) {s : List ℕ} {d : TnDesc} (hc : CfgInv (s, d)) {x : ℕ}
    {e : MethodDesc} (hx : x ∈ d.ids) (hl : lblOf d x = (true, e.1)) (he : e ∈ p.methods)
    {tn₁ : TaskNetwork ℕ ℕ ℕ} (hag : tn₁.Agree (cfgNet d)) :
    ∃ tn₂, DecompStep p.toProblem.methods tn₁ x e.toMethod tn₂ ∧
      tn₂.Agree (cfgNet (decDesc d x e)) ∧ CfgInv (s, decDesc d x e) := by
  have hev := hp.methods e he
  set fr := freshIds d.ids e.2.ids.length with hfr
  have hfrn : fr.Nodup := freshIds_nodup _ _
  have hfrl : fr.length = e.2.ids.length := length_freshIds _ _
  refine ⟨decomposeWith tn₁ x (cfgNet (copyDesc e.2 fr)), ⟨⟨e, he, rfl⟩, ?_, ?_,
    cfgNet (copyDesc e.2 fr), wf_copyDesc hev hfrn hfrl,
    (HTN.TaskNetwork.IsoVia.iso (isoVia_copyDesc hev hfrn hfrl)).symm, ?_, rfl⟩, ?_,
    inv_decDesc hc hev⟩
  · rw [hag.1]; simpa [cfgNet] using hx
  · have hxT : x ∈ tn₁.T := by rw [hag.1]; simpa [cfgNet] using hx
    rw [hag.2.2 x hxT, cfgNet_label, hl]; rfl
  · rw [hag.1]; exact disjoint_copy e.2
  · exact (decomposeWith_agree hag x _).trans (agree_decDesc
      ⟨hc.ids_nodup, hc.lbl_mem, hc.lbl_nodup, hc.ord_nodup, List.nodup_nil, hc.wf⟩ hev)

theorem mem_decMoves {s : List ℕ} {d : TnDesc} {c : GCfg} :
    c ∈ decMoves p s d ↔ (∃ x ∈ d.ids, (lblOf d x).1 = true ∧ ∃ e ∈ p.methods,
      e.1 = (lblOf d x).2 ∧ c = (2, 0, s, decDesc d x e)) ∨
      ((∀ x ∈ d.ids, (lblOf d x).1 = false) ∧ c = (0, 0, s, d)) := by
  unfold decMoves
  simp only [List.mem_append, List.mem_flatMap]
  refine or_congr ?_ ?_
  · refine exists_congr fun x => and_congr_right fun _ => ?_
    cases hb : (lblOf d x).1
    · simp
    · simp only [cond_true, List.mem_map, List.mem_filter, beq_iff_eq, true_and]
      constructor
      · rintro ⟨e, ⟨he, h⟩, rfl⟩; exact ⟨e, he, h, rfl⟩
      · rintro ⟨e, he, h, rfl⟩; exact ⟨e, ⟨he, h⟩, rfl⟩
  · cases hb : d.ids.all (fun x => !(lblOf d x).1)
    · simp only [cond_false, List.not_mem_nil, false_iff, not_and]
      intro h
      rw [List.all_eq_false] at hb
      obtain ⟨x, hx, hx'⟩ := hb
      simp [h x hx] at hx'
    · simp only [cond_true, List.mem_singleton]
      rw [List.all_eq_true] at hb
      exact ⟨fun h => ⟨fun x hx => by simpa using hb x hx, h⟩, fun h => h.2⟩

theorem gameVal_dec (k : ℕ) (y : ℕ) (s : List ℕ) (d : TnDesc) :
    gameVal gacc guni gsuccs p (k + 1) (2, y, s, d) =
      (decMoves p s d).any (gameVal gacc guni gsuccs p k) := by
  rw [gameVal_succ']
  simp [gacc, guni, gsuccs]

/-- **Soundness of the decomposition positions.** -/
theorem dec_sound (hp : p.Valid) : ∀ k y s d, CfgInv (s, d) → ∀ tn₁ : TaskNetwork ℕ ℕ ℕ,
    tn₁.Agree (cfgNet d) → gameVal gacc guni gsuccs p k (2, y, s, d) = true →
      ∃ tn, HTN.DecomposesTo p.toProblem.methods tn₁ tn ∧ tn.IsPrimitive ∧
        p.toProblem.BeliefSolvable tn {f | f ∈ s} := by
  intro k
  induction k with
  | zero => intro y s d _ _ _ hw; simp [gameVal_zero', gacc] at hw
  | succ k ih =>
    intro y s d hc tn₁ hag hw
    rw [gameVal_dec, List.any_eq_true] at hw
    obtain ⟨c, hcm, hw⟩ := hw
    rcases mem_decMoves.1 hcm with ⟨x, hx, hb, e, he, he1, rfl⟩ | ⟨hprim, rfl⟩
    · have hl : lblOf d x = (true, e.1) := by rw [lblOf_eq_of_fst hb, he1]
      obtain ⟨tn₂, hstep, hag₂, hc₂⟩ := decStep_sound hp hc hx hl he hag
      obtain ⟨tn, hdec, hpr, hbs⟩ := ih 0 s _ hc₂ tn₂ hag₂ hw
      exact ⟨tn, Relation.ReflTransGen.head ⟨x, _, hstep⟩ hdec, hpr, hbs⟩
    · refine ⟨tn₁, Relation.ReflTransGen.refl, fun t ht => ?_, ?_⟩
      · have htd : t ∈ d.ids := by rw [hag.1] at ht; simpa [cfgNet] using ht
        exact ⟨_, (hag.2.2 t ht).trans (cfgNet_α_of_lbl (hprim t htd))⟩
      · exact Problem.BeliefSolvable.congr _ (play_sound k 0 s d hc hw)
          (sameOn_of_agree hag.symm)

/-- **Completeness of the decomposition positions**, for a potential `Φ` bounding the number of
tasks and decreasing along the description decompositions of the descriptions satisfying
`Good`. -/
theorem dec_complete (hp : p.Valid) {Good : TnDesc → Prop} {Φ : TnDesc → ℕ}
    (hΦ : ∀ d, Good d → d.ids.length ≤ Φ d)
    (hstep : ∀ s d x e, CfgInv (s, d) → Good d → x ∈ d.ids → lblOf d x = (true, e.1) →
      e ∈ p.methods → Good (decDesc d x e) ∧ Φ (decDesc d x e) < Φ d)
    {tn : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ} (hprim : tn.IsPrimitive)
    (hbs : p.toProblem.BeliefSolvable tn S) {tn₁ : TaskNetwork ℕ ℕ ℕ}
    (hdec : HTN.DecomposesTo p.toProblem.methods tn₁ tn) :
    tn₁.WF → ∀ σ s d k, HTN.TaskNetwork.IsoVia σ tn₁ (cfgNet d) → S = {f | f ∈ s} →
      CfgInv (s, d) → Good d → 2 * Φ d + 1 ≤ k →
        gameVal gacc guni gsuccs p k (2, 0, s, d) = true := by
  induction hdec using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ σ s d k hσ hS hc hg hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [gameVal_dec, List.any_eq_true]
    refine ⟨(0, 0, s, d), mem_decMoves.2 (Or.inr ⟨fun x hx => ?_, rfl⟩), ?_⟩
    · have hxT : x ∈ (cfgNet d).T := by simpa [cfgNet] using hx
      obtain ⟨t, ht, rfl⟩ := hσ.surj hxT
      obtain ⟨a, ha⟩ := hprim t ht
      have := lblOf_eq_of_α ((hσ.α_eq ht).trans ha)
      rw [this]
    · subst hS
      have := hΦ d hg
      exact play_complete (beliefSolvable_isoVia hbs hσ) k 0 s d
        (sameOn_of_agree (HTN.TaskNetwork.Agree.refl _)) rfl hc (by omega)
  | @head tn₁ tn₂ h12 _ ih =>
    intro hwf σ s d k hσ hS hc hg hk
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
    obtain ⟨hg', hΦ'⟩ := hstep s d (σ t) e hc hg hxd hl he
    have hiso := DecompStep.iso_of_isoVia hst hst' rfl hwf hc.wf hσ
    obtain ⟨σ', hσ'⟩ := hiso
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [gameVal_dec, List.any_eq_true]
    exact ⟨(2, 0, s, decDesc d (σ t) e), mem_decMoves.2 (Or.inl ⟨σ t, hxd, by rw [hl], e, he,
      by rw [hl], rfl⟩), ih (hst.wf hwf) σ' s _ k (IsoVia.of_agree hσ' hag') hS hc' hg' (by omega)⟩

end SOD

end FOND
