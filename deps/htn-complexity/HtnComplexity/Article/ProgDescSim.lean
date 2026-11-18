import HtnComplexity.Article.ProgDesc
/-!
# Progression on descriptions simulates progression

* `HTN.Article.succs_sound` — a step of `HTN.Article.succs` is a progression step of the
  configuration's network, up to agreement;
* `HTN.Article.succs_complete` — a progression step of a network isomorphic to the configuration's
  is matched by a step of `succs`, again up to isomorphism;
* **`HTN.Article.solvable_iff_cfg`** — a well-formed description has a solution iff a
  configuration with no tasks and a goal state is reachable from the initial one (with
  Thm. 4.2.12).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

theorem mem_succs {p : ProbDesc} {c c' : PCfg} : c' ∈ succs p c ↔ ∃ x ∈ c.2.ids,
    (∀ q ∈ c.2.ordList, q.2 ≠ x) ∧
      ((∃ e ∈ p.methods, lblOf c.2 x = (true, e.1) ∧ c' = (c.1, decDesc c.2 x e)) ∨
        (∃ a, lblOf c.2 x = (false, a) ∧ (runStep p (true, c.1) a).1 = true ∧
          c' = ((runStep p (true, c.1) a).2.dedup, progDesc c.2 x))) := by
  have hall : ∀ x, (c.2.ordList.all fun q => q.2 != x) = true ↔ ∀ q ∈ c.2.ordList, q.2 ≠ x := by
    intro x; simp [List.all_eq_true]
  unfold succs
  constructor
  · intro h
    obtain ⟨x, hx, hc'⟩ := List.mem_flatMap.1 h
    split_ifs at hc' with hu hb hr
    · obtain ⟨e, hef, rfl⟩ := List.mem_map.1 hc'
      obtain ⟨he, he1⟩ := List.mem_filter.1 hef
      refine ⟨x, hx, (hall x).1 hu, Or.inl ⟨e, he, Prod.ext hb ?_, rfl⟩⟩
      exact (beq_iff_eq.1 he1).symm
    · rw [List.mem_singleton] at hc'
      subst hc'
      exact ⟨x, hx, (hall x).1 hu, Or.inr ⟨(lblOf c.2 x).2, Prod.ext (by simpa using hb) rfl, hr,
        rfl⟩⟩
    · simp at hc'
    · simp at hc'
  · rintro ⟨x, hx, hu, ⟨e, he, hl, rfl⟩ | ⟨a, hl, hr, rfl⟩⟩
    · refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
      rw [if_pos ((hall x).2 hu), hl]
      simp only [↓reduceIte]
      exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp⟩, rfl⟩
    · refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
      rw [if_pos ((hall x).2 hu), hl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [if_pos hr]
      exact List.mem_singleton.2 rfl

theorem disjoint_copy {d : TnDesc} (k : TnDesc) :
    Disjoint (cfgNet d).T (cfgNet (copyDesc k (freshIds d.ids k.ids.length))).T := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  exact not_mem_of_mem_freshIds (by simpa [cfgNet, copyDesc] using hy') (by simpa [cfgNet] using hy)

theorem cfgNet_label {d : TnDesc} {x : ℕ} : (cfgNet d).α x = toSum (lblOf d x) :=
  label_eq_toSum d x

/-- **Soundness of a step.** -/
theorem succs_sound {p : ProbDesc} (hp : p.Valid) {c c' : PCfg} (hc : CfgInv c)
    (h : c' ∈ succs p c) (π : List ℕ) : CfgInv c' ∧ ∃ π' tn', p.toProblem.ProgStep
      ⟨{f | f ∈ c.1}, cfgNet c.2, π⟩ ⟨{f | f ∈ c'.1}, tn', π'⟩ ∧ tn'.Agree (cfgNet c'.2) := by
  obtain ⟨x, hx, hu, ⟨e, he, hl, rfl⟩ | ⟨a, hl, hr, rfl⟩⟩ := mem_succs.1 h
  · have hev := hp.methods e he
    refine ⟨inv_decDesc hc hev, π, _, .decomp (unconstrained_cfgNet hx hu)
      ⟨⟨e, he, rfl⟩, List.mem_toFinset.2 hx, by rw [cfgNet_label, hl]; rfl,
        cfgNet (copyDesc e.2 (freshIds c.2.ids e.2.ids.length)),
        wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _),
        (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso.symm,
        disjoint_copy _, rfl⟩,
      agree_decDesc ⟨hc.ids_nodup, hc.lbl_mem, hc.lbl_nodup, hc.ord_nodup, List.nodup_nil, hc.wf⟩
        hev⟩
  · have hst : (p.toProblem.δ a).apply {f | f ∈ c.1} =
        {f | f ∈ (runStep p (true, c.1) a).2.dedup} := by
      rw [← runStep_state p true c.1 a]; ext f; simp
    refine ⟨inv_progDesc hc hx hu (List.nodup_dedup _), π ++ [a], _, ?_, agree_progDesc hu⟩
    rw [← hst]
    exact .prog (unconstrained_cfgNet hx hu) (by rw [cfgNet_label, hl]; rfl)
      ((runStep_flag p true c.1 a).1 hr).2

/-- **Completeness of a step.** -/
theorem succs_complete {p : ProbDesc} (hp : p.Valid) {c : PCfg} (hc : CfgInv c)
    {nd nd' : PNode ℕ ℕ ℕ ℕ} (hstep : p.toProblem.ProgStep nd nd') (hst : nd.state = {f | f ∈ c.1})
    {σ : ℕ → ℕ} (hσ : IsoVia σ nd.net (cfgNet c.2)) (hwf : nd.net.WF) :
    ∃ c' ∈ succs p c, nd'.state = {f | f ∈ c'.1} ∧ ∃ σ', IsoVia σ' nd'.net (cfgNet c'.2) := by
  have hunc : ∀ {x : ℕ}, (cfgNet c.2).Unconstrained x → ∀ q ∈ c.2.ordList, q.2 ≠ x := by
    intro x hu q hq e
    have h1 : (cfgNet c.2).ord q.1 x := by rw [← e]; exact hq
    exact hu.2 q.1 (hc.wf.mem_left h1) h1
  cases hstep with
  | @prog s tn π t a hu hα happ =>
    dsimp only at hst hσ hwf ⊢
    have hu' := hσ.unconstrained hu
    have hx : σ t ∈ c.2.ids := List.mem_toFinset.1 hu'.1
    have hl : lblOf c.2 (σ t) = (false, a) := by
      rw [← toSum_eq_inl, ← cfgNet_label, ← hσ.2.2 t hu.1, hα]
    have hr : (runStep p (true, c.1) a).1 = true :=
      (runStep_flag p true c.1 a).2 ⟨rfl, hst ▸ happ⟩
    refine ⟨_, mem_succs.2 ⟨σ t, hx, hunc hu', Or.inr ⟨a, hl, hr, rfl⟩⟩, ?_, σ,
      (hσ.progress hu.1).of_agree (agree_progDesc (hunc hu'))⟩
    rw [hst, ← runStep_state p true c.1 a]; ext f; simp
  | @decomp s tn tn₂ π t m hu hd =>
    dsimp only at hst hσ hwf ⊢
    obtain ⟨⟨e, he, rfl⟩, ht, hαt, tn'', hwf'', hiso, hdisj, rfl⟩ := hd
    have hev := hp.methods e he
    have hu' := hσ.unconstrained hu
    have hx : σ t ∈ c.2.ids := List.mem_toFinset.1 hu'.1
    have hl : lblOf c.2 (σ t) = (true, e.1) := by
      rw [← toSum_eq_inr, ← cfgNet_label, ← hσ.2.2 t ht, hαt]; rfl
    obtain ⟨σ', hσ', -, -⟩ := hσ.decomposeWith hwf hc.wf ht hwf''
      (wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _))
      (hiso.trans (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso) hdisj
      (disjoint_copy _)
    exact ⟨_, mem_succs.2 ⟨σ t, hx, hunc hu', Or.inl ⟨e, he, hl, rfl⟩⟩, hst, σ',
      hσ'.of_agree (agree_decDesc ⟨hc.ids_nodup, hc.lbl_mem, hc.lbl_nodup, hc.ord_nodup,
        List.nodup_nil, hc.wf⟩ hev)⟩

/-! ### The initial configuration -/

theorem agree_initCfg {p : ProbDesc} (hp : p.Valid) :
    p.toProblem.tnI.Agree (cfgNet (initCfg p).2) := by
  refine ⟨rfl, ?_, fun _ _ => rfl⟩
  funext a b
  simp only [ProbDesc.toProblem, TnDesc.toTaskNetwork, cfgNet, initCfg, TnDesc.ordList,
    List.mem_dedup, eq_iff_iff]
  exact hp.tnI.ordOf_iff

theorem inv_initCfg {p : ProbDesc} (hp : p.Valid) : CfgInv (initCfg p) := by
  have hperm := hp.tnI.lbl_perm
  refine ⟨hp.tnI.nodup, fun q hq => hperm.subset (List.mem_map.2 ⟨q, hq, rfl⟩),
    hperm.nodup_iff.2 hp.tnI.nodup, List.nodup_dedup _, List.nodup_dedup _, ?_⟩
  exact (TnDesc.toTaskNetwork_wf p.tnI).of_agree (agree_initCfg hp)

/-! ### Solutions -/

/-- **Plan existence via progression on descriptions.** -/
theorem solvable_iff_cfg {p : ProbDesc} (hp : p.Valid) :
    p.toProblem.Solvable ↔ ∃ c, Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c ∧
      c.2.ids = [] ∧ goalB p c.1 = true := by
  rw [Problem.thm_4_2_12_htn (wf_toProblem p)]
  constructor
  · rintro ⟨nd, hr, hg⟩
    -- follow the progression, up to isomorphism
    have key : ∀ nd, p.toProblem.ProgReach nd → ∃ c σ, Relation.ReflTransGen
        (fun c c' => c' ∈ succs p c) (initCfg p) c ∧ CfgInv c ∧ nd.state = {f | f ∈ c.1} ∧
        IsoVia σ nd.net (cfgNet c.2) ∧ nd.net.WF := by
      intro nd hr
      induction hr with
      | refl =>
        refine ⟨initCfg p, id, .refl, inv_initCfg hp, ?_, isoVia_id_of_agree (agree_initCfg hp),
          (wf_toProblem p).tnI⟩
        ext f; simp [initCfg, Problem.initPNode, ProbDesc.toProblem]
      | @tail n₁ n₂ _ hs ih =>
        obtain ⟨c, σ, hrc, hc, hst, hσ, hwf⟩ := ih
        obtain ⟨c', hc', hst', σ', hσ'⟩ := succs_complete hp hc hs hst hσ hwf
        have hwf' : n₂.net.WF := by
          cases hs with
          | prog hu _ _ => exact TaskNetwork.progress_wf hwf hu
          | decomp _ hd => exact hd.wf hwf
        exact ⟨c', σ', hrc.tail hc', (succs_sound hp hc hc' []).1, hst', hσ', hwf'⟩
    obtain ⟨c, σ, hrc, -, hst, hσ, -⟩ := key nd hr
    refine ⟨c, hrc, ?_, (goalB_iff p c.1).2 (hst ▸ hg.2)⟩
    have hT : (cfgNet c.2).T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨a, ha, -⟩ := hσ.surj hy
      rw [hg.1] at ha
      simp at ha
    simpa [cfgNet] using hT
  · rintro ⟨c, hrc, hids, hgoal⟩
    have key : ∀ c, Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c →
        CfgInv c ∧ ∃ nd, p.toProblem.ProgReach nd ∧ nd.state = {f | f ∈ c.1} ∧
          nd.net.Agree (cfgNet c.2) := by
      intro c hrc
      induction hrc with
      | refl =>
        refine ⟨inv_initCfg hp, _, .refl, ?_, agree_initCfg hp⟩
        ext f; simp [initCfg, Problem.initPNode, ProbDesc.toProblem]
      | @tail c₁ c₂ _ hs ih =>
        obtain ⟨hc, nd, hnd, hst, hag⟩ := ih
        obtain ⟨hc', π', tn', hstep, hag'⟩ := succs_sound hp hc hs nd.plan
        obtain ⟨B', hstep', hagB⟩ := Problem.ProgStep.agree p.toProblem hstep hag.symm
        refine ⟨hc', ⟨{f | f ∈ c₂.1}, B', π'⟩, hnd.tail ?_, rfl, hagB.symm.trans hag'⟩
        have : nd = ⟨{f | f ∈ c₁.1}, nd.net, nd.plan⟩ := by rw [← hst]
        rw [this]
        exact hstep'
    obtain ⟨-, nd, hnd, hst, hag⟩ := key c hrc
    refine ⟨nd, hnd, ?_, hst ▸ (goalB_iff p c.1).1 hgoal⟩
    rw [hag.1]
    simp [cfgNet, hids]

end Article

end HTN
