import FondHtn.MPStrong.CyclicDesc
/-!
# The fair game on descriptions, without a size bound

`FondHtn/MPStrong/CyclicDesc.lean` plays the fair progression game on descriptions with an
attractor over configurations of bounded size (`HTN.Syn.PolyDom.BAttr`), which is what the
decision procedures for the restricted classes need.  For unrestricted problems there is no
bound; **`FOND.FS.fair_iff_uWin`**: fair solvability of a well-formed description is the
unbounded fair game `FOND.FS.UWin` on its description-level configurations.  The proofs are those
of `CyclicDesc.lean` without the size side conditions.
-/

namespace FOND

namespace FS

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

section Game

variable {α σ : Type}

/-- **The unbounded attractor** of the accepting configurations with respect to `X`. -/
inductive UAttr (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (a : α) (X : σ → Prop) :
    σ → Prop
  | acc {c : σ} : acc (a, c) = true → UAttr acc uni step a X c
  | ex {c c' : σ} : uni (a, c) = false → step (a, c, c') = true → X c' →
      UAttr acc uni step a X c' → UAttr acc uni step a X c
  | univ {c c' : σ} : uni (a, c) = true → (∀ c'', step (a, c, c'') = true → X c'') →
      step (a, c, c') = true → UAttr acc uni step a X c' → UAttr acc uni step a X c

/-- **The unbounded fair game**: a set containing `c` every element of which is in its
attractor. -/
def UWin (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (a : α) (c : σ) : Prop :=
  ∃ X : σ → Prop, X c ∧ ∀ c', X c' → UAttr acc uni step a X c'

end Game

section Correct

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β] {p : FProbDesc} {b : β}

/-- **Soundness**: configurations in the attractor of a set `X` are won semantically, with
respect to the semantic set of `X`. -/
theorem uattr_sound (hp : p.Valid) {X : β × GNode → Prop}
    {g : β × GNode} (hw : UAttr gAcc gUni gStep p X g) : GReach p b g →
      (g.2.1.1 = false → ∃ n, p.toProblem.FAttrH true (semSet p b X) n (cfgNet g.2.2.2)
        {f | f ∈ g.2.2.1}) ∧
      (g.2.1.1 = true → (∀ S' ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1},
        semSet p b X ((cfgNet g.2.2.2).progress g.2.1.2) S') ∧
        ∃ s₀ ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1}, ∃ n,
          p.toProblem.FAttrH true (semSet p b X) n ((cfgNet g.2.2.2).progress g.2.1.2) s₀) := by
  induction hw with
  | @acc c ha =>
    intro _
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := c
    simp only [gAcc, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at ha
    obtain ⟨rfl, hids⟩ := ha
    refine ⟨fun _ => ⟨0, .goal ?_⟩, fun h => absurd h (by simp)⟩
    simp [cfgNet, hids]
  | @ex c c' hu hs hX _ ih =>
    intro hr
    have hr' : GReach p b c' := hr.tail hs
    have ih' := ih hr'
    have hinv := (gInv_of_reach hp hr).inv
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := c
    simp only [gUni] at hu
    subst hu
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨b', g'⟩ := c'
    simp only at hs ih' hr'
    rcases nodeSuccs_ex hs.2 with ⟨x, hx, hu, e, he, hl, rfl⟩ | ⟨x, hx, hok, rfl⟩
    · obtain ⟨n, hn⟩ := ih'.1 rfl
      obtain ⟨tn', hd, hiso⟩ := decStep_of_desc hp hinv hx he hl
      obtain ⟨τ, hτ, -⟩ := hiso.exists_inv
      have hwd := (gInv_of_reach hp hr').inv.wf
      have hD := semSet_mem hp hr' rfl hX
      simp only at hD hwd
      exact ⟨n + 1, .decomp (fun _ => unconstrained_cfgNet hx ((unc_iff _ _).1 hu)) hd
        ((semSet_good X).2 _ _ _ _ hD (hd.wf hinv.wf) hτ)
        (hn.isoVia (semSet_good X) hwd (hd.wf hinv.wf) hτ)⟩
    · obtain ⟨hl, hu, happ⟩ := lbl_false_of_primOk hok
      obtain ⟨hall, s₀, hs₀, n, hn⟩ := ih'.2 rfl
      exact ⟨n + 1, .prim (unconstrained_cfgNet hx ((unc_iff _ _).1 hu))
        (by rw [cfgNet_label, hl]; rfl) ((fApp_iff _ _ _).1 happ) hall hs₀ hn⟩
  | @univ c c' hu hall hs _ ih =>
    intro hr
    have hgi := gInv_of_reach hp hr
    have hr' : GReach p b c' := hr.tail hs
    have ih' := ih hr'
    obtain ⟨b₀, ⟨tg, x⟩, s, d⟩ := c
    simp only [gUni] at hu
    subst hu
    obtain ⟨hx, hok⟩ := hgi.tagT rfl
    have hinv := hgi.inv
    simp only at hx hok hinv
    obtain ⟨-, hu, -⟩ := lbl_false_of_primOk hok
    have hu' := (unc_iff _ _).1 hu
    have hwp := TaskNetwork.progress_wf hinv.wf (unconstrained_cfgNet hx hu')
    refine ⟨fun h => absurd h (by simp), fun _ => ⟨fun S' hS' => ?_, ?_⟩⟩
    · obtain ⟨s', hs', rfl⟩ := outs_complete hS'
      have hst : gStep (p, (b₀, ((true, x), (s, d))), (b₀, ((false, 0), (s', progDesc d x)))) =
          true := by
        simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
        exact mem_nodeSuccs_out hs'
      have hr'' := hr.tail hst
      have hD := semSet_mem hp hr'' rfl (hall _ hst)
      simp only at hD
      exact (semSet_good X).2 _ _ _ _ hD hwp
        (isoVia_art (isoVia_id_of_agree (agree_progDesc hu').symm))
    · simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨b', g'⟩ := c'
      simp only at hs ih' hr'
      obtain ⟨rfl, hs⟩ := hs
      obtain ⟨s', hs', rfl⟩ := nodeSuccs_univ hs
      obtain ⟨n, hn⟩ := ih'.1 rfl
      refine ⟨_, outs_sound hs', n, ?_⟩
      exact hn.isoVia (semSet_good X) (inv_progDesc hinv hx hu' (nodup_of_mem_outs hs')).wf hwp
        (isoVia_art (isoVia_id_of_agree (agree_progDesc hu').symm))

/-- **Soundness of the fair game on descriptions.** -/
theorem fairWin_of_uWin (hp : p.Valid)
    (hw : UWin gAcc gUni gStep p (b, ((false, 0), initF p))) :
    p.toProblem.FairWin true (cfgNet (initF p).2) {f | f ∈ (initF p).1} := by
  obtain ⟨X, hX₀, hXa⟩ := hw
  refine ⟨semSet p b X, semSet_good X, semSet_mem hp .refl rfl hX₀, fun tn S hD => ?_⟩
  obtain ⟨hw, g, σ, hg, htag, hX, rfl, hσ⟩ := hD
  obtain ⟨n, hn⟩ := (uattr_sound hp (hXa g hX) hg).1 htag
  exact ⟨n, hn.isoVia (semSet_good X) (gInv_of_reach hp hg).inv.wf hw hσ⟩

/-- **Completeness**: a reachable existential configuration matching a node of the semantic
attractor is in the attractor of `cfgSet`. -/
theorem uattr_complete (hp : p.Valid)
    {D : Problem.NSet ℕ ℕ ℕ ℕ} (hD : Problem.NGood D) {n : ℕ} {tn : TaskNetwork ℕ ℕ ℕ}
    {S : Set ℕ} (h : p.toProblem.FAttrH true D n tn S) :
    ∀ {g : β × GNode} {σ : ℕ → ℕ}, GReach p b g → g.2.1.1 = false → S = {f | f ∈ g.2.2.1} →
      tn.WF → HTN.TaskNetwork.IsoVia σ tn (cfgNet g.2.2.2) →
        UAttr gAcc gUni gStep p (cfgSet p b D) g := by
  induction h with
  | goal he =>
    intro g σ hr htag _ _ hσ
    refine UAttr.acc ?_
    have hT := hσ.empty he
    simp only [cfgNet, List.toFinset_eq_empty_iff] at hT
    simp [gAcc, htag, hT]
  | @prim n tn S t a hu hα happ hall s₀ hs₀ h₀ ih =>
    intro g σ hr htag hS hwf hσ
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    simp only at htag hS hσ
    subst htag hS
    have hy := hgi.tagF rfl
    have hinv := hgi.inv
    have hcert := hgi.cert
    simp only at hy hinv hcert
    subst hy hcert
    obtain ⟨hx, hunc⟩ := unc_of_isoVia hinv hσ hu
    have hl : lblOf d (σ t) = (false, a) := by
      rw [← toSum_eq_inl, ← cfgNet_label, ← hσ.2.2 t hu.1, hα]
    have hok : primOk p (s, d) (σ t) = true := by
      simp only [primOk, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨(unc_iff _ _).2 hunc, by rw [hl]⟩, ?_⟩
      rw [hl]; exact (fApp_iff _ _ _).2 happ
    have hs₁ : gStep (p, (b₀, ((false, 0), (s, d))), (b₀, ((true, σ t), (s, d)))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_prim hx hok
    have hr₁ := hr.tail hs₁
    have hwp := TaskNetwork.progress_wf hwf hu
    have hwp' := TaskNetwork.progress_wf hinv.wf (unconstrained_cfgNet hx hunc)
    have hσp : HTN.TaskNetwork.IsoVia σ (tn.progress t) ((cfgNet d).progress (σ t)) :=
      hσ.progress hu.1
    have hall' : ∀ S' ∈ (p.δ (lblOf d (σ t)).2).outcomes {f | f ∈ s},
        D ((cfgNet d).progress (σ t)) S' := by
      rw [hl]; exact fun S' hS' => hD.2 _ _ _ _ (hall S' hS') hwp' hσp
    -- the universal configuration is in the set and in the attractor
    obtain ⟨s₀', hs₀', rfl⟩ := outs_complete hs₀
    have hst₀ : gStep (p, (b₀, ((true, σ t), (s, d))),
        (b₀, ((false, 0), (s₀', progDesc d (σ t))))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_out (by rw [hl]; exact hs₀')
    have hr₀ := hr₁.tail hst₀
    have hB₀ : UAttr gAcc gUni gStep p (cfgSet p b₀ D) (b₀, ((false, 0), (s₀', progDesc d (σ t)))) :=
      ih hr₀ rfl rfl hwp ((isoVia_of_art hσp).of_agree (agree_progDesc hunc))
    have hX₁ : cfgSet p b₀ D (b₀, ((true, σ t), (s, d))) := by
      refine ⟨hr₁, Or.inr ⟨rfl, hall', ?_⟩⟩
      rw [hl]
      exact ⟨_, hs₀, n, h₀.isoVia hD hwp hwp' hσp⟩
    refine UAttr.ex (by simp [gUni]) hs₁ hX₁ ?_
    exact UAttr.univ (by simp [gUni])
      (fun c'' hs'' => cfgSet_univ_succ hp hD hr₁ hall' hs'') hst₀ hB₀
  | @decomp n tn tn' S t m hu hd hDt _ ih =>
    intro g σ hr htag hS hwf hσ
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    simp only at htag hS hσ
    subst htag hS
    have hy := hgi.tagF rfl
    have hinv := hgi.inv
    have hcert := hgi.cert
    simp only at hy hinv hcert
    subst hy hcert
    have hwf' := hd.wf hwf
    have hu₁ := hu rfl
    obtain ⟨⟨e, he, rfl⟩, ht, hαt, tn'', hwf'', hiso, hdisj, rfl⟩ := hd
    have hev := hp.methods e he
    obtain ⟨hx, hunc⟩ := unc_of_isoVia hinv hσ hu₁
    have hl : lblOf d (σ t) = (true, e.1) := by
      rw [← toSum_eq_inr, ← cfgNet_label, ← hσ.2.2 t ht, hαt]; rfl
    obtain ⟨σ', hσ', -, -⟩ := (isoVia_of_art hσ).decomposeWith hwf hinv.wf ht hwf''
      (wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _))
      (hiso.trans (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso) hdisj
      (disjoint_copy _)
    have hσ'' := isoVia_art (hσ'.of_agree (agree_decDesc ⟨hinv.ids_nodup, hinv.lbl_mem,
      hinv.lbl_nodup, hinv.ord_nodup, List.nodup_nil, hinv.wf⟩ hev))
    have hs₁ : gStep (p, (b₀, ((false, 0), (s, d))),
        (b₀, ((false, 0), (s, decDesc d (σ t) e)))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_dec hx ((unc_iff _ _).2 hunc) he hl
    have hr₁ := hr.tail hs₁
    have hX₁ : cfgSet p b₀ D (b₀, ((false, 0), (s, decDesc d (σ t) e))) :=
      ⟨hr₁, Or.inl ⟨rfl, hD.2 _ _ _ _ hDt (inv_decDesc hinv hev).wf hσ''⟩⟩
    exact UAttr.ex (by simp [gUni]) hs₁ hX₁ (ih hr₁ rfl rfl hwf' hσ'')

/-- **Completeness of the fair game on descriptions.** -/
theorem uWin_of_fairWin (hp : p.Valid)
    (h : p.toProblem.FairWin true (cfgNet (initF p).2) {f | f ∈ (initF p).1}) :
    UWin gAcc gUni gStep p (b, ((false, 0), initF p)) := by
  obtain ⟨D, hD, hD₀, hDa⟩ := h
  refine ⟨cfgSet p b D, ⟨.refl, Or.inl ⟨rfl, hD₀⟩⟩, fun g hg => ?_⟩
  obtain ⟨hr, ⟨htag, hDg⟩ | ⟨htag, hall, s₀, hs₀, n, hn⟩⟩ := hg
  · obtain ⟨n, hn⟩ := hDa _ _ hDg
    exact uattr_complete hp hD hn hr htag rfl (hD.1 _ _ hDg) (HTN.TaskNetwork.IsoVia.refl _)
  · have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, x⟩, s, d⟩ := g
    simp only at htag hall hs₀ hn
    subst htag
    have hcert := hgi.cert
    simp only at hcert
    subst hcert
    obtain ⟨hx, hok⟩ := hgi.tagT rfl
    have hinv := hgi.inv
    simp only at hx hok hinv
    obtain ⟨-, hu, -⟩ := lbl_false_of_primOk hok
    have hu' := (unc_iff _ _).1 hu
    obtain ⟨s₀', hs₀', rfl⟩ := outs_complete hs₀
    have hst₀ : gStep (p, (b₀, ((true, x), (s, d))),
        (b₀, ((false, 0), (s₀', progDesc d x)))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_out hs₀'
    have hr₀ := hr.tail hst₀
    have hwp := TaskNetwork.progress_wf hinv.wf (unconstrained_cfgNet hx hu')
    exact UAttr.univ (by simp [gUni])
      (fun c'' hs'' => cfgSet_univ_succ hp hD hr hall hs'') hst₀
      (uattr_complete hp hD hn hr₀ rfl rfl hwp
        (isoVia_art (isoVia_id_of_agree (agree_progDesc hu'))))

end Correct

/-- **Fair solvability is the unbounded fair game on descriptions.** -/
theorem fair_iff_uWin {p : FProbDesc} (hp : p.Valid) :
    p.toProblem.MPStrongCyclicFairSolvable ↔
      UWin gAcc gUni gStep p ((0 : ℕ), ((false, 0), initF p)) := by
  rw [fair_iff_initF hp]
  exact ⟨uWin_of_fairWin hp, fairWin_of_uWin hp⟩

end FS

end FOND
