import FondHtn.MPStrong.CyclicGame
import FondHtn.MPStrong.Acyc
import FondHtn.Alt.Buchi
/-!
# Fair strong cyclic plan existence on descriptions: `EXPTIME` / `2-EXPTIME`

The progression fair game `FOND.Problem.FairWin true` (`FondHtn/MPStrong/CyclicGame.lean`)
played on descriptions, with the nodes, moves and size bounds of `FondHtn/MPStrong/Game.lean`,
decided as a fair AND-OR game (`HTN.Syn.PolyDom.BWin`, `FondHtn/Alt/Buchi.lean`).

* `FOND.MPS.fairWin_of_bWin` / `FOND.MPS.bWin_of_fairWin` — soundness and completeness of the
  description-level game;
* `FOND.MPS.inExpTime_planExMPFair`, `FOND.MPS.inExp2Time_planExMPFair` — the generic
  memberships (polynomial resp. exponential certificates and progression bounds);
* **`FOND.fairMP_REG_mem`** ([CB22, Thm. 3], strong cyclic, fair reading) and
  `FOND.fairMP_REG_TO_mem`;
* **`FOND.fairMP_TR_TO_mem`** ([CB22, Thm. 4], fair reading);
* **`FOND.fairMP_TR_mem`** — `2-EXPTIME` ([CB22, Thm. 5], fair reading).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

namespace MPS

section Correct

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β] {p : FProbDesc} {b : β} {B : ℕ}

/-- A decomposition on descriptions as a semantic decomposition step, up to agreement. -/
theorem decStep_of_desc (hp : p.Valid) {s : List ℕ} {d : TnDesc} {x : ℕ} {e : MethodDesc}
    (hinv : CfgInv (s, d)) (hx : x ∈ d.ids) (he : e ∈ p.methods) (hl : lblOf d x = (true, e.1)) :
    ∃ tn', DecompStep p.toProblem.methods (cfgNet d) x e.toMethod tn' ∧
      HTN.TaskNetwork.IsoVia id tn' (cfgNet (decDesc d x e)) := by
  have hev := hp.methods e he
  refine ⟨_, ⟨⟨e, he, rfl⟩, List.mem_toFinset.2 hx, by rw [cfgNet_label, hl]; rfl,
    cfgNet (copyDesc e.2 (freshIds d.ids e.2.ids.length)),
    wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _),
    (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso.symm,
    disjoint_copy _, rfl⟩, isoVia_art (isoVia_id_of_agree (agree_decDesc ⟨hinv.ids_nodup,
      hinv.lbl_mem, hinv.lbl_nodup, hinv.ord_nodup, List.nodup_nil, hinv.wf⟩ hev))⟩

/-! ### Soundness -/

/-- The semantic set of a set of configurations: networks isomorphic to the networks of
reachable existential configurations of `X`. -/
def semSet (p : FProbDesc) (b : β) (X : β × GNode → Prop) : Problem.NSet ℕ ℕ ℕ ℕ :=
  fun tn S => tn.WF ∧ ∃ (g : β × GNode) (σ : ℕ → ℕ), GReach p b g ∧ g.2.1.1 = false ∧ X g ∧
    S = {f | f ∈ g.2.2.1} ∧ HTN.TaskNetwork.IsoVia σ (cfgNet g.2.2.2) tn

theorem semSet_good (X : β × GNode → Prop) : Problem.NGood (semSet p b X) := by
  refine ⟨fun _ _ h => h.1, fun tn tn' S σ h hw' hσ => ?_⟩
  obtain ⟨-, g, τ, hg, htag, hX, hS, hτ⟩ := h
  exact ⟨hw', g, σ ∘ τ, hg, htag, hX, hS, hτ.comp hσ⟩

theorem semSet_mem (hp : p.Valid) {X : β × GNode → Prop} {g : β × GNode} (hg : GReach p b g)
    (htag : g.2.1.1 = false) (hX : X g) : semSet p b X (cfgNet g.2.2.2) {f | f ∈ g.2.2.1} :=
  ⟨(gInv_of_reach hp hg).inv.wf, g, id, hg, htag, hX, rfl, HTN.TaskNetwork.IsoVia.refl _⟩

/-- **Soundness**: configurations in the attractor of a set `X` are won semantically, with
respect to the semantic set of `X`. -/
theorem attr_sound (hp : p.Valid) (hsz : ∀ g, GReach p b g → sz g ≤ B) {X : β × GNode → Prop}
    {g : β × GNode} (hw : BAttr B gAcc gUni gStep p X g) : GReach p b g →
      (g.2.1.1 = false → ∃ n, p.toProblem.FAttrH true (semSet p b X) n (cfgNet g.2.2.2)
        {f | f ∈ g.2.2.1}) ∧
      (g.2.1.1 = true → (∀ S' ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1},
        semSet p b X ((cfgNet g.2.2.2).progress g.2.1.2) S') ∧
        ∃ s₀ ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1}, ∃ n,
          p.toProblem.FAttrH true (semSet p b X) n ((cfgNet g.2.2.2).progress g.2.1.2) s₀) := by
  induction hw with
  | @acc c _ ha =>
    intro _
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := c
    simp only [gAcc, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at ha
    obtain ⟨rfl, hids⟩ := ha
    refine ⟨fun _ => ⟨0, .goal ?_⟩, fun h => absurd h (by simp)⟩
    simp [cfgNet, hids]
  | @ex c c' _ hu _ hs hX _ ih =>
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
  | @univ c c' _ hu hall _ hs _ ih =>
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
      have hD := semSet_mem hp hr'' rfl (hall _ (hsz _ hr'') hst)
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
theorem fairWin_of_bWin (hp : p.Valid) (hsz : ∀ g, GReach p b g → sz g ≤ B)
    (hw : BWin B gAcc gUni gStep p (b, ((false, 0), initF p))) :
    p.toProblem.FairWin true (cfgNet (initF p).2) {f | f ∈ (initF p).1} := by
  obtain ⟨X, hX₀, hXa⟩ := hw
  refine ⟨semSet p b X, semSet_good X, semSet_mem hp .refl rfl hX₀, fun tn S hD => ?_⟩
  obtain ⟨hw, g, σ, hg, htag, hX, rfl, hσ⟩ := hD
  obtain ⟨n, hn⟩ := (attr_sound hp hsz (hXa g hX) hg).1 htag
  exact ⟨n, hn.isoVia (semSet_good X) (gInv_of_reach hp hg).inv.wf hw hσ⟩

/-! ### Completeness -/

/-- The configurations of a semantic set `D`: reachable existential configurations whose
network is in `D`, and reachable universal configurations whose outcomes are in `D` and one of
which is won. -/
def cfgSet (p : FProbDesc) (b : β) (D : Problem.NSet ℕ ℕ ℕ ℕ) (g : β × GNode) : Prop :=
  GReach p b g ∧
    ((g.2.1.1 = false ∧ D (cfgNet g.2.2.2) {f | f ∈ g.2.2.1}) ∨
      (g.2.1.1 = true ∧
        (∀ S' ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1},
          D ((cfgNet g.2.2.2).progress g.2.1.2) S') ∧
        ∃ s₀ ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1}, ∃ n,
          p.toProblem.FAttrH true D n ((cfgNet g.2.2.2).progress g.2.1.2) s₀))

/-- The successors of a universal configuration of `cfgSet` are in `cfgSet`. -/
theorem cfgSet_univ_succ (hp : p.Valid) {D : Problem.NSet ℕ ℕ ℕ ℕ} (hD : Problem.NGood D)
    {x : ℕ} {s : List ℕ} {d : TnDesc} (hr : GReach p b (b, ((true, x), (s, d))))
    (hall : ∀ S' ∈ (p.δ (lblOf d x).2).outcomes {f | f ∈ s}, D ((cfgNet d).progress x) S')
    {g' : β × GNode} (hs : gStep (p, (b, ((true, x), (s, d))), g') = true) :
    cfgSet p b D g' := by
  have hgi := gInv_of_reach hp hr
  obtain ⟨hx, hok⟩ := hgi.tagT rfl
  have hinv := hgi.inv
  simp only at hx hok hinv
  obtain ⟨-, hu, -⟩ := lbl_false_of_primOk hok
  have hu' := (unc_iff _ _).1 hu
  have hr' := hr.tail hs
  obtain ⟨b', g''⟩ := g'
  simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨rfl, hs⟩ := hs
  obtain ⟨s', hs', rfl⟩ := nodeSuccs_univ hs
  refine ⟨hr', Or.inl ⟨rfl, ?_⟩⟩
  exact hD.2 _ _ _ _ (hall _ (outs_sound hs')) (inv_progDesc hinv hx hu' (nodup_of_mem_outs hs')).wf
    (isoVia_art (isoVia_id_of_agree (agree_progDesc hu')))

/-- **Completeness**: a reachable existential configuration matching a node of the semantic
attractor is in the attractor of `cfgSet`. -/
theorem attr_complete (hp : p.Valid) (hsz : ∀ g, GReach p b g → sz g ≤ B)
    {D : Problem.NSet ℕ ℕ ℕ ℕ} (hD : Problem.NGood D) {n : ℕ} {tn : TaskNetwork ℕ ℕ ℕ}
    {S : Set ℕ} (h : p.toProblem.FAttrH true D n tn S) :
    ∀ {g : β × GNode} {σ : ℕ → ℕ}, GReach p b g → g.2.1.1 = false → S = {f | f ∈ g.2.2.1} →
      tn.WF → HTN.TaskNetwork.IsoVia σ tn (cfgNet g.2.2.2) →
        BAttr B gAcc gUni gStep p (cfgSet p b D) g := by
  induction h with
  | goal he =>
    intro g σ hr htag _ _ hσ
    refine BAttr.acc (hsz g hr) ?_
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
    have hB₀ : BAttr B gAcc gUni gStep p (cfgSet p b₀ D) (b₀, ((false, 0), (s₀', progDesc d (σ t)))) :=
      ih hr₀ rfl rfl hwp ((isoVia_of_art hσp).of_agree (agree_progDesc hunc))
    have hX₁ : cfgSet p b₀ D (b₀, ((true, σ t), (s, d))) := by
      refine ⟨hr₁, Or.inr ⟨rfl, hall', ?_⟩⟩
      rw [hl]
      exact ⟨_, hs₀, n, h₀.isoVia hD hwp hwp' hσp⟩
    refine BAttr.ex (hsz _ hr) (by simp [gUni]) (hsz _ hr₁) hs₁ hX₁ ?_
    exact BAttr.univ (hsz _ hr₁) (by simp [gUni])
      (fun c'' _ hs'' => cfgSet_univ_succ hp hD hr₁ hall' hs'') (hsz _ hr₀) hst₀ hB₀
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
    exact BAttr.ex (hsz _ hr) (by simp [gUni]) (hsz _ hr₁) hs₁ hX₁ (ih hr₁ rfl rfl hwf' hσ'')

/-- **Completeness of the fair game on descriptions.** -/
theorem bWin_of_fairWin (hp : p.Valid) (hsz : ∀ g, GReach p b g → sz g ≤ B)
    (h : p.toProblem.FairWin true (cfgNet (initF p).2) {f | f ∈ (initF p).1}) :
    BWin B gAcc gUni gStep p (b, ((false, 0), initF p)) := by
  obtain ⟨D, hD, hD₀, hDa⟩ := h
  refine ⟨cfgSet p b D, ⟨.refl, Or.inl ⟨rfl, hD₀⟩⟩, fun g hg => ?_⟩
  obtain ⟨hr, ⟨htag, hDg⟩ | ⟨htag, hall, s₀, hs₀, n, hn⟩⟩ := hg
  · obtain ⟨n, hn⟩ := hDa _ _ hDg
    exact attr_complete hp hsz hD hn hr htag rfl (hD.1 _ _ hDg) (HTN.TaskNetwork.IsoVia.refl _)
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
    exact BAttr.univ (hsz _ hr) (by simp [gUni])
      (fun c'' _ hs'' => cfgSet_univ_succ hp hD hr hall hs'') (hsz _ hr₀) hst₀
      (attr_complete hp hsz hD hn hr₀ rfl rfl hwp
        (isoVia_art (isoVia_id_of_agree (agree_progDesc hu'))))

end Correct

/-! ## Membership -/

section Main

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

/-- Fair solvability of a well-formed description is the fair progression game from the
initial configuration. -/
theorem fair_iff_initF {p : FProbDesc} (hp : p.Valid) :
    p.toProblem.MPStrongCyclicFairSolvable ↔
      p.toProblem.FairWin true (cfgNet (initF p).2) {f | f ∈ (initF p).1} := by
  rw [Problem.mpStrongCyclicFairSolvable_iff_prog (FProbDesc.toProblem_wf hp).tnI, init_state]
  have hw := (FProbDesc.toProblem_wf hp).tnI
  have hw' := (gInv_init (β := ℕ) hp 0).inv.wf
  have hσ := isoVia_art (isoVia_id_of_agree (agree_initF hp))
  obtain ⟨τ, hτ, -⟩ := hσ.exists_inv
  constructor
  · rintro ⟨X, hX, hX₀, hXa⟩
    exact ⟨X, hX, hX.2 _ _ _ _ hX₀ hw' hσ, hXa⟩
  · rintro ⟨X, hX, hX₀, hXa⟩
    exact ⟨X, hX, hX.2 _ _ _ _ hX₀ hw hτ, hXa⟩

/-- The common core: the language as a fair game, for a bound `Bd` on reachable nodes. -/
theorem planExMPFair_iff_game {Y : FClass} {cB : FProbDesc × β → Bool}
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (R Bd : FProbDesc → ℕ)
    (hcomp : ∀ p : FProbDesc, p.Valid → Y p.toProblem → ∃ b, cB (p, b) = true ∧ sz b ≤ R p)
    (hreach : ∀ p : FProbDesc, p.Valid → Y p.toProblem → ∀ b : β, sz b ≤ R p →
      ∀ g, GReach p b g → sz g ≤ Bd p) (p : FProbDesc) :
    (p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongCyclicFairSolvable) ↔
      ∃ c₀, sz c₀ ≤ Bd p ∧ gInit cB R (p, c₀) = true ∧ BWin (Bd p) gAcc gUni gStep p c₀ := by
  constructor
  · rintro ⟨hp, hY, hsol⟩
    obtain ⟨b, hb, hbs⟩ := hcomp p hp hY
    have hsz := hreach p hp hY b hbs
    refine ⟨(b, ((false, 0), initF p)), hsz _ .refl, ?_, ?_⟩
    · simp [gInit, (FProbDesc.validB_iff p).2 hp, hb, hbs]
    · exact bWin_of_fairWin hp hsz ((fair_iff_initF hp).1 hsol)
  · rintro ⟨⟨b, g⟩, -, hi, hw⟩
    simp only [gInit, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨hv, hb⟩, hbs⟩, rfl⟩ := hi
    have hp := (FProbDesc.validB_iff p).1 hv
    have hY := hsound p b hp hb
    exact ⟨hp, hY, (fair_iff_initF hp).2 (fairWin_of_bWin hp (hreach p hp hY b hbs) hw)⟩

/-- **Fair strong cyclic plan existence is in `EXPTIME`** for classes with polynomial
certificates and polynomial progression bounds of the skeleton. -/
theorem inExpTime_planExMPFair {Y : FClass} {cB : FProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r : Polynomial ℕ)
    (hcomp : ∀ p : FProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ r.eval (sz p)) ∧ (skDesc p).toProblem.IsHTNProgBound (r.eval (sz p))) :
    Cx.EXPTIME (PlanExMPFair Y) := by
  obtain ⟨gr, hgr, hgrlen⟩ := HTN.Syn.PolyDom.exists_pt_polyLen r
  have hR : PT fun p : FProbDesc => r.eval (sz p) :=
    (PT.length (hgr.comp (BDec.pt_encL (α := FProbDesc)))).of_eq fun p => by rw [hgrlen]; rfl
  let q : Polynomial ℕ := r + Polynomial.C (3 + sz (0 : ℕ)) +
    80 * (r + 2 * Polynomial.X + 1) ^ 3 + Polynomial.X * (2 * Polynomial.X + 2)
  have hq : ∀ n, q.eval n = r.eval n + nodeBound (r.eval n) n := fun n => by
    simp only [q, nodeBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    ring
  exact inExpTime_codeLang_of_buchi (α := FProbDesc) (σ := β × GNode)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongCyclicFairSolvable)
    (pt_gInit hcB hR) pt_gAcc pt_gUni pt_gStep q fun p =>
      planExMPFair_iff_game hsound _ (fun p => q.eval (sz p)) (fun p hp hY => (hcomp p hp hY).1)
        (fun p hp hY b hb g hg => by
          have := sz_le_of_gInv hp (hcomp p hp hY).2 (gInv_of_reach hp hg)
          show sz g ≤ q.eval (sz p)
          rw [hq]; omega) p

/-- **Fair strong cyclic plan existence is in `2-EXPTIME`** for classes with exponential
certificates and exponential progression bounds of the skeleton. -/
theorem inExp2Time_planExMPFair {Y : FClass} {cB : FProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r : Polynomial ℕ)
    (hcomp : ∀ p : FProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ 2 ^ r.eval (sz p)) ∧ (skDesc p).toProblem.IsHTNProgBound (2 ^ r.eval (sz p))) :
    Cx.EXPTIME2 (PlanExMPFair Y) := by
  have hR := pt_two_pow_poly r
  let q : Polynomial ℕ := 3 * r + 3 * Polynomial.X + 12
  have hq : ∀ n, q.eval n = 3 * r.eval n + 3 * n + 12 := fun n => by simp [q]
  exact inExp2Time_codeLang_of_buchi (α := FProbDesc) (σ := β × GNode)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongCyclicFairSolvable)
    (pt_gInit hcB hR) pt_gAcc pt_gUni pt_gStep q fun p =>
      planExMPFair_iff_game hsound _ (fun p => 2 ^ q.eval (sz p))
        (fun p hp hY => (hcomp p hp hY).1)
        (fun p hp hY b hb g hg => by
          have := sz_le_of_gInv hp (hcomp p hp hY).2 (gInv_of_reach hp hg)
          have h2 := exp_nodeBound_le (r.eval (sz p)) (sz p)
          show sz g ≤ 2 ^ q.eval (sz p)
          rw [hq]; omega) p

end Main

end MPS

/-! ## The classes -/

/-- **[CB22, Thm. 3], strong cyclic (fair reading), membership.** -/
theorem fairMP_REG_mem : Cx.EXPTIME (PlanExMPFair FClass.REG) := by
  let r : Polynomial ℕ := 50 * (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 50 * (n + 1) ^ 2 := fun n => by simp [r]
  refine inExpTime_planExMPFair (β := List ℕ × List (ℕ × ℕ))
    (cB := fun x => trB 1 (skDesc x.1, x.2)) ((pt_trB 1).comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r fun p hp hY => ?_
  · obtain ⟨R, rkL⟩ := b
    have hq := skDesc_valid hp
    exact (sameShape_skDesc p).isRegularM.2 (((skDesc p).toProblem.thm_3_0_1
      (wf_toProblem _)).2 (((trB_iff 1 (skDesc p) R rkL).1 hb).isTailREC_h hq))
  · have hq := skDesc_valid hp
    have hY' := ((skDesc p).toProblem.thm_3_0_1 (wf_toProblem _)).1
      ((sameShape_skDesc p).isRegularM.1 hY)
    have hS := sz_skDesc_le p
    obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -⟩ := exists_trCert hq hY'
    refine ⟨⟨(R, rkL), hb, ?_⟩, ?_⟩
    · have h1 : sz (R, rkL) ≤ 10 * (sz (skDesc p) + 1 + 1) ^ 2 := sz_rcert_le hRN hRl hrkN hrkl
      have h2 : (sz (skDesc p) + 1 + 1) ^ 2 ≤ (2 * (sz p + 1)) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      rw [hr]
      nlinarith
    · have hb := ((skDesc p).toProblem.lem_4_2_15 (wf_toProblem _) hY' (tnI_card_le _)
        (one_le_S _) (meth_card_le _)).1
      refine IsHTNProgBound.mono hb ?_
      rw [hr]
      nlinarith

/-- **[CB22, Thm. 4], strong cyclic (fair reading), membership.** -/
theorem fairMP_TR_TO_mem : Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.TR FClass.TO)) := by
  let r : Polynomial ℕ := 200 * (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 200 * (n + 1) ^ 2 := fun n => by simp [r]
  refine inExpTime_planExMPFair (β := ℕ × (List ℕ × List (ℕ × ℕ)))
    (cB := fun x => trTOB (skDesc x.1, x.2)) (pt_trTOB.comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r fun p hp hY => ?_
  · have hq := skDesc_valid hp
    simp only [trTOB, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    obtain ⟨htr, hcl⟩ := trHB_sound hq h1
    exact ⟨(sameShape_skDesc p).isTailRecursive.2 htr, (skDesc_TO p).2
      ⟨(toB_iff hq.tnI).1 h2, methodsRB_sound hq hcl (fun ht => toB_iff ht) h3⟩⟩
  · have hq := skDesc_valid hp
    have hS := sz_skDesc_le p
    have htr := (sameShape_skDesc p).isTailRecursive.1 hY.1
    have hto := (skDesc_TO p).1 hY.2
    obtain ⟨b, hb, hsz, hRr⟩ := exists_trHB hq htr
    refine ⟨⟨b, ?_, ?_⟩, ?_⟩
    · simp only [trTOB, Bool.and_eq_true]
      exact ⟨⟨hb, (toB_iff hq.tnI).2 hto.1⟩, methodsRB_complete hq hRr (fun ht => toB_iff ht) hto.2⟩
    · have h2 : (2 * sz (skDesc p) + 1) ^ 2 ≤ (4 * (sz p + 1)) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      rw [hr]
      nlinarith
    · have hb := ((skDesc p).toProblem.lem_4_2_19 (wf_toProblem _)
        (isTailREC_h_of_isTailREC hq htr) hto (tnI_card_le _) (meth_card_le _)).1
      refine IsHTNProgBound.mono hb ?_
      rw [hr]
      have hK : (numsOf (skDesc p)).length ≤ sz (skDesc p) := length_numsOf_le _
      have : (sz (skDesc p) - 1) * (numsOf (skDesc p)).length ≤ sz (skDesc p) * sz (skDesc p) :=
        Nat.mul_le_mul (Nat.sub_le _ _) hK
      nlinarith

/-- **[CB22, Thm. 5], strong cyclic (fair reading), membership in `2-EXPTIME`.** -/
theorem fairMP_TR_mem : Cx.EXPTIME2 (PlanExMPFair FClass.TR) := by
  let r : Polynomial ℕ := 4 * Polynomial.X ^ 2 + 4 * Polynomial.X + 6
  have hr : ∀ n, r.eval n = 4 * n ^ 2 + 4 * n + 6 := fun n => by simp [r]
  refine inExp2Time_planExMPFair (β := ℕ × (List ℕ × List (ℕ × ℕ)))
    (cB := fun x => trHB (skDesc x.1, x.2)) (pt_trHB.comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r fun p hp hY => ?_
  · exact (sameShape_skDesc p).isTailRecursive.2 (trHB_sound (skDesc_valid hp) hb).1
  · obtain ⟨⟨b, hb, hbs⟩, hn⟩ := tr_hcomp (skDesc_valid hp)
      ((sameShape_skDesc p).isTailRecursive.1 hY)
    have he := skDesc_exp_le p
    rw [hr]
    exact ⟨⟨b, hb, hbs.trans he⟩, IsHTNProgBound.mono hn he⟩

/-- Dropping a restriction decided in polynomial time (fair strong cyclic). -/
theorem redP_filterFair {Y Z : FClass} {b : FProbDesc → Bool} (hb : PT b)
    (hbZ : ∀ p : FProbDesc, p.Valid → (b p = true ↔ Z p.toProblem)) :
    Cx.RedP (PlanExMPFair (FClass.inter Y Z)) (PlanExMPFair Y) := by
  refine redP_codeLang (f := fun p => bif b p then p else badDesc)
    (PT.cond hb PT.id (PT.const badDesc)) (fun p => ?_) badDesc
    (fun h => badDesc_not_valid h.1)
  by_cases hp : p.Valid
  · by_cases hz : b p = true
    · simp only [hz, cond_true]
      exact ⟨fun ⟨hv, ⟨hy, _⟩, hs⟩ => ⟨hv, hy, hs⟩,
        fun ⟨hv, hy, hs⟩ => ⟨hv, ⟨hy, (hbZ p hp).1 hz⟩, hs⟩⟩
    · simp only [Bool.not_eq_true] at hz
      simp only [hz, cond_false]
      exact ⟨fun ⟨_, ⟨_, hz'⟩, _⟩ => absurd ((hbZ p hp).2 hz') (by simp [hz]),
        fun h => absurd h.1 badDesc_not_valid⟩
  · cases hz : b p
    · simp only [hz, cond_false]
      exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badDesc_not_valid⟩
    · simp only [hz, cond_true]
      exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 hp⟩

theorem fairMP_REG_TO_mem : Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.REG FClass.TO)) :=
  Cx.EXPTIME.of_redP (redP_filterFair pt_fTOB fun _ hp => fTOB_iff hp) fairMP_REG_mem

/-! ## Membership with the available lower bounds -/

theorem fairMP_REG_TO_bounds :
    Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.REG FClass.TO)) ∧
      Cx.Hard Cx.PSPACE (PlanExMPFair (FClass.inter FClass.REG FClass.TO)) :=
  ⟨fairMP_REG_TO_mem, hardFair_REG_TO⟩

theorem fairMP_REG_bounds :
    Cx.EXPTIME (PlanExMPFair FClass.REG) ∧ Cx.Hard Cx.PSPACE (PlanExMPFair FClass.REG) :=
  ⟨fairMP_REG_mem, hardFair_REG_TO.of_redP (redP_filterFair pt_fTOB fun _ hp => fTOB_iff hp)⟩

theorem fairMP_TR_TO_bounds :
    Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.TR FClass.TO)) ∧
      Cx.Hard Cx.PSPACE (PlanExMPFair (FClass.inter FClass.TR FClass.TO)) :=
  ⟨fairMP_TR_TO_mem, hardFair_TR_TO⟩

theorem fairMP_TR_bounds :
    Cx.EXPTIME2 (PlanExMPFair FClass.TR) ∧ Cx.Hard Cx.EXPSPACE (PlanExMPFair FClass.TR) :=
  ⟨fairMP_TR_mem, hardFair_TR.of_redP (redP_filterFair pt_fToB fun _ hp => fToB_iff hp)⟩

end FOND
