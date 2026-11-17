import FondHtn.MPStrong.TR
import FondHtn.Alt.Depth
import HtnPlanning.Article.DecompBound
/-!
# Strong method-based plan existence for acyclic problems is in `EXPSPACE`
([CB22, Thm. 2], membership, strong)

For acyclic problems every progression step lowers the measure
`μ(tn) = (m + 1) · pot(tn) + |tn|`, where `pot` is the potential of the corrected Lemma 4.2.4
(`HTN.Problem.potential`: a compound task of stratum `j` is worth `1 + m + … + m^j`, a primitive
task `0`; a decomposition lowers it by at least one and inserts at most `m` tasks).  Hence a
strategy of the progression game has height at most `μ(tn_I)`, which is exponential
(`FOND.MPS.MPProg.toH_measure`), and the game can be evaluated depth-first with an exponential
depth budget over configurations of exponential size (`HTN.Syn.PolyDom.inExpSpace_codeLang_of_game`,
`AEXPTIME = EXPSPACE`).

* `FOND.MPS.gameVal_sound`, `FOND.MPS.gameVal_complete` — the depth-bounded value of the game on
  descriptions agrees with the semantic progression game;
* **`FOND.strongMP_ACYC_mem`** — `PlanExMP .strong ACYC ∈ EXPSPACE` ([CB22, Thm. 2]).

[CB22] claims EXPSPACE-completeness; only NEXPTIME-hardness is inherited (`FOND.hard_ACYC_mp`),
recorded in `FOND.strongMP_ACYC_bounds`.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

namespace MPS

/-! ## A measure decreased by progression -/

section Measure

variable {F F' : Type} {P : Problem F ℕ ℕ ℕ} {Q : HTN.Problem F' ℕ ℕ ℕ}

/-- The measure `(m + 1) · pot + |tn|`. -/
def mu (mm : ℕ) (f : ℕ → ℕ) (tn : TaskNetwork ℕ ℕ ℕ) : ℕ :=
  (mm + 1) * HTN.Problem.potential mm f tn + tn.T.card

theorem mu_progress {mm : ℕ} {f : ℕ → ℕ} {tn : TaskNetwork ℕ ℕ ℕ} {t a : ℕ} (ht : t ∈ tn.T)
    (hα : tn.α t = Sum.inl a) : mu mm f (tn.progress t) + 1 ≤ mu mm f tn := by
  unfold mu HTN.Problem.potential
  have h1 := Finset.add_sum_erase tn.T (fun x => HTN.Problem.worth mm f (tn.α x)) ht
  have h2 := Finset.card_erase_add_one ht
  have hw : HTN.Problem.worth mm f (tn.α t) = 0 := by simp [HTN.Problem.worth, hα]
  simp only [hw, zero_add] at h1
  simp only [TaskNetwork.progress_T, TaskNetwork.progress_α]
  rw [← h1]
  omega

theorem mu_decomp (hM : Q.methods = P.methods) {le : ℕ → ℕ → Prop} (hs : Q.IsStrat0 le)
    {f : ℕ → ℕ} (hf : ∀ c c', Q.ReachableName c → Q.ReachableName c' → (le c c' ↔ f c ≤ f c'))
    {mm : ℕ} (hmm : ∀ m, Q.ReachableMethod m → m.subtasks.T.card ≤ mm)
    {tn tn' : TaskNetwork ℕ ℕ ℕ} {t : ℕ} {m : Method ℕ ℕ ℕ}
    (hd : DecompStep P.methods tn t m tn') (hn : Q.NamesReachable tn) :
    mu mm f tn' + 1 ≤ mu mm f tn ∧ Q.NamesReachable tn' := by
  rw [← hM] at hd
  have hpot := HTN.Problem.potential_step Q hs hf hmm hd hn
  have hrm := HTN.Problem.reachableMethod_of_decompStep hd hn
  have hn' := HTN.Problem.namesReachable_of_decompStep hd hn
  refine ⟨?_, hn'⟩
  obtain ⟨-, htT, -, u, -, ⟨σ, hbij, -, -⟩, -, rfl⟩ := hd
  have hcu : u.T.card = m.subtasks.T.card :=
    Finset.card_nbij σ (fun x hx => hbij.mapsTo hx) hbij.injOn hbij.surjOn
  have hcard : (decomposeWith tn t u).T.card + 1 ≤ tn.T.card + mm := by
    have h1 : (decomposeWith tn t u).T.card ≤ (tn.T.erase t).card + u.T.card :=
      Finset.card_union_le _ _
    have h2 := Finset.card_erase_add_one htT
    have h3 := hmm m hrm
    omega
  unfold mu
  have : (mm + 1) * (HTN.Problem.potential mm f (decomposeWith tn t u) + 1) ≤
      (mm + 1) * HTN.Problem.potential mm f tn := Nat.mul_le_mul_left _ hpot
  rw [mul_add, mul_one] at this
  omega

/-- **Strategies of the progression game have height at most `μ`.** -/
theorem MPProg.toH_measure (hM : Q.methods = P.methods) {le : ℕ → ℕ → Prop} (hs : Q.IsStrat0 le)
    {f : ℕ → ℕ} (hf : ∀ c c', Q.ReachableName c → Q.ReachableName c' → (le c c' ↔ f c ≤ f c'))
    {mm : ℕ} (hmm : ∀ m, Q.ReachableMethod m → m.subtasks.T.card ≤ mm)
    {tn : TaskNetwork ℕ ℕ ℕ} {S : Set F} (h : P.MPProg tn S) :
    Q.NamesReachable tn → P.MPProgH (mu mm f tn) tn S := by
  induction h with
  | empty he => exact fun _ => .empty he
  | @prim tn S t a hu hα happ _ ih =>
    intro hn
    have hle := mu_progress (mm := mm) (f := f) hu.1 hα
    obtain ⟨k, hk⟩ : ∃ k, mu mm f tn = k + 1 := ⟨mu mm f tn - 1, by omega⟩
    rw [hk]
    exact .prim hu hα happ fun s' hs' =>
      (ih s' hs' fun x hx c hc => hn x (Finset.mem_of_mem_erase hx) c hc).mono (by omega)
  | @decomp tn tn' S t m hu hd _ ih =>
    intro hn
    obtain ⟨hle, hn'⟩ := mu_decomp hM hs hf hmm hd hn
    obtain ⟨k, hk⟩ : ∃ k, mu mm f tn = k + 1 := ⟨mu mm f tn - 1, by omega⟩
    rw [hk]
    exact .decomp hu hd ((ih hn').mono (by omega))

end Measure

/-! ## The game with a depth budget -/

section Depth

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

/-- The successor list of the game (the certificate is kept). -/
def succsG (x : FProbDesc × (β × GNode)) : List (β × GNode) :=
  (nodeSuccs x.1 x.2.2).map fun n => (x.2.1, n)

theorem mem_succsG {p : FProbDesc} {g g' : β × GNode} :
    g' ∈ succsG (p, g) ↔ gStep (p, g, g') = true := by
  obtain ⟨b', n'⟩ := g'
  simp only [succsG, List.mem_map, gStep, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨n, hn, rfl, rfl⟩; exact ⟨rfl, hn⟩
  · rintro ⟨rfl, hn⟩; exact ⟨n', hn, rfl, rfl⟩

theorem pt_succsG : PT (succsG (β := β)) := by
  unfold succsG
  exact PT.map (pt_nodeSuccs.comp (PT.pair PT.fst (PT.snd.comp PT.snd)))
    (PT.pair (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd)

variable {acc uni : FProbDesc × (β × GNode) → Bool}
  {sc : FProbDesc × (β × GNode) → List (β × GNode)}

theorem gameVal_ex {p : FProbDesc} {k : ℕ} {c : β × GNode} (h : uni (p, c) = false) :
    gameVal acc uni sc p (k + 1) c = (acc (p, c) || (sc (p, c)).any (gameVal acc uni sc p k)) := by
  simp [gameVal, h]

theorem gameVal_uni {p : FProbDesc} {k : ℕ} {c : β × GNode} (h : uni (p, c) = true) :
    gameVal acc uni sc p (k + 1) c = (acc (p, c) || (sc (p, c)).all (gameVal acc uni sc p k)) := by
  simp [gameVal, h]

theorem gameVal_mono {p : FProbDesc} : ∀ (k : ℕ) {c : β × GNode},
    gameVal acc uni sc p k c = true → gameVal acc uni sc p (k + 1) c = true := by
  intro k
  induction k with
  | zero =>
    intro c h
    simp only [gameVal] at h ⊢
    simp [h]
  | succ k ih =>
    intro c h
    cases hu : uni (p, c)
    · rw [gameVal_ex hu] at h ⊢
      simp only [Bool.or_eq_true, List.any_eq_true] at h ⊢
      rcases h with h | ⟨c', hc', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨c', hc', ih h⟩
    · rw [gameVal_uni hu] at h ⊢
      simp only [Bool.or_eq_true, List.all_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr fun c' hc' => ih (h c' hc')

theorem gameVal_mono_le {p : FProbDesc} {k k' : ℕ} (hk : k ≤ k') {c : β × GNode}
    (h : gameVal acc uni sc p k c = true) : gameVal acc uni sc p k' c = true := by
  obtain ⟨j, rfl⟩ : ∃ j, k' = k + j := ⟨k' - k, by omega⟩
  clear hk
  induction j with
  | zero => exact h
  | succ j ih => exact gameVal_mono _ ih

variable {p : FProbDesc} {b : β}

/-- **Soundness of the depth-bounded value.** -/
theorem gameVal_sound (hp : p.Valid) : ∀ (k : ℕ) {g : β × GNode},
    gameVal gAcc gUni succsG p k g = true → GReach p b g →
      (g.2.1.1 = false → p.toProblem.MPProg (cfgNet g.2.2.2) {f | f ∈ g.2.2.1}) ∧
      (g.2.1.1 = true → ∀ S' ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1},
        p.toProblem.MPProg ((cfgNet g.2.2.2).progress g.2.1.2) S') := by
  have hacc : ∀ {g : β × GNode}, gAcc (p, g) = true →
      (g.2.1.1 = false → p.toProblem.MPProg (cfgNet g.2.2.2) {f | f ∈ g.2.2.1}) ∧
      (g.2.1.1 = true → ∀ S' ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1},
        p.toProblem.MPProg ((cfgNet g.2.2.2).progress g.2.1.2) S') := by
    intro g ha
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    simp only [gAcc, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at ha
    obtain ⟨rfl, hids⟩ := ha
    refine ⟨fun _ => .empty ?_, fun h => absurd h (by simp)⟩
    simp [cfgNet, hids]
  intro k
  induction k with
  | zero => intro g h _; exact hacc h
  | succ k ih =>
    intro g h hr
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    cases tg with
    | false =>
      rw [gameVal_ex (by simp [gUni])] at h
      simp only [Bool.or_eq_true, List.any_eq_true] at h
      rcases h with h | ⟨g', hg', h⟩
      · exact hacc h
      have hs := mem_succsG.1 hg'
      have ih' := ih h (hr.tail hs)
      have hinv := hgi.inv
      simp only at hinv
      refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨b', g''⟩ := g'
      simp only at hs ih'
      rcases nodeSuccs_ex hs.2 with ⟨x, hx, hu, e, he, hl, rfl⟩ | ⟨x, hx, hok, rfl⟩
      · exact mpProg_of_dec hp hinv hx ((unc_iff _ _).1 hu) he hl (ih'.1 rfl)
      · obtain ⟨hl, hu, happ⟩ := lbl_false_of_primOk hok
        exact .prim (unconstrained_cfgNet hx ((unc_iff _ _).1 hu))
          (by rw [cfgNet_label, hl]; rfl) ((fApp_iff _ _ _).1 happ) (ih'.2 rfl)
    | true =>
      rw [gameVal_uni (by simp [gUni])] at h
      simp only [Bool.or_eq_true, List.all_eq_true] at h
      rcases h with h | h
      · exact hacc h
      obtain ⟨hx, hok⟩ := hgi.tagT rfl
      have hinv := hgi.inv
      simp only at hx hok hinv
      obtain ⟨-, hu, -⟩ := lbl_false_of_primOk hok
      have hu' := (unc_iff _ _).1 hu
      refine ⟨fun h => absurd h (by simp), fun _ S' hS' => ?_⟩
      obtain ⟨s', hs', rfl⟩ := outs_complete hS'
      have hst : gStep (p, (b₀, ((true, y), (s, d))), (b₀, ((false, 0), (s', progDesc d y)))) =
          true := by
        simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
        exact mem_nodeSuccs_out hs'
      have h' := (ih (h _ (mem_succsG.2 hst)) (hr.tail hst)).1 rfl
      simp only at h'
      exact h'.isoVia (inv_progDesc hinv hx hu' (nodup_of_mem_outs hs')).wf
        (TaskNetwork.progress_wf hinv.wf (unconstrained_cfgNet hx hu'))
        (isoVia_art (isoVia_id_of_agree (agree_progDesc hu').symm))

/-- **Completeness of the depth-bounded value**: a strategy of height `n` wins within `2 n`. -/
theorem gameVal_complete (hp : p.Valid) {n : ℕ} {tn : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ}
    (h : p.toProblem.MPProgH n tn S) :
    ∀ {g : β × GNode} {σ : ℕ → ℕ}, GReach p b g → g.2.1.1 = false → S = {f | f ∈ g.2.2.1} →
      tn.WF → HTN.TaskNetwork.IsoVia σ tn (cfgNet g.2.2.2) →
        gameVal gAcc gUni succsG p (2 * n) g = true := by
  induction h with
  | empty he =>
    intro g σ _ htag _ _ hσ
    refine gameVal_of_acc ?_ _
    have hT := hσ.empty he
    simp only [cfgNet, List.toFinset_eq_empty_iff] at hT
    simp [gAcc, htag, hT]
  | @prim n tn S t a hu hα happ _ ih =>
    intro g σ hr htag hS hwf hσ
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    simp only at htag hS hσ
    subst htag hS
    have hy := hgi.tagF rfl
    have hinv := hgi.inv
    simp only at hy hinv
    subst hy
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
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, gameVal_ex (by simp [gUni])]
    simp only [Bool.or_eq_true, List.any_eq_true]
    refine Or.inr ⟨_, mem_succsG.2 hs₁, ?_⟩
    rw [gameVal_uni (by simp [gUni])]
    simp only [Bool.or_eq_true, List.all_eq_true]
    refine Or.inr fun g' hg' => ?_
    have hs' := mem_succsG.1 hg'
    have hr' := hr₁.tail hs'
    obtain ⟨b', g''⟩ := g'
    simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs'
    obtain ⟨rfl, hs'⟩ := hs'
    obtain ⟨s', hs'', rfl⟩ := nodeSuccs_univ hs'
    simp only [hl] at hs''
    exact ih _ (outs_sound hs'') hr' rfl rfl (TaskNetwork.progress_wf hwf hu)
      (isoVia_art ((isoVia_of_art (hσ.progress hu.1)).of_agree (agree_progDesc hunc)))
  | @decomp n tn tn' S t m hu hd _ ih =>
    intro g σ hr htag hS hwf hσ
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    simp only at htag hS hσ
    subst htag hS
    have hy := hgi.tagF rfl
    have hinv := hgi.inv
    simp only at hy hinv
    subst hy
    have hwf' := hd.wf hwf
    obtain ⟨⟨e, he, rfl⟩, ht, hαt, tn'', hwf'', hiso, hdisj, rfl⟩ := hd
    have hev := hp.methods e he
    obtain ⟨hx, hunc⟩ := unc_of_isoVia hinv hσ hu
    have hl : lblOf d (σ t) = (true, e.1) := by
      rw [← toSum_eq_inr, ← cfgNet_label, ← hσ.2.2 t ht, hαt]; rfl
    obtain ⟨σ', hσ', -, -⟩ := (isoVia_of_art hσ).decomposeWith hwf hinv.wf ht hwf''
      (wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _))
      (hiso.trans (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso) hdisj
      (disjoint_copy _)
    have hs₁ : gStep (p, (b₀, ((false, 0), (s, d))),
        (b₀, ((false, 0), (s, decDesc d (σ t) e)))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_dec hx ((unc_iff _ _).2 hunc) he hl
    have hr₁ := hr.tail hs₁
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, gameVal_ex (by simp [gUni])]
    simp only [Bool.or_eq_true, List.any_eq_true]
    refine Or.inr ⟨_, mem_succsG.2 hs₁, gameVal_mono _ ?_⟩
    exact ih hr₁ rfl rfl hwf' (isoVia_art (hσ'.of_agree (agree_decDesc ⟨hinv.ids_nodup,
      hinv.lbl_mem, hinv.lbl_nodup, hinv.ord_nodup, List.nodup_nil, hinv.wf⟩ hev)))

theorem greach_of_gameReach {p : FProbDesc} {b : β} : ∀ (n : ℕ) {g c : β × GNode},
    GReach p b g → GameReach succsG p n g c → GReach p b c := by
  intro n
  induction n with
  | zero => intro g c hg h; simp only [GameReach] at h; subst h; exact hg
  | succ n ih =>
    intro g c hg h
    obtain ⟨c₁, hc₁, h⟩ := h
    exact ih (hg.tail (mem_succsG.1 hc₁)) h

end Depth

/-! ## Sizes of successor lists -/

section Sizes

set_option linter.unusedSectionVars false

theorem sz_fprob (acts : List FActDesc) (ms : List MethodDesc) (init : List ℕ) (tn : TnDesc) :
    sz (((acts, ms), (init, tn)) : FProbDesc) = sz acts + sz ms + sz init + sz tn := by
  simp only [sz_prod]; ring

theorem length_effs_fActOf (p : FProbDesc) (a : ℕ) : (fActOf p a).2.2.2.length ≤ sz p + 1 := by
  have hm := headI_mem_of_ne_nil (l := (p.actions.filter fun x : FActDesc => x.1 == a) ++
    [(a, [], [], [([], [])])]) (by simp)
  have hf : fActOf p a = ((p.actions.filter fun x : FActDesc => x.1 == a) ++
    [(a, [], [], [([], [])])]).headI := rfl
  rcases List.mem_append.1 hm with hm | hm
  · rw [← hf] at hm
    have hx := (List.mem_filter.1 hm).1
    obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
    rw [sz_fprob]
    have h1 := sz_le_of_mem hx
    have h2 := length_le_sz (fActOf (((acts, ms), (init, tn)) : FProbDesc) a).2.2.2
    have h3 : sz (fActOf (((acts, ms), (init, tn)) : FProbDesc) a).2.2.2 ≤
        sz (fActOf (((acts, ms), (init, tn)) : FProbDesc) a) := by
      obtain ⟨n, l₁, l₂, l₃⟩ := fActOf (((acts, ms), (init, tn)) : FProbDesc) a
      simp only [sz_prod]; omega
    simp only [FProbDesc.actions] at h1
    omega
  · rw [List.mem_singleton, ← hf] at hm
    rw [hm]; simp

theorem length_flatMap_le_mul {α γ : Type} (l : List α) (g : α → List γ) {K : ℕ}
    (h : ∀ a ∈ l, (g a).length ≤ K) : (l.flatMap g).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    rw [Nat.add_mul, one_mul]; omega

theorem length_methods_le (p : FProbDesc) : p.methods.length ≤ sz p := by
  obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
  rw [sz_fprob]
  have := length_le_sz ms
  simp only [FProbDesc.methods]; omega

theorem length_nodeSuccs (p : FProbDesc) (g : GNode) :
    (nodeSuccs p g).length ≤ g.2.2.ids.length * (sz p + 1) + sz p + 1 := by
  obtain ⟨⟨tg, x⟩, s, d⟩ := g
  cases tg with
  | true =>
    simp only [nodeSuccs, ↓reduceIte, List.length_map, outs]
    have := length_effs_fActOf p (lblOf d x).2
    nlinarith
  | false =>
    simp only [nodeSuccs, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_map]
    have h1 := length_flatMap_le_mul d.ids (decSuccsAt p d) (K := p.methods.length) fun y _ => by
      unfold decSuccsAt
      split_ifs
      · rw [List.length_map]; exact List.length_filter_le _ _
      · simp
    have h2 := List.length_filter_le (primOk p (s, d)) d.ids
    have h3 := length_methods_le p
    have h4 : d.ids.length * p.methods.length ≤ d.ids.length * sz p := Nat.mul_le_mul_left _ h3
    simp only at h1 h2 ⊢
    nlinarith

end Sizes

/-! ## Membership in `EXPSPACE` -/

section Main

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

theorem pt_two_pow_poly (r : Polynomial ℕ) : PT fun p : FProbDesc => 2 ^ r.eval (sz p) := by
  obtain ⟨gr, hgr, hgrlen⟩ := HTN.Syn.PolyDom.exists_pt_polyLen r
  have h := PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
    (hgr.comp (BDec.pt_encL (α := FProbDesc))) (PT.const false)) (PT.const [true]))
  exact h.of_eq fun a => by rw [List.map_const', hgrlen, natOfBits_pow]; rfl

/-- **Strong method-based plan existence is in `EXPSPACE`** for classes with exponential
certificates, exponential progression bounds of the skeleton and strategies of exponential
height. -/
theorem inExpSpace_planExMP_strong {Y : FClass} {cB : FProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r D : Polynomial ℕ)
    (hcomp : ∀ p : FProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ 2 ^ r.eval (sz p)) ∧ (skDesc p).toProblem.IsHTNProgBound (2 ^ r.eval (sz p)))
    (hdepth : ∀ p : FProbDesc, p.Valid → Y p.toProblem → ∀ S,
      p.toProblem.MPProg p.toProblem.tnI S →
        p.toProblem.MPProgH (2 ^ D.eval (sz p)) p.toProblem.tnI S) :
    Cx.EXPSPACE (PlanExMP .strong Y) := by
  have hR := pt_two_pow_poly r
  have hD := pt_two_pow_poly (D + 1)
  let q₀ : Polynomial ℕ := 3 * r + 3 * Polynomial.X + 12
  have hq₀ : ∀ n, q₀.eval n = 3 * r.eval n + 3 * n + 12 := fun n => by simp [q₀]
  let q : Polynomial ℕ := 3 * q₀ + 4
  have hq : ∀ n, q.eval n = 3 * q₀.eval n + 4 := fun n => by simp [q]
  have hreach : ∀ p : FProbDesc, p.Valid → Y p.toProblem → ∀ b : β, sz b ≤ 2 ^ r.eval (sz p) →
      ∀ g, GReach p b g → sz g ≤ 2 ^ q₀.eval (sz p) := by
    intro p hp hY b hb g hg
    have := sz_le_of_gInv hp (hcomp p hp hY).2 (gInv_of_reach hp hg)
    have h2 := exp_nodeBound_le (r.eval (sz p)) (sz p)
    rw [hq₀]
    omega
  have hq₀q : ∀ n, 2 ^ q₀.eval n ≤ 2 ^ q.eval n := fun n =>
    Nat.pow_le_pow_right (by norm_num) (by rw [hq]; omega)
  refine inExpSpace_codeLang_of_game (α := FProbDesc) (σ := β × GNode)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongSolvable)
    (acc := gAcc) (uni := gUni) (succs := succsG)
    (pt_gInit hcB hR) pt_gAcc pt_gUni pt_succsG hD q ?_ ?_
  · intro p c₀ hi
    simp only [gInit, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨hv, hb⟩, hbs⟩, hc₀⟩ := hi
    obtain ⟨b, g₀⟩ := c₀
    simp only at hb hbs hc₀
    subst hc₀
    have hp := (FProbDesc.validB_iff p).1 hv
    have hY := hsound p b hp hb
    have hsz := hreach p hp hY b hbs
    refine ⟨(hsz _ .refl).trans (hq₀q _), fun n _ c hc => ?_⟩
    have hrc := greach_of_gameReach n .refl hc
    set B := 2 ^ q₀.eval (sz p) with hBdef
    have hcB := hsz c hrc
    have hel : ∀ g' ∈ succsG (p, c), sz g' ≤ B := fun g' hg' =>
      hsz g' (hrc.tail (mem_succsG.1 hg'))
    have h1 := sz_list_le hel
    have hlen : (succsG (p, c)).length ≤ c.2.2.2.ids.length * (sz p + 1) + sz p + 1 := by
      unfold succsG; rw [List.length_map]; exact length_nodeSuccs p c.2
    have hids : c.2.2.2.ids.length ≤ B := by
      have e1 := length_le_sz c.2.2.2.ids
      have e2 : sz c.2.2.2.ids ≤ sz c.2.2.2 := by rw [sz_tnDesc]; omega
      have e3 : sz c.2.2.2 ≤ sz c := by
        obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := c
        simp only [sz_prod]; omega
      omega
    have hS : sz p + 1 ≤ B := by
      have := Nat.lt_two_pow_self (n := sz p)
      have : 2 ^ sz p ≤ B := Nat.pow_le_pow_right (by norm_num) (by rw [hq₀]; omega)
      omega
    have hB1 : 1 ≤ B := Nat.one_le_two_pow
    have hfin : 2 ^ q.eval (sz p) = 16 * B ^ 3 := by
      rw [hq, hBdef, ← pow_mul, show 3 * q₀.eval (sz p) + 4 = 4 + q₀.eval (sz p) * 3 by ring,
        pow_add]
      norm_num
    rw [hfin]
    have e1 : (succsG (p, c)).length ≤ B * B + B := by
      have : c.2.2.2.ids.length * (sz p + 1) ≤ B * B := Nat.mul_le_mul hids hS
      omega
    have e2 : (succsG (p, c)).length * (2 * B + 2) ≤ (B * B + B) * (4 * B) :=
      Nat.mul_le_mul e1 (by omega)
    have e3 : (B * B + B) * (4 * B) ≤ 8 * B ^ 3 := by nlinarith
    have e4 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB1
    omega
  · intro p
    constructor
    · rintro ⟨hp, hY, hsol⟩
      obtain ⟨⟨b, hb, hbs⟩, -⟩ := hcomp p hp hY
      have hsz := hreach p hp hY b hbs
      refine ⟨(b, ((false, 0), initF p)), (hsz _ .refl).trans (hq₀q _), ?_, ?_⟩
      · simp [gInit, (FProbDesc.validB_iff p).2 hp, hb, hbs]
      · have h := (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).1 hsol
        have hH := hdepth p hp hY _ h
        have := gameVal_complete hp hH (b := b) .refl rfl (init_state p)
          (FProbDesc.toProblem_wf hp).tnI (isoVia_art (isoVia_id_of_agree (agree_initF hp)))
        have he : 2 * 2 ^ D.eval (sz p) = 2 ^ (D + 1).eval (sz p) := by
          rw [Polynomial.eval_add, Polynomial.eval_one, pow_succ]; ring
        rw [he] at this
        exact this
    · rintro ⟨⟨b, g⟩, -, hi, hw⟩
      simp only [gInit, Bool.and_eq_true, decide_eq_true_eq] at hi
      obtain ⟨⟨⟨hv, hb⟩, hbs⟩, rfl⟩ := hi
      have hp := (FProbDesc.validB_iff p).1 hv
      have hY := hsound p b hp hb
      refine ⟨hp, hY, ?_⟩
      have h := (gameVal_sound hp _ hw .refl).1 rfl
      have hinv := (gInv_init hp b).inv
      rw [← init_state] at h
      exact (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).2
        (h.isoVia hinv.wf (FProbDesc.toProblem_wf hp).tnI
          (isoVia_art (isoVia_id_of_agree (agree_initF hp).symm)))

end Main

/-! ## Acyclic problems -/

/-- **Strategies for acyclic problems have exponential height**: `μ(tn_I) ≤ 2^(4|p|² + 2|p| + 2)`. -/
theorem acyc_depth {p : FProbDesc} (hp : p.Valid) (hY : FClass.ACYC p.toProblem) {S : Set ℕ}
    (h : p.toProblem.MPProg p.toProblem.tnI S) :
    p.toProblem.MPProgH (2 ^ (4 * sz p ^ 2 + 2 * sz p + 2)) p.toProblem.tnI S := by
  set q := skDesc p with hqdef
  have hq := skDesc_valid hp
  have hac := (sameShape_skDesc p).isAcyclic.1 hY
  obtain ⟨R, rkL, hb, -, hRl, -, -, hnd, -, -, -⟩ := exists_acycCert hq hac
  have hh := ((acycB_iff q R rkL).1 hb).isACYC_h hnd hRl
  obtain ⟨le, hs, f, hfh, hf⟩ := hh
  set Q := q.toProblem.toPos
  set S' := sz q with hS'
  have hmm : ∀ m, Q.ReachableMethod m → m.subtasks.T.card ≤ S' := meth_card_le q
  have hH := MPProg.toH_measure (Q := Q) rfl hs hf hmm h (HTN.Problem.namesReachable_tnI Q)
  refine hH.mono ?_
  -- the bound on the measure
  set k := p.toProblem.tnI.T.card
  set hgt := (numsOf q).length
  have hk : k ≤ S' := tnI_card_le q
  have hhgt : hgt ≤ S' := length_numsOf_le q
  have hpot : HTN.Problem.potential S' f p.toProblem.tnI ≤ k * geomSum S' hgt := by
    unfold HTN.Problem.potential
    have := Finset.sum_le_card_nsmul p.toProblem.tnI.T
      (fun t => HTN.Problem.worth S' f (p.toProblem.tnI.α t)) (geomSum S' hgt) fun t ht => by
        cases hc : p.toProblem.tnI.α t with
        | inl a => simp [HTN.Problem.worth, hc]
        | inr c =>
          simp only [HTN.Problem.worth, hc, Sum.elim_inr]
          exact geomSum_mono S' (hfh c (HTN.Problem.ReachableName.tnI (P := Q) ht hc))
    simpa using this
  have hg := mul_geomSum_lt k S' hgt
  have hmax : max k S' + 1 ≤ S' + 1 := by omega
  have hpow1 : (max k S' + 1) ^ hgt ≤ (S' + 1) ^ S' :=
    (Nat.pow_le_pow_left hmax _).trans (Nat.pow_le_pow_right (by omega) hhgt)
  have hmu : mu S' f p.toProblem.tnI ≤ (S' + 1) * (S' + 1) ^ S' + S' := by
    unfold mu
    have : (S' + 1) * HTN.Problem.potential S' f p.toProblem.tnI ≤ (S' + 1) * (S' + 1) ^ S' :=
      Nat.mul_le_mul_left _ (hpot.trans (by omega))
    omega
  have hS1 : S' + 1 ≤ 2 ^ S' := Nat.lt_two_pow_self
  have e1 : (S' + 1) * (S' + 1) ^ S' ≤ 2 ^ (S' * (S' + 1)) := by
    calc (S' + 1) * (S' + 1) ^ S' = (S' + 1) ^ (S' + 1) := by ring
      _ ≤ (2 ^ S') ^ (S' + 1) := Nat.pow_le_pow_left hS1 _
      _ = 2 ^ (S' * (S' + 1)) := by rw [← pow_mul]
  have e2 : S' ≤ 2 ^ (S' * (S' + 1)) :=
    (Nat.lt_two_pow_self (n := S')).le.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hS := sz_skDesc_le p
  have e3 : S' * (S' + 1) + 1 ≤ 4 * sz p ^ 2 + 2 * sz p + 2 := by nlinarith
  have e4 : 2 ^ (S' * (S' + 1) + 1) ≤ 2 ^ (4 * sz p ^ 2 + 2 * sz p + 2) :=
    Nat.pow_le_pow_right (by norm_num) e3
  rw [pow_succ] at e4
  omega

theorem skDesc_cert_le (p : FProbDesc) :
    10 * (4 * (sz p + 1)) ^ 2 ≤ 2 ^ (4 * sz p ^ 2 + 4 * sz p + 8) := by
  set S := sz p
  have h1 : S + 1 ≤ 2 ^ S := Nat.lt_two_pow_self
  have h2 : (S + 1) ^ 2 ≤ 2 ^ (2 * S) := by
    calc (S + 1) ^ 2 ≤ (2 ^ S) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 2 ^ (2 * S) := by rw [← pow_mul, mul_comm]
  have h3 : 2 ^ (4 * S ^ 2 + 4 * S + 8) = 2 ^ 8 * (2 ^ (2 * S) * 2 ^ (4 * S ^ 2 + 2 * S)) := by
    rw [← pow_add, ← pow_add]; ring_nf
  have h4 : 1 ≤ 2 ^ (4 * S ^ 2 + 2 * S) := Nat.one_le_two_pow
  rw [h3]
  have : 10 * (4 * (S + 1)) ^ 2 = 160 * (S + 1) ^ 2 := by ring
  rw [this]
  nlinarith

end MPS

/-- **[CB22, Thm. 2], membership (strong)**: strong method-based plan existence for acyclic
problems is in `EXPSPACE`. -/
theorem strongMP_ACYC_mem : Cx.EXPSPACE (PlanExMP .strong FClass.ACYC) := by
  let r : Polynomial ℕ := 4 * Polynomial.X ^ 2 + 4 * Polynomial.X + 8
  have hr : ∀ n, r.eval n = 4 * n ^ 2 + 4 * n + 8 := fun n => by simp [r]
  let D : Polynomial ℕ := 4 * Polynomial.X ^ 2 + 2 * Polynomial.X + 2
  have hD : ∀ n, D.eval n = 4 * n ^ 2 + 2 * n + 2 := fun n => by simp [D]
  refine inExpSpace_planExMP_strong (β := List ℕ × List (ℕ × ℕ))
    (cB := fun x => acycB (skDesc x.1) x.2) (pt_acycB.comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r D (fun p hp hY => ?_) (fun p hp hY S h => ?_)
  · obtain ⟨R, rkL⟩ := b
    exact (sameShape_skDesc p).isAcyclic.2 ((acycB_iff (skDesc p) R rkL).1 hb).isACYC
  · have hq := skDesc_valid hp
    have hS := sz_skDesc_le p
    have hac := (sameShape_skDesc p).isAcyclic.1 hY
    obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -, -, -⟩ := exists_acycCert hq hac
    have hK : (numsOf (skDesc p)).length ≤ sz (skDesc p) := length_numsOf_le _
    have h1 := sz_rcert_le (H := (numsOf (skDesc p)).length + 1) hRN hRl
      (fun q hq => ⟨(hrkN q hq).1, Nat.lt_succ_of_le (hrkN q hq).2⟩) hrkl
    have h2 : (sz (skDesc p) + ((numsOf (skDesc p)).length + 1) + 1) ^ 2 ≤
        (4 * (sz p + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 := skDesc_cert_le p
    have he := skDesc_exp_le p
    have he' : 2 ^ (4 * sz p ^ 2 + 4 * sz p + 6) ≤ 2 ^ (4 * sz p ^ 2 + 4 * sz p + 8) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨-, hn⟩ := tr_hcomp hq (isTailREC_of_isACYC hac)
    rw [hr]
    exact ⟨⟨(R, rkL), hb, by omega⟩, IsHTNProgBound.mono hn (he.trans he')⟩
  · rw [hD]
    exact acyc_depth hp hY h

/-- Membership in `EXPSPACE` together with the inherited lower bound (NEXPTIME-hardness, already
for acyclic problems with a totally ordered initial network). -/
theorem strongMP_ACYC_bounds :
    Cx.EXPSPACE (PlanExMP .strong FClass.ACYC) ∧
      Cx.Hard Cx.NEXPTIME (PlanExMP .strong FClass.ACYC) :=
  ⟨strongMP_ACYC_mem, (hard_ACYC_mp .strong (by decide)).of_redP
    (redP_filterMP pt_fToB fun _ hp => fToB_iff hp)⟩

end FOND
