import HtnPlanning.Article.MostlyAcyc
import HtnPlanning.Article.Progression
import HtnPlanning.Article.AbsProgression
import HtnPlanning.Article.AcycProgression
/-!
# Progression up to isomorphism

Progression creates fresh task ids, so the task networks a search over *descriptions* produces
(with ids chosen by the search) are only isomorphic to those of a given progression.  This file
transfers progression steps:

* along *agreement* (`HTN.TaskNetwork.Agree`: same tasks, order and labels on the tasks) —
  `HTN.Article.Problem.ProgStep.agree`;
* along an *isomorphism* `σ` (`HTN.Article.IsoVia`), for an arbitrary choice of the fresh copy of
  the method — `HTN.Article.IsoVia.progress`, `HTN.Article.IsoVia.decomposeWith`.
-/

namespace HTN

namespace Article

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

theorem IsoVia.of_agree {σ : I → I} {tn u u' : TaskNetwork I A C} (h : IsoVia σ tn u)
    (hag : u.Agree u') : IsoVia σ tn u' := by
  obtain ⟨hT, ho, hα⟩ := hag
  obtain ⟨hb, hord, hlab⟩ := h
  refine ⟨by rw [← hT]; exact hb, fun a ha b hb' => by rw [← ho]; exact hord a ha b hb',
    fun a ha => ?_⟩
  have hm : σ a ∈ u.T := by simpa using hb.mapsTo (by simpa using ha)
  rw [hlab a ha, hα _ hm]

theorem isoVia_id_of_agree {tn u : TaskNetwork I A C} (h : tn.Agree u) : IsoVia id tn u :=
  IsoVia.of_agree ⟨Set.bijOn_id _, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩ h

theorem IsoVia.mem {σ : I → I} {tn u : TaskNetwork I A C} (h : IsoVia σ tn u) {a : I}
    (ha : a ∈ tn.T) : σ a ∈ u.T := by
  simpa using h.1.mapsTo (by simpa using ha)

theorem IsoVia.inj {σ : I → I} {tn u : TaskNetwork I A C} (h : IsoVia σ tn u) {a b : I}
    (ha : a ∈ tn.T) (hb : b ∈ tn.T) (e : σ a = σ b) : a = b :=
  h.1.injOn (by simpa using ha) (by simpa using hb) e

theorem IsoVia.surj {σ : I → I} {tn u : TaskNetwork I A C} (h : IsoVia σ tn u) {b : I}
    (hb : b ∈ u.T) : ∃ a ∈ tn.T, σ a = b := by
  obtain ⟨a, ha, e⟩ := h.1.surjOn (by simpa using hb)
  exact ⟨a, by simpa using ha, e⟩

theorem IsoVia.unconstrained {σ : I → I} {tn u : TaskNetwork I A C} (h : IsoVia σ tn u) {t : I}
    (hu : tn.Unconstrained t) : u.Unconstrained (σ t) := by
  refine ⟨h.mem hu.1, fun y hy hyt => ?_⟩
  obtain ⟨a, ha, rfl⟩ := h.surj hy
  exact hu.2 a ha ((h.2.1 a ha t hu.1).2 hyt)

theorem IsoVia.progress {σ : I → I} {tn u : TaskNetwork I A C} (h : IsoVia σ tn u) {t : I}
    (ht : t ∈ tn.T) : IsoVia σ (tn.progress t) (u.progress (σ t)) := by
  refine ⟨⟨fun a ha => ?_, fun a ha b hb e => h.inj ?_ ?_ e, fun b hb => ?_⟩,
    fun a ha b hb => ?_, fun a ha => h.2.2 a ?_⟩
  · simp only [Finset.mem_coe, TaskNetwork.mem_progress_T] at ha ⊢
    exact ⟨fun e => ha.1 (h.inj ha.2 ht e), h.mem ha.2⟩
  · exact (TaskNetwork.mem_progress_T.1 (Finset.mem_coe.1 ha)).2
  · exact (TaskNetwork.mem_progress_T.1 (Finset.mem_coe.1 hb)).2
  · simp only [Finset.mem_coe, TaskNetwork.mem_progress_T] at hb
    obtain ⟨a, ha, rfl⟩ := h.surj hb.2
    exact ⟨a, Finset.mem_coe.2 (TaskNetwork.mem_progress_T.2 ⟨fun e => hb.1 (by rw [e]), ha⟩), rfl⟩
  · rw [TaskNetwork.mem_progress_T] at ha hb
    simp only [TaskNetwork.progress]
    rw [h.2.1 a ha.2 b hb.2]
    exact and_congr Iff.rfl ⟨fun e e' => e (h.inj ha.2 ht e'), fun e e' => e (e' ▸ rfl)⟩
  · exact (TaskNetwork.mem_progress_T.1 ha).2

section Decomp

variable {tn tn'' : TaskNetwork I A C} {t : I}

/-- The order of a decomposed network, by the origin of the two tasks. -/
theorem dord_iff (hwf : tn.WF) (hwf'' : tn''.WF) (hd : Disjoint tn.T tn''.T) (a b : I) :
    (decomposeWith tn t tn'').ord a b ↔
      (a ∈ tn''.T ∧ b ∈ tn''.T ∧ tn''.ord a b) ∨ (a ∈ tn''.T ∧ b ∉ tn''.T ∧ tn.ord t b) ∨
      (a ∉ tn''.T ∧ b ∈ tn''.T ∧ tn.ord a t) ∨
      (a ∉ tn''.T ∧ b ∉ tn''.T ∧ tn.ord a b ∧ a ≠ t ∧ b ≠ t) := by
  have hdis : ∀ y, y ∈ tn.T → y ∉ tn''.T := fun y hy hy' => Finset.disjoint_left.1 hd hy hy'
  simp only [decomposeWith]
  by_cases ha : a ∈ tn''.T <;> by_cases hb : b ∈ tn''.T
  · have h1 : ¬ tn.ord a t := fun h => hdis a (hwf.mem_left h) ha
    have h2 : ¬ tn.ord t b := fun h => hdis b (hwf.mem_right h) hb
    have h3 : ¬ tn.ord a b := fun h => hdis a (hwf.mem_left h) ha
    simp only [ha, hb, h1, h2, h3]; tauto
  · have h1 : ¬ tn''.ord a b := fun h => hb (hwf''.mem_right h)
    have h3 : ¬ tn.ord a b := fun h => hdis a (hwf.mem_left h) ha
    have h4 : ¬ tn.ord a t := fun h => hdis a (hwf.mem_left h) ha
    simp only [ha, hb, h1, h3, h4]; tauto
  · have h1 : ¬ tn''.ord a b := fun h => ha (hwf''.mem_left h)
    have h3 : ¬ tn.ord a b := fun h => hdis b (hwf.mem_right h) hb
    have h4 : ¬ tn.ord t b := fun h => hdis b (hwf.mem_right h) hb
    simp only [ha, hb, h1, h3, h4]; tauto
  · have h1 : ¬ tn''.ord a b := fun h => ha (hwf''.mem_left h)
    simp only [ha, hb, h1]; tauto

/-- **Decomposition transfers along an isomorphism**, for any choice of the fresh copy. -/
theorem IsoVia.decomposeWith {σ : I → I} {u u'' : TaskNetwork I A C} (h : IsoVia σ tn u)
    (hwf : tn.WF) (huwf : u.WF) (ht : t ∈ tn.T) (hwf'' : tn''.WF) (hu'' : u''.WF)
    (hiso : tn''.Iso u'') (hd : Disjoint tn.T tn''.T) (hdu : Disjoint u.T u''.T) :
    ∃ σ', IsoVia σ' (HTN.decomposeWith tn t tn'') (HTN.decomposeWith u (σ t) u'') ∧
      (∀ y ∈ tn''.T, σ' y ∈ u''.T) ∧ ∀ y ∈ tn.T, σ' y = σ y := by
  classical
  obtain ⟨τ, hτ⟩ := hiso
  have hτv : IsoVia τ tn'' u'' := hτ
  have hdis : ∀ y, y ∈ tn.T → y ∉ tn''.T := fun y hy hy' => Finset.disjoint_left.1 hd hy hy'
  have hdisu : ∀ y, y ∈ u.T → y ∉ u''.T := fun y hy hy' => Finset.disjoint_left.1 hdu hy hy'
  let σ' : I → I := fun y => if y ∈ tn''.T then τ y else σ y
  have hn : ∀ y ∈ tn''.T, σ' y = τ y := fun y hy => if_pos hy
  have ho : ∀ y, y ∉ tn''.T → σ' y = σ y := fun y hy => if_neg hy
  -- memberships
  have hmem : ∀ y, y ∈ (HTN.decomposeWith tn t tn'').T ↔ (y ∈ tn.T ∧ y ≠ t) ∨ y ∈ tn''.T :=
    fun y => mem_decomposeWith_T
  have hmemu : ∀ y, y ∈ (HTN.decomposeWith u (σ t) u'').T ↔ (y ∈ u.T ∧ y ≠ σ t) ∨ y ∈ u''.T :=
    fun y => mem_decomposeWith_T
  have himg_new : ∀ y ∈ tn''.T, σ' y ∈ u''.T := fun y hy => by rw [hn y hy]; exact hτv.mem hy
  have himg_old : ∀ y ∈ tn.T, σ' y = σ y ∧ σ y ∉ u''.T := fun y hy =>
    ⟨ho y (hdis y hy), hdisu _ (h.mem hy)⟩
  refine ⟨σ', ⟨⟨fun y hy => ?_, fun y hy z hz e => ?_, fun z hz => ?_⟩, fun a ha b hb => ?_,
    fun a ha => ?_⟩, himg_new, fun y hy => (himg_old y hy).1⟩
  · rw [Finset.mem_coe, hmem] at hy
    rw [Finset.mem_coe, hmemu]
    rcases hy with ⟨hy, hyt⟩ | hy
    · rw [(himg_old y hy).1]
      exact Or.inl ⟨h.mem hy, fun e => hyt (h.inj hy ht e)⟩
    · exact Or.inr (himg_new y hy)
  · rw [Finset.mem_coe, hmem] at hy hz
    rcases hy with ⟨hy, -⟩ | hy <;> rcases hz with ⟨hz, -⟩ | hz
    · rw [(himg_old y hy).1, (himg_old z hz).1] at e; exact h.inj hy hz e
    · exfalso; have := himg_new z hz; rw [← e, (himg_old y hy).1] at this
      exact (himg_old y hy).2 this
    · exfalso; have := himg_new y hy; rw [e, (himg_old z hz).1] at this
      exact (himg_old z hz).2 this
    · rw [hn y hy, hn z hz] at e; exact hτv.inj hy hz e
  · rw [Finset.mem_coe, hmemu] at hz
    rcases hz with ⟨hz, hzt⟩ | hz
    · obtain ⟨a, ha, rfl⟩ := h.surj hz
      refine ⟨a, ?_, (himg_old a ha).1⟩
      rw [Finset.mem_coe, hmem]
      exact Or.inl ⟨ha, fun e => hzt (e ▸ rfl)⟩
    · obtain ⟨a, ha, rfl⟩ := hτv.surj hz
      exact ⟨a, by rw [Finset.mem_coe, hmem]; exact Or.inr ha, hn a ha⟩
  · have hwfD : (HTN.decomposeWith u (σ t) u'').WF := decomposeWith_wf huwf hu'' hdu
    rw [hmem] at ha hb
    rw [dord_iff hwf hwf'' hd, dord_iff huwf hu'' hdu]
    rcases ha with ⟨ha, hat⟩ | ha <;> rcases hb with ⟨hb, hbt⟩ | hb
    · obtain ⟨ea, na⟩ := himg_old a ha
      obtain ⟨eb, nb⟩ := himg_old b hb
      rw [ea, eb]
      have hat' : σ a ≠ σ t := fun e => hat (h.inj ha ht e)
      have hbt' : σ b ≠ σ t := fun e => hbt (h.inj hb ht e)
      simp only [hdis a ha, hdis b hb, na, nb, false_and, not_false_eq_true, true_and, false_or,
        hat, hbt, hat', hbt', ne_eq, and_true]
      exact h.2.1 a ha b hb
    · obtain ⟨ea, na⟩ := himg_old a ha
      rw [ea, hn b hb]
      simp only [hdis a ha, na, hb, hτv.mem hb, not_false_eq_true, true_and, false_and, false_or,
        and_false, or_false, not_true_eq_false]
      exact h.2.1 a ha t ht
    · obtain ⟨eb, nb⟩ := himg_old b hb
      rw [hn a ha, eb]
      simp only [hdis b hb, nb, ha, hτv.mem ha, not_false_eq_true, true_and, false_and, false_or,
        and_false, or_false, not_true_eq_false]
      exact h.2.1 t ht b hb
    · rw [hn a ha, hn b hb]
      simp only [ha, hb, hτv.mem ha, hτv.mem hb, true_and, not_true_eq_false, false_and, or_false]
      exact hτv.2.1 a ha b hb
  · rw [hmem] at ha
    simp only [HTN.decomposeWith]
    rcases ha with ⟨ha, -⟩ | ha
    · rw [if_neg (hdis a ha), (himg_old a ha).1, if_neg (himg_old a ha).2]
      exact h.2.2 a ha
    · rw [if_pos ha, hn a ha, if_pos (hτv.mem ha)]
      exact hτv.2.2 a ha

end Decomp

/-! ### Progression along agreement -/

namespace Problem

variable (P : Problem F A C I)

/-- **Progression depends on the tasks, the order on them and their labels only.** -/
theorem ProgStep.agree {n₁ n₂ : PNode F A C I} (h : P.ProgStep n₁ n₂) {B : TaskNetwork I A C}
    (hag : n₁.net.Agree B) :
    ∃ B', P.ProgStep ⟨n₁.state, B, n₁.plan⟩ ⟨n₂.state, B', n₂.plan⟩ ∧ n₂.net.Agree B' := by
  cases h with
  | @prog s tn π t a hu hαt happ =>
    obtain ⟨hT, ho, hα⟩ := hag
    dsimp only at hT ho hα
    refine ⟨B.progress t, .prog ⟨hT ▸ hu.1, fun t' ht' => ?_⟩ ((hα t hu.1).symm.trans hαt) happ,
      ?_, ?_, ?_⟩
    · rw [← ho]; exact hu.2 t' (hT ▸ ht')
    · simp [TaskNetwork.progress, hT]
    · funext a b; simp [TaskNetwork.progress, ho]
    · intro y hy; exact hα y (Finset.mem_of_mem_erase hy)
  | @decomp s tn tn' π t m hu hd =>
    obtain ⟨hT, ho, hα⟩ := hag
    dsimp only at hT ho hα
    obtain ⟨hm, ht, hαt, tn'', hwf'', hiso, hdisj, rfl⟩ := hd
    refine ⟨HTN.decomposeWith B t tn'',
      .decomp ⟨hT ▸ hu.1, fun t' ht' => ?_⟩ ⟨hm, hT ▸ ht, (hα t ht).symm.trans hαt, tn'', hwf'',
        hiso, hT ▸ hdisj, rfl⟩, ?_, ?_, ?_⟩
    · rw [← ho]; exact hu.2 t' (hT ▸ ht')
    · simp [HTN.decomposeWith, hT]
    · funext a b; simp [HTN.decomposeWith, ho]
    · intro y hy
      simp only [HTN.decomposeWith]
      split_ifs with h
      · rfl
      · rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact hα y hy
        · exact absurd hy h

/-- **Acyclic progression depends on the tasks, the order and labels on them, and their
ancestors only.** -/
theorem AProgStep.agree {n₁ n₂ : APNode F A C I} (h : P.AProgStep n₁ n₂) {B : TaskNetwork I A C}
    (hag : n₁.net.Agree B) {an : I → Set C} (han : ∀ x ∈ n₁.net.T, n₁.anc x = an x) :
    ∃ B' an', P.AProgStep ⟨n₁.state, B, an, n₁.plan⟩ ⟨n₂.state, B', an', n₂.plan⟩ ∧
      n₂.net.Agree B' ∧ ∀ x ∈ n₂.net.T, n₂.anc x = an' x := by
  cases h with
  | @prog s tn an₀ π t a hu hαt happ =>
    obtain ⟨hT, ho, hα⟩ := hag
    dsimp only at hT ho hα han ⊢
    refine ⟨B.progress t, an, .prog ⟨hT ▸ hu.1, fun t' ht' => ?_⟩ ((hα t hu.1).symm.trans hαt) happ,
      ⟨?_, ?_, ?_⟩, fun x hx => han x (Finset.mem_of_mem_erase hx)⟩
    · rw [← ho]; exact hu.2 t' (hT ▸ ht')
    · simp [TaskNetwork.progress, hT]
    · funext a b; simp [TaskNetwork.progress, ho]
    · intro y hy; exact hα y (Finset.mem_of_mem_erase hy)
  | @decomp s tn tn'' an₀ π t m hu hm hαt hwf'' hiso hdisj hanc =>
    obtain ⟨hT, ho, hα⟩ := hag
    dsimp only at hT ho hα han ⊢
    refine ⟨HTN.decomposeWith B t tn'', fun x => if x ∈ tn''.T then Insert.insert m.abstractTask (an t)
      else an x, .decomp ⟨hT ▸ hu.1, fun t' ht' => ?_⟩ hm ((hα t hu.1).symm.trans hαt) hwf'' hiso
        (hT ▸ hdisj) (fun v hv c hc => (han t hu.1) ▸ hanc v hv c hc), ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← ho]; exact hu.2 t' (hT ▸ ht')
    · simp [HTN.decomposeWith, hT]
    · funext a b; simp [HTN.decomposeWith, ho]
    · intro y hy
      simp only [HTN.decomposeWith]
      split_ifs with h
      · rfl
      · rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact hα y hy
        · exact absurd hy h
    · intro x hx
      simp only
      split_ifs with h
      · rw [han t hu.1]
      · rcases mem_decomposeWith_T.1 hx with ⟨hx, -⟩ | hx
        · exact han x hx
        · exact absurd hx h
  | @insert s tn an₀ π a happ =>
    exact ⟨B, an, .insert happ, hag, han⟩

end Problem

end Article

end HTN
