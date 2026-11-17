import HtnPlanning.Core.DecompositionIso
import HtnPlanning.Core.SolutionIso
import HtnPlanning.Core.ReachableLabels
/-!
# Task networks under label maps

`HTN.TaskNetwork.mapL ψ tn` keeps the ids and the order of `tn` and maps every label by an
arbitrary function `ψ : A ⊕ C → A' ⊕ C'` — unlike `HTN.TaskNetwork.relabel` of the library, a
primitive name may become a compound one and vice versa.  This is what the weak compilation of
[CB21, Lemma 4.3] needs: every primitive task `a` becomes a compound task `c_a` with one method
per outcome of `a`.

* `HTN.decomposesTo_mapL` — **embedding**: decompositions are mapped along `e` when every method
  has an image method;
* `HTN.exists_decomposesTo_mapL_of` — **projection**: a decomposition with methods `M'` maps
  along `ψ`, up to isomorphism, to a decomposition with methods `M`, when every method of `M'`
  either maps onto a method of `M` or is *silent*: it replaces a task by a single task with the
  same `ψ`-image;
* `HTN.exists_decomposesTo_setLabels` — **expansion**: given, for every task, a method replacing
  it by a single task, all tasks can be expanded.
-/

namespace HTN

variable {I A C A' C' A'' C'' : Type}

namespace TaskNetwork

/-- The task network with all labels mapped by `ψ`. -/
def mapL (ψ : A ⊕ C → A' ⊕ C') (tn : TaskNetwork I A C) : TaskNetwork I A' C' :=
  ⟨tn.T, tn.ord, fun x => ψ (tn.α x)⟩

variable {ψ : A ⊕ C → A' ⊕ C'}

@[simp] theorem mapL_T (tn : TaskNetwork I A C) : (tn.mapL ψ).T = tn.T := rfl
@[simp] theorem mapL_ord (tn : TaskNetwork I A C) : (tn.mapL ψ).ord = tn.ord := rfl
@[simp] theorem mapL_α (tn : TaskNetwork I A C) (x : I) : (tn.mapL ψ).α x = ψ (tn.α x) := rfl

theorem mapL_mapL {χ : A' ⊕ C' → A'' ⊕ C''} (tn : TaskNetwork I A C) :
    (tn.mapL ψ).mapL χ = tn.mapL (χ ∘ ψ) := rfl

theorem mapL_id (tn : TaskNetwork I A C) : tn.mapL id = tn := rfl

theorem mapL_wf {tn : TaskNetwork I A C} (h : tn.WF) : (tn.mapL ψ).WF :=
  ⟨h.mem_left, h.mem_right, h.irrefl, h.trans⟩

theorem mapL_decomposeWith [DecidableEq I] (tn u : TaskNetwork I A C) (t : I) :
    (decomposeWith tn t u).mapL ψ = decomposeWith (tn.mapL ψ) t (u.mapL ψ) := by
  refine ext' rfl rfl ?_
  funext x
  simp only [mapL, decomposeWith]
  split_ifs <;> rfl

theorem Iso.mapL {tn u : TaskNetwork I A C} (h : tn.Iso u) : (tn.mapL ψ).Iso (u.mapL ψ) := by
  obtain ⟨σ, hb, ho, hα⟩ := h
  exact ⟨σ, hb, ho, fun t ht => by simp [hα t ht]⟩

theorem isLinearization_mapL {tn : TaskNetwork I A C} {l : List I} :
    (tn.mapL ψ).IsLinearization l ↔ tn.IsLinearization l := Iff.rfl

/-- The task network with the labels given by `f` on the ids. -/
def setLabels (tn : TaskNetwork I A C) (f : I → A ⊕ C) : TaskNetwork I A C := ⟨tn.T, tn.ord, f⟩

theorem setLabels_wf {tn : TaskNetwork I A C} (h : tn.WF) (f : I → A ⊕ C) :
    (tn.setLabels f).WF := ⟨h.mem_left, h.mem_right, h.irrefl, h.trans⟩

/-- **Replacing a task by a single fresh task** gives, up to isomorphism, the same network with
one label changed. -/
theorem decomposeWith_single_iso [DecidableEq I] {tn u : TaskNetwork I A C} {t j : I}
    (htn : tn.WF) (ht : t ∈ tn.T) (hu : u.WF) (huT : u.T = {j}) (hj : j ∉ tn.T) :
    (decomposeWith tn t u).Iso (tn.setLabels (Function.update tn.α t (u.α j))) := by
  classical
  have hjt : j ≠ t := fun e => hj (e ▸ ht)
  have huo : ∀ x y, ¬ u.ord x y := by
    intro x y hxy
    have hx := hu.mem_left hxy
    have hy := hu.mem_right hxy
    rw [huT, Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact hu.irrefl _ hxy
  have hnl : ∀ y, ¬ tn.ord j y := fun y h => hj (htn.mem_left h)
  have hnr : ∀ y, ¬ tn.ord y j := fun y h => hj (htn.mem_right h)
  let σ : I → I := fun x => if x = j then t else x
  have hT : (decomposeWith tn t u).T = insert j (tn.T.erase t) := by
    simp only [decomposeWith, huT]
    ext x; simp [or_comm]
  refine ⟨σ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, hT, Finset.mem_insert, Finset.mem_erase] at hx
    simp only [Finset.mem_coe, setLabels, σ]
    rcases hx with hx | ⟨-, hx⟩
    · simpa [hx] using ht
    · have : x ≠ j := fun e => hj (e ▸ hx)
      simpa [this] using hx
  · intro x hx y hy hxy
    rw [Finset.mem_coe, hT, Finset.mem_insert, Finset.mem_erase] at hx hy
    have hne : ∀ z, z ∈ tn.T → z ≠ j := fun z hz e => hj (e ▸ hz)
    simp only [σ] at hxy
    rcases hx with hx | ⟨hxt, hx⟩ <;> rcases hy with hy | ⟨hyt, hy⟩
    · rw [hx, hy]
    · rw [if_pos hx, if_neg (hne y hy)] at hxy; exact absurd hxy.symm hyt
    · rw [if_neg (hne x hx), if_pos hy] at hxy; exact absurd hxy hxt
    · rwa [if_neg (hne x hx), if_neg (hne y hy)] at hxy
  · intro y hy
    rw [Finset.mem_coe] at hy
    simp only [setLabels] at hy
    by_cases hyt : y = t
    · subst hyt
      exact ⟨j, by rw [Finset.mem_coe, hT]; simp, by simp [σ]⟩
    · have hyj : y ≠ j := fun e => hj (e ▸ hy)
      exact ⟨y, by rw [Finset.mem_coe, hT]; simp [hyt, hy], by simp [σ, hyj]⟩
  · intro x hx y hy
    rw [hT, Finset.mem_insert, Finset.mem_erase] at hx hy
    simp only [decomposeWith, setLabels, σ, huT, Finset.mem_singleton]
    rcases hx with hx | ⟨hxt, hx⟩ <;> rcases hy with hy | ⟨hyt, hy⟩
    · subst x; subst y; simp [huo, hnl, hnr, htn.irrefl]
    · subst x
      have hyj : y ≠ j := fun e => hj (e ▸ hy)
      simp [huo, hnl, hyj, hyt]
    · subst y
      have hxj : x ≠ j := fun e => hj (e ▸ hx)
      simp [huo, hnr, hxj, hxt]
    · have hxj : x ≠ j := fun e => hj (e ▸ hx)
      have hyj : y ≠ j := fun e => hj (e ▸ hy)
      simp [huo, hxj, hyj, hxt, hyt]
  · intro x hx
    rw [hT, Finset.mem_insert, Finset.mem_erase] at hx
    simp only [decomposeWith, setLabels, σ, huT, Finset.mem_singleton]
    rcases hx with hx | ⟨hxt, hx⟩
    · subst x
      rw [if_pos rfl, if_pos rfl, Function.update_self]
    · have hxj : x ≠ j := fun e => hj (e ▸ hx)
      simp [hxj, hxt]

end TaskNetwork

open TaskNetwork

/-- A method with mapped labels. -/
def Method.mapL (ψ : A ⊕ C → A' ⊕ C') (c' : C') (m : Method I A C) : Method I A' C' :=
  ⟨c', m.subtasks.mapL ψ⟩

variable [DecidableEq I]

/-! ### Embedding -/

theorem decomposesTo_mapL {M : Set (Method I A C)} {M' : Set (Method I A' C')}
    {e : A ⊕ C → A' ⊕ C'} {eC : C → C'} (he : ∀ c, e (Sum.inr c) = Sum.inr (eC c))
    (hM : ∀ m ∈ M, ∃ m' ∈ M', m'.abstractTask = eC m.abstractTask ∧
      (m.subtasks.mapL e).Iso m'.subtasks) {tn tn' : TaskNetwork I A C}
    (h : DecomposesTo M tn tn') : DecomposesTo M' (tn.mapL e) (tn'.mapL e) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨t, m, hm, ht, hα, u, hu, huiso, hdisj, rfl⟩ := hstep
    obtain ⟨m', hm', hc, hiso⟩ := hM m hm
    refine ih.tail ⟨t, m', hm', ht, by simp [hα, he, hc], u.mapL e, mapL_wf hu,
      huiso.mapL.trans hiso, hdisj, mapL_decomposeWith _ _ _⟩

/-! ### Projection -/

/-- A method of `M'` that maps to a method of `M` along `ψ`, or is silent. -/
def ProjOK (M : Set (Method I A C)) (ψ : A' ⊕ C' → A ⊕ C) (m' : Method I A' C') : Prop :=
  (∃ m ∈ M, ψ (Sum.inr m'.abstractTask) = Sum.inr m.abstractTask ∧
    (m'.subtasks.mapL ψ).Iso m.subtasks) ∨
  (∃ i, m'.subtasks.T = {i} ∧ ψ (m'.subtasks.α i) = ψ (Sum.inr m'.abstractTask))

theorem exists_decomposesTo_mapL_of [Infinite I] {M : Set (Method I A C)}
    {M' : Set (Method I A' C')} {ψ : A' ⊕ C' → A ⊕ C} (hM : ∀ m' ∈ M', ProjOK M ψ m')
    (hMwf : ∀ m' ∈ M', m'.subtasks.WF) {tn tn' : TaskNetwork I A' C'}
    (h : DecomposesTo M' tn tn') (htn : tn.WF) :
    ∃ X, DecomposesTo M (tn.mapL ψ) X ∧ X.Iso (tn'.mapL ψ) ∧ X.WF := by
  induction h with
  | refl => exact ⟨tn.mapL ψ, Relation.ReflTransGen.refl, Iso.refl _, mapL_wf htn⟩
  | @tail tn₁ tn₂ h₁ hstep ih =>
    obtain ⟨X₁, hX₁, hiso₁, hwfX₁⟩ := ih
    have hwf₁ : tn₁.WF := HTN.DecomposesTo.wf (M := M') h₁ htn
    obtain ⟨t, m', hstep⟩ := hstep
    have hwf₂ : tn₂.WF := hstep.wf hwf₁
    obtain ⟨hm', ht, hα, u, hu, huiso, hdisj, htn₂⟩ := hstep
    rcases hM m' hm' with ⟨m, hm, hc, hsub⟩ | ⟨i, hiT, hiα⟩
    · have hs : DecompStep M (tn₁.mapL ψ) t m (tn₂.mapL ψ) := by
        refine ⟨hm, ht, by simp [hα, hc], u.mapL ψ, mapL_wf hu, ?_, hdisj, ?_⟩
        · exact huiso.mapL.trans hsub
        · rw [htn₂]; exact mapL_decomposeWith _ _ _
      obtain ⟨t', X₂, hs', hiso₂⟩ := hs.iso (mapL_wf hwf₁) hwfX₁ hiso₁.symm
      exact ⟨X₂, hX₁.tail ⟨t', m, hs'⟩, hiso₂.symm, hs'.wf hwfX₁⟩
    · -- the silent case: the network does not change up to isomorphism
      obtain ⟨σ, hb, -, hσα⟩ := huiso
      have hu1 : ∃ j, u.T = {j} := by
        have hcard : u.T.card = 1 := by
          have := hb.image_eq
          have h' : (u.T.image σ) = m'.subtasks.T := by
            ext x; simpa [Set.ext_iff] using congrArg (x ∈ ·) this
          rw [← Finset.card_image_of_injOn hb.injOn, h', hiT, Finset.card_singleton]
        exact Finset.card_eq_one.1 hcard
      obtain ⟨j, hjT⟩ := hu1
      have hσj : σ j = i := by
        have := hb.mapsTo (show j ∈ (u.T : Set I) by simp [hjT])
        simpa [hiT] using this
      have hjα : ψ (u.α j) = ψ (tn₁.α t) := by
        rw [hσα j (by simp [hjT]), hσj, hiα, hα]
      have hj : j ∉ tn₁.T := fun hj => Finset.disjoint_left.1 hdisj hj (by simp [hjT])
      have hiso := (decomposeWith_single_iso hwf₁ ht hu hjT hj).mapL (ψ := ψ)
      have heq : (tn₁.setLabels (Function.update tn₁.α t (u.α j))).mapL ψ = tn₁.mapL ψ := by
        refine ext' rfl rfl ?_
        funext x
        simp only [mapL, setLabels]
        by_cases hx : x = t
        · subst hx; simp [hjα]
        · simp [Function.update_of_ne hx]
      rw [heq, ← htn₂] at hiso
      exact ⟨X₁, hX₁, hiso₁.trans hiso.symm, hwfX₁⟩

/-! ### Expansion -/

theorem exists_decomposesTo_setLabels [Infinite I] {M' : Set (Method I A' C')}
    {N : TaskNetwork I A' C'} (hN : N.WF) (f : I → A' ⊕ C')
    (hf : ∀ t ∈ N.T, ∃ m ∈ M', N.α t = Sum.inr m.abstractTask ∧ m.subtasks.WF ∧
      ∃ i, m.subtasks.T = {i} ∧ m.subtasks.α i = f t) :
    ∃ N', DecomposesTo M' N N' ∧ N'.Iso (N.setLabels f) ∧ N'.WF := by
  classical
  let relab : Finset I → TaskNetwork I A' C' := fun S =>
    N.setLabels fun x => if x ∈ S then f x else N.α x
  suffices key : ∀ S : Finset I, S ⊆ N.T →
      ∃ N', DecomposesTo M' N N' ∧ N'.Iso (relab S) ∧ N'.WF by
    obtain ⟨N', h1, h2, h3⟩ := key N.T subset_rfl
    refine ⟨N', h1, ?_, h3⟩
    have : (relab N.T).Iso (N.setLabels f) :=
      ⟨id, Set.bijOn_id _, fun _ _ _ _ => Iff.rfl, fun x hx => by have hx' : x ∈ N.T := hx; simp [relab, setLabels, hx']⟩
    exact h2.trans this
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨N, Relation.ReflTransGen.refl, ?_, hN⟩
    have : relab ∅ = N := ext' rfl rfl (by funext x; simp [relab, setLabels])
    rw [this]
  | @insert t S htS ih =>
    intro hsub
    obtain ⟨N', hN', hiso, hwf'⟩ := ih ((Finset.subset_insert _ _).trans hsub)
    have ht : t ∈ N.T := hsub (Finset.mem_insert_self _ _)
    obtain ⟨m, hm, hα, hmwf, i, hiT, hiα⟩ := hf t ht
    -- decompose `t` in `relab S` into a fresh task
    have hwfR : (relab S).WF := setLabels_wf hN _
    obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset (relab S).T
    let u : TaskNetwork I A' C' := ⟨{j}, fun _ _ => False, fun _ => f t⟩
    have hu : u.WF := ⟨fun h => h.elim, fun h => h.elim, fun _ h => h, fun h => h.elim⟩
    have huiso : u.Iso m.subtasks := by
      refine ⟨fun _ => i, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · intro x _; simp [hiT]
      · intro x hx y hy _; simp [u] at hx hy; rw [hx, hy]
      · intro y hy; simp [hiT] at hy; exact ⟨j, by simp [u], hy.symm⟩
      · intro x hx y hy
        simp only [u, false_iff]
        intro h
        have := hmwf.mem_left h
        rw [hiT, Finset.mem_singleton] at this
        exact hmwf.irrefl _ (this ▸ h)
      · intro x _; simp [u, hiα]
    have hs : DecompStep M' (relab S) t m (decomposeWith (relab S) t u) :=
      ⟨hm, ht, by simp [relab, setLabels, htS, hα], u, hu, huiso,
        Finset.disjoint_singleton_right.2 hj, rfl⟩
    obtain ⟨t', N'', hs', hiso''⟩ := hs.iso hwfR hwf' hiso.symm
    refine ⟨N'', hN'.tail ⟨t', m, hs'⟩, ?_, hs'.wf hwf'⟩
    have h1 := decomposeWith_single_iso hwfR ht hu rfl hj
    have h2 : (relab S).setLabels (Function.update (relab S).α t (u.α j)) = relab (insert t S) := by
      refine ext' rfl rfl ?_
      funext x
      simp only [relab, setLabels, u]
      by_cases hx : x = t
      · subst hx; simp
      · simp [Function.update_of_ne hx, hx]
    rw [h2] at h1
    exact hiso''.symm.trans h1

end HTN
