import HtnPlanning.Core.Decomposition
/-!
# Decomposition does not depend on the choice of task identifiers

Task networks are only relevant up to isomorphism (`HTN.TaskNetwork.Iso`), i.e. up to renaming
of task identifiers.  This file shows that the decomposition relation respects this:

* `HTN.decomposeWith_iso_congr`: decomposing isomorphic task networks (at corresponding tasks,
  by isomorphic subtask networks) yields isomorphic task networks;
* `HTN.DecompStep.iso`: if `tn₁ ≅ tn₁'` and `tn₁ --t,m--> tn₂`, then `tn₁'` can be decomposed by
  the same method into some `tn₂' ≅ tn₂`;
* `HTN.DecomposesTo.iso`: the same for arbitrary decomposition sequences `tn₁ →* tn₂`.

These are the technical backbone for every argument that transforms an HTN planning problem
(such as the compilations of hierarchical structures into other planning formalisms).
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

/-- **Decomposition is compatible with isomorphism.** If `σ` is an isomorphism from `tn₁` to
`tn₁'`, `ρ` an isomorphism from the fresh network `u` to the fresh network `u'`, and `t` a task
of `tn₁`, then decomposing `t` in `tn₁` by `u` and `σ t` in `tn₁'` by `u'` gives isomorphic
results. -/
theorem decomposeWith_iso_congr [DecidableEq I] {tn₁ tn₁' u u' : TaskNetwork I A C} {t : I}
    {σ ρ : I → I} (h₁ : tn₁.WF) (h₁' : tn₁'.WF) (hu : u.WF) (hu' : u'.WF)
    (hdisj : Disjoint tn₁.T u.T) (hdisj' : Disjoint tn₁'.T u'.T) (ht : t ∈ tn₁.T)
    (hσbij : Set.BijOn σ (tn₁.T : Set I) (tn₁'.T : Set I))
    (hσord : ∀ x ∈ tn₁.T, ∀ y ∈ tn₁.T, (tn₁.ord x y ↔ tn₁'.ord (σ x) (σ y)))
    (hσα : ∀ x ∈ tn₁.T, tn₁.α x = tn₁'.α (σ x))
    (hρbij : Set.BijOn ρ (u.T : Set I) (u'.T : Set I))
    (hρord : ∀ x ∈ u.T, ∀ y ∈ u.T, (u.ord x y ↔ u'.ord (ρ x) (ρ y)))
    (hρα : ∀ x ∈ u.T, u.α x = u'.α (ρ x)) :
    (decomposeWith tn₁ t u).Iso (decomposeWith tn₁' (σ t) u') := by
  classical
  -- basic consequences of the hypotheses
  have hσmaps : ∀ x ∈ tn₁.T, σ x ∈ tn₁'.T := fun x hx => by
    simpa using hσbij.mapsTo (by simpa using hx)
  have hσinj : ∀ x ∈ tn₁.T, ∀ y ∈ tn₁.T, σ x = σ y → x = y := fun x hx y hy h =>
    hσbij.injOn (by simpa using hx) (by simpa using hy) h
  have hσsurj : ∀ y ∈ tn₁'.T, ∃ x ∈ tn₁.T, σ x = y := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hσbij.surjOn (by simpa using hy)
    exact ⟨x, by simpa using hx, hxy⟩
  have hρmaps : ∀ x ∈ u.T, ρ x ∈ u'.T := fun x hx => by
    simpa using hρbij.mapsTo (by simpa using hx)
  have hρinj : ∀ x ∈ u.T, ∀ y ∈ u.T, ρ x = ρ y → x = y := fun x hx y hy h =>
    hρbij.injOn (by simpa using hx) (by simpa using hy) h
  have hρsurj : ∀ y ∈ u'.T, ∃ x ∈ u.T, ρ x = y := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hρbij.surjOn (by simpa using hy)
    exact ⟨x, by simpa using hx, hxy⟩
  have hnot : ∀ x ∈ tn₁.T, x ∉ u.T := fun x hx => Finset.disjoint_left.1 hdisj hx
  have hnot' : ∀ x ∈ tn₁'.T, x ∉ u'.T := fun x hx => Finset.disjoint_left.1 hdisj' hx
  have hnotu : ∀ x ∈ u.T, x ∉ tn₁.T := fun x hx hc => hnot x hc hx
  have hnotu' : ∀ x ∈ u'.T, x ∉ tn₁'.T := fun x hx hc => hnot' x hc hx
  have hσt : σ t ∈ tn₁'.T := hσmaps t ht
  -- membership in the decomposed networks
  have hmem : ∀ x : I, x ∈ ((decomposeWith tn₁ t u).T : Set I) ↔ (x ∈ tn₁.T ∧ x ≠ t) ∨ x ∈ u.T :=
    fun x => by rw [Finset.mem_coe]; exact mem_decomposeWith_T
  have hmem' : ∀ x : I, x ∈ ((decomposeWith tn₁' (σ t) u').T : Set I) ↔
      (x ∈ tn₁'.T ∧ x ≠ σ t) ∨ x ∈ u'.T :=
    fun x => by rw [Finset.mem_coe]; exact mem_decomposeWith_T
  -- the combined renaming
  set φ : I → I := fun x => if x ∈ u.T then ρ x else σ x with hφdef
  have hφold : ∀ x ∈ tn₁.T, φ x = σ x := fun x hx => by simp [hφdef, hnot x hx]
  have hφnew : ∀ x ∈ u.T, φ x = ρ x := fun x hx => by simp [hφdef, hx]
  have hσne : ∀ x ∈ tn₁.T, x ≠ t → σ x ≠ σ t := fun x hx hxt hc => hxt (hσinj x hx t ht hc)
  refine ⟨φ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- maps to
    intro x hx
    rcases (hmem x).1 hx with ⟨hxT, hxt⟩ | hxu
    · rw [hφold x hxT]
      exact (hmem' _).2 (Or.inl ⟨hσmaps x hxT, hσne x hxT hxt⟩)
    · rw [hφnew x hxu]
      exact (hmem' _).2 (Or.inr (hρmaps x hxu))
  · -- injective on
    intro x hx y hy hxy
    rcases (hmem x).1 hx with ⟨hxT, -⟩ | hxu <;> rcases (hmem y).1 hy with ⟨hyT, -⟩ | hyu
    · rw [hφold x hxT, hφold y hyT] at hxy
      exact hσinj x hxT y hyT hxy
    · rw [hφold x hxT, hφnew y hyu] at hxy
      exact absurd (hxy ▸ hσmaps x hxT) (hnotu' (ρ y) (hρmaps y hyu))
    · rw [hφnew x hxu, hφold y hyT] at hxy
      exact absurd (hxy ▸ hρmaps x hxu) (hnot' (σ y) (hσmaps y hyT))
    · rw [hφnew x hxu, hφnew y hyu] at hxy
      exact hρinj x hxu y hyu hxy
  · -- surjective on
    intro y hy
    rcases (hmem' y).1 hy with ⟨hyT, hyt⟩ | hyu
    · obtain ⟨x, hxT, rfl⟩ := hσsurj y hyT
      have hxt : x ≠ t := fun hc => hyt (by rw [hc])
      exact ⟨x, (hmem x).2 (Or.inl ⟨hxT, hxt⟩), hφold x hxT⟩
    · obtain ⟨x, hxu, rfl⟩ := hρsurj y hyu
      exact ⟨x, (hmem x).2 (Or.inr hxu), hφnew x hxu⟩
  · -- the orderings correspond
    intro x hx y hy
    rcases mem_decomposeWith_T.1 hx with ⟨hxT, hxt⟩ | hxu <;>
      rcases mem_decomposeWith_T.1 hy with ⟨hyT, hyt⟩ | hyu
    · rw [hφold x hxT, hφold y hyT,
        decomposeWith_ord_old_old hu hdisj hxT hxt hyT hyt,
        decomposeWith_ord_old_old hu' hdisj' (hσmaps x hxT) (hσne x hxT hxt)
          (hσmaps y hyT) (hσne y hyT hyt)]
      exact hσord x hxT y hyT
    · rw [hφold x hxT, hφnew y hyu,
        decomposeWith_ord_old_new h₁ hu hdisj hxT hyu,
        decomposeWith_ord_old_new h₁' hu' hdisj' (hσmaps x hxT) (hρmaps y hyu)]
      exact hσord x hxT t ht
    · rw [hφnew x hxu, hφold y hyT,
        decomposeWith_ord_new_old h₁ hu hdisj hxu hyT,
        decomposeWith_ord_new_old h₁' hu' hdisj' (hρmaps x hxu) (hσmaps y hyT)]
      exact hσord t ht y hyT
    · rw [hφnew x hxu, hφnew y hyu,
        decomposeWith_ord_new_new h₁ hdisj hxu hyu,
        decomposeWith_ord_new_new h₁' hdisj' (hρmaps x hxu) (hρmaps y hyu)]
      exact hρord x hxu y hyu
  · -- the labellings correspond
    intro x hx
    rcases mem_decomposeWith_T.1 hx with ⟨hxT, -⟩ | hxu
    · rw [hφold x hxT]
      simp only [decomposeWith_α, if_neg (hnot x hxT), if_neg (hnot' (σ x) (hσmaps x hxT))]
      exact hσα x hxT
    · rw [hφnew x hxu]
      simp only [decomposeWith_α, if_pos hxu, if_pos (hρmaps x hxu)]
      exact hρα x hxu

/-- **A decomposition step can be replayed on an isomorphic task network.** -/
theorem DecompStep.iso [DecidableEq I] [Infinite I] {M : Set (Method I A C)}
    {tn₁ tn₁' tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    (hstep : DecompStep M tn₁ t m tn₂) (h₁ : tn₁.WF) (h₁' : tn₁'.WF) (hiso : tn₁.Iso tn₁') :
    ∃ (t' : I) (tn₂' : TaskNetwork I A C), DecompStep M tn₁' t' m tn₂' ∧ tn₂.Iso tn₂' := by
  classical
  obtain ⟨hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hstep
  obtain ⟨σ, hσbij, hσord, hσα⟩ := hiso
  have hσmaps : ∀ x ∈ tn₁.T, σ x ∈ tn₁'.T := fun x hx => by
    simpa using hσbij.mapsTo (by simpa using hx)
  -- a fresh copy of `u` for `tn₁'`
  obtain ⟨u', hu', hu'iso, hdisj'⟩ := TaskNetwork.exists_fresh_iso_copy u hu tn₁'.T
  obtain ⟨ρ, hρbij, hρord, hρα⟩ := hu'iso.symm
  refine ⟨σ t, decomposeWith tn₁' (σ t) u', ⟨hmM, hσmaps t htT, ?_, u', hu',
    hu'iso.trans huiso, hdisj', rfl⟩, ?_⟩
  · rw [← hσα t htT]; exact hαt
  · exact decomposeWith_iso_congr h₁ h₁' hu hu' hdisj hdisj' htT hσbij hσord hσα
      hρbij hρord hρα

/-- **A decomposition sequence can be replayed on an isomorphic task network.** -/
theorem DecomposesTo.iso [DecidableEq I] [Infinite I] {M : Set (Method I A C)}
    {tn₁ tn₂ : TaskNetwork I A C} (h : DecomposesTo M tn₁ tn₂) (h₁ : tn₁.WF) :
    ∀ {tn₁' : TaskNetwork I A C}, tn₁'.WF → tn₁.Iso tn₁' →
      ∃ tn₂' : TaskNetwork I A C, DecomposesTo M tn₁' tn₂' ∧ tn₂.Iso tn₂' := by
  induction h with
  | refl => exact fun {tn₁'} _ hiso => ⟨tn₁', Relation.ReflTransGen.refl, hiso⟩
  | @tail b c hab hbc ih =>
    intro tn₁' hwf₁' hiso
    obtain ⟨b', hb', hbiso⟩ := ih hwf₁' hiso
    obtain ⟨t, m, hstep⟩ := hbc
    have hbwf : b.WF := HTN.DecomposesTo.wf hab h₁
    have hb'wf : b'.WF := HTN.DecomposesTo.wf hb' hwf₁'
    obtain ⟨t', c', hstep', hciso⟩ := hstep.iso hbwf hb'wf hbiso
    exact ⟨c', Relation.ReflTransGen.tail hb' ⟨t', m, hstep'⟩, hciso⟩

end HTN
