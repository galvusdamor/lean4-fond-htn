import FondHtn.MethodPolicies
import HtnPlanning.Core.DecompositionIso
/-!
# Isomorphisms with explicit renamings

Lemmas about `HTN.TaskNetwork.IsoVia σ tn tn'` (an isomorphism given by an explicit renaming `σ`):
inverses, composition, and transport of unconstrained tasks, progression and decomposition.
-/

namespace HTN

namespace TaskNetwork

universe v w x

variable {I : Type x} {A : Type v} {C : Type w}

namespace IsoVia

variable {σ τ : I → I} {tn tn' tn'' : TaskNetwork I A C}

lemma mem (h : IsoVia σ tn tn') {t : I} (ht : t ∈ tn.T) : σ t ∈ tn'.T := by
  simpa using h.1.mapsTo (by simpa using ht)

lemma inj (h : IsoVia σ tn tn') {t t' : I} (ht : t ∈ tn.T) (ht' : t' ∈ tn.T)
    (he : σ t = σ t') : t = t' :=
  h.1.injOn (by simpa using ht) (by simpa using ht') he

lemma surj (h : IsoVia σ tn tn') {y : I} (hy : y ∈ tn'.T) : ∃ t ∈ tn.T, σ t = y := by
  obtain ⟨t, ht, rfl⟩ := h.1.surjOn (by simpa using hy)
  exact ⟨t, by simpa using ht, rfl⟩

lemma iso (h : IsoVia σ tn tn') : tn.Iso tn' := ⟨σ, h⟩

lemma refl (tn : TaskNetwork I A C) : IsoVia id tn tn :=
  ⟨Set.bijOn_id _, by simp, by simp⟩

lemma comp (h₁ : IsoVia σ tn tn') (h₂ : IsoVia τ tn' tn'') : IsoVia (τ ∘ σ) tn tn'' := by
  obtain ⟨σ', h⟩ := Iso.trans ⟨σ, h₁⟩ ⟨τ, h₂⟩
  refine ⟨h₂.1.comp h₁.1, fun t ht t' ht' => ?_, fun t ht => ?_⟩
  · exact (h₁.2.1 t ht t' ht').trans (h₂.2.1 _ (h₁.mem ht) _ (h₁.mem ht'))
  · exact (h₁.2.2 t ht).trans (h₂.2.2 _ (h₁.mem ht))

/-- Every isomorphism has an inverse. -/
lemma exists_inv [Nonempty I] (h : IsoVia σ tn tn') :
    ∃ τ, IsoVia τ tn' tn ∧ ∀ t ∈ tn.T, τ (σ t) = t := by
  obtain ⟨hbij, hord, hα⟩ := h
  set τ := Function.invFunOn σ (tn.T : Set I)
  have hinv : Set.InvOn τ σ (tn.T : Set I) (tn'.T : Set I) := hbij.invOn_invFunOn
  have hbij' : Set.BijOn τ (tn'.T : Set I) (tn.T : Set I) := hbij.symm hinv.symm
  have hright : ∀ t ∈ tn'.T, σ (τ t) = t := fun t ht => hinv.2 (by simpa using ht)
  have hmaps : ∀ t ∈ tn'.T, τ t ∈ tn.T := fun t ht => by
    simpa using hbij'.mapsTo (by simpa using ht)
  refine ⟨τ, ⟨hbij', fun t ht t' ht' => ?_, fun t ht => ?_⟩, fun t ht => hinv.1 (by simpa using ht)⟩
  · have := hord _ (hmaps t ht) _ (hmaps t' ht')
    rw [hright t ht, hright t' ht'] at this
    exact this.symm
  · have := hα _ (hmaps t ht)
    rw [hright t ht] at this
    exact this.symm

lemma α_eq (h : IsoVia σ tn tn') {t : I} (ht : t ∈ tn.T) : tn'.α (σ t) = tn.α t :=
  (h.2.2 t ht).symm

lemma unconstrained (h : IsoVia σ tn tn') {t : I} (hu : tn.Unconstrained t) :
    tn'.Unconstrained (σ t) := by
  refine ⟨h.mem hu.1, fun y hy hord => ?_⟩
  obtain ⟨t', ht', rfl⟩ := h.surj hy
  exact hu.2 t' ht' ((h.2.1 t' ht' t hu.1).2 hord)

lemma empty (h : IsoVia σ tn tn') (he : tn.T = ∅) : tn'.T = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro y hy
  obtain ⟨t, ht, -⟩ := h.surj hy
  simp [he] at ht

lemma progress [DecidableEq I] (h : IsoVia σ tn tn') {t : I} (ht : t ∈ tn.T) :
    IsoVia σ (tn.progress t) (tn'.progress (σ t)) := by
  have hm : ∀ {y}, y ∈ ((tn.progress t).T : Set I) → y ≠ t ∧ y ∈ tn.T := fun hy =>
    mem_progress_T.1 (Finset.mem_coe.1 hy)
  have hm' : ∀ {y}, y ∈ ((tn'.progress (σ t)).T : Set I) → y ≠ σ t ∧ y ∈ tn'.T := fun hy =>
    mem_progress_T.1 (Finset.mem_coe.1 hy)
  refine ⟨⟨fun y hy => ?_, fun y hy z hz he => ?_, fun y hy => ?_⟩, fun a ha b hb => ?_,
    fun a ha => ?_⟩
  · obtain ⟨hyt, hyT⟩ := hm hy
    exact Finset.mem_coe.2 (mem_progress_T.2 ⟨fun he => hyt (h.inj hyT ht he), h.mem hyT⟩)
  · exact h.inj (hm hy).2 (hm hz).2 he
  · obtain ⟨hyt, hyT⟩ := hm' hy
    obtain ⟨z, hz, rfl⟩ := h.surj hyT
    refine ⟨z, Finset.mem_coe.2 (mem_progress_T.2 ⟨fun he => hyt (by rw [he]), hz⟩), rfl⟩
  · have ha' := mem_progress_T.1 ha
    have hb' : b ∈ tn.T := (mem_progress_T.1 hb).2
    simp only [progress_ord, h.2.1 a ha'.2 b hb']
    exact and_congr_right fun _ => ⟨fun hne he => hne (h.inj ha'.2 ht he), fun hne he =>
      hne (by rw [he])⟩
  · exact h.2.2 a (mem_progress_T.1 ha).2

end IsoVia

end TaskNetwork

open TaskNetwork

variable {I : Type x} {A : Type v} {C : Type w}

/-- A decomposition step can be replayed along an explicit isomorphism. -/
theorem DecompStep.isoVia [DecidableEq I] [Infinite I] {M : Set (Method I A C)}
    {tn₁ tn₁' tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C} {σ : I → I}
    (hstep : DecompStep M tn₁ t m tn₂) (h₁ : tn₁.WF) (h₁' : tn₁'.WF) (hσ : IsoVia σ tn₁ tn₁') :
    ∃ tn₂' : TaskNetwork I A C, DecompStep M tn₁' (σ t) m tn₂' ∧ tn₂.Iso tn₂' := by
  classical
  obtain ⟨hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hstep
  obtain ⟨u', hu', hu'iso, hdisj'⟩ := TaskNetwork.exists_fresh_iso_copy u hu tn₁'.T
  obtain ⟨ρ, hρbij, hρord, hρα⟩ := hu'iso.symm
  refine ⟨decomposeWith tn₁' (σ t) u', ⟨hmM, hσ.mem htT, ?_, u', hu', hu'iso.trans huiso,
    hdisj', rfl⟩, ?_⟩
  · rw [hσ.α_eq htT]; exact hαt
  · exact decomposeWith_iso_congr h₁ h₁' hu hu' hdisj hdisj' htT hσ.1 hσ.2.1 hσ.2.2
      hρbij hρord hρα

/-- Decomposing corresponding tasks of isomorphic networks with the same method gives isomorphic
results. -/
theorem DecompStep.iso_of_isoVia [DecidableEq I] [Nonempty I] {M : Set (Method I A C)}
    {tn₁ tn₁' tn₂ tn₂' : TaskNetwork I A C} {t : I} {m m' : Method I A C} {σ : I → I}
    (hstep : DecompStep M tn₁ t m tn₂) (hstep' : DecompStep M tn₁' (σ t) m' tn₂')
    (hm : m = m') (h₁ : tn₁.WF) (h₁' : tn₁'.WF) (hσ : IsoVia σ tn₁ tn₁') : tn₂.Iso tn₂' := by
  subst hm
  obtain ⟨-, htT, -, u, hu, huiso, hdisj, rfl⟩ := hstep
  obtain ⟨-, -, -, u', hu', hu'iso, hdisj', rfl⟩ := hstep'
  obtain ⟨ρ, hρbij, hρord, hρα⟩ := huiso.trans hu'iso.symm
  exact decomposeWith_iso_congr h₁ h₁' hu hu' hdisj hdisj' htT hσ.1 hσ.2.1 hσ.2.2
    hρbij hρord hρα

end HTN

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace MPNode

lemma Iso.refl (x : MPNode F A C I) : x.Iso x := ⟨rfl, HTN.TaskNetwork.Iso.refl _⟩

lemma Iso.symm [Nonempty I] {x y : MPNode F A C I} (h : x.Iso y) : y.Iso x :=
  ⟨h.1.symm, h.2.symm⟩

lemma Iso.trans {x y z : MPNode F A C I} (h₁ : x.Iso y) (h₂ : y.Iso z) : x.Iso z :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

end MPNode

namespace Problem

variable {P : Problem F A C I} [DecidableEq I]

/-- Steps preserve well-formedness. -/
lemma MPStep.wf {π : MPPolicy F A C I} {x y : MPNode F A C I} (h : P.MPStep π x y)
    (hx : x.net.WF) : y.net.WF := by
  cases h with
  | prim _ hu _ _ _ => exact HTN.TaskNetwork.progress_wf hx hu
  | decomp _ hd => exact hd.wf hx

lemma MPStep.wf_star {π : MPPolicy F A C I} {x y : MPNode F A C I}
    (h : Relation.ReflTransGen (P.MPStep π) x y) (hx : x.net.WF) : y.net.WF := by
  induction h with
  | refl => exact hx
  | tail _ hs ih => exact hs.wf ih

lemma mpReach_wf (hP : P.tnI.WF) {π : MPPolicy F A C I} {x : MPNode F A C I}
    (h : P.MPReach π x) : x.net.WF := MPStep.wf_star h hP

/-- **Simulation.** Steps can be replayed at isomorphic nodes. -/
theorem MPStep.sim [Infinite I] {π : MPPolicy F A C I} {x x' y : MPNode F A C I}
    (hs : P.MPStep π x y) (hx : x.net.WF) (hx' : x'.net.WF) (hiso : x.Iso x') :
    ∃ y', P.MPStep π x' y' ∧ y.Iso y' := by
  obtain ⟨hst, τ, hτ⟩ := hiso
  replace hτ : IsoVia τ x.net x'.net := hτ
  cases hs with
  | @prim t a s' hi hu hα happ hs' =>
    obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, rfl⟩ := hi
    refine ⟨⟨x'.net.progress (τ (σ t₀)), s'⟩, ?_, rfl, τ, hτ.progress hu.1⟩
    refine MPStep.prim ⟨tn₀, τ ∘ σ, t₀, hσ.comp hτ, ht₀, hst ▸ hπ, rfl⟩ (hτ.unconstrained hu)
      ((hτ.α_eq hu.1).trans hα) (hst ▸ happ) (hst ▸ hs')
  | @decomp t m tn' hi hd =>
    obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, rfl⟩ := hi
    obtain ⟨u', hd', hiso'⟩ := hd.isoVia hx hx' hτ
    exact ⟨⟨u', x'.state⟩, MPStep.decomp ⟨tn₀, τ ∘ σ, t₀, hσ.comp hτ, ht₀, hst ▸ hπ, rfl⟩ hd',
      hst, hiso'⟩

theorem MPStep.sim_star [Infinite I] {π : MPPolicy F A C I} {x x' y : MPNode F A C I}
    (hs : Relation.ReflTransGen (P.MPStep π) x y) (hx : x.net.WF) (hx' : x'.net.WF)
    (hiso : x.Iso x') :
    ∃ y', Relation.ReflTransGen (P.MPStep π) x' y' ∧ y.Iso y' := by
  induction hs with
  | refl => exact ⟨x', .refl, hiso⟩
  | @tail b c hab hbc ih =>
    obtain ⟨b', hb', hbb'⟩ := ih
    obtain ⟨c', hc', hcc'⟩ := hbc.sim (MPStep.wf_star hab hx) (MPStep.wf_star hb' hx') hbb'
    exact ⟨c', hb'.tail hc', hcc'⟩

end Problem

end FOND
