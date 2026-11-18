import HtnPlanning.Core.Classical
import HtnPlanning.Basic
/-!
# Task networks

This file formalises task networks as used in the HTN formalism of Geier and Bercher (2011)
in the presentation of

  D. Höller, P. Bercher, G. Behnke, S. Biundo,
  *HTN Planning as Heuristic Progression Search*, JAIR 67 (2020), Section 3.2.

A task network is a triple `tn = (T, ≺, α)` where

* `T` is a (possibly empty, finite) set of *task identifiers* (ids),
* `α : T → A ∪ C` maps ids to task names, either primitive (`A`) or abstract (`C`),
* `≺ ⊆ T × T` is a strict partial order on the ids.

Here ids are drawn from an ambient type `I`, `T` is a `Finset I`, `α` is a total function
`I → A ⊕ C` (only its values on `T` matter) and `≺` is a relation `I → I → Prop` (again only
its restriction to `T` matters).  The disjointness requirement `C ∩ A = ∅` of the paper is
built into the use of the sum type `A ⊕ C`.

The predicate `TaskNetwork.WF` collects the requirements on `≺` (a strict partial order
supported on `T`), and `TaskNetwork.Iso` is the isomorphism `tn ≅ tn'` of the paper
("two task networks that differ only in their identifiers").

The main results of this file are

* `TaskNetwork.Iso` is an equivalence relation (`TaskNetwork.Iso.refl/symm/trans`);
* every well-formed task network admits a linearization (`TaskNetwork.exists_linearization`),
  i.e. the executability criterion for solutions is never vacuous for ordering reasons;
* linearizations and their induced action sequences are invariant under isomorphism
  (`TaskNetwork.Iso.exists_linearization_actionSeq_iff`).
-/

namespace HTN

universe u v w

namespace TaskNetwork

variable {I : Type u} {A : Type v} {C : Type w}

lemma WF.asymm {tn : TaskNetwork I A C} (h : tn.WF) {a b : I}
    (hab : tn.ord a b) (hba : tn.ord b a) : False :=
  h.irrefl a (h.trans hab hba)

/-- **Task networks are determined by their three components.** -/
lemma ext' {tn tn' : TaskNetwork I A C} (hT : tn.T = tn'.T) (ho : tn.ord = tn'.ord)
    (hα : tn.α = tn'.α) : tn = tn' := by
  cases tn
  cases tn'
  simp only at hT ho hα
  subst hT; subst ho; subst hα
  rfl

/-- The empty task network. -/
def empty (A : Type v) (C : Type w) [Inhabited A] : TaskNetwork I A C where
  T := ∅
  ord := fun _ _ => False
  α := fun _ => Sum.inl default

lemma empty_wf [Inhabited A] : (empty (I := I) A C).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

/-! ### Primitive and abstract tasks -/

/-! ### Unconstrained tasks (Definition 2 of the paper) -/

/-- A task id `t` is *unconstrained* in a task network iff it belongs to the network and there
is no `t' ∈ T` with `(t', t) ∈ ≺`. -/
def Unconstrained (tn : TaskNetwork I A C) (t : I) : Prop :=
  t ∈ tn.T ∧ ∀ t' ∈ tn.T, ¬ tn.ord t' t

/-! ### Isomorphism of task networks -/

@[refl] lemma Iso.refl (tn : TaskNetwork I A C) : tn.Iso tn :=
  ⟨id, Set.bijOn_id _, by simp, by simp⟩

lemma Iso.symm [Nonempty I] {tn tn' : TaskNetwork I A C} (h : tn.Iso tn') : tn'.Iso tn := by
  obtain ⟨σ, hbij, hord, hα⟩ := h
  set τ := Function.invFunOn σ (tn.T : Set I) with hτdef
  have hinv : Set.InvOn τ σ (tn.T : Set I) (tn'.T : Set I) := hbij.invOn_invFunOn
  have hbij' : Set.BijOn τ (tn'.T : Set I) (tn.T : Set I) := hbij.symm hinv.symm
  have hright : ∀ t ∈ tn'.T, σ (τ t) = t := fun t ht => hinv.2 (by simpa using ht)
  have hmaps : ∀ t ∈ tn'.T, τ t ∈ tn.T := fun t ht => by
    simpa using hbij'.mapsTo (by simpa using ht)
  refine ⟨τ, hbij', ?_, ?_⟩
  · intro t ht t' ht'
    have := hord _ (hmaps t ht) _ (hmaps t' ht')
    rw [hright t ht, hright t' ht'] at this
    exact this.symm
  · intro t ht
    have := hα _ (hmaps t ht)
    rw [hright t ht] at this
    exact this.symm

lemma Iso.trans {tn₁ tn₂ tn₃ : TaskNetwork I A C} (h₁ : tn₁.Iso tn₂) (h₂ : tn₂.Iso tn₃) :
    tn₁.Iso tn₃ := by
  obtain ⟨σ, hbij, hord, hα⟩ := h₁
  obtain ⟨τ, hbij', hord', hα'⟩ := h₂
  refine ⟨τ ∘ σ, hbij'.comp hbij, ?_, ?_⟩
  · intro t ht t' ht'
    have hst : σ t ∈ tn₂.T := by simpa using hbij.mapsTo (by simpa using ht)
    have hst' : σ t' ∈ tn₂.T := by simpa using hbij.mapsTo (by simpa using ht')
    exact (hord t ht t' ht').trans (hord' _ hst _ hst')
  · intro t ht
    have hst : σ t ∈ tn₂.T := by simpa using hbij.mapsTo (by simpa using ht)
    exact (hα t ht).trans (hα' _ hst)

/-- Isomorphic task networks have the same number of tasks. -/
lemma Iso.card_eq {tn tn' : TaskNetwork I A C} (h : tn.Iso tn') : tn.T.card = tn'.T.card := by
  obtain ⟨σ, hbij, _, _⟩ := h
  have := Set.BijOn.image_eq hbij
  classical
  have himg : tn.T.image σ = tn'.T := by
    apply Finset.coe_injective
    simpa using this
  rw [← himg, Finset.card_image_of_injOn hbij.injOn]

/-- Isomorphism preserves well-formedness of the ordering *restricted to the networks*:
if `tn` is well formed and `tn ≅ tn'`, then the order of `tn'` is irreflexive and transitive
on `tn'.T`. -/
lemma Iso.irrefl_of_wf {tn tn' : TaskNetwork I A C} (h : tn.Iso tn') (hwf : tn.WF)
    {t : I} (ht : t ∈ tn'.T) : ¬ tn'.ord t t := by
  obtain ⟨σ, hbij, hord, _⟩ := h
  obtain ⟨s, hs, rfl⟩ := hbij.surjOn (by simpa using ht)
  have hsT : s ∈ tn.T := by simpa using hs
  intro hcon
  exact hwf.irrefl s ((hord s hsT s hsT).2 hcon)

/-! ### Linearizations -/

lemma isActionSeq_unique {tn : TaskNetwork I A C} {l : List I} {as bs : List A}
    (h₁ : tn.IsActionSeq l as) (h₂ : tn.IsActionSeq l bs) : as = bs := by
  have : as.map (Sum.inl (β := C)) = bs.map Sum.inl := h₁ ▸ h₂
  exact List.map_injective_iff.2 (fun _ _ h => Sum.inl_injective h) this

/-- Any list of primitive ids induces an action sequence. -/
lemma exists_actionSeq {tn : TaskNetwork I A C} {l : List I}
    (h : ∀ t ∈ l, tn.IsPrimitiveId t) : ∃ as : List A, tn.IsActionSeq l as := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons t l ih =>
    obtain ⟨a, ha⟩ := h t (by simp)
    obtain ⟨as, has⟩ := ih (fun s hs => h s (by simp [hs]))
    refine ⟨a :: as, ?_⟩
    have has' : l.map tn.α = as.map Sum.inl := has
    simp only [IsActionSeq, List.map_cons, ha, has']

/-- **Existence of a minimal element.** A nonempty finite set carrying an irreflexive and
transitive relation has an element with no predecessor in the set. -/
lemma exists_minimal_of_finset {r : I → I → Prop} (hirr : ∀ a, ¬ r a a)
    (htr : ∀ {a b c}, r a b → r b c → r a c) :
    ∀ (T : Finset I), T.Nonempty → ∃ t ∈ T, ∀ t' ∈ T, ¬ r t' t := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro hne
    obtain ⟨x, hx⟩ := hne
    by_cases hpred : ∃ y ∈ T, r y x
    · set S : Finset I := T.filter (fun y => r y x) with hS
      have hSsub : S ⊂ T := by
        refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨x, hx, ?_⟩
        simp [hirr x]
      have hSne : S.Nonempty := by
        obtain ⟨y, hy, hyx⟩ := hpred
        exact ⟨y, by simp [hS, hy, hyx]⟩
      obtain ⟨m, hm, hmin⟩ := ih S hSsub hSne
      have hmT : m ∈ T := (Finset.filter_subset _ _) hm
      have hmx : r m x := by simpa [hS] using (Finset.mem_filter.1 hm).2
      refine ⟨m, hmT, ?_⟩
      intro y hy hym
      have : y ∈ S := by simp [hS, hy, htr hym hmx]
      exact hmin y this hym
    · push_neg at hpred
      exact ⟨x, hx, fun y hy => hpred y hy⟩

/-- **Topological sort.** A finite set with an irreflexive transitive relation can be
enumerated in a way that is in line with the relation. -/
lemma exists_topSort {r : I → I → Prop} (hirr : ∀ a, ¬ r a a)
    (htr : ∀ {a b c}, r a b → r b c → r a c) :
    ∀ (T : Finset I), ∃ l : List I,
      l.Nodup ∧ (∀ t, t ∈ l ↔ t ∈ T) ∧ l.Pairwise (fun a b => ¬ r b a) := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], by simp, by simp, by simp⟩
    · obtain ⟨t, htT, hmin⟩ := exists_minimal_of_finset hirr htr T hne
      have hsub : T.erase t ⊂ T := Finset.erase_ssubset htT
      obtain ⟨l, hnodup, hmem, hpair⟩ := ih (T.erase t) hsub
      refine ⟨t :: l, ?_, ?_, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, hnodup⟩
        intro hcon
        have := (hmem t).1 hcon
        simp at this
      · intro s
        constructor
        · intro hs
          rcases List.mem_cons.1 hs with rfl | hs
          · exact htT
          · exact Finset.mem_of_mem_erase ((hmem s).1 hs)
        · intro hs
          by_cases hst : s = t
          · simp [hst]
          · exact List.mem_cons.2 (Or.inr ((hmem s).2 (Finset.mem_erase.2 ⟨hst, hs⟩)))
      · refine List.pairwise_cons.2 ⟨?_, hpair⟩
        intro b hb
        exact hmin b (Finset.mem_of_mem_erase ((hmem b).1 hb))

/-- **Every well-formed task network has a linearization.** -/
lemma exists_linearization {tn : TaskNetwork I A C} (hwf : tn.WF) :
    ∃ l : List I, tn.IsLinearization l :=
  exists_topSort hwf.irrefl hwf.trans tn.T

/-- A primitive well-formed task network has a linearization together with its induced
action sequence. -/
lemma exists_linearization_actionSeq {tn : TaskNetwork I A C} (hwf : tn.WF)
    (hprim : tn.IsPrimitive) :
    ∃ (l : List I) (as : List A), tn.IsLinearization l ∧ tn.IsActionSeq l as := by
  obtain ⟨l, hl⟩ := exists_linearization hwf
  obtain ⟨as, has⟩ := exists_actionSeq (fun t ht => hprim t ((hl.2.1 t).1 ht))
  exact ⟨l, as, hl, has⟩

/-! ### Invariance of linearizations under isomorphism -/

/-- If `tn ≅ tn'` via `σ` and `l` is a linearization of `tn` with action sequence `as`, then
`l.map σ` is a linearization of `tn'` with the same action sequence. -/
lemma Iso.map_isLinearization {tn tn' : TaskNetwork I A C} {σ : I → I}
    (hbij : Set.BijOn σ (tn.T : Set I) (tn'.T : Set I))
    (hord : ∀ t ∈ tn.T, ∀ t' ∈ tn.T, (tn.ord t t' ↔ tn'.ord (σ t) (σ t')))
    (hα : ∀ t ∈ tn.T, tn.α t = tn'.α (σ t))
    {l : List I} (hl : tn.IsLinearization l) :
    tn'.IsLinearization (l.map σ) ∧ ∀ as, tn.IsActionSeq l as → tn'.IsActionSeq (l.map σ) as := by
  obtain ⟨hnodup, hmem, hpair⟩ := hl
  have hmemT : ∀ t ∈ l, t ∈ tn.T := fun t ht => (hmem t).1 ht
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · refine List.Nodup.map_on ?_ hnodup
    intro x hx y hy hxy
    exact hbij.injOn (by simpa using hmemT x hx) (by simpa using hmemT y hy) hxy
  · intro t
    constructor
    · rintro ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      simpa using hbij.mapsTo (by simpa using hmemT s hs)
    · intro ht
      obtain ⟨s, hs, hseq⟩ := hbij.surjOn (by simpa using ht)
      exact List.mem_map.2 ⟨s, (hmem s).2 (by simpa using hs), hseq⟩
  · refine List.Pairwise.map _ ?_ (List.Pairwise.and_mem.1 hpair)
    intro a b hab
    obtain ⟨ha, hb, hnord⟩ := hab
    intro hcon
    exact hnord ((hord b (hmemT b hb) a (hmemT a ha)).2 hcon)
  · intro as has
    have : (l.map σ).map tn'.α = l.map tn.α := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro t ht
      exact (hα t (hmemT t ht)).symm
    rw [IsActionSeq, this]
    exact has

/-- Isomorphic task networks admit exactly the same action sequences of linearizations. -/
lemma Iso.exists_linearization_actionSeq_iff [Nonempty I] {tn tn' : TaskNetwork I A C}
    (h : tn.Iso tn') (as : List A) :
    (∃ l, tn.IsLinearization l ∧ tn.IsActionSeq l as) ↔
      (∃ l, tn'.IsLinearization l ∧ tn'.IsActionSeq l as) := by
  constructor
  · rintro ⟨l, hl, has⟩
    obtain ⟨σ, hbij, hord, hα⟩ := h
    obtain ⟨h1, h2⟩ := Iso.map_isLinearization hbij hord hα hl
    exact ⟨l.map σ, h1, h2 as has⟩
  · rintro ⟨l, hl, has⟩
    obtain ⟨σ, hbij, hord, hα⟩ := h.symm
    obtain ⟨h1, h2⟩ := Iso.map_isLinearization hbij hord hα hl
    exact ⟨l.map σ, h1, h2 as has⟩

/-! ### Existence of fresh isomorphic copies

Decomposition replaces a task by a *fresh* copy of the subtask network of a method, i.e. by an
isomorphic task network whose identifiers do not occur in the network being decomposed.  The
following theorem shows that such a fresh copy always exists as soon as there is an infinite
supply of identifiers, so that the decomposition relation is never vacuous. -/

/-- **Fresh copies exist.** For every well-formed task network `tn` and every finite set `S` of
identifiers there is a well-formed task network isomorphic to `tn` whose identifiers avoid
`S`. -/
theorem exists_fresh_iso_copy [DecidableEq I] [Infinite I] (tn : TaskNetwork I A C)
    (hwf : tn.WF) (S : Finset I) :
    ∃ tn' : TaskNetwork I A C, tn'.WF ∧ tn'.Iso tn ∧ Disjoint S tn'.T := by
  classical
  have hfin : ((S ∪ tn.T : Finset I) : Set I).Finite := (S ∪ tn.T).finite_toSet
  obtain ⟨Fresh, hsub, hcard⟩ := hfin.infinite_compl.exists_subset_card_eq tn.T.card
  have hFreshMem : ∀ x ∈ Fresh, x ∉ S ∧ x ∉ tn.T := by
    intro x hx
    have := hsub (by simpa using hx)
    simp only [Set.mem_compl_iff, Finset.coe_union, Set.mem_union, Finset.mem_coe] at this
    exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩
  -- a bijection between the fresh identifiers and the identifiers of `tn`
  let e : ↑Fresh ≃ ↑tn.T := Finset.equivOfCardEq hcard
  let τ : I → I := fun a => if h : a ∈ Fresh then (e ⟨a, h⟩ : ↑tn.T) else Classical.arbitrary I
  have hτmem : ∀ a (h : a ∈ Fresh), τ a = (e ⟨a, h⟩ : ↑tn.T) := by
    intro a h; simp [τ, h]
  have hbij : Set.BijOn τ (Fresh : Set I) (tn.T : Set I) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have ha' : a ∈ Fresh := by simpa using ha
      rw [hτmem a ha']
      simp
    · intro a ha b hb hab
      have ha' : a ∈ Fresh := by simpa using ha
      have hb' : b ∈ Fresh := by simpa using hb
      rw [hτmem a ha', hτmem b hb'] at hab
      have : (e ⟨a, ha'⟩) = (e ⟨b, hb'⟩) := Subtype.ext hab
      simpa using e.injective this
    · intro y hy
      have hy' : y ∈ tn.T := by simpa using hy
      refine ⟨(e.symm ⟨y, hy'⟩ : ↑Fresh), by simp, ?_⟩
      rw [hτmem _ (e.symm ⟨y, hy'⟩).2]
      simp
  refine ⟨{ T := Fresh
            ord := fun a b => a ∈ Fresh ∧ b ∈ Fresh ∧ tn.ord (τ a) (τ b)
            α := fun a => tn.α (τ a) }, ?_, ?_, ?_⟩
  · constructor
    · rintro a b ⟨ha, -, -⟩; exact ha
    · rintro a b ⟨-, hb, -⟩; exact hb
    · rintro a ⟨-, -, h⟩; exact hwf.irrefl _ h
    · rintro a b c ⟨ha, -, hab⟩ ⟨-, hc, hbc⟩
      exact ⟨ha, hc, hwf.trans hab hbc⟩
  · exact ⟨τ, hbij, by intro t ht t' ht'; simp [ht, ht'], by intro t _; rfl⟩
  · refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    exact (hFreshMem x hx').1 hx

end TaskNetwork

end HTN
