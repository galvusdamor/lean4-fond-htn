import FondHtn.IsoLemmas
/-!
# Replaying decompositions away from given ids; appending a last task

* `HTN.decomposesTo_avoid` — every decomposition sequence can be replayed, up to isomorphism of
  the result, such that no intermediate network uses an id of a given finite set `S`.
* `HTN.TaskNetwork.appendLast tn i a` — `tn` with a new primitive task `i ↦ a` after all tasks.
  Decomposition commutes with it (`decomposeWith_appendLast`), so decompositions of `tn` that
  avoid `i` lift to the extended network (`decomposesTo_appendLast`), and every decomposition of
  the extended network comes from one of `tn` (`decomposesTo_of_appendLast`).
* Linearisations of `appendLast tn i a` are those of `tn` followed by `i`
  (`isLinearization_appendLast_iff`).
-/

namespace HTN

universe v w x

variable {I : Type x} {A : Type v} {C : Type w} [DecidableEq I]

open TaskNetwork

/-! ## Replaying decompositions away from a finite set of ids -/

/-- A decomposition step whose result avoids the ids in `S`. -/
def StepAvoid (M : Set (Method I A C)) (S : Finset I) (tn₁ tn₂ : TaskNetwork I A C) : Prop :=
  DecompStep' M tn₁ tn₂ ∧ Disjoint S tn₂.T

theorem decomposesTo_avoid [Infinite I] {M : Set (Method I A C)} {tn₁ tn₂ : TaskNetwork I A C}
    (h : DecomposesTo M tn₁ tn₂) (hwf : tn₁.WF) (S : Finset I) (hS : Disjoint S tn₁.T) :
    ∃ tn₂' σ, Relation.ReflTransGen (StepAvoid M S) tn₁ tn₂' ∧ IsoVia σ tn₂ tn₂' ∧
      tn₂'.WF ∧ Disjoint S tn₂'.T := by
  induction h with
  | refl => exact ⟨tn₁, id, .refl, IsoVia.refl _, hwf, hS⟩
  | @tail b c hab hbc ih =>
    obtain ⟨b', σ, hb', hσ, hb'wf, hSb'⟩ := ih
    obtain ⟨t, m, hm, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hbc
    obtain ⟨u', hu', hu'iso, hdisj'⟩ := exists_fresh_iso_copy u hu (S ∪ b'.T)
    have hd1 : Disjoint b'.T u'.T :=
      Finset.disjoint_of_subset_left Finset.subset_union_right hdisj'
    have hd2 : Disjoint S u'.T :=
      Finset.disjoint_of_subset_left Finset.subset_union_left hdisj'
    obtain ⟨ρ, hρbij, hρord, hρα⟩ := hu'iso.symm
    have hbwf : b.WF := HTN.DecomposesTo.wf hab hwf
    obtain ⟨σ', hσ'⟩ := decomposeWith_iso_congr hbwf hb'wf hu hu' hdisj hd1 htT hσ.1 hσ.2.1
      hσ.2.2 hρbij hρord hρα
    refine ⟨decomposeWith b' (σ t) u', σ', hb'.tail ⟨⟨σ t, m, hm, hσ.mem htT, ?_, u', hu',
      hu'iso.trans huiso, hd1, rfl⟩, ?_⟩, hσ', decomposeWith_wf hb'wf hu' hd1, ?_⟩
    · rw [hσ.α_eq htT]; exact hαt
    all_goals
      rw [Finset.disjoint_left]
      intro y hyS hy
      rcases mem_decomposeWith_T.1 hy with ⟨hy', -⟩ | hy'
      · exact Finset.disjoint_left.1 hSb' hyS hy'
      · exact Finset.disjoint_left.1 hd2 hyS hy'

/-! ## Appending a last task -/

namespace TaskNetwork

/-- `tn` followed by a new primitive task `i ↦ a`, ordered after all tasks of `tn`. -/
def appendLast (tn : TaskNetwork I A C) (i : I) (a : A) : TaskNetwork I A C where
  T := insert i tn.T
  ord := fun x y => (tn.ord x y ∧ x ≠ i ∧ y ≠ i) ∨ (x ∈ tn.T ∧ x ≠ i ∧ y = i)
  α := fun x => if x = i then Sum.inl a else tn.α x

variable {tn : TaskNetwork I A C} {i : I} {a : A}

lemma appendLast_wf (hwf : tn.WF) : (tn.appendLast i a).WF where
  mem_left := by
    rintro x y (⟨h, -, -⟩ | ⟨h, -, -⟩)
    · exact Finset.mem_insert_of_mem (hwf.mem_left h)
    · exact Finset.mem_insert_of_mem h
  mem_right := by
    rintro x y (⟨h, -, -⟩ | ⟨-, -, rfl⟩)
    · exact Finset.mem_insert_of_mem (hwf.mem_right h)
    · exact Finset.mem_insert_self _ _
  irrefl := by
    rintro x (⟨h, -, -⟩ | ⟨-, h1, h2⟩)
    · exact hwf.irrefl x h
    · exact h1 h2
  trans := by
    intro x y z h1 h2
    rcases h1 with ⟨h1, hx, hy⟩ | ⟨h1, hx, hy⟩ <;> rcases h2 with ⟨h2, hy', hz⟩ | ⟨h2, hy', hz⟩
    · exact Or.inl ⟨hwf.trans h1 h2, hx, hz⟩
    · exact Or.inr ⟨hwf.mem_left h1, hx, hz⟩
    · exact absurd hy hy'
    · exact absurd hy hy'

lemma decomposeWith_appendLast {u : TaskNetwork I A C} {t : I} (hwf : tn.WF) (hu : u.WF)
    (hi : i ∉ tn.T) (hiu : i ∉ u.T) (ht : t ∈ tn.T) :
    decomposeWith (tn.appendLast i a) t u = (decomposeWith tn t u).appendLast i a := by
  have hti : t ≠ i := fun h => hi (h ▸ ht)
  refine ext' ?_ ?_ ?_
  · ext x
    simp only [decomposeWith, appendLast, Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
    by_cases hx : x = i
    · subst hx; simp [hiu, Ne.symm hti]
    · simp [hx]
  · funext x y
    apply propext
    simp only [decomposeWith, appendLast, Finset.mem_union, Finset.mem_erase]
    have hu1 : ∀ {x y}, u.ord x y → x ≠ i ∧ y ≠ i := fun h =>
      ⟨fun e => hiu (e ▸ hu.mem_left h), fun e => hiu (e ▸ hu.mem_right h)⟩
    have ht1 : ∀ {x y}, tn.ord x y → x ≠ i ∧ y ≠ i := fun h =>
      ⟨fun e => hi (e ▸ hwf.mem_left h), fun e => hi (e ▸ hwf.mem_right h)⟩
    constructor
    · rintro (h | ⟨⟨h, hx, -⟩ | ⟨-, -, h⟩, hy⟩ | ⟨⟨h, -, hy⟩ | ⟨-, -, hy⟩, hx⟩ |
        ⟨⟨h, hx, hy⟩ | ⟨h, hx, hy⟩, hxt, hyt⟩)
      · exact Or.inl ⟨Or.inl h, hu1 h⟩
      · exact Or.inl ⟨Or.inr (Or.inl ⟨h, hy⟩), hx, fun e => hiu (e ▸ hy)⟩
      · exact absurd h hti
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inl ⟨h, hx⟩)), fun e => hiu (e ▸ hx), hy⟩
      · exact Or.inr ⟨Or.inr hx, fun e => hiu (e ▸ hx), hy⟩
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨h, hxt, hyt⟩)), hx, hy⟩
      · exact Or.inr ⟨Or.inl ⟨hxt, h⟩, hx, hy⟩
    · rintro (⟨h | ⟨h, hy⟩ | ⟨h, hx⟩ | ⟨h, hxt, hyt⟩, hx', hy'⟩ | ⟨hx | hx, hxi, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inl ⟨h, hx', (ht1 h).2⟩, hy⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨h, (ht1 h).1, hy'⟩, hx⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨h, hx', hy'⟩, hxt, hyt⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨hx.2, hxi, rfl⟩, hx.1, hti.symm⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨ht, hti, rfl⟩, hx⟩))
  · funext x
    simp only [decomposeWith, appendLast]
    by_cases hx : x = i
    · subst hx; simp [hiu]
    · simp [hx]

end TaskNetwork

/-- Decompositions avoiding `i` lift to the network with the last task `i ↦ a`. -/
theorem decomposesTo_appendLast {M : Set (Method I A C)} {tn₁ tn₂ : TaskNetwork I A C} {i : I}
    {a : A} (h : Relation.ReflTransGen (StepAvoid M {i}) tn₁ tn₂) (hwf : tn₁.WF)
    (hi : i ∉ tn₁.T) :
    DecomposesTo M (tn₁.appendLast i a) (tn₂.appendLast i a) ∧ tn₂.WF ∧ i ∉ tn₂.T := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hwf, hi⟩
  | @tail b c _ hbc ih =>
    obtain ⟨ih, hbwf, hib⟩ := ih
    obtain ⟨⟨t, m, hm, htT, hαt, u, hu, huiso, hdisj, rfl⟩, hic⟩ := hbc
    have hic' : i ∉ (decomposeWith b t u).T := Finset.disjoint_singleton_left.1 hic
    have hiu : i ∉ u.T := fun h => hic' (mem_decomposeWith_T.2 (Or.inr h))
    have hti : t ≠ i := fun e => hib (e ▸ htT)
    refine ⟨ih.tail ⟨t, m, hm, Finset.mem_insert_of_mem htT, ?_, u, hu, huiso, ?_,
      (decomposeWith_appendLast (a := a) hbwf hu hib hiu htT).symm⟩,
      decomposeWith_wf hbwf hu hdisj, hic'⟩
    · simp [appendLast, hti, hαt]
    · rw [Finset.disjoint_left]
      intro y hy hyu
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hiu hyu
      · exact Finset.disjoint_left.1 hdisj hy hyu

/-- Every decomposition of the network with the last task comes from one of the network. -/
theorem decomposesTo_of_appendLast {M : Set (Method I A C)} {tn₁ X : TaskNetwork I A C} {i : I}
    {a : A} (h : DecomposesTo M (tn₁.appendLast i a) X) (hwf : tn₁.WF) (hi : i ∉ tn₁.T) :
    ∃ tn₂, X = tn₂.appendLast i a ∧ DecomposesTo M tn₁ tn₂ ∧ tn₂.WF ∧ i ∉ tn₂.T := by
  induction h with
  | refl => exact ⟨tn₁, rfl, Relation.ReflTransGen.refl, hwf, hi⟩
  | @tail Y Z _ hYZ ih =>
    obtain ⟨b, rfl, hb, hbwf, hib⟩ := ih
    obtain ⟨t, m, hm, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hYZ
    have hti : t ≠ i := by
      rintro rfl; simp [appendLast] at hαt
    have htT' : t ∈ b.T := by
      rcases Finset.mem_insert.1 htT with h | h
      · exact absurd h hti
      · exact h
    have hiu : i ∉ u.T := fun h => Finset.disjoint_left.1 hdisj (Finset.mem_insert_self _ _) h
    have hdisj' : Disjoint b.T u.T :=
      Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    refine ⟨decomposeWith b t u, decomposeWith_appendLast hbwf hu hib hiu htT',
      hb.tail ⟨t, m, hm, htT', ?_, u, hu, huiso, hdisj', rfl⟩, decomposeWith_wf hbwf hu hdisj',
      fun h => ?_⟩
    · simpa [appendLast, hti] using hαt
    · rcases mem_decomposeWith_T.1 h with ⟨h, -⟩ | h
      · exact hib h
      · exact hiu h

namespace TaskNetwork

variable {tn : TaskNetwork I A C} {i : I} {a : A}

lemma isLinearization_appendLast (hl : tn.IsLinearization l) (hi : i ∉ tn.T) :
    (tn.appendLast i a).IsLinearization (l ++ [i]) := by
  obtain ⟨hnd, hmem, hpw⟩ := hl
  refine ⟨?_, fun y => ?_, ?_⟩
  · exact List.nodup_append.2 ⟨hnd, List.nodup_singleton _, by
      intro x hx y hy; simp at hy; subst hy; exact fun e => hi (e ▸ (hmem x).1 hx)⟩
  · simp [appendLast, hmem, or_comm]
  · refine List.pairwise_append.2 ⟨hpw.imp_of_mem fun {x y} hx _ h h' => ?_,
      List.pairwise_singleton _ _, ?_⟩
    · rcases h' with ⟨h', -, -⟩ | ⟨-, -, rfl⟩
      · exact h h'
      · exact hi ((hmem _).1 hx)
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> exact h rfl

lemma isLinearization_appendLast_iff (hi : i ∉ tn.T) {l' : List I} :
    (tn.appendLast i a).IsLinearization l' ↔ ∃ l, l' = l ++ [i] ∧ tn.IsLinearization l := by
  constructor
  · intro hl'
    obtain ⟨hnd, hmem, hpw⟩ := hl'
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ((hmem i).2 (Finset.mem_insert_self _ _))
    have hl₂ : l₂ = [] := by
      rcases l₂ with _ | ⟨y, l₂⟩
      · rfl
      · exfalso
        have hy : y ∈ insert i tn.T := (hmem y).1 (by simp)
        have hyi : y ≠ i := by
          intro e; subst e
          have := (List.nodup_append.1 hnd).2.1
          simp at this
        have hyT : y ∈ tn.T := by
          rcases Finset.mem_insert.1 hy with h | h
          · exact absurd h hyi
          · exact h
        have hp := (List.pairwise_append.1 hpw).2.1
        have := (List.pairwise_cons.1 hp).1 y (by simp)
        exact this (Or.inr ⟨hyT, hyi, rfl⟩)
    subst hl₂
    refine ⟨l₁, rfl, (List.nodup_append.1 hnd).1, fun y => ?_, ?_⟩
    · have := hmem y
      simp only [List.mem_append, List.mem_singleton, appendLast, Finset.mem_insert] at this
      have hni : i ∉ l₁ := by
        intro h; have := (List.nodup_append.1 hnd).2.2 i h i (by simp); exact this rfl
      constructor
      · intro hy
        rcases this.1 (Or.inl hy) with h | h
        · exact absurd (h ▸ hy) hni
        · exact h
      · intro hy
        rcases this.2 (Or.inr hy) with h | h
        · exact h
        · exact absurd (h ▸ hy) hi
    · refine (List.pairwise_append.1 hpw).1.imp_of_mem fun {x y} hx hy h hord => h ?_
      have hni : i ∉ l₁ := by
        intro h; have := (List.nodup_append.1 hnd).2.2 i h i (by simp); exact this rfl
      exact Or.inl ⟨hord, fun e => hni (e ▸ hy), fun e => hni (e ▸ hx)⟩
  · rintro ⟨l, rfl, hl⟩
    exact isLinearization_appendLast hl hi

lemma isActionSeq_appendLast_iff (hl : tn.IsLinearization l) (hi : i ∉ tn.T) {bs : List A} :
    (tn.appendLast i a).IsActionSeq (l ++ [i]) bs ↔ ∃ as, bs = as ++ [a] ∧ tn.IsActionSeq l as := by
  have hli : ∀ x ∈ l, x ≠ i := fun x hx e => hi (e ▸ (hl.2.1 x).1 hx)
  have hmap : l.map (tn.appendLast i a).α = l.map tn.α :=
    List.map_congr_left fun x hx => by simp [appendLast, hli x hx]
  unfold IsActionSeq
  rw [List.map_append, hmap]
  constructor
  · intro h
    rcases List.eq_nil_or_concat bs with rfl | ⟨as, b, rfl⟩
    · simp at h
    · rw [List.concat_eq_append, List.map_append] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
      simp [appendLast] at h2
      exact ⟨as, by simp [h2], h1⟩
  · rintro ⟨as, rfl, has⟩
    simp [has, appendLast]

end TaskNetwork

end HTN
