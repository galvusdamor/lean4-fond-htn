import HtnComplexity.HDDecide.Pieces
/-!
# Semantic lemmas for the completeness of the search on pieces

* `HTN.TaskNetwork.drop`: removing a task together with *all* the ordering constraints it is
  involved in (progression only removes the outgoing ones; for the regression of a maximal task
  the incoming ones have to go as well), and the fact that it commutes with decomposition
  sequences (`HTN.DecomposesToN.drop`);
* primitive tasks keep their mutual ordering along decomposition sequences;
* in a one-hole network, everything a decomposition sequence produces from the compound task
  lies after every predecessor and before every successor of that task
  (`HTN.DecomposesTo.ord_after`, `HTN.DecomposesTo.ord_before`).
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

namespace TaskNetwork

variable [DecidableEq I]

/-- Removing a task and all the ordering constraints it is involved in. -/
def drop (tn : TaskNetwork I A C) (t : I) : TaskNetwork I A C where
  T := tn.T.erase t
  ord := fun a b => tn.ord a b ∧ a ≠ t ∧ b ≠ t
  α := tn.α

@[simp] lemma drop_T (tn : TaskNetwork I A C) (t : I) : (tn.drop t).T = tn.T.erase t := rfl

@[simp] lemma drop_ord (tn : TaskNetwork I A C) (t a b : I) :
    (tn.drop t).ord a b ↔ (tn.ord a b ∧ a ≠ t ∧ b ≠ t) := Iff.rfl

@[simp] lemma drop_α (tn : TaskNetwork I A C) (t x : I) : (tn.drop t).α x = tn.α x := rfl

lemma drop_wf {tn : TaskNetwork I A C} (hwf : tn.WF) (t : I) : (tn.drop t).WF where
  mem_left := by
    rintro a b ⟨hab, hat, -⟩
    exact Finset.mem_erase.2 ⟨hat, hwf.mem_left hab⟩
  mem_right := by
    rintro a b ⟨hab, -, hbt⟩
    exact Finset.mem_erase.2 ⟨hbt, hwf.mem_right hab⟩
  irrefl := fun a h => hwf.irrefl a h.1
  trans := by
    rintro a b c ⟨hab, hat, -⟩ ⟨hbc, -, hct⟩
    exact ⟨hwf.trans hab hbc, hat, hct⟩

lemma IsPrimitive.drop {tn : TaskNetwork I A C} (h : tn.IsPrimitive) (t : I) :
    (tn.drop t).IsPrimitive := fun x hx => h x (Finset.mem_of_mem_erase hx)

/-- The tail of a linearization linearizes the network without its first task. -/
lemma isLinearization_drop_head {tn : TaskNetwork I A C} {h : I} {l : List I}
    (hl : tn.IsLinearization (h :: l)) : (tn.drop h).IsLinearization l := by
  obtain ⟨hnd, hmem, hpw⟩ := hl
  have hnd' := List.nodup_cons.1 hnd
  refine ⟨hnd'.2, fun t => ?_, ?_⟩
  · simp only [drop_T, Finset.mem_erase, ← hmem t, List.mem_cons]
    constructor
    · intro ht
      exact ⟨fun he => hnd'.1 (he ▸ ht), Or.inr ht⟩
    · rintro ⟨hne, rfl | ht⟩
      · exact absurd rfl hne
      · exact ht
  · exact (List.pairwise_cons.1 hpw).2.imp fun hn ho => hn ho.1

/-- The initial segment of a linearization linearizes the network without its last task. -/
lemma isLinearization_drop_last {tn : TaskNetwork I A C} {h : I} {l : List I}
    (hl : tn.IsLinearization (l ++ [h])) : (tn.drop h).IsLinearization l := by
  obtain ⟨hnd, hmem, hpw⟩ := hl
  have hnd' : l.Nodup ∧ h ∉ l := by
    rw [List.nodup_append] at hnd
    exact ⟨hnd.1, fun hh => hnd.2.2 h hh h (List.mem_singleton_self h) rfl⟩
  refine ⟨hnd'.1, fun t => ?_, ?_⟩
  · simp only [drop_T, Finset.mem_erase, ← hmem t, List.mem_append, List.mem_singleton]
    constructor
    · intro ht
      exact ⟨fun he => hnd'.2 (he ▸ ht), Or.inl ht⟩
    · rintro ⟨hne, ht | rfl⟩
      · exact ht
      · exact absurd rfl hne
  · exact (List.pairwise_append.1 hpw).1.imp fun hn ho => hn ho.1

end TaskNetwork

section Commute

variable [DecidableEq I]

/-- **Dropping a task commutes with decomposing another one.** -/
theorem drop_decomposeWith_comm {tn u : TaskNetwork I A C} {t t₁ : I}
    (hu : u.WF) (hne : t₁ ≠ t) (ht₁u : t₁ ∉ u.T) :
    (decomposeWith tn t u).drop t₁ = decomposeWith (tn.drop t₁) t u := by
  have hT : ((decomposeWith tn t u).drop t₁).T = (decomposeWith (tn.drop t₁) t u).T := by
    show (tn.T.erase t ∪ u.T).erase t₁ = ((tn.T.erase t₁).erase t ∪ u.T)
    ext x
    have h1 : x ∈ u.T → x ≠ t₁ := fun hx => by rintro rfl; exact ht₁u hx
    simp only [Finset.mem_union, Finset.mem_erase]
    tauto
  have hord : ((decomposeWith tn t u).drop t₁).ord = (decomposeWith (tn.drop t₁) t u).ord := by
    funext a b
    apply propext
    have h1 : u.ord a b → a ≠ t₁ ∧ b ≠ t₁ := fun h =>
      ⟨by rintro rfl; exact ht₁u (hu.mem_left h), by rintro rfl; exact ht₁u (hu.mem_right h)⟩
    have h2 : ∀ {x}, x ∈ u.T → x ≠ t₁ := fun hx => by rintro rfl; exact ht₁u hx
    simp only [TaskNetwork.drop_ord, decomposeWith_ord_iff]
    constructor
    · rintro ⟨h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, hat, hbt⟩, hat₁, hbt₁⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨⟨h, hat₁, Ne.symm hne⟩, hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨h, Ne.symm hne, hbt₁⟩, ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨⟨h, hat₁, hbt₁⟩, hat, hbt⟩))
    · rintro (h | ⟨⟨h, hat₁, -⟩, hb⟩ | ⟨⟨h, -, hbt₁⟩, ha⟩ | ⟨⟨h, hat₁, hbt₁⟩, hat, hbt⟩)
      · exact ⟨Or.inl h, h1 h⟩
      · exact ⟨Or.inr (Or.inl ⟨h, hb⟩), hat₁, h2 hb⟩
      · exact ⟨Or.inr (Or.inr (Or.inl ⟨h, ha⟩)), h2 ha, hbt₁⟩
      · exact ⟨Or.inr (Or.inr (Or.inr ⟨h, hat, hbt⟩)), hat₁, hbt₁⟩
  have hα : ((decomposeWith tn t u).drop t₁).α = (decomposeWith (tn.drop t₁) t u).α := by
    funext x
    simp [decomposeWith, TaskNetwork.drop]
  exact TaskNetwork.ext' hT hord hα

variable {M : Set (Method I A C)} {tn tnStar : TaskNetwork I A C}

/-- **Dropping a primitive task commutes with a decomposition sequence.** -/
lemma DecomposesToN.drop {n : ℕ} {t₁ : I} (h : DecomposesToN M n tn tnStar) :
    t₁ ∈ tn.T → tn.IsPrimitiveId t₁ →
      DecomposesToN M n (tn.drop t₁) (tnStar.drop t₁) := by
  induction h with
  | refl tn => exact fun _ _ => DecomposesToN.refl _
  | @head a b c n hstep _ ih =>
    intro ht₁ hprim
    obtain ⟨t, m, hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hstep
    have hstep' : DecompStep' M a (decomposeWith a t u) :=
      ⟨t, m, hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩
    have hne : t₁ ≠ t := by
      rintro rfl
      obtain ⟨x, hx⟩ := hprim
      rw [hx] at hαt
      exact Sum.inl_ne_inr hαt
    have ht₁u : t₁ ∉ u.T := Finset.disjoint_left.1 hdisj ht₁
    have ht₁b : t₁ ∈ (decomposeWith a t u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht₁, hne⟩)
    have hprimb : (decomposeWith a t u).IsPrimitiveId t₁ := by
      obtain ⟨x, hx⟩ := hprim
      exact ⟨x, by rw [hstep'.α_eq ht₁]; exact hx⟩
    have hstepP : DecompStep' M (a.drop t₁) (decomposeWith (a.drop t₁) t u) := by
      refine ⟨t, m, hmM, ?_, ?_, u, hu, huiso, ?_, rfl⟩
      · exact Finset.mem_erase.2 ⟨fun h => hne h.symm, htT⟩
      · exact hαt
      · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
    refine DecomposesToN.head hstepP ?_
    rw [← drop_decomposeWith_comm hu hne ht₁u]
    exact ih ht₁b hprimb

/-- A network without compound tasks admits no decomposition step. -/
lemma DecomposesToN.eq_of_noAbstract {n : ℕ} (h : DecomposesToN M n tn tnStar)
    (hno : ∀ t ∈ tn.T, ¬ tn.IsAbstractId t) : n = 0 ∧ tnStar = tn := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | head hstep _ =>
    obtain ⟨t, m, -, htT, hαt, -⟩ := hstep
    exact absurd ⟨_, hαt⟩ (hno t htT)

/-- **Primitive tasks keep their mutual ordering** along a decomposition sequence. -/
lemma DecomposesTo.ord_iff_of_prim (h : DecomposesTo M tn tnStar) (hwf : tn.WF) {x y : I}
    (hx : x ∈ tn.T) (hpx : tn.IsPrimitiveId x) (hy : y ∈ tn.T) (hpy : tn.IsPrimitiveId y) :
    tnStar.ord x y ↔ tn.ord x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Iff.rfl
  | @head a b hstep hrest ih =>
    have hxb := hstep.mem_of_isPrimitiveId hx hpx
    have hyb := hstep.mem_of_isPrimitiveId hy hpy
    have hpxb : b.IsPrimitiveId x := by
      obtain ⟨n, hn⟩ := hpx; exact ⟨n, by rw [hstep.α_eq hx]; exact hn⟩
    have hpyb : b.IsPrimitiveId y := by
      obtain ⟨n, hn⟩ := hpy; exact ⟨n, by rw [hstep.α_eq hy]; exact hn⟩
    exact (ih (hstep.wf hwf) hxb hpxb hyb hpyb).trans (hstep.ord_iff hx hy hxb hyb)

/-- Primitive tasks keep their name along a decomposition sequence. -/
lemma DecomposesTo.α_eq_of_prim (h : DecomposesTo M tn tnStar) {x : I} (hx : x ∈ tn.T)
    (hpx : tn.IsPrimitiveId x) : tnStar.α x = tn.α x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head a b hstep hrest ih =>
    have hxb := hstep.mem_of_isPrimitiveId hx hpx
    have hpxb : b.IsPrimitiveId x := by
      obtain ⟨n, hn⟩ := hpx; exact ⟨n, by rw [hstep.α_eq hx]; exact hn⟩
    rw [ih hxb hpxb, hstep.α_eq hx]

end Commute

/-! ### One-hole networks -/

section OneHole

variable [DecidableEq I] {M : Set (Method I A C)} {tn tnStar : TaskNetwork I A C}

lemma TaskNetwork.IsOneHole.drop (h : tn.IsOneHole) (t : I) : (tn.drop t).IsOneHole :=
  fun a ha b hb => h a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)

omit [DecidableEq I] in
lemma TaskNetwork.Iso.isOneHole {tn' : TaskNetwork I A C} (h : tn.Iso tn')
    (h1 : tn'.IsOneHole) : tn.IsOneHole := by
  obtain ⟨σ, hbij, -, hα⟩ := h
  rintro a ha b hb ⟨c, hc⟩ ⟨c', hc'⟩
  refine hbij.injOn ha hb (h1 _ (hbij.mapsTo ha) _ (hbij.mapsTo hb) ⟨c, ?_⟩ ⟨c', ?_⟩)
  · rw [← hα a ha]; exact hc
  · rw [← hα b hb]; exact hc'

lemma isOneHole_decomposeWith {t : I} {u : TaskNetwork I A C} (h1 : tn.IsOneHole) (ht : t ∈ tn.T)
    (hta : tn.IsAbstractId t) (hu : u.IsOneHole) (hdisj : Disjoint tn.T u.T) :
    (decomposeWith tn t u).IsOneHole := by
  have key : ∀ y ∈ (decomposeWith tn t u).T, (decomposeWith tn t u).IsAbstractId y →
      y ∈ u.T ∧ u.IsAbstractId y := by
    intro y hy hya
    rcases mem_decomposeWith_T.1 hy with ⟨hyT, hyt⟩ | hyu
    · have hyu : y ∉ u.T := Finset.disjoint_left.1 hdisj hyT
      obtain ⟨c, hc⟩ := hya
      rw [decomposeWith_α, if_neg hyu] at hc
      exact absurd (h1 y hyT t ht ⟨c, hc⟩ hta) hyt
    · obtain ⟨c, hc⟩ := hya
      rw [decomposeWith_α, if_pos hyu] at hc
      exact ⟨hyu, c, hc⟩
  intro a ha b hb hab hbb
  obtain ⟨hau, haa⟩ := key a ha hab
  obtain ⟨hbu, hba⟩ := key b hb hbb
  exact hu a hau b hbu haa hba

omit [DecidableEq I] in
/-- A task of a one-hole network other than its compound task is primitive. -/
lemma isPrimitiveId_of_ne (h1 : tn.IsOneHole) {x y : I} (hx : x ∈ tn.T) (hxa : tn.IsAbstractId x)
    (hy : y ∈ tn.T) (hyx : y ≠ x) : tn.IsPrimitiveId y := by
  rcases h : tn.α y with a | c
  · exact ⟨a, h⟩
  · exact absurd (h1 y hy x hx ⟨c, h⟩ hxa) hyx

/-- **Everything a decomposition sequence produces from the compound task of a one-hole network
lies after every predecessor of that task.** -/
lemma DecomposesTo.ord_after (h : DecomposesTo M tn tnStar) (hwf : tn.WF) (h1 : tn.IsOneHole)
    {x u0 : I} (hx : x ∈ tn.T) (hxa : tn.IsAbstractId x) (hu0 : u0 ∈ tn.T) (ho : tn.ord u0 x) :
    ∀ y ∈ tnStar.T, (y ∉ tn.T ∨ y = x) → tnStar.ord u0 y := by
  have hu0x : u0 ≠ x := by rintro rfl; exact hwf.irrefl _ ho
  have hpu0 : tn.IsPrimitiveId u0 := isPrimitiveId_of_ne h1 hx hxa hu0 hu0x
  suffices ∀ tn', DecomposesTo M tn tn' →
      (∀ y ∈ tn'.T, (y ∉ tn.T ∨ y = x) → tn'.ord u0 y) ∧
      (∀ y ∈ tn'.T, tn'.IsAbstractId y → (y ∉ tn.T ∨ y = x)) from (this tnStar h).1
  intro tn' h'
  induction h' with
  | refl =>
    refine ⟨fun y _ hy => ?_, fun y hy hya => Or.inr (h1 y hy x hx hya hxa)⟩
    rcases hy with hy | rfl
    · exact absurd ‹y ∈ tn.T› hy
    · exact ho
  | @tail b c hpre hstep ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨t, m, -, htT, hαt, u', hu', -, hdisj, rfl⟩ := hstep
    have hub : u0 ∈ b.T ∧ b.IsPrimitiveId u0 := DecomposesTo.mem_of_isPrimitiveId hpre hu0 hpu0
    have hu0t : u0 ≠ t := by
      rintro rfl
      obtain ⟨a, ha⟩ := hub.2
      rw [ha] at hαt
      exact Sum.inl_ne_inr hαt
    have hot : b.ord u0 t := ih1 t htT (ih2 t htT ⟨_, hαt⟩)
    refine ⟨fun y hy hyx => ?_, fun y hy hya => ?_⟩
    · rcases mem_decomposeWith_T.1 hy with ⟨hyb, hyt⟩ | hyu
      · exact Or.inr (Or.inr (Or.inr ⟨ih1 y hyb hyx, hu0t, hyt⟩))
      · exact Or.inr (Or.inl ⟨hot, hyu⟩)
    · rcases mem_decomposeWith_T.1 hy with ⟨hyb, hyt⟩ | hyu
      · have hyu : y ∉ u'.T := Finset.disjoint_left.1 hdisj hyb
        obtain ⟨c', hc'⟩ := hya
        rw [decomposeWith_α, if_neg hyu] at hc'
        exact ih2 y hyb ⟨c', hc'⟩
      · by_contra hcon
        push_neg at hcon
        have hyp := isPrimitiveId_of_ne h1 hx hxa hcon.1 hcon.2
        exact Finset.disjoint_left.1 hdisj (DecomposesTo.mem_of_isPrimitiveId hpre hcon.1 hyp).1 hyu

/-- **Everything a decomposition sequence produces from the compound task of a one-hole network
lies before every successor of that task.** -/
lemma DecomposesTo.ord_before (h : DecomposesTo M tn tnStar) (hwf : tn.WF) (h1 : tn.IsOneHole)
    {x v0 : I} (hx : x ∈ tn.T) (hxa : tn.IsAbstractId x) (hv0 : v0 ∈ tn.T) (ho : tn.ord x v0) :
    ∀ y ∈ tnStar.T, (y ∉ tn.T ∨ y = x) → tnStar.ord y v0 := by
  have hv0x : v0 ≠ x := by rintro rfl; exact hwf.irrefl _ ho
  have hpv0 : tn.IsPrimitiveId v0 := isPrimitiveId_of_ne h1 hx hxa hv0 hv0x
  suffices ∀ tn', DecomposesTo M tn tn' →
      (∀ y ∈ tn'.T, (y ∉ tn.T ∨ y = x) → tn'.ord y v0) ∧
      (∀ y ∈ tn'.T, tn'.IsAbstractId y → (y ∉ tn.T ∨ y = x)) from (this tnStar h).1
  intro tn' h'
  induction h' with
  | refl =>
    refine ⟨fun y _ hy => ?_, fun y hy hya => Or.inr (h1 y hy x hx hya hxa)⟩
    rcases hy with hy | rfl
    · exact absurd ‹y ∈ tn.T› hy
    · exact ho
  | @tail b c hpre hstep ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨t, m, -, htT, hαt, u', hu', -, hdisj, rfl⟩ := hstep
    have hvb : v0 ∈ b.T ∧ b.IsPrimitiveId v0 := DecomposesTo.mem_of_isPrimitiveId hpre hv0 hpv0
    have hv0t : v0 ≠ t := by
      rintro rfl
      obtain ⟨a, ha⟩ := hvb.2
      rw [ha] at hαt
      exact Sum.inl_ne_inr hαt
    have hot : b.ord t v0 := ih1 t htT (ih2 t htT ⟨_, hαt⟩)
    refine ⟨fun y hy hyx => ?_, fun y hy hya => ?_⟩
    · rcases mem_decomposeWith_T.1 hy with ⟨hyb, hyt⟩ | hyu
      · exact Or.inr (Or.inr (Or.inr ⟨ih1 y hyb hyx, hyt, hv0t⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hot, hyu⟩))
    · rcases mem_decomposeWith_T.1 hy with ⟨hyb, hyt⟩ | hyu
      · have hyu : y ∉ u'.T := Finset.disjoint_left.1 hdisj hyb
        obtain ⟨c', hc'⟩ := hya
        rw [decomposeWith_α, if_neg hyu] at hc'
        exact ih2 y hyb ⟨c', hc'⟩
      · by_contra hcon
        push_neg at hcon
        have hyp := isPrimitiveId_of_ne h1 hx hxa hcon.1 hcon.2
        exact Finset.disjoint_left.1 hdisj (DecomposesTo.mem_of_isPrimitiveId hpre hcon.1 hyp).1 hyu

end OneHole

end HTN
