import HtnPlanning.Core.SolutionIso
import HtnPlanning.Core.Reachability
/-!
# Relabelling a task network along a change of signature

Every construction of this development that leaves the *semantic* world and enters the
*syntactic* one — the finite description language of
`HtnPlanning/Computable/Syntax.lean` — has to compare two planning problems that live
over **different signatures**: a problem over the abstract types `(F, A, C, I)` and a problem
over `(ℕ, ℕ, ℕ, ℕ)` obtained by encoding the four components as numbers.

This file provides the vocabulary for such a comparison at the level of task networks and
decomposition:

* `HTN.TaskNetwork.relabel eA eC eI tn` — the image of the task network `tn` under a map `eA`
  of action names, a map `eC` of compound task names and a **bijection** `eI` of task
  identifiers;
* `HTN.Method.relabel` — the same for a decomposition method;
* `HTN.TaskNetwork.unrelabel` — a partial inverse, used to reflect a target-side network back
  to the source side;
* the transfer of well-formedness, primitiveness, linearizations, action sequences,
  isomorphism, `HTN.decomposeWith` and, the main results, of a decomposition step and of a
  whole decomposition sequence, in **both** directions
  (`HTN.decomposesTo_relabel`, `HTN.exists_decomposesTo_of_relabel`).

Identifiers are relabelled along a bijection: a task network only ever uses finitely many
identifiers, and both id types of interest are countably infinite, so this costs nothing and
makes the image of a network an exact copy of it.  Action and compound task names are
relabelled along mere injections, since the target signature is typically much larger than the
source one.

`HtnPlanning/Core/Transfer.lean` uses this to transfer *solvability*.
-/

namespace HTN

universe u u' v v' w w'

variable {A : Type v} {A' : Type v'} {C : Type w} {C' : Type w'} {I : Type u} {I' : Type u'}

namespace TaskNetwork

/-! ### The image of a task network -/

/-- **The image of a task network** under the maps `eA` of action names and `eC` of compound
task names and the bijection `eI` of task identifiers. -/
def relabel [DecidableEq I'] (eA : A → A') (eC : C → C') (eI : I ≃ I')
    (tn : TaskNetwork I A C) : TaskNetwork I' A' C' where
  T := tn.T.image eI
  ord x y := tn.ord (eI.symm x) (eI.symm y)
  α x := Sum.map eA eC (tn.α (eI.symm x))

variable [DecidableEq I'] {eA : A → A'} {eC : C → C'} {eI : I ≃ I'}

lemma relabel_T (tn : TaskNetwork I A C) :
    (relabel eA eC eI tn).T = tn.T.image eI := rfl

@[simp] lemma relabel_ord (tn : TaskNetwork I A C) (x y : I') :
    (relabel eA eC eI tn).ord x y ↔ tn.ord (eI.symm x) (eI.symm y) := Iff.rfl

@[simp] lemma relabel_α (tn : TaskNetwork I A C) (x : I') :
    (relabel eA eC eI tn).α x = Sum.map eA eC (tn.α (eI.symm x)) := rfl

@[simp] lemma mem_relabel_T {tn : TaskNetwork I A C} {x : I'} :
    x ∈ (relabel eA eC eI tn).T ↔ eI.symm x ∈ tn.T := by
  simp only [relabel_T, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨eI.symm x, h, by simp⟩

@[simp] lemma mem_relabel_T_apply {tn : TaskNetwork I A C} {x : I} :
    eI x ∈ (relabel eA eC eI tn).T ↔ x ∈ tn.T := by
  simp

lemma relabel_ord_apply (tn : TaskNetwork I A C) (x y : I) :
    (relabel eA eC eI tn).ord (eI x) (eI y) ↔ tn.ord x y := by simp

/-- Relabelling preserves well-formedness. -/
lemma relabel_wf {tn : TaskNetwork I A C} (h : tn.WF) : (relabel eA eC eI tn).WF where
  mem_left := fun hxy => mem_relabel_T.2 (h.mem_left hxy)
  mem_right := fun hxy => mem_relabel_T.2 (h.mem_right hxy)
  irrefl := fun _ hc => h.irrefl _ hc
  trans := fun hab hbc => h.trans hab hbc

/-- Primitiveness is preserved and reflected by relabelling. -/
lemma relabel_isPrimitive_iff {tn : TaskNetwork I A C} :
    (relabel eA eC eI tn).IsPrimitive ↔ tn.IsPrimitive := by
  constructor
  · intro h t ht
    obtain ⟨a', ha'⟩ := h (eI t) (mem_relabel_T_apply.2 ht)
    simp only [relabel_α, Equiv.symm_apply_apply] at ha'
    rcases hx : tn.α t with a | c
    · exact ⟨a, hx⟩
    · rw [hx] at ha'; simp at ha'
  · intro h t ht
    obtain ⟨a, ha⟩ := h (eI.symm t) (mem_relabel_T.1 ht)
    exact ⟨eA a, by simp [ha]⟩

/-! ### Linearizations and action sequences -/

lemma isLinearization_relabel_iff {tn : TaskNetwork I A C} {l : List I} :
    (relabel eA eC eI tn).IsLinearization (l.map eI) ↔ tn.IsLinearization l := by
  constructor
  · rintro ⟨hnd, hmem, hpair⟩
    refine ⟨(List.nodup_map_iff eI.injective).1 hnd, fun t => ?_, ?_⟩
    · have := hmem (eI t)
      simpa using this
    · have h2 := (List.pairwise_map (f := (eI : I → I'))).1 hpair
      refine h2.imp ?_
      intro a b hab hc
      exact hab ((relabel_ord_apply (eA := eA) (eC := eC) tn b a).2 hc)
  · rintro ⟨hnd, hmem, hpair⟩
    refine ⟨hnd.map eI.injective, fun t => ?_,
      (List.pairwise_map (f := (eI : I → I'))).2 (hpair.imp (fun {a b} hab hc =>
        hab ((relabel_ord_apply (eA := eA) (eC := eC) tn b a).1 hc)))⟩
    constructor
    · intro ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      exact mem_relabel_T_apply.2 ((hmem s).1 hs)
    · intro ht
      exact List.mem_map.2 ⟨eI.symm t, (hmem _).2 (mem_relabel_T.1 ht), by simp⟩

lemma isActionSeq_relabel {tn : TaskNetwork I A C} {l : List I} {as : List A}
    (h : tn.IsActionSeq l as) :
    (relabel eA eC eI tn).IsActionSeq (l.map eI) (as.map eA) := by
  have h' : l.map tn.α = as.map Sum.inl := h
  show (l.map eI).map (relabel eA eC eI tn).α = (as.map eA).map Sum.inl
  rw [List.map_map, List.map_map]
  have hl : (relabel eA eC eI tn).α ∘ (eI : I → I') = (Sum.map eA eC) ∘ tn.α := by
    funext x; simp
  rw [hl, ← List.map_map, h', List.map_map]
  rfl

/-! ### Isomorphism -/

lemma Iso.relabel {tn u : TaskNetwork I A C} (h : tn.Iso u) :
    (TaskNetwork.relabel eA eC eI tn).Iso (TaskNetwork.relabel eA eC eI u) := by
  obtain ⟨σ, hbij, hord, hα⟩ := h
  refine ⟨fun x => eI (σ (eI.symm x)), ?_, ?_, ?_⟩
  · constructor
    · intro x hx
      have : eI.symm x ∈ tn.T := by simpa using hx
      have := hbij.mapsTo (by simpa using this)
      simpa using this
    constructor
    · intro x hx y hy hxy
      have hx' : eI.symm x ∈ tn.T := by simpa using hx
      have hy' : eI.symm y ∈ tn.T := by simpa using hy
      have := hbij.injOn (by simpa using hx') (by simpa using hy') (eI.injective hxy)
      exact eI.symm.injective this
    · intro y hy
      have hy' : eI.symm y ∈ u.T := by simpa using hy
      obtain ⟨x, hx, hxy⟩ := hbij.surjOn (by simpa using hy')
      exact ⟨eI x, by simpa using hx, by simp [hxy]⟩
  · intro x hx y hy
    have hx' : eI.symm x ∈ tn.T := by simpa using hx
    have hy' : eI.symm y ∈ tn.T := by simpa using hy
    simpa using hord _ hx' _ hy'
  · intro x hx
    have hx' : eI.symm x ∈ tn.T := by simpa using hx
    simpa using congrArg (Sum.map eA eC) (hα _ hx')

/-- An isomorphism of the images is an isomorphism of the sources. -/
lemma iso_of_relabel_iso (hA : Function.Injective eA) (hC : Function.Injective eC)
    {tn u : TaskNetwork I A C}
    (h : (TaskNetwork.relabel eA eC eI tn).Iso (TaskNetwork.relabel eA eC eI u)) : tn.Iso u := by
  obtain ⟨σ, hbij, hord, hα⟩ := h
  have hsum : Function.Injective (Sum.map eA eC) := by
    rintro (a | c) (a' | c') hh <;> simp only [Sum.map_inl, Sum.map_inr] at hh ⊢
    · exact congrArg Sum.inl (hA (Sum.inl_injective hh))
    · exact absurd hh (by simp)
    · exact absurd hh (by simp)
    · exact congrArg Sum.inr (hC (Sum.inr_injective hh))
  have hmt : ∀ x : I, x ∈ (tn.T : Set I) → eI x ∈ (TaskNetwork.relabel eA eC eI tn).T := by
    intro x hx; simpa using hx
  refine ⟨fun x => eI.symm (σ (eI x)), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hx' : eI x ∈ ((TaskNetwork.relabel eA eC eI tn).T : Set I') := by
        simpa using hmt x hx
      have h2 := hbij.mapsTo hx'
      simpa using h2
    · intro x hx y hy hxy
      have hx' : eI x ∈ ((TaskNetwork.relabel eA eC eI tn).T : Set I') := by
        simpa using hmt x hx
      have hy' : eI y ∈ ((TaskNetwork.relabel eA eC eI tn).T : Set I') := by
        simpa using hmt y hy
      have := hbij.injOn hx' hy' (eI.symm.injective hxy)
      exact eI.injective this
    · intro y hy
      have hy' : eI y ∈ ((TaskNetwork.relabel eA eC eI u).T : Set I') := by
        have : eI y ∈ (TaskNetwork.relabel eA eC eI u).T := by simpa using hy
        simpa using this
      obtain ⟨x, hx, hxy⟩ := hbij.surjOn hy'
      refine ⟨eI.symm x, ?_, ?_⟩
      · have : eI.symm x ∈ tn.T := by simpa using hx
        simpa using this
      · show eI.symm (σ (eI (eI.symm x))) = y
        rw [Equiv.apply_symm_apply, hxy, Equiv.symm_apply_apply]
  · intro x hx y hy
    have hx' : eI x ∈ ((TaskNetwork.relabel eA eC eI tn).T : Set I') := by
      simpa using hmt x hx
    have hy' : eI y ∈ ((TaskNetwork.relabel eA eC eI tn).T : Set I') := by
      simpa using hmt y hy
    have := hord _ hx' _ hy'
    simpa using this
  · intro x hx
    have hx' : eI x ∈ ((TaskNetwork.relabel eA eC eI tn).T : Set I') := by
      simpa using hmt x hx
    have := hα _ hx'
    simp only [relabel_α, Equiv.symm_apply_apply] at this
    exact hsum this

/-! ### Decomposition -/

lemma relabel_decomposeWith [DecidableEq I] {tn u : TaskNetwork I A C} {t : I} :
    TaskNetwork.relabel eA eC eI (decomposeWith tn t u) =
      decomposeWith (TaskNetwork.relabel eA eC eI tn) (eI t)
        (TaskNetwork.relabel eA eC eI u) := by
  refine ext' ?_ ?_ ?_
  · simp only [relabel_T, decomposeWith_T, Finset.image_union]
    rw [Finset.image_erase eI.injective]
  · funext x y
    simp only [relabel_ord, decomposeWith_ord_iff, eq_iff_iff]
    constructor
    · rintro (h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by simpa using h, mem_relabel_T.2 hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by simpa using h, mem_relabel_T.2 ha⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨h, ?_, ?_⟩))
        · intro hc; exact h1 (by rw [hc]; simp)
        · intro hc; exact h2 (by rw [hc]; simp)
    · rintro (h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr (Or.inl ⟨by simpa using h, mem_relabel_T.1 hb⟩)
      · refine Or.inr (Or.inr (Or.inl ⟨by simpa using h, mem_relabel_T.1 ha⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨h, ?_, ?_⟩))
        · intro hc; exact h1 (by simp [← hc])
        · intro hc; exact h2 (by simp [← hc])
  · funext x
    simp only [relabel_α, decomposeWith_α]
    by_cases hx : eI.symm x ∈ u.T
    · rw [if_pos hx, if_pos (mem_relabel_T.2 hx)]
    · rw [if_neg hx, if_neg (fun hc => hx (mem_relabel_T.1 hc))]

/-! ### The partial inverse -/

/-- **The preimage of a task network** along the relabelling: identifiers are moved back along
the bijection `eI`, names are moved back along a left inverse of `Sum.map eA eC`.  This is an
exact inverse of `TaskNetwork.relabel` on the networks all of whose labels are in the image
(`relabel_unrelabel_iso`).  Only `A ⊕ C` has to be nonempty (one of the two name types may be
empty). -/
noncomputable def unrelabel [DecidableEq I] [Nonempty (A ⊕ C)] (eA : A → A')
    (eC : C → C') (eI : I ≃ I') (v : TaskNetwork I' A' C') : TaskNetwork I A C where
  T := v.T.image eI.symm
  ord x y := v.ord (eI x) (eI y)
  α x := Function.invFun (Sum.map eA eC) (v.α (eI x))

variable [DecidableEq I] [Nonempty (A ⊕ C)]

omit [DecidableEq I'] in
@[simp] lemma unrelabel_ord (v : TaskNetwork I' A' C') (x y : I) :
    (unrelabel eA eC eI v).ord x y ↔ v.ord (eI x) (eI y) := Iff.rfl

omit [DecidableEq I'] in
@[simp] lemma mem_unrelabel_T {v : TaskNetwork I' A' C'} {x : I} :
    x ∈ (unrelabel eA eC eI v).T ↔ eI x ∈ v.T := by
  simp only [unrelabel, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨eI x, h, by simp⟩

omit [DecidableEq I'] in
lemma unrelabel_wf {v : TaskNetwork I' A' C'} (h : v.WF) : (unrelabel eA eC eI v).WF where
  mem_left := fun hxy => mem_unrelabel_T.2 (h.mem_left hxy)
  mem_right := fun hxy => mem_unrelabel_T.2 (h.mem_right hxy)
  irrefl := fun _ hc => h.irrefl _ hc
  trans := fun hab hbc => h.trans hab hbc

/-- On a network whose labels are in the image of the name maps, relabelling the preimage
returns an isomorphic copy — in fact the same identifiers, the same ordering, and the same
labels on the network. -/
lemma relabel_unrelabel_iso (hA : Function.Injective eA) (hC : Function.Injective eC)
    {v : TaskNetwork I' A' C'}
    (hlab : ∀ x ∈ v.T, ∃ y : A ⊕ C, v.α x = Sum.map eA eC y) :
    (TaskNetwork.relabel eA eC eI (unrelabel eA eC eI v)).Iso v := by
  have hT : (TaskNetwork.relabel eA eC eI (unrelabel eA eC eI v)).T = v.T := by
    ext x
    simp
  refine ⟨id, ?_, ?_, ?_⟩
  · rw [hT]
    exact Set.bijOn_id _
  · intro x hx y hy
    simp
  · intro x hx
    have hxv : x ∈ v.T := by rwa [hT] at hx
    obtain ⟨y, hy⟩ := hlab x hxv
    simp only [id, relabel_α, unrelabel, Equiv.apply_symm_apply, hy]
    rw [Function.leftInverse_invFun (Sum.map_injective.2 ⟨hA, hC⟩) y]

end TaskNetwork

/-! ### Methods -/

/-- The image of a decomposition method under a change of signature. -/
def Method.relabel [DecidableEq I'] (eA : A → A') (eC : C → C') (eI : I ≃ I')
    (m : Method I A C) : Method I' A' C' where
  abstractTask := eC m.abstractTask
  subtasks := TaskNetwork.relabel eA eC eI m.subtasks

@[simp] lemma Method.relabel_abstractTask [DecidableEq I'] (eA : A → A') (eC : C → C')
    (eI : I ≃ I') (m : Method I A C) :
    (Method.relabel eA eC eI m).abstractTask = eC m.abstractTask := rfl

@[simp] lemma Method.relabel_subtasks [DecidableEq I'] (eA : A → A') (eC : C → C') (eI : I ≃ I')
    (m : Method I A C) :
    (Method.relabel eA eC eI m).subtasks = TaskNetwork.relabel eA eC eI m.subtasks := rfl

open TaskNetwork

section Steps

variable [DecidableEq I] [DecidableEq I'] {eA : A → A'} {eC : C → C'} {eI : I ≃ I'}
  {M : Set (Method I A C)}

/-- **A decomposition step is preserved by relabelling.** -/
theorem decompStep_relabel {tn tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    (h : DecompStep M tn t m tn₂) :
    DecompStep (Method.relabel eA eC eI '' M) (TaskNetwork.relabel eA eC eI tn) (eI t)
      (Method.relabel eA eC eI m) (TaskNetwork.relabel eA eC eI tn₂) := by
  obtain ⟨hm, ht, hαt, u, huwf, huiso, hdisj, rfl⟩ := h
  refine ⟨⟨m, hm, rfl⟩, mem_relabel_T_apply.2 ht, ?_, TaskNetwork.relabel eA eC eI u,
    relabel_wf huwf, huiso.relabel, ?_, ?_⟩
  · simp [hαt]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (mem_relabel_T.1 hx) (mem_relabel_T.1 hx')
  · exact relabel_decomposeWith

/-- **A decomposition sequence is preserved by relabelling.** -/
theorem decomposesTo_relabel {tn tn₂ : TaskNetwork I A C}
    (h : DecomposesTo M tn tn₂) :
    DecomposesTo (Method.relabel eA eC eI '' M) (TaskNetwork.relabel eA eC eI tn)
      (TaskNetwork.relabel eA eC eI tn₂) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact Relation.ReflTransGen.tail ih ⟨eI t, Method.relabel eA eC eI m, decompStep_relabel hs⟩

variable [Nonempty (A ⊕ C)] [Infinite I]

set_option maxHeartbeats 1000000 in
omit [Infinite I] in
/-- **A decomposition step of the image comes from a decomposition step of the source.** -/
theorem exists_decompStep_of_relabel (hA : Function.Injective eA) (hC : Function.Injective eC)
    {w : TaskNetwork I A C} {t' : I'} {m' : Method I' A' C'} {v₂ : TaskNetwork I' A' C'}
    (hw : w.WF)
    (h : DecompStep (Method.relabel eA eC eI '' M) (TaskNetwork.relabel eA eC eI w) t' m' v₂) :
    ∃ w₂ : TaskNetwork I A C, DecompStep' M w w₂ ∧
      (TaskNetwork.relabel eA eC eI w₂).Iso v₂ := by
  obtain ⟨⟨m, hm, rfl⟩, ht', hαt', u', hu'wf, hu'iso, hdisj', rfl⟩ := h
  set t : I := eI.symm t' with hts
  have htw : t ∈ w.T := mem_relabel_T.1 ht'
  have hαt : w.α t = Sum.inr m.abstractTask := by
    have := hαt'
    simp only [relabel_α, Method.relabel_abstractTask, ← hts] at this
    rcases hx : w.α t with a | c
    · rw [hx] at this; simp at this
    · rw [hx] at this
      simp only [Sum.map_inr, Sum.inr.injEq] at this
      rw [hC this]
  -- the labels of `u'` are in the image, because `u'` is a copy of a relabelled network
  have hlab : ∀ x ∈ u'.T, ∃ y : A ⊕ C, u'.α x = Sum.map eA eC y := by
    obtain ⟨σ, hbij, -, hα⟩ := hu'iso
    intro x hx
    exact ⟨m.subtasks.α (eI.symm (σ x)), by rw [hα x hx]; simp⟩
  set u : TaskNetwork I A C := unrelabel eA eC eI u' with hu
  have huwf : u.WF := unrelabel_wf hu'wf
  have hiso1 : (TaskNetwork.relabel eA eC eI u).Iso u' := relabel_unrelabel_iso hA hC hlab
  have huiso : u.Iso m.subtasks := by
    refine iso_of_relabel_iso (eI := eI) hA hC ?_
    exact hiso1.trans hu'iso
  have hdisj : Disjoint w.T u.T := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.disjoint_left] at hdisj'
    exact hdisj' (mem_relabel_T_apply.2 hx) (mem_unrelabel_T.1 hx')
  refine ⟨decomposeWith w t u, ⟨t, m, hm, htw, hαt, u, huwf, huiso, hdisj, rfl⟩, ?_⟩
  rw [relabel_decomposeWith]
  have heq : eI t = t' := by simp [hts]
  rw [heq]
  obtain ⟨ρ, hρbij, hρord, hρα⟩ := hiso1
  refine decomposeWith_iso_congr (relabel_wf hw) (relabel_wf hw) (relabel_wf huwf) hu'wf ?_ ?_
    ht' (Set.bijOn_id _) (by simp) (by simp) hρbij hρord hρα
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (mem_relabel_T.1 hx) (mem_relabel_T.1 hx')
  · exact hdisj'

omit [Infinite I] in
/-- **A decomposition sequence of the image comes from one of the source**, up to isomorphism. -/
theorem exists_decomposesTo_of_relabel [Infinite I'] (hA : Function.Injective eA)
    (hC : Function.Injective eC) {tn : TaskNetwork I A C} (hwf : tn.WF)
    {v : TaskNetwork I' A' C'}
    (h : DecomposesTo (Method.relabel eA eC eI '' M) (TaskNetwork.relabel eA eC eI tn) v) :
    ∃ w : TaskNetwork I A C, DecomposesTo M tn w ∧ (TaskNetwork.relabel eA eC eI w).Iso v := by
  induction h with
  | refl => exact ⟨tn, Relation.ReflTransGen.refl, TaskNetwork.Iso.refl _⟩
  | @tail v₁ v₂ hstep₁ hstep ih =>
    obtain ⟨w, hw, hwiso⟩ := ih
    obtain ⟨t', m', hs⟩ := hstep
    have hwwf : w.WF := HTN.DecomposesTo.wf hw hwf
    have hv₁wf : v₁.WF :=
      HTN.DecomposesTo.wf hstep₁ (relabel_wf hwf)
    obtain ⟨t'', v₂', hs', hiso₂⟩ :=
      hs.iso hv₁wf (relabel_wf hwwf) (hwiso.symm)
    obtain ⟨w₂, hstep₂, hiso₃⟩ := exists_decompStep_of_relabel hA hC hwwf hs'
    exact ⟨w₂, Relation.ReflTransGen.tail hw hstep₂, hiso₃.trans hiso₂.symm⟩

end Steps

end HTN
