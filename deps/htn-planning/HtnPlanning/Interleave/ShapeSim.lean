import HtnPlanning.Core.Noop
/-!
# Reordering a hierarchy does not change what it can produce

Two task networks have the same **shape** if they have the same task identifiers and the same
labels — they may order them differently.  Since the tasks and the labels of a decomposed
network do not depend on the ordering (`HTN.decomposeWith_T`, `HTN.decomposeWith_α`), the
decomposition relation is *shape-functorial*: whatever a hierarchy can decompose its initial
network into, a hierarchy with the same methods up to their orderings can decompose the
reordered initial network into a network of the same shape.

The main results are

* `HTN.DecomposesTo.shape` — the simulation, and
* `HTN.exists_primitive_reachable_congr` — consequently the existence of a *primitive* reachable
  network is invariant under reordering,

and the point of them is `HTN.Problem.IsNoop.solvable_congr_shape`: in a **no-op** problem
solvability is exactly the existence of a primitive reachable network plus `g ⊆ s₀`
(`HTN.Problem.IsNoop.solvable_iff`), so a no-op problem may be reordered freely without changing
its solvability.  This is the correctness argument of the compilation of a partially ordered
no-op problem into a totally ordered one.

Well-formedness of the *reordered* method bodies is a hypothesis of the simulation: a
decomposition step inserts a well-formed copy of the method body, so the ordering that replaces
the original one has to be a strict partial order.
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

/-- **Two task networks have the same shape** if they have the same tasks and the same labels.
They may order the tasks differently. -/
structure TaskNetwork.SameShape (tn tn' : TaskNetwork I A C) : Prop where
  /-- The two networks have the same tasks. -/
  T : tn.T = tn'.T
  /-- The two networks have the same labelling. -/
  α : tn.α = tn'.α

namespace TaskNetwork.SameShape

@[refl] theorem refl (tn : TaskNetwork I A C) : tn.SameShape tn := ⟨rfl, rfl⟩

theorem symm {tn tn' : TaskNetwork I A C} (h : tn.SameShape tn') : tn'.SameShape tn :=
  ⟨h.T.symm, h.α.symm⟩

theorem trans {tn₁ tn₂ tn₃ : TaskNetwork I A C} (h₁ : tn₁.SameShape tn₂)
    (h₂ : tn₂.SameShape tn₃) : tn₁.SameShape tn₃ := ⟨h₁.T.trans h₂.T, h₁.α.trans h₂.α⟩

/-- Being primitive depends only on the shape. -/
theorem isPrimitive {tn tn' : TaskNetwork I A C} (h : tn.SameShape tn')
    (hp : tn.IsPrimitive) : tn'.IsPrimitive := by
  intro t ht
  obtain ⟨a, ha⟩ := hp t (h.T ▸ ht)
  exact ⟨a, by rw [← h.α]; exact ha⟩

end TaskNetwork.SameShape

/-- **A method set is a reordering of another** if every one of its methods decomposes the same
task into a body of the same shape as some method of the other set, whose body is well
formed. -/
def MethodsShape (M M' : Set (Method I A C)) : Prop :=
  ∀ m ∈ M, ∃ m' ∈ M', m.abstractTask = m'.abstractTask ∧
    m.subtasks.SameShape m'.subtasks ∧ m'.subtasks.WF

section Step

variable [DecidableEq I] {M M' : Set (Method I A C)}

/-- **The simulation of a single decomposition step.** -/
theorem DecompStep'.shape (hM : MethodsShape M M') {tn₁ tn₂ u₁ : TaskNetwork I A C}
    (hs : tn₁.SameShape u₁) (h : DecompStep' M tn₁ tn₂) :
    ∃ u₂, DecompStep' M' u₁ u₂ ∧ tn₂.SameShape u₂ := by
  obtain ⟨t, m, hm, ht, hα, tn', hwf', hiso, hdisj, rfl⟩ := h
  obtain ⟨m', hm', hab, hshape, hwfm'⟩ := hM m hm
  obtain ⟨σ, hbij, hord, hαiso⟩ := hiso
  -- the copy of the *reordered* body on the identifiers of `tn'`
  set u' : TaskNetwork I A C :=
    { T := tn'.T
      ord := fun a b => a ∈ tn'.T ∧ b ∈ tn'.T ∧ m'.subtasks.ord (σ a) (σ b)
      α := tn'.α } with hu'
  have hbij' : Set.BijOn σ (tn'.T : Set I) (m'.subtasks.T : Set I) := by
    rw [← hshape.T]; exact hbij
  have hwfu' : u'.WF :=
    { mem_left := fun h => h.1
      mem_right := fun h => h.2.1
      irrefl := fun a h => hwfm'.irrefl (σ a) h.2.2
      trans := fun hab hbc => ⟨hab.1, hbc.2.1, hwfm'.trans hab.2.2 hbc.2.2⟩ }
  have hisou' : u'.Iso m'.subtasks := by
    refine ⟨σ, hbij', ?_, ?_⟩
    · intro a ha b hb
      exact ⟨fun h => h.2.2, fun h => ⟨by simpa using ha, by simpa using hb, h⟩⟩
    · intro a ha
      have := hαiso a ha
      rw [hshape.α] at this
      exact this
  refine ⟨decomposeWith u₁ t u', ⟨t, m', hm', ?_, ?_, u', hwfu', hisou', ?_, rfl⟩, ?_, ?_⟩
  · exact hs.T ▸ ht
  · rw [← hs.α, hα, hab]
  · rw [← hs.T]; exact hdisj
  · simp only [decomposeWith_T, hs.T, hu']
  · funext x
    simp only [decomposeWith_α, hu', hs.α]

/-- **The simulation of a decomposition.** -/
theorem DecomposesTo.shape (hM : MethodsShape M M') {tn₁ tn₂ u₁ : TaskNetwork I A C}
    (hs : tn₁.SameShape u₁) (h : DecomposesTo M tn₁ tn₂) :
    ∃ u₂, DecomposesTo M' u₁ u₂ ∧ tn₂.SameShape u₂ := by
  induction h with
  | refl => exact ⟨u₁, Relation.ReflTransGen.refl, hs⟩
  | tail _ hstep ih =>
    obtain ⟨u, hu, hsu⟩ := ih
    obtain ⟨u₂, hstep', hs₂⟩ := hstep.shape hM hsu
    exact ⟨u₂, hu.tail hstep', hs₂⟩

end Step

section Problem

variable [DecidableEq I] {P P' : Problem I A C I}

open Problem

/-- **Reordering does not change whether a primitive network can be reached.** -/
theorem exists_primitive_reachable_of_shape {M M' : Set (Method I A C)}
    {tn₁ u₁ : TaskNetwork I A C} (hM : MethodsShape M M') (hs : tn₁.SameShape u₁)
    (h : ∃ tn, DecomposesTo M tn₁ tn ∧ tn.IsPrimitive) :
    ∃ u, DecomposesTo M' u₁ u ∧ u.IsPrimitive := by
  obtain ⟨tn, hreach, hprim⟩ := h
  obtain ⟨u, hu, hsu⟩ := hreach.shape hM hs
  exact ⟨u, hu, hsu.isPrimitive hprim⟩

/-- The two-sided form. -/
theorem exists_primitive_reachable_congr {M M' : Set (Method I A C)}
    {tn₁ u₁ : TaskNetwork I A C} (hM : MethodsShape M M') (hM' : MethodsShape M' M)
    (hs : tn₁.SameShape u₁) :
    (∃ tn, DecomposesTo M tn₁ tn ∧ tn.IsPrimitive) ↔
      (∃ u, DecomposesTo M' u₁ u ∧ u.IsPrimitive) :=
  ⟨exists_primitive_reachable_of_shape hM hs, exists_primitive_reachable_of_shape hM' hs.symm⟩

end Problem

section Noop

variable {F : Type u} {A : Type v} {C : Type w} {I : Type*} [DecidableEq I]

/-- **A no-op problem may be reordered freely.**  If two well-formed no-op problems have the
same initial state, the same goal, initial task networks of the same shape and method sets that
are reorderings of each other, then they are solvable together. -/
theorem Problem.IsNoop.solvable_congr_shape {P P' : Problem F A C I} (hnoop : P.IsNoop)
    (hnoop' : P'.IsNoop) (hwf : P.WF) (hwf' : P'.WF) (hinit : P.init = P'.init)
    (hgoal : P.goal = P'.goal) (htn : P.tnI.SameShape P'.tnI)
    (hM : MethodsShape P.methods P'.methods) (hM' : MethodsShape P'.methods P.methods) :
    P.Solvable ↔ P'.Solvable := by
  rw [hnoop.solvable_iff hwf, hnoop'.solvable_iff hwf', hinit, hgoal]
  exact and_congr_right fun _ => exists_primitive_reachable_congr hM hM' htn

end Noop

end HTN
