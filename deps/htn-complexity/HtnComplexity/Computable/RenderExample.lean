import HtnComplexity.Computable.RenderClass
/-!
# A rendering, written out

`HtnComplexity/Computable/Render.lean` states what it takes to write a semantic problem
down as a pair of descriptions.  Its hypotheses are conditions on the problem *and* on the lists
the rendering carries, so they could in principle be unsatisfiable together; this file rules
that out by instantiating every one of them.

The example is the smallest problem with a compound task: one fact, one action, which adds the
fact, and one method, which decomposes the single compound task into the single action.  The
initial task network is that compound task, the goal is the fact.

* `HTN.Syn.Example.rendering` — the rendering;
* `HTN.Syn.Example.solvable_desc_iff` — the bridge applied to it;
* `HTN.Syn.Example.isAcyclic_desc`, `HTN.Syn.Example.isRooted_desc` — and the class conditions
  of `HtnComplexity/Computable/RenderClass.lean`, so those are not vacuous either.
-/

namespace HTN

namespace Syn

namespace Example

open TaskNetwork

/-- The problem: one fact, one action adding it, one compound task decomposing into it. -/
def prob : Problem Unit Unit Unit (ℕ × ℕ) where
  prec := fun _ => ∅
  add := fun _ => Set.univ
  del := fun _ => ∅
  methods := {⟨(), TaskNetwork.grid [[Sum.inl ()]]⟩}
  init := ∅
  goal := Set.univ
  tnI := TaskNetwork.grid [[Sum.inr ()]]

/-- **The rendering of `HTN.Syn.Example.prob`.** -/
def rendering : Rendering prob where
  eF := fun _ => 0
  eA := fun _ => 0
  eC := fun _ => 0
  eF_inj := fun _ _ _ => rfl
  eA_inj := fun _ _ _ => rfl
  eC_inj := fun _ _ _ => rfl
  acts := [()]
  precL := fun _ => []
  addL := fun _ => [()]
  delL := fun _ => []
  bodies := [((), ⟨[[Sum.inl ()]], 0⟩)]
  tnIshape := ⟨[[Sum.inr ()]], 0⟩
  initL := []
  goalL := [()]
  used_mem := fun _ _ => by simp
  precL_eq := fun _ _ => by simp [prob]
  addL_eq := fun _ _ => by
    ext v
    simp [prob]
  delL_eq := fun _ _ => by simp [prob]
  init_eq := by simp [prob]
  goal_eq := by
    ext v
    simp [prob]
  tnI_wf := TaskNetwork.grid_wf
  tnI_iso := by rw [prob, Shape.net_zero]
  bodies_sub := fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨⟨(), TaskNetwork.grid [[Sum.inl ()]]⟩, rfl, rfl, by rw [Shape.net_zero]⟩
  bodies_all := fun m hm => by
    have hm' : m = ⟨(), TaskNetwork.grid [[Sum.inl ()]]⟩ := hm.1
    subst hm'
    exact ⟨((), ⟨[[Sum.inl ()]], 0⟩), by simp, rfl, by rw [Shape.net_zero]⟩

/-- The bridge, for the example. -/
theorem solvable_desc_iff :
    Solvable rendering.domDesc rendering.instDesc ↔ prob.Solvable :=
  rendering.solvable_iff

/-- The described domain is acyclic: the one body has no compound subtask. -/
theorem isAcyclic_desc : DomDesc.IsAcyclic rendering.domDesc := by
  refine rendering.isAcyclic_domDesc (fun _ => 0) ?_
  rintro p hp row hrow x hx c hc
  simp only [rendering, List.mem_singleton] at hp
  subst hp
  simp only [List.mem_singleton] at hrow
  subst hrow
  simp only [List.mem_singleton] at hx
  subst hx
  exact absurd hc (by simp)

/-- The described instance is rooted. -/
theorem isRooted_desc : InstDesc.IsRooted rendering.instDesc :=
  rendering.isRooted_instDesc (c := ()) rfl

end Example

end Syn

end HTN
