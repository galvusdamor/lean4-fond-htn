import HtnPlanning.Core.Decomposition
/-!
# Two invariants of decomposition

Both statements of this file are invariants of the refinement relation `HTN.DecomposesTo` that
hold for an arbitrary hierarchy, and both are used to read off what a hierarchy can *not* do.

* `HTN.DecomposesTo.labels_mem` — the labels occurring in a refinement of a task network are
  labels of the network itself or of the body of a method.  In particular a hierarchy can only
  produce the actions that its methods mention.
* `HTN.DecomposesTo.exists_method_nocompound` — if a network contains a compound task, then
  every *primitive* refinement of it uses some method whose body contains no compound task.  In
  particular a hierarchy all of whose bodies contain a compound task refines nothing into a
  primitive network, so a problem over it is unsolvable.
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w} [DecidableEq I] {M : Set (Method I A C)}

/-- The labels of a refinement come from the network or from the bodies of the methods. -/
theorem DecomposesTo.labels_mem {L : Set (A ⊕ C)} {tn tn' : TaskNetwork I A C}
    (h : DecomposesTo M tn tn') (h₀ : ∀ t ∈ tn.T, tn.α t ∈ L)
    (hM : ∀ m ∈ M, ∀ t ∈ m.subtasks.T, m.subtasks.α t ∈ L) :
    ∀ t ∈ tn'.T, tn'.α t ∈ L := by
  induction h with
  | refl => exact h₀
  | tail _ hstep ih =>
    obtain ⟨t, m, hm, htT, -, u, -, ⟨σ, hbij, -, hα⟩, -, rfl⟩ := hstep
    intro x hx
    rw [decomposeWith_α]
    by_cases hxu : x ∈ u.T
    · simp only [hxu, if_true]
      rw [hα x hxu]
      exact hM m hm _ (by simpa using hbij.mapsTo (by simpa using hxu))
    · simp only [hxu, if_false]
      rcases mem_decomposeWith_T.1 hx with ⟨hxT, -⟩ | hxu'
      · exact ih x hxT
      · exact absurd hxu' hxu

/-- If a network has a compound task, then every primitive refinement of it uses a method whose
body has no compound task. -/
theorem DecomposesTo.exists_method_nocompound {tn tn' : TaskNetwork I A C}
    (h : DecomposesTo M tn tn') (h₀ : ∃ t ∈ tn.T, ∃ c : C, tn.α t = Sum.inr c)
    (hprim : tn'.IsPrimitive) :
    ∃ m ∈ M, ∀ t ∈ m.subtasks.T, ∀ c : C, m.subtasks.α t ≠ Sum.inr c := by
  have key : ∀ {x y : TaskNetwork I A C}, DecomposesTo M x y →
      (∃ t ∈ x.T, ∃ c : C, x.α t = Sum.inr c) →
      (∃ t ∈ y.T, ∃ c : C, y.α t = Sum.inr c) ∨
        ∃ m ∈ M, ∀ t ∈ m.subtasks.T, ∀ c : C, m.subtasks.α t ≠ Sum.inr c := by
    intro x y hxy hx
    induction hxy with
    | refl => exact Or.inl hx
    | tail _ hstep ih =>
      rcases ih with hmid | hdone
      · obtain ⟨t, m, hm, -, -, u, -, ⟨σ, hbij, -, hα⟩, -, rfl⟩ := hstep
        by_cases hnc : ∀ t ∈ m.subtasks.T, ∀ c : C, m.subtasks.α t ≠ Sum.inr c
        · exact Or.inr ⟨m, hm, hnc⟩
        · push_neg at hnc
          obtain ⟨t₀, ht₀, c, hc⟩ := hnc
          obtain ⟨x₀, hx₀, hσ⟩ := hbij.surjOn (by simpa using ht₀)
          have hx₀T : x₀ ∈ u.T := by simpa using hx₀
          refine Or.inl ⟨x₀, mem_decomposeWith_T.2 (Or.inr hx₀T), c, ?_⟩
          rw [decomposeWith_α, if_pos hx₀T, hα x₀ hx₀T, hσ]
          exact hc
      · exact Or.inr hdone
  rcases key h h₀ with ⟨t, ht, c, hc⟩ | hdone
  · obtain ⟨a, ha⟩ := hprim t ht
    rw [hc] at ha
    exact absurd ha (by simp)
  · exact hdone

end HTN
