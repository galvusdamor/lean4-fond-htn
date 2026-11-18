import HtnPlanning.Core.ClassicalPlanLength
/-!
# Short plans over a finite set of mutable facts

`HtnPlanning/Core/ClassicalPlanLength.lean` bounds the length of a shortest solution of a
classical planning problem by `2 ^ |F|`, for a *finite* type of facts `F`.  A description of a
planning problem lives over the infinite type `ℕ` of facts, but it mentions only finitely many
of them, and only those can ever change.  This file gives the corresponding bound:

`HTN.ClassicalProblem.exists_short_solution` — if every action of a set `Acts` changes only
facts of a finite set `F₀`, then a solution using only actions of `Acts` can be replaced by one
using only actions of `Acts` of length `< 2 ^ |F₀|`.

The argument is the same loop removal as in the finite case
(`HTN.ClassicalProblem.IsSolution.cut`); what changes is the pigeonhole: two prefixes of the
plan reaching the same state *on `F₀`* already reach the same state, because outside `F₀` every
reachable state agrees with the initial one.
-/

namespace HTN

namespace ClassicalProblem

universe u v

variable {F : Type u} {A : Type v} {P : ClassicalProblem F A}

/-- Outside the mutable facts nothing changes. -/
theorem transitionSeq_eq_of_not_mem {Acts : Set A} {F₀ : Set F}
    (hmut : ∀ a ∈ Acts, P.add a ⊆ F₀ ∧ P.del a ⊆ F₀) {f : F} (hf : f ∉ F₀)
    (as : List A) (has : ∀ a ∈ as, a ∈ Acts) (s : Set F) :
    (f ∈ P.transitionSeq as s ↔ f ∈ s) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [ActionModel.transitionSeq_cons]
    refine (ih (fun b hb => has b (by simp [hb])) _).trans ?_
    obtain ⟨hadd, hdel⟩ := hmut a (has a (by simp))
    simp only [ActionModel.transition, Set.mem_union, Set.mem_diff]
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact absurd (hadd h) hf
    · intro h
      exact Or.inl ⟨h, fun hd => hf (hdel hd)⟩

/-- A shortest solution among those using only actions of `Acts`. -/
theorem exists_solution_minimal_mem {Acts : Set A} {as : List A} (has : ∀ a ∈ as, a ∈ Acts)
    (hsol : P.IsSolution as) :
    ∃ plan, (∀ a ∈ plan, a ∈ Acts) ∧ P.IsSolution plan ∧
      ∀ q : List A, (∀ a ∈ q, a ∈ Acts) → P.IsSolution q → plan.length ≤ q.length := by
  classical
  set S : Set ℕ := {n | ∃ q : List A, (∀ a ∈ q, a ∈ Acts) ∧ P.IsSolution q ∧ q.length = n} with hS
  have hne : S.Nonempty := ⟨as.length, as, has, hsol, rfl⟩
  obtain ⟨plan, hmem, hsol', hlen⟩ := Nat.sInf_mem hne
  refine ⟨plan, hmem, hsol', fun q hq hqsol => ?_⟩
  rw [hlen]
  exact Nat.sInf_le ⟨q, hq, hqsol, rfl⟩

/-- **A solution over a set of actions that change only finitely many facts can be taken
short.** -/
theorem exists_short_solution [DecidableEq F] {Acts : Set A} {F₀ : Finset F}
    (hmut : ∀ a ∈ Acts, P.add a ⊆ ↑F₀ ∧ P.del a ⊆ ↑F₀) {as : List A}
    (has : ∀ a ∈ as, a ∈ Acts) (hsol : P.IsSolution as) :
    ∃ bs : List A, (∀ a ∈ bs, a ∈ Acts) ∧ P.IsSolution bs ∧ bs.length < 2 ^ F₀.card := by
  classical
  obtain ⟨plan, hmem, hsol', hmin⟩ := exists_solution_minimal_mem has hsol
  refine ⟨plan, hmem, hsol', ?_⟩
  by_contra hcon
  push_neg at hcon
  -- the trace of the plan on the mutable facts
  set g : Fin (plan.length + 1) → Finset F :=
    fun i => F₀.filter (fun f => f ∈ P.transitionSeq (plan.take i) P.init) with hg
  have hmapsto : ∀ i, g i ∈ F₀.powerset := by
    intro i
    exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hcard : F₀.powerset.card < Fintype.card (Fin (plan.length + 1)) := by
    rw [Finset.card_powerset, Fintype.card_fin]
    omega
  obtain ⟨i, -, j, -, hij, hgij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.univ) (t := F₀.powerset)
      (by simpa using hcard) (fun i _ => hmapsto i)
  -- the two prefixes reach the same state
  have hstates : ∀ i j : Fin (plan.length + 1), g i = g j →
      P.transitionSeq (plan.take i) P.init = P.transitionSeq (plan.take j) P.init := by
    intro i j hgij
    ext f
    by_cases hf : f ∈ F₀
    · have := congrArg (fun s : Finset F => f ∈ s) hgij
      simpa [hg, hf] using this
    · rw [transitionSeq_eq_of_not_mem hmut hf _
          (fun a ha => hmem a (List.take_subset _ _ ha)),
        transitionSeq_eq_of_not_mem hmut hf _
          (fun a ha => hmem a (List.take_subset _ _ ha))]
  have hcut : ∀ i j : Fin (plan.length + 1), (i : ℕ) < (j : ℕ) →
      P.transitionSeq (plan.take i) P.init = P.transitionSeq (plan.take j) P.init → False := by
    intro i j hlt heq
    have hle : (i : ℕ) ≤ (j : ℕ) := hlt.le
    have hsolcut := IsSolution.cut P hsol' hle heq
    have hmemcut : ∀ a ∈ plan.take (i : ℕ) ++ plan.drop (j : ℕ), a ∈ Acts := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hmem a (List.take_subset _ _ ha)
      · exact hmem a (List.drop_subset _ _ ha)
    have hle' := hmin _ hmemcut hsolcut
    have hi : (i : ℕ) ≤ plan.length := by omega
    have hj : (j : ℕ) ≤ plan.length := by omega
    simp only [List.length_append, List.length_take, List.length_drop] at hle'
    omega
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with hlt | hlt
  · exact hcut i j hlt (hstates i j hgij)
  · exact hcut j i hlt (hstates j i hgij.symm)

end ClassicalProblem

end HTN
