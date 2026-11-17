import FondHtn.FixedMethodsLemmas
import FondHtn.Prim.WeakMem
/-!
# Strong OD solvability of a primitive network as a game on executed-task sets

For a fixed primitive task network `tn`, `FOND.Problem.Win P tn D s` says that the rest of `tn`
after the tasks `D` have been executed can be solved strongly from the state `s`: either all
tasks are executed, or some task `t ∉ D` whose predecessors are all in `D` has an action
applicable in `s` such that every outcome is again winning with `insert t D`.

`FOND.Problem.win_iff_beliefSolvable`: `Win P tn D s ↔ BeliefSolvable (rest tn D) s`, so
`Win P tn ∅ P.init` is strong OD solvability of `tn` (`FOND.Problem.win_empty_iff`).
-/

namespace FOND

open HTN FOND.TaskNetwork

namespace Problem

variable {F A C I : Type} [DecidableEq I] (P : Problem F A C I) (tn : HTN.TaskNetwork I A C)

/-- The strong solvability game on the sets of executed tasks. -/
inductive Win : Finset I → Set F → Prop
  | done {D : Finset I} {s : Set F} (h : tn.T ⊆ D) : Win D s
  | step {D : Finset I} {s : Set F} {t : I} {a : A} (ht : t ∈ tn.T) (htD : t ∉ D)
      (hpred : ∀ t' ∈ tn.T, tn.ord t' t → t' ∈ D) (hα : tn.α t = Sum.inl a)
      (happ : (P.δ a).Applicable s) (hall : ∀ s' ∈ (P.δ a).outcomes s, Win (insert t D) s') :
      Win D s

variable {P tn}

theorem win_of_beliefSolvable : ∀ {tn' : HTN.TaskNetwork I A C} {s : Set F},
    P.BeliefSolvable tn' s → ∀ D, tn' = rest tn D → P.Win tn D s := by
  intro tn' s h
  induction h with
  | empty h =>
    intro D hD
    subst hD
    refine .done fun x hx => ?_
    by_contra hxD
    have : x ∈ (rest tn D).T := Finset.mem_sdiff.2 ⟨hx, hxD⟩
    rw [h] at this; simp at this
  | @step tn₁ s t a hu hα happ _ ih =>
    intro D hD
    subst hD
    obtain ⟨htT, hu2⟩ := hu
    have htT' := Finset.mem_sdiff.1 htT
    refine .step htT'.1 htT'.2 (fun t' ht' hord => ?_) hα happ fun s' hs' => ?_
    · by_contra hnd
      exact hu2 t' (Finset.mem_sdiff.2 ⟨ht', hnd⟩) ⟨hord, hnd⟩
    · exact ih s' hs' _ (rest_progress tn D t)

theorem beliefSolvable_of_win {D : Finset I} {s : Set F} (h : P.Win tn D s) :
    P.BeliefSolvable (rest tn D) s := by
  induction h with
  | done h =>
    refine .empty ?_
    show tn.T \ _ = ∅
    exact Finset.sdiff_eq_empty_iff_subset.2 h
  | @step D s t a ht htD hpred hα happ _ ih =>
    refine .step (t := t) (a := a) ⟨Finset.mem_sdiff.2 ⟨ht, htD⟩, ?_⟩ hα happ fun s' hs' => ?_
    · rintro t' ht' ⟨hord, hnd⟩
      exact hnd (hpred t' (Finset.mem_sdiff.1 ht').1 hord)
    · rw [rest_progress]; exact ih s' hs'

theorem win_iff_beliefSolvable (D : Finset I) (s : Set F) :
    P.Win tn D s ↔ P.BeliefSolvable (rest tn D) s :=
  ⟨beliefSolvable_of_win, fun h => win_of_beliefSolvable h D rfl⟩

theorem win_empty_iff (s : Set F) : P.Win tn ∅ s ↔ P.BeliefSolvable tn s := by
  rw [win_iff_beliefSolvable]
  constructor
  · intro h
    exact BeliefSolvable.congr P h ⟨by simp [rest], fun a _ b _ => by simp [rest], fun _ _ => rfl⟩
  · intro h
    exact BeliefSolvable.congr P h (sameOn_rest_empty tn)

/-- **Strong OD solvability of a primitive problem** as the game. -/
theorem strongODSolvable_iff_win (hp : P.tnI.IsPrimitive) :
    P.StrongODSolvable ↔ P.Win P.tnI ∅ P.init := by
  rw [strongODSolvable_iff_fmSolvableDB, win_empty_iff]
  constructor
  · rintro ⟨tn, hach, h⟩
    obtain rfl := (P.achievablePrimitive_iff_of_primitive hp).1 hach
    exact h
  · intro h
    exact ⟨P.tnI, (P.achievablePrimitive_iff_of_primitive hp).2 rfl, h⟩

end Problem

end FOND
