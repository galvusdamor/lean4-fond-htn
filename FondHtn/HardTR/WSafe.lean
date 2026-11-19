import FondHtn.HardTR.WTrans
import FondHtn.MPStrong.CyclicGame
/-!
# CB22 Thm 5 (fair): from a fair policy to the safe word game

**`FOND.HardTR.lsafe_of_fairWin`**: if the progression fair game `FOND.Problem.FairWin true`
is won from the initial node, then the safe word game `FOND.HardTR.LSafe` is won on the
refinements of the initial network.  The self-supporting set is read off the fair game: the
nodes of its set `X` that are reachable in the skeleton, each with the residual language of the
word executed so far; the attractor of `X` provides a move (or acceptance) for each of them.
-/

namespace FOND

namespace HardTR

open HTN

variable {F : Type} {A : Type} {C : Type} {I : Type}

theorem lsafe_of_fairWin [DecidableEq I] [Infinite I] {P : Problem F A C I} (hP : P.WF)
    (h : P.FairWin true P.tnI P.init) :
    LSafe (fun a s => (P.δ a).Applicable s) (fun a s => (P.δ a).outcomes s)
      {as | (skelAt P P.tnI).domain.NetYield P.tnI as} P.init := by
  obtain ⟨Xs, -, hX0, hXa⟩ := h
  have hP0 : (skelAt P P.tnI).WF := ⟨hP.tnI, hP.methods⟩
  set Lπ : List A → Set (List A) := fun π => {as | (skelAt P P.tnI).domain.NetYield P.tnI (π ++ as)}
    with hLπ
  set R : Set (Set (List A) × Set F) := {p | ∃ tn π, Xs tn p.2 ∧
    (skelAt P P.tnI).ReachableNode ⟨P.init, tn, π⟩ ∧ p.1 = Lπ π} with hR
  have key : ∀ n tn s, P.FAttrH true Xs n tn s → ∀ π,
      (skelAt P P.tnI).ReachableNode ⟨P.init, tn, π⟩ →
      (∃ w, w ∈ Lπ π) ∧ ([] ∈ Lπ π ∨ ∃ a, (P.δ a).Applicable s ∧
        ∀ s' ∈ (P.δ a).outcomes s, ({w | a :: w ∈ Lπ π}, s') ∈ R) := by
    intro n tn s hA
    induction hA with
    | goal he =>
      intro π hr
      have hsol := HTN.Problem.isSolutionPlan_of_goalNode hP0 hr ⟨he, by
        intro f hf; simp [skelAt, Problem.skeleton] at hf⟩
      have hnil : [] ∈ Lπ π := by
        simpa [hLπ] using (HTN.Problem.isSolutionPlan_iff.1 hsol).1
      exact ⟨⟨[], hnil⟩, Or.inl hnil⟩
    | @prim n tn s t a hu hα happ hall s₀ hs₀ _ ih =>
      intro π hr
      have hstep : (skelAt P P.tnI).Step ⟨P.init, tn, π⟩ ⟨P.init, tn.progress t, π ++ [a]⟩ := by
        have h0 := HTN.Problem.Step.prog (P := skelAt P P.tnI) (s := P.init) (π := π) hu hα
          (by intro f hf; simp [skelAt, Problem.skeleton] at hf)
        have htr : (skelAt P P.tnI).transition a P.init = P.init := by
          simp [ActionModel.transition, skelAt, Problem.skeleton]
        rwa [htr] at h0
      have hr' := hr.tail hstep
      have hres : {w | a :: w ∈ Lπ π} = Lπ (π ++ [a]) := by
        ext w; simp [hLπ]
      obtain ⟨⟨w, hw⟩, -⟩ := ih (π ++ [a]) hr'
      refine ⟨⟨a :: w, ?_⟩, Or.inr ⟨a, happ, fun s' hs' => ⟨tn.progress t, π ++ [a], hall s' hs', hr', hres⟩⟩⟩
      simpa [hLπ] using hw
    | @decomp n tn tn' s t m hu hd _ _ ih =>
      intro π hr
      exact ih π (hr.tail (HTN.Problem.Step.decomp (hu rfl) hd))
  refine ⟨R, ⟨P.tnI, [], hX0, Relation.ReflTransGen.refl, by simp [hLπ]⟩, ?_⟩
  rintro ⟨L, s⟩ ⟨tn, π, hX, hr, rfl⟩
  obtain ⟨n, hn⟩ := hXa tn s hX
  exact key n tn s hn π hr

end HardTR

end FOND
