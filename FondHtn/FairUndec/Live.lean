import FondHtn.HardTR.WSafe
/-!
# From a fair policy to the live word game

The safe word game `FOND.HardTR.LSafe` keeps only the safety half of fairness.
**`FOND.FU.llive_of_fairWin`** keeps the liveness half as well: every position of the
self-supporting set lies in the (ranked) attractor `FOND.FU.LAttr` of the set, i.e. the empty
word is reachable by moves that keep all outcomes in the set.
-/

namespace FOND

namespace FU

open HTN HardTR

section Game

variable {A S : Type} (app : A → S → Prop) (outs : A → S → Set S)

/-- **The ranked attractor of the word game** relative to a set `R` of positions: accept, or a
move all of whose outcomes stay in `R`, one of them in the attractor of lower rank. -/
inductive LAttr (R : Set (Set (List A) × S)) : ℕ → Set (List A) × S → Prop
  | goal {n : ℕ} {L : Set (List A)} {s : S} (h : [] ∈ L) : LAttr R n (L, s)
  | move {n : ℕ} {L : Set (List A)} {s : S} (a : A) (happ : app a s)
      (hall : ∀ s' ∈ outs a s, ({w | a :: w ∈ L}, s') ∈ R) {s₀ : S} (hs₀ : s₀ ∈ outs a s)
      (h : LAttr R n ({w | a :: w ∈ L}, s₀)) : LAttr R (n + 1) (L, s)

/-- **The live word game**: a self-supporting set every position of which is in its
attractor. -/
def LLive (L : Set (List A)) (s : S) : Prop :=
  ∃ R : Set (Set (List A) × S), (L, s) ∈ R ∧ ∀ p ∈ R, (∃ w, w ∈ p.1) ∧ ∃ n, LAttr app outs R n p

variable {app outs}

theorem LAttr.mono {R : Set (Set (List A) × S)} {n : ℕ} {p : Set (List A) × S}
    (h : LAttr app outs R n p) : ∀ {n'}, n ≤ n' → LAttr app outs R n' p := by
  induction h with
  | goal h => intro n' _; exact .goal h
  | move a happ hall hs₀ _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .move a happ hall hs₀ (ih (by omega))

end Game

variable {F : Type} {A : Type} {C : Type} {I : Type}

/-- **A fair policy gives the live word game** on the refinements of the initial network. -/
theorem llive_of_fairWin [DecidableEq I] [Infinite I] {P : Problem F A C I} (hP : P.WF)
    (h : P.FairWin true P.tnI P.init) :
    LLive (fun a s => (P.δ a).Applicable s) (fun a s => (P.δ a).outcomes s)
      {as | (skelAt P P.tnI).domain.NetYield P.tnI as} P.init := by
  obtain ⟨Xs, -, hX0, hXa⟩ := h
  have hP0 : (skelAt P P.tnI).WF := ⟨hP.tnI, hP.methods⟩
  set Lπ : List A → Set (List A) := fun π => {as | (skelAt P P.tnI).domain.NetYield P.tnI (π ++ as)}
    with hLπ
  set R : Set (Set (List A) × Set F) := {p | ∃ tn π, Xs tn p.2 ∧
    (skelAt P P.tnI).ReachableNode ⟨P.init, tn, π⟩ ∧ p.1 = Lπ π} with hR
  have key : ∀ n tn s, P.FAttrH true Xs n tn s → ∀ π,
      (skelAt P P.tnI).ReachableNode ⟨P.init, tn, π⟩ →
      (∃ w, w ∈ Lπ π) ∧ LAttr (fun a s => (P.δ a).Applicable s) (fun a s => (P.δ a).outcomes s)
        R n (Lπ π, s) := by
    intro n tn s hA
    induction hA with
    | goal he =>
      intro π hr
      have hsol := HTN.Problem.isSolutionPlan_of_goalNode hP0 hr ⟨he, by
        intro f hf; simp [skelAt, Problem.skeleton] at hf⟩
      have hnil : [] ∈ Lπ π := by
        simpa [hLπ] using (HTN.Problem.isSolutionPlan_iff.1 hsol).1
      exact ⟨⟨[], hnil⟩, .goal hnil⟩
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
      obtain ⟨⟨w, hw⟩, hl⟩ := ih (π ++ [a]) hr'
      refine ⟨⟨a :: w, ?_⟩, .move a happ (fun s' hs' => ?_) hs₀ (by rw [hres]; exact hl)⟩
      · simpa [hLπ] using hw
      · rw [hres]; exact ⟨tn.progress t, π ++ [a], hall s' hs', hr', rfl⟩
    | @decomp n tn tn' s t m hu hd _ _ ih =>
      intro π hr
      obtain ⟨hw, hl⟩ := ih π (hr.tail (HTN.Problem.Step.decomp (hu rfl) hd))
      exact ⟨hw, hl.mono (by omega)⟩
  refine ⟨R, ⟨P.tnI, [], hX0, Relation.ReflTransGen.refl, by simp [hLπ]⟩, ?_⟩
  rintro ⟨L, s⟩ ⟨tn, π, hX, hr, rfl⟩
  obtain ⟨n, hn⟩ := hXa tn s hX
  obtain ⟨hw, hl⟩ := key n tn s hn π hr
  exact ⟨hw, n, hl⟩

end FU

end FOND
