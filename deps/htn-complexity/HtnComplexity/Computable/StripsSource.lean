import HtnPlanning.Core.ReachableLabels
import HtnPlanning.Interleave.StripsChain
import HtnPlanning.Computable.Classes
/-!
# Solvability of an arbitrary described STRIPS problem

`HtnComplexity/Computable/StripsTarget.lean` characterises the solvability of the
*canonical* STRIPS descriptions a compilation produces.  A compilation *out of* the class
`STRIPS` has to deal with an arbitrary description of the class, and this file characterises
its solvability:

`HTN.Syn.solvable_isStrips_iff` — a described STRIPS problem is solvable exactly when

* the domain description has a method with an empty body — without one no refinement of the
  initial task network is primitive, since every other body reinserts the compound task; and
* there is a classical plan over the actions the hierarchy offers
  (`HTN.Syn.DomDesc.stepActs`) that is applicable in the initial state and reaches the goal.

The two directions use the generic invariants of `HtnPlanning/Core/ReachableLabels.lean` and
the chain construction of `HtnPlanning/Interleave/StripsChain.lean` respectively.
-/

namespace HTN

namespace Syn

/-- **The actions a domain description offers**: the actions occurring in the body of one of
its methods. -/
def DomDesc.stepActs (d : DomDesc) : List ℕ := d.methods.flatMap fun e => e.2.actionNames

/-- **The domain description has a method with an empty body.** -/
def DomDesc.HasEmptyMethod (d : DomDesc) : Prop := ∃ e ∈ d.methods, e.2.ids = []

theorem DomDesc.mem_stepActs {d : DomDesc} {a : ℕ} :
    a ∈ d.stepActs ↔ ∃ e ∈ d.methods, a ∈ e.2.actionNames := by
  simp [DomDesc.stepActs]

section

variable {d : DomDesc} {q : InstDesc}

/-- The described initial network of a STRIPS instance orders nothing. -/
theorem InstDesc.IsStrips.not_ord (hq : q.IsStrips) (x y : ℕ) :
    ¬ q.tnI.toTaskNetwork.ord x y := by
  obtain ⟨t, hT, -⟩ := hq
  intro h
  have hwf := q.tnI.toTaskNetwork_wf
  have hx : x ∈ q.tnI.toTaskNetwork.T := hwf.mem_left h
  have hy : y ∈ q.tnI.toTaskNetwork.T := hwf.mem_right h
  rw [hT] at hx hy
  simp only [Finset.mem_singleton] at hx hy
  have hxy : x = y := hx.trans hy.symm
  subst hxy
  exact hwf.irrefl _ h

/-- Every action label of a listed method's body is an action the domain offers. -/
theorem stepActs_of_label {e : MethodDesc} (he : e ∈ d.methods) {i a : ℕ}
    (hi : i ∈ e.2.toTaskNetwork.T) (ha : e.2.toTaskNetwork.α i = Sum.inl a) :
    a ∈ d.stepActs :=
  DomDesc.mem_stepActs.2 ⟨e, he, TnDesc.mem_actionNames.2 ⟨i, by simpa using hi, ha⟩⟩

/-- **Only the actions the hierarchy offers occur in a refinement of the initial network.** -/
theorem labels_stepActs (hq : q.IsStrips) {tn : TaskNetwork ℕ ℕ ℕ}
    (hreach : (problem d q).Reachable tn) {i a : ℕ} (hi : i ∈ tn.T) (ha : tn.α i = Sum.inl a) :
    a ∈ d.stepActs := by
  have hlab := DecomposesTo.labels_mem (M := (problem d q).methods)
    (L := {x : ℕ ⊕ ℕ | ∀ b, x = Sum.inl b → b ∈ d.stepActs}) hreach ?_ ?_
  · exact hlab i hi a ha
  · obtain ⟨t, hT, hα⟩ := hq
    intro x hx b hb
    rw [problem_tnI, hT] at hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    rw [problem_tnI] at hb
    rw [hα] at hb
    exact absurd hb (by simp)
  · rintro m ⟨e, he, rfl⟩ x hx b hb
    exact stepActs_of_label he hx hb

/-- **A described STRIPS problem with no empty method body is unsolvable.** -/
theorem hasEmptyMethod_of_solvable (hd : d.IsStrips) (hq : q.IsStrips) (h : Solvable d q) :
    d.HasEmptyMethod := by
  obtain ⟨tn, hreach, hprim, -⟩ := h
  obtain ⟨t, hT, hα⟩ := hq
  obtain ⟨m, ⟨e, he, rfl⟩, hnc⟩ :=
    DecomposesTo.exists_method_nocompound (M := (problem d q).methods) hreach
      ⟨t, by rw [problem_tnI, hT]; simp, 0, by rw [problem_tnI]; exact hα⟩ hprim
  refine ⟨e, he, ?_⟩
  rcases (hd e he).2 with hempty | ⟨t₁, t₂, -, hT₂, -, hα₂, -⟩
  · have : e.2.ids.toFinset = ∅ := hempty
    simpa using this
  · refine absurd hα₂ (hnc t₂ ?_ 0)
    show t₂ ∈ e.2.toTaskNetwork.T
    rw [hT₂]
    simp

/-- **Solvability of an arbitrary described STRIPS problem.** -/
theorem solvable_isStrips_iff (hd : d.IsStrips) (hq : q.IsStrips) :
    Solvable d q ↔ d.HasEmptyMethod ∧ ∃ as : List ℕ, (∀ a ∈ as, a ∈ d.stepActs) ∧
      d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList} := by
  constructor
  · intro h
    refine ⟨hasEmptyMethod_of_solvable hd hq h, ?_⟩
    obtain ⟨tn, hreach, -, l, as, hlin, hseq, happ, hgoal⟩ := h
    refine ⟨as, fun a ha => ?_, happ, hgoal⟩
    -- the actions of the plan are labels of the tasks of `tn`
    have hmem : Sum.inl a ∈ l.map tn.α := by
      rw [show l.map tn.α = as.map Sum.inl from hseq]
      exact List.mem_map_of_mem ha
    obtain ⟨i, hi, hia⟩ := List.mem_map.1 hmem
    exact labels_stepActs hq hreach ((hlin.2.1 i).1 hi) hia
  · rintro ⟨⟨e₀, he₀, hnil⟩, as, hus, happ, hgoal⟩
    have hnord := InstDesc.IsStrips.not_ord hq
    obtain ⟨t, hT, hα⟩ := hq
    -- the initial network is an open chain for the empty plan
    have hchain : StripsChain.IsOpenChain (A := ℕ) 0 q.tnI.toTaskNetwork [] [] t :=
      StripsChain.isOpenChain_single hT hα hnord
    -- a step body for every action the hierarchy offers
    have hstep : ∀ a ∈ {a : ℕ | a ∈ d.stepActs}, ∃ nt,
        (⟨0, nt⟩ : Method ℕ ℕ ℕ) ∈ (problem d q).methods ∧ StripsChain.IsStepBody nt 0 a := by
      intro a ha
      obtain ⟨e, he, hae⟩ := DomDesc.mem_stepActs.1 ha
      obtain ⟨i, hi, hia'⟩ := TnDesc.mem_actionNames.1 hae
      have hia : e.2.toTaskNetwork.α i = Sum.inl a := hia'
      have hiT : i ∈ e.2.toTaskNetwork.T := by simpa using hi
      have he1 : e.1 = 0 := (hd e he).1
      rcases (hd e he).2 with hempty | ⟨t₁, t₂, hne, hT₂, hprim₁, hα₂, hord⟩
      · rw [hempty] at hiT
        exact absurd hiT (by simp)
      · have hit : i = t₁ := by
          have : i = t₁ ∨ i = t₂ := by
            have := hT₂ ▸ hiT
            simpa using this
          rcases this with h | rfl
          · exact h
          · rw [hα₂] at hia
            exact absurd hia (by simp)
        subst hit
        refine ⟨e.2.toTaskNetwork, ?_, i, t₂, hne, hT₂, hia, hα₂, hord⟩
        exact ⟨e, he, by rw [Method.mk.injEq]; exact ⟨he1, rfl⟩⟩
    -- the empty body
    have hemptyT : e₀.2.toTaskNetwork.T = ∅ := by
      show e₀.2.ids.toFinset = ∅
      rw [hnil]
      rfl
    have hemptyMem : (⟨0, e₀.2.toTaskNetwork⟩ : Method ℕ ℕ ℕ) ∈ (problem d q).methods :=
      ⟨e₀, he₀, by rw [Method.mk.injEq]; exact ⟨(hd e₀ he₀).1, rfl⟩⟩
    obtain ⟨tn, hreach, hprim, l, hlin, hseq⟩ :=
      StripsChain.exists_solution_of_plan (M := (problem d q).methods) hchain
        (Acts := {a : ℕ | a ∈ d.stepActs}) hstep hemptyMem (TnDesc.toTaskNetwork_wf _)
        hemptyT hus
    exact ⟨tn, hreach, hprim, l, as, hlin, hseq, happ, hgoal⟩

end

end Syn

end HTN
