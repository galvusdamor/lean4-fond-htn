import HtnComplexity.Computable.MergeDom
/-!
# The executable action sequences of the merge domain

The domain description `HTN.Merge.mergeDom`
(`HtnComplexity/Computable/MergeDom.lean`) is a one-bit buffer: the action `aName b`
writes the bit `b` into an empty buffer, the action `bName b` empties a buffer holding `b`.
This file computes its executable sequences: started in the empty buffer `{0}`, an action
sequence over the four actions of the domain is executable and ends with an empty buffer
exactly when it is an alternation

    aName c₁, bName c₁, aName c₂, bName c₂, …

of writes and matching reads (`HTN.Merge.exec_iff_pairsOf`).  Everything here is elementary
reasoning about the four actions; the combinatorial part is in
`HtnComplexity/Computable/MergeCorrect.lean`.
-/

namespace HTN

namespace Merge

open Syn

/-! ### The two kinds of state -/

/-- The state with an empty buffer. -/
def sE : Set ℕ := {0}

/-- The state whose buffer holds the bit `b`. -/
def sF (b : Bool) : Set ℕ := {1, bName b}

theorem sE_eq : ({f | f ∈ [0]} : Set ℕ) = sE := by ext x; simp [sE]

/-! ### The action model -/

@[simp] theorem prec_aName (b : Bool) : semDom.prec (aName b) = ({0} : Set ℕ) := by
  cases b <;> (ext x; simp [semDom, aName, DomDesc.prec, DomDesc.actions, mergeDom, List.lookup_cons])

@[simp] theorem add_aName (b : Bool) : semDom.add (aName b) = ({1, bName b} : Set ℕ) := by
  cases b <;> (ext x; simp [semDom, aName, bName, DomDesc.add, DomDesc.actions, mergeDom, List.lookup_cons])

@[simp] theorem del_aName (b : Bool) : semDom.del (aName b) = ({0, bName (!b)} : Set ℕ) := by
  cases b <;> (ext x; simp [semDom, aName, bName, DomDesc.del, DomDesc.actions, mergeDom, List.lookup_cons])

@[simp] theorem prec_bName (b : Bool) : semDom.prec (bName b) = ({1, bName b} : Set ℕ) := by
  cases b <;> (ext x; simp [semDom, bName, DomDesc.prec, DomDesc.actions, mergeDom, List.lookup_cons])

@[simp] theorem add_bName (b : Bool) : semDom.add (bName b) = ({0} : Set ℕ) := by
  cases b <;> (ext x; simp [semDom, bName, DomDesc.add, DomDesc.actions, mergeDom, List.lookup_cons])

@[simp] theorem del_bName (b : Bool) : semDom.del (bName b) = ({1, bName b} : Set ℕ) := by
  cases b <;> (ext x; simp [semDom, bName, DomDesc.del, DomDesc.actions, mergeDom, List.lookup_cons])

/-! ### The four transitions -/

theorem applicable_aName (b : Bool) : semDom.Applicable (aName b) sE := by
  intro x hx; simpa [sE] using hx

theorem transition_aName (b : Bool) : semDom.transition (aName b) sE = sF b := by
  cases b <;> (ext x; simp [ActionModel.transition, sE, sF, bName]) <;> tauto

theorem applicable_bName (b : Bool) : semDom.Applicable (bName b) (sF b) := by
  intro x hx; simpa [sF] using hx

theorem transition_bName (b : Bool) : semDom.transition (bName b) (sF b) = sE := by
  ext x; simp [ActionModel.transition, sE, sF]

theorem not_applicable_aName_sF (b c : Bool) : ¬ semDom.Applicable (aName c) (sF b) := by
  intro h
  have : (0 : ℕ) ∈ sF b := h (by simp)
  cases b <;> simp [sF, bName] at this

theorem not_applicable_bName_sE (b : Bool) : ¬ semDom.Applicable (bName b) sE := by
  intro h
  have : (1 : ℕ) ∈ sE := h (by simp)
  simp [sE] at this

theorem eq_of_applicable_bName {b c : Bool} (h : semDom.Applicable (bName c) (sF b)) : c = b := by
  have : bName c ∈ sF b := h (by simp)
  cases b <;> cases c <;> simp_all [sF, bName]

/-! ### The four actions are the only ones that matter -/

/-- The names of the four actions of the domain. -/
theorem lt_four_cases {x : ℕ} (h : x < 4) :
    (∃ b, x = aName b) ∨ ∃ b, x = bName b := by
  interval_cases x
  · exact Or.inl ⟨false, rfl⟩
  · exact Or.inl ⟨true, rfl⟩
  · exact Or.inr ⟨false, rfl⟩
  · exact Or.inr ⟨true, rfl⟩

/-! ### The executable sequences -/

/-- The alternation of writes and matching reads for a word. -/
def pairsOf (cs : List Bool) : List ℕ := cs.flatMap fun c => [aName c, bName c]

@[simp] theorem pairsOf_nil : pairsOf [] = [] := rfl

@[simp] theorem pairsOf_cons (c : Bool) (cs : List Bool) :
    pairsOf (c :: cs) = aName c :: bName c :: pairsOf cs := rfl

/-- An alternation of writes and matching reads is executable and empties the buffer. -/
theorem exec_pairsOf (cs : List Bool) :
    semDom.SeqApplicable (pairsOf cs) sE ∧ semDom.transitionSeq (pairsOf cs) sE = sE := by
  induction cs with
  | nil => exact ⟨trivial, rfl⟩
  | cons c cs ih =>
      rw [pairsOf_cons]
      refine ⟨⟨applicable_aName c, ?_⟩, ?_⟩
      · rw [transition_aName]
        exact ⟨applicable_bName c, by rw [transition_bName]; exact ih.1⟩
      · rw [ActionModel.transitionSeq_cons, transition_aName, ActionModel.transitionSeq_cons,
          transition_bName]
        exact ih.2

/-- The auxiliary induction for `HTN.Merge.exists_pairsOf_of_exec`. -/
theorem exists_pairsOf_aux : ∀ (n : ℕ) (as : List ℕ), as.length ≤ n → (∀ x ∈ as, x < 4) →
    semDom.SeqApplicable as sE → sE ⊆ semDom.transitionSeq as sE → ∃ cs, as = pairsOf cs := by
  intro n
  induction n with
  | zero =>
      intro as hlen _ _ _
      rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)]
      exact ⟨[], rfl⟩
  | succ n ih =>
      rintro (_ | ⟨x, _ | ⟨y, rest⟩⟩) hlen hmem happ hgoal
      · exact ⟨[], rfl⟩
      · -- a single action cannot empty the buffer again
        exfalso
        rcases lt_four_cases (hmem x (by simp)) with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · have : sE ⊆ sF b := by
            simpa [transition_aName] using hgoal
          have h0 : (0 : ℕ) ∈ sF b := this (by simp [sE])
          cases b <;> simp [sF, bName] at h0
        · exact not_applicable_bName_sE b happ.1
      · rcases lt_four_cases (hmem x (by simp)) with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · -- a write, which must be followed by the matching read
          have happ2 : semDom.SeqApplicable (y :: rest) (sF b) := by
            simpa [transition_aName] using happ.2
          rcases lt_four_cases (hmem y (by simp)) with ⟨c, rfl⟩ | ⟨c, rfl⟩
          · exact absurd happ2.1 (not_applicable_aName_sF b c)
          · obtain rfl := eq_of_applicable_bName happ2.1
            have happ3 : semDom.SeqApplicable rest sE := by
              simpa [transition_bName] using happ2.2
            have hgoal3 : sE ⊆ semDom.transitionSeq rest sE := by
              have : semDom.transitionSeq (aName c :: bName c :: rest) sE =
                  semDom.transitionSeq rest sE := by
                rw [ActionModel.transitionSeq_cons, transition_aName,
                  ActionModel.transitionSeq_cons, transition_bName]
              rwa [this] at hgoal
            obtain ⟨cs, rfl⟩ := ih rest (by simp at hlen; omega)
              (fun z hz => hmem z (by simp [hz])) happ3 hgoal3
            exact ⟨c :: cs, rfl⟩
        · exact absurd happ.1 (not_applicable_bName_sE b)

/-- **An executable sequence over the four actions is an alternation of writes and matching
reads.** -/
theorem exists_pairsOf_of_exec {as : List ℕ} (hmem : ∀ x ∈ as, x < 4)
    (happ : semDom.SeqApplicable as sE) (hgoal : sE ⊆ semDom.transitionSeq as sE) :
    ∃ cs, as = pairsOf cs :=
  exists_pairsOf_aux as.length as le_rfl hmem happ hgoal

/-- **The executable sequences of the merge domain.** -/
theorem exec_iff_pairsOf {as : List ℕ} (hmem : ∀ x ∈ as, x < 4) :
    (semDom.SeqApplicable as sE ∧ sE ⊆ semDom.transitionSeq as sE) ↔ ∃ cs, as = pairsOf cs := by
  constructor
  · rintro ⟨happ, hgoal⟩
    exact exists_pairsOf_of_exec hmem happ hgoal
  · rintro ⟨cs, rfl⟩
    obtain ⟨happ, hst⟩ := exec_pairsOf cs
    exact ⟨happ, by rw [hst]⟩

end Merge

end HTN
