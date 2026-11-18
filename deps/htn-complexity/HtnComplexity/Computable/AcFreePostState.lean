import HtnComplexity.Computable.AcFreePost
/-!
# What the verification phase does to the state

`HtnComplexity/Computable/AcFreePost.lean` computes the *refinements* of the compound task
`tPost`: one check action and one earn action per fact of the vocabulary.  This file computes
their effect, and assembles the two into

> `HTN.Syn.AcFree.post_iff` — a refinement of `tPost` is executable in the state `s` and
> establishes the set `G` exactly when
>
> * for every `v` of the vocabulary, either `¬v⁰` holds in `s`, or `v⁰` holds and `v` is
>   *licensed*, and
> * every fact of `G` either already holds in `s`, or is the receipt `fRes v` of a fact `v` of
>   the vocabulary which holds in copy `2`.

The check actions are effect free, so they only constrain `s`; the earn actions are the only
ones with an effect, and the best a plan can do is to earn every receipt it can.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

variable {V : List ℕ} {d₀ : DomDesc}

/-! ### The receipts a state lets the phase earn -/

/-- The receipts the earn actions of `W` can produce in the state `s`. -/
def earned (W : List ℕ) (s : Set ℕ) : Set ℕ := {f | ∃ v ∈ W, f = fRes v ∧ fPos v 2 ∈ s}

lemma earned_mono_left {W W' : List ℕ} (h : ∀ v ∈ W, v ∈ W') (s : Set ℕ) :
    earned W s ⊆ earned W' s := by
  rintro f ⟨v, hv, rfl, hp⟩
  exact ⟨v, h v hv, rfl, hp⟩

lemma earned_mono_right (W : List ℕ) {s s' : Set ℕ} (h : s ⊆ s') :
    earned W s ⊆ earned W s' := by
  rintro f ⟨v, hv, rfl, hp⟩
  exact ⟨v, hv, rfl, h hp⟩

/-- A receipt is not a fact of the acyclic construction. -/
lemma fPos_ne_fRes (v i w : ℕ) : fPos v i ≠ fRes w := fun h =>
  not_baseFact_fRes w (h ▸ baseFact_fPos v i)

/-! ### The effect of a single action of the phase -/

variable (V d₀)

lemma transition_chkN (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) (s : Set ℕ) :
    (wrapDom V d₀).toDomain.transition (aChkN v) s = s := by
  show (s \ (wrapDom V d₀).del (aChkN v)) ∪ (wrapDom V d₀).add (aChkN v) = s
  rw [del_chkN V d₀ hshape hv, add_chkN V d₀ hshape hv]
  simp

lemma transition_chkP (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) (s : Set ℕ) :
    (wrapDom V d₀).toDomain.transition (aChkP v) s = s := by
  show (s \ (wrapDom V d₀).del (aChkP v)) ∪ (wrapDom V d₀).add (aChkP v) = s
  rw [del_chkP V d₀ hshape hv, add_chkP V d₀ hshape hv]
  simp

lemma transition_earn (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) (s : Set ℕ) :
    (wrapDom V d₀).toDomain.transition (aEarn v) s = s ∪ {fRes v} := by
  show (s \ (wrapDom V d₀).del (aEarn v)) ∪ (wrapDom V d₀).add (aEarn v) = _
  rw [del_earn V d₀ hshape hv, add_earn V d₀ hshape hv]
  simp

lemma transition_skip (hshape : BaseShaped d₀) (s : Set ℕ) :
    (wrapDom V d₀).toDomain.transition aSkip s = s := by
  show (s \ (wrapDom V d₀).del aSkip) ∪ (wrapDom V d₀).add aSkip = s
  rw [del_skip V d₀ hshape, add_skip V d₀ hshape]
  simp

lemma applicable_chkN (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) {s : Set ℕ} :
    (wrapDom V d₀).toDomain.Applicable (aChkN v) s ↔ fNeg v 0 ∈ s := by
  show (wrapDom V d₀).prec (aChkN v) ⊆ s ↔ _
  rw [prec_chkN V d₀ hshape hv]
  simp

lemma applicable_chkP (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) {s : Set ℕ} :
    (wrapDom V d₀).toDomain.Applicable (aChkP v) s ↔ fPos v 0 ∈ s ∧ fLic v ∈ s := by
  show (wrapDom V d₀).prec (aChkP v) ⊆ s ↔ _
  rw [prec_chkP V d₀ hshape hv]
  constructor
  · intro h; exact ⟨h (by simp), h (by simp)⟩
  · rintro ⟨h1, h2⟩ f hf
    rcases hf with rfl | rfl
    · exact h1
    · exact h2

lemma applicable_earn (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) {s : Set ℕ} :
    (wrapDom V d₀).toDomain.Applicable (aEarn v) s ↔ fPos v 2 ∈ s := by
  show (wrapDom V d₀).prec (aEarn v) ⊆ s ↔ _
  rw [prec_earn V d₀ hshape hv]
  simp

lemma applicable_skip (hshape : BaseShaped d₀) {s : Set ℕ} :
    (wrapDom V d₀).toDomain.Applicable aSkip s := by
  show (wrapDom V d₀).prec aSkip ⊆ s
  rw [prec_skip V d₀ hshape]
  exact Set.empty_subset s

variable {V d₀}

/-! ### The chain of check actions -/

/-- A chain of check actions has no effect, and is executable only in a state that passes all
the checks. -/
theorem chkChain_state (hshape : BaseShaped d₀) (s : Set ℕ) {W as : List ℕ}
    (h : List.Forall₂ (fun v a => a = aChkN v ∨ a = aChkP v) W as) :
    (∀ v ∈ W, v ∈ V) →
      (wrapDom V d₀).toDomain.transitionSeq as s = s ∧
        ((wrapDom V d₀).toDomain.SeqApplicable as s →
          ∀ v ∈ W, fNeg v 0 ∈ s ∨ (fPos v 0 ∈ s ∧ fLic v ∈ s)) := by
  induction h with
  | nil => intro _; exact ⟨rfl, fun _ v hv => absurd hv (by simp)⟩
  | @cons v a W as hva hrest ih =>
      intro hW
      have hvV : v ∈ V := hW v (by simp)
      have hW' : ∀ w ∈ W, w ∈ V := fun w hw => hW w (by simp [hw])
      obtain ⟨hts, hcond⟩ := ih hW'
      have hstep : (wrapDom V d₀).toDomain.transition a s = s := by
        rcases hva with rfl | rfl
        · exact transition_chkN V d₀ hshape hvV s
        · exact transition_chkP V d₀ hshape hvV s
      refine ⟨by rw [ActionModel.transitionSeq_cons, hstep, hts], ?_⟩
      intro happ
      rw [ActionModel.seqApplicable_cons, hstep] at happ
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw'
      · rcases hva with rfl | rfl
        · exact Or.inl ((applicable_chkN V d₀ hshape hvV).1 happ.1)
        · exact Or.inr ((applicable_chkP V d₀ hshape hvV).1 happ.1)
      · exact hcond happ.2 w hw'

/-- In a state that passes all the checks there is an executable chain of check actions. -/
theorem chkChain_exists (hshape : BaseShaped d₀) {W : List ℕ} (hW : ∀ v ∈ W, v ∈ V)
    (s : Set ℕ) (hc : ∀ v ∈ W, fNeg v 0 ∈ s ∨ (fPos v 0 ∈ s ∧ fLic v ∈ s)) :
    ∃ as, List.Forall₂ (fun v a => a = aChkN v ∨ a = aChkP v) W as ∧
      (wrapDom V d₀).toDomain.SeqApplicable as s ∧
      (wrapDom V d₀).toDomain.transitionSeq as s = s := by
  induction W with
  | nil => exact ⟨[], List.Forall₂.nil, trivial, rfl⟩
  | cons v W ih =>
      have hvV : v ∈ V := hW v (by simp)
      obtain ⟨as, hf, happ, hts⟩ :=
        ih (fun w hw => hW w (by simp [hw])) (fun w hw => hc w (by simp [hw]))
      rcases hc v (by simp) with hn | hp
      · refine ⟨aChkN v :: as, List.Forall₂.cons (Or.inl rfl) hf, ?_, ?_⟩
        · rw [ActionModel.seqApplicable_cons, transition_chkN V d₀ hshape hvV]
          exact ⟨(applicable_chkN V d₀ hshape hvV).2 hn, happ⟩
        · rw [ActionModel.transitionSeq_cons, transition_chkN V d₀ hshape hvV, hts]
      · refine ⟨aChkP v :: as, List.Forall₂.cons (Or.inr rfl) hf, ?_, ?_⟩
        · rw [ActionModel.seqApplicable_cons, transition_chkP V d₀ hshape hvV]
          exact ⟨(applicable_chkP V d₀ hshape hvV).2 hp, happ⟩
        · rw [ActionModel.transitionSeq_cons, transition_chkP V d₀ hshape hvV, hts]

/-! ### The chain of earn actions -/

/-- A chain of earn actions can only add receipts a state lets it earn. -/
theorem earnChain_sound (hshape : BaseShaped d₀) {W as : List ℕ}
    (h : List.Forall₂ (fun v a => a = aEarn v ∨ a = aSkip) W as) :
    ∀ s : Set ℕ, (∀ v ∈ W, v ∈ V) → (wrapDom V d₀).toDomain.SeqApplicable as s →
      (wrapDom V d₀).toDomain.transitionSeq as s ⊆ s ∪ earned W s := by
  induction h with
  | nil => intro s _ _; exact Set.subset_union_left
  | @cons v a W as hva hrest ih =>
      intro s hW happ
      have hvV : v ∈ V := hW v (by simp)
      have hW' : ∀ w ∈ W, w ∈ V := fun w hw => hW w (by simp [hw])
      have hsub : earned W s ⊆ earned (v :: W) s :=
        earned_mono_left (fun w hw => by simp [hw]) s
      rcases hva with rfl | rfl
      · have hp : fPos v 2 ∈ s := by
          rw [ActionModel.seqApplicable_cons] at happ
          exact (applicable_earn V d₀ hshape hvV).1 happ.1
        have hstep : (wrapDom V d₀).toDomain.transition (aEarn v) s = s ∪ {fRes v} :=
          transition_earn V d₀ hshape hvV s
        rw [ActionModel.seqApplicable_cons, hstep] at happ
        rw [ActionModel.transitionSeq_cons, hstep]
        refine (ih (s ∪ {fRes v}) hW' happ.2).trans ?_
        rintro f (hf | hf)
        · rcases hf with hf | hf
          · exact Or.inl hf
          · exact Or.inr ⟨v, by simp, hf, hp⟩
        · obtain ⟨w, hw, rfl, hpw⟩ := hf
          refine Or.inr ⟨w, by simp [hw], rfl, ?_⟩
          rcases hpw with hpw | hpw
          · exact hpw
          · exact absurd (Set.mem_singleton_iff.1 hpw) (fPos_ne_fRes w 2 v)
      · have hstep : (wrapDom V d₀).toDomain.transition aSkip s = s :=
          transition_skip V d₀ hshape s
        rw [ActionModel.seqApplicable_cons, hstep] at happ
        rw [ActionModel.transitionSeq_cons, hstep]
        exact (ih s hW' happ.2).trans (Set.union_subset_union_right _ hsub)

/-- Every receipt a state lets the phase earn is earned by some executable chain of earn
actions. -/
theorem earnChain_exists (hshape : BaseShaped d₀) {W : List ℕ} (hW : ∀ v ∈ W, v ∈ V) :
    ∀ s : Set ℕ, ∃ as, List.Forall₂ (fun v a => a = aEarn v ∨ a = aSkip) W as ∧
      (wrapDom V d₀).toDomain.SeqApplicable as s ∧
      s ∪ earned W s ⊆ (wrapDom V d₀).toDomain.transitionSeq as s := by
  classical
  induction W with
  | nil =>
      intro s
      refine ⟨[], List.Forall₂.nil, trivial, ?_⟩
      rintro f (hf | ⟨v, hv, -⟩)
      · exact hf
      · exact absurd hv (by simp)
  | cons v W ih =>
      intro s
      have hvV : v ∈ V := hW v (by simp)
      have hW' : ∀ w ∈ W, w ∈ V := fun w hw => hW w (by simp [hw])
      by_cases hp : fPos v 2 ∈ s
      · obtain ⟨as, hf, happ, hsub⟩ := ih hW' (s ∪ {fRes v})
        have hstep : (wrapDom V d₀).toDomain.transition (aEarn v) s = s ∪ {fRes v} :=
          transition_earn V d₀ hshape hvV s
        refine ⟨aEarn v :: as, List.Forall₂.cons (Or.inl rfl) hf, ?_, ?_⟩
        · rw [ActionModel.seqApplicable_cons, hstep]
          exact ⟨(applicable_earn V d₀ hshape hvV).2 hp, happ⟩
        · rw [ActionModel.transitionSeq_cons, hstep]
          refine subset_trans ?_ hsub
          rintro f (hf | ⟨w, hw, rfl, hpw⟩)
          · exact Or.inl (Or.inl hf)
          · rcases List.mem_cons.1 hw with rfl | hw'
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨w, hw', rfl, Or.inl hpw⟩
      · obtain ⟨as, hf, happ, hsub⟩ := ih hW' s
        have hstep : (wrapDom V d₀).toDomain.transition aSkip s = s :=
          transition_skip V d₀ hshape s
        refine ⟨aSkip :: as, List.Forall₂.cons (Or.inr rfl) hf, ?_, ?_⟩
        · rw [ActionModel.seqApplicable_cons, hstep]
          exact ⟨applicable_skip V d₀ hshape, happ⟩
        · rw [ActionModel.transitionSeq_cons, hstep]
          refine subset_trans ?_ hsub
          rintro f (hf | ⟨w, hw, rfl, hpw⟩)
          · exact Or.inl hf
          · rcases List.mem_cons.1 hw with rfl | hw'
            · exact absurd hpw hp
            · exact Or.inr ⟨w, hw', rfl, hpw⟩

/-! ### The verification phase -/

/-- **What the verification phase achieves.**  A refinement of `tPost` is executable in the
state `s` and establishes the set `G` exactly when `s` passes every check and every fact of `G`
either already holds or is a receipt the state lets the phase earn. -/
theorem post_iff (hshape : BaseShaped d₀) {s G : Set ℕ} :
    (∃ as, (wrapDom V d₀).toDomain.YieldSeq [Sum.inr tPost] as ∧
        (wrapDom V d₀).toDomain.SeqApplicable as s ∧
        G ⊆ (wrapDom V d₀).toDomain.transitionSeq as s) ↔
      (∀ v ∈ V, fNeg v 0 ∈ s ∨ (fPos v 0 ∈ s ∧ fLic v ∈ s)) ∧ G ⊆ s ∪ earned V s := by
  constructor
  · rintro ⟨as, hy, happ, hg⟩
    obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := (yieldSeq_tPost hshape).1 hy
    obtain ⟨hts, hcond⟩ := chkChain_state hshape s h₁ (fun _ hv => hv)
    rw [ActionModel.seqApplicable_append, hts] at happ
    rw [ActionModel.transitionSeq_append, hts] at hg
    exact ⟨hcond happ.1, hg.trans (earnChain_sound hshape h₂ s (fun _ hv => hv) happ.2)⟩
  · rintro ⟨hcond, hg⟩
    obtain ⟨as₁, hf₁, happ₁, hts₁⟩ := chkChain_exists hshape (fun _ hv => hv) s hcond
    obtain ⟨as₂, hf₂, happ₂, hsub₂⟩ := earnChain_exists hshape (fun _ hv => hv) s
    refine ⟨as₁ ++ as₂, (yieldSeq_tPost hshape).2 ⟨as₁, as₂, rfl, hf₁, hf₂⟩, ?_, ?_⟩
    · rw [ActionModel.seqApplicable_append, hts₁]
      exact ⟨happ₁, happ₂⟩
    · rw [ActionModel.transitionSeq_append, hts₁]
      exact hg.trans hsub₂

end AcFree

end Syn

end HTN
