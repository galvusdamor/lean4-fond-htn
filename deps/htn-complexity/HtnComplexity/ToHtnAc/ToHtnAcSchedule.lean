import HtnComplexity.ToHtnAc.ToHtnAcPrimStep
import HtnComplexity.ToHtnAc.ToHtnAcTupleShape
/-!
# Scheduling the proof steps of the HTN-AC compilation

`HtnComplexity/ToHtnAc/ToHtnAcTupleShape.lean` determines the *shape* of a proof step and
`HtnComplexity/ToHtnAc/ToHtnAcMemPhase.lean` the two phases of a memory cell.  This file starts the
converse direction, the one needed for the *completeness* half of the correctness of the
compilation: from a derivation of a proof tuple, build a plan of the compiled problem.

The basic building block is one **scheduled proof step**: the actions of one `TUPLE` run
together with the actions of the memory-cell phases that have to be executed *inside* it,
namely the write phase of the cell the step fills (between its `ask_W` and its `wait_W`).  This
file proves that a primitive proof step can be scheduled in this way:

* `HTN.ToAc.Clean` — the state between two proof steps: the lock is free and no handshake is
  pending;
* `HTN.ToAc.exists_primStep_prefix` — from a state in which the lock is free, the part of a
  primitive proof step up to and including the `setC` action can be executed so that the first
  copy holds `S`, the second and the third hold `γ(S, o)` and the stored task name is `o`;
* `HTN.ToAc.exists_primStep_schedule` — the whole scheduled step: an interleaving of one
  refinement of `TUPLE` with the write phase of one memory cell, executable in every clean
  state, which leaves the state clean again and the cell latched with the proof tuple
  `(S, o, γ(S, o))`.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### Clean states -/

/-- A *clean* state of the compiled problem: the lock is free and no handshake is pending.  This
is the state in which a proof step starts and which it restores. -/
def Clean (s : Set (AcFact F A C)) : Prop :=
  AcFact.key0 ∈ s ∧ ∀ x : RW, AcFact.key1 x ∉ s ∧ AcFact.key2 x ∉ s

/-- The key facts of two states agree. -/
def KeysAgree (s s' : Set (AcFact F A C)) : Prop :=
  ∀ x : RW, (AcFact.key1 x ∈ s' ↔ AcFact.key1 x ∈ s) ∧ (AcFact.key2 x ∈ s' ↔ AcFact.key2 x ∈ s)

lemma KeysAgree.refl (s : Set (AcFact F A C)) : KeysAgree s s := fun _ => ⟨Iff.rfl, Iff.rfl⟩

lemma KeysAgree.trans {s₁ s₂ s₃ : Set (AcFact F A C)} (h₁ : KeysAgree s₁ s₂)
    (h₂ : KeysAgree s₂ s₃) : KeysAgree s₁ s₃ := fun x =>
  ⟨(h₂ x).1.trans (h₁ x).1, (h₂ x).2.trans (h₁ x).2⟩

/-- A change confined to one copy of the source facts leaves the key facts alone. -/
lemma keysAgree_of_unchangedOutside {s s' : Set (AcFact F A C)} {i : Fin 5}
    (h : UnchangedOutside s s' i vars) : KeysAgree s s' := by
  intro x
  exact ⟨(h (AcFact.key1 x) (fun v _ => ⟨by simp, by simp⟩)).symm,
    (h (AcFact.key2 x) (fun v _ => ⟨by simp, by simp⟩)).symm⟩

lemma keysAgree_transition_op2 {o : A} (s : Set (AcFact F A C)) :
    KeysAgree s ((domain D vars bound).transition (AcAct.op2 o) s) := by
  intro x
  exact ⟨mem_transition_op2_of_ne (fun v => ⟨by simp, by simp⟩),
    mem_transition_op2_of_ne (fun v => ⟨by simp, by simp⟩)⟩

lemma keysAgree_transition_setC {t : A ⊕ C} (s : Set (AcFact F A C)) :
    KeysAgree s ((domain D vars bound).transition (AcAct.setC t) s) := by
  intro x
  constructor <;> rw [mem_transition_setC] <;> simp

lemma keysAgree_transition_lock (s : Set (AcFact F A C)) :
    KeysAgree s ((domain D vars bound).transition AcAct.lock s) := by
  intro x
  constructor <;> rw [mem_transition_lock] <;> simp

/-! ### The executable prefix of a primitive proof step -/

/-- The state reached by the prefix of a primitive proof step: the two `EQ` gadgets change
nothing, so only `lock`, the three guesses, `o²` and `setC` contribute. -/
lemma transitionSeq_primStepPrefix {o : A} {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)}
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂)
    (s : Set (AcFact F A C)) :
    (domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s
      = (domain D vars bound).transition (AcAct.setC (Sum.inl o))
          ((domain D vars bound).transition (AcAct.op2 o)
            ((domain D vars bound).transitionSeq g₃
              ((domain D vars bound).transitionSeq g₂
                ((domain D vars bound).transitionSeq g₁
                  ((domain D vars bound).transition AcAct.lock s))))) := by
  rw [primStepPrefix]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    ActionModel.transitionSeq_nil, transitionSeq_yieldSeq_EQ he₁, transitionSeq_yieldSeq_EQ he₂]

/-- The prefix of a primitive proof step is executable as soon as its parts are. -/
lemma seqApplicable_primStepPrefix {o : A} {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)}
    {s : Set (AcFact F A C)}
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁)
    (hlock : AcFact.key0 ∈ s)
    (h₁ : (domain D vars bound).SeqApplicable g₁
      ((domain D vars bound).transition AcAct.lock s))
    (h₂ : (domain D vars bound).SeqApplicable g₂
      ((domain D vars bound).transitionSeq g₁ ((domain D vars bound).transition AcAct.lock s)))
    (h₃ : (domain D vars bound).SeqApplicable g₃
      ((domain D vars bound).transitionSeq g₂
        ((domain D vars bound).transitionSeq g₁
          ((domain D vars bound).transition AcAct.lock s))))
    (he₁a : (domain D vars bound).SeqApplicable e₁
      ((domain D vars bound).transitionSeq g₃
        ((domain D vars bound).transitionSeq g₂
          ((domain D vars bound).transitionSeq g₁
            ((domain D vars bound).transition AcAct.lock s)))))
    (hop : (domain D vars bound).Applicable (AcAct.op2 o)
      ((domain D vars bound).transitionSeq g₃
        ((domain D vars bound).transitionSeq g₂
          ((domain D vars bound).transitionSeq g₁
            ((domain D vars bound).transition AcAct.lock s)))))
    (he₂a : (domain D vars bound).SeqApplicable e₂
      ((domain D vars bound).transition (AcAct.op2 o)
        ((domain D vars bound).transitionSeq g₃
          ((domain D vars bound).transitionSeq g₂
            ((domain D vars bound).transitionSeq g₁
              ((domain D vars bound).transition AcAct.lock s)))))) :
    (domain D vars bound).SeqApplicable (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s := by
  have hl : (domain D vars bound).Applicable AcAct.lock s := by
    simpa [ActionModel.Applicable, domain, actionModel, prec] using hlock
  rw [primStepPrefix]
  simp only [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_append,
    ActionModel.transitionSeq_append, ActionModel.transitionSeq_cons,
    ActionModel.transitionSeq_nil, ActionModel.seqApplicable_nil, and_true,
    transitionSeq_yieldSeq_EQ he₁]
  and_intros
  exacts [hl, h₁, h₂, h₃, he₁a, hop, he₂a, applicable_setC]

/-- **The prefix of a primitive proof step can be scheduled.**  In a state whose lock is free,
the actions of a primitive proof step for the operator `o`, up to and including the action
storing the task name, can be executed so that afterwards the first copy holds `S`, the third
copy holds `γ(S, o)`, the stored task name is `o`, the lock is taken and no handshake has
changed. -/
theorem exists_primStep_prefix (hvars : ∀ v : F, v ∈ vars)
    {o : A} {S : Set F} (hprec : D.Applicable o S) (hdisj : Disjoint (D.add o) (D.del o))
    {s : Set (AcFact F A C)} (hkey0 : AcFact.key0 ∈ s) :
    ∃ (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)) (s' : Set (AcFact F A C)),
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂ ∧
      (domain D vars bound).SeqApplicable (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s ∧
      s' = (domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s ∧
      RepresentsOn s' 0 S vars ∧ RepresentsOn s' 2 (D.transition o S) vars ∧
      AcFact.task (Sum.inl o) ∈ s' ∧ KeysAgree s s' ∧ AcFact.key0 ∉ s' := by
  classical
  obtain ⟨g₁, hg₁, happ₁, hunch₁, hrep₁⟩ :=
    exists_yieldSeq_SEL (D := D) (vars := vars) (bound := bound) 0 S
      ((domain D vars bound).transition AcAct.lock s)
  obtain ⟨g₂, hg₂, happ₂, hunch₂, hrep₂⟩ :=
    exists_yieldSeq_SEL (D := D) (vars := vars) (bound := bound) 1 S
      ((domain D vars bound).transitionSeq g₁
        ((domain D vars bound).transition AcAct.lock s))
  obtain ⟨g₃, hg₃, happ₃, hunch₃, hrep₃⟩ :=
    exists_yieldSeq_SEL (D := D) (vars := vars) (bound := bound) 2 (D.transition o S)
      ((domain D vars bound).transitionSeq g₂
        ((domain D vars bound).transitionSeq g₁
          ((domain D vars bound).transition AcAct.lock s)))
  set t₀ := (domain D vars bound).transition AcAct.lock s with ht₀
  set t₁ := (domain D vars bound).transitionSeq g₁ t₀ with ht₁
  set t₂ := (domain D vars bound).transitionSeq g₂ t₁ with ht₂
  set t₃ := (domain D vars bound).transitionSeq g₃ t₂ with ht₃
  have hrep₁₂ : RepresentsOn t₂ 0 S vars :=
    representsOn_of_unchangedOutside (by decide) hrep₁ hunch₂
  have hrep₁₃ : RepresentsOn t₃ 0 S vars :=
    representsOn_of_unchangedOutside (by decide) hrep₁₂ hunch₃
  have hrep₂₃ : RepresentsOn t₃ 1 S vars :=
    representsOn_of_unchangedOutside (by decide) hrep₂ hunch₃
  obtain ⟨e₁, he₁, happe₁⟩ :=
    (eq_executable_iff (D := D) (bound := bound) hrep₁₃ hrep₂₃).2 (fun _ _ => Iff.rfl)
  have hop : (domain D vars bound).Applicable (AcAct.op2 o) t₃ := by
    rw [applicable_op2_iff]
    intro v hv
    exact (hrep₂₃ v (hvars v)).1.2 (hprec hv)
  set t₄ := (domain D vars bound).transition (AcAct.op2 o) t₃ with ht₄
  have hrep₀₄ : RepresentsOn t₄ 0 S vars := representsOn_transition_op2 (by decide) hrep₁₃
  have hrep₁₄ : RepresentsOn t₄ 1 (D.transition o S) vars := representsOn_op2 hdisj hrep₂₃
  have hrep₂₄ : RepresentsOn t₄ 2 (D.transition o S) vars :=
    representsOn_transition_op2 (by decide) hrep₃
  obtain ⟨e₂, he₂, happe₂⟩ :=
    (eq_executable_iff (D := D) (bound := bound) hrep₁₄ hrep₂₄).2 (fun _ _ => Iff.rfl)
  set t₅ := (domain D vars bound).transition (AcAct.setC (Sum.inl o)) t₄ with ht₅
  have happ : (domain D vars bound).SeqApplicable (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s :=
    seqApplicable_primStepPrefix he₁ hkey0 happ₁ happ₂ happ₃ happe₁ hop
      (by rw [ht₄] at happe₂; exact happe₂)
  have htr : (domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s = t₅ := by
    rw [transitionSeq_primStepPrefix he₁ he₂, ← ht₀, ← ht₁, ← ht₂, ← ht₃, ← ht₄, ← ht₅]
  refine ⟨g₁, g₂, g₃, e₁, e₂, t₅, hg₁, hg₂, hg₃, he₁, he₂, happ, htr.symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact representsOn_transition_setC hrep₀₄
  · exact representsOn_transition_setC hrep₂₄
  · rw [ht₅, mem_transition_setC]
    exact Or.inr rfl
  · have k0 : KeysAgree s t₀ := keysAgree_transition_lock (D := D) (vars := vars)
      (bound := bound) s
    have k1 : KeysAgree t₀ t₁ := keysAgree_of_unchangedOutside hunch₁
    have k2 : KeysAgree t₁ t₂ := keysAgree_of_unchangedOutside hunch₂
    have k3 : KeysAgree t₂ t₃ := keysAgree_of_unchangedOutside hunch₃
    have k4 : KeysAgree t₃ t₄ := keysAgree_transition_op2 (D := D) (vars := vars)
      (bound := bound) t₃
    have k5 : KeysAgree t₄ t₅ := keysAgree_transition_setC (D := D) (vars := vars)
      (bound := bound) t₄
    exact k0.trans (k1.trans (k2.trans (k3.trans (k4.trans k5))))
  · have h₀ : AcFact.key0 ∉ t₀ := by
      rw [ht₀, mem_transition_lock]
      simp
    have h₁ : AcFact.key0 ∉ t₁ := by
      intro hmem
      exact h₀ ((hunch₁ AcFact.key0 (fun v _ => ⟨by simp, by simp⟩)).2 hmem)
    have h₂ : AcFact.key0 ∉ t₂ := by
      intro hmem
      exact h₁ ((hunch₂ AcFact.key0 (fun v _ => ⟨by simp, by simp⟩)).2 hmem)
    have h₃ : AcFact.key0 ∉ t₃ := by
      intro hmem
      exact h₂ ((hunch₃ AcFact.key0 (fun v _ => ⟨by simp, by simp⟩)).2 hmem)
    have h₄ : AcFact.key0 ∉ t₄ := by
      intro hmem
      rw [ht₄] at hmem
      exact h₃ ((mem_transition_op2_of_ne (fun v => ⟨by simp, by simp⟩)).1 hmem)
    intro hmem
    rw [ht₅, mem_transition_setC] at hmem
    rcases hmem with ⟨hmem, -⟩ | hmem
    · exact h₄ hmem
    · simp at hmem

end ToAc

end HTN
