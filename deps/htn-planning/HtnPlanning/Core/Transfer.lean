import HtnPlanning.Core.Relabel
/-!
# Solvability is invariant under a change of signature

`HtnPlanning/Core/Relabel.lean` transports task networks and decomposition along an injection
of the action names, an injection of the compound task names and a bijection of the task
identifiers.  This file completes the picture with the *state* half — the action model, the
initial state and the goal — and proves the theorem the syntactic development needs:

> `HTN.Problem.solvable_relabel_iff` — if the problem `P'` is the image of the problem `P`
> under such a change of signature, then `P'` is solvable exactly when `P` is.

Two points make the statement usable in practice.

* **Only the *used* actions matter.**  The action model of `P'` is required to agree with the
  one of `P` only at the actions that occur in the initial task network or in a method of `P`
  (`HTN.Problem.UsedAction`); at every other action of the target signature `P'` may do
  whatever it likes.  This is what makes the theorem applicable to a *described* problem, whose
  action set is all of `ℕ` while the description mentions only finitely many actions.
  `HTN.Problem.actionsUsed_of_decomposesTo` is the soundness statement behind it: an action
  labelling a reachable task network is used.
* **Identifiers are relabelled along a bijection.**  Both id types are countably infinite in
  every application, so this costs nothing, and it makes the image of a network an exact copy.

Together with `HtnPlanning/Core/MethodRestrict.lean` — which allows the source problem to
carry methods that the target does not have to mirror, as long as they are unreachable — this
is the bridge between the semantic constructions of this development and their counterparts on
finite descriptions.
-/

namespace HTN

namespace Problem

universe uF uF' uA uA' uC uC' uI uI'

variable {F : Type uF} {F' : Type uF'} {A : Type uA} {A' : Type uA'} {C : Type uC}
  {C' : Type uC'} {I : Type uI} {I' : Type uI'}

/-! ### The actions a problem can use -/

/-- An action name is **used** by a problem iff it labels a task of the initial task network or
a task of the subtask network of one of its methods.  No other action can occur in a plan. -/
def UsedAction (P : Problem F A C I) (a : A) : Prop :=
  (∃ t ∈ P.tnI.T, P.tnI.α t = Sum.inl a) ∨
    ∃ m ∈ P.methods, ∃ t ∈ m.subtasks.T, m.subtasks.α t = Sum.inl a

/-- All action names occurring in a task network are used by the problem. -/
def ActionsUsed (P : Problem F A C I) (tn : TaskNetwork I A C) : Prop :=
  ∀ t ∈ tn.T, ∀ a : A, tn.α t = Sum.inl a → P.UsedAction a

lemma actionsUsed_tnI (P : Problem F A C I) : P.ActionsUsed P.tnI :=
  fun t ht _ ha => Or.inl ⟨t, ht, ha⟩

variable [DecidableEq I]

/-- A decomposition step preserves the property that all action names of the network are
used. -/
lemma actionsUsed_of_decompStep {P : Problem F A C I} {tn₁ tn₂ : TaskNetwork I A C} {t : I}
    {m : Method I A C} (h : DecompStep P.methods tn₁ t m tn₂) (hn : P.ActionsUsed tn₁) :
    P.ActionsUsed tn₂ := by
  obtain ⟨hm, htT, hαt, tn', -, ⟨σ, hbij, -, hα⟩, -, rfl⟩ := h
  intro x hx a hc
  by_cases hx' : x ∈ tn'.T
  · have hxσ : σ x ∈ m.subtasks.T := by simpa using hbij.mapsTo (by simpa using hx')
    have : m.subtasks.α (σ x) = Sum.inl a := by
      rw [← hα x hx']
      simpa [hx'] using hc
    exact Or.inr ⟨m, hm, σ x, hxσ, this⟩
  · have hx₁ : x ∈ tn₁.T := by
      rcases mem_decomposeWith_T.1 hx with ⟨h, -⟩ | h
      · exact h
      · exact absurd h hx'
    exact hn x hx₁ a (by simpa [hx'] using hc)

/-- **Soundness of the analysis.**  Every action name occurring in a task network reachable
from `tn_I` by decomposition is used by the problem. -/
theorem actionsUsed_of_decomposesTo {P : Problem F A C I} {tn : TaskNetwork I A C}
    (h : P.DecomposesTo P.tnI tn) : P.ActionsUsed tn := by
  induction h with
  | refl => exact P.actionsUsed_tnI
  | tail _ hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact actionsUsed_of_decompStep hs ih

/-! ### The state half of the transfer -/

section State

variable {P : Problem F A C I} {P' : Problem F' A' C' I'} {eF : F → F'} {eA : A → A'}

omit [DecidableEq I] in
/-- The image of a state under a change of signature evolves along the image of an action
sequence exactly as the state does along the sequence. -/
theorem transitionSeq_relabel (hF : Function.Injective eF)
    (hadd : ∀ o, P.UsedAction o → P'.add (eA o) = eF '' P.add o)
    (hdel : ∀ o, P.UsedAction o → P'.del (eA o) = eF '' P.del o)
    {as : List A} (hused : ∀ a ∈ as, P.UsedAction a) (s : Set F) :
    P'.transitionSeq (as.map eA) (eF '' s) = eF '' P.transitionSeq as s := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
    have hstep : P'.transition (eA a) (eF '' s) = eF '' P.transition a s := by
      have ha : P.UsedAction a := hused a (by simp)
      simp only [ActionModel.transition, hadd a ha, hdel a ha]
      rw [← Set.image_diff hF, ← Set.image_union]
    simp only [List.map_cons, ActionModel.transitionSeq_cons, hstep]
    exact ih (fun x hx => hused x (by simp [hx])) _

omit [DecidableEq I] in
/-- Applicability is preserved and reflected by a change of signature. -/
theorem seqApplicable_relabel_iff (hF : Function.Injective eF)
    (hprec : ∀ o, P.UsedAction o → P'.prec (eA o) = eF '' P.prec o)
    (hadd : ∀ o, P.UsedAction o → P'.add (eA o) = eF '' P.add o)
    (hdel : ∀ o, P.UsedAction o → P'.del (eA o) = eF '' P.del o)
    {as : List A} (hused : ∀ a ∈ as, P.UsedAction a) (s : Set F) :
    P'.SeqApplicable (as.map eA) (eF '' s) ↔ P.SeqApplicable as s := by
  induction as generalizing s with
  | nil => simp [ActionModel.SeqApplicable]
  | cons a as ih =>
    have ha : P.UsedAction a := hused a (by simp)
    have hstep : P'.transition (eA a) (eF '' s) = eF '' P.transition a s := by
      simp only [ActionModel.transition, hadd a ha, hdel a ha]
      rw [← Set.image_diff hF, ← Set.image_union]
    simp only [List.map_cons, ActionModel.SeqApplicable, ActionModel.Applicable, hprec a ha,
      hstep]
    exact and_congr (Set.image_subset_image_iff hF) (ih (fun x hx => hused x (by simp [hx])) _)

end State

/-! ### The transfer of solvability -/

variable [DecidableEq I'] [Infinite I] [Infinite I'] [Nonempty (A ⊕ C)]

open TaskNetwork

omit [Infinite I] in
/-- **Solvability is invariant under a change of signature.**  If the problem `P'` is the image
of the problem `P` under an injection `eF` of facts, an injection `eA` of action names, an
injection `eC` of compound task names and a bijection `eI` of task identifiers, then `P'` is
solvable exactly when `P` is.

The action model of `P'` is only constrained at the actions `P` can actually use
(`HTN.Problem.UsedAction`). -/
theorem solvable_relabel_iff {P : Problem F A C I} {P' : Problem F' A' C' I'} {eF : F → F'}
    {eA : A → A'} {eC : C → C'} {eI : I ≃ I'} (hF : Function.Injective eF)
    (hA : Function.Injective eA) (hC : Function.Injective eC)
    (hprec : ∀ o, P.UsedAction o → P'.prec (eA o) = eF '' P.prec o)
    (hadd : ∀ o, P.UsedAction o → P'.add (eA o) = eF '' P.add o)
    (hdel : ∀ o, P.UsedAction o → P'.del (eA o) = eF '' P.del o)
    (hinit : P'.init = eF '' P.init) (hgoal : P'.goal = eF '' P.goal)
    (hwf : P.tnI.WF) (htnI : P'.tnI = TaskNetwork.relabel eA eC eI P.tnI)
    (hmethods : P'.methods = Method.relabel eA eC eI '' P.methods) :
    P'.Solvable ↔ P.Solvable := by
  constructor
  · rintro ⟨v, hreach, hprim, hexec⟩
    have hreach' : HTN.DecomposesTo (I := I') (A := A') (C := C')
        (Method.relabel eA eC eI '' P.methods) (TaskNetwork.relabel eA eC eI P.tnI) v := by
      have := hreach
      rw [Problem.Reachable, Problem.DecomposesTo, hmethods, htnI] at this
      exact this
    obtain ⟨w, hw, hiso⟩ := exists_decomposesTo_of_relabel hA hC hwf hreach'
    have hwprim : w.IsPrimitive :=
      relabel_isPrimitive_iff.1 (hiso.symm.isPrimitive hprim)
    have hexecw : P'.Executable (TaskNetwork.relabel eA eC eI w) := hexec.iso hiso.symm
    obtain ⟨l', as', hlin', has', happ', hgoal'⟩ := hexecw
    -- the linearization comes from a linearization of `w`
    set l : List I := l'.map eI.symm with hl
    have hll : l.map eI = l' := by
      rw [hl, List.map_map]
      simp
    have hlinw : w.IsLinearization l :=
      (isLinearization_relabel_iff (eA := eA) (eC := eC) (eI := eI)).1
        (by rw [hll]; exact hlin')
    have hprimids : ∀ t ∈ l, w.IsPrimitiveId t := fun t ht => hwprim t ((hlinw.2.1 t).1 ht)
    obtain ⟨as, has⟩ := TaskNetwork.exists_actionSeq hprimids
    have has₂ : (TaskNetwork.relabel eA eC eI w).IsActionSeq l' (as.map eA) := by
      have := isActionSeq_relabel (eA := eA) (eC := eC) (eI := eI) has
      rwa [hll] at this
    have hasel : as' = as.map eA := TaskNetwork.isActionSeq_unique has' has₂
    -- every action of the plan is used
    have hused : ∀ a ∈ as, P.UsedAction a := by
      intro a ha
      have : Sum.inl a ∈ l.map w.α := by
        rw [show l.map w.α = as.map (Sum.inl (β := C)) from has]
        exact List.mem_map_of_mem ha
      obtain ⟨t, htl, hta⟩ := List.mem_map.1 this
      exact actionsUsed_of_decomposesTo hw t ((hlinw.2.1 t).1 htl) a hta
    refine ⟨w, hw, hwprim, l, as, hlinw, has, ?_, ?_⟩
    · have := happ'
      rw [hasel, hinit] at this
      exact (seqApplicable_relabel_iff hF hprec hadd hdel hused _).1 this
    · have h2 : P'.goal ⊆ P'.transitionSeq as' P'.init := hgoal'
      rw [hasel, hinit, hgoal, transitionSeq_relabel hF hadd hdel hused] at h2
      exact (Set.image_subset_image_iff hF).1 h2
  · rintro ⟨tn, hreach, hprim, l, as, hlin, has, happ, hgl⟩
    have hused : ∀ a ∈ as, P.UsedAction a := by
      intro a ha
      have : Sum.inl a ∈ l.map tn.α := by
        rw [show l.map tn.α = as.map (Sum.inl (β := C)) from has]
        exact List.mem_map_of_mem ha
      obtain ⟨t, htl, hta⟩ := List.mem_map.1 this
      exact actionsUsed_of_decomposesTo hreach t ((hlin.2.1 t).1 htl) a hta
    refine ⟨TaskNetwork.relabel eA eC eI tn, ?_, relabel_isPrimitive_iff.2 hprim,
      l.map eI, as.map eA, isLinearization_relabel_iff.2 hlin, isActionSeq_relabel has, ?_, ?_⟩
    · rw [Problem.Reachable, Problem.DecomposesTo, hmethods, htnI]
      exact decomposesTo_relabel hreach
    · rw [hinit]
      exact (seqApplicable_relabel_iff hF hprec hadd hdel hused _).2 happ
    · show P'.goal ⊆ P'.transitionSeq (as.map eA) P'.init
      rw [hinit, hgoal, transitionSeq_relabel hF hadd hdel hused]
      exact Set.image_mono hgl

end Problem

end HTN
