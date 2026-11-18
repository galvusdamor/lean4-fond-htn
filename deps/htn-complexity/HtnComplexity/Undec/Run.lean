import HtnComplexity.Undec.Yield
/-!
# Plans of the encoding are runs of the machine

`HtnComplexity/Undec/Yield.lean` describes the *hierarchical* constraints on a plan of the
encoding: it is an interleaving of a run-down of the first stack with a run-down of the second.
This file adds the *state* constraints and shows that the two together are exactly a run of the
machine:

* `HTN.Undec.reaches_of_plan` — an executable interleaving of two run-downs that reaches the
  goal is a run of the machine to the accepting state with both stacks empty;
* `HTN.Undec.exists_plan_of_reaches` — and conversely.

The state of the planning problem is always a singleton — the current control state of the
machine — which is what serialises the two interleaved chains into a single run: the
precondition of the action of a transition is its source state, so the transition performed at
any point of the plan is enabled at the control state reached so far.
-/

namespace HTN

namespace Undec

open Syn TaskNetwork Domain

variable {M : TSM}

/-! ### The action model on singleton states -/

theorem prec_semDom_lt {n : ℕ} (hn : n < M.trans.length) :
    (semDom M).prec n = {(M.trAt n).src} := by simp [semDom, hn]

theorem add_semDom_lt {n : ℕ} (hn : n < M.trans.length) :
    (semDom M).add n = {(M.trAt n).tgt} := by simp [semDom, hn]

theorem del_semDom_lt {n : ℕ} (hn : n < M.trans.length) :
    (semDom M).del n = {(M.trAt n).src} := by simp [semDom, hn]

/-- An action of the encoding is applicable in a singleton state exactly when the state is the
source state of its transition. -/
theorem applicable_iff {n q : ℕ} (hn : n < M.trans.length) :
    (semDom M).Applicable n {q} ↔ q = (M.trAt n).src := by
  rw [ActionModel.Applicable, prec_semDom_lt hn]
  simp [eq_comm]

/-- Performing a transition in the state of its source moves to the state of its target. -/
theorem transition_semDom {n q : ℕ} (hn : n < M.trans.length) (hq : q = (M.trAt n).src) :
    (semDom M).transition n {q} = {(M.trAt n).tgt} := by
  rw [ActionModel.transition, add_semDom_lt hn, del_semDom_lt hn, hq]
  simp

/-! ### From a plan to a run -/

/-- **An executable plan of the encoding is a run of the machine.** -/
theorem reaches_of_plan {q : ℕ} {s1 s2 : List ℕ} {y1 y2 as : List ℕ}
    (h1 : Yields M false s1 y1) (h2 : Yields M true s2 y2) (hint : Interleave y1 y2 as)
    (happ : (semDom M).SeqApplicable as {q})
    (hgoal : {M.acc} ⊆ (semDom M).transitionSeq as {q}) :
    M.Reaches ⟨q, s1, s2⟩ ⟨M.acc, [], []⟩ := by
  induction as generalizing q s1 s2 y1 y2 with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hint.eq_nil_of_left
    rw [h1.eq_nil, h2.eq_nil]
    have hqa : M.acc = q := by
      have := hgoal (Set.mem_singleton _)
      simpa using this
    rw [hqa]
    exact Relation.ReflTransGen.refl
  | cons n as ih =>
    obtain ⟨happ0, happ1⟩ := happ
    cases hint with
    | @left y1' y2' zs _ hint' =>
      obtain ⟨rest, hn, hstk, rfl, hy⟩ := h1.cons_inv
      have hq : q = (M.trAt n).src := (applicable_iff hn).1 happ0
      have hstep : M.Step ⟨q, (M.trAt n).pop :: rest, s2⟩
          ⟨(M.trAt n).tgt, (M.trAt n).push ++ rest, s2⟩ :=
        TSM.step_left (TSM.mem_trans_trAt hn) hstk q hq rest s2
      refine Relation.ReflTransGen.head hstep (ih hy h2 hint' ?_ ?_)
      · rwa [transition_semDom hn hq] at happ1
      · rwa [ActionModel.transitionSeq_cons, transition_semDom hn hq] at hgoal
    | @right y1' y2' zs _ hint' =>
      obtain ⟨rest, hn, hstk, rfl, hy⟩ := h2.cons_inv
      have hq : q = (M.trAt n).src := (applicable_iff hn).1 happ0
      have hstep : M.Step ⟨q, s1, (M.trAt n).pop :: rest⟩
          ⟨(M.trAt n).tgt, s1, (M.trAt n).push ++ rest⟩ :=
        TSM.step_right (TSM.mem_trans_trAt hn) hstk q hq s1 rest
      refine Relation.ReflTransGen.head hstep (ih h1 hy hint' ?_ ?_)
      · rwa [transition_semDom hn hq] at happ1
      · rwa [ActionModel.transitionSeq_cons, transition_semDom hn hq] at hgoal

/-- **A run of the machine is an executable plan of the encoding.** -/
theorem exists_plan_of_reaches {q : ℕ} {s1 s2 : List ℕ}
    (h : M.Reaches ⟨q, s1, s2⟩ ⟨M.acc, [], []⟩) :
    ∃ as y1 y2, Yields M false s1 y1 ∧ Yields M true s2 y2 ∧ Interleave y1 y2 as ∧
      (semDom M).SeqApplicable as {q} ∧ (semDom M).transitionSeq as {q} = {M.acc} := by
  have key : ∀ c : Cfg, M.Reaches c ⟨M.acc, [], []⟩ →
      ∃ as y1 y2, Yields M false c.s1 y1 ∧ Yields M true c.s2 y2 ∧ Interleave y1 y2 as ∧
        (semDom M).SeqApplicable as {c.st} ∧
        (semDom M).transitionSeq as {c.st} = {M.acc} := by
    intro c hc
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], [], [], Yields.nil, Yields.nil, Interleave.nil, trivial, rfl⟩
    | head hstep _ ih =>
      rename_i c₀ c₁ _
      obtain ⟨as, y1, y2, hy1, hy2, hint, happ, hst⟩ := ih
      obtain ⟨t, ht, hsrc, hcase⟩ := hstep
      obtain ⟨n, hn, rfl⟩ := TSM.exists_trAt ht
      have hq : c₀.st = (M.trAt n).src := hsrc
      rcases hcase with ⟨hstk, rest, hrest, hc1⟩ | ⟨hstk, rest, hrest, hc1⟩
      · subst hc1
        refine ⟨n :: as, n :: y1, y2, ?_, hy2, Interleave.left n hint, ?_, ?_⟩
        · rw [hrest]
          exact Yields.step hn hstk hy1
        · exact ⟨(applicable_iff hn).2 hq, by rw [transition_semDom hn hq]; exact happ⟩
        · rw [ActionModel.transitionSeq_cons, transition_semDom hn hq]
          exact hst
      · subst hc1
        refine ⟨n :: as, y1, n :: y2, hy1, ?_, Interleave.right n hint, ?_, ?_⟩
        · rw [hrest]
          exact Yields.step hn hstk hy2
        · exact ⟨(applicable_iff hn).2 hq, by rw [transition_semDom hn hq]; exact happ⟩
        · rw [ActionModel.transitionSeq_cons, transition_semDom hn hq]
          exact hst
  exact key ⟨q, s1, s2⟩ h

end Undec

end HTN
