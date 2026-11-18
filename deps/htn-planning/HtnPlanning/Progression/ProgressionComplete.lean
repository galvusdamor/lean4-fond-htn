import HtnPlanning.Core.DecompPersist
import HtnPlanning.Core.SolutionIso
/-!
# Completeness of progression search

This file proves the completeness half of Theorem 2 of

  D. Höller, P. Bercher, G. Behnke, S. Biundo,
  *HTN Planning as Heuristic Progression Search*, JAIR 67 (2020):

every solution of an HTN planning problem is found by progression search, i.e. the search space
of `HTN.Problem.Step` contains a goal node whose plan is that solution
(`HTN.Problem.exists_goalNode_of_isSolutionPlan`).

The proof follows the argument of the paper.  The solution is a decomposition sequence
`tn_I →* tn*` together with a linearization of the primitive network `tn*`.  The search node
`(s, tn, π)` is related to that data by the invariant that `tn` still decomposes into (an
isomorphic copy of) the network whose remaining linearization produces the rest of the plan.
Two cases are distinguished at every step, exactly as in the paper:

* if `tn` has an *unconstrained abstract* task, the search decomposes it; that this is possible
  without losing the solution is `HTN.DecomposesToN.pull_out`: the decomposition sequence of the
  solution can be reordered so that this task is decomposed first;
* if it has none, then the task that the solution executes next is already present in `tn` and
  unconstrained there (`HTN.DecomposesTo.unconstrained_of_not_hasUncAbstract`), so the search can
  progress it.

The induction is on the pair (number of remaining decomposition steps, length of the remaining
linearization), ordered lexicographically: the first case consumes a decomposition step, the
second one an action.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable [DecidableEq I] [Infinite I] {P : Problem F A C I}

open TaskNetwork

omit [Infinite I] in
/-- A network without tasks cannot be decomposed. -/
lemma _root_.HTN.DecomposesToN.eq_of_T_empty {M : Set (Method I A C)} {n : ℕ}
    {tn tnStar : TaskNetwork I A C} (h : DecomposesToN M n tn tnStar) (hT : tn.T = ∅) :
    tnStar = tn := by
  cases h with
  | refl => rfl
  | head hstep _ =>
    obtain ⟨t, m, -, ht, -⟩ := hstep
    rw [hT] at ht
    simp at ht

/-- **The main induction of the completeness proof.**  From a search node whose task network
still decomposes (in `n` steps) into a primitive network with a linearization producing the
action sequence `as`, applicable in the node's state and reaching the goal, progression search
reaches a goal node whose plan is the node's plan followed by `as`. -/
theorem exists_goalNode_aux {sel : TaskNetwork I A C → I}
    (hsel : ∀ tn : TaskNetwork I A C, tn.HasUncAbstract →
      tn.Unconstrained (sel tn) ∧ tn.IsAbstractId (sel tn)) :
    ∀ (n len : ℕ) (tn tnStar : TaskNetwork I A C) (s : Set F) (π : List A) (l : List I)
      (as : List A), l.length = len → tn.WF → DecomposesToN P.methods n tn tnStar →
      tnStar.IsPrimitive → tnStar.IsLinearization l → tnStar.IsActionSeq l as →
      P.SeqApplicable as s → P.GoalState (P.transitionSeq as s) →
      ∃ node : SearchNode F A C I, Relation.ReflTransGen (P.StepSel sel) ⟨s, tn, π⟩ node ∧
        P.IsGoalNode node ∧ node.plan = π ++ as := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro len
    induction len using Nat.strong_induction_on with
    | _ len ihlen =>
      intro tn tnStar s π l as hlen hwf hdec hprim hlin hact happ hgoal
      have hwfStar : tnStar.WF := hdec.wf hwf
      by_cases hUA : tn.HasUncAbstract
      · -- Case 1: decompose an unconstrained abstract task
        obtain ⟨hunc, c, hc⟩ := hsel tn hUA
        set t := sel tn with ht_def
        have hnot : t ∈ tnStar.T → ¬ tnStar.IsAbstractId t := by
          intro ht ⟨c', hc'⟩
          obtain ⟨a, ha⟩ := hprim t ht
          rw [ha] at hc'
          exact Sum.inl_ne_inr hc'
        obtain ⟨m, tn₁, tnStar', k, hk, hstep, hrest, hiso⟩ :=
          hdec.pull_out hwf hunc.1 hc hnot
        have hprim' : tnStar'.IsPrimitive := hiso.isPrimitive hprim
        obtain ⟨l', hlin', hact'⟩ :=
          (hiso.exists_linearization_actionSeq_iff as).1 ⟨l, hlin, hact⟩
        obtain ⟨node, hreach, hgoalnode, hplan⟩ :=
          ihn k hk l'.length tn₁ tnStar' s π l' as rfl (hstep.wf hwf) hrest hprim' hlin' hact'
            happ hgoal
        exact ⟨node, Relation.ReflTransGen.head (Problem.StepSel.decomp hunc hstep) hreach,
          hgoalnode, hplan⟩
      · -- Case 2: no unconstrained abstract task
        by_cases hempty : tn.T = ∅
        · -- the network is empty: the current node is already a goal node
          have hstar : tnStar = tn := hdec.eq_of_T_empty hempty
          have hlnil : l = [] := by
            rcases l with _ | ⟨x, l₀⟩
            · rfl
            · exfalso
              have hx := (hlin.2.1 x).1 (by simp)
              rw [hstar, hempty] at hx
              simp at hx
          subst hlnil
          have hasnil : as = [] := by
            have : ([] : List I).map tnStar.α = as.map Sum.inl := hact
            simpa using this.symm
          subst hasnil
          refine ⟨⟨s, tn, π⟩, Relation.ReflTransGen.refl, ⟨hempty, ?_⟩, by simp⟩
          simpa using hgoal
        · -- the network is nonempty: progress the first task of the solution
          have hne : tn.T.Nonempty := Finset.nonempty_of_ne_empty hempty
          obtain ⟨t₀, ht₀⟩ := TaskNetwork.exists_unconstrained hwf hne
          have hprim₀ : tn.IsPrimitiveId t₀ := by
            rcases hx : tn.α t₀ with a | c
            · exact ⟨a, hx⟩
            · exact absurd ⟨t₀, ht₀, c, hx⟩ hUA
          have ht₀Star : t₀ ∈ tnStar.T :=
            (hdec.decomposesTo.mem_of_isPrimitiveId ht₀.1 hprim₀).1
          have hlne : l ≠ [] := by
            intro h
            rw [h] at hlin
            exact absurd ((hlin.2.1 t₀).2 ht₀Star) (by simp)
          obtain ⟨t₁, l', rfl⟩ : ∃ t₁ l', l = t₁ :: l' := by
            cases l with
            | nil => exact absurd rfl hlne
            | cons a b => exact ⟨a, b, rfl⟩
          -- `t₁` is unconstrained in `tn*`
          have ht₁Star : tnStar.Unconstrained t₁ := by
            refine ⟨(hlin.2.1 t₁).1 (by simp), ?_⟩
            intro z hz hcon
            have hzl : z ∈ t₁ :: l' := (hlin.2.1 z).2 hz
            rcases List.mem_cons.1 hzl with rfl | hzl'
            · exact hwfStar.irrefl z hcon
            · exact (List.pairwise_cons.1 hlin.2.2).1 z hzl' hcon
          obtain ⟨ht₁tn, hα₁⟩ :=
            hdec.decomposesTo.unconstrained_of_not_hasUncAbstract ht₁Star hwf hUA
          -- split off the first action
          obtain ⟨a₁, as', rfl, hαStar, hact'⟩ :
              ∃ a₁ as', as = a₁ :: as' ∧ tnStar.α t₁ = Sum.inl a₁ ∧
                tnStar.IsActionSeq l' as' := by
            cases as with
            | nil =>
              exact absurd hact (by simp [TaskNetwork.IsActionSeq])
            | cons a₁ as' =>
              have h := hact
              simp only [TaskNetwork.IsActionSeq, List.map_cons, List.cons.injEq] at h
              exact ⟨a₁, as', rfl, h.1, h.2⟩
          have hαtn : tn.α t₁ = Sum.inl a₁ := by rw [← hα₁]; exact hαStar
          obtain ⟨happ₁, happ'⟩ := happ
          -- the progression step
          have hstepP : P.StepSel sel ⟨s, tn, π⟩
              ⟨P.transition a₁ s, tn.progress t₁, π ++ [a₁]⟩ :=
            Problem.StepSel.prog hUA ht₁tn hαtn happ₁
          -- the remaining problem
          have hdecP : DecomposesToN P.methods n (tn.progress t₁) (tnStar.progress t₁) :=
            hdec.progress ht₁tn.1 ⟨a₁, hαtn⟩
          have hlinP : (tnStar.progress t₁).IsLinearization l' := by
            have hnd := hlin.1
            refine ⟨(List.nodup_cons.1 hnd).2, ?_, ?_⟩
            · intro x
              constructor
              · intro hx
                refine TaskNetwork.mem_progress_T.2 ⟨?_, (hlin.2.1 x).1 (by simp [hx])⟩
                rintro rfl
                exact (List.nodup_cons.1 hnd).1 hx
              · intro hx
                obtain ⟨hxne, hxT⟩ := TaskNetwork.mem_progress_T.1 hx
                rcases List.mem_cons.1 ((hlin.2.1 x).2 hxT) with rfl | h
                · exact absurd rfl hxne
                · exact h
            · exact (List.pairwise_cons.1 hlin.2.2).2.imp (fun h hc => h hc.1)
          have hactP : (tnStar.progress t₁).IsActionSeq l' as' := hact'
          have hprimP : (tnStar.progress t₁).IsPrimitive := hprim.progress t₁
          have hwfP : (tn.progress t₁).WF := TaskNetwork.progress_wf hwf ht₁tn
          obtain ⟨node, hreach, hgoalnode, hplan⟩ :=
            ihlen l'.length (by simp only [List.length_cons] at hlen; omega) (tn.progress t₁) (tnStar.progress t₁)
              (P.transition a₁ s) (π ++ [a₁]) l' as' rfl hwfP hdecP hprimP hlinP hactP
              happ' (by simpa using hgoal)
          refine ⟨node, Relation.ReflTransGen.head hstepP hreach, hgoalnode, ?_⟩
          rw [hplan]
          simp

/-- **Completeness of the optimized progression search** (Theorem 2 of the paper for
Algorithms 2 and 3): even the restricted search space — which decomposes the task chosen by
`sel` whenever an unconstrained abstract task exists, and progresses only otherwise — contains a
goal node for every solution plan. -/
theorem exists_goalNodeSel_of_isSolutionPlan (hP : P.WF) {sel : TaskNetwork I A C → I}
    (hsel : ∀ tn : TaskNetwork I A C, tn.HasUncAbstract →
      tn.Unconstrained (sel tn) ∧ tn.IsAbstractId (sel tn))
    {as : List A} (h : P.IsSolutionPlan as) :
    ∃ node : SearchNode F A C I,
      Relation.ReflTransGen (P.StepSel sel) P.initNode node ∧ P.IsGoalNode node ∧
        node.plan = as := by
  obtain ⟨tnStar, l, hreach, hprim, hlin, hact, happ, hgoal⟩ := h
  obtain ⟨n, hn⟩ := exists_decomposesToN hreach
  obtain ⟨node, hr, hg, hplan⟩ :=
    exists_goalNode_aux hsel n l.length P.tnI tnStar P.init [] l as rfl hP.tnI hn hprim hlin
      hact happ hgoal
  exact ⟨node, hr, hg, by simpa using hplan⟩

open Classical in
/-- A selection function picking an unconstrained abstract task whenever there is one. -/
noncomputable def _root_.HTN.TaskNetwork.uncAbstractSel (tn : TaskNetwork I A C) : I :=
  if h : tn.HasUncAbstract then h.choose else Classical.arbitrary I

omit [DecidableEq I] in
lemma uncAbstractSel_spec (tn : TaskNetwork I A C) (h : tn.HasUncAbstract) :
    tn.Unconstrained tn.uncAbstractSel ∧ tn.IsAbstractId tn.uncAbstractSel := by
  classical
  simp only [TaskNetwork.uncAbstractSel, dif_pos h]
  exact h.choose_spec

/-- **Completeness of progression search** (Theorem 2 of the paper): every solution plan of an
HTN planning problem is the plan of a goal node of the progression search space. -/
theorem exists_goalNode_of_isSolutionPlan (hP : P.WF) {as : List A} (h : P.IsSolutionPlan as) :
    ∃ node : SearchNode F A C I, P.ReachableNode node ∧ P.IsGoalNode node ∧ node.plan = as := by
  obtain ⟨node, hr, hg, hplan⟩ :=
    exists_goalNodeSel_of_isSolutionPlan hP
      (sel := fun tn => tn.uncAbstractSel) uncAbstractSel_spec h
  exact ⟨node, Relation.ReflTransGen.mono (fun _ _ hs => Problem.StepSel.step P hs) hr, hg,
    hplan⟩

end Problem

end HTN
