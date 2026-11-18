import HtnPlanning.Core.Problem
/-!
# Progression search: search nodes, progression and the search space

This file formalises the search space of the progression-based HTN planning algorithms of

  D. Höller, P. Bercher, G. Behnke, S. Biundo,
  *HTN Planning as Heuristic Progression Search*, JAIR 67 (2020), Section 4.1
  (Algorithm 1 and Definitions 1–4).

A *search node* `n = (s, tn, π)` consists of the current state, the task network of the tasks
that still have to be processed, and the prefix of the plan produced so far (Section 4.1).  The
algorithm modifies a node in two ways, and both are only applied to *unconstrained* tasks
(Definition 2, `HTN.TaskNetwork.Unconstrained`):

* **progression** of an unconstrained, primitive and applicable task (Definition 3), and
* **decomposition** of an unconstrained abstract task with one of its methods (Definition 4).

`HTN.Problem.Step` is the union of the two, i.e. the edge relation of the search space that
Algorithm 1 explores; the concrete algorithms of the paper (Algorithms 1–3) differ only in
*which* of these edges they generate, so soundness and completeness of the search space are
the mathematical content of Theorems 1 and 2.  A node is a *goal node* (Definition 1) iff its
task network is empty and its state satisfies the goal description.
-/

namespace HTN

universe u v w x

variable {I : Type x} {A : Type v} {C : Type w} {F : Type u}

namespace TaskNetwork

/-- **Progression** (Definition 3 of the paper), the task-network part: the task `t` is removed
from the network, together with all ordering constraints `(t, t')` starting at it. -/
def progress [DecidableEq I] (tn : TaskNetwork I A C) (t : I) : TaskNetwork I A C where
  T := tn.T.erase t
  ord := fun a b => tn.ord a b ∧ a ≠ t
  α := tn.α

@[simp] lemma progress_T [DecidableEq I] (tn : TaskNetwork I A C) (t : I) :
    (tn.progress t).T = tn.T.erase t := rfl

@[simp] lemma progress_ord [DecidableEq I] (tn : TaskNetwork I A C) (t a b : I) :
    (tn.progress t).ord a b ↔ (tn.ord a b ∧ a ≠ t) := Iff.rfl

@[simp] lemma progress_α [DecidableEq I] (tn : TaskNetwork I A C) (t x : I) :
    (tn.progress t).α x = tn.α x := rfl

lemma mem_progress_T [DecidableEq I] {tn : TaskNetwork I A C} {t x : I} :
    x ∈ (tn.progress t).T ↔ x ≠ t ∧ x ∈ tn.T := by
  simp [progress]

/-- Progressing an unconstrained task of a well-formed network gives a well-formed network. -/
lemma progress_wf [DecidableEq I] {tn : TaskNetwork I A C} {t : I} (hwf : tn.WF)
    (hu : tn.Unconstrained t) : (tn.progress t).WF where
  mem_left := by
    rintro a b ⟨hab, hat⟩
    exact Finset.mem_erase.2 ⟨hat, hwf.mem_left hab⟩
  mem_right := by
    rintro a b ⟨hab, hat⟩
    refine Finset.mem_erase.2 ⟨?_, hwf.mem_right hab⟩
    rintro rfl
    exact hu.2 a (hwf.mem_left hab) hab
  irrefl := fun a h => hwf.irrefl a h.1
  trans := by
    rintro a b c ⟨hab, hat⟩ ⟨hbc, -⟩
    exact ⟨hwf.trans hab hbc, hat⟩

/-- A task network *has an unconstrained abstract task*: exactly the situation in which
progression search decomposes instead of progressing. -/
def HasUncAbstract (tn : TaskNetwork I A C) : Prop :=
  ∃ v, tn.Unconstrained v ∧ tn.IsAbstractId v

/-- A primitive network stays primitive under progression. -/
lemma IsPrimitive.progress [DecidableEq I] {tn : TaskNetwork I A C} (h : tn.IsPrimitive)
    (t : I) : (tn.progress t).IsPrimitive := by
  intro x hx
  exact h x (Finset.mem_of_mem_erase hx)

end TaskNetwork

/-- A **search node** of progression search: the current state, the task network of the tasks
that still have to be processed, and the prefix of the plan progressed so far. -/
structure SearchNode (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The current state. -/
  state : Set F
  /-- The remaining task network. -/
  net : TaskNetwork I A C
  /-- The sequence of actions progressed so far. -/
  plan : List A

namespace Problem

variable [DecidableEq I] (P : Problem F A C I)

/-- **The edge relation of the progression search space.**  A search node is modified either by
progressing an unconstrained, primitive and applicable task (Definition 3) or by decomposing an
unconstrained abstract task with one of the methods of the problem (Definition 4). -/
inductive Step : SearchNode F A C I → SearchNode F A C I → Prop
  /-- Progression of an unconstrained applicable action (Definition 3). -/
  | prog {s : Set F} {tn : TaskNetwork I A C} {π : List A} {t : I} {a : A}
      (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a) (happ : P.Applicable a s) :
      Step ⟨s, tn, π⟩ ⟨P.transition a s, tn.progress t, π ++ [a]⟩
  /-- Decomposition of an unconstrained abstract task (Definition 4). -/
  | decomp {s : Set F} {tn tn' : TaskNetwork I A C} {π : List A} {t : I} {m : Method I A C}
      (hu : tn.Unconstrained t) (hstep : DecompStep P.methods tn t m tn') :
      Step ⟨s, tn, π⟩ ⟨s, tn', π⟩

/-- **The search space of the optimized algorithms** (Algorithms 2 and 3 of the paper): as long
as the task network has an unconstrained *abstract* task the search only decomposes, and it
decomposes the task chosen by the selection function `sel`; only when no unconstrained abstract
task is left does it progress an action. -/
inductive StepSel (sel : TaskNetwork I A C → I) : SearchNode F A C I → SearchNode F A C I → Prop
  /-- Progression, only allowed when no unconstrained abstract task is left. -/
  | prog {s : Set F} {tn : TaskNetwork I A C} {π : List A} {t : I} {a : A}
      (hno : ¬ tn.HasUncAbstract) (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a)
      (happ : P.Applicable a s) :
      StepSel sel ⟨s, tn, π⟩ ⟨P.transition a s, tn.progress t, π ++ [a]⟩
  /-- Decomposition of the selected unconstrained abstract task. -/
  | decomp {s : Set F} {tn tn' : TaskNetwork I A C} {π : List A} {m : Method I A C}
      (hu : tn.Unconstrained (sel tn)) (hstep : DecompStep P.methods tn (sel tn) m tn') :
      StepSel sel ⟨s, tn, π⟩ ⟨s, tn', π⟩

/-- The initial search node `(s₀, tn_I, ε)`. -/
def initNode : SearchNode F A C I := ⟨P.init, P.tnI, []⟩

/-- The search nodes explored by progression search: those reachable from the initial node. -/
def ReachableNode (n : SearchNode F A C I) : Prop :=
  Relation.ReflTransGen P.Step P.initNode n

/-- The restricted search space is part of the full one. -/
lemma StepSel.step {sel : TaskNetwork I A C → I} {n n' : SearchNode F A C I}
    (h : P.StepSel sel n n') : P.Step n n' := by
  cases h with
  | prog _ hu hα happ => exact Step.prog hu hα happ
  | decomp hu hstep => exact Step.decomp hu hstep

/-- **Goal nodes** (Definition 1): the task network is empty and the state is a goal state. -/
def IsGoalNode (n : SearchNode F A C I) : Prop := n.net.T = ∅ ∧ P.GoalState n.state

omit [DecidableEq I] in
@[simp] lemma initNode_state : (P.initNode).state = P.init := rfl

omit [DecidableEq I] in
@[simp] lemma initNode_net : (P.initNode).net = P.tnI := rfl

omit [DecidableEq I] in
@[simp] lemma initNode_plan : (P.initNode).plan = ([] : List A) := rfl

lemma ReachableNode.refl : P.ReachableNode P.initNode := Relation.ReflTransGen.refl

variable {P}

lemma ReachableNode.tail {n n' : SearchNode F A C I} (h : P.ReachableNode n)
    (hstep : P.Step n n') : P.ReachableNode n' := Relation.ReflTransGen.tail h hstep

/-- Every reachable node has a well-formed task network. -/
lemma ReachableNode.wf (hP : P.WF) {n : SearchNode F A C I} (h : P.ReachableNode n) :
    n.net.WF := by
  induction h with
  | refl => exact hP.tnI
  | tail _ hstep ih =>
    cases hstep with
    | prog hu _ _ => exact TaskNetwork.progress_wf ih hu
    | decomp _ hstep => exact hstep.wf ih
  
end Problem

end HTN
