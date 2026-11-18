import Mathlib
import HtnPlanning.Basic
/-!
# Classical (STRIPS-style) planning

This file formalises the classical planning part of the formal framework of

  D. Höller, P. Bercher, G. Behnke, S. Biundo,
  *HTN Planning as Heuristic Progression Search*, JAIR 67 (2020), Section 3.1.

There, a classical planning problem is a tuple `Pc = (L, A, s₀, g, δ)` where `L` is a set of
propositional environment facts, `s₀ ⊆ L` the initial state, `g ⊆ L` the goal description,
`A` a set of action names and `δ = (prec, add, del)` maps action names to sets of facts.

In this formalisation the set of facts `L` is represented by a *type* `F` (so `L` is the
universe of `F`) and the set of action names `A` by a type `A`.  A state is then a `Set F`,
following the closed-world assumption of the paper.
-/

namespace HTN

universe u v

namespace ActionModel

variable {F : Type u} {A : Type v} (δ : ActionModel F A)

@[simp] lemma transitionSeq_nil (s : Set F) : δ.transitionSeq [] s = s := rfl

@[simp] lemma transitionSeq_cons (a : A) (as : List A) (s : Set F) :
    δ.transitionSeq (a :: as) s = δ.transitionSeq as (δ.transition a s) := rfl

@[simp] lemma seqApplicable_nil (s : Set F) : δ.SeqApplicable [] s := trivial

@[simp] lemma seqApplicable_cons {a : A} {as : List A} {s : Set F} :
    δ.SeqApplicable (a :: as) s ↔
      δ.Applicable a s ∧ δ.SeqApplicable as (δ.transition a s) := Iff.rfl

lemma transitionSeq_append (as bs : List A) (s : Set F) :
    δ.transitionSeq (as ++ bs) s = δ.transitionSeq bs (δ.transitionSeq as s) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => simp [ih]

lemma seqApplicable_append (as bs : List A) (s : Set F) :
    δ.SeqApplicable (as ++ bs) s ↔
      δ.SeqApplicable as s ∧ δ.SeqApplicable bs (δ.transitionSeq as s) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => simp [ih, and_assoc]

end ActionModel

/-- A classical planning problem `Pc = (L, A, s₀, g, δ)`. -/
structure ClassicalProblem (F : Type u) (A : Type v) extends ActionModel F A where
  /-- The initial state `s₀`. -/
  init : Set F
  /-- The goal description `g`; a state `s` is a goal state iff `g ⊆ s`. -/
  goal : Set F

namespace ClassicalProblem

variable {F : Type u} {A : Type v} (P : ClassicalProblem F A)

/-- A state is a goal state iff it satisfies the goal description. -/
def GoalState (s : Set F) : Prop := P.goal ⊆ s

/-- A solution to a classical planning problem is a sequence of actions that is applicable in
the initial state and results in a goal state. -/
def IsSolution (plan : List A) : Prop :=
  P.SeqApplicable plan P.init ∧ P.GoalState (P.transitionSeq plan P.init)

/-- A classical planning problem is solvable iff it has a solution. -/
def Solvable : Prop := ∃ plan, P.IsSolution plan

end ClassicalProblem

end HTN
