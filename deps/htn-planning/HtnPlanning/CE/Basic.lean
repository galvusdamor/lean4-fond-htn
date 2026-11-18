import Mathlib

/-!
# Classical planning with conditional effects

**Definitions only** (lemmas in `HtnPlanning/CE/Theory/Lemmas.lean`).  This file formalises
the syntax and semantics of classical planning with conditional effects (CEs) exactly as in the
preliminaries of

> A. E. Gerevini, F. Percassi, E. Scala,
> *An Effective Polynomial Technique for Compiling Conditional Effects Away*, AAAI 2024
> (the PDF `09960-AAAI24.GereviniA.pdf` in the repository root),

which is the setting of the compilation `τ^AP_SP` formalised in
`HtnCompilability/CE/TauApSp/TauApSp.lean`.

Unlike the STRIPS action model of `HtnPlanning/Core/Classical.lean`, this model has

* **negative literals** in preconditions, in the conditions of conditional effects, in the
  effects themselves and in the goal — a set of literals is represented by the pair
  `Lits.pos`/`Lits.neg` of its positive and its negative atoms;
* **conditional effects**: an action is a precondition together with a list of pairs
  `⟨cond, eff⟩`.  The list is only a presentation of the *set* of conditional effects — the
  semantics does not depend on the order (`HTN.CE.Action.adds_congr_perm` and friends in `HtnPlanning/CE/Theory/Lemmas.lean`) — but
  the compilation `τ^AP_SP` processes the conditional effects of an action one after the other,
  and the order in which it does so matters for its correctness, so it is convenient to have it
  available.

The semantics is the one of the source: an action `a` is applicable in `s` if `s ⊨ pre(a)` and
the conditional effects that are *active* in `s` do not conflict, and then `f ∈ s[a]` iff some
active effect adds `f`, or `f ∈ s` and no active effect deletes `f`.

The classes `SP` (simple planning problems: no conditions), `AP` (effect-acyclic problems) and
`CP` (arbitrary problems) of the source are `HTN.CE.Problem.IsSimple`,
`HTN.CE.Problem.IsAcyclic` and, respectively, no condition at all.
-/

namespace HTN

namespace CE

universe u v w

/-! ### Literals -/

/-- A set of literals over the atoms `F`, given by its positive and its negative part. -/
structure Lits (F : Type u) where
  /-- The atoms occurring positively. -/
  pos : Set F
  /-- The atoms occurring negatively. -/
  neg : Set F

namespace Lits

variable {F : Type u}

instance : EmptyCollection (Lits F) := ⟨⟨∅, ∅⟩⟩

/-- The atoms occurring in a set of literals. -/
def atoms (L : Lits F) : Set F := L.pos ∪ L.neg

/-- The union of two sets of literals. -/
def union (L L' : Lits F) : Lits F := ⟨L.pos ∪ L'.pos, L.neg ∪ L'.neg⟩

/-- `s ⊨ L`: every positive literal of `L` holds in `s` and no negative one does. -/
def Holds (L : Lits F) (s : Set F) : Prop := L.pos ⊆ s ∧ ∀ f ∈ L.neg, f ∉ s

/-- A set of literals is consistent if no atom occurs both positively and negatively. -/
def Consistent (L : Lits F) : Prop := ∀ f ∈ L.pos, f ∉ L.neg

end Lits

/-! ### Actions with conditional effects -/

/-- A conditional effect `⟨cond, eff⟩`. -/
structure CEff (F : Type u) where
  /-- The condition under which the effect is applied. -/
  cond : Lits F
  /-- The effect: the positive literals are added, the negative ones deleted. -/
  eff : Lits F

/-- An action: a precondition and a list of conditional effects. -/
structure Action (F : Type u) where
  /-- The precondition. -/
  pre : Lits F
  /-- The conditional effects. -/
  post : List (CEff F)

namespace Action

variable {F : Type u}

/-- The facts added by an action in a state: those added by an *active* conditional effect. -/
def adds (a : Action F) (s : Set F) : Set F :=
  {f | ∃ e ∈ a.post, e.cond.Holds s ∧ f ∈ e.eff.pos}

/-- The facts deleted by an action in a state: those deleted by an *active* conditional
effect. -/
def dels (a : Action F) (s : Set F) : Set F :=
  {f | ∃ e ∈ a.post, e.cond.Holds s ∧ f ∈ e.eff.neg}

/-- The active conditional effects of an action do not conflict: no fact is both added and
deleted. -/
def NoConflict (a : Action F) (s : Set F) : Prop := ∀ f ∈ a.adds s, f ∉ a.dels s

/-- An action is applicable if its precondition holds and its active effects do not
conflict. -/
def Applicable (a : Action F) (s : Set F) : Prop := a.pre.Holds s ∧ a.NoConflict s

/-- The successor state `s[a]`. -/
def succ (a : Action F) (s : Set F) : Set F := (s \ a.dels s) ∪ a.adds s

/-- An action all of whose conditional effects are unconditional. -/
def IsSimple (a : Action F) : Prop := ∀ e ∈ a.post, e.cond = (∅ : Lits F)

/-! #### The semantics does not depend on the order of the conditional effects -/

end Action

/-! ### Effect interference -/

variable {F : Type u}

/-- **Definition 2 (effect interference).**  `e` interferes with `e'` if an atom of the effect
of `e` occurs in the condition of `e'`. -/
def Interferes (e e' : CEff F) : Prop := ¬ Disjoint e.eff.atoms e'.cond.atoms

/-- A list of conditional effects is *interference free* if no effect interferes with a later
one — i.e. the list is a topological ordering of the transpose of the effect interference
graph, which is what `τ^AP_SP` uses to sequence the effects of an action. -/
def Interfree (l : List (CEff F)) : Prop :=
  l.Pairwise (fun e e' => Disjoint e.eff.atoms e'.cond.atoms)

/-- **Definition 4 (effect acyclic action).**  An action is effect acyclic iff its conditional
effects can be enumerated in an interference-free order. -/
def Action.EffectAcyclic (a : Action F) : Prop := ∃ l, l.Perm a.post ∧ Interfree l

/-! ### Planning problems -/

/-- A classical planning problem with conditional effects `Π = ⟨F, A, I, G⟩`. -/
structure Problem (F : Type u) (A : Type v) where
  /-- The action model. -/
  act : A → Action F
  /-- The initial state. -/
  init : Set F
  /-- The goal, a set of literals. -/
  goal : Lits F

namespace Problem

variable {A : Type v} (P : Problem F A)

/-- The state reached by executing a sequence of actions (applicability is not required). -/
def transitionSeq : List A → Set F → Set F
  | [], s => s
  | a :: as, s => transitionSeq as ((P.act a).succ s)

/-- A sequence of actions is applicable if each action is applicable when its turn comes. -/
def SeqApplicable : List A → Set F → Prop
  | [], _ => True
  | a :: as, s => (P.act a).Applicable s ∧ SeqApplicable as ((P.act a).succ s)

/-- A solution is an applicable plan reaching a goal state. -/
def IsSolution (plan : List A) : Prop :=
  P.SeqApplicable plan P.init ∧ P.goal.Holds (P.transitionSeq plan P.init)

/-- A problem is solvable if it has a solution. -/
def Solvable : Prop := ∃ plan, P.IsSolution plan

/-- **The class `SP`**: all actions are simple (no conditional effects). -/
def IsSimple : Prop := ∀ a : A, (P.act a).IsSimple

/-- **The class `AP`**: all actions are effect acyclic. -/
def IsAcyclic : Prop := ∀ a : A, (P.act a).EffectAcyclic

end Problem

end CE

end HTN
