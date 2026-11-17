import FondHtn.Basic
/-!
# FOND HTN planning with fixed methods (`FONDFM`, [CB21], [DB25])

In [CB21] a solution first fixes a sequence of decompositions leading from `tn_I` to a primitive
task network `tn` ("achievable primitive task network", Def. 2.5) and then executes `tn`.
Nondeterminism is taken into account either at plan generation time (a fixed linearisation,
**linearisation-dependent**, LD, Def. 2.7) or at execution time (a policy choosing the next task
depending on the observed outcomes, **outcome-dependent**, OD, Defs. 2.8–2.11).  Each comes in a
*weak* and a *strong* flavour.

| paper | here |
| --- | --- |
| linearisation [Def. 2.6] | `HTN.TaskNetwork.IsLinearization` |
| `Sᵢ` / executability of a linearisation for all outcomes | `FOND.Problem.StrongExec` |
| executability for some outcomes | `FOND.Problem.WeakExec` |
| strong / weak LD solution [Def. 2.7] | `IsStrongLDSolution`, `IsWeakLDSolution` |
| policy `π : 2^T × S → T` [Def. 2.8] | `FOND.FMPolicy` |
| execution structure / sequences [Defs. 2.9, 2.10] | `FMConfig`, `FMValid`, `FMStep`, `FMReach` |
| strong / weak OD solution [Def. 2.11] | `IsStrongODSolution`, `IsWeakODSolution` |
| solvable belief state [DB25] | `FOND.Problem.BeliefSolvable` |
| solvability of `H` [DB25] | `FOND.Problem.FMSolvableDB` |

**Faithfulness notes.**

* *Policies and execution sequences.*  Taken literally, Defs. 2.9–2.11 of [CB21] are not what is
  intended: the execution structure is built from states that are "executable by" *some* set of
  tasks, independently of the history, and "every execution sequence is complete" fails for every
  policy, since every one-element prefix of a complete execution sequence is itself an execution
  sequence.  We formalise the evident intent, which is also what the proofs of Props. 2.12, 2.13
  and 2.15 use: a run of a policy is a sequence of configurations `(T', s)` (the executed tasks and
  the current state), in which the policy chooses a task `t ∉ T'` all of whose predecessors are in
  `T'` and whose action is applicable in `s`, and the next state is any outcome of the action.
  A policy is a *strong* OD solution iff no run gets stuck before all tasks are executed (runs
  always terminate, as every step executes a new task), and a *weak* OD solution iff some run
  executes all tasks.
* The side condition of Def. 2.8 on the policy (`t ∉ T'`, all predecessors of `t` in `T'`) is
  checked when the policy is executed (`FMValid`); an instruction violating it simply makes the
  run stuck.
* [DB25] reformulates strong OD solvability through *solvable belief states*.  Their definition
  quantifies over sets of pairs `(tn, s)`; as solvability of a set is the conjunction of the
  solvability of its members, we state it pointwise (`BeliefSolvable`).  The theorem
  `FOND.Problem.strongOD_iff_beliefSolvable` shows that it agrees with the strong OD criterion
  formalised here.
-/

namespace FOND

open HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable (P : Problem F A C I)

/-! ## Linearisation-dependent solutions [CB21 Def. 2.7] -/

/-- **Weak executability** of an action sequence from a state: some choice of outcomes makes every
action applicable (`∃ s₁ = s_I, s₂, …` with `τ(tᵢ, sᵢ)` and `sᵢ₊₁ ∈ γ(tᵢ, sᵢ)`). -/
def WeakExec : List A → Set F → Prop
  | [], _ => True
  | a :: as, s => (P.δ a).Applicable s ∧ ∃ s' ∈ (P.δ a).outcomes s, WeakExec as s'

/-- **Strong executability** of an action sequence from a set `S` of states: every action is
applicable in every state of the current set `Sᵢ`, where `S₁ = S` and
`Sᵢ₊₁ = ⋃_{s ∈ Sᵢ} γ(tᵢ, s)`. -/
def StrongExec : List A → Set (Set F) → Prop
  | [], _ => True
  | a :: as, S => (∀ s ∈ S, (P.δ a).Applicable s) ∧
      StrongExec as {s' | ∃ s ∈ S, s' ∈ (P.δ a).outcomes s}

variable [DecidableEq I]

/-- **Weak LD solution** [CB21 Def. 2.7]: the linearisation `l` of an achievable primitive task
network `tn` is executable for some outcomes of its actions. -/
def IsWeakLDSolution (tn : TaskNetwork I A C) (l : List I) : Prop :=
  P.AchievablePrimitive tn ∧ tn.IsLinearization l ∧
    ∃ as : List A, tn.IsActionSeq l as ∧ P.WeakExec as P.init

/-- **Strong LD solution** [CB21 Def. 2.7]: the linearisation `l` of an achievable primitive
task network `tn` is executable for all outcomes of its actions. -/
def IsStrongLDSolution (tn : TaskNetwork I A C) (l : List I) : Prop :=
  P.AchievablePrimitive tn ∧ tn.IsLinearization l ∧
    ∃ as : List A, tn.IsActionSeq l as ∧ P.StrongExec as {P.init}

end Problem

/-! ## Outcome-dependent solutions [CB21 Defs. 2.8–2.11] -/

/-- A **policy** for a primitive task network [CB21 Def. 2.8]: a partial function from the set
`T'` of already executed tasks and the current state to the next task to execute. -/
abbrev FMPolicy (F : Type u) (I : Type x) : Type (max u x) := Finset I → Set F → Option I

/-- A configuration of the execution of a policy: the executed tasks `T'` and the current
state. -/
structure FMConfig (F : Type u) (I : Type x) where
  /-- The tasks executed so far. -/
  done : Finset I
  /-- The current state. -/
  state : Set F

namespace Problem

variable (P : Problem F A C I)

/-- The policy `π` gives a **valid instruction** at the configuration `c` when executing `tn`:
it chooses a task `t ∉ T'` of `tn` all of whose predecessors have been executed, with an action
`a` applicable in the current state. -/
def FMValid (tn : TaskNetwork I A C) (π : FMPolicy F I) (c : FMConfig F I) (t : I) (a : A) :
    Prop :=
  π c.done c.state = some t ∧ t ∈ tn.T ∧ t ∉ c.done ∧
    (∀ t' ∈ tn.T, tn.ord t' t → t' ∈ c.done) ∧ tn.α t = Sum.inl a ∧ (P.δ a).Applicable c.state

variable [DecidableEq I]

/-- One step of the execution of `π` on `tn`: a valid instruction is executed and *some* outcome
of its action occurs. -/
def FMStep (tn : TaskNetwork I A C) (π : FMPolicy F I) (c c' : FMConfig F I) : Prop :=
  ∃ t a, P.FMValid tn π c t a ∧ ∃ s' ∈ (P.δ a).outcomes c.state, c' = ⟨insert t c.done, s'⟩

/-- The configurations reachable by executing `π` on `tn` from `(∅, s_I)` (the execution
sequences of [CB21 Def. 2.10]). -/
def FMReach (tn : TaskNetwork I A C) (π : FMPolicy F I) (c : FMConfig F I) : Prop :=
  Relation.ReflTransGen (P.FMStep tn π) ⟨∅, P.init⟩ c

/-- A configuration is **complete** iff all tasks of `tn` have been executed. -/
def FMComplete (tn : TaskNetwork I A C) (c : FMConfig F I) : Prop := c.done = tn.T

/-- `π` **strongly executes** `tn`: no execution gets stuck before it is complete. -/
def StrongOD (tn : TaskNetwork I A C) (π : FMPolicy F I) : Prop :=
  ∀ c, P.FMReach tn π c → FMComplete tn c ∨ ∃ t a, P.FMValid tn π c t a

/-- `π` **weakly executes** `tn`: some execution is complete. -/
def WeakOD (tn : TaskNetwork I A C) (π : FMPolicy F I) : Prop :=
  ∃ c, P.FMReach tn π c ∧ FMComplete tn c

/-- **Strong OD solution** [CB21 Def. 2.11]. -/
def IsStrongODSolution (tn : TaskNetwork I A C) (π : FMPolicy F I) : Prop :=
  P.AchievablePrimitive tn ∧ P.StrongOD tn π

/-- **Weak OD solution** [CB21 Def. 2.11]. -/
def IsWeakODSolution (tn : TaskNetwork I A C) (π : FMPolicy F I) : Prop :=
  P.AchievablePrimitive tn ∧ P.WeakOD tn π

/-! ### Plan existence -/

/-- The problem has a weak LD solution. -/
def WeakLDSolvable : Prop := ∃ tn l, P.IsWeakLDSolution tn l

/-- The problem has a strong LD solution. -/
def StrongLDSolvable : Prop := ∃ tn l, P.IsStrongLDSolution tn l

/-- The problem has a weak OD solution. -/
def WeakODSolvable : Prop := ∃ tn π, P.IsWeakODSolution tn π

/-- The problem has a strong OD solution. -/
def StrongODSolvable : Prop := ∃ tn π, P.IsStrongODSolution tn π

/-! ## Solvable belief states [DB25] -/

/-- **Solvable belief states** [DB25], pointwise: `(tn, s)` is solvable iff `tn` is empty, or
some `≺`-minimal primitive task `t` of `tn` is applicable in `s` and `(tn ∖ t, s')` is
(recursively) solvable for every outcome `s'`. -/
inductive BeliefSolvable : TaskNetwork I A C → Set F → Prop
  /-- The empty task network is solved. -/
  | empty {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) : BeliefSolvable tn s
  /-- Execute an unconstrained applicable primitive task; all outcomes must be solvable. -/
  | step {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, BeliefSolvable (tn.progress t) s') :
      BeliefSolvable tn s

/-- **Solvability of a FOND HTN problem** in the sense of [DB25] (fixed methods, strong):
some sequence of decompositions leads to a primitive task network `tn` with `(tn, s_I)`
solvable. -/
def FMSolvableDB : Prop := ∃ tn, P.AchievablePrimitive tn ∧ P.BeliefSolvable tn P.init

end Problem

end FOND
