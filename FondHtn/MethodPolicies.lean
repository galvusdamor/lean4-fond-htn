import FondHtn.Basic
/-!
# FOND HTN planning with method-based policies (`FONDMP`, [CB22])

In [CB22] the choice of decomposition methods is part of the policy: a policy maps a pair
`(tn, s)` of a (not necessarily primitive) task network and a state to an instruction `(t, m)`,
either executing a primitive task `t` (`m = ε`) or decomposing a compound task `t` with the
method `m`.  Executing the policy from `(tn_I, s_I)` yields the *execution structure* (Def. 6),
a graph on pairs `(tn, s)` taken up to isomorphism of the task networks, and the solution criteria
weak / strong cyclic / strong (Def. 7) are properties of this graph.

| paper | here |
| --- | --- |
| policy `π : TN × S ⇀ T × M'`, `M' = M ∪ {ε}` [Def. 5] | `FOND.MPPolicy` (`none` encodes `ε`) |
| "no two isomorphic entries for the same state" [Def. 5] | `FOND.MPPolicy.WellDefined` |
| `InstructionExists` / `GetInstruction` [Alg. 1] | `FOND.MPInstr` |
| the edges `V` of the execution structure [Def. 6] | `FOND.Problem.MPStep` |
| the nodes `U` [Def. 6] | `FOND.Problem.MPReach` |
| the quotient `[L]` by isomorphism [Def. 6] | `MPNode.Iso`, used in `MPFinite`, `MPAcyclic` |
| terminal node / goal node | `MPTerminal`, `MPNode.IsGoal` |
| weak / strong cyclic / strong solution [Def. 7] | `IsMPWeakSolution`, `IsMPStrongCyclicSolution`, `IsMPStrongSolution` |

**Faithfulness notes.**

* *The quotient.*  A policy is a function on concrete task networks; following Algorithm 1, at a
  node `(tn, s)` the instruction is looked up at an entry `(tn', s)` of the policy with
  `tn' ≅ tn` and transported along the isomorphism (`MPInstr`; the paper leaves the transport
  implicit).  Nodes are concrete pairs, and the quotient `[L]` of Def. 6 is taken into account
  wherever it matters: finiteness of `[L]` means finitely many isomorphism classes of reachable
  nodes (`MPFinite`), and a cycle of `[L]` is a non-empty path from a node to an isomorphic one
  (`MPAcyclic`).  Being terminal and being a goal node are invariant under isomorphism.
* *Executing primitive tasks.*  Def. 6 does not require an executed primitive task to have no
  predecessors (Def. 5 does not either), which would make the ordering of primitive tasks
  meaningless; the search algorithm of [CB22] (Alg. 2) only executes tasks without predecessors.
  We require the executed task to be unconstrained (`MPStep.prim`).  Compound tasks may be
  decomposed regardless of their position, exactly as in Defs. 5–6.
* *Ill-typed instructions.*  An instruction `(t, ε)` for a compound `t`, `(t, m)` for a primitive
  `t` or for a method `m` not decomposing `α(t)`, or `(t, ε)` for an inapplicable `t` has no
  successors in Def. 6; the node is then terminal (and not a goal node unless `tn` is empty).
* *Strong cyclic solutions* are formalised as stated in Def. 7: every terminal node is a goal node.
  In particular, an execution may go on forever (e.g. by decomposing a recursive task
  indefinitely) — this differs from the usual notion of Cimatti et al. (from every reachable node
  a goal node is reachable), which is provided as `IsMPStrongCyclicFairSolution` for comparison.
* Decomposition needs fresh task ids; the notions are only meaningful for an infinite type `I`.
-/

namespace HTN

namespace TaskNetwork

universe v w x

variable {I : Type x} {A : Type v} {C : Type w}

/-- `σ` is an isomorphism from `tn` to `tn'` (`tn.Iso tn'` is `∃ σ, IsoVia σ tn tn'`). -/
def IsoVia (σ : I → I) (tn tn' : TaskNetwork I A C) : Prop :=
  Set.BijOn σ (tn.T : Set I) (tn'.T : Set I) ∧
    (∀ t ∈ tn.T, ∀ t' ∈ tn.T, (tn.ord t t' ↔ tn'.ord (σ t) (σ t'))) ∧
    (∀ t ∈ tn.T, tn.α t = tn'.α (σ t))

lemma iso_iff_exists_isoVia {tn tn' : TaskNetwork I A C} : tn.Iso tn' ↔ ∃ σ, IsoVia σ tn tn' :=
  Iff.rfl

end TaskNetwork

end HTN

namespace FOND

open HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- A **method-based policy** [CB22 Def. 5]: a partial function mapping a task network and a
state to a task of the network together with either a method decomposing it (`some m`) or `ε`
(`none`, execute the primitive task). -/
abbrev MPPolicy (F : Type u) (A : Type v) (C : Type w) (I : Type x) :=
  TaskNetwork I A C → Set F → Option (I × Option (Method I A C))

/-- The well-definedness condition on policies of [CB22 Def. 5]: for the same state, the
policy is not defined on two distinct isomorphic task networks. -/
def MPPolicy.WellDefined (π : MPPolicy F A C I) : Prop :=
  ∀ (tn tn' : TaskNetwork I A C) (s : Set F),
    (π tn s).isSome → (π tn' s).isSome → tn.Iso tn' → tn = tn'

/-- A node `(tn, s)` of the execution structure (a "subproblem"). -/
structure MPNode (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The remaining task network. -/
  net : TaskNetwork I A C
  /-- The current state. -/
  state : Set F

namespace MPNode

/-- `(tn, s) ∼ (tn', s')` iff `s = s'` and `tn ≅ tn'` [CB22 Def. 6]. -/
def Iso (x y : MPNode F A C I) : Prop := x.state = y.state ∧ x.net.Iso y.net

/-- A **goal node**: the task network is empty. -/
def IsGoal (x : MPNode F A C I) : Prop := x.net.T = ∅

end MPNode

/-- The instruction `(t, m)` that `π` gives at the node `x` (`GetInstruction` of [CB22 Alg. 1]):
`π` has an entry `(tn', x.state) ↦ (t', m)` for a task network `tn'` isomorphic to `x.net`, and
`t` is the image of `t'` under the isomorphism. -/
def MPInstr (π : MPPolicy F A C I) (x : MPNode F A C I) (t : I) (mo : Option (Method I A C)) :
    Prop :=
  ∃ (tn' : TaskNetwork I A C) (σ : I → I) (t' : I), tn'.IsoVia σ x.net ∧ t' ∈ tn'.T ∧
    π tn' x.state = some (t', mo) ∧ t = σ t'

namespace Problem

variable (P : Problem F A C I)

variable [DecidableEq I]

/-- The edges of the **execution structure** induced by `π` [CB22 Def. 6]. -/
inductive MPStep (π : MPPolicy F A C I) : MPNode F A C I → MPNode F A C I → Prop
  /-- `π` says to execute the primitive task `t`: for every outcome `s'` there is an edge to
  `(tn ∖ t, s')`. -/
  | prim {x : MPNode F A C I} {t : I} {a : A} {s' : Set F} (hi : MPInstr π x t none)
      (hu : x.net.Unconstrained t) (hα : x.net.α t = Sum.inl a)
      (happ : (P.δ a).Applicable x.state) (hs' : s' ∈ (P.δ a).outcomes x.state) :
      MPStep π x ⟨x.net.progress t, s'⟩
  /-- `π` says to decompose the compound task `t` with `m`: there is an edge to `(tn', s)` with
  `tn →_{t,m} tn'`. -/
  | decomp {x : MPNode F A C I} {t : I} {m : Method I A C} {tn' : TaskNetwork I A C}
      (hi : MPInstr π x t (some m)) (hd : DecompStep P.methods x.net t m tn') :
      MPStep π x ⟨tn', x.state⟩

/-- The initial node `(tn_I, s_I)`. -/
def mpInit : MPNode F A C I := ⟨P.tnI, P.init⟩

/-- The nodes `U` of the execution structure: those reachable from `(tn_I, s_I)`. -/
def MPReach (π : MPPolicy F A C I) (x : MPNode F A C I) : Prop :=
  Relation.ReflTransGen (P.MPStep π) P.mpInit x

/-- A **terminal** node has no outgoing edges. -/
def MPTerminal (π : MPPolicy F A C I) (x : MPNode F A C I) : Prop := ∀ y, ¬ P.MPStep π x y

/-- The execution structure `[L]` is **finite**: the reachable nodes fall into finitely many
isomorphism classes. -/
def MPFinite (π : MPPolicy F A C I) : Prop :=
  ∃ S : Set (MPNode F A C I), S.Finite ∧ ∀ x, P.MPReach π x → ∃ y ∈ S, x.Iso y

/-- The execution structure `[L]` is **acyclic**: no non-empty path leads from a reachable node
to a node isomorphic to it. -/
def MPAcyclic (π : MPPolicy F A C I) : Prop :=
  ∀ x y, P.MPReach π x → Relation.TransGen (P.MPStep π) x y → ¬ x.Iso y

/-- **Weak solution** [CB22 Def. 7]: `[L]` is finite and some terminal node is a goal node. -/
def IsMPWeakSolution (π : MPPolicy F A C I) : Prop :=
  π.WellDefined ∧ P.MPFinite π ∧ ∃ x, P.MPReach π x ∧ P.MPTerminal π x ∧ x.IsGoal

/-- **Strong cyclic solution** [CB22 Def. 7]: every terminal node is a goal node. -/
def IsMPStrongCyclicSolution (π : MPPolicy F A C I) : Prop :=
  π.WellDefined ∧ ∀ x, P.MPReach π x → P.MPTerminal π x → x.IsGoal

/-- **Strong (acyclic) solution** [CB22 Def. 7]: `[L]` is finite and acyclic and every terminal
node is a goal node. -/
def IsMPStrongSolution (π : MPPolicy F A C I) : Prop :=
  π.WellDefined ∧ P.MPFinite π ∧ P.MPAcyclic π ∧ ∀ x, P.MPReach π x → P.MPTerminal π x → x.IsGoal

/-- *Not the definition of [CB22]*, for comparison: strong cyclic solutions in the usual sense
of Cimatti et al. — from every reachable node some goal node is reachable. -/
def IsMPStrongCyclicFairSolution (π : MPPolicy F A C I) : Prop :=
  π.WellDefined ∧ ∀ x, P.MPReach π x →
    ∃ y, Relation.ReflTransGen (P.MPStep π) x y ∧ y.IsGoal

/-! ### Plan existence -/

/-- The problem has a weak `FONDMP` solution. -/
def MPWeakSolvable : Prop := ∃ π, P.IsMPWeakSolution π

/-- The problem has a strong cyclic `FONDMP` solution. -/
def MPStrongCyclicSolvable : Prop := ∃ π, P.IsMPStrongCyclicSolution π

/-- The problem has a strong `FONDMP` solution. -/
def MPStrongSolvable : Prop := ∃ π, P.IsMPStrongSolution π

/-! ### An AND/OR characterisation of strong solvability -/

/-- `(tn, s)` is **strongly solvable with method-based policies**: `tn` is empty, or some
unconstrained primitive task is applicable and all its outcomes lead to strongly solvable pairs,
or some decomposition leads to a strongly solvable pair.  This is the game underlying the
alternating progression search of [CB22, Alg. 2].  Its agreement with `MPStrongSolvable` (for an
infinite id type) is not yet proved. -/
inductive MPAndOr : TaskNetwork I A C → Set F → Prop
  /-- The empty task network is solved. -/
  | empty {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) : MPAndOr tn s
  /-- Execute an unconstrained applicable primitive task; all outcomes must be solvable. -/
  | prim {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, MPAndOr (tn.progress t) s') : MPAndOr tn s
  /-- Decompose a compound task. -/
  | decomp {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}
      (hd : DecompStep P.methods tn t m tn') (h : MPAndOr tn' s) : MPAndOr tn s

end Problem

end FOND
