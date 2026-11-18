import HtnPlanning.Computable.Syntax
import HtnPlanning.Core.Decomposition
/-!
# Path witnesses: a flat certificate of plan existence

This file starts the formalisation of the *upper bound* of the cell (`HTN-TR`, `HTN-AC`): plan
existence for acyclic HTN problems is in `NEXPTIME` (Alford et al. 2015).  The certificate is the
decomposition tree of a solution, written **flat**, as the list of its leaves, each leaf given by
its full path from the root:

* a **step** `(k, j)` names the task `j` of a task network: `k = 0` is the initial task network of
  the instance, `k = i + 1` is the subtask network of the `i`-th listed method;
* an **entry** is a pair `(p, ε)` of a path `p = [(0, i₀), (k₁, j₁), …, (kₘ, jₘ)]` and a flag:
  - `ε = false` — an *action leaf*: `jₘ` is a primitive task of its network, and `j_{r}` is
    decomposed by the method `k_{r+1}` for `r < m`;
  - `ε = true` — an *empty leaf*: the last step `(kₘ, jₘ)` only records that the compound task of
    the previous step was decomposed by the method `kₘ`, whose subtask network is empty (`jₘ` is
    a dummy).

A list `W` of entries is a **path witness** (`HTN.Syn.AcVer.PathOK`) when every entry is well
formed, any two entries diverge at a step where they agree on the method (the tree is
consistent), the actions leaves are listed in an order compatible with the inherited ordering
constraints, every task of every expanded network is present (the tree is complete), and the
action sequence of the action leaves is executable and reaches the goal.

The point of the flat form is that every condition is a condition on one entry or on two entries
of the list, which a polynomial-time verifier can check by quantifying over the entries of the
certificate.

The equivalence `Solvable d q ↔ ∃ W, PathOK d q W` is proved in
`HtnComplexity/AcVerify/Sound.lean` and `HtnComplexity/AcVerify/Complete.lean`.
-/

namespace HTN

namespace Syn

namespace AcVer

/-- A step of a path: a network index (`0` the initial task network, `k + 1` the `k`-th method)
and a task identifier of that network. -/
abbrev PStep : Type := ℕ × ℕ

/-- An entry of a path witness: the path of a leaf and the flag *empty leaf*. -/
abbrev Entry : Type := List PStep × Bool

/-- The default method description (never used on well-formed paths). -/
def dfltMethod : MethodDesc := (0, ([], [], []))

/-- The `k`-th listed method, by network index (`k ≥ 1`). -/
def methodAt (d : DomDesc) (k : ℕ) : MethodDesc := d.methods.getD (k - 1) dfltMethod

/-- **The task network a step refers to.** -/
def netOf (d : DomDesc) (q : InstDesc) (k : ℕ) : TnDesc :=
  if k = 0 then q.tnI else (methodAt d k).2

/-- The label of the task a step names. -/
def stepLabel (d : DomDesc) (q : InstDesc) (x : PStep) : ℕ ⊕ ℕ := (netOf d q x.1).label x.2

/-- **Two consecutive steps of a path**: the task of the first step is compound and decomposed by
the (listed) method of the second step. -/
def Link (d : DomDesc) (q : InstDesc) (x y : PStep) : Prop :=
  1 ≤ y.1 ∧ y.1 - 1 < d.methods.length ∧ stepLabel d q x = Sum.inr (methodAt d y.1).1

/-- A step names a task of its network. -/
def StepIn (d : DomDesc) (q : InstDesc) (x : PStep) : Prop := x.2 ∈ (netOf d q x.1).ids

/-- **A well-formed path to a task node**: it starts in the initial task network, consecutive
steps are linked, and every step names a task of its network. -/
def NodeOK (d : DomDesc) (q : InstDesc) (p : List PStep) : Prop :=
  (∃ i s, p = (0, i) :: s) ∧ p.IsChain (Link d q) ∧ ∀ x ∈ p, StepIn d q x

/-- The label of the node a path leads to. -/
def lastLabel (d : DomDesc) (q : InstDesc) (p : List PStep) : ℕ ⊕ ℕ :=
  match p.getLast? with
  | some x => stepLabel d q x
  | none => Sum.inl 0

/-- The action of an action leaf. -/
def leafAct (d : DomDesc) (q : InstDesc) (p : List PStep) : ℕ :=
  match lastLabel d q p with
  | Sum.inl a => a
  | Sum.inr _ => 0

/-- **A well-formed entry.**  An action leaf is a well-formed path to a primitive task; an empty
leaf is a well-formed path to a compound task followed by a step whose method has an empty
subtask network. -/
def EntryOK (d : DomDesc) (q : InstDesc) (u : Entry) : Prop :=
  if u.2 then
    ∃ p y, u.1 = p ++ [y] ∧ p ≠ [] ∧ NodeOK d q p ∧ u.1.IsChain (Link d q) ∧
      (netOf d q y.1).ids = []
  else
    NodeOK d q u.1 ∧ ∃ a, lastLabel d q u.1 = Sum.inl a

/-- `u` and `v` **diverge at** the steps `x` (in `u`) and `y` (in `v`): they share the part before,
and `x ≠ y`. -/
def DivAt (u v : List PStep) (x y : PStep) : Prop :=
  ∃ P su sv, u = P ++ x :: su ∧ v = P ++ y :: sv ∧ x ≠ y

/-- **The inherited order between two paths**: at their divergence they are in the same network
and ordered there. -/
def DivOrd (d : DomDesc) (q : InstDesc) (u v : List PStep) : Prop :=
  ∃ x y, DivAt u v x y ∧ x.1 = y.1 ∧ (netOf d q x.1).ordOf x.2 y.2

/-- **Two entries, `u` listed before `v`**: they diverge, at a step where they use the same
network (the tree is consistent); if both are action leaves, `v` is not ordered before `u`. -/
def PairOK (d : DomDesc) (q : InstDesc) (u v : Entry) : Prop :=
  ∃ x y, DivAt u.1 v.1 x y ∧ x.1 = y.1 ∧
    (u.2 = false → v.2 = false → ¬ (netOf d q x.1).ordOf y.2 x.2)

/-- **Completeness at the root**: every task of the initial task network starts some entry. -/
def RootsOK (q : InstDesc) (W : List Entry) : Prop :=
  ∀ i ∈ q.tnI.ids, ∃ u ∈ W, ∃ s, u.1 = (0, i) :: s

/-- **Completeness below a node**: whenever an entry decomposes the task of a step `x` by the
method of the next step `y`, every task of that method is the next step of some entry. -/
def ChildrenOK (d : DomDesc) (q : InstDesc) (W : List Entry) : Prop :=
  ∀ u ∈ W, ∀ (P : List PStep) (x y : PStep) (s : List PStep), u.1 = P ++ x :: y :: s →
    ∀ j ∈ (netOf d q y.1).ids, ∃ v ∈ W, ∃ s', v.1 = P ++ x :: (y.1, j) :: s'

/-- The action sequence of a path witness: the actions of its action leaves, in order. -/
def actsOf (d : DomDesc) (q : InstDesc) (W : List Entry) : List ℕ :=
  (W.filter fun u => !u.2).map fun u => leafAct d q u.1

/-- An action sequence is executable in the described problem and reaches its goal. -/
def ExecOK (d : DomDesc) (q : InstDesc) (as : List ℕ) : Prop :=
  (problem d q).SeqApplicable as (problem d q).init ∧
    (problem d q).GoalState ((problem d q).transitionSeq as (problem d q).init)

/-- **A path witness** of the described problem `(d, q)`. -/
structure PathOK (d : DomDesc) (q : InstDesc) (W : List Entry) : Prop where
  entries : ∀ u ∈ W, EntryOK d q u
  pairs : W.Pairwise (PairOK d q)
  roots : RootsOK q W
  children : ChildrenOK d q W
  exec : ExecOK d q (actsOf d q W)

end AcVer

end Syn

end HTN
