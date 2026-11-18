import Mathlib
import ComplexityTheory.TM.Basic
import ComplexityTheory.Complexity.Basic
/-!
# HTN planning

**Definitions only.**  The objects of hierarchical task network planning, following the
formalisation of the reference paper:

* the classical (STRIPS) action model `HTN.ActionModel` and its transition function;
* task networks `HTN.TaskNetwork` (task identifiers, a partial order, a labelling by primitive
  and compound task names), methods `HTN.Method`, decomposition `HTN.DecompStep`,
  `HTN.DecomposesTo`;
* planning problems `HTN.Problem`, their solutions `HTN.Problem.IsSolution` and plan existence
  `HTN.Problem.Solvable`; reachable compound tasks and methods;
* domains `HTN.Domain` and instances `HTN.Instance`, their sizes, and compilation schemes
  between classes of problems `HTN.CompilationScheme`;
* the finite *descriptions* of domains and instances over `ℕ` (`HTN.Syn.DomDesc`,
  `HTN.Syn.InstDesc`), the problem `HTN.Syn.problem d q` a pair of descriptions denotes, their
  sizes, and their serialisation into bit strings `HTN.Syn.instSer`.
-/

/-! ## Classical planning -/

namespace HTN

universe u v

/-- The action model `δ = (prec, add, del)` of a planning problem: it maps every action name
to its precondition, add list and delete list. -/
structure ActionModel (F : Type u) (A : Type v) where
  /-- The precondition of an action. -/
  prec : A → Set F
  /-- The facts added by an action. -/
  add : A → Set F
  /-- The facts deleted by an action. -/
  del : A → Set F

namespace ActionModel

variable {F : Type u} {A : Type v} (δ : ActionModel F A)

/-- An action `a` is applicable in a state `s` iff its precondition holds in `s`,
i.e. `τ(a, s) ⇔ prec(a) ⊆ s`. -/
def Applicable (a : A) (s : Set F) : Prop := δ.prec a ⊆ s

/-- The state transition function `γ(a, s) = (s \ del(a)) ∪ add(a)`. -/
def transition (a : A) (s : Set F) : Set F := (s \ δ.del a) ∪ δ.add a

/-- The state resulting from applying a whole sequence of actions to a state
(applicability is *not* required by this function; see `ActionModel.SeqApplicable`). -/
def transitionSeq : List A → Set F → Set F
  | [], s => s
  | a :: as, s => transitionSeq as (δ.transition a s)

/-- A sequence of actions `⟨a₀ a₁ … aₗ⟩` is applicable in a state `s` iff each `aᵢ` is
applicable in the state reached after executing `a₀ … aᵢ₋₁`. -/
def SeqApplicable : List A → Set F → Prop
  | [], _ => True
  | a :: as, s => δ.Applicable a s ∧ SeqApplicable as (δ.transition a s)

end ActionModel

end HTN

/-! ## Task networks -/

namespace HTN

universe u v w

/-- A task network `tn = (T, ≺, α)` over the id type `I`, primitive task names `A` and
abstract task names `C`. -/
structure TaskNetwork (I : Type u) (A : Type v) (C : Type w) where
  /-- The (finite) set of task identifiers of the network. -/
  T : Finset I
  /-- The strict partial order `≺` on the task identifiers. -/
  ord : I → I → Prop
  /-- The labelling of ids with task names, primitive (`A`) or abstract (`C`). -/
  α : I → A ⊕ C

namespace TaskNetwork

variable {I : Type u} {A : Type v} {C : Type w}

/-- Well-formedness of a task network: `≺` is irreflexive and transitive (hence asymmetric),
and it only relates task ids that belong to the network. -/
structure WF (tn : TaskNetwork I A C) : Prop where
  /-- Only ids of the network are ordered (left component). -/
  mem_left : ∀ {t t' : I}, tn.ord t t' → t ∈ tn.T
  /-- Only ids of the network are ordered (right component). -/
  mem_right : ∀ {t t' : I}, tn.ord t t' → t' ∈ tn.T
  /-- The order is irreflexive. -/
  irrefl : ∀ t : I, ¬ tn.ord t t
  /-- The order is transitive. -/
  trans : ∀ {a b c : I}, tn.ord a b → tn.ord b c → tn.ord a c

/-- An id is *primitive* in a task network iff it is mapped to an action name. -/
def IsPrimitiveId (tn : TaskNetwork I A C) (t : I) : Prop := ∃ a : A, tn.α t = Sum.inl a

/-- An id is *abstract* in a task network iff it is mapped to an abstract task name. -/
def IsAbstractId (tn : TaskNetwork I A C) (t : I) : Prop := ∃ c : C, tn.α t = Sum.inr c

/-- A task network is primitive iff all of its tasks are primitive. -/
def IsPrimitive (tn : TaskNetwork I A C) : Prop := ∀ t ∈ tn.T, tn.IsPrimitiveId t

/-- Two task networks are isomorphic (`tn ≅ tn'`) iff they differ only in their identifiers:
there is a bijection `σ : T → T'` preserving the ordering and the task names. -/
def Iso (tn tn' : TaskNetwork I A C) : Prop :=
  ∃ σ : I → I, Set.BijOn σ (tn.T : Set I) (tn'.T : Set I) ∧
    (∀ t ∈ tn.T, ∀ t' ∈ tn.T, (tn.ord t t' ↔ tn'.ord (σ t) (σ t'))) ∧
    (∀ t ∈ tn.T, tn.α t = tn'.α (σ t))

/-- A list `l` of ids is a linearization of a task network iff it enumerates the tasks of the
network without repetition, in an order that is in line with `≺`, i.e. `∀ i < j : (lⱼ, lᵢ) ∉ ≺`. -/
def IsLinearization (tn : TaskNetwork I A C) (l : List I) : Prop :=
  l.Nodup ∧ (∀ t, t ∈ l ↔ t ∈ tn.T) ∧ l.Pairwise (fun a b => ¬ tn.ord b a)

/-- `as` is the sequence of action names induced by the sequence of ids `l`, i.e.
`⟨α(t₁) α(t₂) … α(tₙ)⟩` (which requires all these ids to be primitive). -/
def IsActionSeq (tn : TaskNetwork I A C) (l : List I) (as : List A) : Prop :=
  l.map tn.α = as.map Sum.inl

end TaskNetwork

end HTN

/-! ## Methods and decomposition -/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

/-- A decomposition method `m = (c, tn)`: the abstract task name `c` that it decomposes,
together with its subtask network. -/
structure Method (I : Type u) (A : Type v) (C : Type w) where
  /-- The abstract task name decomposed by the method. -/
  abstractTask : C
  /-- The subtask network of the method. -/
  subtasks : TaskNetwork I A C

/-- The result of replacing the task `t` of `tn₁` by the (fresh) task network `tn'`.

This is the task network `tn₂` of the decomposition definition of the paper; freshness of the
identifiers of `tn'` (`Disjoint tn₁.T tn'.T`) is *not* part of this definition but is required
by `HTN.DecompStep`. -/
def decomposeWith [DecidableEq I] (tn₁ : TaskNetwork I A C) (t : I) (tn' : TaskNetwork I A C) :
    TaskNetwork I A C where
  T := (tn₁.T.erase t) ∪ tn'.T
  ord := fun a b =>
    tn'.ord a b ∨
    (tn₁.ord a t ∧ b ∈ tn'.T) ∨
    (tn₁.ord t b ∧ a ∈ tn'.T) ∨
    (tn₁.ord a b ∧ a ≠ t ∧ b ≠ t)
  α := fun x => if x ∈ tn'.T then tn'.α x else tn₁.α x

/-- `DecompStep M tn₁ t m tn₂` states that the task network `tn₁` can be decomposed into `tn₂`
by applying the method `m ∈ M` to the task id `t`, written `tn₁ --t,m--> tn₂` in the paper.

The inserted copy `tn'` of the method's subtask network is required to be well formed; in the
paper this is implicit, since there every task network carries a strict partial order by
definition, whereas here `TaskNetwork.WF` is a separate predicate. -/
def DecompStep [DecidableEq I] (M : Set (Method I A C)) (tn₁ : TaskNetwork I A C) (t : I)
    (m : Method I A C) (tn₂ : TaskNetwork I A C) : Prop :=
  m ∈ M ∧ t ∈ tn₁.T ∧ tn₁.α t = Sum.inr m.abstractTask ∧
    ∃ tn' : TaskNetwork I A C,
      tn'.WF ∧ tn'.Iso m.subtasks ∧ Disjoint tn₁.T tn'.T ∧ tn₂ = decomposeWith tn₁ t tn'

/-- One decomposition step with the method and the decomposed task existentially quantified. -/
def DecompStep' [DecidableEq I] (M : Set (Method I A C)) (tn₁ tn₂ : TaskNetwork I A C) : Prop :=
  ∃ t m, DecompStep M tn₁ t m tn₂

/-- `DecomposesTo M tn tn'` (written `tn →* tn'` in the paper) holds iff `tn` can be decomposed
into `tn'` by a (possibly empty) sequence of method applications. -/
def DecomposesTo [DecidableEq I] (M : Set (Method I A C)) (tn tn' : TaskNetwork I A C) : Prop :=
  Relation.ReflTransGen (DecompStep' M) tn tn'

end HTN

/-! ## Planning problems and solutions -/

namespace HTN

universe u v w x

/-- An HTN planning problem `P = (L, C, A, M, s₀, tn_I, g, δ)`. -/
structure Problem (F : Type u) (A : Type v) (C : Type w) (I : Type x)
    extends ActionModel F A where
  /-- The set `M` of decomposition methods. -/
  methods : Set (Method I A C)
  /-- The initial state `s₀`. -/
  init : Set F
  /-- The goal description `g`. -/
  goal : Set F
  /-- The initial task network `tn_I`. -/
  tnI : TaskNetwork I A C

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

section

variable (P : Problem F A C I)

/-- Well-formedness of an HTN planning problem: the initial task network and all subtask
networks of the methods are well-formed task networks. -/
structure WF : Prop where
  /-- The initial task network is well formed. -/
  tnI : P.tnI.WF
  /-- All subtask networks of the methods are well formed. -/
  methods : ∀ m ∈ P.methods, m.subtasks.WF

/-- A state is a goal state iff it satisfies the goal description `g`. -/
def GoalState (s : Set F) : Prop := P.goal ⊆ s

/-- The third solution criterion: the task network `tn` has a linearization whose action
sequence is applicable in the initial state and leads to a goal state. -/
def Executable (tn : TaskNetwork I A C) : Prop :=
  ∃ (l : List I) (as : List A), tn.IsLinearization l ∧ tn.IsActionSeq l as ∧
    P.SeqApplicable as P.init ∧ P.GoalState (P.transitionSeq as P.init)

end

section

variable [DecidableEq I] (P : Problem F A C I)

/-- `P.DecomposesTo tn tn'` holds iff `tn →* tn'` using the methods of `P`. -/
def DecomposesTo (tn tn' : TaskNetwork I A C) : Prop := HTN.DecomposesTo P.methods tn tn'

/-- The task networks reachable from the initial task network by decomposition. -/
def Reachable (tn : TaskNetwork I A C) : Prop := P.DecomposesTo P.tnI tn

/-- **Solution criteria.** A task network is a solution to an HTN planning problem iff it is
reachable from the initial task network by decomposition, it is primitive, and it has an
executable linearization leading to a goal state. -/
def IsSolution (tn : TaskNetwork I A C) : Prop :=
  P.Reachable tn ∧ tn.IsPrimitive ∧ P.Executable tn

/-- An HTN planning problem is solvable iff it has a solution. -/
def Solvable : Prop := ∃ tn, P.IsSolution tn

end

end Problem

end HTN

/-! ## Reachable compound tasks and methods -/

namespace HTN

namespace Problem

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- The compound task names reachable from the initial task network by a top-down analysis:
the names occurring in `tn_I`, closed under "occurs in the subtask network of a method whose
decomposed name is reachable". -/
inductive ReachableName (P : Problem F A C I) : C → Prop
  /-- A compound task name occurring in the initial task network is reachable. -/
  | tnI {t : I} {c : C} (ht : t ∈ P.tnI.T) (hc : P.tnI.α t = Sum.inr c) : ReachableName P c
  /-- A compound task name occurring in the subtask network of a method whose decomposed task
  name is reachable is itself reachable. -/
  | method {m : Method I A C} {t : I} {c : C} (hm : m ∈ P.methods)
      (hr : ReachableName P m.abstractTask) (ht : t ∈ m.subtasks.T)
      (hc : m.subtasks.α t = Sum.inr c) : ReachableName P c

/-- A method is *reachable* iff it belongs to the domain and the compound task name it
decomposes is reachable from the initial task network. -/
def ReachableMethod (P : Problem F A C I) (m : Method I A C) : Prop :=
  m ∈ P.methods ∧ P.ReachableName m.abstractTask

end Problem

end HTN

/-! ## Domains, instances, sizes and compilation schemes -/

namespace HTN

universe u v w x u' v' w' x'

/-- The *domain* part `D = (S, O, M)` of an HTN planning problem: the action model (the
operators `O` with their preconditions and effects) together with the set of decomposition
methods `M`.  The signature `S = (V, C)` is represented by the types `F` and `C`. -/
structure Domain (F : Type u) (A : Type v) (C : Type w) (I : Type x) extends ActionModel F A where
  /-- The set of decomposition methods. -/
  methods : Set (Method I A C)

/-- The *problem* part `P = (s_I, g_I, tn_I)` of an HTN planning problem. -/
structure Instance (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The initial state. -/
  init : Set F
  /-- The goal description. -/
  goal : Set F
  /-- The initial task network. -/
  tnI : TaskNetwork I A C

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- The planning problem `(D, P)` obtained from a domain and a problem instance. -/
def Domain.mkProblem (D : Domain F A C I) (Q : Instance F A C I) : Problem F A C I where
  toActionModel := D.toActionModel
  methods := D.methods
  init := Q.init
  goal := Q.goal
  tnI := Q.tnI

open scoped Classical in

/-- The number of ordering constraints of a task network. -/
noncomputable def TaskNetwork.ordSize (tn : TaskNetwork I A C) : ℕ :=
  ((tn.T ×ˢ tn.T).filter (fun p => tn.ord p.1 p.2)).card

/-- The size of a task network: one unit per task id plus one unit per ordering constraint. -/
noncomputable def TaskNetwork.size (tn : TaskNetwork I A C) : ℕ := tn.T.card + tn.ordSize

/-- The size of a decomposition method: one unit for the decomposed task name plus the size of
its subtask network. -/
noncomputable def Method.size (m : Method I A C) : ℕ := 1 + m.subtasks.size

/-- The size of an action in an action model: one unit for its name plus one unit per fact
occurring in its precondition, add or delete list. -/
noncomputable def ActionModel.actionSize (δ : ActionModel F A) (a : A) : ℕ :=
  1 + (δ.prec a).ncard + (δ.add a).ncard + (δ.del a).ncard

/-- The size of a domain: the size of the signature (`|V| + |C|`) plus the sizes of all actions
and of all methods. -/
noncomputable def Domain.size (D : Domain F A C I) : ℕ :=
  Nat.card F + Nat.card C + (∑ᶠ a : A, D.actionSize a) + (∑ᶠ m ∈ D.methods, m.size)

/-- The size of a problem instance: the sizes of the initial state, the goal description and
the initial task network. -/
noncomputable def Instance.size (Q : Instance F A C I) : ℕ :=
  Q.init.ncard + Q.goal.ncard + Q.tnI.size

end HTN

/-! ## Descriptions -/

namespace HTN

namespace Syn

/-- A **description of a task network**: the list of its task identifiers, the list of its
ordering pairs, and the list of its labels (`(i, true, n)` labels `i` with the compound task
name `n`, `(i, false, n)` labels it with the action `n`). -/
abbrev TnDesc : Type := List ℕ × List (ℕ × ℕ) × List (ℕ × Bool × ℕ)

namespace TnDesc

/-- The task identifiers of a described task network. -/
def ids (t : TnDesc) : List ℕ := t.1

/-- The ordering pairs of a described task network. -/
def ordList (t : TnDesc) : List (ℕ × ℕ) := t.2.1

/-- The labels of a described task network. -/
def lbl (t : TnDesc) : List (ℕ × Bool × ℕ) := t.2.2

/-- The label of a task identifier: the first entry of the label list for it, defaulting to the
action `0`. -/
def label (t : TnDesc) (i : ℕ) : ℕ ⊕ ℕ :=
  match t.lbl.lookup i with
  | some (true, n) => Sum.inr n
  | some (false, n) => Sum.inl n
  | none => Sum.inl 0

/-- The relation the description lists explicitly. -/
def listRel (t : TnDesc) (a b : ℕ) : Prop := (a, b) ∈ t.ordList

/-- The transitive closure of the listed relation. -/
def preOrd (t : TnDesc) (a b : ℕ) : Prop := Relation.TransGen t.listRel a b

/-- **The described ordering**: the strict part of the transitive closure of the listed pairs,
restricted to the listed identifiers.  This is a strict partial order for *every* description
(`toTaskNetwork_wf`). -/
def ordOf (t : TnDesc) (a b : ℕ) : Prop :=
  a ∈ t.ids ∧ b ∈ t.ids ∧ t.preOrd a b ∧ ¬ t.preOrd b a

/-- The described task network. -/
def toTaskNetwork (t : TnDesc) : TaskNetwork ℕ ℕ ℕ where
  T := t.ids.toFinset
  ord := t.ordOf
  α := t.label

/-- The **syntactic size** of a described task network: one symbol per identifier, per ordering
pair and per label. -/
def size (t : TnDesc) : ℕ := t.ids.length + t.ordList.length + t.lbl.length

end TnDesc

/-- A **description of a decomposition method**: the compound task name it decomposes and the
description of its subtask network. -/
abbrev MethodDesc : Type := ℕ × TnDesc

namespace MethodDesc

/-- The described method. -/
def toMethod (m : MethodDesc) : Method ℕ ℕ ℕ where
  abstractTask := m.1
  subtasks := m.2.toTaskNetwork

/-- The syntactic size of a described method: one symbol for the decomposed name plus the size
of its subtask network. -/
def size (m : MethodDesc) : ℕ := 1 + m.2.size

end MethodDesc

/-- A **description of an action**: its name, precondition, add and delete list. -/
abbrev ActionDesc : Type := ℕ × List ℕ × List ℕ × List ℕ

namespace ActionDesc

/-- The syntactic size of a described action. -/
def size (a : ActionDesc) : ℕ := 1 + a.2.1.length + a.2.2.1.length + a.2.2.2.length

end ActionDesc

/-- A **description of a domain**: a list of actions and a list of methods. -/
abbrev DomDesc : Type := List ActionDesc × List MethodDesc

namespace DomDesc

/-- The action list of a domain description. -/
def actions (d : DomDesc) : List ActionDesc := d.1

/-- The method list of a domain description. -/
def methods (d : DomDesc) : List MethodDesc := d.2

/-- The precondition of an action, as described (empty for an unmentioned action). -/
def prec (d : DomDesc) (a : ℕ) : Set ℕ :=
  {f | f ∈ ((d.actions.lookup a).elim [] fun x => x.1)}

/-- The add list of an action, as described. -/
def add (d : DomDesc) (a : ℕ) : Set ℕ :=
  {f | f ∈ ((d.actions.lookup a).elim [] fun x => x.2.1)}

/-- The delete list of an action, as described. -/
def del (d : DomDesc) (a : ℕ) : Set ℕ :=
  {f | f ∈ ((d.actions.lookup a).elim [] fun x => x.2.2)}

/-- The described domain. -/
def toDomain (d : DomDesc) : Domain ℕ ℕ ℕ ℕ where
  prec := d.prec
  add := d.add
  del := d.del
  methods := {m | ∃ e ∈ d.methods, e.toMethod = m}

/-- The **syntactic size** of a domain description: the sizes of its actions and methods. -/
def size (d : DomDesc) : ℕ :=
  (d.actions.map ActionDesc.size).sum + (d.methods.map MethodDesc.size).sum

end DomDesc

/-- A **description of a problem instance**: the initial state, the goal, and the initial task
network. -/
abbrev InstDesc : Type := List ℕ × List ℕ × TnDesc

namespace InstDesc

/-- The initial state of an instance description. -/
def initList (q : InstDesc) : List ℕ := q.1

/-- The goal of an instance description. -/
def goalList (q : InstDesc) : List ℕ := q.2.1

/-- The initial task network of an instance description. -/
def tnI (q : InstDesc) : TnDesc := q.2.2

/-- The described problem instance. -/
def toInstance (q : InstDesc) : Instance ℕ ℕ ℕ ℕ where
  init := {f | f ∈ q.initList}
  goal := {f | f ∈ q.goalList}
  tnI := q.tnI.toTaskNetwork

/-- The **syntactic size** of an instance description. -/
def size (q : InstDesc) : ℕ := q.initList.length + q.goalList.length + q.tnI.size

end InstDesc

/-- The planning problem described by a pair of a domain and an instance description. -/
def problem (d : DomDesc) (q : InstDesc) : Problem ℕ ℕ ℕ ℕ :=
  d.toDomain.mkProblem q.toInstance

/-- **Solvability of a described problem** — the predicate the compilability table is about. -/
def Solvable (d : DomDesc) (q : InstDesc) : Prop := (problem d q).Solvable

end Syn

end HTN

/-! ## Serialisation of descriptions -/

namespace HTN

namespace Syn

open PTime

/-- A bit string, written self-delimitingly: each bit `b` becomes `true, b`, and the string is
terminated by `false`. -/
def bstr (x : List Bool) : List Bool := x.foldr (fun b acc => true :: b :: acc) [false]

/-- A list of bit strings, written self-delimitingly: each entry is preceded by `true` and
written with `bstr`, and the list is terminated by `false`. -/
def blist (l : List (List Bool)) : List Bool :=
  l.foldr (fun x acc => true :: (bstr x ++ acc)) [false]

/-- A number, serialised: the self-delimiting form of its binary digits. -/
def serNat (n : ℕ) : List Bool := bstr (bitsOfNat n)

/-- A list of numbers, serialised. -/
def serNatList (l : List ℕ) : List Bool := blist (l.map bitsOfNat)

/-- A pair of numbers, serialised. -/
def serPair (p : ℕ × ℕ) : List Bool := serNat p.1 ++ serNat p.2

/-- A list of pairs of numbers, serialised. -/
def serPairList (l : List (ℕ × ℕ)) : List Bool := blist (l.map serPair)

/-- A label — a task identifier, a Boolean and a name — serialised. -/
def serLbl (p : ℕ × Bool × ℕ) : List Bool := serNat p.1 ++ p.2.1 :: serNat p.2.2

/-- A list of labels, serialised. -/
def serLblList (l : List (ℕ × Bool × ℕ)) : List Bool := blist (l.map serLbl)

/-- A described task network, serialised: its identifiers, its ordering pairs and its labels. -/
def tnSer (t : TnDesc) : List Bool :=
  serNatList t.ids ++ serPairList t.ordList ++ serLblList t.lbl

/-- **A problem-instance description, serialised**: its initial state, its goal and its initial
task network, each self-delimiting, concatenated. -/
def instSer (q : InstDesc) : List Bool :=
  serNatList q.initList ++ serNatList q.goalList ++ tnSer q.tnI

end Syn

end HTN
