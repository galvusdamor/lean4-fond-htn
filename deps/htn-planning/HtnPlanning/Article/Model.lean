import HtnPlanning.Core.TaskNetwork
import HtnPlanning.Core.Decomposition
/-!
# The planning model of Bercher et al. (Section 2)

**Definitions only.**  The HTN and TIHTN planning model of

  P. Bercher, G. Behnke, D. Höller, T. Geier, R. Alford,
  *Propositional Hierarchical Task Network Planning: Problem Classes and Complexity Results*,

as stated there.  It differs from the model `HTN.Problem` of `HtnPlanning/Basic.lean` (which
follows Höller et al., JAIR 2020) in three respects:

* actions have **negative preconditions** and the goal has a **negative part**
  (`HTN.Article.Action`, `HTN.Article.Problem.goalNeg`);
* a task network is executable only if **every** linearisation is executable
  (`HTN.Article.Problem.ExecutableIn`, Def. 2.6), and solutions may be obtained by additionally
  **inserting ordering constraints** (`HTN.Article.OIStep`, Def. 2.5);
* the **TIHTN** solution criterion additionally allows the insertion of primitive tasks
  (`HTN.Article.TIStep`).

Task networks, methods and decomposition (Defs. 2.1, 2.4) are those of `HtnPlanning/Basic.lean`:
`HTN.TaskNetwork`, `HTN.Method`, `HTN.DecompStep`, `HTN.DecomposesTo`.

| article | here |
| --- | --- |
| actions `(prec⁺, prec⁻, eff⁺, eff⁻)`, γ | `HTN.Article.Action`, `Action.Applicable`, `Action.apply` |
| Def. 2.2 (domain `(V, N_C, N_P, δ, M)`) | `HTN.Article.Domain` |
| Def. 2.3 (problem `(D, s_I, tn_I, g)`) | `HTN.Article.Problem` |
| Def. 2.5 (ordering insertion `→_OI`) | `HTN.Article.OIStep` |
| `→*_D` | `HTN.Article.Problem.DecompOI` |
| Def. 2.6 (executable task network) | `HTN.Article.Problem.ExecutableIn`, `Problem.Generates` |
| Def. 2.7 (solutions, `Sol(P)`) | `HTN.Article.Problem.Sol` |
| TIHTN solutions | `HTN.Article.Problem.SolTI` |

**Modelling decisions.**

* The state variables `V`, the task names `N_C`, `N_P` and the task ids are types `F`, `C`, `A`,
  `I`; finiteness is imposed by the finite descriptions, not here.  The primitive task names are
  all of `A`, and `δ : A → Action F` is the task name mapping (it need not be injective).
* γ is defined iff `prec⁺ ⊆ s` and `prec⁻ ∩ s = ∅`.  (The article writes `s ⊆ prec⁺`, a typo.)
* **Def. 2.5.** Inserting `(t, t')` with `t' ≺* t` or `t = t'` does not yield a strict partial
  order, although the article claims it always does; `OIStep` therefore requires the result to be
  well-formed.
* **TIHTN.** The draft refers to a missing definition.  Following Geier and Bercher (IJCAI 2011),
  a TIHTN solution is obtained from `tn_I` by decomposition, then insertion of primitive tasks,
  then insertion of ordering constraints.  (Inserted tasks are primitive and ordering insertion
  only orders primitive tasks, so the order of the three kinds of steps is immaterial.)
-/

namespace HTN

namespace Article

universe u v w x

/-! ### Actions and states -/

/-- An action `(prec⁺, prec⁻, eff⁺, eff⁻)` over the state variables `F`. -/
structure Action (F : Type u) where
  /-- The positive precondition `prec⁺`. -/
  pre : Set F
  /-- The negative precondition `prec⁻`. -/
  preNeg : Set F
  /-- The positive effects `eff⁺`. -/
  add : Set F
  /-- The negative effects `eff⁻`. -/
  del : Set F

namespace Action

variable {F : Type u}

/-- `γ(s, a)` is defined iff `prec⁺ ⊆ s` and `prec⁻ ∩ s = ∅`. -/
def Applicable (a : Action F) (s : Set F) : Prop := a.pre ⊆ s ∧ Disjoint a.preNeg s

/-- `γ(s, a) = (s \ eff⁻) ∪ eff⁺`. -/
def apply (a : Action F) (s : Set F) : Set F := (s \ a.del) ∪ a.add

end Action

/-! ### Domains and problems -/

/-- **Definition 2.2.** A planning domain `(V, N_C, N_P, δ, M)`: the task name mapping `δ` and
the methods `M`. -/
structure Domain (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The task name mapping `δ : N_P → A`. -/
  δ : A → Action F
  /-- The decomposition methods. -/
  methods : Set (Method I A C)

/-- **Definition 2.3.** A planning problem `(D, s_I, tn_I, g)` with `g = (g⁺, g⁻)`. -/
structure Problem (F : Type u) (A : Type v) (C : Type w) (I : Type x)
    extends Domain F A C I where
  /-- The initial state `s_I`. -/
  init : Set F
  /-- The initial task network `tn_I`. -/
  tnI : TaskNetwork I A C
  /-- The positive goal `g⁺`. -/
  goalPos : Set F
  /-- The negative goal `g⁻`. -/
  goalNeg : Set F

/-! ### Ordering and task insertion -/

section Insertion

variable {I : Type x} {A : Type v} {C : Type w}

/-- The task network `tn` with the ordering constraint `(t, t')` added and the order closed
transitively: `≺₂ = (≺₁ ∪ {(t, t')})⁺`. -/
def ordInsert (tn : TaskNetwork I A C) (t t' : I) : TaskNetwork I A C where
  T := tn.T
  ord := Relation.TransGen fun a b => tn.ord a b ∨ (a = t ∧ b = t')
  α := tn.α

/-- **Definition 2.5 (ordering insertion).** `tn₁ →_OI tn₂`: an ordering constraint between two
primitive tasks of `tn₁` is inserted.  The result is required to be a strict partial order (see
the module docstring). -/
def OIStep (tn₁ tn₂ : TaskNetwork I A C) : Prop :=
  ∃ t t', t ∈ tn₁.T ∧ t' ∈ tn₁.T ∧ tn₁.IsPrimitiveId t ∧ tn₁.IsPrimitiveId t' ∧
    tn₂ = ordInsert tn₁ t t' ∧ tn₂.WF

/-- `tn₁ →*_OI tn₂`. -/
def OIReach (tn₁ tn₂ : TaskNetwork I A C) : Prop := Relation.ReflTransGen OIStep tn₁ tn₂

/-- The task network `tn` with a new task id `t` labelled with the primitive task name `a`. -/
def taskInsert [DecidableEq I] (tn : TaskNetwork I A C) (t : I) (a : A) : TaskNetwork I A C where
  T := insert t tn.T
  ord := tn.ord
  α := Function.update tn.α t (Sum.inl a)

/-- **Task insertion.** `tn₁ →_TI tn₂`: a primitive task with a fresh id is inserted. -/
def TIStep [DecidableEq I] (tn₁ tn₂ : TaskNetwork I A C) : Prop :=
  ∃ t a, t ∉ tn₁.T ∧ tn₂ = taskInsert tn₁ t a

/-- `tn₁ →*_TI tn₂`. -/
def TIReach [DecidableEq I] (tn₁ tn₂ : TaskNetwork I A C) : Prop :=
  Relation.ReflTransGen TIStep tn₁ tn₂

end Insertion

/-! ### Executability and solutions -/

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

section Exec

variable (P : Problem F A C I)

/-- Executing a sequence of primitive task names from a state: `Run as s s'` iff there are
states `s = s₀, …, sₙ = s'` with `γ(sᵢ, δ(pᵢ₊₁)) = sᵢ₊₁`. -/
def Run : List A → Set F → Set F → Prop
  | [], s, s' => s' = s
  | a :: as, s, s' => (P.δ a).Applicable s ∧ Run as ((P.δ a).apply s) s'

/-- `s` satisfies the goal condition: `g⁺ ⊆ s` and `g⁻ ∩ s = ∅`. -/
def GoalState (s : Set F) : Prop := P.goalPos ⊆ s ∧ Disjoint P.goalNeg s

/-- `tn` generates `s'` from `s`: some linearisation of `tn` is executable from `s` and ends in
`s'` (Def. 2.6, "a state that can be generated by `tn` in `s`"). -/
def Generates (tn : TaskNetwork I A C) (s s' : Set F) : Prop :=
  ∃ (l : List I) (as : List A), tn.IsLinearization l ∧ tn.IsActionSeq l as ∧ P.Run as s s'

/-- **Definition 2.6 (executable task network).** `tn` is primitive and *every* linearisation
of it is executable in `s`. -/
def ExecutableIn (tn : TaskNetwork I A C) (s : Set F) : Prop :=
  tn.IsPrimitive ∧ ∀ (l : List I) (as : List A), tn.IsLinearization l → tn.IsActionSeq l as →
    ∃ s', P.Run as s s'

end Exec

section Sol

variable [DecidableEq I] (P : Problem F A C I)

/-- `tn₁ →*_D tn₂`: decomposition followed by ordering insertion. -/
def DecompOI (tn₁ tn₂ : TaskNetwork I A C) : Prop :=
  ∃ tn, DecomposesTo P.methods tn₁ tn ∧ OIReach tn tn₂

/-- **Definition 2.7 (solutions).** `tn_S` is executable in `s_I`, every state it generates
satisfies the goal, and `tn_I →*_D tn_S`. -/
def IsSol (tnS : TaskNetwork I A C) : Prop :=
  P.ExecutableIn tnS P.init ∧ (∀ s, P.Generates tnS P.init s → P.GoalState s) ∧
    P.DecompOI P.tnI tnS

/-- `Sol(P)`, the set of HTN solutions. -/
def Sol : Set (TaskNetwork I A C) := {tn | P.IsSol tn}

/-- `tn₁ →*_X tn₂` with `X = {TD, TI, OI}`: decomposition, then task insertion, then ordering
insertion. -/
def DecompTIOI (tn₁ tn₂ : TaskNetwork I A C) : Prop :=
  ∃ tn tn', DecomposesTo P.methods tn₁ tn ∧ TIReach tn tn' ∧ OIReach tn' tn₂

/-- **TIHTN solutions**: as `IsSol`, but primitive tasks may also be inserted. -/
def IsSolTI (tnS : TaskNetwork I A C) : Prop :=
  P.ExecutableIn tnS P.init ∧ (∀ s, P.Generates tnS P.init s → P.GoalState s) ∧
    P.DecompTIOI P.tnI tnS

/-- The set of TIHTN solutions. -/
def SolTI : Set (TaskNetwork I A C) := {tn | P.IsSolTI tn}

/-- Plan existence in the HTN setting: `Sol(P) ≠ ∅`. -/
def Solvable : Prop := P.Sol.Nonempty

/-- Plan existence in the TIHTN setting. -/
def SolvableTI : Prop := P.SolTI.Nonempty

end Sol

/-- Well-formedness: the initial task network and all method networks are strict partial
orders on their ids (implicit in the article's Def. 2.1). -/
structure WF (P : Problem F A C I) : Prop where
  /-- The initial task network is well formed. -/
  tnI : P.tnI.WF
  /-- All method networks are well formed. -/
  methods : ∀ m ∈ P.methods, m.subtasks.WF

end Problem

end Article

end HTN
