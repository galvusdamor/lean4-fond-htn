import HtnPlanning.Basic
import HtnPlanning.Classes.Basic
import HtnPlanning.Progression.Progression
import HtnPlanning.Article.Model
/-!
# FOND HTN planning: actions, domains and problems

**Definitions only.**  The common model underlying

* D. Chen, P. Bercher, *Fully Observable Nondeterministic HTN Planning – Formalisation and
  Complexity Results*, ICAPS 2021 (**[CB21]**, "fixed methods", `FONDFM`),
* D. Z. Chen, P. Bercher, *Flexible FOND HTN Planning: A Complexity Analysis*, ICAPS 2022
  (**[CB22]**, "method-based policies", `FONDMP`),
* P. M. Dekker, G. Behnke, *Hardness of Chosen Length Planning Games and Regular Fixed Methods
  FOND HTN Planning*, ICAPS 2025 (**[DB25]**).

Task networks, methods, isomorphism and decomposition are those of the deterministic library
`HtnPlanning` (`HTN.TaskNetwork`, `HTN.Method`, `HTN.TaskNetwork.Iso`, `HTN.DecompStep`,
`HTN.DecomposesTo`).  Only the actions are new: a nondeterministic action has one precondition
and a *set* of alternative effects.

| paper | here |
| --- | --- |
| action `a = (pre(a), eff(a))`, `eff(a) = {(addᵢ, delᵢ)}` [CB21 Def. 2.2] | `FOND.Action` |
| `δ(pr) = (Π⁺, Π⁻, E)` with negative preconditions [DB25] | `FOND.Action` (`preNeg`) |
| `τ(a, s)` | `FOND.Action.Applicable` |
| `γ(a, s)` / `Γ(S, pr)` | `FOND.Action.outcomes` |
| domain `⟨F, N_P, N_C, δ, M⟩` [CB21 Def. 2.2, CB22 Def. 2] | `FOND.Domain` |
| problem `⟨D, s_I, tn_I⟩` [CB21 Def. 2.3, CB22 Def. 4] | `FOND.Problem` |
| primitive / regular / acyclic / tail-recursive / totally ordered problems | `FOND.Problem.IsPrimitive`, … |

**Modelling decisions.**

* The facts `F`, primitive task names `A`, compound task names `C` and task ids `I` are types;
  finiteness is imposed by finite descriptions later, not here.
* Actions carry **negative preconditions** (as in [DB25]); the actions of [CB21, CB22] are the
  special case `preNeg = ∅`.
* `γ(a, s)` is the *set* of successor states; it is only meaningful when `a` is applicable in `s`
  (applicability is checked separately, exactly as in the papers, where `γ` is undefined
  otherwise).
* The papers implicitly assume `1 ≤ |eff(a)| < ∞`.  This is the well-formedness condition
  `FOND.Action.WF`; it is not built into the type.
* FOND HTN problems have **no state goal** — the only objective is to execute the hierarchy.
* The structural problem classes only depend on the initial task network and the methods; they are
  inherited from the deterministic library through the *skeleton* `FOND.Problem.skeleton`.
-/

namespace FOND

open HTN

universe u v w x

/-! ## Nondeterministic actions -/

/-- A nondeterministic action `(Π⁺, Π⁻, E)`: a positive precondition, a negative precondition
and a set `E` of alternative effects, each a pair `(add, del)`. -/
structure Action (F : Type u) where
  /-- The positive precondition `pre(a)` (`Π⁺`). -/
  pre : Set F
  /-- The negative precondition `Π⁻` (empty in [CB21, CB22]). -/
  preNeg : Set F
  /-- The alternative effects `eff(a) = {(add₁, del₁), …, (addₙ, delₙ)}`. -/
  effs : Set (Set F × Set F)

namespace Action

variable {F : Type u}

theorem ext' {a b : Action F} (h1 : a.pre = b.pre) (h2 : a.preNeg = b.preNeg)
    (h3 : a.effs = b.effs) : a = b := by
  cases a; cases b; simp_all

/-- `τ(a, s) = ⊤` iff `pre(a) ⊆ s` and `Π⁻ ∩ s = ∅`. -/
def Applicable (a : Action F) (s : Set F) : Prop := a.pre ⊆ s ∧ Disjoint a.preNeg s

/-- The result `(s \ del) ∪ add` of one effect `(add, del)`. -/
def applyEff (e : Set F × Set F) (s : Set F) : Set F := (s \ e.2) ∪ e.1

/-- `γ(a, s) = {(s \ delᵢ) ∪ addᵢ | 1 ≤ i ≤ |eff(a)|}`, the possible successor states
(meaningful when `a` is applicable in `s`). -/
def outcomes (a : Action F) (s : Set F) : Set (Set F) :=
  {s' | ∃ e ∈ a.effs, s' = applyEff e s}

/-- Well-formedness: an action has finitely many, and at least one, alternative effects. -/
def WF (a : Action F) : Prop := a.effs.Nonempty ∧ a.effs.Finite

/-- An action is deterministic iff it has exactly one effect. -/
def IsDeterministic (a : Action F) : Prop := ∃ e, a.effs = {e}

/-- The deterministic action `(pre, pre⁻, add, del)` of the deterministic model of Bercher et
al. (`HTN.Article.Action`) as a FOND action with a single effect. -/
def ofDet (a : HTN.Article.Action F) : Action F where
  pre := a.pre
  preNeg := a.preNeg
  effs := {(a.add, a.del)}

lemma mem_outcomes {a : Action F} {s s' : Set F} :
    s' ∈ a.outcomes s ↔ ∃ e ∈ a.effs, s' = applyEff e s := Iff.rfl

lemma outcomes_nonempty {a : Action F} (h : a.WF) (s : Set F) : (a.outcomes s).Nonempty := by
  obtain ⟨e, he⟩ := h.1
  exact ⟨applyEff e s, e, he, rfl⟩

@[simp] lemma ofDet_outcomes (a : HTN.Article.Action F) (s : Set F) :
    (ofDet a).outcomes s = {a.apply s} := by
  ext s'
  simp [outcomes, ofDet, applyEff, HTN.Article.Action.apply]

@[simp] lemma ofDet_applicable (a : HTN.Article.Action F) (s : Set F) :
    (ofDet a).Applicable s ↔ a.Applicable s := Iff.rfl

lemma ofDet_wf (a : HTN.Article.Action F) : (ofDet a).WF :=
  ⟨⟨_, rfl⟩, Set.finite_singleton _⟩

end Action

/-! ## Domains and problems -/

/-- A FOND HTN domain `⟨F, N_P, N_C, δ, M⟩` [CB21 Def. 2.2, CB22 Def. 2]: the action mapping
`δ : N_P → A` and the set of decomposition methods. -/
structure Domain (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The action mapping `δ`. -/
  δ : A → Action F
  /-- The decomposition methods `M`. -/
  methods : Set (Method I A C)

/-- A FOND HTN problem `⟨D, s_I, tn_I⟩` [CB21 Def. 2.3, CB22 Def. 4, DB25]. -/
structure Problem (F : Type u) (A : Type v) (C : Type w) (I : Type x)
    extends Domain F A C I where
  /-- The initial state `s_I`. -/
  init : Set F
  /-- The initial task network `tn_I`. -/
  tnI : TaskNetwork I A C

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

section

variable (P : Problem F A C I)

/-- Well-formedness: all task networks of the problem carry strict partial orders and all
actions have finitely many and at least one effect. -/
structure WF : Prop where
  /-- The initial task network is well formed. -/
  tnI : P.tnI.WF
  /-- The subtask networks of all methods are well formed. -/
  methods : ∀ m ∈ P.methods, m.subtasks.WF
  /-- Every action has at least one and finitely many effects. -/
  actions : ∀ a : A, (P.δ a).WF

/-- The problem is deterministic (a FOD HTN problem) iff every action has exactly one effect. -/
def IsDeterministic : Prop := ∀ a : A, (P.δ a).IsDeterministic

/-- The **skeleton**: the deterministic HTN problem with the same methods, initial state and
initial task network and trivial actions.  The structural problem classes only depend on the
initial task network and the methods, so they are inherited through the skeleton. -/
def skeleton : HTN.Problem F A C I where
  prec := fun _ => ∅
  add := fun _ => ∅
  del := fun _ => ∅
  methods := P.methods
  init := P.init
  goal := ∅
  tnI := P.tnI

/-! ### Problem classes [CB21 §3, CB22 Defs. 8–9, DB25 "Fragments"] -/

/-- **Primitive** problems [CB21 Def. 3.2]: the initial task network is primitive. -/
def IsPrimitive : Prop := P.tnI.IsPrimitive

/-- **Totally ordered** problems [CB21 Def. 2.14]: the initial task network and all (reachable)
method networks are totally ordered. -/
def IsTotallyOrdered : Prop := P.skeleton.IsTO

/-- **Regular** problems [CB21 Def. 3.3]: the initial task network and every (reachable) method
network contain at most one compound task, which is then ordered after all other tasks. -/
def IsRegular : Prop := P.skeleton.IsRegular

/-- **Acyclic** problems [CB21 Def. 3.5]: no compound task can reach itself by decomposition. -/
def IsAcyclic : Prop := P.skeleton.IsAcyclic

/-- **Tail-recursive** problems [CB21 Def. 3.6]. -/
def IsTailRecursive : Prop := P.skeleton.IsTailRecursive

end

section Decomp

variable [DecidableEq I] (P : Problem F A C I)

/-- `tn →* tn'` with the methods of `P`. -/
def DecomposesTo (tn tn' : TaskNetwork I A C) : Prop := HTN.DecomposesTo P.methods tn tn'

/-- **Achievable primitive task networks** [CB21 Def. 2.5]: primitive task networks obtained
from `tn_I` by finitely many decompositions. -/
def AchievablePrimitive (tn : TaskNetwork I A C) : Prop :=
  P.DecomposesTo P.tnI tn ∧ tn.IsPrimitive

end Decomp

/-- The FOND problem induced by a deterministic problem of Bercher et al.
(`HTN.Article.Problem`, ignoring its state goal): every action gets a single effect. -/
def ofDet (Q : HTN.Article.Problem F A C I) : Problem F A C I where
  δ := fun a => Action.ofDet (Q.δ a)
  methods := Q.methods
  init := Q.init
  tnI := Q.tnI

lemma ofDet_isDeterministic (Q : HTN.Article.Problem F A C I) : (ofDet Q).IsDeterministic :=
  fun _ => ⟨_, rfl⟩

end Problem

end FOND
