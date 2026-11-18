import Mathlib
import ComplexityTheory.TM.Basic
import ComplexityTheory.Complexity.Basic
import HtnPlanning.Basic
/-!
# The subclasses of HTN planning

**Definitions only.**

* The structural restrictions of the reference paper as predicates on problems: totally ordered
  (`HTN.Problem.IsTO`), tail-recursive, regular, acyclic, no-op, `STRIPS`-like; the eleven
  classes `HTN.Classes.*` as sets of problems and as families over all signatures
  (`HTN.Table.Cls.*`), finiteness `HTN.Problem.IsFinite` and the finite well-formed part
  `HTN.Table.Family.fwf` of a family.
* The same restrictions as conditions on descriptions (`HTN.Syn.DomDesc.MethodsTO`,
  `HTN.Syn.InstDesc.IsTO`, `HTN.Syn.InstDesc.IsRooted`, …), from which the classes of
  descriptions of `HtnPlanning/SynClasses/Basic.lean` are built.
-/

/-! ## Structural restrictions and the eleven classes -/

namespace HTN

universe u v w x

namespace TaskNetwork

variable {I : Type x} {A : Type v} {C : Type w}

/-- A task network is *totally ordered* iff any two distinct task ids are ordered. -/
def IsTotallyOrdered (tn : TaskNetwork I A C) : Prop :=
  ∀ t ∈ tn.T, ∀ t' ∈ tn.T, t ≠ t' → tn.ord t t' ∨ tn.ord t' t

/-- `t` is a *last* task id of `tn` iff every other task id of `tn` is ordered before it. -/
def IsLastId (tn : TaskNetwork I A C) (t : I) : Prop :=
  t ∈ tn.T ∧ ∀ t' ∈ tn.T, t' ≠ t → tn.ord t' t

/-- **Definition 3.3 (regular task network).** A task network is regular iff it contains at
most one compound task, which then has to be ordered after all other tasks. -/
def IsRegular (tn : TaskNetwork I A C) : Prop :=
  (∀ t ∈ tn.T, ∀ t' ∈ tn.T, tn.IsAbstractId t → tn.IsAbstractId t' → t = t') ∧
    (∀ t ∈ tn.T, tn.IsAbstractId t → ∀ t' ∈ tn.T, t' ≠ t → tn.ord t' t)

end TaskNetwork

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- `TO-tn_I`: the initial task network is totally ordered. -/
def IsTO_tnI (P : Problem F A C I) : Prop := P.tnI.IsTotallyOrdered

/-- `TO-M`: all methods reachable from the initial task network are totally ordered. -/
def IsTO_M (P : Problem F A C I) : Prop :=
  ∀ m : Method I A C, P.ReachableMethod m → m.subtasks.IsTotallyOrdered

/-- `TO = TO-tn_I ∩ TO-M`. -/
def IsTO (P : Problem F A C I) : Prop := P.IsTO_tnI ∧ P.IsTO_M

/-- `REG-M`: all methods reachable from the initial task network are regular.  This is the
*generalised* Definition 3.3 of Bercher et al., which puts no condition on the initial task
network.  It is **not** the class `REG` of this project any more (see `Problem.IsRegular`). -/
def IsRegularM (P : Problem F A C I) : Prop :=
  ∀ m : Method I A C, P.ReachableMethod m → m.subtasks.IsRegular

/-- **`REG` (regular problems, Erol et al.'s definition).**  The initial task network is regular
(at most one compound task, ordered after all other tasks) **and** all methods reachable from it
are regular.  Bercher et al. (Def. 3.3) drop the condition on the initial task network
(`Problem.IsRegularM`); following the user's decision this project uses the original, stronger
definition, under which a solution is the primitive part of the initial network followed by the
yield of a *single* regular chain. -/
def IsRegular (P : Problem F A C I) : Prop :=
  P.tnI.IsRegular ∧ P.IsRegularM

/-- A *stratification* of the compound task names reachable from `tn_I`: a total preorder on
the reachable names. -/
structure IsStratification (P : Problem F A C I) (le : C → C → Prop) : Prop where
  /-- Reflexivity on the reachable names. -/
  refl : ∀ c, P.ReachableName c → le c c
  /-- Transitivity on the reachable names. -/
  trans : ∀ c₁ c₂ c₃, P.ReachableName c₁ → P.ReachableName c₂ → P.ReachableName c₃ →
    le c₁ c₂ → le c₂ c₃ → le c₁ c₃
  /-- Totality on the reachable names. -/
  total : ∀ c₁ c₂, P.ReachableName c₁ → P.ReachableName c₂ → le c₁ c₂ ∨ le c₂ c₁

/-- Antisymmetry on the reachable names; together with `IsStratification` this says that `le`
is a total order, i.e. that every stratum is a singleton. -/
def IsAntisymmOn (P : Problem F A C I) (le : C → C → Prop) : Prop :=
  ∀ c₁ c₂, P.ReachableName c₁ → P.ReachableName c₂ → le c₁ c₂ → le c₂ c₁ → c₁ = c₂

/-- **Definition 3.5 (`≤₀`-stratification).** `le` is a total order on the reachable compound
task names such that every compound task in the subtask network of a reachable method is
*strictly* smaller than the decomposed task. -/
structure IsStrat0 (P : Problem F A C I) (le : C → C → Prop) : Prop where
  /-- `le` is a stratification. -/
  strat : P.IsStratification le
  /-- `le` is a total order (each stratum is a singleton). -/
  antisymm : P.IsAntisymmOn le
  /-- Every compound subtask of a reachable method is strictly smaller than the task that the
  method decomposes. -/
  decreasing : ∀ m : Method I A C, P.ReachableMethod m → ∀ t ∈ m.subtasks.T, ∀ c : C,
    m.subtasks.α t = Sum.inr c → le c m.abstractTask ∧ ¬ le m.abstractTask c

/-- **Definition 3.6 (`ACYC`).** -/
def IsAcyclic (P : Problem F A C I) : Prop := ∃ le : C → C → Prop, P.IsStrat0 le

/-- **Definition 3.9 (`≤_r`-stratification).** A stratification in which a compound *last* task
of a reachable method may stay inside the stratum of the decomposed task, while all other
compound subtasks must be strictly smaller. -/
structure IsStratR (P : Problem F A C I) (le : C → C → Prop) : Prop where
  /-- `le` is a stratification. -/
  strat : P.IsStratification le
  /-- A compound last task does not increase the stratum. -/
  last : ∀ m : Method I A C, P.ReachableMethod m → ∀ t ∈ m.subtasks.T,
    m.subtasks.IsLastId t → ∀ c : C, m.subtasks.α t = Sum.inr c → le c m.abstractTask
  /-- Any compound non-last task strictly decreases the stratum. -/
  nonlast : ∀ m : Method I A C, P.ReachableMethod m → ∀ t ∈ m.subtasks.T,
    ¬ m.subtasks.IsLastId t → ∀ c : C, m.subtasks.α t = Sum.inr c →
      le c m.abstractTask ∧ ¬ le m.abstractTask c

/-- **Definition 3.10 (`TAIL-REC`).** -/
def IsTailRecursive (P : Problem F A C I) : Prop := ∃ le : C → C → Prop, P.IsStratR le

/-- **Definition 3.11 (`UNRES-REC`).** Every planning problem is unrestricted-recursive. -/
def IsUnrestricted (_P : Problem F A C I) : Prop := True

/-- `NOOP`: all actions are no-ops, i.e. have empty precondition, add and delete lists. -/
def IsNoop (P : Problem F A C I) : Prop :=
  ∀ a : A, P.prec a = ∅ ∧ P.add a = ∅ ∧ P.del a = ∅

end Problem

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x)

/-- `HTN`: unrestricted HTN planning problems (Def. 3.11). -/
def HTN : Set (Problem F A C I) := {P | P.IsUnrestricted}

/-- `TO-HTN`: totally ordered HTN planning problems (Def. 3.1). -/
def TO_HTN : Set (Problem F A C I) := {P | P.IsTO}

/-- `HTN-NOOP`: HTN planning problems all of whose actions are no-ops. -/
def HTN_NOOP : Set (Problem F A C I) := {P | P.IsNoop}

/-- `TO-HTN-NOOP`. -/
def TO_HTN_NOOP : Set (Problem F A C I) := TO_HTN F A C I ∩ HTN_NOOP F A C I

/-- `HTN-TR`: tail-recursive HTN planning problems (Def. 3.10). -/
def HTN_TR : Set (Problem F A C I) := {P | P.IsTailRecursive}

/-- `TO-HTN-TR`. -/
def TO_HTN_TR : Set (Problem F A C I) := TO_HTN F A C I ∩ HTN_TR F A C I

/-- `HTN-REG`: regular HTN planning problems (Def. 3.3). -/
def HTN_REG : Set (Problem F A C I) := {P | P.IsRegular}

/-- `TO-HTN-REG`. -/
def TO_HTN_REG : Set (Problem F A C I) := TO_HTN F A C I ∩ HTN_REG F A C I

/-- `TO-HTN-REG-M`: totally ordered problems all of whose reachable methods are regular, with an
*arbitrary* totally ordered initial task network (the paper's generalised notion of regularity,
`Problem.IsRegularM`).  An auxiliary class, not a row of the tables: some constructions produce
such problems, and `TO-HTN-REG ⊆ TO-HTN-REG-M`. -/
def TO_HTN_REGM : Set (Problem F A C I) := TO_HTN F A C I ∩ {P | P.IsRegularM}

/-- `HTN-AC`: acyclic HTN planning problems (Def. 3.6). -/
def HTN_AC : Set (Problem F A C I) := {P | P.IsAcyclic}

/-- `TO-HTN-AC`. -/
def TO_HTN_AC : Set (Problem F A C I) := TO_HTN F A C I ∩ HTN_AC F A C I

end Classes

end HTN

/-! ## `STRIPS` as a class of HTN problems -/

namespace HTN

universe u v w x

namespace TaskNetwork

variable {I : Type x} {A : Type v} {C : Type w} [DecidableEq I]

/-- The subtask network of a method of a STRIPS-like problem: either empty, or one primitive
task followed by the (unique) compound task `c`. -/
def IsStripsStep (tn : TaskNetwork I A C) (c : C) : Prop :=
  tn.T = ∅ ∨ ∃ t₁ t₂ : I, t₁ ≠ t₂ ∧ tn.T = {t₁, t₂} ∧ tn.IsPrimitiveId t₁ ∧
    tn.α t₂ = Sum.inr c ∧ ∀ x y, tn.ord x y ↔ (x = t₁ ∧ y = t₂)

end TaskNetwork

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

/-- A planning problem is *STRIPS-like* iff its initial task network consists of a single
compound task `c` and every reachable method decomposes `c` either into nothing or into a
primitive task followed by `c`. -/
def IsStripsLike (P : Problem F A C I) : Prop := ∃ c : C,
  (∃ t : I, P.tnI.T = {t} ∧ P.tnI.α t = Sum.inr c) ∧
    ∀ m : Method I A C, P.ReachableMethod m →
      m.abstractTask = c ∧ m.subtasks.IsStripsStep c

end Problem

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x) [DecidableEq I]

/-- `STRIPS`: HTN encodings of classical planning problems (Thm. 4.3.1 of Bercher et al.). -/
def STRIPS : Set (Problem F A C I) := {P | P.IsStripsLike}

end Classes

end HTN

/-! ## Families of classes -/

namespace HTN

namespace Table

/-- A *family of problem classes*: one class of planning problems per signature. -/
abbrev Family : Type 1 := ∀ (F A C I : Type) [DecidableEq I], Set (Problem F A C I)

namespace Cls

/-- The row/column `HTN` of the table. -/
def HTN : Family := fun F A C I _ => Classes.HTN F A C I

/-- The row/column `TO-HTN` of the table. -/
def TO_HTN : Family := fun F A C I _ => Classes.TO_HTN F A C I

/-- The row/column `HTN-NOOP` of the table. -/
def HTN_NOOP : Family := fun F A C I _ => Classes.HTN_NOOP F A C I

/-- The row/column `TO-HTN-NOOP` of the table. -/
def TO_HTN_NOOP : Family := fun F A C I _ => Classes.TO_HTN_NOOP F A C I

/-- The row/column `HTN-TR` of the table. -/
def HTN_TR : Family := fun F A C I _ => Classes.HTN_TR F A C I

/-- The row/column `TO-HTN-TR` of the table. -/
def TO_HTN_TR : Family := fun F A C I _ => Classes.TO_HTN_TR F A C I

/-- The row/column `HTN-REG` of the table. -/
def HTN_REG : Family := fun F A C I _ => Classes.HTN_REG F A C I

/-- The row/column `TO-HTN-REG` of the table. -/
def TO_HTN_REG : Family := fun F A C I _ => Classes.TO_HTN_REG F A C I

/-- The auxiliary family `TO-HTN-REG-M` (`HTN.Classes.TO_HTN_REGM`; not a row of the table). -/
def TO_HTN_REGM : Family := fun F A C I _ => Classes.TO_HTN_REGM F A C I

/-- The row/column `HTN-AC` of the table. -/
def HTN_AC : Family := fun F A C I _ => Classes.HTN_AC F A C I

/-- The row/column `TO-HTN-AC` of the table. -/
def TO_HTN_AC : Family := fun F A C I _ => Classes.TO_HTN_AC F A C I

/-- The row/column `STRIPS` of the table. -/
def STRIPS : Family := fun F A C I _ => Classes.STRIPS F A C I

end Cls

end Table

end HTN

/-! ## Conditions on descriptions -/

namespace HTN

namespace Syn

namespace DomDesc

/-- **`TO-M` for descriptions**: every listed method has a totally ordered subtask network. -/
def MethodsTO (d : DomDesc) : Prop := ∀ e ∈ d.methods, e.2.toTaskNetwork.IsTotallyOrdered

/-- **`REG` for descriptions**: every listed method has a regular subtask network. -/
def MethodsReg (d : DomDesc) : Prop := ∀ e ∈ d.methods, e.2.toTaskNetwork.IsRegular

/-- **`NOOP` for descriptions**: every action has empty precondition, add and delete list. -/
def IsNoop (d : DomDesc) : Prop := ∀ a : ℕ, d.prec a = ∅ ∧ d.add a = ∅ ∧ d.del a = ∅

/-- **A rank function witnessing acyclicity**: every compound subtask of a listed method has a
strictly smaller rank than the task the method decomposes. -/
def AcyclicBy (d : DomDesc) (rk : ℕ → ℕ) : Prop :=
  ∀ e ∈ d.methods, ∀ t ∈ e.2.toTaskNetwork.T, ∀ c : ℕ,
    e.2.toTaskNetwork.α t = Sum.inr c → rk c < rk e.1

/-- **`ACYC` for descriptions**. -/
def IsAcyclic (d : DomDesc) : Prop := ∃ rk : ℕ → ℕ, d.AcyclicBy rk

/-- **A rank function witnessing tail recursion**: a compound *last* subtask of a listed method
may keep the rank of the decomposed task, every other compound subtask must decrease it. -/
def TailRecBy (d : DomDesc) (rk : ℕ → ℕ) : Prop :=
  ∀ e ∈ d.methods, ∀ t ∈ e.2.toTaskNetwork.T, ∀ c : ℕ,
    e.2.toTaskNetwork.α t = Sum.inr c →
      (e.2.toTaskNetwork.IsLastId t → rk c ≤ rk e.1) ∧
        (¬ e.2.toTaskNetwork.IsLastId t → rk c < rk e.1)

/-- **`TAIL-REC` for descriptions**. -/
def IsTailRec (d : DomDesc) : Prop := ∃ rk : ℕ → ℕ, d.TailRecBy rk

/-- **`STRIPS` for descriptions**: every listed method decomposes the compound task `0` either
into nothing or into one action followed by `0`. -/
def IsStrips (d : DomDesc) : Prop :=
  ∀ e ∈ d.methods, e.1 = 0 ∧ e.2.toTaskNetwork.IsStripsStep 0

end DomDesc

namespace InstDesc

/-- **`TO-tn_I` for descriptions**: the initial task network is totally ordered. -/
def IsTO (q : InstDesc) : Prop := q.tnI.toTaskNetwork.IsTotallyOrdered

/-- **`REG` for instance descriptions**: the initial task network is regular (a partially
ordered set of primitive tasks followed by at most one compound task). -/
def IsRegular (q : InstDesc) : Prop := q.tnI.toTaskNetwork.IsRegular

/-- **`STRIPS` for instance descriptions**: the initial task network is the single compound
task `0`. -/
def IsStrips (q : InstDesc) : Prop :=
  ∃ t : ℕ, q.tnI.toTaskNetwork.T = {t} ∧ q.tnI.toTaskNetwork.α t = Sum.inr 0

end InstDesc

end Syn

end HTN

/-! ## Rooted instance descriptions -/

namespace HTN

namespace Syn


namespace InstDesc

/-- **A rooted instance description**: the initial task network is a single compound task.  This
is the initial task network of the class `HTN.Classes.TO_HTN_REG_I`. -/
def IsRooted (q : InstDesc) : Prop :=
  ∃ t c : ℕ, q.tnI.toTaskNetwork.T = {t} ∧ q.tnI.toTaskNetwork.α t = Sum.inr c

end InstDesc

end Syn

end HTN

/-! ## Finite problems -/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- **A finite HTN planning problem**: its domain is finite.  (The initial state and the goal
description are then finite as subsets of a finite vocabulary, and the initial task network
carries a `Finset` of task identifiers by construction.) -/
structure Problem.IsFinite (P : Problem F A C I) : Prop where
  /-- The fact vocabulary is finite. -/
  facts : Finite F
  /-- There are finitely many primitive task names. -/
  primitives : Finite A
  /-- There are finitely many abstract task names. -/
  abstracts : Finite C
  /-- There are finitely many decomposition methods. -/
  methods : P.methods.Finite

namespace Table

/-- The finite, **well-formed** part of a family of problem classes: the problems of the class
that are finite HTN planning problems whose initial task network and method bodies are
well-formed task networks (`HTN.Problem.WF`: the ordering is a strict partial order that only
relates tasks of the network).  In the planning literature every task network is well formed by
definition; the structure `HTN.TaskNetwork` does not build this in, and an ill-formed initial
task network can carry ordering constraints between identifiers *outside* the network, which
decomposition inherits (see `HTN.decomposeWith`), so that a compilation could hide information
in them. -/
def Family.fwf (𝒟 : Family) : Family :=
  fun F A C I _ => {P ∈ 𝒟 F A C I | P.IsFinite ∧ P.WF}

end Table

end HTN
