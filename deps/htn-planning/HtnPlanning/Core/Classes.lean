import HtnPlanning.Core.Reachability
import HtnPlanning.Classes.Basic
/-!
# Structural and syntactical restrictions on HTN problems (Section 3)

This file formalises the sub-classes of HTN planning problems of Section 3 of

  P. Bercher, G. Behnke, D. Höller, T. Geier, R. Alford,
  *Propositional Hierarchical Task Network Planning: Problem Classes and Complexity Results*,

namely

| paper | here |
| --- | --- |
| Def. 3.1, `TO-tn_I`, `TO-M`, `TO` | `Problem.IsTO_tnI`, `Problem.IsTO_M`, `Problem.IsTO` |
| Def. 3.2, `noHTN` | `Problem.IsNoHTN` |
| Def. 3.3, `REG` | `TaskNetwork.IsRegular`, `Problem.IsRegular` |
| Def. 3.4, strata / height | `Problem.IsStratification`, `Problem.HasHeightOne`, `Problem.HasHeightZero` |
| Def. 3.5, `≤₀`-stratification | `Problem.IsStrat0` |
| Def. 3.6, `ACYC` | `Problem.IsAcyclic` |
| Def. 3.7, `≤₁`-stratification | `Problem.IsStrat1` |
| Def. 3.8, `MOSTLY-ACYC` | `Problem.IsMostlyAcyclic` |
| Def. 3.9, `≤_r`-stratification | `Problem.IsStratR` |
| Def. 3.10, `TAIL-REC` | `Problem.IsTailRecursive` |
| Def. 3.11, `UNRES-REC` | `Problem.IsUnrestricted` (always true) |

In addition we formalise the *no-op* restriction (all actions have empty precondition, add and
delete lists), which is not part of Section 3 but is one of the classes studied in the
compilability project.

Following the paper, all structural restrictions are stated in terms of the methods that are
*reachable* from the initial task network (see `HtnPlanning/Core/Reachability.lean`).

The named problem classes of the compilability paper (`HTN`, `TO-HTN`, `HTN-NOOP`, …) are
collected as sets of planning problems in the namespace `HTN.Classes` at the end of the file.
-/

namespace HTN

universe u v w x

/-! ### Restrictions on single task networks -/

namespace TaskNetwork

variable {I : Type x} {A : Type v} {C : Type w}

lemma IsRegular.isLastId {tn : TaskNetwork I A C} (h : tn.IsRegular) {t : I} (ht : t ∈ tn.T)
    (habs : tn.IsAbstractId t) : tn.IsLastId t :=
  ⟨ht, h.2 t ht habs⟩

/-- In a regular task network every compound task is a last task. -/
lemma IsRegular.no_nonlast_abstract {tn : TaskNetwork I A C} (h : tn.IsRegular) {t : I}
    (ht : t ∈ tn.T) (habs : tn.IsAbstractId t) (hlast : ¬ tn.IsLastId t) : False :=
  hlast (h.isLastId ht habs)

/-- An empty or purely primitive task network is regular. -/
lemma IsPrimitive.isRegular {tn : TaskNetwork I A C} (h : tn.IsPrimitive) : tn.IsRegular := by
  refine ⟨?_, ?_⟩ <;> intro t ht <;> obtain ⟨a, ha⟩ := h t ht
  · rintro t' ht' ⟨c, hc⟩ -
    exact absurd (ha ▸ hc) (by simp)
  · rintro ⟨c, hc⟩
    exact absurd (ha ▸ hc) (by simp)

end TaskNetwork

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### Definition 3.1: totally ordered problems -/

/-! ### Definition 3.2: non-hierarchical problems -/

/-- `noHTN`: the initial task network contains only primitive tasks. -/
def IsNoHTN (P : Problem F A C I) : Prop := P.tnI.IsPrimitive

/-! ### Definition 3.3: regular problems -/

/-! ### Definition 3.4: stratifications -/

/-- A stratification has *height ≤ 1* iff all reachable compound task names lie in one single
stratum (Def. 3.4: the height is the number of strata). -/
def HasHeightOne (P : Problem F A C I) (le : C → C → Prop) : Prop :=
  ∀ c₁ c₂, P.ReachableName c₁ → P.ReachableName c₂ → le c₁ c₂

/-- A problem has a stratification of height `0` iff it has no reachable compound task name
(Def. 3.4). -/
def HasHeightZero (P : Problem F A C I) : Prop := ∀ c : C, ¬ P.ReachableName c

/-! ### Definitions 3.5/3.6: acyclic problems -/

/-! ### Definitions 3.7/3.8: mostly-acyclic problems -/

/-- **Definition 3.7 (`≤₁`-stratification).** A stratification in which compound subtasks of
methods with more than one subtask are strictly smaller than the decomposed task, while a
method with a single subtask may stay inside the stratum. -/
structure IsStrat1 (P : Problem F A C I) (le : C → C → Prop) : Prop where
  /-- `le` is a stratification. -/
  strat : P.IsStratification le
  /-- Methods with more than one subtask strictly decrease the stratum of compound subtasks. -/
  big : ∀ m : Method I A C, P.ReachableMethod m → 1 < m.subtasks.T.card →
    ∀ t ∈ m.subtasks.T, ∀ c : C, m.subtasks.α t = Sum.inr c →
      le c m.abstractTask ∧ ¬ le m.abstractTask c
  /-- Methods with exactly one subtask do not increase the stratum. -/
  small : ∀ m : Method I A C, P.ReachableMethod m → m.subtasks.T.card = 1 →
    ∀ t ∈ m.subtasks.T, ∀ c : C, m.subtasks.α t = Sum.inr c → le c m.abstractTask

/-- **Definition 3.8 (`MOSTLY-ACYC`).** -/
def IsMostlyAcyclic (P : Problem F A C I) : Prop := ∃ le : C → C → Prop, P.IsStrat1 le

/-! ### Definitions 3.9/3.10: tail-recursive problems -/

/-- Tail-recursive problems with a stratification of height one (`TAIL-REC₁`). -/
def IsTailRecursive1 (P : Problem F A C I) : Prop :=
  ∃ le : C → C → Prop, P.IsStratR le ∧ P.HasHeightOne le

/-! ### Definition 3.11: unrestricted problems -/

/-! ### The no-op restriction -/

end Problem

/-! ### The named problem classes

The classes of the compilability project, as sets of planning problems. -/

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x)

/-- `MOSTLY-ACYC`: mostly-acyclic HTN planning problems (Def. 3.8). -/
def MOSTLY_ACYC : Set (Problem F A C I) := {P | P.IsMostlyAcyclic}

/-- `noHTN`: problems whose initial task network is primitive (Def. 3.2). -/
def noHTN : Set (Problem F A C I) := {P | P.IsNoHTN}

/-- `REG-ACYC`: problems that are both regular and acyclic. -/
def HTN_REG_AC : Set (Problem F A C I) := HTN_REG F A C I ∩ HTN_AC F A C I

end Classes

end HTN
