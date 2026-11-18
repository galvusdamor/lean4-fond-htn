import HtnPlanning.Classes.HD2
/-!
# Loop-unrolling problems (`L`) and the classes `1-HD-HTN ∩ L`, `2-HD-HTN ∩ L`

Following

    M. Dekker, G. Behnke, *Barely Decidable Fragments of Planning* (Sect. 3),

a problem is **loop-unrolling** if it has at most one compound task name and at most two methods
(`|C| ≤ 1` and `|M| ≤ 2`).  As for the other classes of the project, the restriction is imposed on
the part of the problem reachable from the initial task network (`HTN.Problem.IsLU`): the
reachable compound task names form a subsingleton, and there are at most two reachable methods.

Dekker and Behnke show that plan existence is already `ACKERMANN`-hard for clean, bottomless,
one-hole-digging, loop-unrolling problems (Prop. 8), and ask (Sect. 6) whether plan existence for
`H₂ ∩ L` — two-hole-digging, loop-unrolling problems — is decidable.  This file defines the
classes for that question.
-/

namespace HTN

universe u v w x

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- **`L` (loop-unrolling problems, Dekker and Behnke, Sect. 3)**: at most one reachable compound
task name and at most two reachable methods. -/
def IsLU (P : Problem F A C I) : Prop :=
  {c | P.ReachableName c}.Subsingleton ∧ {m | P.ReachableMethod m}.encard ≤ 2

end Problem

/-! ### The named classes -/

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x)

/-- `L`: loop-unrolling HTN planning problems. -/
def LU_HTN : Set (Problem F A C I) := {P | P.IsLU}

/-- `1-HD-HTN ∩ L`: one-hole-digging, loop-unrolling problems. -/
def HD1_LU_HTN : Set (Problem F A C I) := HD1_HTN F A C I ∩ LU_HTN F A C I

/-- `2-HD-HTN ∩ L`: two-hole-digging, loop-unrolling problems. -/
def HD2_LU_HTN : Set (Problem F A C I) := HD2_HTN F A C I ∩ LU_HTN F A C I

theorem HD1_LU_HTN_subset_HD2_LU_HTN : HD1_LU_HTN F A C I ⊆ HD2_LU_HTN F A C I :=
  fun _ h => ⟨HD1_HTN_subset_HD2_HTN F A C I h.1, h.2⟩

end Classes

namespace Table

namespace Cls

/-- The family `L`. -/
def LU_HTN : Family := fun F A C I _ => Classes.LU_HTN F A C I

/-- The family `1-HD-HTN ∩ L`. -/
def HD1_LU_HTN : Family := fun F A C I _ => Classes.HD1_LU_HTN F A C I

/-- The family `2-HD-HTN ∩ L`. -/
def HD2_LU_HTN : Family := fun F A C I _ => Classes.HD2_LU_HTN F A C I

end Cls

end Table

end HTN
