import ComplexityTheory.Complexity.CobhamString
import ComplexityTheory.Complexity.Basic
/-!
# The polynomial hierarchy, over Cobham's class

This file defines the levels of the **polynomial hierarchy** in the standard way — a bounded
alternating quantifier prefix in front of a polynomial-time predicate — with polynomial time read
as Cobham's class `HTN.PTime.Cobham` (`ComplexityTheory/Complexity/Cobham.lean`), the notion of
polynomial time used throughout this development.

* `HTN.PH.qblock B P k b ys` — `k` alternating quantifiers over bit strings of length at most `B`,
  starting with `∃` when `b = true`, in front of the predicate `P` of the list of quantified
  strings (appended to `ys` in the order they are introduced);
* `HTN.PH.SigmaP k L` — `L ∈ Σₖᵖ`: there are a predicate `p` of Cobham's class and a polynomial
  `q` with `x ∈ L ↔ ∃ y₁ ∀ y₂ … p(x, y₁, …, yₖ)`, all `|yᵢ| ≤ q(|x|)`;
* `HTN.PH.PiP k L` — `L ∈ Πₖᵖ`: the complement of `L` is in `Σₖᵖ`;
* `HTN.PH.PHCollapsesTo k` — `Πₖᵖ ⊆ Σₖᵖ`.  By complementation this is `Σₖᵖ = Πₖᵖ`, which is the
  usual formulation of "*the polynomial hierarchy collapses to its `k`-th level*" (it is
  classically equivalent to `PH = Σₖᵖ`).
-/

namespace HTN

namespace PH

open PTime

@[simp] theorem qblock_zero (B : ℕ) (P : List (List Bool) → Prop) (b : Bool)
    (ys : List (List Bool)) : qblock B P 0 b ys = P ys := rfl

@[simp] theorem qblock_succ_true (B : ℕ) (P : List (List Bool) → Prop) (k : ℕ)
    (ys : List (List Bool)) :
    qblock B P (k + 1) true ys = ∃ y : List Bool, y.length ≤ B ∧ qblock B P k false (ys ++ [y]) :=
  rfl

@[simp] theorem qblock_succ_false (B : ℕ) (P : List (List Bool) → Prop) (k : ℕ)
    (ys : List (List Bool)) :
    qblock B P (k + 1) false ys = ∀ y : List Bool, y.length ≤ B → qblock B P k true (ys ++ [y]) :=
  rfl

end PH

end HTN
