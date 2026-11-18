import HtnComplexity.Space.RegRename
import HtnComplexity.Space.TblSolver
import HtnComplexity.Computable.DescEnum
/-!
# The action table of a compiled regular problem has polynomially many symbols

The advice of the target-side machine is (an encoding of) the action table of the compiled
domain, so its length has to be bounded — in the number of symbols of the source domain
description, which is the measure of the compilability table.  This file supplies the
combinatorial half of that bound:

    HTN.Space.tblSize_regTable_le :
      ∃ p : Polynomial ℕ, ∀ d : DomDesc, tblSize (regTable d) ≤ p.eval d.size

with `HTN.Space.tblSize` the number of symbols of a table (one per row, one per listed fact).
The argument is generic: the action table of *any* domain description `e` has at most
`e.size + e.size ^ 2` symbols, because `e` lists at most `e.size` action occurrences in its
methods and each action it describes lists at most `e.size` facts; the compiled domain is
polynomially bigger than the source one (`HTN.Space.size_regDom_le`), and the renaming of
`HtnComplexity/Space/Rename.lean` changes no length.

What this bound does **not** control is the *magnitude* of the facts, and it cannot: a domain
description of few symbols may mention numerals of astronomical size.  That is the reason the
machine hypothesis `HTN.Space.TblSolver` lets the advice depend on the bound `L` on the facts of
the input.
-/

namespace HTN

namespace Space

open Syn

/-! ### The action table of a domain description -/

theorem length_labelList_le_one (k : Bool) (l : List (ℕ × Bool × ℕ)) (i : ℕ) :
    (TnDesc.labelList k l i).length ≤ 1 := by
  rw [TnDesc.labelList_eq]
  rcases l.lookup i with _ | ⟨b, c⟩
  · cases k <;> simp
  · by_cases hb : b = k <;> simp [hb]

theorem length_actionNames_le (t : TnDesc) : t.actionNames.length ≤ t.ids.length := by
  rw [TnDesc.actionNames, List.length_flatMap]
  calc (t.ids.map fun i => (TnDesc.labelList false t.lbl i).length).sum
      ≤ (t.ids.map fun _ => 1).sum :=
        List.sum_le_sum fun i _ => length_labelList_le_one _ _ _
    _ = t.ids.length := by simp

theorem length_stepActs_le_size (e : DomDesc) : e.stepActs.length ≤ e.size := by
  rw [DomDesc.stepActs, List.length_flatMap]
  have h1 : (e.methods.map fun m => m.2.actionNames.length).sum
      ≤ (e.methods.map MethodDesc.size).sum :=
    List.sum_le_sum fun m _ => le_trans (length_actionNames_le m.2)
      (by simp only [MethodDesc.size, TnDesc.size]; omega)
  simp only [DomDesc.size]
  omega

/-- Every row of the action table lists at most `e.size` facts. -/
theorem rowSize_actOf_le (e : DomDesc) (a : ℕ) :
    (actOf e a).1.length + (actOf e a).2.1.length + (actOf e a).2.2.length ≤ e.size := by
  rw [actOf_eq]
  rcases h : e.actions.lookup a with _ | x
  · simp
  · have hs := ActionDesc.size_le_of_mem (mem_of_lookup_eq_some h)
    simp only [ActionDesc.size] at hs
    simp only [Option.elim, id_eq]
    omega

/-- **The action table of a domain description has at most `e.size + e.size ^ 2` symbols.** -/
theorem tblSize_actTable_le (e : DomDesc) :
    tblSize (e.stepActs.map (actOf e)) ≤ e.size + e.size * e.size := by
  have hlen := length_stepActs_le_size e
  rw [tblSize, List.length_map, List.map_map]
  have hsum : (e.stepActs.map ((fun r : Row => r.1.length + r.2.1.length + r.2.2.length) ∘
      actOf e)).sum ≤ e.stepActs.length * e.size := by
    have := List.sum_le_card_nsmul
      (e.stepActs.map ((fun r : Row => r.1.length + r.2.1.length + r.2.2.length) ∘ actOf e))
      e.size (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        exact rowSize_actOf_le e a)
    simpa using this
  calc e.stepActs.length + _ ≤ e.size + e.stepActs.length * e.size := by omega
    _ ≤ e.size + e.size * e.size := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _

/-! ### The compiled table -/

@[simp] theorem tblSize_map_mapRow (ρ : ℕ → ℕ) (tbl : List Row) :
    tblSize (tbl.map (mapRow ρ)) = tblSize tbl := by
  simp [tblSize, mapRow, List.map_map, Function.comp_def]

/-- **The action table of the compiled regular domain has polynomially many symbols in the
number of symbols of the source domain description.** -/
theorem tblSize_regTable_le :
    ∃ p : Polynomial ℕ, ∀ d : DomDesc, tblSize (regTable d) ≤ p.eval d.size := by
  obtain ⟨p, hp⟩ := size_regDom_le
  refine ⟨p + p * p, fun d => ?_⟩
  have h := tblSize_actTable_le (regDom d)
  have hN := hp d
  simp only [Polynomial.eval_add, Polynomial.eval_mul]
  calc tblSize (regTable d) ≤ (regDom d).size + (regDom d).size * (regDom d).size := h
    _ ≤ p.eval d.size + p.eval d.size * p.eval d.size :=
        Nat.add_le_add hN (Nat.mul_le_mul hN hN)

/-- The same bound for the renamed table. -/
theorem tblSize_regTableR_le :
    ∃ p : Polynomial ℕ, ∀ d : DomDesc, tblSize (regTableR d) ≤ p.eval d.size := by
  obtain ⟨p, hp⟩ := tblSize_regTable_le
  exact ⟨p, fun d => by rw [regTableR, tblSize_map_mapRow]; exact hp d⟩

end Space

end HTN
