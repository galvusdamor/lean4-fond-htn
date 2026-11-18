import HtnComplexity.Space.RegTable
import HtnComplexity.Space.Rename
/-!
# The compiled regular problem, in the renamed vocabulary

`HtnComplexity/Space/RegTable.lean` reduces plan existence for a regular HTN description
with a rooted instance to reachability in an action table, with the instance entering only
through

    regInit q = q.initList.map (12 * ·) ++ [8 * rootName q + 1]     regGoal q = … ++ [2].

The numerals `12 v` and `8 c + 1` are not string surgeries on the numeral of `v` resp. `c`:
computing them means multiplying a binary numeral by `3`.  Renaming the facts by
`HTN.Space.regRho` (`HtnComplexity/Space/Rename.lean`), which is injective, leaves
solvability alone and turns the instance side into

    regInitR q = q.initList.map (4 * · + 2) ++ [4 * rootName q + 3]   regGoalR q = … ++ [0],

where every numeral is obtained from the numeral of the instance by appending two constant
bits.  This is the form the machine of `ComplexityTheory/Space/Model.lean` reads:

    HTN.Space.solvable_reg_iff_solvableTblR :
      Solvable d q ↔ (regDom d).HasEmptyMethod ∧ SolvableTbl (regTableR d) (regInitR q) (regGoalR q)

with `regTableR d` — the renamed action table — again a function of the domain description
alone, of size polynomial in it (`HTN.Space.size_regDom_le`), so it can be written into the
advice.
-/

namespace HTN

namespace Space

open Syn

variable {d : DomDesc} {q : InstDesc}

/-- **The renamed action table** of a regular domain description. -/
def regTableR (d : DomDesc) : List Row := (regTable d).map (mapRow regRho)

/-- The initial state of the compiled problem, in the renamed vocabulary. -/
def regInitR (q : InstDesc) : List ℕ :=
  q.initList.map (fun v => 4 * v + 2) ++ [4 * rootName q + 3]

/-- The goal of the compiled problem, in the renamed vocabulary. -/
def regGoalR (q : InstDesc) : List ℕ := q.goalList.map (fun v => 4 * v + 2) ++ [0]

theorem map_regRho_regInit (q : InstDesc) : (regInit q).map regRho = regInitR q := by
  rw [regInit_eq]
  simp [regInitR, List.map_map, Function.comp_def]

theorem map_regRho_regGoal (q : InstDesc) : (regGoal q).map regRho = regGoalR q := by
  rw [regGoal_eq]
  simp [regGoalR, List.map_map, Function.comp_def]

/-- **Plan existence for a regular HTN description with a rooted instance is reachability in the
renamed action table**, with an initial state and a goal read off the instance by appending two
constant bits to each of its numerals. -/
theorem solvable_reg_iff_solvableTblR (hreg : d.MethodsReg) (hq : q.IsRooted) :
    Solvable d q ↔
      (regDom d).HasEmptyMethod ∧ SolvableTbl (regTableR d) (regInitR q) (regGoalR q) := by
  rw [solvable_reg_iff_solvableTbl hreg hq, regTableR, ← map_regRho_regInit q,
    ← map_regRho_regGoal q, solvableTbl_regRho]

end Space

end HTN
