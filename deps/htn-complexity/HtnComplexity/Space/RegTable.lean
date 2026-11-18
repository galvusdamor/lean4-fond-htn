import HtnComplexity.Space.StripsSystem
import HtnComplexity.Computable.TokCell
import HtnComplexity.Computable.RegStripsCell
/-!
# Regular HTN plan existence, as reachability in an action table

This is the *mathematical* half of ingredient 3 of `TABLE3-PLAN.md` for the target class
`HTN-REG-1` (regular methods, a single initial compound task).  It composes

* the token gadget `HTN.Syn.tokDom` / `HTN.Syn.tokInst`
  (`HtnComplexity/Computable/TokDom.lean`), which turns a regular domain into a *totally
  ordered* regular one, and
* the macro-action compilation `HTN.Syn.regStripsDom` / `HTN.Syn.regStripsInst`
  (`HtnComplexity/Computable/RegStrips.lean`), Alford's translation in the form this
  development verified, which turns a totally ordered regular domain into a `STRIPS` one,

with `HtnComplexity/Space/StripsSystem.lean`, and reads off:

    HTN.Space.solvable_reg_iff_solvableTbl :
      Solvable d q ↔ (regDom d).HasEmptyMethod ∧ SolvableTbl (regTable d) (regInit q) (regGoal q)

for a regular domain description `d` and a rooted instance description `q`.  The three
ingredients on the right are completely explicit:

* `HTN.Space.regTable d` — the action table of the compiled `STRIPS` domain: a **function of the
  domain description alone**, which is what will be written into the advice string of the
  machine;
* `HTN.Space.regInit q = q.initList.map (12 * ·) ++ [8 * rootName q + 1]` and
  `HTN.Space.regGoal q = q.goalList.map (12 * ·) ++ [2]` — the initial state and the goal of the
  compiled problem, **functions of the instance description alone**, and of the simplest possible
  shape: a renaming of the facts of `q` by `v ↦ 12 v`, one extra fact naming the initial compound
  task, and the bookkeeping fact `2` ("done") in the goal.

That the two are separated in this way is exactly what the target side needs: the machine of
`ComplexityTheory/Space/Model.lean` reads the table off its advice and the initial state and
goal off its input.

The size bound `HTN.Space.size_regDom_le` records that the compiled domain — hence the table —
is of polynomial size in the source domain description.
-/

namespace HTN

namespace Space

open Syn

variable {d : DomDesc} {q : InstDesc}

/-- **The compiled `STRIPS` domain description** of a regular domain description: the token
gadget followed by the macro-action compilation. -/
def regDom (d : DomDesc) : DomDesc := regStripsDom (tokDom d)

/-- **The action table** of a regular domain description. -/
def regTable (d : DomDesc) : List Row := (regDom d).stepActs.map (actOf (regDom d))

/-- The initial state of the compiled problem. -/
def regInit (q : InstDesc) : List ℕ := (regStripsInst (tokInst q)).initList

/-- The goal of the compiled problem. -/
def regGoal (q : InstDesc) : List ℕ := (regStripsInst (tokInst q)).goalList

/-! ### The compiled instance, explicitly -/

theorem rootName_tokInst (q : InstDesc) : rootName (tokInst q) = 2 * rootName q := by
  simp [rootName, tokInst, InstDesc.tnI, TnDesc.compoundNames, TnDesc.ids, TnDesc.lbl,
    TnDesc.labelList, ctName]

theorem regInit_eq (q : InstDesc) :
    regInit q = q.initList.map (fun v => 12 * v) ++ [8 * rootName q + 1] := by
  have h : regInit q
      = (tokInst q).initList.map (fun v => 4 * v) ++ [4 * rootName (tokInst q) + 1] := rfl
  rw [h, rootName_tokInst]
  simp only [tokInst, InstDesc.initList, stateF, List.map_map, Function.comp_def]
  congr 1
  · exact List.map_congr_left fun v _ => by ring
  · congr 1
    ring

theorem regGoal_eq (q : InstDesc) :
    regGoal q = q.goalList.map (fun v => 12 * v) ++ [2] := by
  simp only [regGoal, regStripsInst, stripsInst, InstDesc.goalList, tokInst, stateF,
    List.map_map, Function.comp_def]
  congr 1
  exact List.map_congr_left fun v _ => by ring

/-! ### Plan existence as reachability -/

/-- **Plan existence for a regular HTN description with a rooted instance is reachability in the
action table of its compiled `STRIPS` domain.** -/
theorem solvable_reg_iff_solvableTbl (hreg : d.MethodsReg) (hq : q.IsRooted) :
    Solvable d q ↔
      (regDom d).HasEmptyMethod ∧ SolvableTbl (regTable d) (regInit q) (regGoal q) := by
  rw [solvable_tok_iff hreg hq,
    solvable_regStrips_iff (tokDom_methodsTO d) (tokDom_methodsReg d) (tokInst_isRooted q),
    solvable_isStrips_iff_solvableTbl (regStripsDom_isStrips (tokDom d))
      (regStripsInst_isStrips (tokInst q))]
  rfl

/-! ### The compiled domain is of polynomial size -/

/-- **The compiled domain description is polynomially longer than the source one.** -/
theorem size_regDom_le : ∃ p : Polynomial ℕ, ∀ d : DomDesc, (regDom d).size ≤ p.eval d.size := by
  refine ⟨Polynomial.C 20 * (Polynomial.C 60 * (Polynomial.X + 1) ^ 3 + 1) ^ 3, fun d => ?_⟩
  have h1 := size_tokDom_le d
  have h2 := size_regStripsDom_le (tokDom d)
  have hm : (tokDom d).size + 1 ≤ 60 * (d.size + 1) ^ 3 + 1 := by
    have : (d.size + 1) ^ 3 = (d.size + 1) * (d.size + 1) * (d.size + 1) := by ring
    omega
  calc (regDom d).size ≤ 20 * (((tokDom d).size + 1) ^ 3) := by
        simpa only [regDom, pow_succ, pow_zero, one_mul] using h2
    _ ≤ 20 * (60 * (d.size + 1) ^ 3 + 1) ^ 3 := by gcongr
    _ = _ := by simp

end Space

end HTN
