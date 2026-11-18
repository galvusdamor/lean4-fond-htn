import HtnComplexity.Space.RegSize
import HtnComplexity.Computable.TrStripsCell
/-!
# Tail-recursive totally ordered HTN plan existence, as reachability in an action table

This is for the target class `TO-HTN-TR-1` what `HtnComplexity/Space/RegTable.lean` and
`HtnComplexity/Space/RegRename.lean` are for `HTN-REG-1`: the *mathematical* half of
ingredient 3 of `TABLE3-PLAN.md`.  It reads Alford's translation of a totally ordered
tail-recursive description into `STRIPS` — the bounded stack machine of
`HtnComplexity/Computable/TrStrips.lean`, whose correctness is
`HTN.Syn.solvable_trStrips_iff` and whose size is polynomial of degree five in the source
(`HTN.Syn.size_trStripsDom_le`) — as reachability in an action table:

    HTN.Space.solvable_tr_iff_solvableTbl :
      Solvable d q ↔ (trDom d).HasEmptyMethod ∧ SolvableTbl (trTable d) (trInit q) (trGoal q)

for a totally ordered tail-recursive domain description `d` and a rooted instance description
`q`.  The table `trTable d` is a function of the *domain description alone*, and is what the
advice of the target-side machine carries; the initial state and the goal are functions of the
*instance description alone*, of the same shape as in the regular case:

    trInit q = q.initList.map (6 * ·) ++ [6 * rootName q + 3],   trGoal q = … ++ [4].

The renaming `HTN.Space.trRho` — `6 v ↦ 4 v + 2`, `6 c + 3 ↦ 4 c + 3`, `4 ↦ 0` and
`n ↦ 4 n + 4` on everything else — is injective, so solvability is invariant under it
(`HTN.Space.solvableTbl_map`), and it turns the instance side into *literally* the lists
`HTN.Space.regInitR q` and `HTN.Space.regGoalR q` of the regular case.  That is what lets the
machine `HTN.Space.instMachine` of `HtnComplexity/Space/InstMachine.lean` — which reads the
compiled initial state and goal off the code of the instance description — be reused verbatim:
only the table, which is advice, changes.

**No assumption is made on the cost of the domain translation.**  Only the number of symbols of
the table matters, and `HTN.Space.tblSize_trTableR_le` bounds it polynomially.
-/

namespace HTN

namespace Space

open Syn

variable {d : DomDesc} {q : InstDesc}

/-! ### The compiled domain, the table and the compiled instance -/

/-- **The compiled `STRIPS` domain description** of a totally ordered tail-recursive domain
description: Alford's bounded stack machine. -/
def trDom (d : DomDesc) : DomDesc := trStripsDom d

/-- **The action table** of a totally ordered tail-recursive domain description. -/
def trTable (d : DomDesc) : List Row := (trDom d).stepActs.map (actOf (trDom d))

/-- The initial state of the compiled problem. -/
def trInit (q : InstDesc) : List ℕ := (trStripsInst q).initList

/-- The goal of the compiled problem. -/
def trGoal (q : InstDesc) : List ℕ := (trStripsInst q).goalList

theorem trInit_eq (q : InstDesc) :
    trInit q = q.initList.map (fun v => 6 * v) ++ [6 * rootName q + 3] := rfl

theorem trGoal_eq (q : InstDesc) : trGoal q = q.goalList.map (fun v => 6 * v) ++ [4] := rfl

/-! ### Plan existence as reachability -/

/-- **Plan existence for a totally ordered tail-recursive HTN description with a rooted instance
is reachability in the action table of its compiled `STRIPS` domain.** -/
theorem solvable_tr_iff_solvableTbl (hTO : d.MethodsTO) (hTR : d.IsTailRec) (hq : q.IsRooted) :
    Solvable d q ↔
      (trDom d).HasEmptyMethod ∧ SolvableTbl (trTable d) (trInit q) (trGoal q) := by
  rw [← solvable_trStrips_iff hTO hTR hq,
    solvable_isStrips_iff_solvableTbl (d := trStripsDom d) (q := trStripsInst q)
      (stripsDom_isStrips (trActions d)) (stripsInst_isStrips _ _)]
  rfl

/-! ### The renaming the compiled problem calls for

The facts of the compiled problem are `6 v` (a fact `v` of the source instance), `6 c + 3` (the
initial compound task `c`, not yet started), `4` ("done"), and the frame facts `6 p + 1`,
`6 p + 2` and the unsatisfiable fact `5`.  Dividing the first two families by `3` resp. `2` and
moving everything else out of the way gives an instance side in which each numeral is obtained
from the numeral of the instance by prefixing two constant bits — the form the machine reads. -/

/-- **The renaming of the facts of a compiled tail-recursive problem**: `6 v ↦ 4 v + 2`,
`6 c + 3 ↦ 4 c + 3`, `4 ↦ 0`, and `n ↦ 4 n + 4` on everything else. -/
def trRho (n : ℕ) : ℕ :=
  if n % 6 = 0 then n / 6 * 4 + 2
  else if n % 6 = 3 then n / 6 * 4 + 3
  else if n = 4 then 0
  else 4 * n + 4

@[simp] theorem trRho_state (v : ℕ) : trRho (6 * v) = 4 * v + 2 := by
  rw [trRho, if_pos (by omega)]; omega

@[simp] theorem trRho_call (c : ℕ) : trRho (6 * c + 3) = 4 * c + 3 := by
  rw [trRho, if_neg (by omega), if_pos (by omega)]; omega

@[simp] theorem trRho_done : trRho 4 = 0 := by decide

/-- **The renaming is injective.** -/
theorem trRho_injective : Function.Injective trRho := by
  intro a b h
  simp only [trRho] at h
  split_ifs at h <;> omega

/-- **The renamed action table** of a totally ordered tail-recursive domain description. -/
def trTableR (d : DomDesc) : List Row := (trTable d).map (mapRow trRho)

/-- The renamed initial state of the compiled problem is the one of the regular case. -/
theorem map_trRho_trInit (q : InstDesc) : (trInit q).map trRho = regInitR q := by
  rw [trInit_eq]
  simp [regInitR, List.map_map, Function.comp_def]

/-- The renamed goal of the compiled problem is the one of the regular case. -/
theorem map_trRho_trGoal (q : InstDesc) : (trGoal q).map trRho = regGoalR q := by
  rw [trGoal_eq]
  simp [regGoalR, List.map_map, Function.comp_def]

/-- **Plan existence for a totally ordered tail-recursive HTN description with a rooted instance
is reachability in the renamed action table**, with an initial state and a goal read off the
instance by prefixing two constant bits to each of its numerals — the very same lists as in the
regular case. -/
theorem solvable_tr_iff_solvableTblR (hTO : d.MethodsTO) (hTR : d.IsTailRec) (hq : q.IsRooted) :
    Solvable d q ↔
      (trDom d).HasEmptyMethod ∧ SolvableTbl (trTableR d) (regInitR q) (regGoalR q) := by
  rw [solvable_tr_iff_solvableTbl hTO hTR hq, trTableR, ← map_trRho_trInit q,
    ← map_trRho_trGoal q, solvableTbl_map (injOnRel_of_injective trRho_injective)]

/-! ### The table has polynomially many symbols -/

/-- **The compiled domain description is polynomially longer than the source one.** -/
theorem size_trDom_le : ∃ p : Polynomial ℕ, ∀ d : DomDesc, (trDom d).size ≤ p.eval d.size := by
  refine ⟨145 * (Polynomial.X + 1) ^ 5, fun d => ?_⟩
  have he : (145 * (Polynomial.X + 1) ^ 5 : Polynomial ℕ).eval d.size =
      145 * ((d.size + 1) ^ 5) := by
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add]
  rw [he]
  exact size_trStripsDom_le d

/-- **The action table of the compiled tail-recursive domain has polynomially many symbols in the
number of symbols of the source domain description.** -/
theorem tblSize_trTable_le :
    ∃ p : Polynomial ℕ, ∀ d : DomDesc, tblSize (trTable d) ≤ p.eval d.size := by
  obtain ⟨p, hp⟩ := size_trDom_le
  refine ⟨p + p * p, fun d => ?_⟩
  have h := tblSize_actTable_le (trDom d)
  have hN := hp d
  simp only [Polynomial.eval_add, Polynomial.eval_mul]
  calc tblSize (trTable d) ≤ (trDom d).size + (trDom d).size * (trDom d).size := h
    _ ≤ p.eval d.size + p.eval d.size * p.eval d.size :=
        Nat.add_le_add hN (Nat.mul_le_mul hN hN)

/-- The same bound for the renamed table. -/
theorem tblSize_trTableR_le :
    ∃ p : Polynomial ℕ, ∀ d : DomDesc, tblSize (trTableR d) ≤ p.eval d.size := by
  obtain ⟨p, hp⟩ := tblSize_trTable_le
  exact ⟨p, fun d => by rw [trTableR, tblSize_map_mapRow]; exact hp d⟩

end Space

end HTN
