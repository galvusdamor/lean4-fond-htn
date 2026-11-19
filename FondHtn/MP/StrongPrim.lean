import FondHtn.MPStrong.CyclicAcyc
import FondHtn.StrongOD.PrimComplete
import FondHtn.Prim.StrongP
import FondHtn.Prim.WeakMem
/-!
# Strong (and fair) method-based policies for primitive problems ([CB22, Cor. 1])

On a primitive task network no decomposition is possible, so the AND/OR game of strong
method-based policies is the solvable-belief-state game of fixed-method strong OD
(`FOND.Problem.mpAndOr_iff_beliefSolvable`).  For primitive problems the two criteria coincide
(`FOND.Problem.mpStrongSolvable_iff_strongOD_of_primitive`), hence so do the languages for every
class of primitive problems (`FOND.planExMP_strong_eq_strongOD`); primitive problems are acyclic,
so the fair strong cyclic language is the same as well.

* **`FOND.strongMP_PRIM_TO_mem`**, **`FOND.fairMP_PRIM_TO_mem`** — in P for primitive totally
  ordered problems;
* **`FOND.strongMP_PRIM_complete`**, **`FOND.fairMP_PRIM_complete`** — PSPACE-complete for
  primitive problems (hardness via TQBF, `FOND.strongOD_PRIM_pspaceHard`).
-/

namespace FOND

open HTN

namespace Problem

variable {F A C I : Type*} [DecidableEq I] {P : Problem F A C I}

/-- **On a primitive network the strong AND/OR game is the solvable-belief-state game.** -/
theorem mpAndOr_iff_beliefSolvable {tn : TaskNetwork I A C} (hp : tn.IsPrimitive) {s : Set F} :
    P.MPAndOr tn s ↔ P.BeliefSolvable tn s := by
  constructor
  · intro h
    induction h with
    | empty h => exact .empty h
    | prim hu hα happ _ ih => exact .step hu hα happ fun s' hs' => ih s' hs' (hp.progress _)
    | @decomp tn tn' s t m hd _ _ =>
      exfalso
      obtain ⟨-, ht, hlab, -⟩ := hd
      obtain ⟨a, ha⟩ := hp t ht
      rw [ha] at hlab
      exact absurd hlab (by simp)
  · intro h
    induction h with
    | empty h => exact .empty h
    | step hu hα happ _ ih => exact .prim hu hα happ fun s' hs' => ih s' hs' (hp.progress _)

/-- **[CB22, Cor. 1]: for primitive problems strong method-based solvability is fixed-method
strong OD solvability.** -/
theorem mpStrongSolvable_iff_strongOD_of_primitive [Infinite I] (hP : P.WF)
    (hp : P.tnI.IsPrimitive) : P.MPStrongSolvable ↔ P.StrongODSolvable := by
  rw [mpStrongSolvable_iff_mpAndOr hP, mpAndOr_iff_beliefSolvable hp,
    strongODSolvable_iff_fmSolvableDB]
  constructor
  · exact fun h => ⟨P.tnI, (P.achievablePrimitive_iff_of_primitive hp).2 rfl, h⟩
  · rintro ⟨tn, hach, h⟩
    rwa [(P.achievablePrimitive_iff_of_primitive hp).1 hach] at h

end Problem

theorem FClass.PRIM.tnI {P : Problem ℕ ℕ ℕ ℕ} (h : FClass.PRIM P) : P.tnI.IsPrimitive := h

theorem FClass.PRIM.acyc {P : Problem ℕ ℕ ℕ ℕ} (h : FClass.PRIM P) : FClass.ACYC P :=
  HTN.Problem.IsNoHTN.isAcyclic h

/-- For classes of primitive problems, strong MP and strong OD plan existence coincide. -/
theorem planExMP_strong_eq_strongOD {Y : FClass} (hY : ∀ P, Y P → FClass.PRIM P) :
    PlanExMP .strong Y = PlanExFM .strongOD Y := by
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy, (Problem.mpStrongSolvable_iff_strongOD_of_primitive
      (FProbDesc.toProblem_wf hp) (hY _ hy).tnI).1 hs⟩
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy, (Problem.mpStrongSolvable_iff_strongOD_of_primitive
      (FProbDesc.toProblem_wf hp) (hY _ hy).tnI).2 hs⟩

/-- **[CB22, Cor. 1]: strong MP plan existence for primitive totally ordered problems is in P.** -/
theorem strongMP_PRIM_TO_mem : Cx.P (PlanExMP .strong (FClass.inter FClass.PRIM FClass.TO)) := by
  rw [planExMP_strong_eq_strongOD fun _ h => h.1]; exact strongOD_PRIM_TO_mem

/-- **[CB22, Cor. 1]: strong MP plan existence for primitive problems is PSPACE-complete.** -/
theorem strongMP_PRIM_complete : Cx.Complete Cx.PSPACE (PlanExMP .strong FClass.PRIM) := by
  rw [planExMP_strong_eq_strongOD fun _ h => h]; exact strongOD_PRIM_complete

/-- **[CB22, Cor. 1], fair strong cyclic: in P for primitive totally ordered problems.** -/
theorem fairMP_PRIM_TO_mem : Cx.P (PlanExMPFair (FClass.inter FClass.PRIM FClass.TO)) := by
  rw [planExMPFair_eq_strong fun _ h => h.1.acyc]; exact strongMP_PRIM_TO_mem

/-- **[CB22, Cor. 1], fair strong cyclic: PSPACE-complete for primitive problems.** -/
theorem fairMP_PRIM_complete : Cx.Complete Cx.PSPACE (PlanExMPFair FClass.PRIM) := by
  rw [planExMPFair_eq_strong fun _ h => h.acyc]; exact strongMP_PRIM_complete

end FOND
