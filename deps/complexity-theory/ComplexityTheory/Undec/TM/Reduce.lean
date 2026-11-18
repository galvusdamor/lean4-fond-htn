import ComplexityTheory.Undec.TM.Digits
import ComplexityTheory.Undec.Sim.Main
/-!
# A two-stack machine with an undecidable halting problem

Putting the two halves together:

* `ComplexityTheory/Undec/TM/Chain.lean` turns Mathlib's evaluator of partial recursive codes
  into a plain Turing machine `N0` with a finite set `S0 c₀` of relevant control states;
* `ComplexityTheory/Undec/Sim/` simulates such a Turing machine by a two-stack machine.

Choosing for `c₀` a code of the universal function `n ↦ ⟦n⟧(0)` and encoding the input on the
second stack gives a *fixed* two-stack machine whose halting problem is undecidable
(`HTN.Undec.exists_undecidable_tsm`).
-/

namespace HTN

namespace Undec

namespace TMChain

open Turing Turing.PartrecToTM2

open scoped Classical

/-! ### A code for the universal function -/

/-- The universal partial function `n ↦ ⟦n⟧(0)`, on codes named by natural numbers. -/
noncomputable def univFun (n : ℕ) : Part ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0

theorem partrec_univFun : Partrec univFun :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)

theorem univFun_exists :
    ∃ c : ToPartrec.Code, ∀ w : List.Vector ℕ 1,
      ToPartrec.Code.eval c w.1 = pure <$> univFun w.head :=
  ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 partrec_univFun)

/-- A code of `Turing.ToPartrec` for the universal function. -/
noncomputable def univCode : ToPartrec.Code := univFun_exists.choose

theorem univCode_dom (n : ℕ) :
    (ToPartrec.Code.eval univCode [n]).Dom ↔ (univFun n).Dom := by
  have h := univFun_exists.choose_spec (⟨[n], rfl⟩ : List.Vector ℕ 1)
  rw [show ((⟨[n], rfl⟩ : List.Vector ℕ 1) : List ℕ) = [n] from rfl] at h
  rw [show univCode = univFun_exists.choose from rfl, h]
  rfl

/-! ### The initial tape of a singleton input -/

/-- The tape cell holding the symbol `a` on the main stack. -/
def cell (a : Γ') : K' → Option Γ' := Function.update (fun _ => none) K'.main (some a)

theorem initTape_singleton (n : ℕ) :
    initTape [n] =
      ((true, cell Γ'.cons) : Gam1) ::
        ((trNat n).reverse.map fun a => ((false, cell a) : Gam1)) := by
  have hrev : (trList [n]).reverse = Γ'.cons :: (trNat n).reverse := by
    simp [trList]
  simp [initTape, TM2to1.trInit, cell]

end TMChain

/-! ### The two-stack machine and the reduction -/

namespace Sim

open Turing Turing.PartrecToTM2 HTN.Undec.TMChain

open scoped Classical

/-- The code of a tape symbol carrying `a` on the main stack. -/
noncomputable def gcode (a : Γ') : ℕ := symCode ((false, cell a) : Gam1)

/-- The reduction: the second stack of the two-stack machine for the input `n`. -/
noncomputable def redStack (n : ℕ) : List ℕ :=
  symCode ((true, cell Γ'.cons) : Gam1) :: ((digs gcode n).reverse ++ [0])

theorem redStack_eq (n : ℕ) : redStack n = encL (initTape [n]) := by
  rw [redStack, initTape_singleton, encL, digs]
  simp [gcode, List.map_reverse]

theorem primrec_redStack : Primrec redStack := by
  refine Primrec.list_cons.comp (Primrec.const _) ?_
  exact Primrec.list_append.comp (Primrec.list_reverse.comp (primrec_digs gcode))
    (Primrec.const [0])

end Sim

/-! ### The result -/

open Turing Turing.PartrecToTM2 HTN.Undec.TMChain HTN.Undec.Sim

open scoped Classical

/-- **The two-stack machine with an undecidable halting problem.** -/
noncomputable def undecTSM : TSM := simTSM N0 (S0 univCode) (q0 univCode)

theorem undecTSM_halts_iff (n : ℕ) :
    undecTSM.Halts [0] (redStack n) ↔ (univFun n).Dom := by
  have h1 : encL ([] : List Gam1) = [0] := rfl
  rw [undecTSM, redStack_eq, ← h1,
    simTSM_halts_iff (supports univCode) (start_mem_supp univCode) (initTape [n]),
    dom_chain univCode [n], univCode_dom]

/-- **The halting problem of `undecTSM` is undecidable.** -/
theorem not_computablePred_undecTSM :
    ¬ ComputablePred fun p : List ℕ × List ℕ => undecTSM.Halts p.1 p.2 := by
  intro h
  obtain ⟨g, hg, hgeq⟩ := ComputablePred.computable_iff.1 h
  refine ComputablePred.halting_problem 0 ?_
  refine ComputablePred.computable_iff.2
    ⟨fun c : Nat.Partrec.Code => g ([0], redStack (Encodable.encode c)), ?_, ?_⟩
  · exact hg.comp ((Primrec.const [0]).pair (primrec_redStack.comp Primrec.encode)).to_comp
  · funext c
    have hg' := congrFun hgeq ([0], redStack (Encodable.encode c))
    have hu := undecTSM_halts_iff (Encodable.encode c)
    rw [univFun, Denumerable.ofNat_encode] at hu
    simp only [eq_iff_iff]
    rw [← hu, ← hg']

/-- **There is a two-stack machine whose halting problem is undecidable.** -/
theorem exists_undecidable_tsm :
    ∃ M : TSM, ¬ ComputablePred fun p : List ℕ × List ℕ => M.Halts p.1 p.2 :=
  ⟨undecTSM, not_computablePred_undecTSM⟩

end Undec

end HTN
