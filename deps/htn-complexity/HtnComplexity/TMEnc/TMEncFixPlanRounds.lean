import HtnComplexity.TMEnc.TMEncFixCounterCount
import HtnComplexity.Interleave.RoundSplit
/-!
# A solution plan of the repaired encoding, cell by cell

`HTN.TMEnc.isSolutionPlanFix_normalForm` describes a solution plan as an interleaving of three
streams.  Using `HTN.interleave_roundStream_split_pos` — the extraction of a round decomposition
from an interleaving — this file cuts the plan along the cells of the tape:

`HTN.TMEnc.isSolutionPlanFix_cells` — **every solution plan is a sequence of `(K+1)²` cells
followed by the accepting test; cell `n` consists of the actions of the tape cell `n`
(`HTN.TMEnc.cellRun`, i.e. `assert (sym n)` and its requests) interleaved with the actions the
head counter and the cell counters perform during that cell.**

This is the cut the soundness argument needs; what is still missing after it is the *content* of
the interleaved parts, which the semaphore protocol determines.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **A solution plan of the repaired problem, cut into the cells of the tape.** -/
theorem isSolutionPlanFix_cells (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)} (h : (problemFix N w K).IsSolutionPlan as) :
    ∃ (sym : ℕ → Option Γ) (cell other : ℕ → List (TMAct Q Γ)) (f : Q),
      (∀ j ≤ K, sym j = tapeInitSym N w j) ∧
      (∀ i ≤ K, sym (i * (K + 1)) = none) ∧
      f ∈ N.accept ∧
      (∀ n < (K + 1) * (K + 1), Interleave (other n) (cellRun Q Γ K (sym n)) (cell n)) ∧
      as = roundStream ((K + 1) * (K + 1)) cell ++ [TMAct.check (TMFact.st f)] ∧
      (problemFix N w K).SeqApplicable as (problemFix N w K).init := by
  obtain ⟨sym, ps, ass, ac, bs, as₁, f, hinit, hsep, -, -, -, hint', hint, hf, rfl, happ⟩ :=
    isSolutionPlanFix_normalForm hw hwK h
  obtain ⟨x, -, hx⟩ := Interleave.assoc' hint' hint
  obtain ⟨others, cells, -, hcells, hall⟩ :=
    interleave_roundStream_split_pos (R := (K + 1) * (K + 1)) (by positivity) hx
  subst hcells
  exact ⟨sym, cells, others, f, hinit, hsep, hf, hall, rfl, happ⟩

end TMEnc

end HTN
