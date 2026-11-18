import HtnComplexity.TMEnc.TMEncFixHeadChain
import HtnPlanning.Interleave.GridTailYield
/-!
# The three chains of the initial task network, interleaved cell by cell

`HtnComplexity/TMEnc/TMEncFixSchedule.lean`, `TMEncFixTape.lean` and `TMEncFixHeadChain.lean`
describe the refinements of the three chains of `HTN.TMEnc.initChains` — the cell counters, the
tape and the head counter — cell by cell.  This file puts them together:

* `HTN.roundStream_sum` — a stream can be regrouped along any partition of its rounds into
  consecutive blocks (this is what turns the *units* of the head counter into *cells*: a cell
  is answered by one unit plus the extra ones its transition consumes);
* `HTN.TMEnc.gridYield_initChains_of_rounds` — **if each of the three chains refines into a
  stream that is decomposed into the same `R` cells, then the cell-major interleaving of the
  three streams is a refinement of the initial task network** (of its grid part).

What is still missing for the completeness half of the simulation argument is the executability
of the resulting plan and the treatment of the fresh initial task `sI`, whose body is not a
grid; see `NOTES.md`.
-/

namespace HTN

variable {α : Type}

/-- **A stream can be regrouped along a partition of its rounds into consecutive blocks.** -/
lemma roundStream_sum (cnt : ℕ → ℕ) (s : ℕ → List α) : ∀ R : ℕ,
    roundStream (∑ n ∈ Finset.range R, cnt n) s =
      roundStream R fun n => roundStream (cnt n) fun k =>
        s ((∑ m ∈ Finset.range n, cnt m) + k) := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, roundStream_add, ih, roundStream_succ]

/-- **Streams that are merged cell by cell interleave.** -/
lemma interleave_roundStream_of_pointwise_lt {u v z : ℕ → List α} (R : ℕ)
    (h : ∀ r < R, Interleave (u r) (v r) (z r)) :
    Interleave (roundStream R u) (roundStream R v) (roundStream R z) := by
  induction R with
  | zero => simpa using Interleave.nil
  | succ R ih =>
      rw [roundStream_succ, roundStream_succ, roundStream_succ]
      exact (ih fun r hr => h r (by omega)).append_append (h R (by omega))

/-- **Streams that are merged cell by cell interleave.** -/
lemma interleave_roundStream_of_pointwise {u v z : ℕ → List α} (R : ℕ)
    (h : ∀ r, Interleave (u r) (v r) (z r)) :
    Interleave (roundStream R u) (roundStream R v) (roundStream R z) :=
  interleave_roundStream_of_pointwise_lt R fun r _ => h r

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **The cell-major interleaving of the three chains of the initial task network.**

The head counter, the cell counters and the tape are described by their per-cell segments, and
inside each cell the three segments may be interleaved in any way — which is what the
executability of the plan dictates: the tape issues a request, the counter that is due answers
it, and only then does the tape continue. -/
theorem gridYield_initChains_of_rounds {R : ℕ} {hseg cseg tseg ctseg zseg : ℕ → List (TMAct Q Γ)}
    (hhead : (domainBod N w K).ChainYield (headChainFix (Q := Q) (Γ := Γ) K)
      (roundStream R hseg))
    (hchk : (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers (K + 1))]
      (roundStream R cseg))
    (htape : (domainBod N w K).ChainYield
      [Sum.inr TMTask.produceInit, Sum.inr (TMTask.cSeq TMTask.tapeProduce K)]
      (roundStream R tseg))
    (hct : ∀ r < R, Interleave (cseg r) (tseg r) (ctseg r))
    (hz : ∀ r < R, Interleave (hseg r) (ctseg r) (zseg r)) :
    (domainBod N w K).GridYield (initChainsFix (Q := Q) (Γ := Γ) K) (roundStream R zseg) := by
  rw [show (initChainsFix (Q := Q) (Γ := Γ) K) =
    headChainFix (Q := Q) (Γ := Γ) K ::
    [[Sum.inr (TMTask.checkers (K + 1))],
      [Sum.inr TMTask.produceInit, Sum.inr (TMTask.cSeq TMTask.tapeProduce K)]] from rfl,
    gridYield_cons_iff]
  refine ⟨roundStream R hseg, roundStream R ctseg, hhead, ?_,
    interleave_roundStream_of_pointwise_lt R hz⟩
  rw [gridYield_cons_iff]
  exact ⟨roundStream R cseg, roundStream R tseg, hchk, gridYield_singleton_iff.2 htape,
    interleave_roundStream_of_pointwise_lt R hct⟩

/-! ### The fresh initial task -/

/-- **A refinement of the grid part followed by a refinement of `done` is a refinement of the
initial task network of the repaired problem.**

The initial task network is the single fresh task `sI`, whose only method has the body
`HTN.TMEnc.initNetFix K` — the three chains of `HTN.TMEnc.initChainsFix`, all ordered before the
task `done`.  This is the last purely syntactic step of the completeness half: what remains of
it is the executability of the plan. -/
theorem netYield_tnIFix_of_gridYield {as₁ as₂ : List (TMAct Q Γ)}
    (h₁ : (domainBod N w K).GridYield (initChainsFix (Q := Q) (Γ := Γ) K) as₁)
    (h₂ : (domainBod N w K).ChainYield [Sum.inr TMTask.done] as₂) :
    (domainFix N w K).NetYield (instance_ N).tnI (as₁ ++ as₂) := by
  have hbody : (domainBod N w K).NetYield (initNetFix (Q := Q) (Γ := Γ) K) (as₁ ++ as₂) :=
    (netYield_gridTail_iff methods_grid_bod).2 ⟨as₁, as₂, rfl, h₁, h₂⟩
  obtain ⟨n, hn⟩ := netYield_fix_of_bod hbody
  refine ⟨n + 1, (netYieldN_single_comp (t := (0, 0)) (c := TMTask.sI)
    (TaskNetwork.isSingle_seq_singleton _) ?_ methodsFix_wf).2 ?_⟩
  · simp
  · exact ⟨n, ⟨TMTask.sI, initNetFix K⟩, rfl, Or.inr rfl, rfl, hn⟩

/-- **The repaired problem is solvable as soon as the cell-major plan is executable.**

The goal of the encoded problem is empty, so a solution plan is exactly a refinement of the
initial task network that is executable in the initial state.  Together with
`HTN.TMEnc.gridYield_initChains_of_rounds` and the three chain lemmas this reduces the
completeness half of the simulation argument to the executability of the constructed plan. -/
theorem solvable_fix_of_gridYield {as₁ as₂ : List (TMAct Q Γ)}
    (h₁ : (domainBod N w K).GridYield (initChainsFix (Q := Q) (Γ := Γ) K) as₁)
    (h₂ : (domainBod N w K).ChainYield [Sum.inr TMTask.done] as₂)
    (happ : (problemFix N w K).SeqApplicable (as₁ ++ as₂) (problemFix N w K).init) :
    (problemFix N w K).Solvable := by
  refine Problem.solvable_iff_exists_solutionPlan.2 ⟨as₁ ++ as₂, Problem.isSolutionPlan_iff.2
    ⟨netYield_tnIFix_of_gridYield h₁ h₂, happ, ?_⟩⟩
  simp [Problem.GoalState, problemFix, Domain.mkProblem, instance_]

end TMEnc

end HTN
