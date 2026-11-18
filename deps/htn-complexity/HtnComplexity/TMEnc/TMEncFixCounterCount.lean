import HtnComplexity.TMEnc.TMEncFixCounterAnalysis
/-!
# One cell counter answers exactly one request per tape cell

The tape of the repaired encoding produces `(K+1)²` cells, and each of them issues one request on
the `check` channel to each of the `K + 1` cell counters (`HTN.TMEnc.cellRun`).  This file proves
the matching statement on the side of the counters: **a cell counter with delays `(d, e)` answers
exactly `d + e + K² + K + 1` requests on the `check` channel**, hence exactly `(K+1)²` of them
when `d + e = K` — one per produced cell.  Together with the request count of the tape this is
the quantitative half of the lock-step argument of the soundness direction.
-/

namespace HTN

variable {α : Type}

/-- The number of marked actions of a stream is the sum over its rounds. -/
lemma countP_roundStream (p : α → Bool) (R : ℕ) (s : ℕ → List α) :
    (roundStream R s).countP p = ∑ r ∈ Finset.range R, (s r).countP p := by
  induction R with
  | zero => simp
  | succ R ih => rw [roundStream_succ, List.countP_append, ih, Finset.sum_range_succ]

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

@[simp] lemma countP_startCheck_acquireActs (x : SyncKind) :
    (acquireActs Q Γ x).countP (isStart SyncKind.check) = 0 := by
  simp [acquireActs, isStart]

@[simp] lemma countP_startCheck_waitCellActs :
    (waitCellActs Q Γ).countP (isStart SyncKind.check) = 1 := by
  simp [waitCellActs, isStart]

@[simp] lemma countP_startCheck_relCheckActs :
    (relCheckActs Q Γ).countP (isStart SyncKind.check) = 1 := by
  simp [relCheckActs, isStart]

@[simp] lemma countP_startCheck_relSyncActs :
    (relSyncActs Q Γ).countP (isStart SyncKind.check) = 0 := by
  simp [relSyncActs, isStart]

@[simp] lemma countP_startCheck_chkAct (c : Option Γ) :
    [chkAct Q Γ c].countP (isStart SyncKind.check) = 0 := by
  simp [chkAct, isStart]

/-- One `chk` gadget spans a block of `K + 1` cells. -/
lemma countP_startCheck_chkRun (c : Option Γ) :
    (chkRun Q Γ K c).countP (isStart SyncKind.check) = K + 1 := by
  simp [chkRun, chkAct, isStart, countP_roundStream]

/-- A decision of a counter answers no request on the `check` channel. -/
lemma countP_startCheck_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    p.countP (isStart SyncKind.check) = 0 := by
  rcases stepDecision_iff.1 h with ⟨q, q', c, c', m, -, rfl⟩ | rfl
  · simp [isStart, countP_roundStream]
  · simp [isStart]

/-- **The body of a cell counter answers `K² + K + 1` requests on the `check` channel.** -/
lemma countP_startCheck_counterBody {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    (counterBody Q Γ K P c).countP (isStart SyncKind.check) = K * K + K + 1 := by
  have hsum : ∀ t ∈ Finset.range K,
      (P t ++ chkRun Q Γ K (c t)).countP (isStart SyncKind.check) = K + 1 := by
    intro t ht
    rw [List.countP_append, countP_startCheck_stepDecision (hP t (Finset.mem_range.1 ht)),
      countP_startCheck_chkRun, Nat.zero_add]
  rw [counterBody, List.countP_append, List.countP_append, countP_roundStream,
    Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, smul_eq_mul,
    countP_startCheck_relCheckActs, countP_startCheck_relSyncActs]
  ring

/-- **A cell counter answers one request on the `check` channel per cell it is alive**: `d + e`
during its delays and `K² + K + 1` during its body. -/
theorem countP_startCheck_counterRun {d e : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    (counterRun Q Γ K d e P c).countP (isStart SyncKind.check) = d + e + (K * K + K + 1) := by
  rw [counterRun, List.countP_append, List.countP_append, countP_roundStream, countP_roundStream,
    countP_startCheck_counterBody hP, countP_startCheck_waitCellActs]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
  ring

/-- **Every cell counter of a plan answers exactly `(K+1)²` requests on the `check` channel** —
one per cell the tape produces.  The delays of the counters of a plan sum to `K`
(`HTN.TMEnc.chainYield_checkers_forward`), so this holds for each of the `K + 1` counters. -/
theorem countP_startCheck_counterRun_of_delays {d e : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) (hde : d + e = K) :
    (counterRun Q Γ K d e P c).countP (isStart SyncKind.check) = (K + 1) * (K + 1) := by
  rw [countP_startCheck_counterRun hP, hde]
  ring

end TMEnc

end HTN
