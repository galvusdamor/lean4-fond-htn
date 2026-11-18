import HtnComplexity.TMEnc.TMEncFixCounterAlt
/-!
# The run of a cell counter, cut into its own cells

The lock-step theorem (`HTN.TMEnc.lockstep`) counts, at the end of the `n`-th cell of the tape,
the requests each cell counter has answered: exactly `n` on either channel.  To turn that count
into a statement about *what* the counter did, the run of a counter has to be cut into its own
cells, and this file provides that cut:

* `HTN.TMEnc.counterCell` — the cell `n` of the counter with the leading delay `d`: a waiting
  cycle during the delay, and otherwise the cell `n - d` of `HTN.TMEnc.counterSeg` (the
  cell-by-cell description of the body that `HtnComplexity/TMEnc/TMEncFixSchedule.lean` builds);
* `HTN.TMEnc.counterRun_eq_roundStream` — **the run of a counter with delays `(d, e)`, `d + e =
  K`, is the stream of its `(K+1)²` cells**;
* `HTN.TMEnc.countP_isStart_counterCell` — **every cell of a counter answers exactly one request
  on each of the two cell channels.**
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **The cell `n` of a cell counter with leading delay `d`.** -/
def counterCell (Q Γ : Type) (K d : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ) (n : ℕ) :
    List (TMAct Q Γ) :=
  if n < d then waitCellActs Q Γ else counterSeg Q Γ K P c (n - d)

/-- Outside its body a counter waits. -/
lemma counterCell_of_lt {d : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} {n : ℕ}
    (h : n < d) : counterCell Q Γ K d P c n = waitCellActs Q Γ := by
  simp [counterCell, h]

lemma counterCell_of_ge {d : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} {n : ℕ}
    (h : d ≤ n) : counterCell Q Γ K d P c n = counterSeg Q Γ K P c (n - d) := by
  simp [counterCell, Nat.not_lt.2 h]

/-- **The run of a cell counter is the stream of its `(K+1)²` cells.** -/
theorem counterRun_eq_roundStream {d e : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hde : d + e = K) :
    counterRun Q Γ K d e P c = roundStream ((K + 1) * (K + 1)) (counterCell Q Γ K d P c) := by
  have hsplit : (K + 1) * (K + 1) = d + ((K * (K + 1) + 1) + e) := by nlinarith [hde]
  have h1 : roundStream d (counterCell Q Γ K d P c) =
      roundStream d fun _ => waitCellActs Q Γ :=
    roundStream_congr fun r hr => counterCell_of_lt hr
  have h2 : (roundStream (K * (K + 1) + 1) fun r => counterCell Q Γ K d P c (d + r)) =
      counterBody Q Γ K P c := by
    rw [roundStream_congr (t := counterSeg Q Γ K P c) fun r _ => by
      rw [counterCell_of_ge (Nat.le_add_right d r)]
      congr 1
      omega]
    rw [counterSeg_run]
    rfl
  have h3 : (roundStream e fun r => counterCell Q Γ K d P c (d + (K * (K + 1) + 1 + r))) =
      roundStream e fun _ => waitCellActs Q Γ := by
    refine roundStream_congr fun r hr => ?_
    rw [counterCell_of_ge (by omega), counterSeg_wait]
    have hmod : (d + (K * (K + 1) + 1 + r) - d) % (K + 1) = (1 + r) % (K + 1) := by
      rw [show d + (K * (K + 1) + 1 + r) - d = 1 + r + K * (K + 1) by omega,
        Nat.add_mul_mod_self_right]
    rw [hmod, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [counterRun, hsplit, roundStream_add, roundStream_add, h1, h2, h3]

/-! ### Every cell of a counter answers exactly one request on each channel -/

lemma countP_isStart_counterSeg (x : SyncKind) (hx : x ≠ SyncKind.head)
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    (r : ℕ) : (counterSeg Q Γ K P c r).countP (isStart x) = 1 := by
  have hP' : ∀ t < K, (P t).countP (isStart x) = 0 := by
    intro t ht
    rcases stepDecision_iff.1 (hP t ht) with ⟨q, q', a, b, m, -, hPt⟩ | hPt <;> rw [hPt]
    · simp [isStart, countP_roundStream, acquireActs]
    · simp [isStart]
  rcases x with _ | _ | _
  · exact absurd rfl hx
  all_goals {
    unfold counterSeg
    split_ifs with h1 h2 h3 h4
    · simp [waitCellActs, isStart]
    · simp [relCheckActs, relSyncActs, isStart]
    · rw [List.countP_append, List.countP_append, List.countP_cons,
        hP' 0 (by omega)]
      simp [relCheckActs, relSyncActs, isStart, chkAct]
    · rw [List.countP_append, List.countP_cons, List.countP_append, List.countP_cons,
        hP' (r / (K + 1)) h4]
      simp [relCheckActs, relSyncActs, isStart, chkAct]
    · rw [List.countP_append, List.countP_cons]
      simp [relCheckActs, relSyncActs, isStart, chkAct] }

/-- **In every one of its cells a counter answers exactly one request on the channel `x`.** -/
theorem countP_isStart_counterCell (x : SyncKind) (hx : x ≠ SyncKind.head) {d : ℕ}
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    (n : ℕ) : (counterCell Q Γ K d P c n).countP (isStart x) = 1 := by
  by_cases h : n < d
  · rw [counterCell_of_lt h]
    rcases x with _ | _ | _
    · exact absurd rfl hx
    all_goals simp [waitCellActs, isStart]
  · rw [counterCell_of_ge (Nat.not_lt.1 h)]
    exact countP_isStart_counterSeg x hx hP _

end TMEnc

end HTN
