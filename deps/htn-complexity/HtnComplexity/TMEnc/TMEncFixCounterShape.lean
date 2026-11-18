import HtnComplexity.Interleave.CutTools
import HtnComplexity.TMEnc.TMEncFixCounterCells
/-!
# The shape of one cell of a cell counter

Every cell of a cell counter of the repaired encoding begins by answering the request on the
`check` channel and ends by answering the one on the `sync` channel.  This file records that
shape — it is what makes a prefix of a counter that has answered `n` requests on either channel
*exactly* the first `n` cells of the counter (`HTN.prefix_roundStream_eq`):

* `HTN.TMEnc.counterCell_head` — a cell starts with `start check`;
* `HTN.TMEnc.counterCell_last` — a cell ends with `respond sync`;
* `HTN.TMEnc.countP_isRespond_counterCell` — a cell answers exactly one request on either
  channel.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Every cell begins with `start check` and ends with `respond sync` -/

lemma counterSeg_head {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (r : ℕ) :
    ∃ t, counterSeg Q Γ K P c r = TMAct.start SyncKind.check :: t := by
  unfold counterSeg
  split_ifs <;> exact ⟨_, rfl⟩

lemma counterSeg_last {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (r : ℕ) :
    ∃ t, counterSeg Q Γ K P c r = t ++ relSyncActs Q Γ := by
  unfold counterSeg
  split_ifs
  · exact ⟨[TMAct.start SyncKind.check, TMAct.respond SyncKind.check], rfl⟩
  · exact ⟨relCheckActs Q Γ, rfl⟩
  · exact ⟨relCheckActs Q Γ ++ (P 0 ++ [chkAct Q Γ (c 0)]), by simp⟩
  · exact ⟨relCheckActs Q Γ ++ (chkAct Q Γ (c (r / (K + 1) - 1)) ::
      (P (r / (K + 1)) ++ [chkAct Q Γ (c (r / (K + 1)))])), by simp⟩
  · exact ⟨relCheckActs Q Γ ++ [chkAct Q Γ (c (K - 1))], by simp⟩

/-- **A cell of a counter begins with the answer to the request on the `check` channel.** -/
lemma counterCell_head {d : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (n : ℕ) :
    ∃ t, counterCell Q Γ K d P c n = TMAct.start SyncKind.check :: t := by
  by_cases h : n < d
  · rw [counterCell_of_lt h]; exact ⟨_, rfl⟩
  · rw [counterCell_of_ge (Nat.not_lt.1 h)]; exact counterSeg_head _

/-- **A cell of a counter ends with the answer to the request on the `sync` channel.** -/
lemma counterCell_last {d : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (n : ℕ) :
    ∃ t, counterCell Q Γ K d P c n = t ++ [TMAct.respond SyncKind.sync] := by
  have hgen : ∀ l : List (TMAct Q Γ), (∃ t, l = t ++ relSyncActs Q Γ) →
      ∃ t, l = t ++ [TMAct.respond SyncKind.sync] := by
    rintro l ⟨t, rfl⟩
    exact ⟨t ++ [TMAct.start SyncKind.sync], by simp [relSyncActs]⟩
  by_cases h : n < d
  · rw [counterCell_of_lt h]
    exact ⟨[TMAct.start SyncKind.check, TMAct.respond SyncKind.check, TMAct.start SyncKind.sync],
      rfl⟩
  · rw [counterCell_of_ge (Nat.not_lt.1 h)]
    exact hgen _ (counterSeg_last _)

/-! ### Every cell answers exactly one request on either channel -/

lemma countP_isRespond_counterSeg (x : SyncKind) (hx : x ≠ SyncKind.head)
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    (r : ℕ) : (counterSeg Q Γ K P c r).countP (isRespond x) = 1 := by
  have hP' : ∀ t < K, (P t).countP (isRespond x) = 0 := by
    intro t ht
    rcases stepDecision_iff.1 (hP t ht) with ⟨q, q', a, b, m, -, hPt⟩ | hPt <;> rw [hPt]
    · simp [isRespond, countP_roundStream, acquireActs]
    · simp [isRespond]
  rcases x with _ | _ | _
  · exact absurd rfl hx
  all_goals {
    unfold counterSeg
    split_ifs with h1 h2 h3 h4
    · simp [waitCellActs, isRespond]
    · simp [relCheckActs, relSyncActs, isRespond]
    · rw [List.countP_append, List.countP_append, List.countP_cons,
        hP' 0 (by omega)]
      simp [relCheckActs, relSyncActs, isRespond, chkAct]
    · rw [List.countP_append, List.countP_cons, List.countP_append, List.countP_cons,
        hP' (r / (K + 1)) h4]
      simp [relCheckActs, relSyncActs, isRespond, chkAct]
    · rw [List.countP_append, List.countP_cons]
      simp [relCheckActs, relSyncActs, isRespond, chkAct] }

/-- **In every one of its cells a counter gives exactly one answer on the channel `x`.** -/
theorem countP_isRespond_counterCell (x : SyncKind) (hx : x ≠ SyncKind.head) {d : ℕ}
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    (n : ℕ) : (counterCell Q Γ K d P c n).countP (isRespond x) = 1 := by
  by_cases h : n < d
  · rw [counterCell_of_lt h]
    rcases x with _ | _ | _
    · exact absurd rfl hx
    all_goals simp [waitCellActs, isRespond]
  · rw [counterCell_of_ge (Nat.not_lt.1 h)]
    exact countP_isRespond_counterSeg x hx hP _

/-! ### A prefix of a counter that has answered `n` requests is its first `n` cells -/

/-- **A prefix of the run of a cell counter that has answered `n` requests on the `check` channel
and given `n` answers on the `sync` channel is exactly the stream of the first `n` cells of that
counter.** -/
theorem prefix_counterRun_eq {d e : ℕ} (hde : d + e = K) {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) {q : List (TMAct Q Γ)}
    (hq : q <+: counterRun Q Γ K d e P c) {n : ℕ} (hn : n ≤ (K + 1) * (K + 1))
    (hcf : q.countP (isStart SyncKind.check) = n)
    (hcg : q.countP (isRespond SyncKind.sync) = n) :
    q = roundStream n (counterCell Q Γ K d P c) := by
  rw [counterRun_eq_roundStream hde] at hq
  refine prefix_roundStream_eq (isStart SyncKind.check) (isRespond SyncKind.sync)
    (fun r _ => countP_isStart_counterCell (N := N) (w := w) SyncKind.check (by simp) hP r)
    (fun r _ => countP_isRespond_counterCell (N := N) (w := w) SyncKind.sync (by simp) hP r)
    (fun r _ => ?_) (fun r _ => ?_) hq hn hcf hcg
  · obtain ⟨t, ht⟩ := counterCell_head (Q := Q) (Γ := Γ) (K := K) (d := d) (P := P) (c := c) r
    exact ⟨TMAct.start SyncKind.check, t, ht, by simp [isStart]⟩
  · obtain ⟨t, ht⟩ := counterCell_last (Q := Q) (Γ := Γ) (K := K) (d := d) (P := P) (c := c) r
    exact ⟨t, TMAct.respond SyncKind.sync, ht, by simp [isRespond]⟩

end TMEnc

end HTN
