import HtnComplexity.TMEnc.TMEncFixCellCut
import HtnComplexity.TMEnc.TMEncFixHeadUnits
/-!
# Counting the actions of the channel `head`

The alignment of the head counter with the tape is a counting argument on the channel `head`:
the tape issues one request per produced cell, a transition of the machine issues `moveExtra`
extra ones, and the head counter consumes them one per unit.  This file collects the counts of
the four synchronisation actions of that channel in the building blocks of a plan:

* one produced cell (`HTN.TMEnc.cellRun`, `HTN.TMEnc.cellTail`) issues exactly one request;
* a cell of a cell counter issues no `start`/`respond` on `head`, and issues as many requests as
  it waits for;
* the stream of the head counter issues no request at all;
* `HTN.TMEnc.countP_isCall_head_of_prefix_cellTail` — **a prefix of a cell of the tape that has
  already issued a request on the `check` channel has issued its request on the `head` channel**
  (and has waited for the answer).  This is what puts the decision of a cell counter *after* the
  `wait head` of the cell it belongs to.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The requests of one produced cell -/

@[simp] lemma countP_isCall_head_acquireActs (x : SyncKind) :
    (acquireActs Q Γ x).countP (isCall SyncKind.head) = if x = SyncKind.head then 1 else 0 := by
  cases x <;> simp [acquireActs, isCall]

@[simp] lemma countP_isWait_head_acquireActs (x : SyncKind) :
    (acquireActs Q Γ x).countP (isWait SyncKind.head) = if x = SyncKind.head then 1 else 0 := by
  cases x <;> simp [acquireActs, isWait]

@[simp] lemma countP_isCall_head_cellTail :
    (cellTail Q Γ K).countP (isCall SyncKind.head) = 1 := by
  simp [cellTail, countP_roundStream]

@[simp] lemma countP_isWait_head_cellTail :
    (cellTail Q Γ K).countP (isWait SyncKind.head) = 1 := by
  simp [cellTail, countP_roundStream]

@[simp] lemma countP_isCall_check_cellTail :
    (cellTail Q Γ K).countP (isCall SyncKind.check) = K + 1 := by
  simp [cellTail, countP_roundStream, acquireActs, isCall]

@[simp] lemma countP_isCall_head_cellRun {b : Option Γ} :
    (cellRun Q Γ K b).countP (isCall SyncKind.head) = 1 := by
  rw [cellRun_eq_cons, List.countP_cons_of_neg (by simp [isCall]), countP_isCall_head_cellTail]

@[simp] lemma countP_isWait_head_cellRun {b : Option Γ} :
    (cellRun Q Γ K b).countP (isWait SyncKind.head) = 1 := by
  rw [cellRun_eq_cons, List.countP_cons_of_neg (by simp [isWait]), countP_isWait_head_cellTail]

@[simp] lemma countP_isCall_head_tapePrefix {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isCall SyncKind.head) = n := by
  rw [tapePrefix, countP_roundStream]
  simp

@[simp] lemma countP_isWait_head_tapePrefix {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isWait SyncKind.head) = n := by
  rw [tapePrefix, countP_roundStream]
  simp

/-! ### A prefix of a cell that has already asked a counter -/

/-- **A prefix of the tail of a produced cell that has issued a request on the `check` channel
has already issued — and waited for the answer to — its request on the `head` channel.** -/
theorem countP_isCall_head_of_prefix_cellTail {T : List (TMAct Q Γ)} (hT : T <+: cellTail Q Γ K)
    (hcheck : 1 ≤ T.countP (isCall SyncKind.check)) :
    T.countP (isCall SyncKind.head) = 1 ∧ T.countP (isWait SyncKind.head) = 1 := by
  have hacq : acquireActs Q Γ SyncKind.head <+: cellTail Q Γ K := by
    rw [cellTail]; exact List.prefix_append _ _
  rcases List.prefix_or_prefix_of_prefix hT hacq with hle | hle
  · exfalso
    have h0 : (acquireActs Q Γ SyncKind.head).countP (isCall SyncKind.check) = 0 := by
      simp [acquireActs, isCall]
    have hcnt := hle.sublist.countP_le (p := isCall SyncKind.check)
    rw [h0] at hcnt
    omega
  · obtain ⟨S, hS⟩ := hle
    have hrest : S <+: (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
        (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync) := by
      have hcell : cellTail Q Γ K = acquireActs Q Γ SyncKind.head ++
          ((roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
            (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync)) := rfl
      obtain ⟨r, hr⟩ := hT
      refine ⟨r, ?_⟩
      have : acquireActs Q Γ SyncKind.head ++ (S ++ r) =
          acquireActs Q Γ SyncKind.head ++
            ((roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
              (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync)) := by
        rw [← List.append_assoc, hS, hr, ← hcell]
      exact List.append_cancel_left this
    have hzeroC : S.countP (isCall SyncKind.head) = 0 := by
      have hle' := hrest.sublist.countP_le (p := isCall SyncKind.head)
      have : ((roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
          (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync)).countP
            (isCall SyncKind.head) = 0 := by
        simp [countP_roundStream]
      omega
    have hzeroW : S.countP (isWait SyncKind.head) = 0 := by
      have hle' := hrest.sublist.countP_le (p := isWait SyncKind.head)
      have : ((roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
          (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync)).countP
            (isWait SyncKind.head) = 0 := by
        simp [countP_roundStream]
      omega
    constructor
    · rw [← hS, List.countP_append, hzeroC]
      simp [acquireActs, isCall]
    · rw [← hS, List.countP_append, hzeroW]
      simp [acquireActs, isWait]

/-! ### The cells of a cell counter -/

@[simp] lemma countP_isCall_head_waitCellActs :
    (waitCellActs Q Γ).countP (isCall SyncKind.head) = 0 := by simp [waitCellActs, isCall]

@[simp] lemma countP_isWait_head_waitCellActs :
    (waitCellActs Q Γ).countP (isWait SyncKind.head) = 0 := by simp [waitCellActs, isWait]

@[simp] lemma countP_isStart_head_waitCellActs :
    (waitCellActs Q Γ).countP (isStart SyncKind.head) = 0 := by simp [waitCellActs, isStart]

@[simp] lemma countP_isRespond_head_waitCellActs :
    (waitCellActs Q Γ).countP (isRespond SyncKind.head) = 0 := by simp [waitCellActs, isRespond]

/-- A decision of a cell counter issues as many requests on the `head` channel as it waits for,
namely `moveExtra` of its move, and it answers none. -/
lemma countP_head_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    p.countP (isCall SyncKind.head) = p.countP (isWait SyncKind.head) ∧
      p.countP (isStart SyncKind.head) = 0 ∧ p.countP (isRespond SyncKind.head) = 0 := by
  rcases stepDecision_iff.1 h with ⟨q, q', a, b, mv, -, rfl⟩ | rfl
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp [countP_roundStream, acquireActs, isCall, isWait, isStart, isRespond]
  · exact ⟨rfl, rfl, rfl⟩

/-- A predicate that is false on every action a cell counter performs does not occur in a cell
of a cell counter. -/
lemma countP_counterCell_eq_zero {f : TMAct Q Γ → Bool} {d : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    (hstart : ∀ x : SyncKind, f (TMAct.start x) = false)
    (hrespond : ∀ x : SyncKind, f (TMAct.respond x) = false)
    (hcall : f (TMAct.call SyncKind.head) = false)
    (hwait : f (TMAct.wait SyncKind.head) = false)
    (hcheck : ∀ g : TMFact Q Γ, f (TMAct.check g) = false)
    (hstep : ∀ (q q' : Q) (a b : Option Γ), f (TMAct.step q a q' b) = false) (n : ℕ) :
    (counterCell Q Γ K d P c n).countP f = 0 := by
  have hdec : ∀ t < K, (P t).countP f = 0 := by
    intro t ht
    rcases stepDecision_iff.1 (hP t ht) with ⟨q, q', a, b, mv, -, hPt⟩ | hPt <;> rw [hPt]
    · simp [hstep, countP_roundStream, acquireActs, hcall, hwait]
    · simp [hcheck]
  by_cases hn : n < d
  · rw [counterCell_of_lt hn]; simp [waitCellActs, hstart, hrespond]
  · rw [counterCell_of_ge (Nat.not_lt.1 hn), counterSeg]
    set r := n - d with hr
    split_ifs with h1 h2 h3 h4
    · simp [waitCellActs, hstart, hrespond]
    · simp [relCheckActs, relSyncActs, hstart, hrespond]
    · rw [List.countP_append, List.countP_append, List.countP_cons, hdec 0 (by omega)]
      simp [relCheckActs, relSyncActs, hstart, hrespond, chkAct, hcheck]
    · rw [List.countP_append, List.countP_cons, List.countP_append, List.countP_cons,
        hdec (r / (K + 1)) h4]
      simp [relCheckActs, relSyncActs, hstart, hrespond, chkAct, hcheck]
    · rw [List.countP_append, List.countP_cons]
      simp [relCheckActs, relSyncActs, hstart, hrespond, chkAct, hcheck]

/-- A cell counter issues no request on a cell channel. -/
lemma countP_isCall_counterCell {x : SyncKind} (hx : x ≠ SyncKind.head) {d : ℕ}
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    (n : ℕ) : (counterCell Q Γ K d P c n).countP (isCall x) = 0 :=
  countP_counterCell_eq_zero hP (by simp [isCall]) (by simp [isCall])
    (by simp [isCall]; exact fun h => hx h.symm) (by simp [isCall]) (by simp [isCall])
    (by simp [isCall]) n

/-- A cell of a cell counter neither consumes a request nor answers one on the `head` channel,
and it issues as many requests there as it waits for. -/
theorem countP_head_counterCell {d : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) (n : ℕ) :
    (counterCell Q Γ K d P c n).countP (isCall SyncKind.head) =
        (counterCell Q Γ K d P c n).countP (isWait SyncKind.head) ∧
      (counterCell Q Γ K d P c n).countP (isStart SyncKind.head) = 0 ∧
      (counterCell Q Γ K d P c n).countP (isRespond SyncKind.head) = 0 := by
  by_cases hn : n < d
  · rw [counterCell_of_lt hn]; exact ⟨rfl, rfl, rfl⟩
  · rw [counterCell_of_ge (Nat.not_lt.1 hn), counterSeg]
    set r := n - d with hr
    split_ifs with h1 h2 h3 h4
    · exact ⟨rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, rfl⟩
    · obtain ⟨e₁, e₂, e₃⟩ := countP_head_stepDecision (hP 0 (by omega))
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [List.countP_append, List.countP_cons, e₁, e₂, e₃] <;>
        simp [relCheckActs, relSyncActs, isCall, isWait, isStart, isRespond, chkAct]
    · obtain ⟨e₁, e₂, e₃⟩ := countP_head_stepDecision (hP (r / (K + 1)) h4)
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [List.countP_append, List.countP_cons, e₁, e₂, e₃] <;>
        simp [relCheckActs, relSyncActs, isCall, isWait, isStart, isRespond, chkAct]
    · refine ⟨?_, ?_, ?_⟩ <;>
        simp [relCheckActs, relSyncActs, isCall, isWait, isStart, isRespond, chkAct]

end TMEnc

end HTN
