import HtnComplexity.TMEnc.TMEncFixCounterAlt
/-!
# Who issues and who answers a request

The three streams a solution plan of the repaired encoding interleaves
(`HTN.TMEnc.isSolutionPlanFix_normalForm`) use the two cell channels `check` and `sync` in
complementary ways:

* the **tape** only ever *issues* requests — `call` and `wait` — and it issues, in every cell,
  the `K + 1` requests on `check` before the `K + 1` requests on `sync`
  (`HTN.TMEnc.cellRun_split`);
* the **cell counters** only ever *answer* them — `start` and `respond`;
* the **head counter** touches neither channel.

This file proves these statements as counting lemmas; they are what lets the lock-step argument
read off the number of answers given so far from the tape content of a prefix of the plan.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The cell counters do not issue requests on the cell channels -/

/-- A predicate that is false on every action a cell counter performs does not occur in the run
of a cell counter. -/
lemma countP_counterRun_eq_zero {f : TMAct Q Γ → Bool} {d e : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    (hstart : ∀ x : SyncKind, f (TMAct.start x) = false)
    (hrespond : ∀ x : SyncKind, f (TMAct.respond x) = false)
    (hcall : f (TMAct.call SyncKind.head) = false)
    (hwait : f (TMAct.wait SyncKind.head) = false)
    (hcheck : ∀ g : TMFact Q Γ, f (TMAct.check g) = false)
    (hstep : ∀ (q q' : Q) (a b : Option Γ), f (TMAct.step q a q' b) = false) :
    (counterRun Q Γ K d e P c).countP f = 0 := by
  have hwaitCell : (waitCellActs Q Γ).countP f = 0 := by
    simp [waitCellActs, hstart, hrespond]
  have hchk : ∀ b : Option Γ, (chkRun Q Γ K b).countP f = 0 := by
    intro b
    simp [chkRun, chkAct, hcheck, relSyncActs, relCheckActs, hstart, hrespond,
      countP_roundStream, hwaitCell]
  have hdec : ∀ t < K, (P t).countP f = 0 := by
    intro t ht
    rcases stepDecision_iff.1 (hP t ht) with ⟨q, q', a, b, m, -, hPt⟩ | hPt <;> rw [hPt]
    · simp [hstep, countP_roundStream, acquireActs, hcall, hwait]
    · simp [hcheck]
  have hbody : (counterBody Q Γ K P c).countP f = 0 := by
    rw [counterBody, List.countP_append, List.countP_append, countP_roundStream,
      Finset.sum_congr rfl (fun t ht => by
        rw [List.countP_append, hdec t (Finset.mem_range.1 ht), hchk]) ]
    simp [relCheckActs, relSyncActs, hstart, hrespond]
  rw [counterRun, List.countP_append, List.countP_append, countP_roundStream, countP_roundStream,
    hbody, hwaitCell]
  simp

lemma countP_isCall_counterRun {x : SyncKind} (hx : x ≠ SyncKind.head) {d e : ℕ}
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) :
    (counterRun Q Γ K d e P c).countP (isCall x) = 0 :=
  countP_counterRun_eq_zero hP (by simp [isCall]) (by simp [isCall])
    (by simp [isCall]; exact fun h => hx h.symm) (by simp [isCall]) (by simp [isCall])
    (by simp [isCall])

lemma countP_isWait_counterRun {x : SyncKind} (hx : x ≠ SyncKind.head) {d e : ℕ}
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) :
    (counterRun Q Γ K d e P c).countP (isWait x) = 0 :=
  countP_counterRun_eq_zero hP (by simp [isWait]) (by simp [isWait]) (by simp [isWait])
    (by simp [isWait]; exact fun h => hx h.symm) (by simp [isWait]) (by simp [isWait])

/-! ### The head counter touches neither cell channel -/

/-- A predicate that is false on every action of the head counter does not occur in its
stream. -/
lemma countP_headStream_eq_zero {f : TMAct Q Γ → Bool}
    (hstart : f (TMAct.start SyncKind.head) = false)
    (hrespond : f (TMAct.respond SyncKind.head) = false)
    (hassert : f (TMAct.assertHead : TMAct Q Γ) = false)
    (hretract : f (TMAct.retractHead : TMAct Q Γ) = false) :
    (headStream Q Γ K).countP f = 0 := by
  have hunit : ∀ b : Bool, (headUnitActs Q Γ b).countP f = 0 := by
    intro b
    cases b <;> simp [headUnitActs, hstart, hrespond, hassert, hretract]
  rw [headStream, countP_roundStream,
    Finset.sum_congr rfl (fun u _ => hunit (headMarkStd K u))]
  simp

lemma countP_isCall_headStream {x : SyncKind} :
    (headStream Q Γ K).countP (isCall x) = 0 :=
  countP_headStream_eq_zero (by simp [isCall]) (by simp [isCall]) (by simp [isCall])
    (by simp [isCall])

lemma countP_isWait_headStream {x : SyncKind} :
    (headStream Q Γ K).countP (isWait x) = 0 :=
  countP_headStream_eq_zero (by simp [isWait]) (by simp [isWait]) (by simp [isWait])
    (by simp [isWait])

lemma countP_isStart_headStream {x : SyncKind} (hx : x ≠ SyncKind.head) :
    (headStream Q Γ K).countP (isStart x) = 0 :=
  countP_headStream_eq_zero (by simp [isStart]; exact fun h => hx h.symm) (by simp [isStart])
    (by simp [isStart]) (by simp [isStart])

lemma countP_isRespond_headStream {x : SyncKind} (hx : x ≠ SyncKind.head) :
    (headStream Q Γ K).countP (isRespond x) = 0 :=
  countP_headStream_eq_zero (by simp [isRespond]) (by simp [isRespond]; exact fun h => hx h.symm)
    (by simp [isRespond]) (by simp [isRespond])

/-! ### The tape does not answer requests -/

/-- A predicate that is false on every action of the tape does not occur in a produced cell. -/
lemma countP_cellRun_eq_zero {f : TMAct Q Γ → Bool} {b : Option Γ}
    (hassert : ∀ a : Option Γ, f (TMAct.assert a) = false)
    (hcall : ∀ x : SyncKind, f (TMAct.call x) = false)
    (hwait : ∀ x : SyncKind, f (TMAct.wait x) = false) :
    (cellRun Q Γ K b).countP f = 0 := by
  simp [cellRun, acquireActs, hassert, hcall, hwait, countP_roundStream]

lemma countP_isStart_cellRun {x : SyncKind} {b : Option Γ} :
    (cellRun Q Γ K b).countP (isStart x) = 0 :=
  countP_cellRun_eq_zero (by simp [isStart]) (by simp [isStart]) (by simp [isStart])

lemma countP_isRespond_cellRun {x : SyncKind} {b : Option Γ} :
    (cellRun Q Γ K b).countP (isRespond x) = 0 :=
  countP_cellRun_eq_zero (by simp [isRespond]) (by simp [isRespond]) (by simp [isRespond])

/-! ### What the tape issues in one cell -/

/-- The requests a cell issues on the `check` channel. -/
@[simp] lemma countP_isCall_check_cellRun {b : Option Γ} :
    (cellRun Q Γ K b).countP (isCall SyncKind.check) = K + 1 := by
  simp [cellRun, acquireActs, isCall, countP_roundStream]

@[simp] lemma countP_isCall_sync_cellRun {b : Option Γ} :
    (cellRun Q Γ K b).countP (isCall SyncKind.sync) = K + 1 := by
  simp [cellRun, acquireActs, isCall, countP_roundStream]

@[simp] lemma countP_isWait_check_cellRun {b : Option Γ} :
    (cellRun Q Γ K b).countP (isWait SyncKind.check) = K + 1 := by
  simp [cellRun, acquireActs, isWait, countP_roundStream]

@[simp] lemma countP_isWait_sync_cellRun {b : Option Γ} :
    (cellRun Q Γ K b).countP (isWait SyncKind.sync) = K + 1 := by
  simp [cellRun, acquireActs, isWait, countP_roundStream]

/-- **A cell issues its requests on the `check` channel before those on the `sync` channel.**
`HTN.TMEnc.cellCheckPart` is the part of a cell up to and including the last `wait check`. -/
def cellCheckPart (Q Γ : Type) (K : ℕ) (b : Option Γ) : List (TMAct Q Γ) :=
  TMAct.assert b :: (acquireActs Q Γ SyncKind.head ++
    roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check)

/-- The part of a cell that issues the requests on the `sync` channel. -/
def cellSyncPart (Q Γ : Type) (K : ℕ) : List (TMAct Q Γ) :=
  roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync

lemma cellRun_split {b : Option Γ} :
    cellRun Q Γ K b = cellCheckPart Q Γ K b ++ cellSyncPart Q Γ K := by
  simp [cellRun, cellCheckPart, cellSyncPart, List.append_assoc]

@[simp] lemma countP_isCall_check_cellCheckPart {b : Option Γ} :
    (cellCheckPart Q Γ K b).countP (isCall SyncKind.check) = K + 1 := by
  simp [cellCheckPart, acquireActs, isCall, countP_roundStream]

@[simp] lemma countP_isWait_check_cellCheckPart {b : Option Γ} :
    (cellCheckPart Q Γ K b).countP (isWait SyncKind.check) = K + 1 := by
  simp [cellCheckPart, acquireActs, isWait, countP_roundStream]

@[simp] lemma countP_isCall_sync_cellCheckPart {b : Option Γ} :
    (cellCheckPart Q Γ K b).countP (isCall SyncKind.sync) = 0 := by
  simp [cellCheckPart, acquireActs, isCall, countP_roundStream]

@[simp] lemma countP_isWait_sync_cellCheckPart {b : Option Γ} :
    (cellCheckPart Q Γ K b).countP (isWait SyncKind.sync) = 0 := by
  simp [cellCheckPart, acquireActs, isWait, countP_roundStream]

/-! ### The whole tape stream -/

/-- The stream of the `(K+1)²` cells the tape produces. -/
def tapeStream (Q Γ : Type) (K : ℕ) (sym : ℕ → Option Γ) : List (TMAct Q Γ) :=
  roundStream ((K + 1) * (K + 1)) fun n => cellRun Q Γ K (sym n)

/-- The first `n` cells of the tape stream. -/
def tapePrefix (Q Γ : Type) (K n : ℕ) (sym : ℕ → Option Γ) : List (TMAct Q Γ) :=
  roundStream n fun m => cellRun Q Γ K (sym m)

lemma tapeStream_split {sym : ℕ → Option Γ} {n : ℕ} (hn : n ≤ (K + 1) * (K + 1)) :
    tapeStream Q Γ K sym = tapePrefix Q Γ K n sym ++
      roundStream ((K + 1) * (K + 1) - n) fun m => cellRun Q Γ K (sym (n + m)) := by
  rw [tapeStream, tapePrefix, ← roundStream_add]
  congr 1
  omega

@[simp] lemma countP_isCall_check_tapePrefix {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isCall SyncKind.check) = n * (K + 1) := by
  rw [tapePrefix, countP_roundStream]
  simp

@[simp] lemma countP_isCall_sync_tapePrefix {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isCall SyncKind.sync) = n * (K + 1) := by
  rw [tapePrefix, countP_roundStream]
  simp

@[simp] lemma countP_isWait_check_tapePrefix {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isWait SyncKind.check) = n * (K + 1) := by
  rw [tapePrefix, countP_roundStream]
  simp

@[simp] lemma countP_isWait_sync_tapePrefix {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isWait SyncKind.sync) = n * (K + 1) := by
  rw [tapePrefix, countP_roundStream]
  simp

@[simp] lemma countP_isStart_tapePrefix {x : SyncKind} {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isStart x) = 0 := by
  rw [tapePrefix, countP_roundStream]
  simp [countP_isStart_cellRun]

@[simp] lemma countP_isRespond_tapePrefix {x : SyncKind} {sym : ℕ → Option Γ} {n : ℕ} :
    (tapePrefix Q Γ K n sym).countP (isRespond x) = 0 := by
  rw [tapePrefix, countP_roundStream]
  simp [countP_isRespond_cellRun]

end TMEnc

end HTN
