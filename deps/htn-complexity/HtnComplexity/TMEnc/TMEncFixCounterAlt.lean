import HtnPlanning.Core.PrefixSum
import HtnComplexity.TMEnc.TMEncFixCounterCount
/-!
# One cell counter alternates between the two cell channels

`HtnComplexity/TMEnc/TMEncFixCounterCount.lean` counts *how many* requests a cell counter answers
on the `check` channel.  The lock-step argument of the soundness direction needs the matching
*prefix* statement — **a cell counter answers its requests strictly alternating between the two
channels**: it answers one request on `check`, then one on `sync`, then one on `check`, …

Formally, for every prefix `p` of the run of a cell counter

```
#start_sync p  ≤  #start_check p  ≤  #start_sync p + 1
```

(`HTN.TMEnc.countP_prefix_counterRun`).

The proof is by prefix sums of the integer weight `HTN.TMEnc.altW` (`+1` for an answer on the
`check` channel, `-1` for one on the `sync` channel), using the little theory of
`HtnPlanning/Core/PrefixSum.lean`.  This is the half of the lock-step argument that lives
inside one counter; the other half — that the tape issues the `K + 1` requests on `check` of a
cell before those on `sync` — lives in the tape.
-/

namespace HTN

variable {α : Type}

/-! ### Three small additions to the prefix-sum theory -/

/-- The weight sum of a stream is the sum of the weight sums of its rounds. -/
lemma wsum_roundStream (w : α → ℤ) (R : ℕ) (s : ℕ → List α) :
    wsum w (roundStream R s) = ∑ r ∈ Finset.range R, wsum w (s r) := by
  induction R with
  | zero => simp
  | succ R ih => rw [roundStream_succ, wsum_append, ih, Finset.sum_range_succ]

/-- A prefix-sum bound holds for a stream of rounds of weight `0` as soon as it holds for each
round. -/
lemma psumGe_roundStream {w : α → ℤ} {c : ℤ} {R : ℕ} {s : ℕ → List α} (hc : c ≤ 0)
    (hz : ∀ r < R, wsum w (s r) = 0) (h : ∀ r < R, PSumGe w c (s r)) :
    PSumGe w c (roundStream R s) := by
  induction R with
  | zero => simpa [roundStream] using PSumGe.nil (w := w) hc
  | succ R ih =>
      have hzR : wsum w (roundStream R s) = 0 := by
        rw [wsum_roundStream]
        exact Finset.sum_eq_zero fun r hr =>
          hz r (Nat.lt_succ_of_lt (Finset.mem_range.1 hr))
      rw [roundStream_succ]
      refine PSumGe.append (ih (fun r hr => hz r (by omega)) (fun r hr => h r (by omega))) ?_
      rw [hzR, sub_zero]
      exact h R (by omega)

/-- A stream of rounds of weight `0` has weight `0`. -/
lemma wsum_roundStream_of_zero {w : α → ℤ} {R : ℕ} {s : ℕ → List α}
    (hz : ∀ r < R, wsum w (s r) = 0) : wsum w (roundStream R s) = 0 := by
  rw [wsum_roundStream]
  exact Finset.sum_eq_zero fun r hr => hz r (Finset.mem_range.1 hr)

/-- `HTN.PSumGe.append` with the bound of the second part given explicitly. -/
lemma psumGe_append' {w : α → ℤ} {c c₂ : ℤ} {l₁ l₂ : List α} (h₁ : PSumGe w c l₁)
    (h₂ : PSumGe w c₂ l₂) (hc : c - wsum w l₁ ≤ c₂) : PSumGe w c (l₁ ++ l₂) :=
  PSumGe.append h₁ (h₂.mono hc)

/-- `HTN.PSumGe.cons` with the bound of the tail given explicitly. -/
lemma psumGe_cons' {w : α → ℤ} {c c₂ : ℤ} {a : α} {l : List α} (hc : c ≤ 0)
    (h : PSumGe w c₂ l) (hle : c - w a ≤ c₂) : PSumGe w c (a :: l) :=
  PSumGe.cons hc (h.mono hle)

/-- A prefix-sum bound for a two-element list. -/
lemma psumGe_pair {w : α → ℤ} {c : ℤ} (a b : α) (hc : c ≤ 0) (h1 : c ≤ w a)
    (h2 : c ≤ w a + w b) : PSumGe w c [a, b] :=
  PSumGe.cons hc (PSumGe.cons (by omega) (PSumGe.nil (by omega)))

/-- A prefix-sum bound for a four-element list. -/
lemma psumGe_quad {w : α → ℤ} {c : ℤ} (a b d e : α) (hc : c ≤ 0) (h1 : c ≤ w a)
    (h2 : c ≤ w a + w b) (h3 : c ≤ w a + w b + w d) (h4 : c ≤ w a + w b + w d + w e) :
    PSumGe w c [a, b, d, e] :=
  PSumGe.cons hc (PSumGe.cons (by omega) (PSumGe.cons (by omega)
    (PSumGe.cons (by omega) (PSumGe.nil (by omega)))))

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The weight -/

/-- The weight that counts the answers of a cell counter: `+1` for an answer on the `check`
channel, `-1` for one on the `sync` channel, `0` for every other action. -/
def altW (Q Γ : Type) : TMAct Q Γ → ℤ := fun a =>
  (if isStart SyncKind.check a then (1 : ℤ) else 0) -
    (if isStart SyncKind.sync a then (1 : ℤ) else 0)

/-- The negation of `HTN.TMEnc.altW`; a lower bound for it is an upper bound for `altW`. -/
def altW' (Q Γ : Type) : TMAct Q Γ → ℤ := fun a => - altW Q Γ a

@[simp] lemma altW'_eq (a : TMAct Q Γ) : altW' Q Γ a = - altW Q Γ a := rfl

lemma wsum_altW (l : List (TMAct Q Γ)) :
    wsum (altW Q Γ) l =
      (l.countP (isStart SyncKind.check) : ℤ) - (l.countP (isStart SyncKind.sync) : ℤ) :=
  sum_map_eq_countP_sub (fun _ => rfl) l

@[simp] lemma wsum_altW'_eq_neg (l : List (TMAct Q Γ)) :
    wsum (altW' Q Γ) l = - wsum (altW Q Γ) l := by
  induction l with
  | nil => simp
  | cons a l ih => rw [wsum_cons, wsum_cons, ih, altW'_eq]; ring

lemma wsum_altW' (l : List (TMAct Q Γ)) :
    wsum (altW' Q Γ) l =
      (l.countP (isStart SyncKind.sync) : ℤ) - (l.countP (isStart SyncKind.check) : ℤ) := by
  rw [wsum_altW'_eq_neg, wsum_altW]
  ring

@[simp] lemma altW_start_check : altW Q Γ (TMAct.start SyncKind.check) = 1 := by
  simp [altW, isStart]

@[simp] lemma altW_start_sync : altW Q Γ (TMAct.start SyncKind.sync) = -1 := by
  simp [altW, isStart]

@[simp] lemma altW_start_head : altW Q Γ (TMAct.start SyncKind.head) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_respond (x : SyncKind) : altW Q Γ (TMAct.respond x) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_call (x : SyncKind) : altW Q Γ (TMAct.call x) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_wait (x : SyncKind) : altW Q Γ (TMAct.wait x) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_assert (c : Option Γ) : altW Q Γ (TMAct.assert c) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_check (f : TMFact Q Γ) : altW Q Γ (TMAct.check f) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_chkAct (c : Option Γ) : altW Q Γ (chkAct Q Γ c) = 0 := by
  simp [chkAct]

@[simp] lemma altW_assertHead : altW Q Γ (TMAct.assertHead : TMAct Q Γ) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_retractHead : altW Q Γ (TMAct.retractHead : TMAct Q Γ) = 0 := by
  simp [altW, isStart]

@[simp] lemma altW_step (q q' : Q) (c c' : Option Γ) : altW Q Γ (TMAct.step q c q' c') = 0 := by
  simp [altW, isStart]

/-! ### The blocks of a counter run -/

@[simp] lemma wsum_altW_waitCellActs : wsum (altW Q Γ) (waitCellActs Q Γ) = 0 := by
  simp [waitCellActs, wsum]

@[simp] lemma wsum_altW_relCheckActs : wsum (altW Q Γ) (relCheckActs Q Γ) = 1 := by
  simp [relCheckActs, wsum]

@[simp] lemma wsum_altW_relSyncActs : wsum (altW Q Γ) (relSyncActs Q Γ) = -1 := by
  simp [relSyncActs, wsum]

lemma psumGe_altW_waitCellActs : PSumGe (altW Q Γ) 0 (waitCellActs Q Γ) :=
  psumGe_quad _ _ _ _ le_rfl (by simp) (by simp) (by simp) (by simp)

lemma psumGe_altW'_waitCellActs : PSumGe (altW' Q Γ) (-1) (waitCellActs Q Γ) :=
  psumGe_quad _ _ _ _ (by norm_num) (by simp) (by simp) (by simp) (by simp)

lemma psumGe_altW_relCheckActs : PSumGe (altW Q Γ) 0 (relCheckActs Q Γ) :=
  psumGe_pair _ _ le_rfl (by simp) (by simp)

lemma psumGe_altW'_relCheckActs : PSumGe (altW' Q Γ) (-1) (relCheckActs Q Γ) :=
  psumGe_pair _ _ (by norm_num) (by simp) (by simp)

lemma psumGe_altW_relSyncActs : PSumGe (altW Q Γ) (-1) (relSyncActs Q Γ) :=
  psumGe_pair _ _ (by norm_num) (by simp) (by simp)

lemma psumGe_altW'_relSyncActs : PSumGe (altW' Q Γ) 0 (relSyncActs Q Γ) :=
  psumGe_pair _ _ le_rfl (by simp) (by simp)

@[simp] lemma wsum_altW_chkRun (c : Option Γ) : wsum (altW Q Γ) (chkRun Q Γ K c) = 0 := by
  rw [chkRun, wsum_cons, wsum_append, wsum_append, wsum_append,
    wsum_roundStream_of_zero (fun _ _ => wsum_altW_waitCellActs)]
  simp

lemma psumGe_altW_chkRun (c : Option Γ) : PSumGe (altW Q Γ) (-1) (chkRun Q Γ K c) :=
  psumGe_cons' (by norm_num)
    (psumGe_append' (psumGe_altW_relSyncActs (Q := Q) (Γ := Γ))
      (psumGe_append'
        (psumGe_roundStream (w := altW Q Γ) (c := 0) le_rfl
          (fun _ _ => wsum_altW_waitCellActs) (fun _ _ => psumGe_altW_waitCellActs))
        (psumGe_append' (psumGe_altW_relCheckActs (Q := Q) (Γ := Γ))
          (psumGe_cons' (w := altW Q Γ) (c := -1) (by norm_num) (PSumGe.nil (w := altW Q Γ) (c := -1)
            (by norm_num)) (by simp)) (by simp))
        (by rw [wsum_roundStream_of_zero (fun _ _ => wsum_altW_waitCellActs)]; simp))
      (by simp)) (by simp)

lemma psumGe_altW'_chkRun (c : Option Γ) : PSumGe (altW' Q Γ) 0 (chkRun Q Γ K c) :=
  psumGe_cons' le_rfl
    (psumGe_append' (psumGe_altW'_relSyncActs (Q := Q) (Γ := Γ))
      (psumGe_append'
        (psumGe_roundStream (w := altW' Q Γ) (c := -1) (by norm_num)
          (fun _ _ => by simp) (fun _ _ => psumGe_altW'_waitCellActs))
        (psumGe_append' (psumGe_altW'_relCheckActs (Q := Q) (Γ := Γ))
          (psumGe_cons' (w := altW' Q Γ) (c := 0) le_rfl (PSumGe.nil (w := altW' Q Γ) (c := 0) le_rfl)
            (by simp)) (by simp))
        (by rw [wsum_roundStream_of_zero (fun _ _ => by simp : ∀ r < K,
            wsum (altW' Q Γ) (waitCellActs Q Γ) = 0)]; simp))
      (by simp)) (by simp)

/-- A decision of a counter is invisible to the two cell channels. -/
lemma altW_eq_zero_of_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    ∀ a ∈ p, altW Q Γ a = 0 := by
  rcases stepDecision_iff.1 h with ⟨q, q', c, c', m, -, rfl⟩ | rfl
  · intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · simp
    · have hmem : a ∈ roundStream (moveExtra m) fun _ => acquireActs Q Γ SyncKind.head := ha
      rw [roundStream, List.mem_flatten] at hmem
      obtain ⟨l, hl, hal⟩ := hmem
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hl
      have : a = TMAct.call SyncKind.head ∨ a = TMAct.wait SyncKind.head := by
        simpa [acquireActs] using hal
      rcases this with rfl | rfl <;> simp
  · intro a ha
    have : a = TMAct.check (TMFact.noHead : TMFact Q Γ) := by simpa using ha
    subst this
    simp

lemma altW'_eq_zero_of_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    ∀ a ∈ p, altW' Q Γ a = 0 := by
  intro a ha
  rw [altW'_eq, altW_eq_zero_of_stepDecision h a ha, neg_zero]

/-! ### The run of one counter -/

lemma wsum_altW_decision_chk {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    ∀ r < K, wsum (altW Q Γ) (P r ++ chkRun Q Γ K (c r)) = 0 := by
  intro r hr
  rw [wsum_append, wsum_eq_zero_of_weights_zero (altW_eq_zero_of_stepDecision (hP r hr)),
    wsum_altW_chkRun, add_zero]

lemma wsum_altW_counterBody {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    wsum (altW Q Γ) (counterBody Q Γ K P c) = 0 := by
  rw [counterBody, wsum_append, wsum_append,
    wsum_roundStream_of_zero (wsum_altW_decision_chk hP)]
  simp

lemma psumGe_altW_counterBody {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    PSumGe (altW Q Γ) 0 (counterBody Q Γ K P c) := by
  rw [counterBody]
  refine psumGe_append' (psumGe_altW_relCheckActs (Q := Q) (Γ := Γ))
    (psumGe_append'
      (psumGe_roundStream (w := altW Q Γ) (c := -1) (by norm_num) (wsum_altW_decision_chk hP)
        (fun r hr => PSumGe.append_zero (altW_eq_zero_of_stepDecision (hP r hr))
          (psumGe_altW_chkRun _)))
      (psumGe_altW_relSyncActs (Q := Q) (Γ := Γ)) ?_) (by simp)
  rw [wsum_roundStream_of_zero (wsum_altW_decision_chk hP)]
  simp

lemma psumGe_altW'_counterBody {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    PSumGe (altW' Q Γ) (-1) (counterBody Q Γ K P c) := by
  have hz : ∀ r < K, wsum (altW' Q Γ) (P r ++ chkRun Q Γ K (c r)) = 0 := by
    intro r hr
    rw [wsum_altW'_eq_neg, wsum_altW_decision_chk hP r hr, neg_zero]
  rw [counterBody]
  refine psumGe_append' (psumGe_altW'_relCheckActs (Q := Q) (Γ := Γ))
    (psumGe_append'
      (psumGe_roundStream (w := altW' Q Γ) (c := 0) le_rfl hz
        (fun r hr => PSumGe.append_zero (altW'_eq_zero_of_stepDecision (hP r hr))
          (psumGe_altW'_chkRun _)))
      (psumGe_altW'_relSyncActs (Q := Q) (Γ := Γ)) ?_) (by simp)
  rw [wsum_roundStream_of_zero hz]
  simp

/-- **A cell counter never answers a request on the `sync` channel before the request on the
`check` channel of the same cell.** -/
theorem psumGe_altW_counterRun {d e : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    PSumGe (altW Q Γ) 0 (counterRun Q Γ K d e P c) := by
  rw [counterRun]
  refine psumGe_append'
    (psumGe_roundStream (w := altW Q Γ) (c := 0) le_rfl (fun _ _ => wsum_altW_waitCellActs)
      (fun _ _ => psumGe_altW_waitCellActs))
    (psumGe_append' (psumGe_altW_counterBody hP)
      (psumGe_roundStream (w := altW Q Γ) (c := 0) le_rfl (fun _ _ => wsum_altW_waitCellActs)
        (fun _ _ => psumGe_altW_waitCellActs)) ?_) ?_
  · rw [wsum_altW_counterBody hP]; simp
  · rw [wsum_roundStream_of_zero (fun _ _ => wsum_altW_waitCellActs)]; simp

/-- **A cell counter never answers two requests on the `check` channel without answering the
request on the `sync` channel in between.** -/
theorem psumGe_altW'_counterRun {d e : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    PSumGe (altW' Q Γ) (-1) (counterRun Q Γ K d e P c) := by
  have hz : ∀ r < d + e + K + 1, wsum (altW' Q Γ) (waitCellActs Q Γ) = 0 := fun _ _ => by simp
  rw [counterRun]
  refine psumGe_append'
    (psumGe_roundStream (w := altW' Q Γ) (c := -1) (by norm_num) (fun r _ => hz r (by omega))
      (fun _ _ => psumGe_altW'_waitCellActs))
    (psumGe_append' (psumGe_altW'_counterBody hP)
      (psumGe_roundStream (w := altW' Q Γ) (c := -1) (by norm_num) (fun r _ => hz r (by omega))
        (fun _ _ => psumGe_altW'_waitCellActs)) ?_) ?_
  · rw [wsum_altW'_eq_neg, wsum_altW_counterBody hP]; simp
  · rw [wsum_roundStream_of_zero (fun r _ => hz r (by omega))]; simp

/-- **The two cell channels of a cell counter alternate**: in every prefix of its run the counter
has answered as many requests on the `check` channel as on the `sync` channel, or one more. -/
theorem countP_prefix_counterRun {d e : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) {p : List (TMAct Q Γ)}
    (hp : p <+: counterRun Q Γ K d e P c) :
    p.countP (isStart SyncKind.sync) ≤ p.countP (isStart SyncKind.check) ∧
      p.countP (isStart SyncKind.check) ≤ p.countP (isStart SyncKind.sync) + 1 := by
  have h₁ := psumGe_altW_counterRun (N := N) (w := w) (d := d) (e := e) (c := c) hP p hp
  have h₂ := psumGe_altW'_counterRun (N := N) (w := w) (d := d) (e := e) (c := c) hP p hp
  rw [wsum_altW] at h₁
  rw [wsum_altW'] at h₂
  omega

/-! ### A counter answers a request before it is asked the next one

The second prefix statement the lock-step argument needs is that inside a counter the `respond`
of a handshake immediately follows its `start`: in every prefix of the run of a counter the
number of `respond x` is at most the number of `start x`. -/

/-- The weight that compares the two halves of the answers a counter gives on the channel `x`. -/
def hsW (Q Γ : Type) (x : SyncKind) : TMAct Q Γ → ℤ := fun a =>
  (if isStart x a then (1 : ℤ) else 0) - (if isRespond x a then (1 : ℤ) else 0)

lemma wsum_hsW (x : SyncKind) (l : List (TMAct Q Γ)) :
    wsum (hsW Q Γ x) l = (l.countP (isStart x) : ℤ) - (l.countP (isRespond x) : ℤ) :=
  sum_map_eq_countP_sub (fun _ => rfl) l

@[simp] lemma wsum_hsW_waitCellActs (x : SyncKind) :
    wsum (hsW Q Γ x) (waitCellActs Q Γ) = 0 := by
  cases x <;> simp [waitCellActs, wsum, hsW, isStart, isRespond]

@[simp] lemma wsum_hsW_relCheckActs (x : SyncKind) :
    wsum (hsW Q Γ x) (relCheckActs Q Γ) = 0 := by
  cases x <;> simp [relCheckActs, wsum, hsW, isStart, isRespond]

@[simp] lemma wsum_hsW_relSyncActs (x : SyncKind) :
    wsum (hsW Q Γ x) (relSyncActs Q Γ) = 0 := by
  cases x <;> simp [relSyncActs, wsum, hsW, isStart, isRespond]

lemma psumGe_hsW_waitCellActs (x : SyncKind) : PSumGe (hsW Q Γ x) 0 (waitCellActs Q Γ) :=
  psumGe_quad _ _ _ _ le_rfl (by cases x <;> simp [hsW, isStart, isRespond])
    (by cases x <;> simp [hsW, isStart, isRespond])
    (by cases x <;> simp [hsW, isStart, isRespond])
    (by cases x <;> simp [hsW, isStart, isRespond])

lemma psumGe_hsW_relCheckActs (x : SyncKind) : PSumGe (hsW Q Γ x) 0 (relCheckActs Q Γ) :=
  psumGe_pair _ _ le_rfl (by cases x <;> simp [hsW, isStart, isRespond])
    (by cases x <;> simp [hsW, isStart, isRespond])

lemma psumGe_hsW_relSyncActs (x : SyncKind) : PSumGe (hsW Q Γ x) 0 (relSyncActs Q Γ) :=
  psumGe_pair _ _ le_rfl (by cases x <;> simp [hsW, isStart, isRespond])
    (by cases x <;> simp [hsW, isStart, isRespond])

@[simp] lemma wsum_hsW_chkRun (x : SyncKind) (c : Option Γ) :
    wsum (hsW Q Γ x) (chkRun Q Γ K c) = 0 := by
  rw [chkRun, wsum_cons, wsum_append, wsum_append, wsum_append,
    wsum_roundStream_of_zero (fun _ _ => wsum_hsW_waitCellActs x)]
  cases x <;> simp [chkAct, hsW, isStart, isRespond]

lemma psumGe_hsW_chkRun (x : SyncKind) (c : Option Γ) :
    PSumGe (hsW Q Γ x) 0 (chkRun Q Γ K c) :=
  psumGe_cons' le_rfl
    (psumGe_append' (psumGe_hsW_relSyncActs (Q := Q) (Γ := Γ) x)
      (psumGe_append'
        (psumGe_roundStream (w := hsW Q Γ x) (c := 0) le_rfl
          (fun _ _ => wsum_hsW_waitCellActs x) (fun _ _ => psumGe_hsW_waitCellActs x))
        (psumGe_append' (psumGe_hsW_relCheckActs (Q := Q) (Γ := Γ) x)
          (psumGe_cons' (w := hsW Q Γ x) (c := 0) le_rfl
            (PSumGe.nil (w := hsW Q Γ x) (c := 0) le_rfl)
            (by cases x <;> simp [chkAct, hsW, isStart, isRespond])) (by simp))
        (by rw [wsum_roundStream_of_zero (fun _ _ => wsum_hsW_waitCellActs x)]; simp))
      (by simp)) (by cases x <;> simp [chkAct, hsW, isStart, isRespond])

lemma hsW_eq_zero_of_stepDecision (x : SyncKind) {p : List (TMAct Q Γ)}
    (h : StepDecision N w K p) : ∀ a ∈ p, hsW Q Γ x a = 0 := by
  rcases stepDecision_iff.1 h with ⟨q, q', c, c', m, -, rfl⟩ | rfl
  · intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · cases x <;> simp [hsW, isStart, isRespond]
    · have hmem : a ∈ roundStream (moveExtra m) fun _ => acquireActs Q Γ SyncKind.head := ha
      rw [roundStream, List.mem_flatten] at hmem
      obtain ⟨l, hl, hal⟩ := hmem
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hl
      have : a = TMAct.call SyncKind.head ∨ a = TMAct.wait SyncKind.head := by
        simpa [acquireActs] using hal
      rcases this with rfl | rfl <;> cases x <;> simp [hsW, isStart, isRespond]
  · intro a ha
    have : a = TMAct.check (TMFact.noHead : TMFact Q Γ) := by simpa using ha
    subst this
    cases x <;> simp [hsW, isStart, isRespond]

lemma wsum_hsW_decision_chk (x : SyncKind) {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    ∀ r < K, wsum (hsW Q Γ x) (P r ++ chkRun Q Γ K (c r)) = 0 := by
  intro r hr
  rw [wsum_append, wsum_eq_zero_of_weights_zero (hsW_eq_zero_of_stepDecision x (hP r hr)),
    wsum_hsW_chkRun, add_zero]

lemma wsum_hsW_counterBody (x : SyncKind) {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    wsum (hsW Q Γ x) (counterBody Q Γ K P c) = 0 := by
  rw [counterBody, wsum_append, wsum_append,
    wsum_roundStream_of_zero (wsum_hsW_decision_chk x hP)]
  simp

lemma psumGe_hsW_counterBody (x : SyncKind) {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) :
    PSumGe (hsW Q Γ x) 0 (counterBody Q Γ K P c) := by
  rw [counterBody]
  refine psumGe_append' (psumGe_hsW_relCheckActs (Q := Q) (Γ := Γ) x)
    (psumGe_append'
      (psumGe_roundStream (w := hsW Q Γ x) (c := 0) le_rfl (wsum_hsW_decision_chk x hP)
        (fun r hr => PSumGe.append_zero (hsW_eq_zero_of_stepDecision x (hP r hr))
          (psumGe_hsW_chkRun x _)))
      (psumGe_hsW_relSyncActs (Q := Q) (Γ := Γ) x) ?_) (by simp)
  rw [wsum_roundStream_of_zero (wsum_hsW_decision_chk x hP)]
  simp

/-- **A counter never gives the second half of an answer before the first.** -/
theorem psumGe_hsW_counterRun (x : SyncKind) {d e : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) :
    PSumGe (hsW Q Γ x) 0 (counterRun Q Γ K d e P c) := by
  rw [counterRun]
  refine psumGe_append'
    (psumGe_roundStream (w := hsW Q Γ x) (c := 0) le_rfl (fun _ _ => wsum_hsW_waitCellActs x)
      (fun _ _ => psumGe_hsW_waitCellActs x))
    (psumGe_append' (psumGe_hsW_counterBody x hP)
      (psumGe_roundStream (w := hsW Q Γ x) (c := 0) le_rfl (fun _ _ => wsum_hsW_waitCellActs x)
        (fun _ _ => psumGe_hsW_waitCellActs x)) ?_) ?_
  · rw [wsum_hsW_counterBody x hP]; simp
  · rw [wsum_roundStream_of_zero (fun _ _ => wsum_hsW_waitCellActs x)]; simp

/-- **In every prefix of the run of a cell counter, every answer that has been given has been
started.** -/
theorem countP_isRespond_le_isStart_counterRun (x : SyncKind) {d e : ℕ}
    {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t))
    {p : List (TMAct Q Γ)} (hp : p <+: counterRun Q Γ K d e P c) :
    p.countP (isRespond x) ≤ p.countP (isStart x) := by
  have h := psumGe_hsW_counterRun (N := N) (w := w) (d := d) (e := e) (c := c) x hP p hp
  rw [wsum_hsW] at h
  omega

end TMEnc

end HTN
