import HtnComplexity.TMEnc.TMEncFixHeadBlock
/-!
# The global count of the channel `head`

The alignment of the head counter with the cells of the tape
(`HTN.TMEnc.headMark_at_decision`) reads off *local* information: at the decision of the cell `n`
the head counter has toggled `n + numEx D n` units, or one more.  This file adds the *global*
count, which pins down the total number of extra requests a solution plan may issue.

Over the whole plan:

* the tape issues one request on `head` per produced cell, so `(K+1)²` in all, and the cell
  counters issue `numEx D ((K+1)²)` extra ones — the `moveExtra` of the transitions taken;
* the head counter consumes one request per unit, so `K² + 3K + 1` in all, and answers one more
  than that (the prologue answers the request of the first cell without running a unit).

The two semaphores of the channel then give

`HTN.TMEnc.numEx_total_bounds` — **`K ≤ numEx D ((K+1)²) ≤ K + 1`.**

In the intended plan the value is exactly `K`: the `K` transitions of a run that starts and ends
with the head at the left end issue `K` extra requests in total
(`HTN.TMEnc.sum_moveExtra_eq`).
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The three streams of a solution plan -/

/-- The decomposition of a solution plan into its three streams. -/
lemma planInter_of_planData (D : SolutionPlanData N w K) :
    PlanInter D.ass (headStream Q Γ K) (tapeStream Q Γ K D.sym) D.as₁ :=
  ⟨D.ac, D.bs, D.hil, D.hac, D.hbs⟩

/-- Each cell counter of a solution plan is the stream of its `(K+1)²` cells. -/
lemma runs_roundStream (D : SolutionPlanData N w K) (j : ℕ) (hj : j < D.ass.length) :
    D.ass[j] = roundStream ((K + 1) * (K + 1))
      (counterCell Q Γ K (D.d j) (D.P j) (D.cc j)) := by
  have hj' : j < K + 1 := by rw [← D.card]; exact hj
  rw [D.runs j hj]
  exact counterRun_eq_roundStream (Nat.add_sub_cancel' (D.dle j hj'))

/-- **Counting an action of the channel `head` over a whole solution plan.** -/
lemma countP_as₁ (D : SolutionPlanData N w K) (f : TMAct Q Γ → Bool) :
    D.as₁.countP f = (headStream Q Γ K).countP f +
      ((∑ j ∈ Finset.range (K + 1), (roundStream ((K + 1) * (K + 1))
          (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP f) +
        (tapeStream Q Γ K D.sym).countP f) := by
  rw [countP_of_planInter (planInter_of_planData D) f,
    sum_parts_countP D D.card (runs_roundStream D) f]

/-! ### The counts of the stream of the head counter -/

lemma countP_headUnitActs_isStart (b : Bool) :
    (headUnitActs Q Γ b).countP (isStart SyncKind.head) = 1 := by
  cases b <;> simp [headUnitActs, isStart]

lemma countP_headUnitActs_isRespond (b : Bool) :
    (headUnitActs Q Γ b).countP (isRespond SyncKind.head) = 1 := by
  cases b <;> simp [headUnitActs, isRespond]

lemma countP_headUnitActs_isCall (b : Bool) :
    (headUnitActs Q Γ b).countP (isCall SyncKind.head) = 0 := by
  cases b <;> simp [headUnitActs, isCall]

lemma countP_headUnitActs_isWait (b : Bool) :
    (headUnitActs Q Γ b).countP (isWait SyncKind.head) = 0 := by
  cases b <;> simp [headUnitActs, isWait]

/-- The head counter consumes one request per unit. -/
lemma countP_isStart_head_headStream :
    (headStream Q Γ K).countP (isStart SyncKind.head) = K * K + 3 * K + 1 := by
  rw [headStream]
  simp only [countP_roundStream]
  rw [Finset.sum_congr rfl fun u _ => countP_headUnitActs_isStart (Q := Q) (Γ := Γ)
    (headMarkStd K u)]
  simp

/-- The head counter answers one request per unit. -/
lemma countP_isRespond_head_headStream :
    (headStream Q Γ K).countP (isRespond SyncKind.head) = K * K + 3 * K + 1 := by
  rw [headStream]
  simp only [countP_roundStream]
  rw [Finset.sum_congr rfl fun u _ => countP_headUnitActs_isRespond (Q := Q) (Γ := Γ)
    (headMarkStd K u)]
  simp

/-- The head counter issues no request on its own channel. -/
lemma countP_isCall_head_headStream :
    (headStream Q Γ K).countP (isCall SyncKind.head) = 0 := by
  rw [headStream]
  simp only [countP_roundStream]
  rw [Finset.sum_congr rfl fun u _ => countP_headUnitActs_isCall (Q := Q) (Γ := Γ)
    (headMarkStd K u)]
  simp

lemma countP_isWait_head_headStream :
    (headStream Q Γ K).countP (isWait SyncKind.head) = 0 := by
  rw [headStream]
  simp only [countP_roundStream]
  rw [Finset.sum_congr rfl fun u _ => countP_headUnitActs_isWait (Q := Q) (Γ := Γ)
    (headMarkStd K u)]
  simp

/-! ### The counts of the whole plan -/

/-- **A solution plan issues `(K+1)² + numEx D ((K+1)²)` requests on the `head` channel**: one
per produced cell, plus the extra ones of the transitions. -/
theorem countP_isCall_head_as₁ (D : SolutionPlanData N w K) :
    D.as₁.countP (isCall SyncKind.head) =
      (K + 1) * (K + 1) + numEx D ((K + 1) * (K + 1)) := by
  rw [countP_as₁ D, countP_isCall_head_headStream,
    show (tapeStream Q Γ K D.sym) = tapePrefix Q Γ K ((K + 1) * (K + 1)) D.sym from rfl,
    countP_isCall_head_tapePrefix]
  rw [numEx]
  omega

/-- Every request on the `head` channel is waited for. -/
theorem countP_isWait_head_as₁ (D : SolutionPlanData N w K) :
    D.as₁.countP (isWait SyncKind.head) =
      (K + 1) * (K + 1) + numEx D ((K + 1) * (K + 1)) := by
  have hdec : ∀ j < K + 1, ∀ t < K, StepDecision N w K (D.P j t) := fun j hj => D.decisions j hj
  rw [countP_as₁ D, countP_isWait_head_headStream,
    show (tapeStream Q Γ K D.sym) = tapePrefix Q Γ K ((K + 1) * (K + 1)) D.sym from rfl,
    countP_isWait_head_tapePrefix]
  rw [Finset.sum_congr rfl fun j hj => countP_isWait_head_roundStream_counterCell
    (N := N) (w := w) (hdec j (Finset.mem_range.1 hj)) ((K + 1) * (K + 1)), numEx]
  omega

theorem countP_isStart_head_as₁ (D : SolutionPlanData N w K) :
    D.as₁.countP (isStart SyncKind.head) = K * K + 3 * K + 1 := by
  have hdec : ∀ j < K + 1, ∀ t < K, StepDecision N w K (D.P j t) := fun j hj => D.decisions j hj
  rw [countP_as₁ D, countP_isStart_head_headStream,
    show (tapeStream Q Γ K D.sym) = tapePrefix Q Γ K ((K + 1) * (K + 1)) D.sym from rfl]
  rw [Finset.sum_congr rfl fun j hj => (countP_head_roundStream_counterCell
    (N := N) (w := w) (hdec j (Finset.mem_range.1 hj)) ((K + 1) * (K + 1))).1]
  simp [tapePrefix, countP_roundStream, cellRun, isStart, acquireActs]

theorem countP_isRespond_head_as₁ (D : SolutionPlanData N w K) :
    D.as₁.countP (isRespond SyncKind.head) = K * K + 3 * K + 1 := by
  have hdec : ∀ j < K + 1, ∀ t < K, StepDecision N w K (D.P j t) := fun j hj => D.decisions j hj
  rw [countP_as₁ D, countP_isRespond_head_headStream,
    show (tapeStream Q Γ K D.sym) = tapePrefix Q Γ K ((K + 1) * (K + 1)) D.sym from rfl]
  rw [Finset.sum_congr rfl fun j hj => (countP_head_roundStream_counterCell
    (N := N) (w := w) (hdec j (Finset.mem_range.1 hj)) ((K + 1) * (K + 1))).2]
  simp [tapePrefix, countP_roundStream, cellRun, isRespond, acquireActs]

/-- A solution plan without its final accepting test is executable in the initial state. -/
lemma seqApplicable_as₁ (D : SolutionPlanData N w K) :
    (problemFix N w K).SeqApplicable D.as₁ (problemFix N w K).init :=
  ((ActionModel.seqApplicable_append _ _ _ _).1
    (Problem.isSolutionPlan_iff.1 D.isPlan).2.1).1

/-- **The total number of extra requests of a solution plan is exactly `K`.**

The repaired head counter has `K² + 3K + 1` units, each of which consumes one request and answers
exactly one; the tape issues `(K+1)²` requests and the transitions the remaining
`numEx D ((K+1)²)`.  The two semaphores of the channel therefore pin the extra requests to `K`. -/
theorem numEx_total_eq (D : SolutionPlanData N w K) :
    numEx D ((K + 1) * (K + 1)) = K := by
  have happ := seqApplicable_as₁ D
  have hsem₁ := countP_start_le_countP_call (Q := Q) (Γ := Γ) SyncKind.head
    (stepF_not_mem_initFix (N := N) (w := w) (K := K) SyncKind.head) happ
  have hsem₂ := countP_wait_le_countP_respond (Q := Q) (Γ := Γ) SyncKind.head
    (steppedF_not_mem_initFix (N := N) (w := w) (K := K) SyncKind.head) happ
  rw [countP_isStart_head_as₁ D, countP_isCall_head_as₁ D] at hsem₁
  rw [countP_isWait_head_as₁ D, countP_isRespond_head_as₁ D] at hsem₂
  set E := numEx D ((K + 1) * (K + 1))
  have hexp : (K + 1) * (K + 1) = K * K + 2 * K + 1 := by ring
  rw [hexp] at hsem₁ hsem₂
  omega

end TMEnc

end HTN
