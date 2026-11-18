import HtnComplexity.TMEnc.TMEncFixCellRun
/-!
# What the mark of the head counter decides, and how the transitions of a plan are spaced

This file sharpens the analysis of the head channel of the repaired Turing-machine encoding.
Two facts were available before:

* `HTN.TMEnc.headMark_at_decision` — the decision of the cell `n` reads the mark of the unit
  `u(n) = HTN.TMEnc.headUnitIndex D n = n + numEx D n`, and of no other; a transition needs the
  mark `true` and the test `check noHead` needs it `false`;
* `HTN.TMEnc.headUnitIndex_of_transition` — a transition therefore sits at
  `u = c (K+2) + 1` for its mark `c = HTN.TMEnc.headBlockIndex D n`.

What is added here:

* `HTN.TMEnc.trCell_iff_headMarkAt` — **a cell carries a transition exactly when the mark it
  reads is `true`**.  This uses that the two decisions are exhaustive
  (`HTN.TMEnc.cell_copy_or_step_classified`), and is the form in which the head channel really
  constrains a plan: at a cell whose mark is `true` the counter *must* step, and at one whose
  mark is `false` it *must not*;
* `HTN.TMEnc.headUnitIndex_succ_of_trCellWith` / `_of_not_trCell` — the unit index advances by
  one per cell, plus the `moveExtra` of a transition;
* `HTN.TMEnc.headUnitIndex_add_of_no_trCell_between` — hence the **spacing** of two consecutive
  transitions: `u(n + g) = u(n) + g + moveExtra (mv n)`;
* `HTN.TMEnc.eq_of_headBlockIndex_eq` — **two transitions that read the same mark are the same
  cell**: every block of the head counter carries at most one step of the machine.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### A transition is taken exactly where the mark is set -/

/-- **A cell carries a transition exactly when the mark of the head counter that its decision
reads is `true`.**

The decision of a cell is either a transition of the machine or the test `check noHead`
(`HTN.TMEnc.cell_copy_or_step_classified`); the first needs the head fact, the second needs its
negation, so the mark decides which of the two the counter takes. -/
theorem trCell_iff_headMarkAt (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K) :
    TrCell D n ↔ headMarkAt K (headUnitIndex D n) = true := by
  obtain ⟨hstep, hnoHead⟩ := headMark_at_decision D hu
  rw [show headUnitIndex D n = n + numEx D n from rfl]
  constructor
  · rintro ⟨mv, q, q', a, b, hP⟩
    exact hstep q q' (some a) (some b) _ hP
  · intro hmark
    rcases cell_copy_or_step_classified D hu with ⟨hP, -⟩ | ⟨q, q', a, b, mv, hP, -, -, -⟩
    · rw [hnoHead hP] at hmark
      exact absurd hmark (by simp)
    · exact trCell_of_shape hP

/-! ### How the unit index advances -/

/-- At a cell that carries a transition the unit index advances by one plus the extra requests
of the move. -/
lemma headUnitIndex_succ_of_trCellWith (D : SolutionPlanData N w K) {n : ℕ} {mv : Move}
    (hu : n / (K + 1) < K) (h : TrCellWith D n mv) :
    headUnitIndex D (n + 1) = headUnitIndex D n + 1 + moveExtra mv := by
  obtain ⟨q, q', a, b, hP⟩ := h
  have hcount : (D.P (due D n) (n / (K + 1))).countP (isCall SyncKind.head) = moveExtra mv := by
    rw [hP]
    simp [countP_roundStream, acquireActs, isCall]
  have := numEx_succ D n
  rw [countP_isCall_head_counterCell_due D hu, hcount] at this
  simp only [headUnitIndex, this]
  omega

/-- At a cell that carries no transition the unit index advances by exactly one. -/
lemma headUnitIndex_succ_of_not_trCell (D : SolutionPlanData N w K) {n : ℕ}
    (hu : n / (K + 1) < K) (h : ¬ TrCell D n) :
    headUnitIndex D (n + 1) = headUnitIndex D n + 1 := by
  have hP : D.P (due D n) (n / (K + 1)) = [TMAct.check TMFact.noHead] := by
    rcases cell_copy_or_step_classified D hu with ⟨hP, -⟩ | ⟨q, q', a, b, mv, hP, -, -, -⟩
    · exact hP
    · exact absurd (trCell_of_shape hP) h
  have hcount : (D.P (due D n) (n / (K + 1))).countP (isCall SyncKind.head) = 0 := by
    rw [hP]; simp [isCall]
  have := numEx_succ D n
  rw [countP_isCall_head_counterCell_due D hu, hcount] at this
  simp only [headUnitIndex, this]
  omega

/-- **The spacing of two consecutive transitions.**  If the cell `n` carries a transition and
none of the `g - 1` cells after it does, the unit index advances by `g` plus the extra requests
of the move of the transition at `n`. -/
theorem headUnitIndex_add_of_no_trCell_between (D : SolutionPlanData N w K) {n : ℕ} {mv : Move}
    (h : TrCellWith D n mv) :
    ∀ g : ℕ, 1 ≤ g → (n + g - 1) / (K + 1) < K → (∀ i, n < i → i < n + g → ¬ TrCell D i) →
      headUnitIndex D (n + g) = headUnitIndex D n + g + moveExtra mv := by
  intro g
  induction g with
  | zero => intro hg; omega
  | succ g ih =>
      intro _ hlast hno
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · have hu : n / (K + 1) < K := by simpa using hlast
        simpa using headUnitIndex_succ_of_trCellWith D hu h
      · have hlast' : (n + g - 1) / (K + 1) < K :=
          lt_of_le_of_lt (Nat.div_le_div_right (by omega)) (lt_of_le_of_lt
            (le_of_eq (rfl : (n + (g + 1) - 1) / (K + 1) = (n + (g + 1) - 1) / (K + 1))) hlast)
        have hrec : headUnitIndex D (n + g) = headUnitIndex D n + g + moveExtra mv :=
          ih hg hlast' fun i hi₁ hi₂ => hno i hi₁ (by omega)
        have hu : (n + g) / (K + 1) < K := by
          have : n + (g + 1) - 1 = n + g := by omega
          rwa [this] at hlast
        have hntr : ¬ TrCell D (n + g) := hno (n + g) (by omega) (by omega)
        have := headUnitIndex_succ_of_not_trCell D hu hntr
        rw [show n + (g + 1) = n + g + 1 by omega, this, hrec]
        omega

/-! ### Two transitions that read the same mark -/

/-- **Two transitions that read the same mark of the head counter are the same cell.**

Every block of the head counter carries at most one step of the machine: the repaired counter
pins the unit a decision reads, so the mark determines the unit and the unit determines the
cell. -/
theorem eq_of_headBlockIndex_eq (D : SolutionPlanData N w K) {n n' : ℕ}
    (hu : n / (K + 1) < K) (hu' : n' / (K + 1) < K)
    (htr : TrCell D n) (htr' : TrCell D n')
    (hc : headBlockIndex D n = headBlockIndex D n') : n = n' := by
  obtain ⟨mv, q, q', a, b, hP⟩ := htr
  obtain ⟨mv', q₂, q₂', a₂, b₂, hP'⟩ := htr'
  refine headUnitIndex_injective D ?_
  rw [headUnitIndex_of_transition D hu hP, headUnitIndex_of_transition D hu' hP', hc]

end TMEnc

end HTN
