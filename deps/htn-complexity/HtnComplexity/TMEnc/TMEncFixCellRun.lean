import HtnComplexity.TMEnc.CellRun
import HtnComplexity.TMEnc.TMEncFixTransCount
/-!
# A solution plan of the repaired encoding is a cell run

`HtnComplexity/TMEnc/CellRun.lean` proves that a space–time diagram read cell by cell — every
cell either copied into the next block or carrying a transition of the machine, the head sitting
on the cells that carry one — is an accepting run of as many steps as it has transition cells.
This file feeds the analysis of a solution plan of the repaired Turing-machine encoding into
that calculus.

Everything the diagram needs is available:

* the symbols are `D.sym`, the states are `HTN.TMEnc.stAt` and the transition cells are
  `HTN.TMEnc.TrCell` — the cells at which the counter that is due takes a `step` action;
* `HTN.TMEnc.cell_copy_of_not_trCell` and `HTN.TMEnc.cell_step_of_trCell` are the two halves of
  `HTN.TMEnc.cell_copy_or_step_classified`;
* the first block is the input and the last one is accepting (`SolutionPlanData.initSym`,
  `HTN.TMEnc.stAt_zero`, `HTN.TMEnc.stAt_lastBlock_eq`);
* the number of transition cells is at most `K` (`HTN.TMEnc.card_transitions_le`).

What is **not** available is the **head**: that the cell at which a transition is taken is the
cell the head of the machine is on, and that the head then moves as the transition prescribes.
That is the alignment of the head counter with the tape, and it is the one open item of the
soundness direction (see `NOTES.md`); it is carried here as the explicit hypothesis
`HTN.TMEnc.HeadAssignment`.  Modulo it, soundness of the repaired encoding is
`HTN.TMEnc.acceptsWithin_of_headAssignment` / `HTN.TMEnc.encodingSound_of_headAssignment`.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The transition cells of a plan -/

/-- **The cell `n` carries a transition with the move `mv`**: the counter that is due there
decided to apply a transition of the machine rather than to test that the head is elsewhere. -/
def TrCellWith (D : SolutionPlanData N w K) (n : ℕ) (mv : Move) : Prop :=
  ∃ (q q' : Q) (a b : Γ),
    D.P (due D n) (n / (K + 1)) = TMAct.step q (some a) q' (some b) ::
      roundStream (moveExtra mv) (fun _ => acquireActs Q Γ SyncKind.head)

/-- **The cell `n` carries a transition.** -/
def TrCell (D : SolutionPlanData N w K) (n : ℕ) : Prop := ∃ mv : Move, TrCellWith D n mv

lemma trCell_of_shape {D : SolutionPlanData N w K} {n : ℕ} {q q' : Q} {a b : Γ} {mv : Move}
    (h : D.P (due D n) (n / (K + 1)) = TMAct.step q (some a) q' (some b) ::
      roundStream (moveExtra mv) (fun _ => acquireActs Q Γ SyncKind.head)) : TrCell D n :=
  ⟨mv, q, q', a, b, h⟩

/-! #### The move of a transition cell is determined -/

private lemma length_roundStream_const {α : Type} (R : ℕ) (l : List α) :
    (roundStream R (fun _ => l)).length = R * l.length := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [roundStream_succ]
      simp only [List.length_append, ih]
      ring

private lemma moveExtra_injective {mv mv' : Move} (h : moveExtra mv = moveExtra mv') :
    mv = mv' := by
  cases mv <;> cases mv' <;> simp_all [moveExtra]

/-- **The move a transition cell performs is determined by the plan.** -/
lemma trCellWith_unique {D : SolutionPlanData N w K} {n : ℕ} {mv mv' : Move}
    (h : TrCellWith D n mv) (h' : TrCellWith D n mv') : mv = mv' := by
  obtain ⟨q, q', a, b, hP⟩ := h
  obtain ⟨q₂, q₂', a₂, b₂, hP'⟩ := h'
  rw [hP] at hP'
  have htail : roundStream (moveExtra mv) (fun _ => acquireActs Q Γ SyncKind.head)
      = roundStream (moveExtra mv') (fun _ => acquireActs Q Γ SyncKind.head) :=
    (List.cons.injEq .. ▸ hP').2
  have hlen := congrArg List.length htail
  rw [length_roundStream_const, length_roundStream_const] at hlen
  simp only [acquireActs, List.length_cons, List.length_nil] at hlen
  exact moveExtra_injective (by omega)

open Classical in
/-- The move the transition of the cell `n` performs (the junk value `stay` if the cell carries
no transition). -/
noncomputable def mvAt (D : SolutionPlanData N w K) (n : ℕ) : Move :=
  if h : TrCell D n then h.choose else Move.stay

lemma trCellWith_mvAt {D : SolutionPlanData N w K} {n : ℕ} (h : TrCell D n) :
    TrCellWith D n (mvAt D n) := by
  classical
  rw [mvAt, dif_pos h]
  exact h.choose_spec

lemma mvAt_eq {D : SolutionPlanData N w K} {n : ℕ} {mv : Move} (h : TrCellWith D n mv) :
    mvAt D n = mv :=
  trCellWith_unique (trCellWith_mvAt ⟨mv, h⟩) h

open Classical in
/-- The transition cells as a boolean predicate. -/
noncomputable def trB (D : SolutionPlanData N w K) (n : ℕ) : Bool :=
  if TrCell D n then true else false

lemma trB_eq_true_iff {D : SolutionPlanData N w K} {n : ℕ} :
    trB D n = true ↔ TrCell D n := by
  classical
  simp only [trB]
  split <;> simp_all

lemma trB_eq_false_iff {D : SolutionPlanData N w K} {n : ℕ} :
    trB D n = false ↔ ¬ TrCell D n := by
  classical
  simp only [trB]
  split <;> simp_all

/-- A cell that carries no transition is copied, and the state does not change. -/
theorem cell_copy_of_not_trCell (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    (htr : ¬ TrCell D n) :
    D.sym (n + (K + 1)) = D.sym n ∧ stAt D (n + 1) = stAt D n := by
  rcases cell_copy_or_step_classified D hu with ⟨-, h⟩ | ⟨q, q', a, b, mv, hP, -, -, -⟩
  · exact h
  · exact absurd (trCell_of_shape hP) htr

/-- A cell that carries a transition applies it: it reads the symbol of the cell, writes the new
one into the same position of the next block and changes the state. -/
theorem cell_step_of_trCell (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    (htr : TrCell D n) :
    ∃ (q q' : Q) (a b : Γ) (mv : Move),
      D.P (due D n) (n / (K + 1)) = TMAct.step q (some a) q' (some b) ::
          roundStream (moveExtra mv) (fun _ => acquireActs Q Γ SyncKind.head) ∧
        (stAt D (n + 1), b, mv) ∈ N.step (stAt D n) a ∧
        D.sym n = some a ∧ D.sym (n + (K + 1)) = some b := by
  rcases cell_copy_or_step_classified D hu with ⟨hP, -⟩ | h
  · obtain ⟨mv, q, q', a, b, hP'⟩ := htr
    rw [hP] at hP'
    exact absurd hP' (by simp)
  · exact h

/-! ### The head assignment -/

/-- **A head assignment for a solution plan**: a head position for every cell such that the head
does not move at a cell without a transition, and a transition is taken at the cell the head is
on and moves the head as it prescribes.

This is the *alignment of the head counter with the tape*.  The hierarchy of the construction and
the semaphore protocol pin it down only up to one unit of the head counter
(`HTN.TMEnc.headMark_at_decision`), which is why it is carried as a hypothesis; see `NOTES.md`. -/
structure HeadAssignment (D : SolutionPlanData N w K) (hd : ℕ → ℕ) : Prop where
  /-- The head starts on the first tape cell. -/
  init : hd 0 = 0
  /-- A cell without a transition does not move the head. -/
  copy : ∀ n < K * (K + 1), ¬ TrCell D n → hd (n + 1) = hd n
  /-- A transition is taken on the cell the head is on, and moves it as it prescribes. -/
  step : ∀ n < K * (K + 1), ∀ (q q' : Q) (a b : Γ) (mv : Move),
    D.P (due D n) (n / (K + 1)) = TMAct.step q (some a) q' (some b) ::
        roundStream (moveExtra mv) (fun _ => acquireActs Q Γ SyncKind.head) →
      n % (K + 1) = hd n + 1 ∧ hd n < K ∧ hd (n + 1) = mv.apply (hd n)

/-- A plan that takes no transition at all has a head assignment (the head never moves): the
notion is not vacuous. -/
lemma headAssignment_const_zero (D : SolutionPlanData N w K)
    (h : ∀ n < K * (K + 1), ¬ TrCell D n) : HeadAssignment D (fun _ => 0) :=
  ⟨rfl, fun _ _ _ => rfl, fun n hn _ _ _ _ _ hP =>
    absurd (trCell_of_shape hP) (h n hn)⟩

/-! #### The canonical head assignment -/

open Classical in
/-- **The head positions the transitions of a plan prescribe**: the head starts at `0` and moves
at every transition cell as that transition says. -/
noncomputable def hdOf (D : SolutionPlanData N w K) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if TrCell D n then (mvAt D n).apply (hdOf D n) else hdOf D n

@[simp] lemma hdOf_zero (D : SolutionPlanData N w K) : hdOf D 0 = 0 := rfl

lemma hdOf_succ_of_not (D : SolutionPlanData N w K) {n : ℕ} (h : ¬ TrCell D n) :
    hdOf D (n + 1) = hdOf D n := by
  classical
  rw [hdOf, if_neg h]

lemma hdOf_succ_of_trCellWith (D : SolutionPlanData N w K) {n : ℕ} {mv : Move}
    (h : TrCellWith D n mv) : hdOf D (n + 1) = mv.apply (hdOf D n) := by
  classical
  rw [hdOf, if_pos ⟨mv, h⟩, mvAt_eq h]

/-- **The one statement soundness is still missing**: at a transition cell the head of the
machine — as the transitions of the plan move it — is on that very cell.

This is the alignment of the head counter with the tape; see `NOTES.md`. -/
def HeadOnCell (D : SolutionPlanData N w K) : Prop :=
  ∀ n < K * (K + 1), TrCell D n → n % (K + 1) = hdOf D n + 1

/-- **`HeadOnCell` is all that is missing**: it turns the head positions the transitions of the
plan prescribe into a head assignment. -/
theorem headAssignment_hdOf (D : SolutionPlanData N w K) (h : HeadOnCell D) :
    HeadAssignment D (hdOf D) := by
  refine ⟨rfl, fun n _ hn => hdOf_succ_of_not D hn, ?_⟩
  intro n hn q q' a b mv hP
  have htr : TrCellWith D n mv := ⟨q, q', a, b, hP⟩
  have hpos : n % (K + 1) = hdOf D n + 1 := h n hn ⟨mv, htr⟩
  have hlt : hdOf D n < K := by
    have := Nat.mod_lt n (show 0 < K + 1 by omega)
    omega
  exact ⟨hpos, hlt, hdOf_succ_of_trCellWith D htr⟩

/-- Inside the array, a cell number below `K (K+1)` lies in a block that is not the last one. -/
lemma div_lt_of_lt_mul {n : ℕ} (hn : n < K * (K + 1)) : n / (K + 1) < K :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hn; exact hn)

/-- **A solution plan of the repaired encoding, together with a head assignment, is a cell
run.** -/
theorem isCellRun_of_planData (D : SolutionPlanData N w K) {hd : ℕ → ℕ}
    (h : HeadAssignment D hd) : IsCellRun N w K D.sym (stAt D) hd (trB D) := by
  refine ⟨?_, stAt_zero D, h.init, ?_, ?_, ?_⟩
  · intro j hj
    have := D.initSym (j + 1) (by omega)
    rw [this, tapeInitSym, if_neg (by omega)]
    simp
  · intro n hn htr
    have hu : n / (K + 1) < K := div_lt_of_lt_mul hn
    have hntr : ¬ TrCell D n := trB_eq_false_iff.1 htr
    obtain ⟨hsym, hst⟩ := cell_copy_of_not_trCell D hu hntr
    exact ⟨hsym, hst, h.copy n hn hntr⟩
  · intro n hn htr
    have hu : n / (K + 1) < K := div_lt_of_lt_mul hn
    obtain ⟨q, q', a, b, mv, hP, hmem, hsa, hsb⟩ :=
      cell_step_of_trCell D hu (trB_eq_true_iff.1 htr)
    obtain ⟨hpos, hlt, hmove⟩ := h.step n hn q q' a b mv hP
    exact ⟨a, b, mv, hmem, hsa, hsb, hpos, hlt, hmove⟩
  · rw [stAt_lastBlock_eq D]
    exact D.accept

/-! ### The number of transition cells -/

private lemma countP_range_eq_card (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (List.range m).countP (fun n => decide (p n)) =
      ((Finset.range m).filter p).card := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
      by_cases hm : p m
      · rw [if_pos hm, Finset.card_insert_of_notMem (by simp)]
        simp [hm]
      · rw [if_neg hm]
        simp [hm]

/-- **A solution plan has at most `K` transition cells.** -/
theorem countP_trB_le (D : SolutionPlanData N w K) :
    (List.range (K * (K + 1))).countP (trB D) ≤ K := by
  classical
  have hdec : (List.range (K * (K + 1))).countP (trB D)
      = (List.range (K * (K + 1))).countP (fun n => decide (TrCell D n)) := by
    refine List.countP_congr ?_
    intro n _
    by_cases hn : TrCell D n
    · simp [trB_eq_true_iff.2 hn, hn]
    · simp [trB_eq_false_iff.2 hn, hn]
  rw [hdec, countP_range_eq_card]
  refine card_transitions_le D _ ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hlt, mv, q, q', a, b, hP⟩ := hn
  have hu : n / (K + 1) < K := div_lt_of_lt_mul hlt
  have hn' : n < (K + 1) * (K + 1) := by
    have : K * (K + 1) ≤ (K + 1) * (K + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  exact ⟨hn', hu, q, q', some a, some b, _, hP⟩

/-! ### Soundness of the encoding, modulo the head assignment -/

/-- **A solution plan with a head assignment exhibits an accepting run of at most `K`
steps.** -/
theorem acceptsWithin_of_headAssignment (D : SolutionPlanData N w K) (hwK : w.length ≤ K)
    {hd : ℕ → ℕ} (h : HeadAssignment D hd) : N.AcceptsWithin w K :=
  acceptsWithin_of_isCellRun_le (isCellRun_of_planData D h) hwK (countP_trB_le D)

/-- **Soundness of the repaired encoding, modulo the alignment of the head counter.**  If every
solution plan admits a head assignment, then solvability of the encoded problem implies that the
machine accepts the input within `K` steps.

The bound `K` is the exact one: the counting of
`HtnComplexity/TMEnc/TMEncFixTransCount.lean` pins every transition to a mark of its own. -/
theorem encodingSound_of_headAssignment (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hHead : ∀ D : SolutionPlanData N w K, ∃ hd : ℕ → ℕ, HeadAssignment D hd)
    (hsol : (problemFix N w K).Solvable) : N.AcceptsWithin w K := by
  obtain ⟨as, hplan⟩ := Problem.solvable_iff_exists_solutionPlan.1 hsol
  obtain ⟨D, -⟩ := exists_planData hw hwK hplan
  obtain ⟨hd, hhd⟩ := hHead D
  exact acceptsWithin_of_headAssignment D hwK hhd

/-- **Soundness of the repaired encoding, modulo `HeadOnCell`.**  This is the sharpest form of
the reduction: the whole soundness direction now rests on the single statement that a transition
is taken on the cell the head of the machine is on. -/
theorem encodingSound_of_headOnCell (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hHead : ∀ D : SolutionPlanData N w K, HeadOnCell D)
    (hsol : (problemFix N w K).Solvable) : N.AcceptsWithin w K :=
  encodingSound_of_headAssignment hw hwK (fun D => ⟨hdOf D, headAssignment_hdOf D (hHead D)⟩) hsol

end TMEnc

end HTN
