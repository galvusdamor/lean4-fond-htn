import HtnComplexity.TMEnc.TMEncFixHeadFact
import HtnComplexity.TMEnc.TMEncFixStCell
/-!
# The head fact of a prefix of a plan is the mark of the last unit of the head counter

Only the head counter toggles the facts `head` and `noHead`
(`HtnComplexity/TMEnc/TMEncFixHeadFact.lean`), and the stream of the head counter is *fixed* by
the hierarchy: it retracts the head once, and then runs `K² + 3K + 1` units, the unit `u`
reporting the head as present exactly when `HTN.TMEnc.headMarkStd K u` is true.  Hence the head
fact at a point of a solution plan depends on **one number only** — how many units of the head
counter have run:

* `HTN.TMEnc.headTog` — the two actions that toggle the head facts;
* `HTN.TMEnc.filter_headTog_headStream` — the toggles of the head counter, in order;
* `HTN.TMEnc.lastHeadF_prefix_headStream` — **the head fact after a prefix of the head counter is
  the mark of its last unit**;
* `HTN.TMEnc.lastHeadF_of_isPlanSplit` — **the head fact after a prefix of a solution plan is the
  head fact after the part of the head counter that the prefix has executed**.

What is still missing for the head half of the soundness argument is the *alignment*: how many
units of the head counter have run when the tape has written its `n`-th cell.  See `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The actions that toggle the head facts -/

/-- The two actions that toggle the facts `head` and `noHead`. -/
def headTog : TMAct Q Γ → Bool
  | .assertHead => true
  | .retractHead => true
  | _ => false

/-- The action of a unit of the head counter with the mark `b`. -/
def togAct (Q Γ : Type) (b : Bool) : TMAct Q Γ :=
  if b then TMAct.assertHead else TMAct.retractHead

@[simp] lemma headTog_togAct (b : Bool) : headTog (togAct Q Γ b) = true := by
  cases b <;> rfl

lemma stepHeadF_of_not_headTog {a : TMAct Q Γ} (ha : headTog a = false) (b : Option Bool) :
    stepHeadF b a = b := by
  cases a <;> simp_all [headTog, stepHeadF]

/-- **The head fact depends only on the actions that toggle it.** -/
lemma lastHeadF_filter (b : Option Bool) : ∀ l : List (TMAct Q Γ),
    lastHeadF b (l.filter headTog) = lastHeadF b l := by
  intro l
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : headTog a
      · rw [List.filter_cons_of_pos ha, lastHeadF_cons, lastHeadF_cons, ih]
      · simp only [Bool.not_eq_true] at ha
        rw [List.filter_cons_of_neg (by simp [ha]), ih, lastHeadF_cons,
          stepHeadF_of_not_headTog ha]

/-! ### Filtering the streams -/

lemma filter_roundStream (g : TMAct Q Γ → Bool) (s : ℕ → List (TMAct Q Γ)) : ∀ R : ℕ,
    (roundStream R s).filter g = roundStream R fun r => (s r).filter g := by
  intro R
  induction R with
  | zero => simp
  | succ R ih => rw [roundStream_succ, List.filter_append, ih, roundStream_succ]

lemma roundStream_nil (R : ℕ) : (roundStream R fun _ => ([] : List (TMAct Q Γ))) = [] := by
  induction R with
  | zero => rfl
  | succ R ih => rw [roundStream_succ, ih]; rfl

lemma roundStream_singleton (f : ℕ → TMAct Q Γ) : ∀ R : ℕ,
    (roundStream R fun u => [f u]) = (List.range R).map f := by
  intro R
  induction R with
  | zero => rfl
  | succ R ih => rw [roundStream_succ, ih, List.range_succ, List.map_append]; rfl

@[simp] lemma filter_headTog_waitCellActs : (waitCellActs Q Γ).filter headTog = [] := by
  simp [waitCellActs, headTog]

@[simp] lemma filter_headTog_relCheckActs : (relCheckActs Q Γ).filter headTog = [] := by
  simp [relCheckActs, headTog]

@[simp] lemma filter_headTog_relSyncActs : (relSyncActs Q Γ).filter headTog = [] := by
  simp [relSyncActs, headTog]

@[simp] lemma headTog_chkAct (c : Option Γ) : headTog (chkAct Q Γ c) = false := rfl

@[simp] lemma filter_headTog_acquireActs (x : SyncKind) :
    (acquireActs Q Γ x).filter headTog = [] := by
  simp [acquireActs, headTog]

@[simp] lemma filter_headTog_cellTail : (cellTail Q Γ K).filter headTog = [] :=
  cellTail_filter fun _ => ⟨rfl, rfl⟩

@[simp] lemma filter_headTog_cellRun (c : Option Γ) : (cellRun Q Γ K c).filter headTog = [] := by
  rw [cellRun_eq_cons, List.filter_cons_of_neg (by simp [headTog]), filter_headTog_cellTail]

@[simp] lemma filter_headTog_tapePrefix (n : ℕ) (sym : ℕ → Option Γ) :
    (tapePrefix Q Γ K n sym).filter headTog = [] := by
  rw [tapePrefix, filter_roundStream]
  simp only [filter_headTog_cellRun]
  exact roundStream_nil n

@[simp] lemma filter_headTog_tapeStream (sym : ℕ → Option Γ) :
    (tapeStream Q Γ K sym).filter headTog = [] :=
  filter_headTog_tapePrefix _ _

/-- A decision of a cell counter does not toggle the head facts. -/
lemma filter_headTog_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    p.filter headTog = [] := by
  rcases stepDecision_iff.1 h with ⟨q, q', a, b, mv, -, rfl⟩ | rfl
  · rw [List.filter_cons_of_neg (by simp [headTog]), filter_roundStream]
    simp only [filter_headTog_acquireActs]
    exact roundStream_nil _
  · simp [headTog]

/-- A cell of a cell counter does not toggle the head facts. -/
lemma filter_headTog_counterCell {d : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, StepDecision N w K (P t)) (n : ℕ) :
    (counterCell Q Γ K d P c n).filter headTog = [] := by
  by_cases hn : n < d
  · rw [counterCell_of_lt hn, filter_headTog_waitCellActs]
  · rw [counterCell_of_ge (Nat.not_lt.1 hn), counterSeg]
    set r := n - d with hr
    by_cases hmod : r % (K + 1) ≠ 0
    · rw [if_pos hmod, filter_headTog_waitCellActs]
    · rw [if_neg hmod]
      by_cases hK : K = 0
      · rw [if_pos hK]; simp [relCheckActs, relSyncActs, headTog]
      · rw [if_neg hK]
        by_cases hu0 : r / (K + 1) = 0
        · rw [if_pos hu0, List.filter_append, List.filter_append,
            List.filter_cons_of_neg (by simp),
            filter_headTog_stepDecision (hP 0 (by omega)), filter_headTog_relCheckActs,
            filter_headTog_relSyncActs]
          rfl
        · by_cases huK : r / (K + 1) < K
          · rw [if_neg hu0, if_pos huK, List.filter_append, List.filter_cons_of_neg (by simp),
              List.filter_append, List.filter_cons_of_neg (by simp),
              filter_headTog_stepDecision (hP _ huK), filter_headTog_relCheckActs,
              filter_headTog_relSyncActs]
            rfl
          · rw [if_neg hu0, if_neg huK, List.filter_append, List.filter_cons_of_neg (by simp),
              filter_headTog_relCheckActs, filter_headTog_relSyncActs]
            rfl

/-- The run of a cell counter does not toggle the head facts. -/
lemma filter_headTog_counterRun {d e : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hde : d + e = K) (hP : ∀ t < K, StepDecision N w K (P t)) :
    (counterRun Q Γ K d e P c).filter headTog = [] := by
  rw [counterRun_eq_roundStream hde, filter_roundStream]
  simp only [filter_headTog_counterCell hP]
  exact roundStream_nil _

/-! ### The toggles of the head counter -/

/-- The marks of the units of the head counter, in order. -/
def headTogList (K : ℕ) : List Bool :=
  (List.range (K * K + 3 * K + 1)).map (headMarkStd K)

/-- **The actions of the head counter that toggle the head facts**, in order. -/
lemma filter_headTog_headStream :
    (headStream Q Γ K).filter headTog = (headTogList K).map (togAct Q Γ) := by
  have hround : (roundStream (K * K + 3 * K + 1)
      fun u => headUnitActs Q Γ (headMarkStd K u)).filter (headTog (Q := Q) (Γ := Γ)) =
      (List.range (K * K + 3 * K + 1)).map fun u => togAct Q Γ (headMarkStd K u) := by
    rw [filter_roundStream]
    have hunit : ∀ u : ℕ, (headUnitActs Q Γ (headMarkStd K u)).filter (headTog (Q := Q) (Γ := Γ))
        = [togAct Q Γ (headMarkStd K u)] := by
      intro u
      cases headMarkStd K u <;> simp [headUnitActs, headTog, togAct]
    simp only [hunit]
    exact roundStream_singleton _ _
  rw [headStream, hround]
  simp [headTogList, List.map_map, Function.comp_def]

/-- The head fact after a list of toggles is the last mark of the list. -/
lemma lastHeadF_map_togAct (b : Option Bool) : ∀ L : List Bool,
    lastHeadF b ((L.map (togAct Q Γ))) = if L = [] then b else L.getLast? := by
  intro L
  induction L generalizing b with
  | nil => rfl
  | cons v L ih =>
      rw [List.map_cons, lastHeadF_cons]
      have hstep : stepHeadF b (togAct Q Γ v) = some v := by
        cases v <;> rfl
      rw [hstep, ih]
      cases L with
      | nil => simp
      | cons v' L' => simp [List.getLast?_cons_cons]

lemma lastHeadF_map_togAct_none (L : List Bool) :
    lastHeadF (Q := Q) (Γ := Γ) none (L.map (togAct Q Γ)) = L.getLast? := by
  rw [lastHeadF_map_togAct]
  split <;> simp_all

/-- **The head fact after a prefix of the stream of the head counter is the mark of the last unit
it has run.** -/
theorem lastHeadF_prefix_headStream {H : List (TMAct Q Γ)} (hH : H <+: headStream Q Γ K) :
    lastHeadF none H = ((headTogList K).take (H.countP headTog)).getLast? := by
  have hpre : H.filter headTog <+: (headTogList K).map (togAct Q Γ) := by
    rw [← filter_headTog_headStream]
    exact List.IsPrefix.filter headTog hH
  have hlen : (H.filter headTog).length = H.countP headTog :=
    List.countP_eq_length_filter.symm
  have heq : H.filter headTog = ((headTogList K).map (togAct Q Γ)).take (H.countP headTog) := by
    rw [← hlen]
    exact List.prefix_iff_eq_take.mp hpre
  rw [← lastHeadF_filter, heq, ← List.map_take, lastHeadF_map_togAct_none]

/-! ### The head fact of a prefix of a solution plan -/

/-- **The head fact after a prefix of a solution plan is the head fact after the part of the head
counter that the prefix has executed.**  Neither the tape nor a cell counter touches it. -/
theorem lastHeadF_of_isPlanSplit (D : SolutionPlanData N w K) {u ph pt : List (TMAct Q Γ)}
    {parts : List (List (TMAct Q Γ))}
    (hsplit : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) u parts ph pt) :
    lastHeadF none u = lastHeadF none ph := by
  obtain ⟨hparts, hph, hpt, pac, pbs, hpl, hpi, hint⟩ := hsplit
  -- every part is a prefix of the run of a cell counter, which has no toggle
  have hpartsnil : ∀ l ∈ parts, l.filter headTog = [] := by
    intro l hl
    obtain ⟨l', hl', hpre⟩ := exists_right_of_forall₂ hparts hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl'
    have hj' : j < K + 1 := by rw [← D.card]; exact hj
    have hrun := D.runs j hj
    have hdle : D.d j ≤ K := D.dle j hj'
    have hzero : (D.ass[j]).filter headTog = [] := by
      rw [hrun]
      exact filter_headTog_counterRun (N := N) (w := w) (by omega) (D.decisions j hj')
    have hsub := (List.IsPrefix.filter headTog hpre)
    rw [hzero] at hsub
    exact List.prefix_nil.1 hsub
  have hptnil : pt.filter headTog = [] := by
    have hsub := List.IsPrefix.filter (headTog (Q := Q) (Γ := Γ)) hpt
    rw [filter_headTog_tapeStream] at hsub
    exact List.prefix_nil.1 hsub
  -- filtering commutes with the interleavings
  have hpl' := hpl.filter headTog
  have hpi' := hpi.filter headTog
  have hint' := hint.filter headTog
  have hpacnil : pac.filter headTog = [] := by
    refine InterleaveList.eq_nil_of_forall_nil hpl' ?_
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact hpartsnil l' hl'
  rw [hpacnil, hptnil] at hpi'
  have hpbs : pbs.filter headTog = [] := hpi'.eq_of_nil_left
  rw [hpbs] at hint'
  have hu : u.filter headTog = ph.filter headTog := hint'.eq_of_nil_right
  rw [← lastHeadF_filter, hu, lastHeadF_filter]

end TMEnc

end HTN
