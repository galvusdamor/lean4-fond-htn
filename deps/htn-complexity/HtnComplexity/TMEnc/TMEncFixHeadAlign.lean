import HtnComplexity.TMEnc.TMEncFixHeadCounts
import HtnComplexity.TMEnc.TMEncFixCellStep
import HtnComplexity.Interleave.CutToolsComp
/-!
# The alignment of the head counter with the cells of the tape

This is the last missing piece of the soundness direction of the repaired Turing-machine
encoding: *which* mark of the head counter a cell of the tape reads when the counter that is
due there takes its decision.

The argument is a counting argument on the channel `head`.  Cut a solution plan immediately
before the decision of the cell `n` (`HTN.TMEnc.exists_decisionCut`).  Then

* the tape has issued `n + 1` requests on `head` — the `n` cells before, and the one of the cell
  `n` itself, because the decision follows the `wait head` of its cell
  (`HTN.TMEnc.countP_isCall_head_of_prefix_cellTail`), and it has waited for every answer;
* the transitions taken so far have issued `HTN.TMEnc.numEx D n` extra requests, and have waited
  for their answers too;
* so the two semaphores of the channel give `#start_head ≤ n + 1 + numEx` and
  `n + 1 + numEx ≤ #respond_head`, while the shape of the stream of the head counter gives
  `#respond_head ≤ #toggles ≤ #start_head + 1`
  (`HTN.TMEnc.headStream_prefix_toggle_bounds`).

Hence the number of *units* of the head counter that have toggled is `n + numEx D n` or one
more, and the head fact the decision reads is the mark of the last of them:

`HTN.TMEnc.headMark_at_decision` — **the decision of the cell `n` is a transition of the machine
exactly when the mark `HTN.TMEnc.headMarkAt K j` is set, for a `j` with
`n + numEx D n ≤ j ≤ n + numEx D n + 1`.**
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Counting and filtering along a `PlanInter` -/

/-- **Counting is additive along the three streams of a plan.** -/
lemma countP_of_planInter {ls : List (List (TMAct Q Γ))} {H T whole : List (TMAct Q Γ)}
    (h : PlanInter ls H T whole) (f : TMAct Q Γ → Bool) :
    whole.countP f = H.countP f + ((ls.map fun l => l.countP f).sum + T.countP f) := by
  obtain ⟨pac, pbs, hpl, hpi, hph⟩ := h
  rw [hph.countP, hpi.countP, hpl.countP]

/-- **Only the head counter toggles the head facts**, so the toggles of a plan are those of its
head-counter part. -/
lemma filter_headTog_of_planInter {ls : List (List (TMAct Q Γ))} {H T whole : List (TMAct Q Γ)}
    (h : PlanInter ls H T whole) (hls : ∀ l ∈ ls, l.filter headTog = [])
    (hT : T.filter headTog = []) : whole.filter headTog = H.filter headTog := by
  obtain ⟨pac, pbs, hpl, hpi, hph⟩ := h
  have hpl' := hpl.filter headTog
  have hpi' := hpi.filter headTog
  have hph' := hph.filter headTog
  have hpacnil : pac.filter headTog = [] := by
    refine InterleaveList.eq_nil_of_forall_nil hpl' ?_
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact hls l' hl'
  rw [hpacnil, hT] at hpi'
  have hpbs : pbs.filter headTog = [] := hpi'.eq_of_nil_left
  rw [hpbs] at hph'
  exact hph'.eq_of_nil_right

/-! ### The first `n` cells of a cell counter -/

lemma filter_headTog_roundStream_counterCell {d : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) (n : ℕ) :
    (roundStream n (counterCell Q Γ K d P c)).filter headTog = [] := by
  rw [filter_roundStream]
  simp only [filter_headTog_counterCell hP]
  exact roundStream_nil _

/-- The cell counters wait for every request they issue on the `head` channel. -/
lemma countP_isWait_head_roundStream_counterCell {d : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) (n : ℕ) :
    (roundStream n (counterCell Q Γ K d P c)).countP (isWait SyncKind.head) =
      (roundStream n (counterCell Q Γ K d P c)).countP (isCall SyncKind.head) := by
  rw [countP_roundStream, countP_roundStream]
  exact Finset.sum_congr rfl fun r _ => (countP_head_counterCell (N := N) (w := w) hP r).1.symm

/-- The cell counters neither consume nor answer requests on the `head` channel. -/
lemma countP_head_roundStream_counterCell {d : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) (n : ℕ) :
    (roundStream n (counterCell Q Γ K d P c)).countP (isStart SyncKind.head) = 0 ∧
      (roundStream n (counterCell Q Γ K d P c)).countP (isRespond SyncKind.head) = 0 := by
  constructor <;> rw [countP_roundStream] <;> refine Finset.sum_eq_zero fun r _ => ?_
  · exact (countP_head_counterCell (N := N) (w := w) hP r).2.1
  · exact (countP_head_counterCell (N := N) (w := w) hP r).2.2

/-- A cell counter issues no request on the `check` channel. -/
lemma countP_isCall_check_roundStream_counterCell {d : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) (n : ℕ) :
    (roundStream n (counterCell Q Γ K d P c)).countP (isCall SyncKind.check) = 0 := by
  rw [countP_roundStream]
  exact Finset.sum_eq_zero fun r _ =>
    countP_isCall_counterCell (N := N) (w := w) (by simp) hP r

/-- Every cell of a counter answers exactly one request on the `check` channel. -/
lemma countP_isStart_check_roundStream_counterCell {d : ℕ} {P : ℕ → List (TMAct Q Γ)}
    {c : ℕ → Option Γ} (hP : ∀ t < K, StepDecision N w K (P t)) (n : ℕ) :
    (roundStream n (counterCell Q Γ K d P c)).countP (isStart SyncKind.check) = n := by
  rw [countP_roundStream,
    Finset.sum_congr rfl fun r _ => countP_isStart_counterCell (N := N) (w := w)
      SyncKind.check (by simp) hP r]
  simp

/-! ### The extra requests of the transitions taken before a cell -/

/-- **The number of extra requests on the `head` channel that the cell counters have issued
during the first `n` cells** — the `moveExtra` of the transitions taken there. -/
def numEx (D : SolutionPlanData N w K) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (K + 1),
    (roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP (isCall SyncKind.head)

@[simp] lemma numEx_zero (D : SolutionPlanData N w K) : numEx D 0 = 0 := by simp [numEx]

/-- The sum of a count over the parts of a prefix that has completed the first `n` cells. -/
lemma sum_parts_countP (D : SolutionPlanData N w K) {n : ℕ}
    {partsU : List (List (TMAct Q Γ))} (hlen : partsU.length = K + 1)
    (hcells : ∀ j, ∀ hj : j < partsU.length,
      partsU[j] = roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j)))
    (f : TMAct Q Γ → Bool) :
    (partsU.map fun l => l.countP f).sum =
      ∑ j ∈ Finset.range (K + 1),
        (roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP f := by
  have hmap : (partsU.map fun l => l.countP f) =
      (List.range (K + 1)).map fun j =>
        (roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP f := by
    refine List.ext_getElem (by simp [hlen]) ?_
    intro j hj₁ hj₂
    have hj : j < partsU.length := by simpa using hj₁
    simp only [List.getElem_map, List.getElem_range]
    rw [hcells j hj]
  rw [hmap, sum_map_range]

/-! ### The decision cell, split at its decision -/

/-- **The cell of a solution plan at which the counter that is due takes its decision, split at
that decision.**  Before it the counter has answered the request of the cell on the `check`
channel and has touched the `head` channel not at all. -/
lemma counterCell_due_split (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K) :
    ∃ A B : List (TMAct Q Γ),
      counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n =
          A ++ (D.P (due D n) (n / (K + 1)) ++ B) ∧
        A.countP (isStart SyncKind.check) = 1 ∧
        A.countP (isCall SyncKind.check) = 0 ∧
        A.countP (isCall SyncKind.head) = 0 ∧ A.countP (isWait SyncKind.head) = 0 ∧
        A.countP (isStart SyncKind.head) = 0 ∧ A.countP (isRespond SyncKind.head) = 0 ∧
        A.filter headTog = [] ∧ B.countP (isCall SyncKind.head) = 0 := by
  have hK0 : ¬ K = 0 := by rintro rfl; exact Nat.not_lt_zero _ hu
  rw [counterCell_due, counterSeg_mul, if_neg hK0]
  by_cases hu0 : n / (K + 1) = 0
  · refine ⟨relCheckActs Q Γ, chkAct Q Γ (D.cc (due D n) 0) :: relSyncActs Q Γ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos hu0, hu0]
    · simp [relCheckActs, isStart]
    · simp [relCheckActs, isCall]
    · simp [relCheckActs, isCall]
    · simp [relCheckActs, isWait]
    · simp [relCheckActs, isStart]
    · simp [relCheckActs, isRespond]
    · simp [relCheckActs, headTog]
    · simp [relSyncActs, isCall, chkAct]
  · refine ⟨relCheckActs Q Γ ++ [chkAct Q Γ (D.cc (due D n) (n / (K + 1) - 1))],
      chkAct Q Γ (D.cc (due D n) (n / (K + 1))) :: relSyncActs Q Γ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hu0, if_pos hu, List.append_assoc]
      rfl
    · simp [relCheckActs, isStart, chkAct]
    · simp [relCheckActs, isCall, chkAct]
    · simp [relCheckActs, isCall, chkAct]
    · simp [relCheckActs, isWait, chkAct]
    · simp [relCheckActs, isStart, chkAct]
    · simp [relCheckActs, isRespond, chkAct]
    · simp [relCheckActs, headTog, chkAct]
    · simp [relSyncActs, isCall, chkAct]

/-- Every decision of a cell counter begins with an action. -/
lemma stepDecision_cons {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    ∃ (a : TMAct Q Γ) (t : List (TMAct Q Γ)), p = a :: t := by
  rcases stepDecision_iff.1 h with ⟨q, q', a, b, mv, -, rfl⟩ | rfl
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-! ### The cut of a solution plan at a decision -/

/-- **A solution plan, cut immediately before the decision of the cell `n`.**

At that moment the tape and the transitions taken so far have issued — and waited for the answer
to — exactly `n + 1 + numEx D n` requests on the `head` channel, while the toggles, the consumed
requests and the answers are those of a prefix of the stream of the head counter. -/
theorem exists_decisionCut (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K) :
    ∃ (p rest H : List (TMAct Q Γ)) (dec : TMAct Q Γ) (tl : List (TMAct Q Γ)),
      D.P (due D n) (n / (K + 1)) = dec :: tl ∧
        D.as₁ = p ++ dec :: rest ∧
        H <+: headStream Q Γ K ∧
        p.filter headTog = H.filter headTog ∧
        p.countP (isStart SyncKind.head) = H.countP (isStart SyncKind.head) ∧
        p.countP (isRespond SyncKind.head) = H.countP (isRespond SyncKind.head) ∧
        p.countP (isCall SyncKind.head) = n + 1 + numEx D n ∧
        p.countP (isWait SyncKind.head) = n + 1 + numEx D n := by
  classical
  have hnlt : n < (K + 1) * (K + 1) := by
    have hdm := Nat.div_add_mod n (K + 1)
    have hmod : n % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
    have h1 : (K + 1) * (n / (K + 1)) + (K + 1) ≤ (K + 1) * K + (K + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have hKK : (K + 1) * K + (K + 1) = (K + 1) * (K + 1) := by ring
    omega
  obtain ⟨u, m, v, Hu, Hm, partsU, parts, heq, hsplit, hcellsU, hpi, hsub, hHpre, hlen, hcells⟩ :=
    exists_cellCutSplit D hnlt
  have hlenU : partsU.length = K + 1 := parts_length hsplit
  have hjlt : due D n < parts.length := by rw [hlen]; exact due_lt D n
  have hjK : due D n < K + 1 := by rw [← hlen]; exact hjlt
  obtain ⟨A, B, hAB, hAcheck, hAcallc, hAcall, hAwait, hAstart, hAresp, hAtog, -⟩ :=
    counterCell_due_split D hu
  obtain ⟨dec, tl, hdec⟩ := stepDecision_cons (D.decisions (due D n) hjK (n / (K + 1)) hu)
  have hpartsj : parts[due D n] = A ++ dec :: (tl ++ B) := by
    rw [hcells (due D n) hjlt, hAB, hdec]
    simp
  obtain ⟨fsts, snds, Hm₁, Hm₂, T₁, T₂, m₁, m₂, hHm, hT, hm, hfall, hfj, -, hpi₁, -⟩ :=
    hpi.cut_at_comp hjlt hpartsj
  -- prefixes of the head stream
  have hHupre : Hu <+: headStream Q Γ K := hsplit.2.1
  have hHu₁pre : Hu ++ Hm₁ <+: headStream Q Γ K := by
    refine List.IsPrefix.trans ?_ hHpre
    rw [hHm, ← List.append_assoc]
    exact List.prefix_append _ _
  have hHm₁sub : Hm₁.Sublist (headStream Q Γ K) :=
    List.Sublist.trans (hHm ▸ List.sublist_append_left Hm₁ Hm₂) hsub
  -- the pieces of the counters before the decision
  have hflen : fsts.length = parts.length := hfall.length_eq
  have hfzero : ∀ i, ∀ hi : i < fsts.length,
      (fsts[i]).countP (isCall SyncKind.head) = 0 ∧
        (fsts[i]).countP (isWait SyncKind.head) = 0 ∧
        (fsts[i]).countP (isStart SyncKind.head) = 0 ∧
        (fsts[i]).countP (isRespond SyncKind.head) = 0 ∧
        (fsts[i]).countP (isCall SyncKind.check) = 0 ∧
        (fsts[i]).filter headTog = [] := by
    intro i hi
    have hi' : i < parts.length := by omega
    by_cases hij : i = due D n
    · have hval : fsts[i] = A := by
        have h : fsts[i]? = some A := by rw [hij]; exact hfj
        rw [List.getElem?_eq_getElem hi] at h
        exact Option.some.inj h
      rw [hval]
      exact ⟨hAcall, hAwait, hAstart, hAresp, hAcallc, hAtog⟩
    · have hpre : fsts[i] <+: parts[i] := hfall.get hi hi'
      rw [hcells i hi', counterCell_of_ne_due D (by omega) hij] at hpre
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := hpre.sublist.countP_le (p := isCall SyncKind.head); simpa using this
      · have := hpre.sublist.countP_le (p := isWait SyncKind.head); simpa using this
      · have := hpre.sublist.countP_le (p := isStart SyncKind.head); simpa using this
      · have := hpre.sublist.countP_le (p := isRespond SyncKind.head); simpa using this
      · have h0 : (waitCellActs Q Γ).countP (isCall SyncKind.check) = 0 := by
          simp [waitCellActs, isCall]
        have hle := hpre.sublist.countP_le (p := isCall SyncKind.check)
        omega
      · have := hpre.filter headTog
        rw [filter_headTog_waitCellActs] at this
        exact List.prefix_nil.1 this
  have hfmem : ∀ l ∈ fsts,
      l.countP (isCall SyncKind.head) = 0 ∧ l.countP (isWait SyncKind.head) = 0 ∧
        l.countP (isStart SyncKind.head) = 0 ∧ l.countP (isRespond SyncKind.head) = 0 ∧
        l.countP (isCall SyncKind.check) = 0 ∧ l.filter headTog = [] := by
    intro l hl
    obtain ⟨i, hi, hval⟩ := List.getElem_of_mem hl
    rw [← hval]
    exact hfzero i hi
  -- the counts of the two pieces
  have hcountU : ∀ f : TMAct Q Γ → Bool,
      u.countP f = Hu.countP f +
        ((∑ i ∈ Finset.range (K + 1),
          (roundStream n (counterCell Q Γ K (D.d i) (D.P i) (D.cc i))).countP f) +
          (tapePrefix Q Γ K n D.sym).countP f) := by
    intro f
    rw [countP_of_isPlanSplit hsplit f, sum_parts_countP D hlenU hcellsU f]
  have hcountM : ∀ f : TMAct Q Γ → Bool,
      m₁.countP f = Hm₁.countP f + ((fsts.map fun l => l.countP f).sum + T₁.countP f) :=
    fun f => countP_of_planInter hpi₁ f
  have hcountP : ∀ f : TMAct Q Γ → Bool, f (TMAct.assert (D.sym n)) = false →
      (u ++ TMAct.assert (D.sym n) :: m₁).countP f = u.countP f + m₁.countP f := by
    intro f hf
    rw [List.countP_append, List.countP_cons_of_neg (by simp [hf])]
  -- the head stream does not touch the cell channels, and the counters do not touch `head`
  have hHzeroC : ∀ (H' : List (TMAct Q Γ)) (x : SyncKind), H'.Sublist (headStream Q Γ K) →
      H'.countP (isCall x) = 0 := by
    intro H' x hH'
    have := hH'.countP_le (p := isCall x)
    rw [countP_isCall_headStream (K := K)] at this
    omega
  have hHzeroW : ∀ (H' : List (TMAct Q Γ)) (x : SyncKind), H'.Sublist (headStream Q Γ K) →
      H'.countP (isWait x) = 0 := by
    intro H' x hH'
    have := hH'.countP_le (p := isWait x)
    rw [countP_isWait_headStream (K := K)] at this
    omega
  have hHzeroS : ∀ H' : List (TMAct Q Γ), H'.Sublist (headStream Q Γ K) →
      H'.countP (isStart SyncKind.check) = 0 := by
    intro H' hH'
    have := hH'.countP_le (p := isStart SyncKind.check)
    rw [countP_isStart_headStream (K := K) (by simp)] at this
    omega
  -- the tape part of the chunk has issued the request of the cell `n`
  have hT₁pre : T₁ <+: cellTail Q Γ K := ⟨T₂, hT.symm⟩
  have happ : (problemFix N w K).SeqApplicable (D.as₁ ++ [TMAct.check (TMFact.st D.f)])
    (problemFix N w K).init := (Problem.isSolutionPlan_iff.1 D.isPlan).2.1
  have hcut : D.as₁ ++ [TMAct.check (TMFact.st D.f)] =
      (u ++ TMAct.assert (D.sym n) :: m₁) ++
        (dec :: (m₂ ++ (v ++ [TMAct.check (TMFact.st D.f)]))) := by
    rw [heq, hm]; simp
  have happ' := (ActionModel.seqApplicable_append _ _ _ _).1 (by rw [hcut] at happ; exact happ)
  have hcheck1 : 1 ≤ T₁.countP (isCall SyncKind.check) := by
    have hstart := countP_start_le_countP_call (Q := Q) (Γ := Γ) SyncKind.check
      (stepF_not_mem_initFix (N := N) (w := w) (K := K) SyncKind.check) happ'.1
    -- the answers on the `check` channel already given
    have hsumU : (∑ i ∈ Finset.range (K + 1),
        (roundStream n (counterCell Q Γ K (D.d i) (D.P i) (D.cc i))).countP
          (isStart SyncKind.check)) = n * (K + 1) := by
      rw [Finset.sum_congr rfl fun i hi =>
        countP_isStart_check_roundStream_counterCell (N := N) (w := w)
          (D.decisions i (Finset.mem_range.1 hi)) n]
      simp [Nat.mul_comm]
    have hsumUc : (∑ i ∈ Finset.range (K + 1),
        (roundStream n (counterCell Q Γ K (D.d i) (D.P i) (D.cc i))).countP
          (isCall SyncKind.check)) = 0 :=
      Finset.sum_eq_zero fun i hi => countP_isCall_check_roundStream_counterCell (N := N) (w := w)
        (D.decisions i (Finset.mem_range.1 hi)) n
    have hfstsC : (fsts.map fun l => l.countP (isCall SyncKind.check)).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact (hfmem l hl).2.2.2.2.1
    have hfstsS : 1 ≤ (fsts.map fun l => l.countP (isStart SyncKind.check)).sum := by
      have hjf : due D n < fsts.length := by omega
      have hval : fsts[due D n] = A := by
        have h := hfj
        rw [List.getElem?_eq_getElem hjf] at h
        exact Option.some.inj h
      have hmem : A.countP (isStart SyncKind.check) ∈
          fsts.map fun l => l.countP (isStart SyncKind.check) := by
        rw [← hval]
        exact List.mem_map_of_mem (List.getElem_mem hjf)
      have := List.single_le_sum (l := fsts.map fun l => l.countP (isStart SyncKind.check))
        (fun x _ => Nat.zero_le x) _ hmem
      omega
    have hS := hcountP (isStart SyncKind.check) (by simp [isStart])
    have hC := hcountP (isCall SyncKind.check) (by simp [isCall])
    rw [hcountU, hcountM, hsumU, hHzeroS Hu hHupre.sublist, hHzeroS Hm₁ hHm₁sub] at hS
    rw [hcountU, hcountM, hsumUc, hHzeroC Hu SyncKind.check hHupre.sublist,
      hHzeroC Hm₁ SyncKind.check hHm₁sub, hfstsC] at hC
    simp only [countP_isStart_tapePrefix, countP_isCall_check_tapePrefix] at hS hC
    have hT₁S : T₁.countP (isStart SyncKind.check) = 0 := by
      have := hT₁pre.sublist.countP_le (p := isStart SyncKind.check)
      have h0 : (cellTail Q Γ K).countP (isStart SyncKind.check) = 0 := by
        simp [cellTail, countP_roundStream, acquireActs, isStart]
      omega
    rw [hT₁S] at hS
    omega
  obtain ⟨hT₁call, hT₁wait⟩ := countP_isCall_head_of_prefix_cellTail hT₁pre hcheck1
  -- the sums over the counters
  have hsumEx : (∑ i ∈ Finset.range (K + 1),
      (roundStream n (counterCell Q Γ K (D.d i) (D.P i) (D.cc i))).countP
        (isCall SyncKind.head)) = numEx D n := rfl
  have hsumExW : (∑ i ∈ Finset.range (K + 1),
      (roundStream n (counterCell Q Γ K (D.d i) (D.P i) (D.cc i))).countP
        (isWait SyncKind.head)) = numEx D n := by
    rw [numEx]
    exact Finset.sum_congr rfl fun i hi =>
      countP_isWait_head_roundStream_counterCell (N := N) (w := w)
        (D.decisions i (Finset.mem_range.1 hi)) n
  have hsumS : (∑ i ∈ Finset.range (K + 1),
      (roundStream n (counterCell Q Γ K (D.d i) (D.P i) (D.cc i))).countP
        (isStart SyncKind.head)) = 0 :=
    Finset.sum_eq_zero fun i hi =>
      (countP_head_roundStream_counterCell (N := N) (w := w)
        (D.decisions i (Finset.mem_range.1 hi)) n).1
  have hsumR : (∑ i ∈ Finset.range (K + 1),
      (roundStream n (counterCell Q Γ K (D.d i) (D.P i) (D.cc i))).countP
        (isRespond SyncKind.head)) = 0 :=
    Finset.sum_eq_zero fun i hi =>
      (countP_head_roundStream_counterCell (N := N) (w := w)
        (D.decisions i (Finset.mem_range.1 hi)) n).2
  have hfstsZero : ∀ f : TMAct Q Γ → Bool,
      (∀ l ∈ fsts, l.countP f = 0) → (fsts.map fun l => l.countP f).sum = 0 := by
    intro f hf
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact hf l hl
  have hT₁S : ∀ x : SyncKind, T₁.countP (isStart x) = 0 := by
    intro x
    have := hT₁pre.sublist.countP_le (p := isStart x)
    have h0 : (cellTail Q Γ K).countP (isStart x) = 0 := by
      simp [cellTail, countP_roundStream, acquireActs, isStart]
    omega
  have hT₁R : ∀ x : SyncKind, T₁.countP (isRespond x) = 0 := by
    intro x
    have := hT₁pre.sublist.countP_le (p := isRespond x)
    have h0 : (cellTail Q Γ K).countP (isRespond x) = 0 := by
      simp [cellTail, countP_roundStream, acquireActs, isRespond]
    omega
  -- the toggles
  have hfilterU : u.filter headTog = Hu.filter headTog := by
    obtain ⟨-, -, -, pac, pbs, hpl, hpq, hph⟩ := hsplit
    refine filter_headTog_of_planInter ⟨pac, pbs, hpl, hpq, hph⟩ ?_ (by simp)
    intro l hl
    obtain ⟨i, hi, hval⟩ := List.getElem_of_mem hl
    rw [← hval, hcellsU i hi]
    exact filter_headTog_roundStream_counterCell (N := N) (w := w)
      (D.decisions i (by omega)) n
  have hfilterM : m₁.filter headTog = Hm₁.filter headTog := by
    refine filter_headTog_of_planInter hpi₁ (fun l hl => (hfmem l hl).2.2.2.2.2) ?_
    have := hT₁pre.filter headTog
    rw [filter_headTog_cellTail] at this
    exact List.prefix_nil.1 this
  refine ⟨u ++ TMAct.assert (D.sym n) :: m₁, m₂ ++ v, Hu ++ Hm₁, dec, tl, hdec, ?_,
    hHu₁pre, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq, hm]; simp
  · rw [List.filter_append, List.filter_cons_of_neg (by simp [headTog]), hfilterU, hfilterM,
      List.filter_append]
  · rw [hcountP _ (by simp [isStart]), hcountU, hcountM, hsumS,
      hfstsZero _ (fun l hl => (hfmem l hl).2.2.1), hT₁S, List.countP_append]
    simp
  · rw [hcountP _ (by simp [isRespond]), hcountU, hcountM, hsumR,
      hfstsZero _ (fun l hl => (hfmem l hl).2.2.2.1), hT₁R, List.countP_append]
    simp
  · rw [hcountP _ (by simp [isCall]), hcountU, hcountM, hsumEx,
      hfstsZero _ (fun l hl => (hfmem l hl).1), hT₁call,
      hHzeroC Hu SyncKind.head hHupre.sublist, hHzeroC Hm₁ SyncKind.head hHm₁sub]
    simp only [countP_isCall_head_tapePrefix]
    omega
  · rw [hcountP _ (by simp [isWait]), hcountU, hcountM, hsumExW,
      hfstsZero _ (fun l hl => (hfmem l hl).2.1), hT₁wait]
    rw [hHzeroW Hu SyncKind.head hHupre.sublist, hHzeroW Hm₁ SyncKind.head hHm₁sub]
    simp only [countP_isWait_head_tapePrefix]
    omega


/-! ### What `numEx` counts -/

/-- Only the counter that is due in the cell `n` can issue an extra request there. -/
lemma numEx_succ (D : SolutionPlanData N w K) (n : ℕ) :
    numEx D (n + 1) = numEx D n +
      (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n).countP
        (isCall SyncKind.head) := by
  have hsplit : ∀ j, (roundStream (n + 1)
      (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP (isCall SyncKind.head) =
      (roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP
          (isCall SyncKind.head) +
        (counterCell Q Γ K (D.d j) (D.P j) (D.cc j) n).countP (isCall SyncKind.head) := by
    intro j
    rw [roundStream_succ, List.countP_append]
  simp only [numEx, hsplit, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_eq_single (due D n) ?_ ?_
  · intro j hj hne
    rw [counterCell_of_ne_due D (Finset.mem_range.1 hj) hne]
    exact countP_isCall_head_waitCellActs
  · intro hmem
    exact absurd (Finset.mem_range.2 (due_lt D n)) hmem

/-- **The extra requests of a cell are those of the decision taken there.** -/
lemma countP_isCall_head_counterCell_due (D : SolutionPlanData N w K) {n : ℕ}
    (hu : n / (K + 1) < K) :
    (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n).countP
        (isCall SyncKind.head) =
      (D.P (due D n) (n / (K + 1))).countP (isCall SyncKind.head) := by
  obtain ⟨A, B, hAB, -, -, hAcall, -, -, -, -, hBcall⟩ := counterCell_due_split D hu
  rw [hAB, List.countP_append, List.countP_append, hAcall, hBcall]
  omega

/-- A transition issues `moveExtra` extra requests, the test that the head is elsewhere issues
none. -/
lemma countP_isCall_head_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    (∃ (q q' : Q) (a b : Γ) (mv : Move), (q', b, mv) ∈ N.step q a ∧
        p.countP (isCall SyncKind.head) = moveExtra mv) ∨
      p.countP (isCall SyncKind.head) = 0 := by
  rcases stepDecision_iff.1 h with ⟨q, q', a, b, mv, hmem, rfl⟩ | rfl
  · refine Or.inl ⟨q, q', a, b, mv, hmem, ?_⟩
    simp [countP_roundStream, acquireActs, isCall]
  · exact Or.inr rfl

/-! ### The mark the decision of a cell reads -/

/-- **The head fact after `j + 1` units of the repaired head counter have toggled**: the mark of
the unit `j`, the last one that has run. -/
def headMarkAt (K j : ℕ) : Bool := headMarkStd K j

@[simp] lemma headMarkAt_zero (K : ℕ) : headMarkAt K 0 = false := by
  simp [headMarkAt]

lemma headTogList_length : (headTogList K).length = K * K + 3 * K + 1 := by
  simp [headTogList]

lemma getElem?_headTogList {i : ℕ} (h : i < (headTogList K).length) :
    (headTogList K)[i]? = some (headMarkAt K i) := by
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [headTogList, headMarkAt]

lemma take_getLast?_headTogList {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ (headTogList K).length) :
    ((headTogList K).take t).getLast? = some (headMarkAt K (t - 1)) := by
  have hlen : ((headTogList K).take t).length = t := by
    rw [List.length_take, min_eq_left h2]
  rw [List.getLast?_eq_getElem?, hlen, List.getElem?_take,
    if_pos (show t - 1 < t by omega)]
  exact getElem?_headTogList (by omega)

/-- The head counter toggles `K² + 3K + 1` times in all — once per unit. -/
lemma countP_headTog_headStream :
    (headStream Q Γ K).countP headTog = K * K + 3 * K + 1 := by
  rw [List.countP_eq_length_filter, filter_headTog_headStream, List.length_map,
    headTogList_length]

/-- **The mark of the head counter that the decision of the cell `n` reads.**

At the decision of the cell `n` the repaired head counter has run exactly `n + 1 + numEx D n`
units — one per request, `numEx D n` being the extra requests the transitions taken before the
cell `n` have issued — so the mark it reads is the one of the unit `n + numEx D n`, and of no
other.  A transition can be taken only where that mark reports the head as present, and the test
`check noHead` only where it reports it as absent.

For the head counter as printed the counter may be one unit ahead, and the reading is pinned
only up to that unit; see `NOTES.md`. -/
theorem headMark_at_decision (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K) :
      (∀ (q q' : Q) (a b : Option Γ) (tl : List (TMAct Q Γ)),
          D.P (due D n) (n / (K + 1)) = TMAct.step q a q' b :: tl →
            headMarkAt K (n + numEx D n) = true) ∧
      (D.P (due D n) (n / (K + 1)) = [TMAct.check TMFact.noHead] →
        headMarkAt K (n + numEx D n) = false) := by
  obtain ⟨p, rest, H, dec, tl, hdec, heq, hHpre, hfil, hst, hre, hcall, hwait⟩ :=
    exists_decisionCut D hu
  -- the plan is executable up to the decision
  have happ : (problemFix N w K).SeqApplicable (D.as₁ ++ [TMAct.check (TMFact.st D.f)])
    (problemFix N w K).init := (Problem.isSolutionPlan_iff.1 D.isPlan).2.1
  have hcut : D.as₁ ++ [TMAct.check (TMFact.st D.f)] =
      p ++ (dec :: (rest ++ [TMAct.check (TMFact.st D.f)])) := by
    rw [heq]; simp
  rw [hcut] at happ
  have happ' := (ActionModel.seqApplicable_append _ _ _ _).1 happ
  -- the two semaphores of the channel `head`
  have hsem₁ := countP_start_le_countP_call (Q := Q) (Γ := Γ) SyncKind.head
    (stepF_not_mem_initFix (N := N) (w := w) (K := K) SyncKind.head) happ'.1
  have hsem₂ := countP_wait_le_countP_respond (Q := Q) (Γ := Γ) SyncKind.head
    (steppedF_not_mem_initFix (N := N) (w := w) (K := K) SyncKind.head) happ'.1
  -- the shape of the stream of the head counter
  obtain ⟨htog₁, htog₂⟩ := headStream_prefix_toggle_bounds hHpre
  set t := H.countP headTog with htdef
  have hptog : p.countP headTog = t := by
    rw [List.countP_eq_length_filter, hfil, ← List.countP_eq_length_filter]
  have hbounds : t = n + 1 + numEx D n := by
    rw [hst] at hsem₁
    rw [hre] at hsem₂
    omega
  have htle : t ≤ (headTogList K).length := by
    have := hHpre.sublist.countP_le (p := headTog)
    rw [countP_headTog_headStream, ← headTogList_length] at this
    omega
  -- what the plan reads at that moment
  have hread : lastHeadF (Q := Q) (Γ := Γ) none p = some (headMarkAt K (t - 1)) := by
    rw [← lastHeadF_filter, hfil, lastHeadF_filter, lastHeadF_prefix_headStream hHpre,
      take_getLast?_headTogList (by omega) htle]
  rw [show n + numEx D n = t - 1 by omega]
  refine ⟨?_, ?_⟩
  · intro q q' a b tl' hstep
    have hdec' : dec = TMAct.step q a q' b := by
      rw [hdec] at hstep
      exact (List.cons.inj hstep).1
    rw [hdec'] at happ
    have := lastHeadF_of_step (N := N) (w := w) (K := K) happ
    rw [hread] at this
    exact Option.some.inj this
  · intro hnoHead
    have hdec' : dec = TMAct.check (TMFact.noHead : TMFact Q Γ) := by
      rw [hdec] at hnoHead
      exact (List.cons.inj hnoHead).1
    rw [hdec'] at happ
    have := lastHeadF_of_check_noHead (N := N) (w := w) (K := K) happ
    rw [hread] at this
    exact Option.some.inj this

end TMEnc

end HTN
