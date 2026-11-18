import HtnComplexity.TMEnc.TMEncFixTwoPhase
import HtnComplexity.TMEnc.TMEncFixInitGrid
import HtnComplexity.TMEnc.TMEncWitness
/-!
# The plan a witness is scheduled into

This file builds, from a witness `sym, st, hd` of an accepting run (`HTN.TMEnc.IsWitness`) and
the transition data of that run, the **explicit plan** of the repaired encoding, and proves that
it is a refinement of the initial task network.  What is left afterwards is its executability.

The plan is *cell-major*: it consists of the `(K+1)²` cells of the space–time diagram, one after
the other, and in the cell `n` (which lies in block `i = n / (K+1)` at column `j = n % (K+1)`)

* the tape writes the symbol of the cell and asks the head counter, then each of the `K + 1`
  cell counters on the `check` and then on the `sync` channel;
* the counter `j` takes its decision number `i` — a transition of the machine if the head of
  the machine is at that column, and the test `noHead` otherwise;
* the head counter answers the request of the *next* cell (its answer to the request of the
  cell `n` was given at the end of the cell `n - 1`, which is what makes the head fact right
  when the decision of the cell `n` is taken), plus the extra requests the transition issues.

The main results are `HTN.TMEnc.gridYield_planStream` — the plan is a refinement of the grid of
the initial task network — and `HTN.TMEnc.solvable_of_plan_seqApplicable`, which reduces the
completeness half of the simulation argument to the executability of the plan.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The data of the plan -/

/-- The symbol of the cell `n` of the space–time diagram. -/
def planSym (K : ℕ) (sym : ℕ → ℕ → Option Γ) (n : ℕ) : Option Γ := sym (n / (K + 1)) (n % (K + 1))

/-- **The actions of one transition of the machine**: the `step` action and the extra requests
on the `head` channel that the movement of the head consumes. -/
def transActs (st : ℕ → Q) (cIn cOut : ℕ → Γ) (mv : ℕ → Move) (t : ℕ) :
    List (TMAct Q Γ) :=
  TMAct.step (st t) (some (cIn t)) (st (t + 1)) (some (cOut t)) ::
    roundStream (moveExtra (mv t)) fun _ => acquireActs Q Γ SyncKind.head

/-- **The decision of the counter `j` at time `t`**: a transition of the machine if the head of
the machine is at the column `j` of the block `t`, and the test `noHead` otherwise. -/
def planP (st : ℕ → Q) (hd : ℕ → ℕ) (cIn cOut : ℕ → Γ) (mv : ℕ → Move) (j t : ℕ) :
    List (TMAct Q Γ) :=
  if j = hd t + 1 then transActs st cIn cOut mv t else [TMAct.check TMFact.noHead]

/-- The symbol the counter `j` compares at its decision number `t`: the symbol of the cell
`(t + 1, j)`, which the transition of the block `t` has already written. -/
def planC (sym : ℕ → ℕ → Option Γ) (j t : ℕ) : Option Γ := sym (t + 1) j

/-- The number of *extra* requests on the `head` channel that the cell `n` issues: those of the
transition taken in that cell, if any. -/
def extraCnt (K : ℕ) (hd : ℕ → ℕ) (mv : ℕ → Move) (n : ℕ) : ℕ :=
  if n / (K + 1) < K ∧ n % (K + 1) = hd (n / (K + 1)) + 1 then moveExtra (mv (n / (K + 1))) else 0

/-- The number of units of the head counter that the cell `n` runs: the answer to the request of
the next cell, and one per extra request of the cell. -/
def headCnt (K : ℕ) (hd : ℕ → ℕ) (mv : ℕ → Move) (n : ℕ) : ℕ := extraCnt K hd mv n + 1

/-- The index of the first unit of the head counter that the cell `n` runs. -/
def headBase (K : ℕ) (hd : ℕ → ℕ) (mv : ℕ → Move) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, headCnt K hd mv m

/-- **The marks of the head counter**: the unit `u` reports the head as present exactly when
`u ≡ 1 (mod K + 2)`.  This is the pattern the repaired chain of the head counter enforces
(`HTN.TMEnc.chainYield_headChainFix`), and — because every unit answers the request it is paired
with, and a transition eats up `1 - δ` further units, where `δ` is the displacement of the head —
it is exactly the pattern a homing run needs. -/
def headMark (K : ℕ) (u : ℕ) : Bool := decide (u % (K + 2) = 1)

/-! ### One transition -/

/-- A chain of requests on the `head` channel refines into that many request pairs. -/
lemma chainYield_replicate_acquireHead (k : ℕ) :
    (domainBod N w K).ChainYield
      (List.replicate k (Sum.inr (TMTask.acquire SyncKind.head)))
      (roundStream k fun _ => acquireActs Q Γ SyncKind.head) := by
  induction k with
  | zero => simp [(chainYield_nil_iff (D := domainBod N w K)).2 rfl]
  | succ k ih =>
      have h := roundStream_add 1 k fun _ : ℕ => acquireActs Q Γ SyncKind.head
      rw [show 1 + k = k + 1 from Nat.add_comm 1 k, roundStream_one] at h
      rw [List.replicate_succ, show (Sum.inr (TMTask.acquire SyncKind.head) ::
          List.replicate k (Sum.inr (TMTask.acquire SyncKind.head)) :
            List (TMAct Q Γ ⊕ TMTask Q Γ)) =
        [Sum.inr (TMTask.acquire SyncKind.head)] ++
          List.replicate k (Sum.inr (TMTask.acquire SyncKind.head)) from rfl, h]
      exact chainYield_app (chainYield_acquire_iff.2 rfl) ih

/-- **The actions of a transition are a refinement of the task `transition`.** -/
lemma chainYield_transActs {st : ℕ → Q} {cIn cOut : ℕ → Γ} {mv : ℕ → Move} {t : ℕ}
    (h : (st (t + 1), cOut t, mv t) ∈ N.step (st t) (cIn t)) :
    (domainBod N w K).ChainYield [Sum.inr TMTask.transition] (transActs st cIn cOut mv t) := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[Sum.inl (TMAct.step (st t) (some (cIn t)) (st (t + 1)) (some (cOut t))) ::
      List.replicate (moveExtra (mv t)) (Sum.inr (TMTask.acquire SyncKind.head))],
    ?_, gridYield_singleton_iff.2 ?_⟩
  · rw [bodiesFix_eq_of_ne (by simp)]
    exact ⟨st t, st (t + 1), cIn t, cOut t, mv t, h, rfl⟩
  · exact chainYield_cons_inl_iff.2 ⟨_, rfl, chainYield_replicate_acquireHead _⟩

/-! ### The tape chain -/

/-- **The tape chain of the initial task network refines into the cells of the witness.** -/
theorem chainYield_planTape {sym : ℕ → ℕ → Option Γ} {st : ℕ → Q} {hd : ℕ → ℕ}
    (hwit : IsWitness N w K sym st hd) (hw : 1 ≤ w.length) (hwK : w.length ≤ K) :
    (domainBod N w K).ChainYield
      [Sum.inr TMTask.produceInit, Sum.inr (TMTask.cSeq TMTask.tapeProduce K)]
      (roundStream ((K + 1) * (K + 1)) fun n => cellRun Q Γ K (planSym K sym n)) := by
  refine chainYield_tapeChain hw hwK ?_ ?_
  · intro j hj
    have hdiv : j / (K + 1) = 0 := Nat.div_eq_of_lt (by omega)
    have hmod : j % (K + 1) = j := Nat.mod_eq_of_lt (by omega)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [planSym, hdiv, hmod, tapeInitSym, hwit.sep 0 (by omega)]
    · simp [planSym, hdiv, hmod, tapeInitSym, Nat.ne_of_gt hj0,
        hwit.initTape j (by omega) (by omega)]
  · intro i hi
    have hmod : (i * (K + 1)) % (K + 1) = 0 := Nat.mul_mod_left i (K + 1)
    have hdiv : (i * (K + 1)) / (K + 1) = i := Nat.mul_div_cancel i (by omega)
    simp [planSym, hmod, hdiv, hwit.sep i hi]

/-! ### The budget of the head counter

The head counter has `K² + 3K + 1` units, one per request: `(K+1)²` from the tape and one per
extra request of a transition.  The extras therefore have to be exactly `K` many, and that is
precisely what a *homing* run — one whose head returns to the first cell and never falls off it
on the left — provides: a transition eats up `1 - δ` units, where `δ ∈ {-1, 0, 1}` is the
displacement of its head movement, and the displacements sum to `0`. -/

/-- A sum over `a * b` is a sum of `a` blocks of `b`. -/
lemma sum_range_mul (a b : ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ Finset.range (a * b), f n = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [show (a + 1) * b = a * b + b by ring, Finset.sum_range_add, ih,
        Finset.sum_range_succ]

/-- **A transition eats up as many units of the head counter as its head movement leaves
over**: the extras of the first `n` transitions and the position of the head after them add up
to `n`. -/
lemma sum_moveExtra_add_head {hd : ℕ → ℕ} {mv : ℕ → Move} (hd0 : hd 0 = 0)
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) :
    ∀ n ≤ K, (∑ i ∈ Finset.range n, moveExtra (mv i)) + hd n = n := by
  intro n
  induction n with
  | zero => simp [hd0]
  | succ n ih =>
      intro hn
      have hstep : moveExtra (mv n) + hd (n + 1) = 1 + hd n := by
        have h := hmove n (by omega)
        cases hmv : mv n with
        | right =>
            rw [hmv] at h
            simp only [Move.apply_right] at h
            simp only [moveExtra]
            omega
        | stay =>
            rw [hmv] at h
            simp only [Move.apply_stay] at h
            simp only [moveExtra]
            omega
        | left =>
            have h1 : 1 ≤ hd n := hbump n (by omega) hmv
            rw [hmv] at h
            simp only [Move.apply_left] at h
            simp only [moveExtra]
            omega
      have := ih (by omega)
      rw [Finset.sum_range_succ]
      omega

/-- **A homing run issues exactly `K` extra requests on the `head` channel.** -/
lemma sum_moveExtra_eq {hd : ℕ → ℕ} {mv : ℕ → Move} (hd0 : hd 0 = 0) (hdK : hd K = 0)
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) :
    ∑ i ∈ Finset.range K, moveExtra (mv i) = K := by
  have := sum_moveExtra_add_head hd0 hmove hbump K le_rfl
  omega

/-- The extras of one block are those of its transition. -/
lemma sum_extraCnt_block {hd : ℕ → ℕ} {mv : ℕ → Move} (hdlt : ∀ i ≤ K, hd i < K) (i : ℕ) :
    ∑ j ∈ Finset.range (K + 1), extraCnt K hd mv (i * (K + 1) + j) =
      if i < K then moveExtra (mv i) else 0 := by
  have hidx : ∀ j < K + 1, (i * (K + 1) + j) / (K + 1) = i ∧ (i * (K + 1) + j) % (K + 1) = j := by
    intro j hj
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < K + 1),
        Nat.div_eq_of_lt hj, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  by_cases hiK : i < K
  · have hhd : hd i < K := hdlt i (by omega)
    rw [Finset.sum_eq_single (hd i + 1)]
    · have h := hidx (hd i + 1) (by omega)
      simp [extraCnt, h.1, h.2, hiK]
    · intro j hj hne
      have h := hidx j (Finset.mem_range.1 hj)
      simp [extraCnt, h.1, h.2, hne]
    · intro hmem
      exact absurd (Finset.mem_range.2 (by omega)) hmem
  · refine (Finset.sum_eq_zero ?_).trans (by simp [hiK])
    intro j hj
    have h := hidx j (Finset.mem_range.1 hj)
    simp [extraCnt, h.1, h.2, hiK]

/-- **The head counter of the plan has exactly `K² + 3K + 1` units.** -/
theorem sum_headCnt {hd : ℕ → ℕ} {mv : ℕ → Move} (hd0 : hd 0 = 0) (hdK : hd K = 0)
    (hdlt : ∀ i ≤ K, hd i < K)
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) :
    ∑ n ∈ Finset.range ((K + 1) * (K + 1)), headCnt K hd mv n = K * K + 3 * K + 1 := by
  have hextra : ∑ n ∈ Finset.range ((K + 1) * (K + 1)), extraCnt K hd mv n = K := by
    rw [sum_range_mul (K + 1) (K + 1) (extraCnt K hd mv),
      Finset.sum_congr rfl fun i hi =>
        sum_extraCnt_block hdlt i,
      Finset.sum_range_succ]
    simp only [lt_irrefl, if_false, Nat.add_zero]
    rw [Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.1 hi)]
    exact sum_moveExtra_eq hd0 hdK hmove hbump
  have hsum : ∑ n ∈ Finset.range ((K + 1) * (K + 1)), headCnt K hd mv n =
      (∑ n ∈ Finset.range ((K + 1) * (K + 1)), extraCnt K hd mv n) + (K + 1) * (K + 1) := by
    simp [headCnt, Finset.sum_add_distrib]
  rw [hsum, hextra]
  ring

/-! ### The head-counter chain of the plan -/

/-- **The units of the head counter that the cell `n` of the plan runs**: the unit that answers
the request the tape issues for the cell, and one unit per extra request of the transition taken
there. -/
def planHeadSeg (Q Γ : Type) (K : ℕ) (hd : ℕ → ℕ) (mv : ℕ → Move) (n : ℕ) : List (TMAct Q Γ) :=
  roundStream (headCnt K hd mv n) fun k =>
    headUnitActs Q Γ (headMark K (headBase K hd mv n + k))

/-- **The head-counter chain of the initial task network refines into the units of the plan.** -/
theorem chainYield_planHead (hK : 1 ≤ K) {hd : ℕ → ℕ} {mv : ℕ → Move} (hd0 : hd 0 = 0)
    (hdK : hd K = 0) (hdlt : ∀ i ≤ K, hd i < K)
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) :
    (domainBod N w K).ChainYield (headChainFix (Q := Q) (Γ := Γ) K)
      (roundStream ((K + 1) * (K + 1)) (planHeadSeg Q Γ K hd mv)) := by
  have hchain := chainYield_headChainFix (N := N) (w := w) (Q := Q) (Γ := Γ) hK
    (s := headMark K) (fun _ _ => rfl)
  have hsum := sum_headCnt (K := K) hd0 hdK hdlt hmove hbump
  have hregroup : (roundStream (K * K + 3 * K + 1) fun u => headUnitActs Q Γ (headMark K u)) =
      roundStream ((K + 1) * (K + 1)) (planHeadSeg Q Γ K hd mv) := by
    rw [← hsum]
    exact roundStream_sum (headCnt K hd mv) (fun u => headUnitActs Q Γ (headMark K u))
      ((K + 1) * (K + 1))
  rw [← hregroup]
  exact hchain

/-! ### The cell counters of the plan -/

/-- **The cell counters of the initial task network refine into the decisions of the
witness.** -/
theorem chainYield_planCounters {sym : ℕ → ℕ → Option Γ} {st : ℕ → Q} {hd : ℕ → ℕ}
    {cIn cOut : ℕ → Γ} {mv : ℕ → Move}
    (hstep : ∀ i < K, (st (i + 1), cOut i, mv i) ∈ N.step (st i) (cIn i)) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers (K + 1))]
      (roundMajor2 (K + 1) ((K + 1) * (K + 1))
        (staggeredSegA (K + 1) ((K + 1) * (K + 1)) fun j =>
          counterSegA Q Γ K (planP st hd cIn cOut mv j) (planC sym j))
        fun _ _ => relSyncActs Q Γ) := by
  refine chainYield_checkers_initChain2 fun j hj t ht => ?_
  unfold planP
  split_ifs with h
  · exact Or.inl (chainYield_transActs (hstep t ht))
  · exact Or.inr rfl

/-! ### Interleaving the units of the head counter into the plan -/

lemma interleave_prepend {α : Type} {u x y : List α} (p : List α) (h : Interleave u x y) :
    Interleave u (p ++ x) (p ++ y) := by
  simpa using (Interleave.nil_left p).append_append h

lemma interleave_appendRight {α : Type} {u x y : List α} (q : List α) (h : Interleave u x y) :
    Interleave u (x ++ q) (y ++ q) := by
  simpa using h.append_append (Interleave.nil_left q)

lemma interleave_appendLeft {α : Type} (p u : List α) : Interleave u p (p ++ u) := by
  simpa using (Interleave.nil_left p).append_append (Interleave.nil_right u)

lemma roundStream_nil_of_forall {α : Type} {R : ℕ} {u : ℕ → List α} (h : ∀ r < R, u r = []) :
    roundStream R u = [] := by
  rw [roundStream_congr (t := fun _ => ([] : List α)) h]
  simp

/-- A stream all of whose rounds but one are empty. -/
lemma roundStream_eq_single {α : Type} : ∀ {R j : ℕ} {u : ℕ → List α}, j < R →
    (∀ r < R, r ≠ j → u r = []) → roundStream R u = u j := by
  intro R
  induction R with
  | zero => intro j u hj; omega
  | succ R ih =>
      intro j u hj h
      rw [roundStream_succ]
      rcases Nat.lt_or_ge j R with hjR | hjR
      · rw [h R (by omega) (by omega), ih hjR fun r hr hne => h r (by omega) hne]
        simp
      · have hjR' : j = R := by omega
        subst hjR'
        rw [roundStream_nil_of_forall fun r hr => h r (by omega) (by omega)]
        simp

/-- **The units of the head counter that the cell `n` of the plan runs.** -/
def cellUnits (Q Γ : Type) (K : ℕ) (hd : ℕ → ℕ) (mv : ℕ → Move) (n : ℕ) : List (TMAct Q Γ) :=
  roundStream (headCnt K hd mv n) fun k =>
    headUnitActs Q Γ (headMark K (headBase K hd mv n + k))

/-- **The unit of the head counter that answers the request the tape issues for the cell `n`.**
It sits inside that very request, between the `call` and the `wait` of the tape, which is what
makes the head fact right when the decision of the cell is taken. -/
def cellUnit0 (Q Γ : Type) (K : ℕ) (hd : ℕ → ℕ) (mv : ℕ → Move) (n : ℕ) : List (TMAct Q Γ) :=
  headUnitActs Q Γ (headMark K (headBase K hd mv n))

/-- **The units the transition taken in the cell `n`, if any, runs for its extra requests.** -/
def cellUnitsExtra (Q Γ : Type) (K : ℕ) (hd : ℕ → ℕ) (mv : ℕ → Move) (n : ℕ) :
    List (TMAct Q Γ) :=
  roundStream (extraCnt K hd mv n) fun k =>
    headUnitActs Q Γ (headMark K (headBase K hd mv n + 1 + k))

lemma cellUnits_split {hd : ℕ → ℕ} {mv : ℕ → Move} (n : ℕ) :
    cellUnits Q Γ K hd mv n = cellUnit0 Q Γ K hd mv n ++ cellUnitsExtra Q Γ K hd mv n := by
  have h := roundStream_add 1 (extraCnt K hd mv n) fun k =>
    headUnitActs Q Γ (headMark K (headBase K hd mv n + k))
  rw [roundStream_one] at h
  simp only [cellUnits, headCnt, Nat.add_comm (extraCnt K hd mv n) 1]
  rw [h]
  simp [cellUnit0, cellUnitsExtra, Nat.add_assoc]

lemma planHeadSeg_eq_cellUnits {hd : ℕ → ℕ} {mv : ℕ → Move} (n : ℕ) :
    planHeadSeg Q Γ K hd mv n = cellUnits Q Γ K hd mv n := rfl

/-- **The decision of the counter `j` at time `t`, with the units of the head counter inserted**:
the counter answers the requests of the cell right after its decision — that is what makes the
head fact of the *next* cell right — and the extra requests of a transition are answered one by
one. -/
def planPZ (K : ℕ) (st : ℕ → Q) (hd : ℕ → ℕ) (cIn cOut : ℕ → Γ) (mv : ℕ → Move) (j t : ℕ) :
    List (TMAct Q Γ) :=
  if j = hd t + 1 then
    TMAct.step (st t) (some (cIn t)) (st (t + 1)) (some (cOut t)) ::
      roundStream (moveExtra (mv t)) fun k =>
        TMAct.call SyncKind.head ::
          (headUnitActs Q Γ (headMark K (headBase K hd mv (t * (K + 1) + j) + 1 + k)) ++
            [TMAct.wait SyncKind.head])
  else [TMAct.check TMFact.noHead]

lemma div_mod_cell {t j : ℕ} (hj : j < K + 1) :
    (t * (K + 1) + j) / (K + 1) = t ∧ (t * (K + 1) + j) % (K + 1) = j := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < K + 1),
      Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **The units of a cell interleave with the decision of the counter that is due there.** -/
lemma interleave_planPZ {st : ℕ → Q} {hd : ℕ → ℕ} {cIn cOut : ℕ → Γ} {mv : ℕ → Move}
    {j t : ℕ} (hj : j < K + 1) (ht : t < K) :
    Interleave (cellUnitsExtra Q Γ K hd mv (t * (K + 1) + j))
      (planP st hd cIn cOut mv j t) (planPZ K st hd cIn cOut mv j t) := by
  obtain ⟨hdiv, hmod⟩ := div_mod_cell (K := K) (t := t) hj
  by_cases hcol : j = hd t + 1
  · -- a transition: the extras are answered one by one
    have hextra : extraCnt K hd mv (t * (K + 1) + j) = moveExtra (mv t) := by
      rw [extraCnt, if_pos ⟨by rw [hdiv]; exact ht, by rw [hmod, hdiv]; exact hcol⟩, hdiv]
    have hinner : Interleave
        (roundStream (moveExtra (mv t)) fun k =>
          headUnitActs Q Γ (headMark K (headBase K hd mv (t * (K + 1) + j) + 1 + k)))
        (roundStream (moveExtra (mv t)) fun _ => acquireActs Q Γ SyncKind.head)
        (roundStream (moveExtra (mv t)) fun k =>
          TMAct.call SyncKind.head ::
            (headUnitActs Q Γ (headMark K (headBase K hd mv (t * (K + 1) + j) + 1 + k)) ++
              [TMAct.wait SyncKind.head])) :=
      interleave_roundStream_of_pointwise _ fun k =>
        Interleave.right _ (Interleave.append _ _)
    rw [show cellUnitsExtra Q Γ K hd mv (t * (K + 1) + j) =
        roundStream (moveExtra (mv t)) fun k =>
          headUnitActs Q Γ (headMark K (headBase K hd mv (t * (K + 1) + j) + 1 + k)) by
        rw [cellUnitsExtra, hextra],
      show planP st hd cIn cOut mv j t = transActs st cIn cOut mv t by
        simp [planP, hcol], transActs, planPZ, if_pos hcol]
    exact Interleave.right _ hinner
  · have hextra : extraCnt K hd mv (t * (K + 1) + j) = 0 := by
      rw [extraCnt, if_neg (by rw [hmod, hdiv]; exact fun h => hcol h.2)]
    rw [show planP st hd cIn cOut mv j t = [TMAct.check TMFact.noHead] by simp [planP, hcol],
      planPZ, if_neg hcol, cellUnitsExtra, hextra]
    simpa using Interleave.nil_left _

/-! ### One counter with its head-counter units -/

/-- **The check phase of one cell of one cell counter, with the units of the head counter
inserted**: `tl` are the units the counter emits in its closing cell. -/
def counterSegAZ (Q Γ : Type) (K : ℕ) (PZ : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ)
    (tl : List (TMAct Q Γ)) (r : ℕ) : List (TMAct Q Γ) :=
  if r % (K + 1) ≠ 0 then relCheckActs Q Γ
  else if K = 0 then relCheckActs Q Γ ++ tl
  else if r / (K + 1) = 0 then relCheckActs Q Γ ++ (PZ 0 ++ [chkAct Q Γ (c 0)])
  else if r / (K + 1) < K then
    relCheckActs Q Γ ++ (chkAct Q Γ (c (r / (K + 1) - 1)) ::
      (PZ (r / (K + 1)) ++ [chkAct Q Γ (c (r / (K + 1)))]))
  else relCheckActs Q Γ ++ (chkAct Q Γ (c (K - 1)) :: tl)

/-- The units of the head counter that one counter emits in the cell `r` of its run. -/
def counterUnits (Q Γ : Type) (K : ℕ) (u : ℕ → List (TMAct Q Γ)) (tl : List (TMAct Q Γ))
    (r : ℕ) : List (TMAct Q Γ) :=
  if r % (K + 1) ≠ 0 then []
  else if K = 0 then tl
  else if r / (K + 1) < K then u (r / (K + 1))
  else tl

/-- **The units of a cell interleave with the check phase of the counter that is due there.** -/
lemma interleave_counterSegAZ {P PZ u : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    {tl : List (TMAct Q Γ)} (h : ∀ t < K, Interleave (u t) (P t) (PZ t)) (r : ℕ) :
    Interleave (counterUnits Q Γ K u tl r) (counterSegA Q Γ K P c r)
      (counterSegAZ Q Γ K PZ c tl r) := by
  unfold counterSegA counterSegAZ counterUnits
  by_cases h1 : r % (K + 1) ≠ 0
  · simp only [if_pos h1]
    exact Interleave.nil_left _
  · by_cases h2 : K = 0
    · simp only [if_neg h1, if_pos h2]
      exact interleave_appendLeft _ _
    · by_cases h3 : r / (K + 1) = 0
      · have h4 : r / (K + 1) < K := by omega
        simp only [if_neg h1, if_neg h2, if_pos h3, if_pos h4]
        rw [h3]
        exact interleave_prepend _ (interleave_appendRight _ (h 0 (by omega)))
      · by_cases h4 : r / (K + 1) < K
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          exact interleave_prepend _ (Interleave.right _ (interleave_appendRight _ (h _ h4)))
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          exact interleave_prepend _ (Interleave.right _ (Interleave.nil_right _))

/-- The units of the head counter that one component of a staggered schedule emits in the cell
`r`. -/
def staggeredUnits (i R : ℕ) (uSeg : ℕ → ℕ → List (TMAct Q Γ)) (j r : ℕ) : List (TMAct Q Γ) :=
  if r < j then [] else if r < R - (i - 1 - j) then uSeg j (r - j) else []

lemma interleave_staggeredSegA {i R j : ℕ} {bodyA bodyAZ uSeg : ℕ → ℕ → List (TMAct Q Γ)}
    (h : ∀ r, Interleave (uSeg j r) (bodyA j r) (bodyAZ j r)) (r : ℕ) :
    Interleave (staggeredUnits i R uSeg j r) (staggeredSegA i R bodyA j r)
      (staggeredSegA i R bodyAZ j r) := by
  unfold staggeredUnits staggeredSegA
  split_ifs
  · exact Interleave.nil_left _
  · exact h (r - j)
  · exact Interleave.nil_left _

/-! ### The plan of a witness -/

/-- The data a plan of the repaired encoding is built from: the space–time diagram of the run
and the transitions it takes. -/
structure PlanData (Q Γ : Type) where
  /-- The symbol of the cell `j` of the block `i`. -/
  sym : ℕ → ℕ → Option Γ
  /-- The state of the machine at the time `i`. -/
  st : ℕ → Q
  /-- The position of the head at the time `i`. -/
  hd : ℕ → ℕ
  /-- The symbol the transition of the block `i` reads. -/
  cIn : ℕ → Γ
  /-- The symbol it writes. -/
  cOut : ℕ → Γ
  /-- The movement of its head. -/
  mv : ℕ → Move

namespace PlanData

variable (D : PlanData Q Γ) (K : ℕ)

/-- The check phase of the counter `j` in the cell `n`. -/
def A (j n : ℕ) : List (TMAct Q Γ) :=
  staggeredSegA (K + 1) ((K + 1) * (K + 1))
    (fun j => counterSegA Q Γ K (planP D.st D.hd D.cIn D.cOut D.mv j) (planC D.sym j)) j n

/-- The check phase of the counter `j` in the cell `n`, with the units of the head counter
inserted. -/
def AZ (j n : ℕ) : List (TMAct Q Γ) :=
  staggeredSegA (K + 1) ((K + 1) * (K + 1))
    (fun j => counterSegAZ Q Γ K (planPZ K D.st D.hd D.cIn D.cOut D.mv j) (planC D.sym j)
      (cellUnitsExtra Q Γ K D.hd D.mv (K * (K + 1) + j))) j n

/-- The units of the head counter that the cell `n` runs. -/
def units (n : ℕ) : List (TMAct Q Γ) := cellUnits Q Γ K D.hd D.mv n

/-- The unit that answers the request the tape issues for the cell `n`. -/
def unit0 (n : ℕ) : List (TMAct Q Γ) := cellUnit0 Q Γ K D.hd D.mv n

/-- The units the transition taken in the cell `n`, if any, runs for its extra requests. -/
def unitsExtra (n : ℕ) : List (TMAct Q Γ) := cellUnitsExtra Q Γ K D.hd D.mv n

lemma units_split (n : ℕ) : D.units K n = D.unit0 K n ++ D.unitsExtra K n :=
  cellUnits_split n

/-- The actions of the cell counters in the cell `n`, in the two-phase order. -/
def cSeg (n : ℕ) : List (TMAct Q Γ) :=
  (roundStream (K + 1) fun j => D.A K j n) ++ (roundStream (K + 1) fun _ => relSyncActs Q Γ)

/-- The actions of the tape in the cell `n`. -/
def tSeg (n : ℕ) : List (TMAct Q Γ) := cellRun Q Γ K (planSym K D.sym n)

/-- The actions of the tape and of the cell counters in the cell `n`, merged. -/
def ctSeg (n : ℕ) : List (TMAct Q Γ) :=
  TMAct.assert (planSym K D.sym n) :: (acquireActs Q Γ SyncKind.head ++
    ((roundStream (K + 1) fun j =>
        TMAct.call SyncKind.check :: (D.A K j n ++ [TMAct.wait SyncKind.check])) ++
      (roundStream (K + 1) fun _ =>
        TMAct.call SyncKind.sync :: (relSyncActs Q Γ ++ [TMAct.wait SyncKind.sync]))))

/-- **The whole cell `n` of the plan.** -/
def cell (n : ℕ) : List (TMAct Q Γ) :=
  TMAct.assert (planSym K D.sym n) ::
    ((TMAct.call SyncKind.head :: (cellUnit0 Q Γ K D.hd D.mv n ++ [TMAct.wait SyncKind.head])) ++
      ((roundStream (K + 1) fun j =>
          TMAct.call SyncKind.check :: (D.AZ K j n ++ [TMAct.wait SyncKind.check])) ++
        (roundStream (K + 1) fun _ =>
          TMAct.call SyncKind.sync :: (relSyncActs Q Γ ++ [TMAct.wait SyncKind.sync]))))

/-- **The plan of the witness**: its `(K+1)²` cells, followed by the accepting test. -/
def plan : List (TMAct Q Γ) :=
  roundStream ((K + 1) * (K + 1)) (D.cell K) ++ [TMAct.check (TMFact.st (D.st K))]

/-- The head-counter segment of the cell `n`. -/
def hSeg (n : ℕ) : List (TMAct Q Γ) := planHeadSeg Q Γ K D.hd D.mv n

end PlanData

/-! ### The three chains of the plan, merged -/

namespace PlanData

variable (D : PlanData Q Γ) (K : ℕ)

/-- The units of the head counter that the counter `j` emits in the cell `r` of its run. -/
def uSeg (j r : ℕ) : List (TMAct Q Γ) :=
  counterUnits Q Γ K (fun t => cellUnitsExtra Q Γ K D.hd D.mv (t * (K + 1) + j))
    (cellUnitsExtra Q Γ K D.hd D.mv (K * (K + 1) + j)) r

/-- The units of the head counter that the counter `j` emits in the cell `n` of the plan. -/
def uCell (j n : ℕ) : List (TMAct Q Γ) :=
  staggeredUnits (K + 1) ((K + 1) * (K + 1)) (D.uSeg K) j n

/-- **The units of a cell interleave with the check phase of one counter.** -/
lemma interleave_A_AZ {j : ℕ} (hj : j < K + 1) (n : ℕ) :
    Interleave (D.uCell K j n) (D.A K j n) (D.AZ K j n) :=
  interleave_staggeredSegA
    (fun r => interleave_counterSegAZ (fun _ ht => interleave_planPZ hj ht) r) n

/-- Only the counter whose decision cell it is emits units in the cell `n`. -/
lemma uCell_eq_nil {j n : ℕ} (hj : j < K + 1) (hne : j ≠ n % (K + 1)) : D.uCell K j n = [] := by
  unfold uCell staggeredUnits
  split_ifs with h1 h2
  · rfl
  · have hmod : (n - j) % (K + 1) ≠ 0 := by
      intro hz
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hz
      have hq' : n - j = q * (K + 1) := by rw [hq, Nat.mul_comm]
      have hn : n = q * (K + 1) + j := by omega
      exact hne (by rw [hn, (div_mod_cell (K := K) (t := q) hj).2])
    simp [uSeg, counterUnits, hmod]
  · rfl

/-- The counter whose decision cell it is emits exactly the units of the cell. -/
lemma uCell_eq_units {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    D.uCell K (n % (K + 1)) n = D.unitsExtra K n := by
  set j := n % (K + 1) with hjdef
  have hj : j < K + 1 := Nat.mod_lt _ (by omega)
  have hjn : j ≤ n := Nat.mod_le _ _
  set t := n / (K + 1) with htdef
  have hnt : n = t * (K + 1) + j := by
    rw [htdef, hjdef, Nat.div_add_mod' n (K + 1)]
  have htK : t ≤ K := by
    by_contra hcon
    have : (K + 1) * (K + 1) ≤ t * (K + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have h1 : ¬ n < j := by omega
  have h2 : n < (K + 1) * (K + 1) - (K + 1 - 1 - j) := by
    have : t * (K + 1) ≤ K * (K + 1) := Nat.mul_le_mul_right _ htK
    have hK : K * (K + 1) + (K + 1) = (K + 1) * (K + 1) := by ring
    omega
  have hsub : n - j = t * (K + 1) := by omega
  unfold uCell staggeredUnits
  rw [if_neg h1, if_pos h2, hsub]
  unfold uSeg counterUnits
  have hmod : (t * (K + 1)) % (K + 1) = 0 := Nat.mul_mod_left _ _
  have hdiv : (t * (K + 1)) / (K + 1) = t := Nat.mul_div_cancel _ (by omega)
  rw [if_neg (by simp [hmod])]
  by_cases hK0 : K = 0
  · subst hK0
    have ht0 : t = 0 := by omega
    have hj0 : j = 0 := by omega
    simp [unitsExtra, hnt, ht0, hj0]
  · rw [if_neg hK0, hdiv]
    by_cases htlt : t < K
    · rw [if_pos htlt, unitsExtra, hnt]
    · have : t = K := by omega
      rw [if_neg htlt, unitsExtra, hnt, this]

/-- **The units of the cell `n` are those of the counter that is due there.** -/
lemma roundStream_uCell {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    (roundStream (K + 1) fun j => D.uCell K j n) = D.unitsExtra K n := by
  rw [roundStream_eq_single (j := n % (K + 1)) (Nat.mod_lt _ (by omega))
    fun r hr hne => D.uCell_eq_nil K hr hne]
  exact D.uCell_eq_units K hn

/-- **The tape and the cell counters merge in every cell of the plan.** -/
lemma interleave_ctSeg (n : ℕ) : Interleave (D.cSeg K n) (D.tSeg K n) (D.ctSeg K n) := by
  unfold cSeg tSeg ctSeg cellRun
  refine Interleave.right _ (interleave_prepend _ (Interleave.append_append ?_ ?_))
  · exact interleave_roundStream_of_pointwise _ fun j =>
      Interleave.right _ (Interleave.append _ _)
  · exact interleave_roundStream_of_pointwise _ fun _ =>
      Interleave.right _ (Interleave.append _ _)

/-- **The head counter merges into every cell of the plan.** -/
lemma interleave_cell {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    Interleave (D.hSeg K n) (D.ctSeg K n) (D.cell K n) := by
  have htape : Interleave (D.unit0 K n) (acquireActs Q Γ SyncKind.head)
      (TMAct.call SyncKind.head :: (cellUnit0 Q Γ K D.hd D.mv n ++
        [TMAct.wait SyncKind.head])) :=
    Interleave.right _ (Interleave.append _ _)
  have hrest : Interleave (D.unitsExtra K n)
      ((roundStream (K + 1) fun j =>
          TMAct.call SyncKind.check :: (D.A K j n ++ [TMAct.wait SyncKind.check])) ++
        (roundStream (K + 1) fun _ =>
          TMAct.call SyncKind.sync :: (relSyncActs Q Γ ++ [TMAct.wait SyncKind.sync])))
      ((roundStream (K + 1) fun j =>
          TMAct.call SyncKind.check :: (D.AZ K j n ++ [TMAct.wait SyncKind.check])) ++
        (roundStream (K + 1) fun _ =>
          TMAct.call SyncKind.sync :: (relSyncActs Q Γ ++ [TMAct.wait SyncKind.sync]))) := by
    rw [← D.roundStream_uCell K hn]
    refine interleave_appendRight _ ?_
    exact interleave_roundStream_of_pointwise_lt _ fun j hj =>
      Interleave.right _ (interleave_appendRight _ (D.interleave_A_AZ K hj n))
  rw [hSeg, planHeadSeg_eq_cellUnits, show cellUnits Q Γ K D.hd D.mv n = D.units K n from rfl,
    D.units_split K n, ctSeg, cell]
  exact Interleave.right _ (htape.append_append hrest)

/-! ### The plan is a refinement of the initial task network -/

/-- The accepting test of the plan refines the task `done`. -/
lemma chainYield_planDone (hacc : D.st K ∈ N.accept) :
    (domainBod N w K).ChainYield [Sum.inr TMTask.done]
      [TMAct.check (TMFact.st (D.st K))] := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[[Sum.inl (TMAct.check (TMFact.st (D.st K)))]], ?_,
    gridYield_singleton_iff.2 chainYield_singleton_inl⟩
  rw [bodiesFix_eq_of_ne (by simp)]
  exact ⟨D.st K, hacc, rfl⟩

/-- **The cells of the plan are a refinement of the grid of the initial task network.** -/
theorem gridYield_plan (hwit : IsWitness N w K D.sym D.st D.hd)
    (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hstep : ∀ i < K, (D.st (i + 1), D.cOut i, D.mv i) ∈ N.step (D.st i) (D.cIn i))
    (hmove : ∀ i < K, D.hd (i + 1) = (D.mv i).apply (D.hd i))
    (hbump : ∀ i < K, D.mv i = Move.left → 1 ≤ D.hd i) :
    (domainBod N w K).GridYield (initChainsFix (Q := Q) (Γ := Γ) K)
      (roundStream ((K + 1) * (K + 1)) (D.cell K)) := by
  refine gridYield_initChains_of_rounds (hseg := D.hSeg K) (cseg := D.cSeg K)
    (tseg := D.tSeg K) (ctseg := D.ctSeg K) ?_ ?_ ?_ (fun r _ => D.interleave_ctSeg K r) ?_
  · exact chainYield_planHead (by omega) hwit.headInit hwit.headHome
      (fun i hi => hwit.headLt i hi) hmove hbump
  · exact chainYield_planCounters hstep
  · exact chainYield_planTape hwit hw hwK
  · exact fun r hr => D.interleave_cell K hr

/-- **The repaired problem is solvable as soon as the plan of a witness is executable.**

This is the completeness half of the simulation argument, reduced to the executability of one
explicit plan: everything about the *hierarchy* — that the plan is a refinement of the initial
task network — is proved here. -/
theorem solvable_of_plan_seqApplicable (hwit : IsWitness N w K D.sym D.st D.hd)
    (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hstep : ∀ i < K, (D.st (i + 1), D.cOut i, D.mv i) ∈ N.step (D.st i) (D.cIn i))
    (hmove : ∀ i < K, D.hd (i + 1) = (D.mv i).apply (D.hd i))
    (hbump : ∀ i < K, D.mv i = Move.left → 1 ≤ D.hd i)
    (happ : (problemFix N w K).SeqApplicable (D.plan K) (problemFix N w K).init) :
    (problemFix N w K).Solvable :=
  solvable_fix_of_gridYield (D.gridYield_plan K hwit hw hwK hstep hmove hbump)
    (D.chainYield_planDone K hwit.accept) happ

end PlanData

end TMEnc

end HTN
