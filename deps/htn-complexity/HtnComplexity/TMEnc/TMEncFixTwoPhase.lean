import HtnComplexity.TMEnc.TMEncFixSchedule
/-!
# The two-phase cell-major schedule of the cell counters

`HtnComplexity/TMEnc/TMEncFixSchedule.lean` shows that the *cell-major* schedule of the `K + 1`
cell counters — in every cell, counter `0`, then counter `1`, … each emit their whole segment
for that cell — is a refinement of `checkers (K+1)` (`HTN.TMEnc.chainYield_checkers_cellMajor`).
That order is, however, **not executable**: in one cell the tape issues its `K + 1` requests on
the `check` channel *before* its `K + 1` requests on the `sync` channel, so all counters have to
answer on the `check` channel before any of them answers on the `sync` channel.

This file therefore redoes the assembly for the *two-phase* cell-major schedule

`roundMajor2 i R A B = ⋯ (A 0 r ⋯ A (i-1) r) (B 0 r ⋯ B (i-1) r) ⋯`,

in which every cell `r` consists of the check phase of all components followed by their sync
phase.  The two main results are

* `HTN.TMEnc.chainYield_checkers_backward2` — a staggered two-phase schedule is a refinement of
  `checkers i` (the two-phase analogue of `HTN.TMEnc.chainYield_checkers_backward`);
* `HTN.TMEnc.chainYield_checkers_initChain2` — the two-phase cell-major schedule of the `K + 1`
  cell counters over the `(K+1)²` cells is a refinement of the second chain of the initial task
  network.

The per-cell segments are split accordingly: `HTN.TMEnc.counterSegA` is the check phase of one
cell of one counter (its answer on the `check` channel, and — in a decision cell — the symbol
tests and the transition), and the sync phase is always just `HTN.TMEnc.relSyncActs`.
-/

namespace HTN

variable {α : Type}

/-! ### Two-phase round-major schedules -/

/-- **The two-phase round-major schedule**: in each of the `R` rounds every one of the `i`
components emits its first-phase segment, and then every one of them emits its second-phase
segment. -/
def roundMajor2 (i R : ℕ) (A B : ℕ → ℕ → List α) : List α :=
  roundStream R fun r => (roundStream i fun j => A j r) ++ (roundStream i fun j => B j r)

/-- **Two two-phase streams merge phase by phase.** -/
lemma interleave_roundStream2 (R : ℕ) (a₁ b₁ a₂ b₂ : ℕ → List α) :
    Interleave (roundStream R fun r => a₁ r ++ b₁ r) (roundStream R fun r => a₂ r ++ b₂ r)
      (roundStream R fun r => (a₁ r ++ a₂ r) ++ (b₁ r ++ b₂ r)) := by
  induction R with
  | zero => simpa using Interleave.nil
  | succ R ih =>
      rw [roundStream_succ, roundStream_succ, roundStream_succ]
      exact ih.append_append ((Interleave.append (a₁ R) (a₂ R)).append_append
        (Interleave.append (b₁ R) (b₂ R)))

/-- **A two-phase round-major schedule is an interleaving of the streams of its
components.** -/
lemma interleaveList_roundMajor2 (i R : ℕ) (A B : ℕ → ℕ → List α) :
    InterleaveList ((List.range i).map fun j => roundStream R fun r => A j r ++ B j r)
      (roundMajor2 i R A B) := by
  induction R with
  | zero =>
      refine InterleaveList.of_forall_nil ?_
      intro l hl
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hl
      rfl
  | succ R ih =>
      have hA : InterleaveList ((List.range i).map fun j => A j R)
        (roundStream i fun j => A j R) := interleaveList_flatten _
      have hB : InterleaveList ((List.range i).map fun j => B j R)
        (roundStream i fun j => B j R) := interleaveList_flatten _
      have hlenAB : ((List.range i).map fun j => A j R).length =
          ((List.range i).map fun j => B j R).length := by simp
      have h2 := TMEnc.interleaveList_append_pointwise hA hB hlenAB
      rw [zipWith_map_map] at h2
      have hlen : ((List.range i).map fun j => roundStream R fun r => A j r ++ B j r).length =
          ((List.range i).map fun j => A j R ++ B j R).length := by simp
      have h := TMEnc.interleaveList_append_pointwise ih h2 hlen
      rw [zipWith_map_map] at h
      have hcomp : ((List.range i).map fun j =>
            (roundStream R fun r => A j r ++ B j r) ++ (A j R ++ B j R)) =
          (List.range i).map fun j => roundStream (R + 1) fun r => A j r ++ B j r := by
        refine List.map_congr_left fun j _ => ?_
        rw [roundStream_succ]
      rw [hcomp] at h
      simpa [roundMajor2, roundStream_succ] using h

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- A group of components that all wait during the same `c` cells refines `C_n^{wait^c}`, in
the two-phase order. -/
lemma chainYield_cPar_waitN_of_rounds2 {c n : ℕ} {A B : ℕ → ℕ → List (TMAct Q Γ)}
    (h : ∀ j < n, ∀ r < c,
      (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] (A j r ++ B j r)) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.cPar (TMTask.waitN c) n)]
      (roundMajor2 n c A B) := by
  refine (chainYield_cPar_iff n).2
    ⟨(List.range n).map fun j => roundStream c fun r => A j r ++ B j r, by simp, ?_, ?_⟩
  · intro l hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact chainYield_waitN_of_rounds (h j (List.mem_range.1 hj))
  · exact interleaveList_roundMajor2 n c A B

/-- **Every staggered two-phase cell-major schedule of `i` counters is a refinement of
`checkers i`.**

This is the executable variant of `HTN.TMEnc.chainYield_checkers_backward`: the schedule is
still staggered — component `j` waits during the first `j` and the last `i - 1 - j` cells — but
in every cell all components answer on the `check` channel before any of them answers on the
`sync` channel. -/
theorem chainYield_checkers_backward2 : ∀ (i : ℕ) {R : ℕ} {A B : ℕ → ℕ → List (TMAct Q Γ)},
    Staggered N w K i R (fun j r => A j r ++ B j r) →
      (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers i)] (roundMajor2 i R A B) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro R A B hst
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · -- no counter at all
      have hz : roundMajor2 0 R A B = ([] : List (TMAct Q Γ)) := by
        simp [roundMajor2]
      rw [hz, chainYield_singleton_bod_iff]
      exact ⟨[], by simp [bodiesFix, bodies], by simp⟩
    · -- a single counter, which runs during all `R` cells
      have hb := hst.body 0 (by omega)
      simp only [Nat.sub_zero, Nat.zero_add] at hb
      have hz : roundMajor2 1 R A B = roundStream R fun r => A 0 r ++ B 0 r := by
        simp [roundMajor2]
      rw [hz]
      simpa using hb
  · set m := i / 2 with hm
    have hmi : m < i := Nat.div_lt_self (by omega) (by omega)
    rcases Nat.even_or_odd i with hev | hod
    · -- ### the even case: two groups of `m` counters
      have he : i % 2 = 0 := Nat.even_iff.1 hev
      have him : i = m + m := by omega
      have hm1 : 1 ≤ m := by omega
      have hmR : m ≤ R := by have := hst.le; omega
      set A₂ : ℕ → ℕ → List (TMAct Q Γ) := fun j r => A (m + j) (m + r) with hA₂
      set B₂ : ℕ → ℕ → List (TMAct Q Γ) := fun j r => B (m + j) (m + r) with hB₂
      have hA : Staggered N w K m (R - m) (fun j r => A j r ++ B j r) := by
        refine ⟨by have := hst.le; omega, ?_, ?_, ?_⟩
        · exact fun j hj r hr => hst.lead j (by omega) r hr
        · intro j hj r hr1 hr2
          exact hst.trail j (by omega) r (by omega) (by omega)
        · intro j hj
          have hcnt : R - m - (m - 1 - j) - j = R - (i - 1 - j) - j := by omega
          rw [hcnt]
          exact hst.body j (by omega)
      have hB : Staggered N w K m (R - m) (fun j r => A₂ j r ++ B₂ j r) := by
        refine ⟨by have := hst.le; omega, ?_, ?_, ?_⟩
        · intro j hj r hr
          exact hst.lead (m + j) (by omega) (m + r) (by omega)
        · intro j hj r hr1 hr2
          exact hst.trail (m + j) (by omega) (m + r) (by omega) (by omega)
        · intro j hj
          have hcnt : R - m - (m - 1 - j) - j = R - (i - 1 - (m + j)) - (m + j) := by omega
          have hfun : (fun r => A₂ j (j + r) ++ B₂ j (j + r)) =
              fun r => A (m + j) (m + j + r) ++ B (m + j) (m + j + r) := by
            funext r
            simp [hA₂, hB₂, Nat.add_assoc]
          rw [hcnt, hfun]
          exact hst.body (m + j) (by omega)
      have hyA := ih m hmi hA
      have hyB := ih m hmi hB
      -- the two waiting groups
      have hwA : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN m) m)]
          (roundMajor2 m m (fun j r => A j (R - m + r)) fun j r => B j (R - m + r)) := by
        refine chainYield_cPar_waitN_of_rounds2 ?_
        intro j hj r hr
        exact hst.trail j (by omega) (R - m + r) (by omega) (by omega)
      have hwB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN m) m)]
          (roundMajor2 m m (fun j r => A (m + j) r) fun j r => B (m + j) r) := by
        refine chainYield_cPar_waitN_of_rounds2 ?_
        intro j hj r hr
        exact hst.lead (m + j) (by omega) r (by omega)
      -- the two group streams
      have hsplitA : (roundStream R fun r =>
            (roundStream m fun j => A j r) ++ (roundStream m fun j => B j r)) =
          roundMajor2 m (R - m) A B ++
            (roundMajor2 m m (fun j r => A j (R - m + r)) fun j r => B j (R - m + r)) := by
        have h := roundStream_add (R - m) m fun r =>
          (roundStream m fun j => A j r) ++ (roundStream m fun j => B j r)
        rw [Nat.sub_add_cancel hmR] at h
        exact h
      have hsplitB : (roundStream R fun r =>
            (roundStream m fun j => A (m + j) r) ++ (roundStream m fun j => B (m + j) r)) =
          (roundMajor2 m m (fun j r => A (m + j) r) fun j r => B (m + j) r) ++
            roundMajor2 m (R - m) A₂ B₂ := by
        have h := roundStream_add m (R - m) fun r =>
          (roundStream m fun j => A (m + j) r) ++ (roundStream m fun j => B (m + j) r)
        rw [Nat.add_sub_cancel' hmR] at h
        exact h
      -- the two chains of the method body
      have hchainB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN m) m), Sum.inr (TMTask.checkers m)]
          (roundStream R fun r =>
            (roundStream m fun j => A (m + j) r) ++ (roundStream m fun j => B (m + j) r)) := by
        rw [show [Sum.inr (TMTask.cPar (TMTask.waitN m) m), Sum.inr (TMTask.checkers m)] =
          [(Sum.inr (TMTask.cPar (TMTask.waitN m) m) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.checkers m)] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitB, hwB, hyB⟩
      have hchainA : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.checkers m), Sum.inr (TMTask.cPar (TMTask.waitN m) m)]
          (roundStream R fun r =>
            (roundStream m fun j => A j r) ++ (roundStream m fun j => B j r)) := by
        rw [show [Sum.inr (TMTask.checkers m), Sum.inr (TMTask.cPar (TMTask.waitN m) m)] =
          [(Sum.inr (TMTask.checkers m) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.cPar (TMTask.waitN m) m)] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitA, hyA, hwA⟩
      -- the whole schedule is the interleaving of the two groups
      have hz : roundMajor2 i R A B = roundStream R fun r =>
          ((roundStream m fun j => A j r) ++ (roundStream m fun j => A (m + j) r)) ++
            ((roundStream m fun j => B j r) ++ (roundStream m fun j => B (m + j) r)) := by
        refine roundStream_congr fun r _ => ?_
        rw [show (roundStream i fun j => A j r) =
            (roundStream m fun j => A j r) ++ (roundStream m fun j => A (m + j) r) by
          rw [him, roundStream_add],
          show (roundStream i fun j => B j r) =
            (roundStream m fun j => B j r) ++ (roundStream m fun j => B (m + j) r) by
          rw [him, roundStream_add]]
      have hint : Interleave
          (roundStream R fun r =>
            (roundStream m fun j => A (m + j) r) ++ (roundStream m fun j => B (m + j) r))
          (roundStream R fun r =>
            (roundStream m fun j => A j r) ++ (roundStream m fun j => B j r))
          (roundMajor2 i R A B) := by
        rw [hz]
        exact (interleave_roundStream2 R _ _ _ _).symm
      rw [chainYield_singleton_bod_iff]
      refine ⟨_, (bodiesFix_checkers_even hi he).2 rfl, ?_⟩
      rw [gridYield_cons_iff]
      exact ⟨_, _, hchainB, gridYield_singleton_iff.2 hchainA, hint⟩
    · -- ### the odd case: one counter and a group of `i - 1`
      have ho : i % 2 = 1 := Nat.odd_iff.1 hod
      have hi3 : 3 ≤ i := by omega
      have hiR : i - 1 ≤ R := by have := hst.le; omega
      set A₂ : ℕ → ℕ → List (TMAct Q Γ) := fun j r => A (1 + j) (1 + r) with hA₂
      set B₂ : ℕ → ℕ → List (TMAct Q Γ) := fun j r => B (1 + j) (1 + r) with hB₂
      have hB : Staggered N w K (i - 1) (R - 1) (fun j r => A₂ j r ++ B₂ j r) := by
        refine ⟨by omega, ?_, ?_, ?_⟩
        · intro j hj r hr
          exact hst.lead (1 + j) (by omega) (1 + r) (by omega)
        · intro j hj r hr1 hr2
          exact hst.trail (1 + j) (by omega) (1 + r) (by omega) (by omega)
        · intro j hj
          have hcnt : R - 1 - (i - 1 - 1 - j) - j = R - (i - 1 - (1 + j)) - (1 + j) := by omega
          have hfun : (fun r => A₂ j (j + r) ++ B₂ j (j + r)) =
              fun r => A (1 + j) (1 + j + r) ++ B (1 + j) (1 + j + r) := by
            funext r
            simp [hA₂, hB₂, Nat.add_assoc]
          rw [hcnt, hfun]
          exact hst.body (1 + j) (by omega)
      have hyB := ih (i - 1) (by omega) hB
      -- the group of `i - 1` counters waits during the first cell
      have hwB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1))]
          ((roundStream (i - 1) fun j => A (1 + j) 0) ++
            (roundStream (i - 1) fun j => B (1 + j) 0)) := by
        have h := chainYield_cPar_waitN_of_rounds2 (N := N) (w := w) (K := K) (c := 1)
          (n := i - 1) (A := fun j r => A (1 + j) r) (B := fun j r => B (1 + j) r) ?_
        · simpa [roundMajor2] using h
        · intro j hj r hr
          have hr0 : r = 0 := by omega
          subst hr0
          exact hst.lead (1 + j) (by omega) 0 (by omega)
      -- the single counter of the second chain
      have hbody0 := hst.body 0 (by omega)
      have hb0 : (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers 1)]
          (roundStream (R - (i - 1)) fun r => A 0 r ++ B 0 r) := by
        have hcnt : R - (i - 1 - 0) - 0 = R - (i - 1) := by omega
        have hfun : (fun r => A 0 (0 + r) ++ B 0 (0 + r)) = fun r => A 0 r ++ B 0 r := by
          funext r; simp
        rw [hcnt, hfun] at hbody0
        exact hbody0
      have hw0 : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN (i - 1))]
          (roundStream (i - 1) fun r => A 0 (R - (i - 1) + r) ++ B 0 (R - (i - 1) + r)) := by
        refine chainYield_waitN_of_rounds ?_
        intro r hr
        exact hst.trail 0 (by omega) (R - (i - 1) + r) (by omega) (by omega)
      -- the two group streams
      have hsplitA : (roundStream R fun r => A 0 r ++ B 0 r) =
          (roundStream (R - (i - 1)) fun r => A 0 r ++ B 0 r) ++
            (roundStream (i - 1) fun r =>
              A 0 (R - (i - 1) + r) ++ B 0 (R - (i - 1) + r)) := by
        have hR : R = R - (i - 1) + (i - 1) := by omega
        rw [hR, roundStream_add]
        simp
      have hsplitB : (roundStream R fun r =>
            (roundStream (i - 1) fun j => A (1 + j) r) ++
              (roundStream (i - 1) fun j => B (1 + j) r)) =
          ((roundStream (i - 1) fun j => A (1 + j) 0) ++
            (roundStream (i - 1) fun j => B (1 + j) 0)) ++
              roundMajor2 (i - 1) (R - 1) A₂ B₂ := by
        have hR : R = 1 + (R - 1) := by omega
        rw [hR, roundStream_add]
        simp [roundMajor2, hA₂, hB₂]
      -- the two chains of the method body
      have hchainB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)), Sum.inr (TMTask.checkers (i - 1))]
          (roundStream R fun r =>
            (roundStream (i - 1) fun j => A (1 + j) r) ++
              (roundStream (i - 1) fun j => B (1 + j) r)) := by
        rw [show [Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)),
            Sum.inr (TMTask.checkers (i - 1))] =
          [(Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.checkers (i - 1))] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitB, hwB, hyB⟩
      have hchainA : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN (i - 1))]
          (roundStream R fun r => A 0 r ++ B 0 r) := by
        rw [show [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN (i - 1))] =
          [(Sum.inr (TMTask.checkers 1) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.waitN (i - 1))] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitA, hb0, hw0⟩
      -- the whole schedule is the interleaving of the two groups
      have hz : roundMajor2 i R A B = roundStream R fun r =>
          (A 0 r ++ (roundStream (i - 1) fun j => A (1 + j) r)) ++
            (B 0 r ++ (roundStream (i - 1) fun j => B (1 + j) r)) := by
        refine roundStream_congr fun r _ => ?_
        have hii : i = 1 + (i - 1) := by omega
        rw [show (roundStream i fun j => A j r) =
            A 0 r ++ (roundStream (i - 1) fun j => A (1 + j) r) by
          rw [hii, roundStream_add]; simp,
          show (roundStream i fun j => B j r) =
            B 0 r ++ (roundStream (i - 1) fun j => B (1 + j) r) by
          rw [hii, roundStream_add]; simp]
      have hint : Interleave
          (roundStream R fun r =>
            (roundStream (i - 1) fun j => A (1 + j) r) ++
              (roundStream (i - 1) fun j => B (1 + j) r))
          (roundStream R fun r => A 0 r ++ B 0 r)
          (roundMajor2 i R A B) := by
        rw [hz]
        exact (interleave_roundStream2 R _ _ _ _).symm
      rw [chainYield_singleton_bod_iff]
      refine ⟨_, (bodiesFix_checkers_odd hi ho).2 rfl, ?_⟩
      rw [gridYield_cons_iff]
      exact ⟨_, _, hchainB, gridYield_singleton_iff.2 hchainA, hint⟩

/-! ### The two phases of one cell of one counter -/

/-- **The check phase of one cell of one cell counter**: it answers the request on the `check`
channel and — in a decision cell — closes the previous symbol test, takes its decision and
opens the next symbol test.  The sync phase is always just `HTN.TMEnc.relSyncActs`. -/
def counterSegA (Q Γ : Type) (K : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ) (r : ℕ) :
    List (TMAct Q Γ) :=
  if r % (K + 1) ≠ 0 then relCheckActs Q Γ
  else if K = 0 then relCheckActs Q Γ
  else if r / (K + 1) = 0 then relCheckActs Q Γ ++ (P 0 ++ [chkAct Q Γ (c 0)])
  else if r / (K + 1) < K then
    relCheckActs Q Γ ++ (chkAct Q Γ (c (r / (K + 1) - 1)) ::
      (P (r / (K + 1)) ++ [chkAct Q Γ (c (r / (K + 1)))]))
  else relCheckActs Q Γ ++ [chkAct Q Γ (c (K - 1))]

/-- The two phases of a cell of a counter are its whole segment for that cell. -/
lemma counterSegA_append {K r : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} :
    counterSegA Q Γ K P c r ++ relSyncActs Q Γ = counterSeg Q Γ K P c r := by
  unfold counterSegA counterSeg
  split_ifs <;> simp [waitCellActs_eq, List.append_assoc]

/-- **The check phase of one cell of a staggered schedule.** -/
def staggeredSegA (i R : ℕ) (bodyA : ℕ → ℕ → List (TMAct Q Γ)) (j r : ℕ) : List (TMAct Q Γ) :=
  if r < j then relCheckActs Q Γ
  else if r < R - (i - 1 - j) then bodyA j (r - j)
  else relCheckActs Q Γ

/-- The two phases of a cell of a staggered schedule are its whole segment for that cell. -/
lemma staggeredSegA_append {i R j r : ℕ} {bodyA : ℕ → ℕ → List (TMAct Q Γ)} :
    staggeredSegA i R bodyA j r ++ relSyncActs Q Γ =
      staggeredSeg i R (fun j r => bodyA j r ++ relSyncActs Q Γ) j r := by
  unfold staggeredSegA staggeredSeg
  split_ifs <;> simp [waitCellActs_eq]

/-! ### The cell counters of the initial task network, in the executable order -/

/-- **The cell counters of the initial task network refine into the two-phase cell-major
schedule.**

This is `HTN.TMEnc.chainYield_checkers_initChain` in the order the plan of the completeness
half actually uses: in every cell, all `K + 1` counters answer on the `check` channel — the one
whose decision cell it is also takes its decision there — and only then do they answer on the
`sync` channel. -/
theorem chainYield_checkers_initChain2 {P : ℕ → ℕ → List (TMAct Q Γ)} {c : ℕ → ℕ → Option Γ}
    (hP : ∀ j < K + 1, ∀ t < K,
      (domainBod N w K).ChainYield [Sum.inr TMTask.transition] (P j t) ∨
        P j t = [TMAct.check TMFact.noHead]) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers (K + 1))]
      (roundMajor2 (K + 1) ((K + 1) * (K + 1))
        (staggeredSegA (K + 1) ((K + 1) * (K + 1)) fun j => counterSegA Q Γ K (P j) (c j))
        fun _ _ => relSyncActs Q Γ) := by
  refine chainYield_checkers_backward2 (K + 1) ?_
  have hfun : (fun j r =>
      (staggeredSegA (K + 1) ((K + 1) * (K + 1))
        (fun j => counterSegA Q Γ K (P j) (c j)) j r) ++ relSyncActs Q Γ) =
      staggeredSeg (K + 1) ((K + 1) * (K + 1))
        (fun j => counterSeg Q Γ K (P j) (c j)) := by
    funext j r
    rw [staggeredSegA_append]
    congr 1
    funext j' r'
    exact counterSegA_append
  have hsq : (K + 1) * (K + 1) = K * (K + 1) + (K + 1) := by ring
  rw [hfun]
  refine staggered_staggeredSeg (by omega) ?_
  intro j hj
  rw [show (K + 1) * (K + 1) - (K + 1 - 1) = K * (K + 1) + 1 by omega]
  exact chainYield_checkers_one_cells fun t ht => hP j hj t ht

end TMEnc

end HTN
