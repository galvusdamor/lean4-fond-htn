import HtnComplexity.TMEnc.TMEncFixYield
/-!
# Cell-major schedules: the converse of `chainYield_checkers_forward`

`HtnComplexity/TMEnc/TMEncFixYield.lean` proves that **every** refinement of the cell-counter
task `checkers i` is an interleaving of `i` staggered counters
(`HTN.TMEnc.chainYield_checkers_forward`).  The completeness half of the simulation argument
needs the converse: the concrete *cell-major* schedule — in every cell each of the `i` counters
emits its contribution to that cell, in order — has to be exhibited as a refinement of
`checkers i`.

The plain converse of `chainYield_checkers_forward` is false: the nesting of the recursion also
forces all counters of a group to leave their leading delay at the same cell boundary.  The
cell-major schedule respects exactly that, which is why it is formulated here as a *round*
decomposition:

* `HTN.roundStream R s` — the concatenation of the `R` segments `s 0, …, s (R-1)`;
* `HTN.roundMajor i R seg` — the schedule that runs, cell by cell, the segments of the `i`
  components in order;
* `HTN.TMEnc.Staggered N w K i R seg` — the segments form a staggered family: component `j`
  waits during the first `j` cells, then runs one cell counter, then waits during the last
  `i - 1 - j` cells.

The result is

* `HTN.TMEnc.chainYield_checkers_backward` — **every staggered cell-major schedule of `i`
  counters is a refinement of `checkers i`**,

and, packaged with the counting theorem of `TMEncFixYield.lean`,
`HTN.TMEnc.chainYield_checkers_roundMajor`.

The generic combinatorics this needs — a round-major schedule is an interleaving of the
component streams — is proved first (`HTN.interleaveList_roundMajor`); it belongs to
`HtnPlanning/Interleave/InterleaveList.lean` and is kept here only to avoid rebuilding the whole
library.
-/

namespace HTN

variable {α : Type}

/-! ### Round decompositions -/

/-- The concatenation of the `R` segments `s 0, …, s (R - 1)`. -/
def roundStream (R : ℕ) (s : ℕ → List α) : List α := ((List.range R).map s).flatten

/-- The **round-major schedule**: in each of the `R` rounds every one of the `i` components
emits its segment for that round, the components being taken in order. -/
def roundMajor (i R : ℕ) (seg : ℕ → ℕ → List α) : List α :=
  roundStream R fun r => roundStream i fun j => seg j r

@[simp] lemma roundStream_zero (s : ℕ → List α) : roundStream 0 s = [] := rfl

@[simp] lemma roundStream_one (s : ℕ → List α) : roundStream 1 s = s 0 := by
  simp [roundStream]

@[simp] lemma roundStream_nil (R : ℕ) : roundStream R (fun _ => ([] : List α)) = [] := by
  simp [roundStream]

lemma roundStream_add (a b : ℕ) (s : ℕ → List α) :
    roundStream (a + b) s = roundStream a s ++ roundStream b fun r => s (a + r) := by
  simp [roundStream, List.range_add, Function.comp_def]

lemma roundStream_succ (R : ℕ) (s : ℕ → List α) :
    roundStream (R + 1) s = roundStream R s ++ s R := by
  simp [roundStream_add R 1]

/-- A stream of `a * b` rounds is a stream of `a` blocks of `b` rounds. -/
lemma roundStream_mul (a b : ℕ) (s : ℕ → List α) :
    roundStream (a * b) s = roundStream a fun i => roundStream b fun j => s (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [show (a + 1) * b = a * b + b by ring, roundStream_add, roundStream_succ, ih]

lemma roundStream_congr {R : ℕ} {s t : ℕ → List α} (h : ∀ r < R, s r = t r) :
    roundStream R s = roundStream R t := by
  simp only [roundStream]
  congr 1
  exact List.map_congr_left fun r hr => h r (List.mem_range.1 hr)

/-- Concatenation is an interleaving. -/
lemma interleaveList_flatten (ls : List (List α)) : InterleaveList ls ls.flatten := by
  induction ls with
  | nil => exact InterleaveList.nil
  | cons l ls ih => simpa using InterleaveList.cons ih (Interleave.append l ls.flatten)

lemma zipWith_map_map {β : Type} (l : List β) (f g : β → List α) :
    List.zipWith (· ++ ·) (l.map f) (l.map g) = l.map fun x => f x ++ g x := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- **Two streams that are merged round by round interleave.** -/
lemma interleave_roundStream (R : ℕ) (u v : ℕ → List α) :
    Interleave (roundStream R u) (roundStream R v) (roundStream R fun r => u r ++ v r) := by
  induction R with
  | zero => simpa using Interleave.nil
  | succ R ih =>
      rw [roundStream_succ, roundStream_succ, roundStream_succ]
      exact ih.append_append (Interleave.append (u R) (v R))

/-- **A round-major schedule is an interleaving of the streams of its components.** -/
lemma interleaveList_roundMajor (i R : ℕ) (seg : ℕ → ℕ → List α) :
    InterleaveList ((List.range i).map fun j => roundStream R (seg j)) (roundMajor i R seg) := by
  induction R with
  | zero =>
      refine InterleaveList.of_forall_nil ?_
      intro l hl
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hl
      rfl
  | succ R ih =>
      have h2 : InterleaveList ((List.range i).map fun j => seg j R)
          (roundStream i fun j => seg j R) := interleaveList_flatten _
      have hlen : ((List.range i).map fun j => roundStream R (seg j)).length =
          ((List.range i).map fun j => seg j R).length := by simp
      have := TMEnc.interleaveList_append_pointwise ih h2 hlen
      rw [zipWith_map_map] at this
      have hcomp : ((List.range i).map fun j => roundStream R (seg j) ++ seg j R) =
          (List.range i).map fun j => roundStream (R + 1) (seg j) := by
        refine List.map_congr_left fun j _ => ?_
        rw [roundStream_succ]
      rw [hcomp] at this
      simpa [roundMajor, roundStream_succ] using this

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Staggered cell-major schedules -/

/-- **A staggered cell-major schedule** of `i` cell counters over `R` cells: component `j`
performs a waiting cycle in each of the first `j` cells, then runs one cell counter
(`checkers 1`), and performs a waiting cycle in each of the last `i - 1 - j` cells. -/
structure Staggered (N : NTM Q Γ) (w : List Γ) (K i R : ℕ)
    (seg : ℕ → ℕ → List (TMAct Q Γ)) : Prop where
  /-- There are at least as many cells as the total delay of a counter. -/
  le : i ≤ R + 1
  /-- Before its counter starts, a component waits. -/
  lead : ∀ j < i, ∀ r < j, (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] (seg j r)
  /-- After its counter has finished, a component waits. -/
  trail : ∀ j < i, ∀ r, R - (i - 1 - j) ≤ r → r < R →
    (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] (seg j r)
  /-- In between, the component runs one cell counter. -/
  body : ∀ j < i, (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers 1)]
    (roundStream (R - (i - 1 - j) - j) fun r => seg j (j + r))

/-- The waiting runs of a staggered schedule are refinements of `wait^c`. -/
lemma chainYield_waitN_of_rounds {c : ℕ} {s : ℕ → List (TMAct Q Γ)}
    (h : ∀ r < c, (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] (s r)) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN c)] (roundStream c s) := by
  refine chainYield_waitN_iff.2 ⟨(List.range c).map s, by simp, ?_, rfl⟩
  intro l hl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
  exact h r (List.mem_range.1 hr)

/-- A group of components that all wait during the same `c` cells refines `C_n^{wait^c}`. -/
lemma chainYield_cPar_waitN_of_rounds {c n : ℕ} {seg : ℕ → ℕ → List (TMAct Q Γ)}
    (h : ∀ j < n, ∀ r < c, (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] (seg j r)) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.cPar (TMTask.waitN c) n)]
      (roundMajor n c seg) := by
  refine (chainYield_cPar_iff n).2
    ⟨(List.range n).map fun j => roundStream c (seg j), by simp, ?_, ?_⟩
  · intro l hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact chainYield_waitN_of_rounds (h j (List.mem_range.1 hj))
  · exact interleaveList_roundMajor n c seg

lemma bodiesFix_checkers_even {i : ℕ} (hi : 2 ≤ i) (he : i % 2 = 0)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.checkers i) ↔
      ls = [[Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2)),
          Sum.inr (TMTask.checkers (i / 2))],
        [Sum.inr (TMTask.checkers (i / 2)),
          Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2))]] := by
  have h0 : ¬ (i = 0) := by omega
  have h1 : ¬ (i = 1) := by omega
  simp [bodiesFix, bodies, h0, h1, he]

lemma bodiesFix_checkers_odd {i : ℕ} (hi : 2 ≤ i) (ho : i % 2 = 1)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.checkers i) ↔
      ls = [[Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)), Sum.inr (TMTask.checkers (i - 1))],
        [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN (i - 1))]] := by
  have h0 : ¬ (i = 0) := by omega
  have h1 : ¬ (i = 1) := by omega
  have he : ¬ (i % 2 = 0) := by omega
  simp [bodiesFix, bodies, h0, h1, he]

/-- **Every staggered cell-major schedule of `i` counters is a refinement of `checkers i`.**

This is the converse of `HTN.TMEnc.chainYield_checkers_forward` for the schedules the
completeness half of the simulation argument produces. -/
theorem chainYield_checkers_backward : ∀ (i : ℕ) {R : ℕ} {seg : ℕ → ℕ → List (TMAct Q Γ)},
    Staggered N w K i R seg →
      (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers i)] (roundMajor i R seg) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro R seg hst
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · -- no counter at all
      have hz : roundMajor 0 R seg = ([] : List (TMAct Q Γ)) := by
        simp [roundMajor]
      rw [hz, chainYield_singleton_bod_iff]
      exact ⟨[], by simp [bodiesFix, bodies], by simp⟩
    · -- a single counter, which runs during all `R` cells
      have hb := hst.body 0 (by omega)
      simp only [Nat.sub_zero, Nat.zero_add] at hb
      have hz : roundMajor 1 R seg = roundStream R fun r => seg 0 r := by
        simp [roundMajor]
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
      set segB : ℕ → ℕ → List (TMAct Q Γ) := fun j r => seg (m + j) (m + r) with hsegB
      -- the two recursive schedules
      have hA : Staggered N w K m (R - m) seg := by
        refine ⟨by have := hst.le; omega, ?_, ?_, ?_⟩
        · exact fun j hj r hr => hst.lead j (by omega) r hr
        · intro j hj r hr1 hr2
          exact hst.trail j (by omega) r (by omega) (by omega)
        · intro j hj
          have hcnt : R - m - (m - 1 - j) - j = R - (i - 1 - j) - j := by omega
          rw [hcnt]
          exact hst.body j (by omega)
      have hB : Staggered N w K m (R - m) segB := by
        refine ⟨by have := hst.le; omega, ?_, ?_, ?_⟩
        · intro j hj r hr
          exact hst.lead (m + j) (by omega) (m + r) (by omega)
        · intro j hj r hr1 hr2
          exact hst.trail (m + j) (by omega) (m + r) (by omega) (by omega)
        · intro j hj
          have hcnt : R - m - (m - 1 - j) - j = R - (i - 1 - (m + j)) - (m + j) := by omega
          have hfun : (fun r => segB j (j + r)) = fun r => seg (m + j) (m + j + r) := by
            funext r
            simp [hsegB, Nat.add_assoc]
          rw [hcnt, hfun]
          exact hst.body (m + j) (by omega)
      have hyA := ih m hmi hA
      have hyB := ih m hmi hB
      -- the two waiting groups
      have hwA : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN m) m)]
          (roundMajor m m fun j r => seg j (R - m + r)) := by
        refine chainYield_cPar_waitN_of_rounds ?_
        intro j hj r hr
        exact hst.trail j (by omega) (R - m + r) (by omega) (by omega)
      have hwB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN m) m)]
          (roundMajor m m fun j r => seg (m + j) r) := by
        refine chainYield_cPar_waitN_of_rounds ?_
        intro j hj r hr
        exact hst.lead (m + j) (by omega) r (by omega)
      -- the two group streams
      have hsplitA : (roundStream R fun r => roundStream m fun j => seg j r) =
          roundMajor m (R - m) seg ++ (roundMajor m m fun j r => seg j (R - m + r)) := by
        have h := roundStream_add (R - m) m fun r => roundStream m fun j => seg j r
        rw [Nat.sub_add_cancel hmR] at h
        exact h
      have hsplitB : (roundStream R fun r => roundStream m fun j => seg (m + j) r) =
          (roundMajor m m fun j r => seg (m + j) r) ++ roundMajor m (R - m) segB := by
        have h := roundStream_add m (R - m) fun r => roundStream m fun j => seg (m + j) r
        rw [Nat.add_sub_cancel' hmR] at h
        exact h
      -- the two chains of the method body
      have hchainB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN m) m), Sum.inr (TMTask.checkers m)]
          (roundStream R fun r => roundStream m fun j => seg (m + j) r) := by
        rw [show [Sum.inr (TMTask.cPar (TMTask.waitN m) m), Sum.inr (TMTask.checkers m)] =
          [(Sum.inr (TMTask.cPar (TMTask.waitN m) m) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.checkers m)] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitB, hwB, hyB⟩
      have hchainA : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.checkers m), Sum.inr (TMTask.cPar (TMTask.waitN m) m)]
          (roundStream R fun r => roundStream m fun j => seg j r) := by
        rw [show [Sum.inr (TMTask.checkers m), Sum.inr (TMTask.cPar (TMTask.waitN m) m)] =
          [(Sum.inr (TMTask.checkers m) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.cPar (TMTask.waitN m) m)] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitA, hyA, hwA⟩
      -- the whole schedule is the interleaving of the two groups
      have hround : ∀ r, (roundStream i fun j => seg j r) =
          (roundStream m fun j => seg j r) ++ (roundStream m fun j => seg (m + j) r) := by
        intro r
        rw [him, roundStream_add]
      have hz : roundMajor i R seg =
          roundStream R fun r => (roundStream m fun j => seg j r) ++
            (roundStream m fun j => seg (m + j) r) := by
        refine roundStream_congr fun r _ => hround r
      have hint : Interleave (roundStream R fun r => roundStream m fun j => seg (m + j) r)
          (roundStream R fun r => roundStream m fun j => seg j r) (roundMajor i R seg) := by
        rw [hz]
        exact (interleave_roundStream R _ _).symm
      rw [chainYield_singleton_bod_iff]
      refine ⟨_, (bodiesFix_checkers_even hi he).2 rfl, ?_⟩
      rw [gridYield_cons_iff]
      exact ⟨_, _, hchainB, gridYield_singleton_iff.2 hchainA, hint⟩
    · -- ### the odd case: one counter and a group of `i - 1`
      have ho : i % 2 = 1 := Nat.odd_iff.1 hod
      have hi3 : 3 ≤ i := by omega
      have hiR : i - 1 ≤ R := by have := hst.le; omega
      set segB : ℕ → ℕ → List (TMAct Q Γ) := fun j r => seg (1 + j) (1 + r) with hsegB
      have hB : Staggered N w K (i - 1) (R - 1) segB := by
        refine ⟨by omega, ?_, ?_, ?_⟩
        · intro j hj r hr
          exact hst.lead (1 + j) (by omega) (1 + r) (by omega)
        · intro j hj r hr1 hr2
          exact hst.trail (1 + j) (by omega) (1 + r) (by omega) (by omega)
        · intro j hj
          have hcnt : R - 1 - (i - 1 - 1 - j) - j = R - (i - 1 - (1 + j)) - (1 + j) := by omega
          have hfun : (fun r => segB j (j + r)) = fun r => seg (1 + j) (1 + j + r) := by
            funext r
            simp [hsegB, Nat.add_assoc]
          rw [hcnt, hfun]
          exact hst.body (1 + j) (by omega)
      have hyB := ih (i - 1) (by omega) hB
      -- the group of `i - 1` counters waits during the first cell
      have hwB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1))]
          (roundStream (i - 1) fun j => seg (1 + j) 0) := by
        refine (chainYield_cPar_iff (i - 1)).2
          ⟨(List.range (i - 1)).map fun j => seg (1 + j) 0, by simp, ?_, ?_⟩
        · intro l hl
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
          have hj' : j < i - 1 := List.mem_range.1 hj
          have := hst.lead (1 + j) (by omega) 0 (by omega)
          simpa using chainYield_waitN_of_rounds (c := 1) (s := fun _ => seg (1 + j) 0)
            (fun _ _ => this)
        · exact interleaveList_flatten _
      -- the single counter of the second chain
      have hbody0 := hst.body 0 (by omega)
      have hb0 : (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers 1)]
          (roundStream (R - (i - 1)) fun r => seg 0 r) := by
        have hcnt : R - (i - 1 - 0) - 0 = R - (i - 1) := by omega
        have hfun : (fun r => seg 0 (0 + r)) = fun r => seg 0 r := by
          funext r; simp
        rw [hcnt, hfun] at hbody0
        exact hbody0
      have hw0 : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN (i - 1))]
          (roundStream (i - 1) fun r => seg 0 (R - (i - 1) + r)) := by
        refine chainYield_waitN_of_rounds ?_
        intro r hr
        exact hst.trail 0 (by omega) (R - (i - 1) + r) (by omega) (by omega)
      -- the two group streams
      have hsplitA : (roundStream R fun r => seg 0 r) =
          (roundStream (R - (i - 1)) fun r => seg 0 r) ++
            (roundStream (i - 1) fun r => seg 0 (R - (i - 1) + r)) := by
        have hR : R = R - (i - 1) + (i - 1) := by omega
        rw [hR, roundStream_add]
        simp
      have hsplitB : (roundStream R fun r => roundStream (i - 1) fun j => seg (1 + j) r) =
          (roundStream (i - 1) fun j => seg (1 + j) 0) ++ roundMajor (i - 1) (R - 1) segB := by
        have hR : R = 1 + (R - 1) := by omega
        rw [hR, roundStream_add]
        simp [roundMajor, hsegB]
      -- the two chains of the method body
      have hchainB : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)), Sum.inr (TMTask.checkers (i - 1))]
          (roundStream R fun r => roundStream (i - 1) fun j => seg (1 + j) r) := by
        rw [show [Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)),
            Sum.inr (TMTask.checkers (i - 1))] =
          [(Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.checkers (i - 1))] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitB, hwB, hyB⟩
      have hchainA : (domainBod N w K).ChainYield
          [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN (i - 1))]
          (roundStream R fun r => seg 0 r) := by
        rw [show [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN (i - 1))] =
          [(Sum.inr (TMTask.checkers 1) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.waitN (i - 1))] from rfl, chainYield_append_iff]
        exact ⟨_, _, hsplitA, hb0, hw0⟩
      -- the whole schedule is the interleaving of the two groups
      have hround : ∀ r, (roundStream i fun j => seg j r) =
          seg 0 r ++ (roundStream (i - 1) fun j => seg (1 + j) r) := by
        intro r
        have hii : i = 1 + (i - 1) := by omega
        rw [hii, roundStream_add]
        simp
      have hz : roundMajor i R seg =
          roundStream R fun r => seg 0 r ++ (roundStream (i - 1) fun j => seg (1 + j) r) :=
        roundStream_congr fun r _ => hround r
      have hint : Interleave (roundStream R fun r => roundStream (i - 1) fun j => seg (1 + j) r)
          (roundStream R fun r => seg 0 r) (roundMajor i R seg) := by
        rw [hz]
        exact (interleave_roundStream R _ _).symm
      rw [chainYield_singleton_bod_iff]
      refine ⟨_, (bodiesFix_checkers_odd hi ho).2 rfl, ?_⟩
      rw [gridYield_cons_iff]
      exact ⟨_, _, hchainB, gridYield_singleton_iff.2 hchainA, hint⟩

/-- **The refinements of `checkers i` are exactly the staggered interleavings of `i` cell
counters**, in the two directions the two halves of the simulation argument need: every
refinement is such an interleaving (`chainYield_checkers_forward`), and every cell-major
staggered schedule is a refinement. -/
theorem chainYield_checkers_roundMajor {i R : ℕ} {seg : ℕ → ℕ → List (TMAct Q Γ)}
    (h : Staggered N w K i R seg) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers i)] (roundMajor i R seg) ∧
      ∃ (ps : List (ℕ × ℕ)) (ass : List (List (TMAct Q Γ))),
        ps.Perm ((List.range i).map fun j => (j, i - 1 - j)) ∧
          CounterRuns N w K ps ass ∧ InterleaveList ass (roundMajor i R seg) := by
  have hy := chainYield_checkers_backward i h
  exact ⟨hy, chainYield_checkers_forward i hy⟩

/-! ### The waiting cycle, explicitly

A counter that is being delayed performs one waiting cycle per cell, and a waiting cycle has
exactly one refinement: it answers the request on the `check` channel and then the one on the
`sync` channel. -/

/-- A synchronisation task has exactly one refinement: the answer to one request. -/
lemma chainYield_release_iff {x : SyncKind} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.release x)] as ↔
      as = [TMAct.start x, TMAct.respond x] := by
  rw [chainYield_singleton_bod_iff]
  constructor
  · rintro ⟨ls, hls, hy⟩
    have hls' : ls = [[Sum.inl (TMAct.start x), Sum.inl (TMAct.respond x)]] := by
      simpa [bodiesFix, bodies] using hls
    subst hls'
    rw [gridYield_singleton_iff, chainYield_cons_inl_iff] at hy
    obtain ⟨as', rfl, hy⟩ := hy
    rw [chainYield_cons_inl_iff] at hy
    obtain ⟨as'', rfl, hy⟩ := hy
    rw [chainYield_nil_iff] at hy
    subst hy
    rfl
  · rintro rfl
    refine ⟨[[Sum.inl (TMAct.start x), Sum.inl (TMAct.respond x)]],
      by simp [bodiesFix, bodies], gridYield_singleton_iff.2 ?_⟩
    exact chainYield_cons_inl_iff.2 ⟨_, rfl,
      chainYield_cons_inl_iff.2 ⟨[], rfl, chainYield_nil_iff.2 rfl⟩⟩

/-- The four actions of one waiting cycle: the answers to the two requests of a cell. -/
def waitCellActs (Q Γ : Type) : List (TMAct Q Γ) :=
  [TMAct.start SyncKind.check, TMAct.respond SyncKind.check,
    TMAct.start SyncKind.sync, TMAct.respond SyncKind.sync]

/-- **A waiting cycle has exactly one refinement.** -/
lemma chainYield_waitCell_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] as ↔ as = waitCellActs Q Γ := by
  rw [chainYield_singleton_bod_iff]
  constructor
  · rintro ⟨ls, hls, hy⟩
    have hls' : ls = [[Sum.inr (TMTask.release SyncKind.check),
        Sum.inr (TMTask.release SyncKind.sync)]] := by
      simpa [bodiesFix, bodies] using hls
    subst hls'
    rw [gridYield_singleton_iff, show
      [Sum.inr (TMTask.release SyncKind.check), Sum.inr (TMTask.release SyncKind.sync)] =
        [(Sum.inr (TMTask.release SyncKind.check) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
          [Sum.inr (TMTask.release SyncKind.sync)] from rfl, chainYield_append_iff] at hy
    obtain ⟨u, v, rfl, hu, hv⟩ := hy
    rw [chainYield_release_iff] at hu hv
    subst hu; subst hv
    rfl
  · rintro rfl
    refine ⟨[[Sum.inr (TMTask.release SyncKind.check), Sum.inr (TMTask.release SyncKind.sync)]],
      by simp [bodiesFix, bodies], gridYield_singleton_iff.2 ?_⟩
    rw [show [Sum.inr (TMTask.release SyncKind.check), Sum.inr (TMTask.release SyncKind.sync)] =
      [(Sum.inr (TMTask.release SyncKind.check) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
        [Sum.inr (TMTask.release SyncKind.sync)] from rfl, chainYield_append_iff]
    exact ⟨_, _, rfl, chainYield_release_iff.2 rfl, chainYield_release_iff.2 rfl⟩

lemma chainYield_waitCellActs :
    (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] (waitCellActs Q Γ) :=
  chainYield_waitCell_iff.2 rfl

/-! ### Assembling the schedule from the runs of the single counters -/

/-- **The cell-major schedule of `i` cell counters over `R` cells**: counter `j` waits during
the first `j` cells, runs its counter — whose segments over the remaining `R - (i - 1)` cells
are `body j` — and waits during the last `i - 1 - j` cells. -/
def staggeredSeg (i R : ℕ) (body : ℕ → ℕ → List (TMAct Q Γ)) (j r : ℕ) : List (TMAct Q Γ) :=
  if r < j then waitCellActs Q Γ
  else if r < R - (i - 1 - j) then body j (r - j)
  else waitCellActs Q Γ

/-- **The cell-major schedule of `i` counter runs is staggered.** -/
theorem staggered_staggeredSeg {i R : ℕ} (hiR : i ≤ R + 1)
    {body : ℕ → ℕ → List (TMAct Q Γ)}
    (hbody : ∀ j < i, (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers 1)]
      (roundStream (R - (i - 1)) (body j))) :
    Staggered N w K i R (staggeredSeg i R body) := by
  refine ⟨hiR, ?_, ?_, ?_⟩
  · intro j hj r hr
    rw [show staggeredSeg i R body j r = waitCellActs Q Γ by simp [staggeredSeg, hr]]
    exact chainYield_waitCellActs
  · intro j hj r hr1 hr2
    have hnl : ¬ r < j := by omega
    have hnb : ¬ r < R - (i - 1 - j) := by omega
    rw [show staggeredSeg i R body j r = waitCellActs Q Γ by simp [staggeredSeg, hnl, hnb]]
    exact chainYield_waitCellActs
  · intro j hj
    have hcnt : R - (i - 1 - j) - j = R - (i - 1) := by omega
    have hseg : ∀ r < R - (i - 1),
        staggeredSeg i R body j (j + r) = body j r := by
      intro r hr
      have hnl : ¬ j + r < j := by omega
      have hb : j + r < R - (i - 1 - j) := by omega
      simp [staggeredSeg, hnl, hb]
    rw [hcnt, roundStream_congr hseg]
    exact hbody j hj

/-- **The cell-major schedule of `i` cell counters is a refinement of `checkers i`.**

This is the form in which the completeness half of the simulation argument uses
`HTN.TMEnc.chainYield_checkers_backward`: it only has to produce, for each counter, a
decomposition of one counter run into the `R - (i - 1)` cells during which it is active. -/
theorem chainYield_checkers_cellMajor {i R : ℕ} (hiR : i ≤ R + 1)
    {body : ℕ → ℕ → List (TMAct Q Γ)}
    (hbody : ∀ j < i, (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers 1)]
      (roundStream (R - (i - 1)) (body j))) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers i)]
      (roundMajor i R (staggeredSeg i R body)) :=
  chainYield_checkers_backward i (staggered_staggeredSeg hiR hbody)

/-! ### One cell counter, cell by cell

The body of one cell counter is `release check ; C^K_{transitionAndCheck} ; release sync`, and
`transitionAndCheck` unfolds into a decision (a transition of the machine, or the test that the
head is elsewhere) followed by the gadget `chk`, which tests the symbol of the current cell,
answers the request on the `sync` channel, waits for `K` cells and answers the request on the
`check` channel before testing the symbol again — the symbol of the cell `K + 1` positions
later.  A counter therefore answers exactly one pair of requests per cell, and its run splits
into `K(K+1) + 1` cells: the `K` decisions are taken `K + 1` cells apart. -/

/-- The test action of a `chk` gadget. -/
def chkAct (Q Γ : Type) (c : Option Γ) : TMAct Q Γ := TMAct.check (TMFact.sym c)

/-- The two actions that answer a request on the `check` channel. -/
def relCheckActs (Q Γ : Type) : List (TMAct Q Γ) :=
  [TMAct.start SyncKind.check, TMAct.respond SyncKind.check]

/-- The two actions that answer a request on the `sync` channel. -/
def relSyncActs (Q Γ : Type) : List (TMAct Q Γ) :=
  [TMAct.start SyncKind.sync, TMAct.respond SyncKind.sync]

lemma waitCellActs_eq : waitCellActs Q Γ = relCheckActs Q Γ ++ relSyncActs Q Γ := rfl

/-- The actions of one `chk` gadget. -/
def chkRun (Q Γ : Type) (K : ℕ) (c : Option Γ) : List (TMAct Q Γ) :=
  chkAct Q Γ c :: (relSyncActs Q Γ ++ (roundStream K (fun _ => waitCellActs Q Γ) ++
    (relCheckActs Q Γ ++ [chkAct Q Γ c])))

lemma chainYield_singleton_inl {a : TMAct Q Γ} :
    (domainBod N w K).ChainYield [Sum.inl a] [a] :=
  chainYield_cons_inl_iff.2 ⟨[], rfl, chainYield_nil_iff.2 rfl⟩

lemma chainYield_app {xs ys : List (TMAct Q Γ ⊕ TMTask Q Γ)} {as bs : List (TMAct Q Γ)}
    (h₁ : (domainBod N w K).ChainYield xs as) (h₂ : (domainBod N w K).ChainYield ys bs) :
    (domainBod N w K).ChainYield (xs ++ ys) (as ++ bs) :=
  chainYield_append_iff.2 ⟨as, bs, rfl, h₁, h₂⟩

lemma chainYield_waitN_waits {n : ℕ} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN n)]
      (roundStream n fun _ => waitCellActs Q Γ) :=
  chainYield_waitN_of_rounds fun _ _ => chainYield_waitCellActs

/-- **The `chk` gadget refines into its run.** -/
lemma chainYield_chk {c : Option Γ} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.chk] (chkRun Q Γ K c) := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[[Sum.inl (TMAct.check (TMFact.sym c)), Sum.inr (TMTask.release SyncKind.sync),
      Sum.inr (TMTask.waitN K), Sum.inr (TMTask.release SyncKind.check),
      Sum.inl (TMAct.check (TMFact.sym c))]], ⟨c, rfl⟩, gridYield_singleton_iff.2 ?_⟩
  have h := chainYield_app (N := N) (w := w) (K := K)
    (chainYield_singleton_inl (a := chkAct Q Γ c))
    (chainYield_app ((chainYield_release_iff (x := SyncKind.sync)).2 rfl)
      (chainYield_app (chainYield_waitN_waits (n := K))
        (chainYield_app ((chainYield_release_iff (x := SyncKind.check)).2 rfl)
          (chainYield_singleton_inl (a := chkAct Q Γ c)))))
  simpa [chkRun, chkAct, relSyncActs, relCheckActs] using h

/-- **A step of a counter refines `transitionAndCheck`**, whichever of the two decisions it
takes: a transition of the machine, or the test that the head is elsewhere. -/
lemma chainYield_transitionAndCheck {p : List (TMAct Q Γ)} {c : Option Γ}
    (hp : (domainBod N w K).ChainYield [Sum.inr TMTask.transition] p ∨
      p = [TMAct.check TMFact.noHead]) :
    (domainBod N w K).ChainYield [Sum.inr TMTask.transitionAndCheck] (p ++ chkRun Q Γ K c) := by
  rw [chainYield_singleton_bod_iff]
  rcases hp with hp | rfl
  · refine ⟨[[Sum.inr TMTask.transition, Sum.inr TMTask.chk]], by simp [bodiesFix, bodies],
      gridYield_singleton_iff.2 ?_⟩
    simpa using chainYield_app hp chainYield_chk
  · refine ⟨[[Sum.inl (TMAct.check TMFact.noHead), Sum.inr TMTask.chk]],
      by simp [bodiesFix, bodies], gridYield_singleton_iff.2 ?_⟩
    simpa using chainYield_app chainYield_singleton_inl chainYield_chk

/-- The actions one counter performs for its decision number `t`: the decision `P t` and the
`chk` gadget that compares the symbol of the current cell with the one `K + 1` cells later. -/
def stepRun (Q Γ : Type) (K : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ) (t : ℕ) :
    List (TMAct Q Γ) :=
  P t ++ chkRun Q Γ K (c t)

/-- **The cells of one cell counter.**  In every cell the counter answers the request on the
`check` channel and then the one on the `sync` channel; in every `(K+1)`-st cell it also takes
a decision — the first one opens the run, the last one closes it. -/
def counterSeg (Q Γ : Type) (K : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ) (r : ℕ) :
    List (TMAct Q Γ) :=
  if r % (K + 1) ≠ 0 then waitCellActs Q Γ
  else if K = 0 then relCheckActs Q Γ ++ relSyncActs Q Γ
  else if r / (K + 1) = 0 then
    relCheckActs Q Γ ++ (P 0 ++ (chkAct Q Γ (c 0) :: relSyncActs Q Γ))
  else if r / (K + 1) < K then
    relCheckActs Q Γ ++ (chkAct Q Γ (c (r / (K + 1) - 1)) ::
      (P (r / (K + 1)) ++ (chkAct Q Γ (c (r / (K + 1))) :: relSyncActs Q Γ)))
  else relCheckActs Q Γ ++ (chkAct Q Γ (c (K - 1)) :: relSyncActs Q Γ)

lemma counterSeg_wait {K r : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (h : r % (K + 1) ≠ 0) : counterSeg Q Γ K P c r = waitCellActs Q Γ := by
  simp [counterSeg, h]

/-- The cells of a counter that are not decision cells are waiting cycles. -/
lemma counterSeg_waits {K t : ℕ} {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} :
    (roundStream K fun r => counterSeg Q Γ K P c (t * (K + 1) + 1 + r)) =
      roundStream K fun _ => waitCellActs Q Γ := by
  refine roundStream_congr fun r hr => ?_
  refine counterSeg_wait ?_
  have h1 : (t * (K + 1) + 1 + r) % (K + 1) = (1 + r) % (K + 1) := by
    rw [show t * (K + 1) + 1 + r = 1 + r + t * (K + 1) by ring, Nat.add_mul_mod_self_right]
  rw [h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The tail of the run of a counter, from its decision number `t` on. -/
lemma counterSeg_tail {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (hK : 1 ≤ K) :
    ∀ n t : ℕ, t + n = K → 1 ≤ t →
      (roundStream (n * (K + 1) + 1) fun r => counterSeg Q Γ K P c (t * (K + 1) + r)) =
        relCheckActs Q Γ ++ (chkAct Q Γ (c (t - 1)) ::
          ((roundStream n fun k => stepRun Q Γ K P c (t + k)) ++ relSyncActs Q Γ)) := by
  intro n
  induction n with
  | zero =>
      intro t htn ht1
      have htK : t = K := by omega
      subst htK
      have hmod : (t * (t + 1)) % (t + 1) = 0 := by simp [Nat.mul_mod_left]
      have hdiv : (t * (t + 1)) / (t + 1) = t := by
        simp [Nat.mul_div_cancel _ (by omega : 0 < t + 1)]
      simp only [Nat.zero_mul, Nat.zero_add, roundStream_one, roundStream_zero,
        List.nil_append, counterSeg]
      have h0 : ¬ (t = 0) := by omega
      simp [h0]
  | succ n ih =>
      intro t htn ht1
      have htK : t < K := by omega
      have hsplit : (n + 1) * (K + 1) + 1 = 1 + (K + (n * (K + 1) + 1)) := by ring
      rw [hsplit, roundStream_add, roundStream_add, roundStream_one]
      have hmod : (t * (K + 1)) % (K + 1) = 0 := by simp [Nat.mul_mod_left]
      have hdiv : (t * (K + 1)) / (K + 1) = t := Nat.mul_div_cancel _ (by omega)
      have hfirst : counterSeg Q Γ K P c (t * (K + 1) + 0) =
          relCheckActs Q Γ ++ (chkAct Q Γ (c (t - 1)) ::
            (P t ++ (chkAct Q Γ (c t) :: relSyncActs Q Γ))) := by
        have h0 : ¬ (t = 0) := by omega
        have hK0 : ¬ (K = 0) := by omega
        simp only [Nat.add_zero, counterSeg, hmod, hdiv]
        simp [h0, hK0, htK]
      have hwaits : (roundStream K fun r => counterSeg Q Γ K P c (t * (K + 1) + (0 + 1 + r))) =
          roundStream K fun _ => waitCellActs Q Γ := by
        have := counterSeg_waits (Q := Q) (Γ := Γ) (K := K) (t := t) (P := P) (c := c)
        simpa [Nat.add_assoc] using this
      have hrest : (roundStream (n * (K + 1) + 1) fun r =>
            counterSeg Q Γ K P c (t * (K + 1) + (0 + 1 + (K + r)))) =
          relCheckActs Q Γ ++ (chkAct Q Γ (c t) ::
            ((roundStream n fun k => stepRun Q Γ K P c (t + 1 + k)) ++ relSyncActs Q Γ)) := by
        have hidx : ∀ r, t * (K + 1) + (0 + 1 + (K + r)) = (t + 1) * (K + 1) + r := by
          intro r; ring
        have h := ih (t + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at h
        simpa [hidx] using h
      rw [hfirst, hwaits, hrest]
      have hstep : (roundStream (n + 1) fun k => stepRun Q Γ K P c (t + k)) =
          stepRun Q Γ K P c t ++ roundStream n fun k => stepRun Q Γ K P c (t + 1 + k) := by
        have h := roundStream_add 1 n fun k => stepRun Q Γ K P c (t + k)
        simpa [Nat.add_comm 1 n, Nat.add_assoc, Nat.add_left_comm] using h
      rw [hstep]
      simp [stepRun, chkRun, List.append_assoc]

/-- **The run of one cell counter, decomposed into its `K(K+1) + 1` cells.** -/
theorem counterSeg_run {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} :
    (roundStream (K * (K + 1) + 1) (counterSeg Q Γ K P c)) =
      relCheckActs Q Γ ++ ((roundStream K fun k => stepRun Q Γ K P c k) ++ relSyncActs Q Γ) := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp [counterSeg]
  · have hsplit : K * (K + 1) + 1 = 1 + (K + ((K - 1) * (K + 1) + 1)) := by
      cases K with
      | zero => omega
      | succ k => simp; ring
    rw [hsplit, roundStream_add, roundStream_add, roundStream_one]
    have hfirst : counterSeg Q Γ K P c 0 =
        relCheckActs Q Γ ++ (P 0 ++ (chkAct Q Γ (c 0) :: relSyncActs Q Γ)) := by
      have hK0 : ¬ (K = 0) := by omega
      simp [counterSeg, hK0]
    have hwaits : (roundStream K fun r => counterSeg Q Γ K P c (0 + 1 + r)) =
        roundStream K fun _ => waitCellActs Q Γ := by
      have := counterSeg_waits (Q := Q) (Γ := Γ) (K := K) (t := 0) (P := P) (c := c)
      simpa using this
    have hrest : (roundStream ((K - 1) * (K + 1) + 1) fun r =>
          counterSeg Q Γ K P c (0 + 1 + (K + r))) =
        relCheckActs Q Γ ++ (chkAct Q Γ (c 0) ::
          ((roundStream (K - 1) fun k => stepRun Q Γ K P c (1 + k)) ++ relSyncActs Q Γ)) := by
      have hidx : ∀ r, 0 + 1 + (K + r) = 1 * (K + 1) + r := by intro r; ring
      have h := counterSeg_tail (Q := Q) (Γ := Γ) (P := P) (c := c) hK (K - 1) 1
        (by omega) (by omega)
      simp only [Nat.sub_self] at h
      simpa [hidx] using h
    rw [hfirst, hwaits, hrest]
    have hstep : (roundStream K fun k => stepRun Q Γ K P c k) =
        stepRun Q Γ K P c 0 ++ roundStream (K - 1) fun k => stepRun Q Γ K P c (1 + k) := by
      have h := roundStream_add 1 (K - 1) fun k => stepRun Q Γ K P c k
      rw [show 1 + (K - 1) = K by omega] at h
      simpa using h
    rw [hstep]
    simp [stepRun, chkRun, List.append_assoc]

/-- **One cell counter refines `checkers 1`, cell by cell.**

The data of a counter run are, for each of its `K` decisions, either a transition of the
machine (`P t` a refinement of `transition`) or the test that the head is elsewhere, together
with the symbol `c t` it compares. -/
theorem chainYield_checkers_one_cells {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ}
    (hP : ∀ t < K, (domainBod N w K).ChainYield [Sum.inr TMTask.transition] (P t) ∨
      P t = [TMAct.check TMFact.noHead]) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers 1)]
      (roundStream (K * (K + 1) + 1) (counterSeg Q Γ K P c)) := by
  rw [counterSeg_run, chainYield_singleton_bod_iff]
  refine ⟨checkerBodyFix K, by rw [bodiesFix_checkers_one]; rfl, gridYield_singleton_iff.2 ?_⟩
  have hsteps : (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K)]
      (roundStream K fun k => stepRun Q Γ K P c k) := by
    refine (chainYield_cSeq_iff K).2
      ⟨(List.range K).map fun t => stepRun Q Γ K P c t, by simp, ?_, rfl⟩
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
    exact chainYield_transitionAndCheck (hP t (List.mem_range.1 ht))
  rw [show (List.cons (Sum.inr (TMTask.release SyncKind.check))
      [Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K),
        Sum.inr (TMTask.release SyncKind.sync)] : List (TMAct Q Γ ⊕ TMTask Q Γ)) =
    [(Sum.inr (TMTask.release SyncKind.check) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      ([Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K)] ++
        [Sum.inr (TMTask.release SyncKind.sync)]) from rfl]
  exact chainYield_app ((chainYield_release_iff (x := SyncKind.check)).2 rfl)
    (chainYield_app hsteps ((chainYield_release_iff (x := SyncKind.sync)).2 rfl))

/-- **The cell counters of the initial task network refine into the cell-major schedule.**

The second chain of `HTN.TMEnc.initChains` is `checkers (K+1)`; the plan produces `(K+1)²`
cells, and this is the schedule in which the `K + 1` counters answer, cell by cell, the two
requests of every cell — counter `j` running its own counter over the cells `j, …,
j + K(K+1)` and waiting during the `K` remaining ones.  It is the shape the completeness half
of the simulation argument needs; the data are, for every counter `j` and every one of its `K`
decisions `t`, either a transition of the machine or the test that the head is elsewhere,
together with the symbols it compares. -/
theorem chainYield_checkers_initChain {P : ℕ → ℕ → List (TMAct Q Γ)} {c : ℕ → ℕ → Option Γ}
    (hP : ∀ j < K + 1, ∀ t < K,
      (domainBod N w K).ChainYield [Sum.inr TMTask.transition] (P j t) ∨
        P j t = [TMAct.check TMFact.noHead]) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers (K + 1))]
      (roundMajor (K + 1) ((K + 1) * (K + 1))
        (staggeredSeg (K + 1) ((K + 1) * (K + 1)) fun j => counterSeg Q Γ K (P j) (c j))) := by
  have hsq : (K + 1) * (K + 1) = K * (K + 1) + (K + 1) := by ring
  refine chainYield_checkers_cellMajor (by omega) ?_
  intro j hj
  rw [show (K + 1) * (K + 1) - (K + 1 - 1) = K * (K + 1) + 1 by omega]
  exact chainYield_checkers_one_cells fun t ht => hP j hj t ht

end TMEnc

end HTN
