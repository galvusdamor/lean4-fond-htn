import HtnComplexity.TMEnc.TMEncFixSchedule
/-!
# The tape chain of the encoding, cell by cell

The third chain of `HTN.TMEnc.initChains` is `produceInit ; C^K_{tapeProduce}`: it writes out
the `K + 1` tapes of the space–time diagram, each of them the separator `#` followed by the `K`
tape cells of the machine, and it is the chain that drives the whole plan — for every cell it
issues one request to the head counter and one request to each of the `K + 1` cell counters on
each of the two channels.

This file describes its refinements cell by cell, in the same round (cell) decomposition as
`HtnComplexity/TMEnc/TMEncFixSchedule.lean` uses for the cell counters:

* `HTN.TMEnc.cellRun` — the actions of one produced cell;
* `HTN.TMEnc.chainYield_produceInit` — the first tape is the input, padded with blanks;
* `HTN.TMEnc.chainYield_tapeProduce` — every later tape may carry arbitrary symbols, except
  that it starts with the separator;
* `HTN.TMEnc.chainYield_tapeChain` — **the whole tape chain refines into the `(K+1)²` cells of
  any word `# w⁰ # w¹ … # w^K` whose first block is the input**.

Together with `HTN.TMEnc.chainYield_checkers_initChain` this covers two of the three chains of
the initial task network; see `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### One produced cell -/

/-- The two actions that issue a request on the channel `x`. -/
def acquireActs (Q Γ : Type) (x : SyncKind) : List (TMAct Q Γ) := [TMAct.call x, TMAct.wait x]

/-- **The actions of one produced tape cell**: write the symbol, ask the head counter whether
the head is here, and ask each of the `K + 1` cell counters on the `check` and then on the
`sync` channel. -/
def cellRun (Q Γ : Type) (K : ℕ) (c : Option Γ) : List (TMAct Q Γ) :=
  TMAct.assert c :: (acquireActs Q Γ SyncKind.head ++
    ((roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
      (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync)))

/-- A request task has exactly one refinement. -/
lemma chainYield_acquire_iff {x : SyncKind} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.acquire x)] as ↔
      as = acquireActs Q Γ x := by
  rw [chainYield_singleton_bod_iff]
  constructor
  · rintro ⟨ls, hls, hy⟩
    have hls' : ls = [[Sum.inl (TMAct.call x), Sum.inl (TMAct.wait x)]] := by
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
    refine ⟨[[Sum.inl (TMAct.call x), Sum.inl (TMAct.wait x)]],
      by simp [bodiesFix, bodies], gridYield_singleton_iff.2 ?_⟩
    exact chainYield_cons_inl_iff.2 ⟨_, rfl,
      chainYield_cons_inl_iff.2 ⟨[], rfl, chainYield_nil_iff.2 rfl⟩⟩

/-- A totally ordered counting task refines into any round decomposition of refinements. -/
lemma chainYield_cSeq_rounds {t : TMTask Q Γ} {n : ℕ} {s : ℕ → List (TMAct Q Γ)}
    (h : ∀ k < n, (domainBod N w K).ChainYield [Sum.inr t] (s k)) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq t n)] (roundStream n s) := by
  refine (chainYield_cSeq_iff n).2 ⟨(List.range n).map s, by simp, ?_, rfl⟩
  intro l hl
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
  exact h k (List.mem_range.1 hk)

lemma chainYield_cSeq_acquire {x : SyncKind} {n : ℕ} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq (TMTask.acquire x) n)]
      (roundStream n fun _ => acquireActs Q Γ x) :=
  chainYield_cSeq_rounds fun _ _ => chainYield_acquire_iff.2 rfl

/-- **A cell task refines into the actions of one produced cell.** -/
lemma chainYield_produceSym {c : Option Γ} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.produceSym c)] (cellRun Q Γ K c) := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[[Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire SyncKind.head),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))]],
    by simp [bodiesFix, bodies], gridYield_singleton_iff.2 ?_⟩
  rw [show [Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire SyncKind.head),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))] =
    [(Sum.inl (TMAct.assert c) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      ([Sum.inr (TMTask.acquire SyncKind.head)] ++
        ([Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1))] ++
          [Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))])) from rfl]
  exact chainYield_app (chainYield_singleton_inl (a := TMAct.assert c))
    (chainYield_app ((chainYield_acquire_iff (x := SyncKind.head)).2 rfl)
      (chainYield_app (chainYield_cSeq_acquire (x := SyncKind.check) (n := K + 1))
        (chainYield_cSeq_acquire (x := SyncKind.sync) (n := K + 1))))

/-- The unconstrained cell task refines into the actions of one produced cell, with any
symbol. -/
lemma chainYield_produce {c : Option Γ} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.produce] (cellRun Q Γ K c) := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[[Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire SyncKind.head),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))]],
    ⟨c, rfl⟩, gridYield_singleton_iff.2 ?_⟩
  rw [show [Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire SyncKind.head),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
      Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))] =
    [(Sum.inl (TMAct.assert c) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      ([Sum.inr (TMTask.acquire SyncKind.head)] ++
        ([Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1))] ++
          [Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))])) from rfl]
  exact chainYield_app (chainYield_singleton_inl (a := TMAct.assert c))
    (chainYield_app ((chainYield_acquire_iff (x := SyncKind.head)).2 rfl)
      (chainYield_app (chainYield_cSeq_acquire (x := SyncKind.check) (n := K + 1))
        (chainYield_cSeq_acquire (x := SyncKind.sync) (n := K + 1))))

/-! ### The first tape: the input -/

/-- The symbols of the first block of the space–time diagram: the separator, then the input,
padded with blanks. -/
def tapeInitSym (N : NTM Q Γ) (w : List Γ) (j : ℕ) : Option Γ :=
  if j = 0 then none else some (w.getD (j - 1) N.blank)

/-- **The task that writes the input refines into the cells of the input word.** -/
lemma chainYield_produceWord : ∀ n i : ℕ, w.length - i = n → i < w.length →
    (domainBod N w K).ChainYield [Sum.inr (TMTask.produceWord i)]
      (roundStream (w.length - i) fun k => cellRun Q Γ K (some (w.getD (i + k) N.blank))) := by
  intro n
  induction n with
  | zero => intro i hn hi; omega
  | succ n ih =>
      intro i hn hi
      rw [chainYield_singleton_bod_iff]
      by_cases hlast : i + 1 < w.length
      · refine ⟨[[Sum.inr (TMTask.produceSym (some (w.getD i N.blank))),
          Sum.inr (TMTask.produceWord (i + 1))]], by simp [bodiesFix, bodies, hlast],
          gridYield_singleton_iff.2 ?_⟩
        have hrest := ih (i + 1) (by omega) hlast
        have hsplit : (roundStream (w.length - i) fun k =>
              cellRun Q Γ K (some (w.getD (i + k) N.blank))) =
            cellRun Q Γ K (some (w.getD i N.blank)) ++
              (roundStream (w.length - (i + 1)) fun k =>
                cellRun Q Γ K (some (w.getD (i + 1 + k) N.blank))) := by
          have h := roundStream_add 1 (w.length - (i + 1))
            fun k => cellRun Q Γ K (some (w.getD (i + k) N.blank))
          rw [show 1 + (w.length - (i + 1)) = w.length - i by omega] at h
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        rw [hsplit]
        simpa using chainYield_app chainYield_produceSym hrest
      · refine ⟨[[Sum.inr (TMTask.produceSym (some (w.getD i N.blank)))]],
          by simp [bodiesFix, bodies, hlast], gridYield_singleton_iff.2 ?_⟩
        rw [show w.length - i = 1 by omega]
        simpa using chainYield_produceSym (N := N) (w := w) (K := K)
          (c := some (w.getD (i + 0) N.blank))

/-- **The initial tape refines into the cells of the input, padded with blanks.** -/
lemma chainYield_produceInit (hw : 1 ≤ w.length) (hwK : w.length ≤ K) :
    (domainBod N w K).ChainYield [Sum.inr TMTask.produceInit]
      (roundStream (K + 1) fun j => cellRun Q Γ K (tapeInitSym N w j)) := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[[Sum.inr (TMTask.produceSym none), Sum.inr (TMTask.produceWord 0),
      Sum.inr (TMTask.cSeq (TMTask.produceSym (some N.blank)) (K - w.length))]],
    by simp [bodiesFix, bodies], gridYield_singleton_iff.2 ?_⟩
  -- the three parts of the chain
  have hword := chainYield_produceWord (Q := Q) (N := N) (K := K) (w.length - 0) 0 rfl (by omega)
  have hblank : (domainBod N w K).ChainYield
      [Sum.inr (TMTask.cSeq (TMTask.produceSym (some N.blank)) (K - w.length))]
      (roundStream (K - w.length) fun _ => cellRun Q Γ K (some N.blank)) :=
    chainYield_cSeq_rounds fun _ _ => chainYield_produceSym
  -- the cells of the first block
  have hsplit : (roundStream (K + 1) fun j => cellRun Q Γ K (tapeInitSym N w j)) =
      cellRun Q Γ K none ++
        ((roundStream (w.length - 0) fun k => cellRun Q Γ K (some (w.getD (0 + k) N.blank))) ++
          (roundStream (K - w.length) fun _ => cellRun Q Γ K (some N.blank))) := by
    have h1 : (roundStream (K + 1) fun j => cellRun Q Γ K (tapeInitSym N w j)) =
        cellRun Q Γ K none ++
          (roundStream K fun k => cellRun Q Γ K (some (w.getD k N.blank))) := by
      have h := roundStream_add 1 K fun j => cellRun Q Γ K (tapeInitSym N w j)
      rw [show 1 + K = K + 1 by omega] at h
      rw [h]
      simp only [roundStream_one, tapeInitSym]
      congr 1
      refine roundStream_congr fun k _ => ?_
      simp
    have h2 : (roundStream K fun k => cellRun Q Γ K (some (w.getD k N.blank))) =
        (roundStream w.length fun k => cellRun Q Γ K (some (w.getD k N.blank))) ++
          (roundStream (K - w.length) fun _ => cellRun Q Γ K (some N.blank)) := by
      have h := roundStream_add w.length (K - w.length)
        fun k => cellRun Q Γ K (some (w.getD k N.blank))
      rw [show w.length + (K - w.length) = K by omega] at h
      rw [h]
      congr 1
      refine roundStream_congr fun r _ => ?_
      simp [List.getD]
    rw [h1, h2]
    simp
  rw [hsplit]
  simpa using chainYield_app chainYield_produceSym (chainYield_app hword hblank)

/-! ### The later tapes -/

/-- **A later tape refines into the cells of any word that starts with the separator.** -/
lemma chainYield_tapeProduce {s : ℕ → Option Γ} (hs : s 0 = none) :
    (domainBod N w K).ChainYield [Sum.inr TMTask.tapeProduce]
      (roundStream (K + 1) fun j => cellRun Q Γ K (s j)) := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[[Sum.inr (TMTask.produceSym none), Sum.inr (TMTask.cSeq TMTask.produce K)]],
    by simp [bodiesFix, bodies], gridYield_singleton_iff.2 ?_⟩
  have hrest : (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq TMTask.produce K)]
      (roundStream K fun k => cellRun Q Γ K (s (1 + k))) :=
    chainYield_cSeq_rounds fun _ _ => chainYield_produce
  have hsplit : (roundStream (K + 1) fun j => cellRun Q Γ K (s j)) =
      cellRun Q Γ K none ++ (roundStream K fun k => cellRun Q Γ K (s (1 + k))) := by
    have h := roundStream_add 1 K fun j => cellRun Q Γ K (s j)
    rw [show 1 + K = K + 1 by omega] at h
    rw [h, roundStream_one, hs]
  rw [hsplit]
  simpa using chainYield_app chainYield_produceSym hrest

/-! ### The whole tape chain -/

/-- **The tape chain of the initial task network refines into the `(K+1)²` cells of the
space–time diagram**, for any symbols whose first block is the input and each of whose blocks
starts with the separator. -/
theorem chainYield_tapeChain {sym : ℕ → Option Γ} (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hinit : ∀ j ≤ K, sym j = tapeInitSym N w j)
    (hsep : ∀ i ≤ K, sym (i * (K + 1)) = none) :
    (domainBod N w K).ChainYield
      [Sum.inr TMTask.produceInit, Sum.inr (TMTask.cSeq TMTask.tapeProduce K)]
      (roundStream ((K + 1) * (K + 1)) fun n => cellRun Q Γ K (sym n)) := by
  have hsplit : (roundStream ((K + 1) * (K + 1)) fun n => cellRun Q Γ K (sym n)) =
      (roundStream (K + 1) fun j => cellRun Q Γ K (tapeInitSym N w j)) ++
        (roundStream K fun i => roundStream (K + 1) fun j =>
          cellRun Q Γ K (sym ((i + 1) * (K + 1) + j))) := by
    have h := roundStream_add (K + 1) (K * (K + 1)) fun n => cellRun Q Γ K (sym n)
    rw [show K + 1 + K * (K + 1) = (K + 1) * (K + 1) by ring] at h
    rw [h]
    congr 1
    · exact roundStream_congr fun j hj => by rw [hinit j (by omega)]
    · rw [roundStream_mul K (K + 1) fun r => cellRun Q Γ K (sym (K + 1 + r))]
      refine roundStream_congr fun i _ => roundStream_congr fun j _ => ?_
      congr 2
      ring
  rw [hsplit, show [Sum.inr TMTask.produceInit,
      Sum.inr (TMTask.cSeq TMTask.tapeProduce K)] =
    [(Sum.inr TMTask.produceInit : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      [Sum.inr (TMTask.cSeq TMTask.tapeProduce K)] from rfl]
  refine chainYield_app (chainYield_produceInit hw hwK) (chainYield_cSeq_rounds ?_)
  intro i hi
  exact chainYield_tapeProduce (by simpa using hsep (i + 1) (by omega))

end TMEnc

end HTN
