import HtnComplexity.TMEnc.TMEncFixNoSI
/-!
# The refinements of the tape chain, analysed

`HtnComplexity/TMEnc/TMEncFixTape.lean` shows that the tape chain of the initial task network
*can* be refined into the `(K+1)²` cells of a space–time diagram.  The soundness half of the
simulation argument needs the converse: **every** refinement of the tape chain is of that shape.
That is what this file proves.

* `HTN.TMEnc.chainYield_cSeq_rounds_iff` — a totally ordered counting task refines exactly into
  the round decompositions of `k` refinements of its argument;
* `HTN.TMEnc.chainYield_produceSym_iff`, `HTN.TMEnc.chainYield_produce_iff` — one produced cell
  is exactly `HTN.TMEnc.cellRun`, with a fixed resp. an arbitrary symbol;
* `HTN.TMEnc.chainYield_produceInit_iff` — the initial tape is exactly the input, padded with
  blanks and preceded by the separator;
* `HTN.TMEnc.chainYield_tapeProduce_iff` — a later tape is exactly `K + 1` cells whose first
  symbol is the separator;
* `HTN.TMEnc.chainYield_tapeChain_iff` — **the refinements of the tape chain are exactly the
  `(K+1)²` cells of a space–time diagram whose first block is the input and each of whose blocks
  starts with the separator.**
-/

namespace HTN

variable {α : Type}

/-- A concatenation of `k` lists is the stream of its entries. -/
lemma flatten_eq_roundStream {ass : List (List α)} {k : ℕ} (h : ass.length = k) :
    ass.flatten = roundStream k fun i => ass.getD i [] := by
  subst h
  simp only [roundStream]
  congr 1
  refine (List.ext_getElem (by simp) ?_).symm
  intro n h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- The `(K+1)²` rounds of the tape, split into the first block and the `K` later ones. -/
lemma roundStream_tape_split (K : ℕ) (f : ℕ → List α) :
    roundStream ((K + 1) * (K + 1)) f =
      roundStream (K + 1) f ++
        roundStream K fun i => roundStream (K + 1) fun j => f ((i + 1) * (K + 1) + j) := by
  have h := roundStream_add (K + 1) (K * (K + 1)) f
  rw [show K + 1 + K * (K + 1) = (K + 1) * (K + 1) by ring] at h
  rw [h, roundStream_mul K (K + 1) fun r => f (K + 1 + r)]
  congr 1
  refine roundStream_congr fun i _ => roundStream_congr fun j _ => ?_
  congr 1
  ring

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Counting tasks as streams -/

/-- **A totally ordered counting task refines exactly into round decompositions.** -/
lemma chainYield_cSeq_rounds_iff {t : TMTask Q Γ} {n : ℕ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq t n)] as ↔
      ∃ s : ℕ → List (TMAct Q Γ), (∀ k < n, (domainBod N w K).ChainYield [Sum.inr t] (s k)) ∧
        as = roundStream n s := by
  rw [chainYield_cSeq_iff n]
  constructor
  · rintro ⟨ass, hlen, hall, rfl⟩
    refine ⟨fun i => ass.getD i [], fun k hk => hall _ ?_, flatten_eq_roundStream hlen⟩
    have hk' : k < ass.length := by omega
    show ass.getD k [] ∈ ass
    rw [show ass.getD k [] = ass[k] from List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem _
  · rintro ⟨s, hall, rfl⟩
    refine ⟨(List.range n).map s, by simp, ?_, ?_⟩
    · intro l hl
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
      exact hall k (List.mem_range.1 hk)
    · rfl

lemma chainYield_cSeq_acquire_forward {x : SyncKind} {n : ℕ} {as : List (TMAct Q Γ)}
    (h : (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq (TMTask.acquire x) n)] as) :
    as = roundStream n fun _ => acquireActs Q Γ x := by
  obtain ⟨s, hall, rfl⟩ := chainYield_cSeq_rounds_iff.1 h
  exact roundStream_congr fun r hr => chainYield_acquire_iff.1 (hall r hr)

/-! ### One produced cell -/

/-- The body of a cell task refines exactly into the actions of one produced cell. -/
lemma chainYield_cellBody_iff {c : Option Γ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield
      [Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire SyncKind.head),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))] as ↔
      as = cellRun Q Γ K c := by
  constructor
  · intro h
    rw [chainYield_cons_inl_iff] at h
    obtain ⟨as₁, rfl, h⟩ := h
    rw [show [(Sum.inr (TMTask.acquire SyncKind.head) : TMAct Q Γ ⊕ TMTask Q Γ),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))] =
      [(Sum.inr (TMTask.acquire SyncKind.head) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
        ([Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1))] ++
          [Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))]) from rfl,
      chainYield_append_iff] at h
    obtain ⟨bs, cs, rfl, hb, hc⟩ := h
    rw [chainYield_append_iff] at hc
    obtain ⟨cs₁, cs₂, rfl, hc₁, hc₂⟩ := hc
    rw [chainYield_acquire_iff.1 hb, chainYield_cSeq_acquire_forward hc₁,
      chainYield_cSeq_acquire_forward hc₂]
    rfl
  · rintro rfl
    rw [show cellRun Q Γ K c = TMAct.assert c :: (acquireActs Q Γ SyncKind.head ++
        ((roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
          (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync))) from rfl]
    refine chainYield_cons_inl_iff.2 ⟨_, rfl, ?_⟩
    rw [show [(Sum.inr (TMTask.acquire SyncKind.head) : TMAct Q Γ ⊕ TMTask Q Γ),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))] =
      [(Sum.inr (TMTask.acquire SyncKind.head) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
        ([Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1))] ++
          [Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))]) from rfl]
    exact chainYield_app (chainYield_acquire_iff.2 rfl)
      (chainYield_app (chainYield_cSeq_acquire (x := SyncKind.check) (n := K + 1))
        (chainYield_cSeq_acquire (x := SyncKind.sync) (n := K + 1)))

/-- **A cell task with a fixed symbol refines exactly into the actions of one produced cell.** -/
lemma chainYield_produceSym_iff {c : Option Γ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.produceSym c)] as ↔ as = cellRun Q Γ K c := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ls = [[Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire SyncKind.head),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
        Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))]] := by
      simpa [bodiesFix, bodies] using hls
    subst hls'
    rw [gridYield_singleton_iff] at hy
    exact chainYield_cellBody_iff.1 hy
  · rintro rfl
    exact chainYield_produceSym

/-- **The unconstrained cell task refines exactly into the actions of one produced cell**, with
an arbitrary symbol. -/
lemma chainYield_produce_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.produce] as ↔
      ∃ c : Option Γ, as = cellRun Q Γ K c := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ∃ c : Option Γ, ls =
        [[Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire SyncKind.head),
          Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.check) (K + 1)),
          Sum.inr (TMTask.cSeq (TMTask.acquire SyncKind.sync) (K + 1))]] := by
      simpa [bodiesFix, bodies] using hls
    obtain ⟨c, rfl⟩ := hls'
    rw [gridYield_singleton_iff] at hy
    exact ⟨c, chainYield_cellBody_iff.1 hy⟩
  · rintro ⟨c, rfl⟩
    exact chainYield_produce

/-! ### The first tape: the input -/

/-- **The task that writes the input refines exactly into the cells of the input word.** -/
lemma chainYield_produceWord_forward : ∀ n i : ℕ, w.length - i = n → i < w.length →
    ∀ {as : List (TMAct Q Γ)},
      (domainBod N w K).ChainYield [Sum.inr (TMTask.produceWord i)] as →
      as = roundStream (w.length - i) fun k => cellRun Q Γ K (some (w.getD (i + k) N.blank)) := by
  intro n
  induction n with
  | zero => intro i hn hi; omega
  | succ n ih =>
      intro i hn hi as h
      rw [chainYield_singleton_bod_iff] at h
      obtain ⟨ls, hls, hy⟩ := h
      by_cases hlast : i + 1 < w.length
      · have hls' : ls = [[Sum.inr (TMTask.produceSym (some (w.getD i N.blank))),
            Sum.inr (TMTask.produceWord (i + 1))]] := by
          simpa [bodiesFix, bodies, hlast] using hls
        subst hls'
        rw [gridYield_singleton_iff, show
          [(Sum.inr (TMTask.produceSym (some (w.getD i N.blank))) : TMAct Q Γ ⊕ TMTask Q Γ),
            Sum.inr (TMTask.produceWord (i + 1))] =
          [(Sum.inr (TMTask.produceSym (some (w.getD i N.blank))) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
            [Sum.inr (TMTask.produceWord (i + 1))] from rfl, chainYield_append_iff] at hy
        obtain ⟨bs, cs, rfl, hb, hc⟩ := hy
        rw [chainYield_produceSym_iff.1 hb, ih (i + 1) (by omega) hlast hc]
        have h := roundStream_add 1 (w.length - (i + 1))
          fun k => cellRun Q Γ K (some (w.getD (i + k) N.blank))
        rw [show 1 + (w.length - (i + 1)) = w.length - i by omega] at h
        rw [h]
        simp only [roundStream_one, Nat.add_zero, Nat.add_assoc]
      · have hls' : ls = [[Sum.inr (TMTask.produceSym (some (w.getD i N.blank)))]] := by
          simpa [bodiesFix, bodies, hlast] using hls
        subst hls'
        rw [gridYield_singleton_iff] at hy
        rw [chainYield_produceSym_iff.1 hy, show w.length - i = 1 by omega]
        simp

lemma chainYield_cSeq_produceSym_forward {c : Option Γ} {n : ℕ} {as : List (TMAct Q Γ)}
    (h : (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq (TMTask.produceSym c) n)] as) :
    as = roundStream n fun _ => cellRun Q Γ K c := by
  obtain ⟨s, hall, rfl⟩ := chainYield_cSeq_rounds_iff.1 h
  exact roundStream_congr fun r hr => chainYield_produceSym_iff.1 (hall r hr)

/-- The cells of the first block: the separator, the input, and the blanks that pad it. -/
lemma cells_initBlock_split (hwK : w.length ≤ K) :
    (roundStream (K + 1) fun j => cellRun Q Γ K (tapeInitSym N w j)) =
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

/-- **The initial tape refines exactly into the cells of the input, padded with blanks.** -/
lemma chainYield_produceInit_forward (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)}
    (h : (domainBod N w K).ChainYield [Sum.inr TMTask.produceInit] as) :
    as = roundStream (K + 1) fun j => cellRun Q Γ K (tapeInitSym N w j) := by
  rw [chainYield_singleton_bod_iff] at h
  obtain ⟨ls, hls, hy⟩ := h
  have hls' : ls = [[Sum.inr (TMTask.produceSym none), Sum.inr (TMTask.produceWord 0),
      Sum.inr (TMTask.cSeq (TMTask.produceSym (some N.blank)) (K - w.length))]] := by
    simpa [bodiesFix, bodies] using hls
  subst hls'
  rw [gridYield_singleton_iff, show
    [(Sum.inr (TMTask.produceSym none) : TMAct Q Γ ⊕ TMTask Q Γ), Sum.inr (TMTask.produceWord 0),
      Sum.inr (TMTask.cSeq (TMTask.produceSym (some N.blank)) (K - w.length))] =
    [(Sum.inr (TMTask.produceSym none) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      ([Sum.inr (TMTask.produceWord 0)] ++
        [Sum.inr (TMTask.cSeq (TMTask.produceSym (some N.blank)) (K - w.length))]) from rfl,
    chainYield_append_iff] at hy
  obtain ⟨bs, cs, rfl, hb, hc⟩ := hy
  rw [chainYield_append_iff] at hc
  obtain ⟨cs₁, cs₂, rfl, hc₁, hc₂⟩ := hc
  rw [chainYield_produceSym_iff.1 hb,
    chainYield_produceWord_forward (K := K) (w.length - 0) 0 rfl (by omega) hc₁,
    chainYield_cSeq_produceSym_forward hc₂, cells_initBlock_split hwK]

/-! ### The later tapes -/

/-- **A later tape refines exactly into `K + 1` cells whose first symbol is the separator.** -/
lemma chainYield_tapeProduce_forward {as : List (TMAct Q Γ)}
    (h : (domainBod N w K).ChainYield [Sum.inr TMTask.tapeProduce] as) :
    ∃ s : ℕ → Option Γ, s 0 = none ∧
      as = roundStream (K + 1) fun j => cellRun Q Γ K (s j) := by
  classical
  rw [chainYield_singleton_bod_iff] at h
  obtain ⟨ls, hls, hy⟩ := h
  have hls' : ls = [[Sum.inr (TMTask.produceSym none), Sum.inr (TMTask.cSeq TMTask.produce K)]] := by
    simpa [bodiesFix, bodies] using hls
  subst hls'
  rw [gridYield_singleton_iff, show
    [(Sum.inr (TMTask.produceSym none) : TMAct Q Γ ⊕ TMTask Q Γ),
      Sum.inr (TMTask.cSeq TMTask.produce K)] =
    [(Sum.inr (TMTask.produceSym none) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      [Sum.inr (TMTask.cSeq TMTask.produce K)] from rfl, chainYield_append_iff] at hy
  obtain ⟨bs, cs, rfl, hb, hc⟩ := hy
  obtain ⟨seg, hall, rfl⟩ := chainYield_cSeq_rounds_iff.1 hc
  have hex : ∀ k : ℕ, ∃ c : Option Γ, k < K → seg k = cellRun Q Γ K c := by
    intro k
    by_cases hk : k < K
    · obtain ⟨c, hc'⟩ := chainYield_produce_iff.1 (hall k hk)
      exact ⟨c, fun _ => hc'⟩
    · exact ⟨none, fun hk' => absurd hk' hk⟩
  choose f hf using hex
  refine ⟨fun j => if j = 0 then none else f (j - 1), rfl, ?_⟩
  have hsplit : (roundStream (K + 1) fun j =>
        cellRun Q Γ K (if j = 0 then none else f (j - 1))) =
      cellRun Q Γ K none ++ (roundStream K fun r => cellRun Q Γ K (f r)) := by
    have h := roundStream_add 1 K fun j => cellRun Q Γ K (if j = 0 then none else f (j - 1))
    rw [show 1 + K = K + 1 by omega] at h
    rw [h, roundStream_one]
    simp
  rw [hsplit, chainYield_produceSym_iff.1 hb]
  congr 1
  exact roundStream_congr fun r hr => hf r hr

/-! ### The whole tape chain -/

/-- **The refinements of the tape chain are exactly the `(K+1)²` cells of a space–time
diagram** whose first block is the input, padded with blanks, and each of whose blocks starts
with the separator.  This is the tape half of the analysis of a solution plan. -/
theorem chainYield_tapeChain_iff (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield
      [Sum.inr TMTask.produceInit, Sum.inr (TMTask.cSeq TMTask.tapeProduce K)] as ↔
      ∃ sym : ℕ → Option Γ, (∀ j ≤ K, sym j = tapeInitSym N w j) ∧
        (∀ i ≤ K, sym (i * (K + 1)) = none) ∧
        as = roundStream ((K + 1) * (K + 1)) fun n => cellRun Q Γ K (sym n) := by
  classical
  constructor
  · intro h
    rw [show [(Sum.inr TMTask.produceInit : TMAct Q Γ ⊕ TMTask Q Γ),
        Sum.inr (TMTask.cSeq TMTask.tapeProduce K)] =
      [(Sum.inr TMTask.produceInit : TMAct Q Γ ⊕ TMTask Q Γ)] ++
        [Sum.inr (TMTask.cSeq TMTask.tapeProduce K)] from rfl, chainYield_append_iff] at h
    obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h
    obtain ⟨blk, hall, rfl⟩ := chainYield_cSeq_rounds_iff.1 h₂
    have hex : ∀ i : ℕ, ∃ g : ℕ → Option Γ, i < K →
        (g 0 = none ∧ blk i = roundStream (K + 1) fun j => cellRun Q Γ K (g j)) := by
      intro i
      by_cases hi : i < K
      · obtain ⟨g, hg0, hgs⟩ := chainYield_tapeProduce_forward (hall i hi)
        exact ⟨g, fun _ => ⟨hg0, hgs⟩⟩
      · exact ⟨fun _ => none, fun hi' => absurd hi' hi⟩
    choose g hg using hex
    refine ⟨fun n => if n < K + 1 then tapeInitSym N w n else
      g ((n - (K + 1)) / (K + 1)) ((n - (K + 1)) % (K + 1)), fun j hj => by simp [hj],
      ?_, ?_⟩
    · -- every block starts with the separator
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp [tapeInitSym]
      · have hge : ¬ (i * (K + 1) < K + 1) := by
          have : 1 * (K + 1) ≤ i * (K + 1) := Nat.mul_le_mul_right _ hi0
          omega
        have hsub : i * (K + 1) - (K + 1) = 0 + (K + 1) * (i - 1) := by
          cases i with
          | zero => omega
          | succ i => simp; ring_nf; omega
        simp only [hge, if_false, hsub]
        rw [Nat.add_mul_div_left _ _ (Nat.succ_pos K), Nat.add_mul_mod_self_left]
        simpa using (hg (i - 1) (by omega)).1
    · -- the stream of cells
      rw [roundStream_tape_split, chainYield_produceInit_forward hw hwK h₁]
      congr 1
      · exact (roundStream_congr fun j hj => by simp [hj]).symm
      · refine roundStream_congr fun i hi => ?_
        rw [(hg i hi).2]
        refine roundStream_congr fun j hj => ?_
        have hge : ¬ ((i + 1) * (K + 1) + j < K + 1) := by
          have : 1 * (K + 1) ≤ (i + 1) * (K + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have hsub : (i + 1) * (K + 1) + j - (K + 1) = j + (K + 1) * i := by
          have : (i + 1) * (K + 1) = (K + 1) * i + (K + 1) := by ring
          omega
        simp only [hge, if_false, hsub]
        rw [Nat.add_mul_div_left _ _ (Nat.succ_pos K), Nat.add_mul_mod_self_left,
          Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
        simp
  · rintro ⟨sym, hinit, hsep, rfl⟩
    exact chainYield_tapeChain hw hwK hinit hsep

end TMEnc

end HTN
