import HtnComplexity.TMEnc.TMEncFixTapeAnalysis
/-!
# The refinements of the head-counter chain, analysed

This is the head-counter counterpart of `HtnComplexity/TMEnc/TMEncFixTapeAnalysis.lean`: the
soundness half of the simulation argument needs that **every** refinement of the head-counter
chain of the initial task network is the one that `HtnComplexity/TMEnc/TMEncFixHeadChain.lean`
constructs.

* `HTN.TMEnc.chainYield_headCell_iff`, `HTN.TMEnc.chainYield_noHeadCell_iff` — one unit of the
  counter;
* `HTN.TMEnc.chainYield_heads_iff` — one cycle: `K + 2` units, the head at the second one;
* `HTN.TMEnc.chainYield_headChainFix_iff` — **the refinements of the repaired head-counter chain
  are exactly its `K² + 3K + 1` units, with the head at the units `u ≡ 1 (mod K + 2)`**
  (`HTN.TMEnc.headMarkStd`).
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- A chain of three primitive tasks refines only into those three actions. -/
lemma chainYield_three_inl_iff {a b c : TMAct Q Γ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inl a, Sum.inl b, Sum.inl c] as ↔ as = [a, b, c] := by
  constructor
  · intro h
    obtain ⟨as₁, rfl, h₁⟩ := chainYield_cons_inl_iff.1 h
    obtain ⟨as₂, rfl, h₂⟩ := chainYield_cons_inl_iff.1 h₁
    obtain ⟨as₃, rfl, h₃⟩ := chainYield_cons_inl_iff.1 h₂
    rw [chainYield_nil_iff] at h₃
    subst h₃
    rfl
  · rintro rfl
    exact chainYield_cons_inl_iff.2 ⟨_, rfl, chainYield_cons_inl_iff.2 ⟨_, rfl,
      chainYield_cons_inl_iff.2 ⟨[], rfl, chainYield_nil_iff.2 rfl⟩⟩⟩

/-- **The unit at which the head is present has exactly one refinement.** -/
lemma chainYield_headCell_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.headCell] as ↔ as = headUnitActs Q Γ true := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ls = [[Sum.inl (TMAct.start SyncKind.head), Sum.inl TMAct.assertHead,
        Sum.inl (TMAct.respond SyncKind.head)]] := by
      simpa [bodiesFix, bodies] using hls
    subst hls'
    rw [gridYield_singleton_iff] at hy
    rw [chainYield_three_inl_iff.1 hy]
    rfl
  · rintro rfl
    exact chainYield_headCell

/-- **The unit at which the head is absent has exactly one refinement.** -/
lemma chainYield_noHeadCell_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.noHeadCell] as ↔
      as = headUnitActs Q Γ false := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ls = [[Sum.inl (TMAct.start SyncKind.head), Sum.inl TMAct.retractHead,
        Sum.inl (TMAct.respond SyncKind.head)]] := by
      simpa [bodiesFix, bodies] using hls
    subst hls'
    rw [gridYield_singleton_iff] at hy
    rw [chainYield_three_inl_iff.1 hy]
    rfl
  · rintro rfl
    exact chainYield_noHeadCell

lemma chainYield_cSeq_noHeadCell_forward {n : ℕ} {as : List (TMAct Q Γ)}
    (h : (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq TMTask.noHeadCell n)] as) :
    as = roundStream n fun _ => headUnitActs Q Γ false := by
  obtain ⟨s, hall, rfl⟩ := chainYield_cSeq_rounds_iff.1 h
  exact roundStream_congr fun r hr => chainYield_noHeadCell_iff.1 (hall r hr)

/-- **One cycle of the head counter has exactly one refinement**: `K + 2` units with the head at
the second one. -/
lemma chainYield_heads_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.heads] as ↔
      as = roundStream (K + 2) fun j => headUnitActs Q Γ (decide (j = 1)) := by
  have hstd : (roundStream (K + 2) fun j => headUnitActs Q Γ (decide (j = 1))) =
      headUnitActs Q Γ false ++ (headUnitActs Q Γ true ++
        (roundStream K fun _ => headUnitActs Q Γ false)) := by
    have h2 : (roundStream 2 fun j => headUnitActs Q Γ (decide (j = 1))) =
        headUnitActs Q Γ false ++ headUnitActs Q Γ true := by
      simp [roundStream, List.range_succ]
    have h := roundStream_add 2 K fun j => headUnitActs Q Γ (decide (j = 1))
    rw [show 2 + K = K + 2 by omega] at h
    have h3 : (roundStream K fun r => headUnitActs Q Γ (decide (2 + r = 1))) =
        roundStream K fun _ => headUnitActs Q Γ false :=
      roundStream_congr fun k _ => by
        have hk : ¬ (2 + k = 1) := by omega
        simp [hk]
    rw [h, h2, List.append_assoc, h3]
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ls = [[Sum.inr TMTask.noHeadCell, Sum.inr TMTask.headCell,
        Sum.inr (TMTask.cSeq TMTask.noHeadCell K)]] := by
      simpa [bodiesFix, bodies] using hls
    subst hls'
    rw [gridYield_singleton_iff, show [(Sum.inr TMTask.noHeadCell : TMAct Q Γ ⊕ TMTask Q Γ),
        Sum.inr TMTask.headCell, Sum.inr (TMTask.cSeq TMTask.noHeadCell K)] =
      [(Sum.inr TMTask.noHeadCell : TMAct Q Γ ⊕ TMTask Q Γ)] ++
        ([Sum.inr TMTask.headCell] ++ [Sum.inr (TMTask.cSeq TMTask.noHeadCell K)]) from rfl,
      chainYield_append_iff] at hy
    obtain ⟨bs, cs, rfl, hb, hc⟩ := hy
    rw [chainYield_append_iff] at hc
    obtain ⟨cs₁, cs₂, rfl, hc₁, hc₂⟩ := hc
    rw [hstd, chainYield_noHeadCell_iff.1 hb, chainYield_headCell_iff.1 hc₁,
      chainYield_cSeq_noHeadCell_forward hc₂]
  · rintro rfl
    exact chainYield_heads (by simp) (by simp) (fun j hj2 _ => by simp; omega)

lemma chainYield_cSeq_heads_forward {n : ℕ} {as : List (TMAct Q Γ)}
    (h : (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq TMTask.heads n)] as) :
    as = roundStream n fun _ => roundStream (K + 2) fun j =>
      headUnitActs Q Γ (decide (j = 1)) := by
  obtain ⟨s, hall, rfl⟩ := chainYield_cSeq_rounds_iff.1 h
  exact roundStream_congr fun r hr => chainYield_heads_iff.1 (hall r hr)

/-! ### The whole head-counter chain -/

/-- The marks of the repaired head counter: the head is reported at the units `u` with
`u ≡ 1 (mod K + 2)` — the second unit of each cycle `noHead, head, noHead^K`. -/
def headMarkStd (K u : ℕ) : Bool := decide (u % (K + 2) = 1)

lemma headMarkStd_eq_true_iff {K u : ℕ} : headMarkStd K u = true ↔ u % (K + 2) = 1 := by
  simp [headMarkStd]

@[simp] lemma headMarkStd_zero : headMarkStd K 0 = false := by
  simp [headMarkStd, Nat.zero_mod]

lemma headMarkStd_block {b j : ℕ} (hj : j < K + 2) :
    headMarkStd K (b * (K + 2) + j) = decide (j = 1) := by
  rw [headMarkStd, Nat.add_comm (b * (K + 2)) j, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hj]

/-- **The refinements of the repaired head-counter chain are exactly its `K² + 3K + 1` units**,
with the head reported at the units `u ≡ 1 (mod K + 2)`.  This is the head-counter half of the
analysis of a solution plan. -/
theorem chainYield_headChainFix_iff (hK : 1 ≤ K) {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield (headChainFix (Q := Q) (Γ := Γ) K) as ↔
      as = roundStream (K * K + 3 * K + 1) fun u => headUnitActs Q Γ (headMarkStd K u) := by
  have hstd := headStream_splitFix (Q := Q) (Γ := Γ) (K := K) hK
    (s := headMarkStd K) (fun u _ => rfl)
  constructor
  · intro h
    rw [show (headChainFix (Q := Q) (Γ := Γ) K) =
        [Sum.inr (TMTask.cSeq TMTask.heads K)] ++
          ([Sum.inr TMTask.noHeadCell] ++ ([Sum.inr TMTask.headCell] ++
            [Sum.inr (TMTask.cSeq TMTask.noHeadCell (K - 1))])) from rfl,
      chainYield_append_iff] at h
    obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h
    rw [chainYield_append_iff] at h₂
    obtain ⟨bs₁, bs₂, rfl, hb₁, hb₂⟩ := h₂
    rw [chainYield_append_iff] at hb₂
    obtain ⟨cs₁, cs₂, rfl, hc₁, hc₂⟩ := hb₂
    rw [hstd, chainYield_cSeq_heads_forward h₁, chainYield_noHeadCell_iff.1 hb₁,
      chainYield_headCell_iff.1 hc₁, chainYield_cSeq_noHeadCell_forward hc₂]
  · rintro rfl
    exact chainYield_headChainFix hK (fun u _ => rfl)

end TMEnc

end HTN
