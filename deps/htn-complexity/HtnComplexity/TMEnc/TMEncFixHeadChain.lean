import HtnComplexity.TMEnc.TMEncFixTape
/-!
# The head counter of the encoding, cell by cell

The first chain of `HTN.TMEnc.initChainsFix` is the repaired head counter

`C^K_{heads} ; noHead ; head ; C^{K-1}_{noHead}`   (`HTN.TMEnc.headChainFix`),

which answers the requests the tape issues on the `head` channel; the cell at which it answers
`head` rather than `noHead` is the position of the machine head.  Every `head`/`noHead` unit
consumes exactly one request and answers exactly one — there is no free answer, which is what
pins the counter to the tape — so a plan of the encoding runs the counter through
`K² + 3K + 1` units, one per request, which is exactly the budget computed in
`HtnComplexity/TMEnc/TMEncFixRight.lean`.

This file describes the refinements of that chain unit by unit:

* `HTN.TMEnc.headUnitActs` — the three actions of one unit of the head counter;
* `HTN.TMEnc.chainYield_heads` — one cycle of the counter is `noHead, head, noHead^K`;
* `HTN.TMEnc.chainYield_headChainFix` — **the whole chain refines into the sequence of
  `K² + 3K + 1` units whose `head` marks sit at the units `u ≡ 1 (mod K + 2)`**, i.e. at the
  second unit of each cycle.

With `HTN.TMEnc.chainYield_checkers_initChain` and `HTN.TMEnc.chainYield_tapeChain` this
describes all three chains of the initial task network; see `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **The three actions of one unit of the head counter**: it answers one request, and reports
whether the head is at the cell that issued it. -/
def headUnitActs (Q Γ : Type) (present : Bool) : List (TMAct Q Γ) :=
  [TMAct.start SyncKind.head, if present then TMAct.assertHead else TMAct.retractHead,
    TMAct.respond SyncKind.head]

lemma chainYield_headUnit_aux {a : TMAct Q Γ}
    (hls : [[Sum.inl (TMAct.start SyncKind.head), Sum.inl a,
      Sum.inl (TMAct.respond SyncKind.head)]] ∈ bodiesFix N w K t) :
    (domainBod N w K).ChainYield [Sum.inr t]
      [TMAct.start SyncKind.head, a, TMAct.respond SyncKind.head] := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨_, hls, gridYield_singleton_iff.2 ?_⟩
  exact chainYield_cons_inl_iff.2 ⟨_, rfl, chainYield_cons_inl_iff.2 ⟨_, rfl,
    chainYield_cons_inl_iff.2 ⟨[], rfl, chainYield_nil_iff.2 rfl⟩⟩⟩

/-- The unit at which the head is present. -/
lemma chainYield_headCell :
    (domainBod N w K).ChainYield [Sum.inr TMTask.headCell] (headUnitActs Q Γ true) :=
  chainYield_headUnit_aux (by simp [bodiesFix, bodies])

/-- The unit at which the head is absent. -/
lemma chainYield_noHeadCell :
    (domainBod N w K).ChainYield [Sum.inr TMTask.noHeadCell] (headUnitActs Q Γ false) :=
  chainYield_headUnit_aux (by simp [bodiesFix, bodies])

/-- **One cycle of the head counter**: the head is at the second of its `K + 2` units. -/
lemma chainYield_heads {s : ℕ → Bool} (h0 : s 0 = false) (h1 : s 1 = true)
    (hrest : ∀ j, 2 ≤ j → j < K + 2 → s j = false) :
    (domainBod N w K).ChainYield [Sum.inr TMTask.heads]
      (roundStream (K + 2) fun j => headUnitActs Q Γ (s j)) := by
  rw [chainYield_singleton_bod_iff]
  refine ⟨[[Sum.inr TMTask.noHeadCell, Sum.inr TMTask.headCell,
      Sum.inr (TMTask.cSeq TMTask.noHeadCell K)]], by simp [bodiesFix, bodies],
    gridYield_singleton_iff.2 ?_⟩
  have hsplit : (roundStream (K + 2) fun j => headUnitActs Q Γ (s j)) =
      headUnitActs Q Γ false ++ (headUnitActs Q Γ true ++
        (roundStream K fun k => headUnitActs Q Γ false)) := by
    have h := roundStream_add 1 (1 + K) fun j => headUnitActs Q Γ (s j)
    rw [show 1 + (1 + K) = K + 2 by omega] at h
    rw [h, roundStream_one, h0]
    congr 1
    have h' := roundStream_add 1 K fun j => headUnitActs Q Γ (s (1 + j))
    rw [h', roundStream_one, Nat.add_zero, h1]
    congr 1
    refine roundStream_congr fun k hk => ?_
    rw [hrest (1 + (1 + k)) (by omega) (by omega)]
  rw [hsplit, show [Sum.inr TMTask.noHeadCell, Sum.inr TMTask.headCell,
      Sum.inr (TMTask.cSeq TMTask.noHeadCell K)] =
    [(Sum.inr TMTask.noHeadCell : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      ([Sum.inr TMTask.headCell] ++ [Sum.inr (TMTask.cSeq TMTask.noHeadCell K)]) from rfl]
  exact chainYield_app chainYield_noHeadCell
    (chainYield_app chainYield_headCell (chainYield_cSeq_rounds fun _ _ => chainYield_noHeadCell))

/-- The stream of the units of the repaired head counter, split into the `K` full cycles and the
truncated last one. -/
lemma headStream_splitFix (hK : 1 ≤ K) {s : ℕ → Bool}
    (hs : ∀ u < K * K + 3 * K + 1, s u = decide (u % (K + 2) = 1)) :
    (roundStream (K * K + 3 * K + 1) fun u => headUnitActs Q Γ (s u)) =
      (roundStream K fun _ => roundStream (K + 2) fun j => headUnitActs Q Γ (decide (j = 1))) ++
        (headUnitActs Q Γ false ++ (headUnitActs Q Γ true ++
          (roundStream (K - 1) fun _ => headUnitActs Q Γ false))) := by
  have hsum : K * (K + 2) + (K + 1) = K * K + 3 * K + 1 := by ring
  rw [← hsum, roundStream_add]
  congr 1
  · rw [roundStream_mul K (K + 2) fun u => headUnitActs Q Γ (s u)]
    refine roundStream_congr fun b hb => roundStream_congr fun j hj => ?_
    have hlt : b * (K + 2) + j < K * K + 3 * K + 1 := by
      have : b * (K + 2) ≤ (K - 1) * (K + 2) := Nat.mul_le_mul_right _ (by omega)
      have hexp : (K - 1) * (K + 2) + (K + 2) = K * (K + 2) := by
        obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      have : K * (K + 2) ≤ K * K + 3 * K + 1 := by nlinarith
      omega
    rw [hs _ hlt, Nat.add_comm (b * (K + 2)) j, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hj]
  · have h1 : K + 1 = 1 + (1 + (K - 1)) := by omega
    rw [h1, roundStream_add, roundStream_one, roundStream_add, roundStream_one]
    have hle : K * (K + 2) + (K + 1) ≤ K * K + 3 * K + 1 := by omega
    have h0 : s (K * (K + 2) + 0) = false := by
      rw [hs _ (by omega), Nat.add_zero, Nat.mul_mod_left]
      simp
    have h2 : s (K * (K + 2) + (0 + 1)) = true := by
      rw [hs _ (by omega), Nat.add_comm (K * (K + 2)) (0 + 1), Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (show 0 + 1 < K + 2 by omega)]
      simp
    rw [h0, h2]
    congr 1
    congr 1
    refine roundStream_congr fun k hk => ?_
    have hfalse : s (K * (K + 2) + (1 + (1 + k))) = false := by
      rw [hs _ (by omega), Nat.add_comm (K * (K + 2)) (1 + (1 + k)), Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (show 1 + (1 + k) < K + 2 by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    rw [hfalse]

/-- **The repaired head-counter chain of the initial task network refines into its
`K² + 3K + 1` units**: `K` full cycles `noHead, head, noHead^K` and the last cycle truncated
after `K + 1` of its `K + 2` units, so that the head is reported exactly at the units `u` with
`u ≡ 1 (mod K + 2)`. -/
theorem chainYield_headChainFix (hK : 1 ≤ K) {s : ℕ → Bool}
    (hs : ∀ u < K * K + 3 * K + 1, s u = decide (u % (K + 2) = 1)) :
    (domainBod N w K).ChainYield (headChainFix (Q := Q) (Γ := Γ) K)
      (roundStream (K * K + 3 * K + 1) fun u => headUnitActs Q Γ (s u)) := by
  rw [headStream_splitFix hK hs,
    show (headChainFix (Q := Q) (Γ := Γ) K) =
      [Sum.inr (TMTask.cSeq TMTask.heads K)] ++
        ([Sum.inr TMTask.noHeadCell] ++ ([Sum.inr TMTask.headCell] ++
          [Sum.inr (TMTask.cSeq TMTask.noHeadCell (K - 1))])) from rfl]
  refine chainYield_app (chainYield_cSeq_rounds fun b _ =>
    chainYield_heads (by simp) (by simp) (fun j hj2 _ => by simp; omega))
    (chainYield_app chainYield_noHeadCell (chainYield_app chainYield_headCell
      (chainYield_cSeq_rounds fun _ _ => chainYield_noHeadCell)))

end TMEnc

end HTN
