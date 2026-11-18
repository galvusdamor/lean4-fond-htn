import HtnComplexity.TMEnc.TMEncFixMarkClass
import HtnComplexity.TMEnc.CorrectFix
/-!
# The alignment of the head counter, modulo the one-unit slack of the protocol

`HTN.TMEnc.HeadOnCell` — *a transition of a solution plan is taken on the cell the head of the
machine is on* — is the one statement the soundness direction of the repaired Turing-machine
encoding is still missing (`HtnComplexity/TMEnc/TMEncFixCellRun.lean`).

What the head channel gives is `HTN.TMEnc.trCell_iff_headMarkAt`: the cell `n` carries a
transition exactly when the mark of the head counter that its decision *reads* is `true`, the
unit read being `HTN.TMEnc.headUnitIndex D n` **or one more** — the semaphore protocol pins the
counter down only up to one unit, because the prologue of the head counter answers the first
request for free.

This file shows that **the one-unit slack is the whole of the gap**: a solution plan whose
decisions read their own unit — `HTN.TMEnc.ExactMark` — satisfies `HeadOnCell`, and hence the
encoding is sound for such plans (`HTN.TMEnc.encodingSound_of_exactMark`).

`ExactMark` is not vacuous: the plans of the completeness direction satisfy it.  In them a
transition sits at the cell `i (K+1) + h i + 1` of the block `i`, the extra requests issued
before it are `∑_{k < i} moveExtra (mv k) = i - h i`, so its unit index is exactly
`i (K+2) + 1` — the unit the `i`-th mark sits at — while every other cell misses the mark.

## How the proof goes

Write `u(n) = HTN.TMEnc.headUnitIndex D n`, `h(n) = HTN.TMEnc.hdOf D n` (the head position the
moves of the plan prescribe), `B = n / (K+1)` for the block of the cell `n` and
`col = n % (K+1)` for its column.  Under `ExactMark` a cell carries a transition **iff**
`u(n) ≡ 1 (mod K+2)`.  Since `B (K+2) + col = n + B`, the invariant

  `u(n) + h(n) = n + B + s(n)` with `s(n) ∈ {0, 1, 2}`

(`HTN.TMEnc.MarkInv`) makes the mark condition read `col + s ≡ 1 (mod K+2)`, i.e. — the range of
`col - h` being `[-K, K+2]` — `col + s = h + 1`.  The three values of `s` are the three phases of
a block:

* `s = 0`, `col ≤ h + 1`: the transition of the block has not been taken yet, and it is taken
  exactly at `col = h + 1` — which is `HeadOnCell`;
* `s = 1`, `col ≥ h + 1`: it has been taken, and no second one can be taken in the block;
* `s = 2`, `h = 0`: the plan moved left at the left end of the tape.

The two ways of leaving the invariant — the head walking off the right end (`h = K`), and the
left move at `h = 0` — both make the *separator* of a later block read a set mark, and a
separator carries no transition (`HTN.TMEnc.decision_of_separator`); so they cannot happen.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Arithmetic -/

private lemma mod_eq_one_iff' (K B col s u h : ℕ) (hcol : col ≤ K) (hh : h ≤ K) (hs : s ≤ 2)
    (heq : u + h = B * (K + 2) + col + s) : u % (K + 2) = 1 ↔ col + s = h + 1 := by
  have key : (u + h) % (K + 2) = (col + s) % (K + 2) := by
    rw [heq, show B * (K + 2) + col + s = col + s + B * (K + 2) by ring,
      Nat.add_mul_mod_self_right]
  have hcancel : u % (K + 2) = 1 ↔ (u + h) % (K + 2) = (1 + h) % (K + 2) := by
    constructor
    · intro hu
      have hmod : u ≡ 1 [MOD K + 2] := by
        show u % (K + 2) = 1 % (K + 2)
        rw [hu, Nat.mod_eq_of_lt (by omega)]
      exact hmod.add_right h
    · intro hu
      have hmod : u ≡ 1 [MOD K + 2] := Nat.ModEq.add_right_cancel' h hu
      rw [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < K + 2 by omega)] at hmod
      exact hmod
  rw [hcancel, key, Nat.mod_eq_of_lt (show 1 + h < K + 2 by omega)]
  rcases Nat.lt_or_ge (col + s) (K + 2) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · rw [show col + s = K + 2 by omega, Nat.mod_self]
    omega

private lemma divmod_succ_last {K n : ℕ} (hc : n % (K + 1) = K) :
    (n + 1) / (K + 1) = n / (K + 1) + 1 ∧ (n + 1) % (K + 1) = 0 := by
  have hnB := Nat.mod_add_div n (K + 1)
  have h1 : n + 1 = 0 + (K + 1) * (n / (K + 1) + 1) := by
    have hm : (K + 1) * (n / (K + 1) + 1) = (K + 1) * (n / (K + 1)) + (K + 1) := by ring
    omega
  refine ⟨?_, ?_⟩
  · rw [h1, Nat.add_mul_div_left _ _ (show 0 < K + 1 by omega)]; simp
  · rw [h1, Nat.add_mul_mod_self_left]
    simp

private lemma divmod_succ_mid {K n : ℕ} (hc : n % (K + 1) < K) :
    (n + 1) / (K + 1) = n / (K + 1) ∧ (n + 1) % (K + 1) = n % (K + 1) + 1 := by
  have hnB := Nat.mod_add_div n (K + 1)
  have h1 : n + 1 = (n % (K + 1) + 1) + (K + 1) * (n / (K + 1)) := by omega
  refine ⟨?_, ?_⟩
  · rw [h1, Nat.add_mul_div_left _ _ (show 0 < K + 1 by omega),
      Nat.div_eq_of_lt (show n % (K + 1) + 1 < K + 1 by omega)]
    simp
  · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show n % (K + 1) + 1 < K + 1 by omega)]

/-- The invariant is stated in terms of `n + n / (K+1)`; this is the same as
`(n / (K+1)) * (K+2) + n % (K+1)`. -/
private lemma eq_block_form {K n u h s : ℕ} (heq : u + h = n + n / (K + 1) + s) :
    u + h = (n / (K + 1)) * (K + 2) + n % (K + 1) + s := by
  have hnB : n % (K + 1) + (K + 1) * (n / (K + 1)) = n := Nat.mod_add_div n (K + 1)
  have hmul : (n / (K + 1)) * (K + 2) = (K + 1) * (n / (K + 1)) + (n / (K + 1)) := by ring
  omega

/-! ### Where the head counter marks the head -/

/-- The head counter reports the head as present exactly at the units whose index is `1` modulo
`K + 2`. -/
lemma headMarkAt_eq_true_iff {K j : ℕ} : headMarkAt K j = true ↔ j % (K + 2) = 1 :=
  headMarkStd_eq_true_iff

/-! ### Plans whose decisions read their own unit -/

/-- **The decisions of the plan read their own unit of the head counter.**

`HTN.TMEnc.trCell_iff_headMarkAt` says that the cell `n` carries a transition exactly when the
mark of the unit the decision *reads* is set, and that this unit is `headUnitIndex D n` or one
more.  `ExactMark` is the statement that it is always the former — that the head counter is not
one unit ahead of the tape when the decision is taken. -/
def ExactMark (D : SolutionPlanData N w K) : Prop :=
  ∀ n, n / (K + 1) < K → (TrCell D n ↔ headMarkAt K (headUnitIndex D n) = true)

/-- **Every solution plan of the repaired encoding reads its own unit of the head counter.**

In the repaired head counter every unit consumes a request of its own and answers exactly one,
so the two semaphores of the `head` channel pin the counter to the tape: at the decision of the
cell `n` the counter has run exactly `n + 1 + numEx D n` units
(`HTN.TMEnc.headMark_at_decision`). -/
theorem exactMark (D : SolutionPlanData N w K) : ExactMark D :=
  fun _ hu => trCell_iff_headMarkAt D hu

/-- Under `ExactMark` a cell carries a transition exactly when its unit index is `1` modulo
`K + 2`. -/
lemma trCell_iff_mod (D : SolutionPlanData N w K) (hex : ExactMark D) {n : ℕ}
    (hu : n / (K + 1) < K) : TrCell D n ↔ headUnitIndex D n % (K + 2) = 1 := by
  rw [hex n hu, headMarkAt_eq_true_iff]

/-- A separator cell carries no transition. -/
lemma not_trCell_of_separator (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    (hmod : n % (K + 1) = 0) : ¬ TrCell D n := by
  rintro ⟨mv, q, q', a, b, hP⟩
  rw [decision_of_separator D hu hmod] at hP
  exact absurd hP (by simp)

/-- **`ExactMark` has real force**: it makes the cell the head starts on carry a transition.  In
particular a plan that takes no transition at all does not satisfy it — the hypothesis is not
satisfied vacuously, it says that the plan simulates the machine. -/
lemma trCell_one_of_exactMark (D : SolutionPlanData N w K) (hex : ExactMark D) (hK : 1 ≤ K) :
    TrCell D 1 := by
  have hu : (1 : ℕ) / (K + 1) < K := by
    rw [Nat.div_eq_of_lt (by omega)]; omega
  have hu0 : (0 : ℕ) / (K + 1) < K := by simpa using hK
  have h0 : numEx D 1 = numEx D 0 := numEx_separator D hu0 (by simp)
  have hval : headUnitIndex D 1 = 1 := by
    simp only [headUnitIndex, h0, numEx_zero]
  refine (trCell_iff_mod D hex hu).2 ?_
  rw [hval, Nat.mod_eq_of_lt (by omega)]

/-! ### The invariant -/

/-- **The invariant of the head channel.**  `u(n) + h(n) = n + B + s` with `s ∈ {0, 1, 2}`, the
three values being the three phases of a block: before its transition, after it, and after a
left move at the left end of the tape. -/
def MarkInv (D : SolutionPlanData N w K) (n : ℕ) : Prop :=
  hdOf D n ≤ K ∧
    ((headUnitIndex D n + hdOf D n = n + n / (K + 1) ∧ n % (K + 1) ≤ hdOf D n + 1) ∨
     (headUnitIndex D n + hdOf D n = n + n / (K + 1) + 1 ∧ hdOf D n + 1 ≤ n % (K + 1)) ∨
     (headUnitIndex D n + hdOf D n = n + n / (K + 1) + 2 ∧ hdOf D n = 0 ∧
        2 ≤ n % (K + 1)))

/-- **The invariant holds along the whole array.** -/
theorem markInv_of_exactMark (D : SolutionPlanData N w K) (hex : ExactMark D) :
    ∀ n, n < K * (K + 1) → MarkInv D n := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨by simp, Or.inl ⟨by simp [headUnitIndex], by simp⟩⟩
  | succ n ih =>
      intro hn1
      have hnlt : n < K * (K + 1) := by omega
      obtain ⟨hhK, hcases⟩ := ih hnlt
      have hu : n / (K + 1) < K := div_lt_of_lt_mul hnlt
      have hu1 : (n + 1) / (K + 1) < K := div_lt_of_lt_mul hn1
      have hcK : n % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
      have htriff : TrCell D n ↔ headUnitIndex D n % (K + 2) = 1 := trCell_iff_mod D hex hu
      have htriff1 : TrCell D (n + 1) ↔ headUnitIndex D (n + 1) % (K + 2) = 1 :=
        trCell_iff_mod D hex hu1
      -- the contradiction used twice: the next cell is a separator whose mark is set
      have hsep : n % (K + 1) = K →
          headUnitIndex D (n + 1) % (K + 2) = 1 → False := by
        intro hlast hmark
        obtain ⟨-, hmod1⟩ := divmod_succ_last (K := K) (n := n) hlast
        exact not_trCell_of_separator D hu1 hmod1 (htriff1.2 hmark)
      rcases hcases with ⟨heq, hle⟩ | ⟨heq, hle⟩ | ⟨heq, hh0, hle⟩
      · -- phase `s = 0`
        have hblk : headUnitIndex D n + hdOf D n =
            (n / (K + 1)) * (K + 2) + n % (K + 1) + 0 := eq_block_form (by omega)
        have hmod : headUnitIndex D n % (K + 2) = 1 ↔ n % (K + 1) + 0 = hdOf D n + 1 :=
          mod_eq_one_iff' K (n / (K + 1)) (n % (K + 1)) 0 _ _ (by omega) hhK (by omega)
            hblk
        by_cases htr : TrCell D n
        · -- the transition of the block
          have hcol : n % (K + 1) = hdOf D n + 1 := by
            have := hmod.1 (htriff.1 htr); omega
          have htw : TrCellWith D n (mvAt D n) := trCellWith_mvAt htr
          have hu' : headUnitIndex D (n + 1) = headUnitIndex D n + 1 + moveExtra (mvAt D n) :=
            headUnitIndex_succ_of_trCellWith D hu htw
          have hh' : hdOf D (n + 1) = (mvAt D n).apply (hdOf D n) :=
            hdOf_succ_of_trCellWith D htw
          have hnormal : (mvAt D n = Move.left ∧ hdOf D n = 0) ∨
              headUnitIndex D (n + 1) + hdOf D (n + 1) =
                headUnitIndex D n + hdOf D n + 2 := by
            rcases hmv : mvAt D n with _ | _ | _
            · rcases Nat.eq_zero_or_pos (hdOf D n) with h0 | h0
              · exact Or.inl ⟨rfl, h0⟩
              · refine Or.inr ?_
                rw [hu', hh', hmv]
                simp only [moveExtra, Move.apply_left]
                omega
            · refine Or.inr ?_
              rw [hu', hh', hmv]
              simp only [moveExtra, Move.apply_stay]
              omega
            · refine Or.inr ?_
              rw [hu', hh', hmv]
              simp only [moveExtra, Move.apply_right]
              omega
          have hh'le : hdOf D (n + 1) ≤ K := by
            have := Move.apply_le (mvAt D n) (hdOf D n)
            omega
          rcases hnormal with ⟨hmv, h0⟩ | hnorm
          · -- a left move at the left end of the tape
            have hcol1 : n % (K + 1) = 1 := by omega
            have hh'0 : hdOf D (n + 1) = 0 := by simp [hh', hmv, h0]
            have hu'' : headUnitIndex D (n + 1) = headUnitIndex D n + 3 := by
              rw [hu', hmv]; simp [moveExtra]
            by_cases hlast : n % (K + 1) = K
            · -- forces `K = 1`, which the bound on `n` excludes
              exfalso
              have hK1 : K = 1 := by omega
              subst hK1
              omega
            · obtain ⟨hd1, hm1⟩ := divmod_succ_mid (K := K) (n := n) (by omega)
              refine ⟨by omega, Or.inr (Or.inr ⟨?_, by omega, by omega⟩)⟩
              omega
          · by_cases hlast : n % (K + 1) = K
            · obtain ⟨hd1, hm1⟩ := divmod_succ_last (K := K) (n := n) hlast
              refine ⟨hh'le, Or.inl ⟨?_, by omega⟩⟩
              omega
            · obtain ⟨hd1, hm1⟩ := divmod_succ_mid (K := K) (n := n) (by omega)
              have := Move.apply_le (mvAt D n) (hdOf D n)
              refine ⟨hh'le, Or.inr (Or.inl ⟨?_, by omega⟩)⟩
              omega
        · -- no transition: the cell is copied
          have hcol : n % (K + 1) ≤ hdOf D n := by
            by_contra hcon
            exact htr (htriff.2 (hmod.2 (by omega)))
          have hu' : headUnitIndex D (n + 1) = headUnitIndex D n + 1 :=
            headUnitIndex_succ_of_not_trCell D hu htr
          have hh' : hdOf D (n + 1) = hdOf D n := hdOf_succ_of_not D htr
          by_cases hlast : n % (K + 1) = K
          · -- the head would have walked off the right end
            exfalso
            refine hsep hlast ?_
            have hhK' : hdOf D n = K := by omega
            have : headUnitIndex D (n + 1) = 1 + (n / (K + 1)) * (K + 2) := by omega
            rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
          · obtain ⟨hd1, hm1⟩ := divmod_succ_mid (K := K) (n := n) (by omega)
            refine ⟨by omega, Or.inl ⟨?_, by omega⟩⟩
            omega
      · -- phase `s = 1`
        have hblk := eq_block_form (K := K) (n := n) heq
        have hmod : headUnitIndex D n % (K + 2) = 1 ↔ n % (K + 1) + 1 = hdOf D n + 1 :=
          mod_eq_one_iff' K (n / (K + 1)) (n % (K + 1)) 1 _ _ (by omega) hhK (by omega) hblk
        have htr : ¬ TrCell D n := by
          intro h
          have := hmod.1 (htriff.1 h)
          omega
        have hu' : headUnitIndex D (n + 1) = headUnitIndex D n + 1 :=
          headUnitIndex_succ_of_not_trCell D hu htr
        have hh' : hdOf D (n + 1) = hdOf D n := hdOf_succ_of_not D htr
        by_cases hlast : n % (K + 1) = K
        · obtain ⟨hd1, hm1⟩ := divmod_succ_last (K := K) (n := n) hlast
          refine ⟨by omega, Or.inl ⟨?_, by omega⟩⟩
          omega
        · obtain ⟨hd1, hm1⟩ := divmod_succ_mid (K := K) (n := n) (by omega)
          refine ⟨by omega, Or.inr (Or.inl ⟨?_, by omega⟩)⟩
          omega
      · -- phase `s = 2`
        have hblk := eq_block_form (K := K) (n := n) heq
        have hmod : headUnitIndex D n % (K + 2) = 1 ↔ n % (K + 1) + 2 = hdOf D n + 1 :=
          mod_eq_one_iff' K (n / (K + 1)) (n % (K + 1)) 2 _ _ (by omega) hhK (by omega) hblk
        have htr : ¬ TrCell D n := by
          intro h
          have := hmod.1 (htriff.1 h)
          omega
        have hu' : headUnitIndex D (n + 1) = headUnitIndex D n + 1 :=
          headUnitIndex_succ_of_not_trCell D hu htr
        have hh' : hdOf D (n + 1) = hdOf D n := hdOf_succ_of_not D htr
        by_cases hlast : n % (K + 1) = K
        · -- the drift of the left move reaches the next separator
          exfalso
          refine hsep hlast ?_
          have hmul : (n / (K + 1) + 1) * (K + 2) = (n / (K + 1)) * (K + 2) + (K + 2) := by ring
          have hval : headUnitIndex D (n + 1) = 1 + (n / (K + 1) + 1) * (K + 2) := by omega
          rw [hval, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        · obtain ⟨hd1, hm1⟩ := divmod_succ_mid (K := K) (n := n) (by omega)
          refine ⟨by omega, Or.inr (Or.inr ⟨?_, by omega, by omega⟩)⟩
          omega

/-! ### `HeadOnCell`, and soundness -/

/-- **A solution plan whose decisions read their own unit takes its transitions on the cell the
head of the machine is on.** -/
theorem headOnCell_of_exactMark (D : SolutionPlanData N w K) (hex : ExactMark D) :
    HeadOnCell D := by
  intro n hn htr
  obtain ⟨hhK, hcases⟩ := markInv_of_exactMark D hex n hn
  have hu : n / (K + 1) < K := div_lt_of_lt_mul hn
  have hcK : n % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
  have hmark : headUnitIndex D n % (K + 2) = 1 := (trCell_iff_mod D hex hu).1 htr
  rcases hcases with ⟨heq, hle⟩ | ⟨heq, hle⟩ | ⟨heq, hh0, hle⟩
  · have hblk : headUnitIndex D n + hdOf D n =
        (n / (K + 1)) * (K + 2) + n % (K + 1) + 0 := eq_block_form (by omega)
    have hmod := (mod_eq_one_iff' K (n / (K + 1)) (n % (K + 1)) 0 _ _ (by omega) hhK
      (by omega) hblk).1 hmark
    omega
  · have hblk := eq_block_form (K := K) (n := n) heq
    have hmod := (mod_eq_one_iff' K (n / (K + 1)) (n % (K + 1)) 1 _ _ (by omega) hhK
      (by omega) hblk).1 hmark
    omega
  · have hblk := eq_block_form (K := K) (n := n) heq
    have hmod := (mod_eq_one_iff' K (n / (K + 1)) (n % (K + 1)) 2 _ _ (by omega) hhK
      (by omega) hblk).1 hmark
    omega

/-- **Soundness of the repaired encoding for plans that read their own unit.**  If every solution
plan of the encoded problem satisfies `HTN.TMEnc.ExactMark` then solvability of the encoded
problem implies that the machine accepts the input within `K` steps.  By
`HTN.TMEnc.exactMark` the hypothesis always holds. -/
theorem encodingSound_of_exactMark (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hExact : ∀ D : SolutionPlanData N w K, ExactMark D)
    (hsol : (problemFix N w K).Solvable) : N.AcceptsWithin w K :=
  encodingSound_of_headOnCell hw hwK (fun D => headOnCell_of_exactMark D (hExact D)) hsol


/-! ### The sharp count: at most `K` transitions -/

private lemma countP_range_eq_card' (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
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

/-- Under `ExactMark` the unit index of a transition cell is `b (K + 2) + 1` for a mark `b < K`:
the one-unit slack being gone, the `K + 1`-st mark of the head counter — the one of the last
block, at which no decision is taken any more — is out of reach. -/
lemma headUnitIndex_of_trCell_of_exactMark (D : SolutionPlanData N w K) (hex : ExactMark D)
    {n : ℕ} (hn : n < K * (K + 1)) :
    TrCell D n → headUnitIndex D n % (K + 2) = 1 ∧ headUnitIndex D n / (K + 2) < K := by
  intro htr
  have hu : n / (K + 1) < K := div_lt_of_lt_mul hn
  have hmod : headUnitIndex D n % (K + 2) = 1 := (trCell_iff_mod D hex hu).1 htr
  refine ⟨hmod, ?_⟩
  have hex' : numEx D n ≤ K := by
    have hnle : n ≤ (K + 1) * (K + 1) := by nlinarith
    have h1 := numEx_mono D hnle
    have h2 := numEx_total_eq D
    omega
  have hle : headUnitIndex D n ≤ K * (K + 2) := by
    have : K * (K + 1) + (K + 1) = K * (K + 2) + 1 := by ring
    simp only [headUnitIndex]
    omega
  have hdm := Nat.div_add_mod (headUnitIndex D n) (K + 2)
  by_contra hcon
  have hge : (K + 2) * K ≤ (K + 2) * (headUnitIndex D n / (K + 2)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hKK : (K + 2) * K = K * (K + 2) := Nat.mul_comm _ _
  omega

/-- **Under `ExactMark` a solution plan takes at most `K` transitions** — one per block, the
factor two of `HTN.TMEnc.card_transitions_le` being exactly the one-unit slack. -/
theorem card_transitions_le_of_exactMark (D : SolutionPlanData N w K) (hex : ExactMark D)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n < K * (K + 1) ∧ TrCell D n) : S.card ≤ K := by
  classical
  have hmaps : Set.MapsTo (fun n => headUnitIndex D n / (K + 2)) ↑S ↑(Finset.range K) := by
    intro n hn
    obtain ⟨hn₁, hn₂⟩ := hS n (by simpa using hn)
    exact Finset.mem_coe.2 (Finset.mem_range.2
      (headUnitIndex_of_trCell_of_exactMark D hex hn₁ hn₂).2)
  have hinj : Set.InjOn (fun n => headUnitIndex D n / (K + 2)) ↑S := by
    intro x hx y hy hxy
    obtain ⟨hx₁, hx₂⟩ := hS x (by simpa using hx)
    obtain ⟨hy₁, hy₂⟩ := hS y (by simpa using hy)
    have hmx := (headUnitIndex_of_trCell_of_exactMark D hex hx₁ hx₂).1
    have hmy := (headUnitIndex_of_trCell_of_exactMark D hex hy₁ hy₂).1
    have hdx := Nat.div_add_mod (headUnitIndex D x) (K + 2)
    have hdy := Nat.div_add_mod (headUnitIndex D y) (K + 2)
    simp only at hxy
    rw [hxy] at hdx
    exact headUnitIndex_injective D (by omega)
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa using this

/-- **Under `ExactMark` a solution plan has at most `K` transition cells.** -/
theorem countP_trB_le_of_exactMark (D : SolutionPlanData N w K) (hex : ExactMark D) :
    (List.range (K * (K + 1))).countP (trB D) ≤ K := by
  classical
  have hdec : (List.range (K * (K + 1))).countP (trB D)
      = (List.range (K * (K + 1))).countP (fun n => decide (TrCell D n)) := by
    refine List.countP_congr ?_
    intro n _
    by_cases hn : TrCell D n
    · simp [trB_eq_true_iff.2 hn, hn]
    · simp [trB_eq_false_iff.2 hn, hn]
  rw [hdec, countP_range_eq_card']
  refine card_transitions_le_of_exactMark D hex _ ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  exact hn

/-! ### Soundness with the sharp bound -/

/-- **A solution plan that reads its own unit exhibits an accepting run of at most `K` steps.** -/
theorem acceptsWithin_of_exactMark (D : SolutionPlanData N w K) (hwK : w.length ≤ K)
    (hex : ExactMark D) : N.AcceptsWithin w K :=
  acceptsWithin_of_isCellRun_le
    (isCellRun_of_planData D (headAssignment_hdOf D (headOnCell_of_exactMark D hex))) hwK
    (countP_trB_le_of_exactMark D hex)

/-- **Soundness of the repaired encoding, for plans that read their own unit** — with the sharp
bound `K` of the source, rather than the `2 (K + 1)` of
`HTN.TMEnc.encodingSound_of_headAssignment`.

This is `HTN.TMEnc.EncodingSoundFix`, the soundness half of the simulation correctness of the
repaired construction, under the single remaining hypothesis that a solution plan does not
exploit the one-unit slack of the semaphore protocol of the head channel. -/
theorem encodingSoundFix_of_exactMark (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hExact : ∀ D : SolutionPlanData N w K, ExactMark D) : EncodingSoundFix N w K := by
  intro hsol
  obtain ⟨as, hplan⟩ := Problem.solvable_iff_exists_solutionPlan.1 hsol
  obtain ⟨D, -⟩ := exists_planData hw hwK hplan
  exact acceptsWithin_of_exactMark D hwK (hExact D)

/-! ### Soundness, unconditionally -/

/-- **A solution plan takes its transitions on the cell the head of the machine is on.** -/
theorem headOnCell_of_solutionPlan (D : SolutionPlanData N w K) : HeadOnCell D :=
  headOnCell_of_exactMark D (exactMark D)

/-- **Soundness of the simulation of the repaired encoding.**

If the encoded problem is solvable then the machine accepts the input within `K` steps.  This is
`HTN.TMEnc.EncodingSoundFix`, now unconditional: the repaired head counter leaves a solution
plan no slack. -/
theorem encodingSoundFix (hw : 1 ≤ w.length) (hwK : w.length ≤ K) : EncodingSoundFix N w K :=
  encodingSoundFix_of_exactMark hw hwK fun D => exactMark D

end TMEnc

end HTN
