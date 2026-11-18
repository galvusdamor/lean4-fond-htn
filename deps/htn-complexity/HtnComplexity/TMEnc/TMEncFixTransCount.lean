import HtnComplexity.TMEnc.TMEncFixHeadTotal
/-!
# How many transitions a solution plan can take

`HTN.TMEnc.transition_index` says that the counter that is due in the cell `n` can take a
transition of the machine only if `n + numEx D n` — the index of the unit of the head counter
that answers the request of that cell — is congruent to `1` modulo `K + 2`.  The head counter
marks the head as present at exactly `K + 1` of its units, and the index

`HTN.TMEnc.headBlockIndex D n = (n + numEx D n) / (K + 2)`

names the mark a transition at the cell `n` reads.  Since `n ↦ n + numEx D n` is strictly
increasing, no two cells can read the same mark, and only the `K` marks of the blocks that carry
a decision are available, so

`HTN.TMEnc.card_transitions_le` — **a solution plan takes at most `K` transitions.**

This is the counting half of the soundness direction.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- The index of the unit of the head counter that answers the request of the cell `n`. -/
def headUnitIndex (D : SolutionPlanData N w K) (n : ℕ) : ℕ := n + numEx D n

/-- **The unit index is strictly increasing in the cell.** -/
lemma headUnitIndex_strictMono (D : SolutionPlanData N w K) {n m : ℕ} (h : n < m) :
    headUnitIndex D n < headUnitIndex D m := by
  have := numEx_mono D (le_of_lt h)
  simp only [headUnitIndex]
  omega

lemma headUnitIndex_injective (D : SolutionPlanData N w K) {n m : ℕ}
    (h : headUnitIndex D n = headUnitIndex D m) : n = m := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (headUnitIndex_strictMono D hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (headUnitIndex_strictMono D hgt))

/-- **The mark a transition at the cell `n` reads**, numbered from `0`. -/
def headBlockIndex (D : SolutionPlanData N w K) (n : ℕ) : ℕ := headUnitIndex D n / (K + 2)

/-- A transition at the cell `n` sits exactly at the mark `headBlockIndex D n`. -/
lemma headUnitIndex_of_transition (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    {q q' : Q} {a b : Option Γ} {tl : List (TMAct Q Γ)}
    (hP : D.P (due D n) (n / (K + 1)) = TMAct.step q a q' b :: tl) :
    headUnitIndex D n = headBlockIndex D n * (K + 2) + 1 := by
  have hmod : headUnitIndex D n % (K + 2) = 1 := transition_index D hu hP
  have hdm := Nat.div_add_mod (headUnitIndex D n) (K + 2)
  have hcomm : (K + 2) * (headUnitIndex D n / (K + 2)) =
      headUnitIndex D n / (K + 2) * (K + 2) := Nat.mul_comm _ _
  simp only [headBlockIndex]
  omega

/-- A cell at which a decision is taken lies in the first `K` blocks. -/
lemma lt_of_div_lt {n : ℕ} (hu : n / (K + 1) < K) : n < K * (K + 1) :=
  (Nat.div_lt_iff_lt_mul (Nat.succ_pos K)).1 hu

/-- **Every mark a transition reads is one of the `K` marks the blocks of the diagram carry.** -/
lemma headBlockIndex_lt (D : SolutionPlanData N w K) {n : ℕ}
    (hu : n / (K + 1) < K) {q q' : Q} {a b : Option Γ} {tl : List (TMAct Q Γ)}
    (hP : D.P (due D n) (n / (K + 1)) = TMAct.step q a q' b :: tl) :
    headBlockIndex D n < K := by
  have hK : 1 ≤ K := Nat.lt_of_le_of_lt (Nat.zero_le _) hu
  have hn : n < K * (K + 1) := lt_of_div_lt hu
  have hexp1 : K * (K + 1) = K * K + K := by ring
  have hle1 : K * (K + 1) ≤ (K + 1) * (K + 1) := Nat.mul_le_mul_right _ (by omega)
  have hle : numEx D n ≤ K := by
    have h1 := numEx_mono D (le_of_lt (show n < (K + 1) * (K + 1) by omega))
    have h2 := numEx_total_eq D
    omega
  have hidx := headUnitIndex_of_transition D hu hP
  have hg : headUnitIndex D n < K * K + 2 * K := by
    simp only [headUnitIndex]
    omega
  by_contra hcon
  have hge : K * (K + 2) ≤ headBlockIndex D n * (K + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hexp : K * (K + 2) = K * K + 2 * K := by ring
  omega

/-- **The first transition of a plan reads a mark of its own block or of an earlier one.**

Before any transition has been taken there are no extra requests, so the unit that answers the
cell `n` is the unit `n` itself, and the mark it carries is the one of the block `n / (K + 1)`
or of an earlier block. -/
lemma headBlockIndex_le_block_of_numEx_zero (D : SolutionPlanData N w K) {n : ℕ}
    (hu : n / (K + 1) < K) (hex : numEx D n = 0) {q q' : Q} {a b : Option Γ}
    {tl : List (TMAct Q Γ)} (hP : D.P (due D n) (n / (K + 1)) = TMAct.step q a q' b :: tl) :
    headBlockIndex D n ≤ n / (K + 1) := by
  have hg : headUnitIndex D n = n := by simp [headUnitIndex, hex]
  have hle : headBlockIndex D n * (K + 2) ≤ n := by
    have := headUnitIndex_of_transition D hu hP
    omega
  have hdm := Nat.div_add_mod n (K + 1)
  have hmod : n % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
  by_contra hcon
  have hge : (n / (K + 1) + 1) * (K + 2) ≤ headBlockIndex D n * (K + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **A solution plan takes at most `K` transitions.**

The statement is about an arbitrary finite set `S` of cells at each of which the counter that is
due takes a transition of the machine; `S.card ≤ K` bounds the number of machine steps a
solution plan can encode. -/
theorem card_transitions_le (D : SolutionPlanData N w K) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n < (K + 1) * (K + 1) ∧ n / (K + 1) < K ∧
      ∃ (q q' : Q) (a b : Option Γ) (tl : List (TMAct Q Γ)),
        D.P (due D n) (n / (K + 1)) = TMAct.step q a q' b :: tl) :
    S.card ≤ K := by
  classical
  have hmaps : Set.MapsTo (headBlockIndex D) ↑S ↑(Finset.range K) := by
    intro n hn
    obtain ⟨-, hu, q, q', a, b, tl, hP⟩ := hS n hn
    exact Finset.mem_range.2 (headBlockIndex_lt D hu hP)
  have hinj : Set.InjOn (headBlockIndex D) ↑S := by
    intro x hx y hy h
    obtain ⟨-, hux, qx, qx', ax, bx, tlx, hPx⟩ := hS x hx
    obtain ⟨-, huy, qy, qy', ay, by', tly, hPy⟩ := hS y hy
    refine headUnitIndex_injective D ?_
    rw [headUnitIndex_of_transition D hux hPx, headUnitIndex_of_transition D huy hPy, h]
  simpa using Finset.card_le_card_of_injOn (headBlockIndex D) hmaps hinj

end TMEnc

end HTN
