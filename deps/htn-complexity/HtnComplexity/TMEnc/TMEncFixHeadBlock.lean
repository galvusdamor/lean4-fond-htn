import HtnComplexity.TMEnc.TMEncFixHeadAlign
/-!
# No transition on a separator cell

`HTN.TMEnc.cell_separator_copy` says that the *symbol* of a separator cell is copied.  What the
head alignment needs is the sharper statement about the *decision*: the counter that is due on a
separator cell can only take the test `check noHead`, because a transition of the machine reads
a symbol of the alphabet and the separator carries none.

`HTN.TMEnc.decision_of_separator` — **the decision taken on a separator cell is
`check noHead`** — hence, by `HTN.TMEnc.headMark_at_decision`, the head counter does not mark a
separator cell.  This is the fact that forces the marked cell of a block to lie inside the block,
i.e. that the head position read off a solution plan is a genuine tape cell.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **On a separator cell the counter that is due can only test that the head is elsewhere.** -/
theorem decision_of_separator (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    (hmod : n % (K + 1) = 0) :
    D.P (due D n) (n / (K + 1)) = [TMAct.check TMFact.noHead] := by
  have hK0 : ¬ K = 0 := by rintro rfl; exact Nat.not_lt_zero _ hu
  have hdm := Nat.div_add_mod n (K + 1)
  have hnlt : n < (K + 1) * (K + 1) := by
    have h1 : (K + 1) * (n / (K + 1)) + (K + 1) ≤ (K + 1) * K + (K + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have hKK : (K + 1) * K + (K + 1) = (K + 1) * (K + 1) := by ring
    omega
  have hsep : D.sym n = none := by
    have h := D.sepSym (n / (K + 1)) (by omega)
    rw [show n / (K + 1) * (K + 1) = n by rw [Nat.mul_comm]; omega] at h
    exact h
  have hdec := D.decisions (due D n) (due_lt D n) (n / (K + 1)) hu
  rcases stepDecision_iff.1 hdec with ⟨q, q', a, b, mv, -, hPu⟩ | hPu
  · exfalso
    -- what the due counter reads during the cell `n`
    have hsym := symConsistent_cellChunk D hnlt
    rw [counterCell_due, counterSeg_mul, ← symConsistent_filter] at hsym
    have hfilSym : (D.P (due D n) (n / (K + 1))).filter symRel =
        [TMAct.step q (some a) q' (some b)] := by
      have hround : ∀ R : ℕ,
          (roundStream R fun _ => acquireActs Q Γ SyncKind.head).filter (symRel (Q := Q)) = [] := by
        intro R
        induction R with
        | zero => simp
        | succ R ih =>
            rw [roundStream_succ, List.filter_append, ih]
            simp [acquireActs, symRel]
      rw [hPu, List.filter_cons_of_pos (by simp [symRel]), hround]
    have hredSym : SymConsistent (some (D.sym n))
        ((D.P (due D n) (n / (K + 1))).filter symRel ++
          [chkAct Q Γ (D.cc (due D n) (n / (K + 1)))]) := by
      by_cases hu0 : n / (K + 1) = 0
      · rw [if_neg hK0, if_pos hu0, filter_shape_first] at hsym
        rw [hu0]
        exact hsym
      · rw [if_neg hK0, if_neg hu0, if_pos hu, filter_shape_mid, symConsistent_chk_cons] at hsym
        exact hsym.2
    rw [hfilSym, List.cons_append, List.nil_append, symConsistent_step_cons,
      symConsistent_chk] at hredSym
    have : D.sym n = some a := Option.some.inj hredSym.1
    rw [hsep] at this
    exact absurd this (by simp)
  · exact hPu

/-- **The head counter does not mark a separator cell.**  Combined with
`HTN.TMEnc.headMark_at_decision`: at the decision of a separator cell the mark read is `false`. -/
theorem headMark_separator (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    (hmod : n % (K + 1) = 0) : headMarkAt K (n + numEx D n) = false :=
  (headMark_at_decision D hu).2 (decision_of_separator D hu hmod)

/-- **A separator cell issues no extra request**, since no transition is taken there. -/
theorem numEx_separator (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    (hmod : n % (K + 1) = 0) : numEx D (n + 1) = numEx D n := by
  rw [numEx_succ D n, countP_isCall_head_counterCell_due D hu,
    decision_of_separator D hu hmod]
  rfl


/-! ### Where the transitions of a plan sit -/

/-- The number of extra requests issued so far does not decrease. -/
lemma numEx_mono (D : SolutionPlanData N w K) {n m : ℕ} (h : n ≤ m) :
    numEx D n ≤ numEx D m := by
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  rw [roundStream_add, List.countP_append]
  omega

/-- **A transition of the machine can be taken only at a marked position.**

If the counter that is due in the cell `n` takes a transition, then `n + numEx D n` — the index
of the unit of the head counter that answers the request of the cell `n` — is congruent to `1`
modulo `K + 2`.  Those are exactly the positions the repaired head-counter chain marks. -/
theorem transition_index (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    {q q' : Q} {a b : Option Γ} {tl : List (TMAct Q Γ)}
    (hP : D.P (due D n) (n / (K + 1)) = TMAct.step q a q' b :: tl) :
    (n + numEx D n) % (K + 2) = 1 :=
  headMarkStd_eq_true_iff.1 ((headMark_at_decision D hu).1 q q' a b tl hP)

end TMEnc

end HTN
