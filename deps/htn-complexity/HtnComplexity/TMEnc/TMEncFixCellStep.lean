import HtnComplexity.TMEnc.TMEncFixStCell
/-!
# A cell of the space–time diagram: copied, or changed by a transition

`HTN.TMEnc.sym_copy_or_step` says that a cell of the tape and the cell `K + 1` positions later
either carry the same symbol or differ by a transition of the machine.  With the state
(`HTN.TMEnc.stAt`) available, that dichotomy can be stated *together with the state of the
machine*, which is what the simulation argument needs:

* `HTN.TMEnc.cell_copy_or_step` — in the cell `n` of a block that is not the last one, either the
  symbol is copied to the next block and the state does not change, or the counter that is due
  applies a transition `(stAt D (n+1), b, mv) ∈ N.step (stAt D n) a` which reads the symbol `a` of
  the cell and writes the symbol `b` into the same position of the next block;
* `HTN.TMEnc.stAt_succ_of_last_block` — in the last block no transition is taken, so the state no
  longer changes.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Unfolding state consistency on the short lists that occur -/

@[simp] lemma stRel_check_noHead :
    stRel (TMAct.check (TMFact.noHead : TMFact Q Γ)) = false := rfl

@[simp] lemma stRel_step (q q' : Q) (x y : Option Γ) :
    stRel (TMAct.step q x q' y) = true := rfl

lemma stConsistent_step_cons {q q₁ q₁' : Q} {x y : Option Γ} {l : List (TMAct Q Γ)} :
    StConsistent q (TMAct.step q₁ x q₁' y :: l) ↔ (q₁ = q ∧ StConsistent q₁' l) := by
  rw [stConsistent_cons]
  simp only [stepStQ]
  constructor
  · rintro ⟨-, h₂, h₃⟩
    exact ⟨h₂ q₁ x q₁' y rfl, h₃⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_, h₂⟩
    · intro r hr
      simp at hr
    · rintro q₂ x₂ q₂' y₂ heq
      obtain ⟨rfl, -, -, -⟩ := TMAct.step.inj heq
      exact h₁

/-! ### The filtered shapes of a decision cell -/

lemma filter_stRel_shape_first {P₀ : List (TMAct Q Γ)} {c₀ : Option Γ} :
    (relCheckActs Q Γ ++ (P₀ ++ (chkAct Q Γ c₀ :: relSyncActs Q Γ))).filter stRel =
      P₀.filter stRel := by
  rw [List.filter_append, List.filter_append, List.filter_cons_of_neg (by simp)]
  simp

lemma filter_stRel_shape_mid {P₀ : List (TMAct Q Γ)} {c₁ c₀ : Option Γ} :
    (relCheckActs Q Γ ++ (chkAct Q Γ c₁ ::
      (P₀ ++ (chkAct Q Γ c₀ :: relSyncActs Q Γ)))).filter stRel = P₀.filter stRel := by
  rw [List.filter_append, List.filter_cons_of_neg (by simp), List.filter_append,
    List.filter_cons_of_neg (by simp)]
  simp

lemma filter_stRel_shape_last {c₁ : Option Γ} :
    (relCheckActs Q Γ ++ (chkAct Q Γ c₁ :: relSyncActs Q Γ)).filter stRel = [] := by
  rw [List.filter_append, List.filter_cons_of_neg (by simp)]
  simp

/-- The actions of a decision that touch the fact `st`: none if the decision is the test that the
head is elsewhere, and the transition itself if it is a transition. -/
lemma filter_stRel_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    p.filter stRel = [] ∨
      ∃ (q q' : Q) (a b : Γ) (mv : Move), (q', b, mv) ∈ N.step q a ∧
        p.filter stRel = [TMAct.step q (some a) q' (some b)] := by
  rcases stepDecision_iff.1 h with ⟨q, q', a, b, mv, hmem, rfl⟩ | rfl
  · refine Or.inr ⟨q, q', a, b, mv, hmem, ?_⟩
    have hround : ∀ R : ℕ,
        (roundStream R fun _ => acquireActs Q Γ SyncKind.head).filter (stRel (Q := Q)) = [] := by
      intro R
      induction R with
      | zero => simp
      | succ R ih =>
          rw [roundStream_succ, List.filter_append, ih]
          simp [acquireActs, stRel]
    rw [List.filter_cons_of_pos (by simp), hround]
  · exact Or.inl (by simp)

/-! ### The last block -/

/-- **In the last block no counter takes a transition**, so the state no longer changes. -/
theorem stAt_succ_of_last_block (D : SolutionPlanData N w K) {n : ℕ}
    (hn : n < (K + 1) * (K + 1)) (hu : K ≤ n / (K + 1)) : stAt D (n + 1) = stAt D n := by
  have hzero : (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n).countP
      stRel = 0 := by
    have hle : n / (K + 1) ≤ K := by
      by_contra hcon
      have : (K + 1) * (K + 1) ≤ (K + 1) * (n / (K + 1)) := Nat.mul_le_mul_left _ (by omega)
      have hdm := Nat.div_add_mod n (K + 1)
      omega
    have huK : n / (K + 1) = K := by omega
    rw [counterCell_due, counterSeg_mul, List.countP_eq_length_filter]
    by_cases hK0 : K = 0
    · rw [if_pos hK0]
      simp [relCheckActs, relSyncActs, stRel]
    · rw [if_neg hK0, if_neg (by omega : ¬ n / (K + 1) = 0), if_neg (by omega : ¬ n / (K + 1) < K),
        filter_stRel_shape_last]
      rfl
  rw [stAt, stAt, numTr_succ, hzero, Nat.add_zero]

/-- **The state does not change any more once the last block has begun.** -/
theorem stAt_last_block (D : SolutionPlanData N w K) {t : ℕ}
    (ht : K * (K + 1) + t ≤ (K + 1) * (K + 1)) :
    stAt D (K * (K + 1) + t) = stAt D (K * (K + 1)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hKK : (K + 1) * (K + 1) = K * (K + 1) + (K + 1) := by ring
      have hlt : K * (K + 1) + t < (K + 1) * (K + 1) := by omega
      have hdiv : (K * (K + 1) + t) / (K + 1) = K := by
        rw [show K * (K + 1) + t = t + K * (K + 1) by ring,
          Nat.add_mul_div_right _ _ (show 0 < K + 1 by omega),
          Nat.div_eq_of_lt (show t < K + 1 by omega)]
        omega
      rw [show K * (K + 1) + (t + 1) = (K * (K + 1) + t) + 1 by ring,
        stAt_succ_of_last_block D hlt (by rw [hdiv]), ih (by omega)]

/-- **When the last block begins, the machine is already in the accepting state the plan tests
for.** -/
theorem stAt_lastBlock_eq (D : SolutionPlanData N w K) : stAt D (K * (K + 1)) = D.f := by
  have h := stAt_last_block D (t := K + 1) (by ring_nf; omega)
  rw [show K * (K + 1) + (K + 1) = (K + 1) * (K + 1) by ring] at h
  rw [← h, stAt_full]

/-! ### A cell of a block that is not the last one -/

/-- **What happens in the cell `n` of a block that is not the last one.**

The counter that is due there either tests that the head is elsewhere — and then the symbol of the
cell is copied to the same position of the next block and the state of the machine does not
change — or it applies a transition of the machine, which reads the symbol of the cell, writes the
new symbol into the same position of the next block and changes the state.

The statement records **which** of the two decisions the counter took, so that the two cases can
be told apart by the plan; `cell_copy_or_step` below is the plain disjunction. -/
theorem cell_copy_or_step_classified (D : SolutionPlanData N w K) {n : ℕ}
    (hu : n / (K + 1) < K) :
    (D.P (due D n) (n / (K + 1)) = [TMAct.check TMFact.noHead] ∧
        D.sym (n + (K + 1)) = D.sym n ∧ stAt D (n + 1) = stAt D n) ∨
      ∃ (q q' : Q) (a b : Γ) (mv : Move),
        D.P (due D n) (n / (K + 1)) = TMAct.step q (some a) q' (some b) ::
            roundStream (moveExtra mv) (fun _ => acquireActs Q Γ SyncKind.head) ∧
          (stAt D (n + 1), b, mv) ∈ N.step (stAt D n) a ∧
          D.sym n = some a ∧ D.sym (n + (K + 1)) = some b := by
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · simp at hu
    · exact h
  have hK0 : ¬ K = 0 := by omega
  have hdm := Nat.div_add_mod n (K + 1)
  have hmod : n % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
  have hnlt : n < (K + 1) * (K + 1) := by
    have : (K + 1) * (n / (K + 1)) + (K + 1) ≤ (K + 1) * K + (K + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have hKK : (K + 1) * K + (K + 1) = (K + 1) * (K + 1) := by ring
    omega
  -- the same position of the next block
  have hdiv' : (n + (K + 1)) / (K + 1) = n / (K + 1) + 1 := by
    rw [Nat.add_div_right _ (by omega)]
  have hmod' : (n + (K + 1)) % (K + 1) = n % (K + 1) := Nat.add_mod_right _ _
  have hnlt' : n + (K + 1) < (K + 1) * (K + 1) := by
    have : (K + 1) * (n / (K + 1) + 1) + (K + 1) ≤ (K + 1) * K + (K + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have hKK : (K + 1) * K + (K + 1) = (K + 1) * (K + 1) := by ring
    have hdm' := Nat.div_add_mod (n + (K + 1)) (K + 1)
    rw [hdiv', hmod'] at hdm'
    omega
  have hclose : D.cc (due D n) (n / (K + 1)) = D.sym (n + (K + 1)) := by
    have h := cc_closing D hK hnlt' (by rw [hdiv']; exact Nat.le_add_left 1 _)
    rw [hdiv', due_congr D hmod'] at h
    simpa using h
  set u := n / (K + 1) with hudef
  set P := D.P (due D n) with hP
  set c := D.cc (due D n) with hc
  -- the symbols the due counter compares
  have hsym := symConsistent_cellChunk D hnlt
  rw [counterCell_due, counterSeg_mul, ← symConsistent_filter] at hsym
  have hredSym : SymConsistent (some (D.sym n)) ((P u).filter symRel ++ [chkAct Q Γ (c u)]) := by
    by_cases hu0 : u = 0
    · rw [if_neg hK0, if_pos hu0, filter_shape_first] at hsym
      rw [hu0]
      exact hsym
    · rw [if_neg hK0, if_neg hu0, if_pos hu, filter_shape_mid, symConsistent_chk_cons] at hsym
      exact hsym.2
  -- the state the due counter is in
  obtain ⟨hcons, hstate⟩ := stAt_cellChunk D hnlt
  rw [counterCell_due, counterSeg_mul, ← stConsistent_filter] at hcons
  rw [counterCell_due, counterSeg_mul, ← lastStQ_filter] at hstate
  have hshape : (if K = 0 then relCheckActs Q Γ ++ relSyncActs Q Γ
      else if u = 0 then relCheckActs Q Γ ++ (P 0 ++ (chkAct Q Γ (c 0) :: relSyncActs Q Γ))
      else if u < K then relCheckActs Q Γ ++ (chkAct Q Γ (c (u - 1)) ::
        (P u ++ (chkAct Q Γ (c u) :: relSyncActs Q Γ)))
      else relCheckActs Q Γ ++ (chkAct Q Γ (c (K - 1)) ::
        relSyncActs Q Γ)).filter stRel = (P u).filter stRel := by
    by_cases hu0 : u = 0
    · rw [if_neg hK0, if_pos hu0, filter_stRel_shape_first, hu0]
    · rw [if_neg hK0, if_neg hu0, if_pos hu, filter_stRel_shape_mid]
  rw [hshape] at hcons hstate
  -- the decision
  have hdec := D.decisions (due D n) (due_lt D n) u hu
  rw [← hP] at hdec
  rcases stepDecision_iff.1 hdec with ⟨q, q', a, b, mv, hmem, hPu⟩ | hPu
  · -- a transition of the machine
    have hfil : (P u).filter stRel = [TMAct.step q (some a) q' (some b)] := by
      have hround : ∀ R : ℕ,
          (roundStream R fun _ => acquireActs Q Γ SyncKind.head).filter (stRel (Q := Q)) = [] := by
        intro R
        induction R with
        | zero => simp
        | succ R ih =>
            rw [roundStream_succ, List.filter_append, ih]
            simp [acquireActs, stRel]
      rw [hPu, List.filter_cons_of_pos (by simp), hround]
    have hfilSym : (P u).filter symRel = [TMAct.step q (some a) q' (some b)] := by
      have hround : ∀ R : ℕ,
          (roundStream R fun _ => acquireActs Q Γ SyncKind.head).filter (symRel (Q := Q)) = [] := by
        intro R
        induction R with
        | zero => simp
        | succ R ih =>
            rw [roundStream_succ, List.filter_append, ih]
            simp [acquireActs, symRel]
      rw [hPu, List.filter_cons_of_pos (by simp [symRel]), hround]
    rw [hfil, stConsistent_step_cons] at hcons
    rw [hfil] at hstate
    rw [hfilSym, List.cons_append, List.nil_append, symConsistent_step_cons,
      symConsistent_chk] at hredSym
    have hq : q = stAt D n := hcons.1
    have hq' : stAt D (n + 1) = q' := by
      rw [hstate]
      rfl
    refine Or.inr ⟨q, q', a, b, mv, hPu, ?_, ?_, ?_⟩
    · rw [hq', ← hq]
      exact hmem
    · exact Option.some.inj hredSym.1
    · rw [← hclose]
      exact (Option.some.inj hredSym.2).symm
  · -- the test that the head is elsewhere
    have hfil : (P u).filter stRel = [] := by rw [hPu]; simp
    have hfilSym : (P u).filter symRel = [] := by rw [hPu]; simp [symRel]
    rw [hfilSym, List.nil_append, symConsistent_chk] at hredSym
    rw [hfil] at hstate
    refine Or.inl ⟨hPu, ?_, ?_⟩
    · rw [← hclose, ← Option.some.inj hredSym]
    · rw [hstate]
      rfl

/-- **What happens in the cell `n` of a block that is not the last one** (the plain
disjunction; `cell_copy_or_step_classified` also records the decision). -/
theorem cell_copy_or_step (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K) :
    (D.sym (n + (K + 1)) = D.sym n ∧ stAt D (n + 1) = stAt D n) ∨
      ∃ (a b : Γ) (mv : Move), (stAt D (n + 1), b, mv) ∈ N.step (stAt D n) a ∧
        D.sym n = some a ∧ D.sym (n + (K + 1)) = some b := by
  rcases cell_copy_or_step_classified D hu with ⟨-, h⟩ | ⟨q, q', a, b, mv, -, h₁, h₂, h₃⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, mv, h₁, h₂, h₃⟩

/-- **No transition is taken on a separator cell.**  The first cell of a block carries the
separator `#`, and a transition of the machine reads a symbol of the alphabet, so the counter
that is due on a separator can only copy it. -/
theorem cell_separator_copy (D : SolutionPlanData N w K) {n : ℕ} (hu : n / (K + 1) < K)
    (hmod : n % (K + 1) = 0) :
    D.sym (n + (K + 1)) = D.sym n ∧ stAt D (n + 1) = stAt D n := by
  have hdm := Nat.div_add_mod n (K + 1)
  have hsep : D.sym n = none := by
    have h := D.sepSym (n / (K + 1)) (by omega)
    rw [show n / (K + 1) * (K + 1) = n by rw [Nat.mul_comm]; omega] at h
    exact h
  rcases cell_copy_or_step D hu with h | ⟨a, b, mv, -, ha, -⟩
  · exact h
  · rw [hsep] at ha
    exact absurd ha (by simp)

end TMEnc

end HTN
