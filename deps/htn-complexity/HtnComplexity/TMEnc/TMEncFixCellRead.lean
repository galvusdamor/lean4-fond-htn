import HtnComplexity.TMEnc.TMEncFixConsistent
/-!
# What the counter that is due in a cell reads and writes

`HTN.TMEnc.symConsistent_cellChunk` says that the cell `n` of the counter that is due there is
consistent with the symbol `sym n` that the tape has just written.  Unfolding it for the explicit
cell of a counter gives the two statements that the soundness argument needs.  Write
`u = n / (K+1)` for the block and `j = n mod (K+1)` for the position of the cell `n`; the counter
that is due is the one with the delay `j`, and it is in its `u`-th decision cell:

* `HTN.TMEnc.cc_closing` — the **closing** test of its previous `chk` gadget forces
  `cc (u-1) = sym n`: the symbol the counter remembered from the block `u - 1` is the symbol of
  the same position in the block `u`;
* `HTN.TMEnc.cell_decision` — its **decision** is either the test `check noHead`, and then the
  opening test forces `cc u = sym n`, or a transition `step q a q' b` of the machine, and then
  `sym n = a` and `cc u = b`.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The cell of the due counter, written out -/

lemma counterSeg_mul {P : ℕ → List (TMAct Q Γ)} {c : ℕ → Option Γ} (u : ℕ) :
    counterSeg Q Γ K P c ((K + 1) * u) =
      if K = 0 then relCheckActs Q Γ ++ relSyncActs Q Γ
      else if u = 0 then relCheckActs Q Γ ++ (P 0 ++ (chkAct Q Γ (c 0) :: relSyncActs Q Γ))
      else if u < K then relCheckActs Q Γ ++ (chkAct Q Γ (c (u - 1)) ::
        (P u ++ (chkAct Q Γ (c u) :: relSyncActs Q Γ)))
      else relCheckActs Q Γ ++ (chkAct Q Γ (c (K - 1)) :: relSyncActs Q Γ) := by
  have hmod : ((K + 1) * u) % (K + 1) = 0 := Nat.mul_mod_right _ _
  have hdiv : ((K + 1) * u) / (K + 1) = u := Nat.mul_div_cancel_left _ (by omega)
  simp [counterSeg, hmod, hdiv]

/-- The cell `n` of the counter that is due there is its `n / (K+1)`-st decision cell. -/
lemma counterCell_due (D : SolutionPlanData N w K) (n : ℕ) :
    counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n =
      counterSeg Q Γ K (D.P (due D n)) (D.cc (due D n)) ((K + 1) * (n / (K + 1))) := by
  have hdm := Nat.div_add_mod n (K + 1)
  rw [counterCell_of_ge (by rw [d_due]; exact Nat.mod_le _ _)]
  congr 1
  rw [d_due]
  omega

/-! ### The filtered actions -/

@[simp] lemma filter_symRel_relCheckActs : (relCheckActs Q Γ).filter symRel = [] := by
  simp [relCheckActs, symRel]

@[simp] lemma filter_symRel_relSyncActs : (relSyncActs Q Γ).filter symRel = [] := by
  simp [relSyncActs, symRel]

@[simp] lemma symRel_chkAct (c : Option Γ) : symRel (chkAct Q Γ c) = true := rfl

/-- The actions of a decision that touch the fact `sym`: none if the decision is the test that
the head is elsewhere, and the transition itself if it is a transition. -/
lemma filter_symRel_stepDecision {p : List (TMAct Q Γ)} (h : StepDecision N w K p) :
    p.filter symRel = [] ∨
      ∃ (q q' : Q) (a b : Γ) (mv : Move), (q', b, mv) ∈ N.step q a ∧
        p.filter symRel = [TMAct.step q (some a) q' (some b)] := by
  rcases stepDecision_iff.1 h with ⟨q, q', a, b, mv, hmem, rfl⟩ | rfl
  · refine Or.inr ⟨q, q', a, b, mv, hmem, ?_⟩
    have hround : ∀ R : ℕ,
        (roundStream R fun _ => acquireActs Q Γ SyncKind.head).filter (symRel (Q := Q)) = [] := by
      intro R
      induction R with
      | zero => simp
      | succ R ih =>
          rw [roundStream_succ, List.filter_append, ih]
          simp [acquireActs, symRel]
    rw [List.filter_cons_of_pos (by simp [symRel]), hround]
  · exact Or.inl (by simp [symRel])

/-! ### Unfolding consistency on the short lists that occur -/

lemma symConsistent_chk_cons {s : Option (Option Γ)} {cc : Option Γ} {l : List (TMAct Q Γ)} :
    SymConsistent s (chkAct Q Γ cc :: l) ↔ (s = some cc ∧ SymConsistent s l) := by
  rw [symConsistent_cons]
  constructor
  · rintro ⟨h₁, -, h₃⟩
    exact ⟨h₁ cc rfl, h₃⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_, h₂⟩
    · rintro c hc
      have : cc = c := by simpa [chkAct] using hc
      rw [h₁, this]
    · intro q x q' y hxy
      simp [chkAct] at hxy

lemma symConsistent_step_cons {s : Option (Option Γ)} {q q' : Q} {x y : Option Γ}
    {l : List (TMAct Q Γ)} :
    SymConsistent s (TMAct.step q x q' y :: l) ↔ (s = some x ∧ SymConsistent (some y) l) := by
  rw [symConsistent_cons]
  simp only [stepSym]
  constructor
  · rintro ⟨-, h₂, h₃⟩
    exact ⟨h₂ q x q' y rfl, h₃⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨by simp, ?_, h₂⟩
    rintro q₁ x₁ q₁' y₁ heq
    obtain ⟨-, rfl, -, -⟩ := TMAct.step.inj heq
    exact h₁

lemma symConsistent_chk {s : Option (Option Γ)} {cc : Option Γ} :
    SymConsistent s [chkAct Q Γ cc] ↔ s = some cc := by
  rw [symConsistent_chk_cons]
  simp

/-! ### The filtered shapes of a decision cell -/

lemma filter_shape_first {P₀ : List (TMAct Q Γ)} {c₀ : Option Γ} :
    (relCheckActs Q Γ ++ (P₀ ++ (chkAct Q Γ c₀ :: relSyncActs Q Γ))).filter symRel =
      P₀.filter symRel ++ [chkAct Q Γ c₀] := by
  rw [List.filter_append, List.filter_append, List.filter_cons_of_pos (by simp)]
  simp

lemma filter_shape_mid {P₀ : List (TMAct Q Γ)} {c₁ c₀ : Option Γ} :
    (relCheckActs Q Γ ++ (chkAct Q Γ c₁ ::
      (P₀ ++ (chkAct Q Γ c₀ :: relSyncActs Q Γ)))).filter symRel =
      chkAct Q Γ c₁ :: (P₀.filter symRel ++ [chkAct Q Γ c₀]) := by
  rw [List.filter_append, List.filter_cons_of_pos (by simp), List.filter_append,
    List.filter_cons_of_pos (by simp)]
  simp

lemma filter_shape_last {c₁ : Option Γ} :
    (relCheckActs Q Γ ++ (chkAct Q Γ c₁ :: relSyncActs Q Γ)).filter symRel =
      [chkAct Q Γ c₁] := by
  rw [List.filter_append, List.filter_cons_of_pos (by simp)]
  simp

/-! ### The two readings -/

/-- **The closing test of a `chk` gadget reads the symbol of the cell in which it is
executed.**  The counter that is due in the cell `n` closes, there, the gadget it opened `K + 1`
cells earlier: the symbol it remembered is the symbol of the cell `n`. -/
theorem cc_closing (D : SolutionPlanData N w K) (hK : 1 ≤ K) {n : ℕ}
    (hn : n < (K + 1) * (K + 1)) (hu : 1 ≤ n / (K + 1)) :
    D.cc (due D n) (n / (K + 1) - 1) = D.sym n := by
  have hcons := symConsistent_cellChunk D hn
  rw [counterCell_due, counterSeg_mul, ← symConsistent_filter] at hcons
  set u := n / (K + 1) with hudef
  set P := D.P (due D n) with hP
  set c := D.cc (due D n) with hc
  have hK0 : ¬ K = 0 := by omega
  have hu0 : ¬ u = 0 := by omega
  by_cases huK : u < K
  · rw [if_neg hK0, if_neg hu0, if_pos huK, filter_shape_mid] at hcons
    rw [symConsistent_chk_cons] at hcons
    exact (Option.some.inj hcons.1).symm
  · have h1 : (K + 1) * u ≤ n := by
      have hdm := Nat.div_add_mod n (K + 1)
      rw [← hudef] at hdm
      omega
    have h2 : u < K + 1 := by
      by_contra hcon
      have hle : (K + 1) * (K + 1) ≤ (K + 1) * u := Nat.mul_le_mul_left _ (by omega)
      omega
    have huK' : u = K := by omega
    rw [if_neg hK0, if_neg hu0, if_neg huK, filter_shape_last, symConsistent_chk] at hcons
    rw [huK']
    exact (Option.some.inj hcons).symm

/-- **The decision the due counter takes in the cell `n`**: either the test that the head is
elsewhere, and then the symbol it remembers for the next block is the symbol of the cell `n`, or
a transition of the machine, which reads the symbol of the cell `n` and writes the symbol the
counter remembers. -/
theorem cell_decision (D : SolutionPlanData N w K) (hK : 1 ≤ K) {n : ℕ}
    (hn : n < (K + 1) * (K + 1)) (hu : n / (K + 1) < K) :
    D.cc (due D n) (n / (K + 1)) = D.sym n ∨
      ∃ (q q' : Q) (a b : Γ) (mv : Move), (q', b, mv) ∈ N.step q a ∧
        D.sym n = some a ∧ D.cc (due D n) (n / (K + 1)) = some b := by
  have hcons := symConsistent_cellChunk D hn
  rw [counterCell_due, counterSeg_mul, ← symConsistent_filter] at hcons
  set u := n / (K + 1) with hudef
  set P := D.P (due D n) with hP
  set c := D.cc (due D n) with hc
  have hK0 : ¬ K = 0 := by omega
  have hdec := D.decisions (due D n) (due_lt D n) u hu
  -- reduce to the consistency of `(P u).filter ++ [chkAct (c u)]`
  have hred : SymConsistent (some (D.sym n)) ((P u).filter symRel ++ [chkAct Q Γ (c u)]) := by
    by_cases hu0 : u = 0
    · rw [if_neg hK0, if_pos hu0, filter_shape_first] at hcons
      rw [hu0]
      exact hcons
    · rw [if_neg hK0, if_neg hu0, if_pos hu, filter_shape_mid, symConsistent_chk_cons] at hcons
      exact hcons.2
  rcases filter_symRel_stepDecision hdec with hf | hf
  · left
    rw [hf, List.nil_append, symConsistent_chk] at hred
    exact (Option.some.inj hred).symm
  · right
    obtain ⟨q, q', a, b, mv, hmem, hfp⟩ := hf
    rw [hfp, List.cons_append, List.nil_append, symConsistent_step_cons,
      symConsistent_chk] at hred
    exact ⟨q, q', a, b, mv, hmem, Option.some.inj hred.1, (Option.some.inj hred.2).symm⟩

/-! ### Consecutive blocks -/

/-- Two cells at the same position of their blocks are served by the same counter. -/
lemma due_congr (D : SolutionPlanData N w K) {n₁ n₂ : ℕ} (h : n₁ % (K + 1) = n₂ % (K + 1)) :
    due D n₁ = due D n₂ :=
  D.dinj _ (due_lt D n₁) _ (due_lt D n₂) (by rw [d_due, d_due, h])

/-- **A cell of the tape and the cell `K + 1` positions later — the same position of the next
block — either carry the same symbol or differ by a transition of the machine.**  Which of the
two happens is decided by the counter that is due at that position: it either tests that the head
is elsewhere, and then copies the symbol, or applies a transition. -/
theorem sym_copy_or_step (D : SolutionPlanData N w K) (hK : 1 ≤ K) {n : ℕ}
    (hn : n / (K + 1) < K) :
    D.sym (n + (K + 1)) = D.sym n ∨
      ∃ (q q' : Q) (a b : Γ) (mv : Move), (q', b, mv) ∈ N.step q a ∧
        D.sym n = some a ∧ D.sym (n + (K + 1)) = some b := by
  have hdm := Nat.div_add_mod n (K + 1)
  have hmod : n % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
  have hnlt : n < (K + 1) * (K + 1) := by
    have : (K + 1) * (n / (K + 1)) + (K + 1) ≤ (K + 1) * K + (K + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have hKK : (K + 1) * K + (K + 1) = (K + 1) * (K + 1) := by ring
    omega
  -- the cell `K + 1` positions later
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
  have hclose := cc_closing D hK hnlt' (by rw [hdiv']; exact Nat.le_add_left 1 _)
  rw [hdiv', due_congr D hmod'] at hclose
  simp only [Nat.add_sub_cancel] at hclose
  rcases cell_decision D hK hnlt hn with hcopy | ⟨q, q', a, b, mv, hmem, ha, hb⟩
  · exact Or.inl (by rw [← hclose, hcopy])
  · exact Or.inr ⟨q, q', a, b, mv, hmem, ha, by rw [← hclose, hb]⟩

end TMEnc

end HTN
