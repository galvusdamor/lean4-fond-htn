import HtnComplexity.TMEnc.TMEncFixCellCut
import HtnComplexity.TMEnc.TMEncFixSymFact
/-!
# Which symbol a cell counter reads

`HTN.TMEnc.exists_cellCut` cuts a solution plan at the `assert` of the cell `n` of the tape and
shows that the cell `n` of every cell counter is executed in the piece `m` that follows it.  Of
the `K + 1` counters exactly one is *due* in the cell `n` — the one whose delay is `n mod (K+1)`
(`HTN.TMEnc.due`) — and all the others merely wait.  Since only the tape `assert`s and only a
counter `step`s, the actions of `m` that touch the fact `sym` are therefore exactly those of the
cell `n` of the due counter (`HTN.TMEnc.filter_cellChunk`).

* `HTN.TMEnc.symRel` — the actions that read or write the fact `sym`;
* `HTN.TMEnc.due` — the counter that is due in a cell;
* `HTN.TMEnc.filter_cellChunk` — **the only actions of the cell `n` of the plan that touch `sym`
  are those of the due counter**, and they all follow the tape's `assert (sym n)`.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The actions that touch the fact `sym` -/

/-- The actions that read or write the fact `sym`: the `assert`s of the tape, the `step`s of the
counters and the tests of a `chk` gadget. -/
def symRel : TMAct Q Γ → Bool
  | .assert _ => true
  | .step _ _ _ _ => true
  | .check (.sym _) => true
  | _ => false

/-- An action that does not touch `sym` does not change it. -/
lemma stepSym_of_not_symRel {a : TMAct Q Γ} (ha : symRel a = false)
    (c : Option (Option Γ)) : stepSym c a = c := by
  cases a <;> simp_all [symRel, stepSym]

/-- **The symbol on the tape depends only on the actions that touch it.** -/
lemma lastSym_filter (c : Option (Option Γ)) : ∀ l : List (TMAct Q Γ),
    lastSym c (l.filter symRel) = lastSym c l := by
  intro l
  induction l generalizing c with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : symRel a
      · rw [List.filter_cons_of_pos ha, lastSym_cons, lastSym_cons, ih]
      · simp only [Bool.not_eq_true] at ha
        rw [List.filter_cons_of_neg (by simp [ha]), ih, lastSym_cons,
          stepSym_of_not_symRel ha]

/-! ### The streams that do not touch `sym` -/

@[simp] lemma filter_symRel_waitCellActs :
    (waitCellActs Q Γ).filter symRel = [] := by
  simp [waitCellActs, symRel]

@[simp] lemma filter_symRel_cellTail : (cellTail Q Γ K).filter symRel = [] :=
  cellTail_filter fun _ => ⟨rfl, rfl⟩

@[simp] lemma filter_symRel_headUnitActs (b : Bool) :
    (headUnitActs Q Γ b).filter symRel = [] := by
  cases b <;> simp [headUnitActs, symRel]

@[simp] lemma filter_symRel_headStream : (headStream Q Γ K).filter symRel = [] := by
  have hround : ∀ R : ℕ, (roundStream R fun u => headUnitActs Q Γ (headMarkStd K u)).filter
      (symRel (Q := Q) (Γ := Γ)) = [] := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
        rw [roundStream_succ, List.filter_append, ih, filter_symRel_headUnitActs]
        rfl
  simp [headStream, hround]

/-! ### The counter that is due in a cell -/

/-- The delays of the `K + 1` cell counters are a permutation of `0, …, K`, so for every cell
there is a counter whose delay is the residue of the cell. -/
lemma exists_due (D : SolutionPlanData N w K) (n : ℕ) :
    ∃ j, j < K + 1 ∧ D.d j = n % (K + 1) := by
  have hinj : Function.Injective (fun j : Fin (K + 1) => (⟨D.d j, by
      have := D.dle j j.2; omega⟩ : Fin (K + 1))) := by
    intro j₁ j₂ h
    exact Fin.ext (D.dinj j₁ j₁.2 j₂ j₂.2 (by simpa using congrArg Fin.val h))
  obtain ⟨j, hj⟩ := Finite.injective_iff_surjective.1 hinj ⟨n % (K + 1), Nat.mod_lt _ (by omega)⟩
  exact ⟨j, j.2, by simpa using congrArg Fin.val hj⟩

/-- **The cell counter that takes a decision in the cell `n`**: the one whose leading delay is
`n mod (K + 1)`. -/
noncomputable def due (D : SolutionPlanData N w K) (n : ℕ) : ℕ :=
  Classical.choose (exists_due D n)

lemma due_lt (D : SolutionPlanData N w K) (n : ℕ) : due D n < K + 1 :=
  (Classical.choose_spec (exists_due D n)).1

lemma d_due (D : SolutionPlanData N w K) (n : ℕ) : D.d (due D n) = n % (K + 1) :=
  (Classical.choose_spec (exists_due D n)).2

/-- Every counter that is not due in the cell `n` merely waits. -/
lemma counterCell_of_ne_due (D : SolutionPlanData N w K) {n j : ℕ} (hj : j < K + 1)
    (hne : j ≠ due D n) :
    counterCell Q Γ K (D.d j) (D.P j) (D.cc j) n = waitCellActs Q Γ := by
  have hdj : D.d j ≤ K := D.dle j hj
  have hd' : D.d j ≠ n % (K + 1) := by
    intro h
    exact hne (D.dinj j hj (due D n) (due_lt D n) (by rw [h, d_due]))
  by_cases hlt : n < D.d j
  · exact counterCell_of_lt hlt
  · rw [counterCell_of_ge (Nat.not_lt.1 hlt)]
    refine counterSeg_wait fun hmod => hd' ?_
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hcomm : (K + 1) * k = k * (K + 1) := Nat.mul_comm _ _
    have hn : n = D.d j + k * (K + 1) := by omega
    conv_rhs => rw [hn]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-! ### Only the due counter touches `sym` during a cell -/

/-- **The actions of the cell `n` of a solution plan that touch the fact `sym`.**  The plan is
`u₀ ++ assert (sym n) :: (m ++ v)`, and inside `m` — which is everything that happens between
that `assert` and the `assert` of the next cell — the only actions that touch `sym` are those of
the cell `n` of the counter that is due. -/
theorem filter_cellChunk (D : SolutionPlanData N w K) {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    ∃ u₀ m v : List (TMAct Q Γ),
      D.as₁ = u₀ ++ TMAct.assert (D.sym n) :: (m ++ v) ∧
        m.filter symRel =
          (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n).filter symRel := by
  obtain ⟨u₀, m, v, Hm, parts, heq, hpi, hsub, hlen, hcells⟩ := exists_cellCut D hn
  refine ⟨u₀, m, v, heq, ?_⟩
  have hHm : Hm.filter symRel = [] := by
    have hs := hsub.filter symRel
    rw [filter_symRel_headStream] at hs
    exact List.sublist_nil.1 hs
  have hj : due D n < parts.length := by rw [hlen]; exact due_lt D n
  have hothers : ∀ i, ∀ hi : i < parts.length, i ≠ due D n → (parts[i]).filter symRel = [] := by
    intro i hi hne
    rw [hcells i hi, counterCell_of_ne_due D (by omega) hne, filter_symRel_waitCellActs]
  rw [hpi.filter_eq_getElem symRel hHm filter_symRel_cellTail hj hothers, hcells _ hj]

end TMEnc

end HTN
