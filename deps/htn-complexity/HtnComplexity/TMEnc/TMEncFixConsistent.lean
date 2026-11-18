import HtnComplexity.TMEnc.TMEncFixSymRead
/-!
# What a piece of an executable plan says about the symbol on the tape

The fact `sym` of the encoding is single valued: it is written by the `assert`s of the tape and
by the `step`s of the counters, and it is read by the tests of the `chk` gadgets and by the
`step`s (`HtnComplexity/TMEnc/TMEncFixSymFact.lean`).  A piece of an executable plan is therefore
*consistent*, in the following sense.

* `HTN.TMEnc.SymConsistent s p` — reading `p` from a state in which the symbol is `s`, every test
  and every transition reads the symbol that the last `assert` or `step` before it has written;
* `HTN.TMEnc.symConsistent_of_seqApplicable` — **every piece of an executable plan is
  consistent**;
* `HTN.TMEnc.symConsistent_filter` — consistency depends only on the actions that touch `sym`;
* `HTN.TMEnc.symConsistent_cellChunk` — **the actions of the due counter during the cell `n` of a
  solution plan are consistent with the symbol `sym n` that the tape has just written**.

The last statement is the one the soundness argument uses: unfolding it for the (explicit) cell
of a counter says exactly which symbols the counter compares.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **Consistency of a piece of a plan with the symbol `s` on the tape**: every test and every
transition of the piece reads the symbol that is on the tape at that moment. -/
def SymConsistent : Option (Option Γ) → List (TMAct Q Γ) → Prop
  | _, [] => True
  | s, a :: l =>
      (∀ c, a = TMAct.check (TMFact.sym c) → s = some c) ∧
        (∀ q x q' y, a = TMAct.step q x q' y → s = some x) ∧
          SymConsistent (stepSym s a) l

@[simp] lemma symConsistent_nil (s : Option (Option Γ)) :
    SymConsistent (Q := Q) s [] := trivial

lemma symConsistent_cons {s : Option (Option Γ)} {a : TMAct Q Γ} {l : List (TMAct Q Γ)} :
    SymConsistent s (a :: l) ↔
      ((∀ c, a = TMAct.check (TMFact.sym c) → s = some c) ∧
        (∀ q x q' y, a = TMAct.step q x q' y → s = some x) ∧
          SymConsistent (stepSym s a) l) := Iff.rfl

/-! ### Consistency depends only on the actions that touch `sym` -/

lemma symConsistent_filter (s : Option (Option Γ)) : ∀ l : List (TMAct Q Γ),
    SymConsistent s (l.filter symRel) ↔ SymConsistent s l := by
  intro l
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
      by_cases ha : symRel a
      · rw [List.filter_cons_of_pos ha, symConsistent_cons, symConsistent_cons, ih]
      · simp only [Bool.not_eq_true] at ha
        rw [List.filter_cons_of_neg (by simp [ha]), ih, symConsistent_cons,
          stepSym_of_not_symRel ha]
        constructor
        · intro h
          refine ⟨?_, ?_, h⟩
          · intro c hc; rw [hc] at ha; simp [symRel] at ha
          · intro q x q' y hxy; rw [hxy] at ha; simp [symRel] at ha
        · exact fun h => h.2.2

/-! ### Every piece of an executable plan is consistent -/

/-- **Every piece of a solution plan of the repaired problem is consistent**: each of its tests
and each of its transitions reads the symbol written by the last `assert` or `step` before it. -/
theorem symConsistent_of_seqApplicable : ∀ (mid p rest : List (TMAct Q Γ)),
    (problemFix N w K).SeqApplicable (p ++ (mid ++ rest)) (problemFix N w K).init →
      SymConsistent (lastSym none p) mid := by
  intro mid
  induction mid with
  | nil => intro p rest _; simp
  | cons a mid ih =>
      intro p rest happ
      have hsplit : p ++ ((a :: mid) ++ rest) = (p ++ [a]) ++ (mid ++ rest) := by simp
      have happ' : (problemFix N w K).SeqApplicable ((p ++ [a]) ++ (mid ++ rest))
          (problemFix N w K).init := by rwa [hsplit] at happ
      have hrec := ih (p ++ [a]) rest happ'
      have hlast : lastSym none (p ++ [a]) = stepSym (lastSym none p) a := by
        rw [lastSym_append]; rfl
      rw [hlast] at hrec
      refine ⟨?_, ?_, hrec⟩
      · rintro c rfl
        exact lastSym_of_check (N := N) (w := w) (K := K) (p := p) (rest := mid ++ rest)
          (by simpa using happ)
      · rintro q x q' y rfl
        exact lastSym_of_step (N := N) (w := w) (K := K) (p := p) (rest := mid ++ rest)
          (by simpa using happ)

/-! ### The cell of the due counter -/

/-- **The actions of the counter that is due in the cell `n` of a solution plan are consistent
with the symbol `sym n` the tape has just written.** -/
theorem symConsistent_cellChunk (D : SolutionPlanData N w K) {n : ℕ}
    (hn : n < (K + 1) * (K + 1)) :
    SymConsistent (some (D.sym n))
      (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n) := by
  obtain ⟨u₀, m, v, heq, hfilter⟩ := filter_cellChunk D hn
  have happ : (problemFix N w K).SeqApplicable (D.as₁ ++ [TMAct.check (TMFact.st D.f)])
      (problemFix N w K).init := (Problem.isSolutionPlan_iff.1 D.isPlan).2.1
  have hsplit : D.as₁ ++ [TMAct.check (TMFact.st D.f)] =
      (u₀ ++ [TMAct.assert (D.sym n)]) ++ (m ++ (v ++ [TMAct.check (TMFact.st D.f)])) := by
    rw [heq]; simp
  rw [hsplit] at happ
  have hcons := symConsistent_of_seqApplicable m (u₀ ++ [TMAct.assert (D.sym n)])
    (v ++ [TMAct.check (TMFact.st D.f)]) happ
  have hlast : lastSym none (u₀ ++ [TMAct.assert (D.sym n)]) = some (D.sym n) := by
    rw [lastSym_append]; rfl
  rw [hlast] at hcons
  rw [← symConsistent_filter, hfilter, symConsistent_filter] at hcons
  exact hcons

end TMEnc

end HTN
