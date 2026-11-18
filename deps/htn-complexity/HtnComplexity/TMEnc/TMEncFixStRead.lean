import HtnComplexity.TMEnc.TMEncFixConsistent
import HtnComplexity.TMEnc.TMEncFixStFact
/-!
# What a piece of an executable plan says about the state of the machine

This is the state analogue of `HtnComplexity/TMEnc/TMEncFixSymRead.lean` and
`HtnComplexity/TMEnc/TMEncFixConsistent.lean`.  The fact `st` is single valued
(`HtnComplexity/TMEnc/TMEncFixStFact.lean`); the actions that touch it are the transitions
`step q c q' c'` of the cell counters and the accepting test `check (st f)` at the end of the
plan.  In particular the tape, the head counter and a waiting cell of a counter do not touch it.

* `HTN.TMEnc.stRel` — the actions that read or write the fact `st`;
* `HTN.TMEnc.lastStQ_filter` — the state depends only on those actions;
* `HTN.TMEnc.StConsistent` — reading a piece of a plan from a state `q`, every test and every
  transition of the piece is taken in the state the plan is in;
* `HTN.TMEnc.stConsistent_of_seqApplicable` — **every piece of an executable plan is
  consistent**.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The actions that touch the fact `st` -/

/-- The actions that read or write the fact `st`: the transitions of the cell counters and the
accepting test at the end of a plan. -/
def stRel : TMAct Q Γ → Bool
  | .step _ _ _ _ => true
  | .check (.st _) => true
  | _ => false

/-- An action that does not touch `st` does not change it. -/
lemma stepStQ_of_not_stRel {a : TMAct Q Γ} (ha : stRel a = false) (q : Q) :
    stepStQ q a = q := by
  cases a <;> simp_all [stRel, stepStQ]

/-- **The state depends only on the actions that touch it.** -/
lemma lastStQ_filter (q : Q) : ∀ l : List (TMAct Q Γ),
    lastStQ q (l.filter stRel) = lastStQ q l := by
  intro l
  induction l generalizing q with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : stRel a
      · rw [List.filter_cons_of_pos ha, lastStQ_cons, lastStQ_cons, ih]
      · simp only [Bool.not_eq_true] at ha
        rw [List.filter_cons_of_neg (by simp [ha]), ih, lastStQ_cons, stepStQ_of_not_stRel ha]

/-! ### The streams that do not touch `st` -/

@[simp] lemma filter_stRel_waitCellActs : (waitCellActs Q Γ).filter stRel = [] := by
  simp [waitCellActs, stRel]

@[simp] lemma filter_stRel_relCheckActs : (relCheckActs Q Γ).filter stRel = [] := by
  simp [relCheckActs, stRel]

@[simp] lemma filter_stRel_relSyncActs : (relSyncActs Q Γ).filter stRel = [] := by
  simp [relSyncActs, stRel]

@[simp] lemma stRel_chkAct (c : Option Γ) : stRel (chkAct Q Γ c) = false := rfl

@[simp] lemma filter_stRel_cellTail : (cellTail Q Γ K).filter stRel = [] :=
  cellTail_filter fun _ => ⟨rfl, rfl⟩

@[simp] lemma filter_stRel_headUnitActs (b : Bool) :
    (headUnitActs Q Γ b).filter stRel = [] := by
  cases b <;> simp [headUnitActs, stRel]

@[simp] lemma filter_stRel_headStream : (headStream Q Γ K).filter stRel = [] := by
  have hround : ∀ R : ℕ, (roundStream R fun u => headUnitActs Q Γ (headMarkStd K u)).filter
      (stRel (Q := Q) (Γ := Γ)) = [] := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
        rw [roundStream_succ, List.filter_append, ih, filter_stRel_headUnitActs]
        rfl
  simp [headStream, hround]

@[simp] lemma filter_stRel_cellRun (c : Option Γ) : (cellRun Q Γ K c).filter stRel = [] := by
  rw [cellRun_eq_cons, List.filter_cons_of_neg (by simp [stRel]), filter_stRel_cellTail]

@[simp] lemma filter_stRel_tapePrefix (n : ℕ) (sym : ℕ → Option Γ) :
    (tapePrefix Q Γ K n sym).filter stRel = [] := by
  induction n with
  | zero => simp [tapePrefix]
  | succ n ih =>
      rw [tapePrefix, roundStream_succ, List.filter_append, ← tapePrefix, ih,
        filter_stRel_cellRun]
      rfl

/-! ### Consistency of a piece of a plan with the state -/

/-- **Consistency of a piece of a plan with the state `q`**: every test and every transition of
the piece is taken in the state the machine is in at that moment. -/
def StConsistent : Q → List (TMAct Q Γ) → Prop
  | _, [] => True
  | q, a :: l =>
      (∀ r, a = TMAct.check (TMFact.st r) → r = q) ∧
        (∀ q₁ x q₁' y, a = TMAct.step q₁ x q₁' y → q₁ = q) ∧
          StConsistent (stepStQ q a) l

@[simp] lemma stConsistent_nil (q : Q) : StConsistent (Γ := Γ) q [] := trivial

lemma stConsistent_cons {q : Q} {a : TMAct Q Γ} {l : List (TMAct Q Γ)} :
    StConsistent q (a :: l) ↔
      ((∀ r, a = TMAct.check (TMFact.st r) → r = q) ∧
        (∀ q₁ x q₁' y, a = TMAct.step q₁ x q₁' y → q₁ = q) ∧
          StConsistent (stepStQ q a) l) := Iff.rfl

lemma stConsistent_filter (q : Q) : ∀ l : List (TMAct Q Γ),
    StConsistent q (l.filter stRel) ↔ StConsistent q l := by
  intro l
  induction l generalizing q with
  | nil => simp
  | cons a l ih =>
      by_cases ha : stRel a
      · rw [List.filter_cons_of_pos ha, stConsistent_cons, stConsistent_cons, ih]
      · simp only [Bool.not_eq_true] at ha
        rw [List.filter_cons_of_neg (by simp [ha]), ih, stConsistent_cons,
          stepStQ_of_not_stRel ha]
        constructor
        · intro h
          refine ⟨?_, ?_, h⟩
          · intro r hr; rw [hr] at ha; simp [stRel] at ha
          · intro q₁ x q₁' y hxy; rw [hxy] at ha; simp [stRel] at ha
        · exact fun h => h.2.2

/-- **Every piece of a solution plan of the repaired problem is consistent with the state**: each
of its tests and each of its transitions is taken in the state the plan is in. -/
theorem stConsistent_of_seqApplicable : ∀ (mid p rest : List (TMAct Q Γ)),
    (problemFix N w K).SeqApplicable (p ++ (mid ++ rest)) (problemFix N w K).init →
      StConsistent (lastStQ N.init p) mid := by
  intro mid
  induction mid with
  | nil => intro p rest _; simp
  | cons a mid ih =>
      intro p rest happ
      have hsplit : p ++ ((a :: mid) ++ rest) = (p ++ [a]) ++ (mid ++ rest) := by simp
      have happ' : (problemFix N w K).SeqApplicable ((p ++ [a]) ++ (mid ++ rest))
          (problemFix N w K).init := by rwa [hsplit] at happ
      have hrec := ih (p ++ [a]) rest happ'
      have hlast : lastStQ N.init (p ++ [a]) = stepStQ (lastStQ N.init p) a := by
        rw [lastStQ_append]; rfl
      rw [hlast] at hrec
      refine ⟨?_, ?_, hrec⟩
      · rintro r rfl
        exact lastStQ_of_check (N := N) (w := w) (K := K) (p := p) (rest := mid ++ rest)
          (by simpa using happ)
      · rintro q₁ x q₁' y rfl
        exact lastStQ_of_step (N := N) (w := w) (K := K) (p := p) (rest := mid ++ rest)
          (by simpa using happ)

end TMEnc

end HTN
