import HtnComplexity.TMEnc.TMEncFixCounterCells
/-!
# What the tests of a plan read: the fact `sym`

Every test `check (sym c)` of a plan of the repaired encoding — the two tests of a `chk` gadget
of a cell counter — and every transition `step q c q' c'` require the fact `sym c` to hold.  The
fact `sym` is *single valued*: the actions that touch it are `assert d` (which writes `d` and
deletes every other symbol) and `step _ _ _ d` (which writes `d` and deletes the symbol it read),
so at every point of an executable plan the fact that holds is the argument of the last such
action.

* `HTN.TMEnc.lastSym` — that argument;
* `HTN.TMEnc.sym_mem_transitionSeq` — **the invariant**;
* `HTN.TMEnc.lastSym_of_check`, `HTN.TMEnc.lastSym_of_step` — what a test, respectively a
  transition, of a plan of the repaired problem therefore reads.

This is the semantic half of the second step of the soundness argument: together with the
alignment (`HTN.TMEnc.lockstep`) it identifies the tape cell whose symbol a `chk` gadget
compares.  See `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM ActionModel

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- The symbol the tape holds after the action `a`, given that it held `c` before (`none`: no
symbol has been written yet). -/
def stepSym (c : Option (Option Γ)) : TMAct Q Γ → Option (Option Γ)
  | .assert d => some d
  | .step _ _ _ d => some d
  | _ => c

/-- The symbol the tape holds after the sequence `p`, given that it held `c` before. -/
def lastSym (c : Option (Option Γ)) (p : List (TMAct Q Γ)) : Option (Option Γ) :=
  p.foldl stepSym c

@[simp] lemma lastSym_nil (c : Option (Option Γ)) : lastSym (Q := Q) c [] = c := rfl

@[simp] lemma lastSym_cons (c : Option (Option Γ)) (a : TMAct Q Γ) (p : List (TMAct Q Γ)) :
    lastSym c (a :: p) = lastSym (stepSym c a) p := rfl

lemma lastSym_append (c : Option (Option Γ)) (p q : List (TMAct Q Γ)) :
    lastSym c (p ++ q) = lastSym (lastSym c p) q := by
  simp [lastSym, List.foldl_append]

/-- **The fact `sym` of an executable plan is single valued, and its value is the argument of the
last `assert` or `step`.** -/
theorem sym_mem_transitionSeq : ∀ (p : List (TMAct Q Γ)) (s : Set (TMFact Q Γ))
    (c₀ : Option (Option Γ)), (actionModel (Q := Q) (Γ := Γ)).SeqApplicable p s →
      (∀ c, (TMFact.sym c : TMFact Q Γ) ∈ s ↔ c₀ = some c) →
      ∀ c, (TMFact.sym c : TMFact Q Γ) ∈ (actionModel (Q := Q) (Γ := Γ)).transitionSeq p s ↔
        lastSym c₀ p = some c := by
  intro p
  induction p with
  | nil => intro s c₀ _ hs c; simpa using hs c
  | cons a p ih =>
      intro s c₀ happ hs c
      refine ih _ (stepSym c₀ a) happ.2 ?_ c
      intro d
      have hmem : ∀ e : Option Γ, (TMFact.sym e : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
            ((TMFact.sym e : TMFact Q Γ) ∈ s ∧ (TMFact.sym e : TMFact Q Γ) ∉ TMEnc.del a) ∨
              (TMFact.sym e : TMFact Q Γ) ∈ TMEnc.add a := by
        intro e
        simp [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff]
      cases a with
      | assert b =>
          have hdel : (TMFact.sym d : TMFact Q Γ) ∈ TMEnc.del (TMAct.assert b) ↔ d ≠ b := by
            simp [TMEnc.del]
          have hadd : (TMFact.sym d : TMFact Q Γ) ∈ TMEnc.add (TMAct.assert b) ↔ d = b := by
            simp [TMEnc.add]
          rw [hmem d, hdel, hadd]
          simp only [stepSym, ne_eq, not_not, Option.some.injEq]
          constructor
          · rintro (⟨-, rfl⟩ | rfl) <;> rfl
          · rintro rfl
            exact Or.inr rfl
      | step q x q' y =>
          have hprec : (TMFact.sym x : TMFact Q Γ) ∈ s := happ.1 (by simp [actionModel, TMEnc.prec])
          have hx : c₀ = some x := (hs x).1 hprec
          have hdel : (TMFact.sym d : TMFact Q Γ) ∈ TMEnc.del (TMAct.step q x q' y) ↔ d = x := by
            simp [TMEnc.del]
          have hadd : (TMFact.sym d : TMFact Q Γ) ∈ TMEnc.add (TMAct.step q x q' y) ↔ d = y := by
            simp [TMEnc.add]
          have hins : (TMFact.sym d : TMFact Q Γ) ∈ s ↔ d = x := by
            rw [hs d, hx]
            simp [eq_comm]
          rw [hmem d, hdel, hadd, hins]
          simp only [stepSym, Option.some.injEq]
          constructor
          · rintro (⟨h1, h2⟩ | rfl)
            · exact absurd h1 h2
            · rfl
          · rintro rfl
            exact Or.inr rfl
      | _ =>
          rw [hmem d, hs d]
          simp_all [stepSym, TMEnc.add, TMEnc.del]

/-- No symbol has been written in the initial state of the repaired problem. -/
lemma sym_not_mem_initFix (c : Option Γ) :
    (TMFact.sym c : TMFact Q Γ) ∉ (problemFix N w K).init := by
  show (TMFact.sym c : TMFact Q Γ) ∉ ({TMFact.st N.init} : Set (TMFact Q Γ))
  simp

/-- **A test `check (sym c)` of an executable plan reads the last symbol written before it.** -/
theorem lastSym_of_check {p rest : List (TMAct Q Γ)} {c : Option Γ}
    (happ : (problemFix N w K).SeqApplicable (p ++ (TMAct.check (TMFact.sym c) :: rest))
      (problemFix N w K).init) :
    lastSym none p = some c := by
  have hinit : ∀ d : Option Γ, (TMFact.sym d : TMFact Q Γ) ∈ (problemFix N w K).init ↔
      (none : Option (Option Γ)) = some d := by
    intro d
    exact ⟨fun hd => absurd hd (sym_not_mem_initFix d), fun hd => absurd hd (by simp)⟩
  rw [ActionModel.seqApplicable_append] at happ
  have hinv := sym_mem_transitionSeq p ((problemFix N w K).init) none happ.1 hinit c
  exact hinv.1 (happ.2.1 rfl)

/-- **A transition `step q c q' c'` of an executable plan reads the last symbol written before
it**, and the state it requires is the one the plan is in. -/
theorem lastSym_of_step {p rest : List (TMAct Q Γ)} {q q' : Q} {c c' : Option Γ}
    (happ : (problemFix N w K).SeqApplicable (p ++ (TMAct.step q c q' c' :: rest))
      (problemFix N w K).init) :
    lastSym none p = some c := by
  have hinit : ∀ d : Option Γ, (TMFact.sym d : TMFact Q Γ) ∈ (problemFix N w K).init ↔
      (none : Option (Option Γ)) = some d := by
    intro d
    exact ⟨fun hd => absurd hd (sym_not_mem_initFix d), fun hd => absurd hd (by simp)⟩
  rw [ActionModel.seqApplicable_append] at happ
  have hinv := sym_mem_transitionSeq p ((problemFix N w K).init) none happ.1 hinit c
  exact hinv.1 (happ.2.1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

end TMEnc

end HTN
