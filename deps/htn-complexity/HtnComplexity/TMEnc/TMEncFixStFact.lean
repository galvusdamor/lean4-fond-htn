import HtnComplexity.TMEnc.TMEncFixSymFact
/-!
# What the tests of a plan read: the fact `st`

The state of the machine is carried by the fact `st q`.  Only a transition
`step q c q' c'` touches it — it requires `st q`, deletes it and adds `st q'` — so, the initial
state of the encoded problem being `{st N.init}`, at every point of an executable plan **exactly
one** state fact holds, namely the target state of the last transition executed so far.

* `HTN.TMEnc.lastStQ` — that state;
* `HTN.TMEnc.st_mem_transitionSeq` — **the invariant**;
* `HTN.TMEnc.lastStQ_of_check`, `HTN.TMEnc.lastStQ_of_step` — what a test `check (st q)`,
  respectively a transition, of a plan of the repaired problem therefore reads.

This is the state analogue of `HtnComplexity/TMEnc/TMEncFixSymFact.lean`.
-/

namespace HTN

namespace TMEnc

open TM ActionModel

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- The state after the action `a`, given that the machine was in the state `q` before. -/
def stepStQ : Q → TMAct Q Γ → Q
  | _, .step _ _ q' _ => q'
  | q, _ => q

/-- The state after the sequence `p`, given that the machine was in the state `q` before. -/
def lastStQ (q : Q) (p : List (TMAct Q Γ)) : Q :=
  p.foldl stepStQ q

@[simp] lemma lastStQ_nil (q : Q) : lastStQ (Γ := Γ) q [] = q := rfl

@[simp] lemma lastStQ_cons (q : Q) (a : TMAct Q Γ) (p : List (TMAct Q Γ)) :
    lastStQ q (a :: p) = lastStQ (stepStQ q a) p := rfl

lemma lastStQ_append (q : Q) (p p' : List (TMAct Q Γ)) :
    lastStQ q (p ++ p') = lastStQ (lastStQ q p) p' := by
  simp [lastStQ, List.foldl_append]

/-- **The fact `st` of an executable plan is single valued, and its value is the target state of
the last transition.** -/
theorem st_mem_transitionSeq : ∀ (p : List (TMAct Q Γ)) (s : Set (TMFact Q Γ)) (q₀ : Q),
    (actionModel (Q := Q) (Γ := Γ)).SeqApplicable p s →
      (∀ q, (TMFact.st q : TMFact Q Γ) ∈ s ↔ q = q₀) →
      ∀ q, (TMFact.st q : TMFact Q Γ) ∈ (actionModel (Q := Q) (Γ := Γ)).transitionSeq p s ↔
        q = lastStQ q₀ p := by
  intro p
  induction p with
  | nil => intro s q₀ _ hs q; simpa using hs q
  | cons a p ih =>
      intro s q₀ happ hs q
      refine ih _ (stepStQ q₀ a) happ.2 ?_ q
      intro d
      have hmem : ∀ e : Q, (TMFact.st e : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
            ((TMFact.st e : TMFact Q Γ) ∈ s ∧ (TMFact.st e : TMFact Q Γ) ∉ TMEnc.del a) ∨
              (TMFact.st e : TMFact Q Γ) ∈ TMEnc.add a := by
        intro e
        simp [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff]
      cases a with
      | step q₁ x q₁' y =>
          have hprec : (TMFact.st q₁ : TMFact Q Γ) ∈ s :=
            happ.1 (by simp [actionModel, TMEnc.prec])
          have hq₁ : q₁ = q₀ := (hs q₁).1 hprec
          have hdel : (TMFact.st d : TMFact Q Γ) ∈ TMEnc.del (TMAct.step q₁ x q₁' y) ↔ d = q₁ := by
            simp [TMEnc.del]
          have hadd : (TMFact.st d : TMFact Q Γ) ∈ TMEnc.add (TMAct.step q₁ x q₁' y) ↔ d = q₁' := by
            simp [TMEnc.add]
          have hins : (TMFact.st d : TMFact Q Γ) ∈ s ↔ d = q₁ := by
            rw [hs d, hq₁]
          rw [hmem d, hdel, hadd, hins]
          simp only [stepStQ]
          constructor
          · rintro (⟨h1, h2⟩ | rfl)
            · exact absurd h1 h2
            · rfl
          · rintro rfl
            exact Or.inr rfl
      | _ =>
          rw [hmem d, hs d]
          simp_all [stepStQ, TMEnc.add, TMEnc.del]

/-- The initial state of the repaired problem holds exactly the fact `st N.init`. -/
lemma st_mem_initFix (q : Q) :
    (TMFact.st q : TMFact Q Γ) ∈ (problemFix N w K).init ↔ q = N.init := by
  show (TMFact.st q : TMFact Q Γ) ∈ ({TMFact.st N.init} : Set (TMFact Q Γ)) ↔ q = N.init
  simp

/-- **A test `check (st q)` of an executable plan reads the state the plan is in.** -/
theorem lastStQ_of_check {p rest : List (TMAct Q Γ)} {q : Q}
    (happ : (problemFix N w K).SeqApplicable (p ++ (TMAct.check (TMFact.st q) :: rest))
      (problemFix N w K).init) :
    q = lastStQ N.init p := by
  rw [ActionModel.seqApplicable_append] at happ
  have hinv := st_mem_transitionSeq p ((problemFix N w K).init) N.init happ.1
    (fun d => st_mem_initFix (N := N) (w := w) (K := K) d) q
  exact hinv.1 (happ.2.1 rfl)

/-- **A transition `step q c q' c'` of an executable plan is taken in the state the plan is
in.** -/
theorem lastStQ_of_step {p rest : List (TMAct Q Γ)} {q q' : Q} {c c' : Option Γ}
    (happ : (problemFix N w K).SeqApplicable (p ++ (TMAct.step q c q' c' :: rest))
      (problemFix N w K).init) :
    q = lastStQ N.init p := by
  rw [ActionModel.seqApplicable_append] at happ
  have hinv := st_mem_transitionSeq p ((problemFix N w K).init) N.init happ.1
    (fun d => st_mem_initFix (N := N) (w := w) (K := K) d) q
  exact hinv.1 (happ.2.1 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

end TMEnc

end HTN
