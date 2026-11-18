import HtnComplexity.TMEnc.TMEncFixStFact
/-!
# What the tests of a plan read: the facts `head` and `noHead`

The two facts that say whether the head of the machine is at the cell the tape is writing are
touched by exactly two actions of the encoding: `assertHead` (which adds `head` and deletes
`noHead`) and `retractHead` (which does the opposite).  Both belong to the units of the *head
counter*, whose stream is fixed by the hierarchy — no cell of the tape and no cell counter
touches them.  Consequently, at every point of an executable plan at most one of the two facts
holds, and which one is determined by the last unit of the head counter that has run:

* `HTN.TMEnc.lastHeadF` — that value (`none` before the first unit);
* `HTN.TMEnc.headF_mem_transitionSeq` — **the invariant**;
* `HTN.TMEnc.lastHeadF_of_check_noHead` — a test `check noHead` of a plan of the repaired problem
  is taken while the head counter reports the head as *absent*;
* `HTN.TMEnc.lastHeadF_of_step` — a transition is taken while it reports the head as *present*.

This is the head analogue of `HtnComplexity/TMEnc/TMEncFixSymFact.lean` and
`HtnComplexity/TMEnc/TMEncFixStFact.lean`; see `NOTES.md` for what the remaining step — the
alignment of the units of the head counter with the cells of the tape — needs.
-/

namespace HTN

namespace TMEnc

open TM ActionModel

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- Whether the head is reported as present after the action `a`, given that it was reported as
`b` before (`none`: no unit of the head counter has run yet). -/
def stepHeadF : Option Bool → TMAct Q Γ → Option Bool
  | _, .assertHead => some true
  | _, .retractHead => some false
  | b, _ => b

/-- Whether the head is reported as present after the sequence `p`. -/
def lastHeadF (b : Option Bool) (p : List (TMAct Q Γ)) : Option Bool :=
  p.foldl stepHeadF b

@[simp] lemma lastHeadF_nil (b : Option Bool) : lastHeadF (Q := Q) (Γ := Γ) b [] = b := rfl

@[simp] lemma lastHeadF_cons (b : Option Bool) (a : TMAct Q Γ) (p : List (TMAct Q Γ)) :
    lastHeadF b (a :: p) = lastHeadF (stepHeadF b a) p := rfl

lemma lastHeadF_append (b : Option Bool) (p p' : List (TMAct Q Γ)) :
    lastHeadF b (p ++ p') = lastHeadF (lastHeadF b p) p' := by
  simp [lastHeadF, List.foldl_append]

/-- **The two head facts of an executable plan are single valued, and their value is the mark of
the last unit of the head counter that has run.** -/
theorem headF_mem_transitionSeq : ∀ (p : List (TMAct Q Γ)) (s : Set (TMFact Q Γ))
    (b₀ : Option Bool), (actionModel (Q := Q) (Γ := Γ)).SeqApplicable p s →
      ((TMFact.head : TMFact Q Γ) ∈ s ↔ b₀ = some true) →
      ((TMFact.noHead : TMFact Q Γ) ∈ s ↔ b₀ = some false) →
      (((TMFact.head : TMFact Q Γ) ∈ (actionModel (Q := Q) (Γ := Γ)).transitionSeq p s ↔
          lastHeadF b₀ p = some true) ∧
        ((TMFact.noHead : TMFact Q Γ) ∈ (actionModel (Q := Q) (Γ := Γ)).transitionSeq p s ↔
          lastHeadF b₀ p = some false)) := by
  intro p
  induction p with
  | nil => intro s b₀ _ h₁ h₂; exact ⟨by simpa using h₁, by simpa using h₂⟩
  | cons a p ih =>
      intro s b₀ happ h₁ h₂
      refine ih _ (stepHeadF b₀ a) happ.2 ?_ ?_
      · have hmem : (TMFact.head : TMFact Q Γ) ∈
            (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
              ((TMFact.head : TMFact Q Γ) ∈ s ∧ (TMFact.head : TMFact Q Γ) ∉ TMEnc.del a) ∨
                (TMFact.head : TMFact Q Γ) ∈ TMEnc.add a := by
          simp [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff]
        cases a with
        | assertHead => simp [hmem, TMEnc.add, TMEnc.del, stepHeadF]
        | retractHead => simp [hmem, TMEnc.add, TMEnc.del, stepHeadF]
        | _ => rw [hmem, h₁]; simp_all [stepHeadF, TMEnc.add, TMEnc.del]
      · have hmem : (TMFact.noHead : TMFact Q Γ) ∈
            (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
              ((TMFact.noHead : TMFact Q Γ) ∈ s ∧ (TMFact.noHead : TMFact Q Γ) ∉ TMEnc.del a) ∨
                (TMFact.noHead : TMFact Q Γ) ∈ TMEnc.add a := by
          simp [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff]
        cases a with
        | assertHead => simp [hmem, TMEnc.add, TMEnc.del, stepHeadF]
        | retractHead => simp [hmem, TMEnc.add, TMEnc.del, stepHeadF]
        | _ => rw [hmem, h₂]; simp_all [stepHeadF, TMEnc.add, TMEnc.del]

/-- Neither head fact holds in the initial state of the repaired problem. -/
lemma head_not_mem_initFix :
    (TMFact.head : TMFact Q Γ) ∉ (problemFix N w K).init := by
  show (TMFact.head : TMFact Q Γ) ∉ ({TMFact.st N.init} : Set (TMFact Q Γ))
  simp

lemma noHead_not_mem_initFix :
    (TMFact.noHead : TMFact Q Γ) ∉ (problemFix N w K).init := by
  show (TMFact.noHead : TMFact Q Γ) ∉ ({TMFact.st N.init} : Set (TMFact Q Γ))
  simp

private lemma headF_init_iff :
    (((TMFact.head : TMFact Q Γ) ∈ (problemFix N w K).init ↔
        (none : Option Bool) = some true) ∧
      ((TMFact.noHead : TMFact Q Γ) ∈ (problemFix N w K).init ↔
        (none : Option Bool) = some false)) :=
  ⟨⟨fun h => absurd h head_not_mem_initFix, fun h => absurd h (by simp)⟩,
    ⟨fun h => absurd h noHead_not_mem_initFix, fun h => absurd h (by simp)⟩⟩

/-- **A test `check noHead` of an executable plan is taken while the head counter reports the
head as absent.** -/
theorem lastHeadF_of_check_noHead {p rest : List (TMAct Q Γ)}
    (happ : (problemFix N w K).SeqApplicable (p ++ (TMAct.check TMFact.noHead :: rest))
      (problemFix N w K).init) :
    lastHeadF none p = some false := by
  rw [ActionModel.seqApplicable_append] at happ
  have hinv := headF_mem_transitionSeq p ((problemFix N w K).init) none happ.1
    (headF_init_iff (N := N) (w := w) (K := K)).1 (headF_init_iff (N := N) (w := w) (K := K)).2
  exact hinv.2.1 (happ.2.1 rfl)

/-- **A transition of an executable plan is taken while the head counter reports the head as
present.** -/
theorem lastHeadF_of_step {p rest : List (TMAct Q Γ)} {q q' : Q} {c c' : Option Γ}
    (happ : (problemFix N w K).SeqApplicable (p ++ (TMAct.step q c q' c' :: rest))
      (problemFix N w K).init) :
    lastHeadF none p = some true := by
  rw [ActionModel.seqApplicable_append] at happ
  have hinv := headF_mem_transitionSeq p ((problemFix N w K).init) none happ.1
    (headF_init_iff (N := N) (w := w) (K := K)).1 (headF_init_iff (N := N) (w := w) (K := K)).2
  exact hinv.1.1 (happ.2.1 (Set.mem_insert _ _))

end TMEnc

end HTN
