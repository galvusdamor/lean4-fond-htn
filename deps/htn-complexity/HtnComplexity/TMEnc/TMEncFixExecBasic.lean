import HtnComplexity.TMEnc.TMEncFixMark
import HtnComplexity.Interleave.RunsCalculus
/-!
# The action model of the encoding, step by step

This file collects the elementary steps of the executability proof of the plan of a witness: for
each action, respectively for each small group of actions that always occur together, a lemma of
the calculus of `HtnComplexity/Interleave/RunsCalculus.lean` that says which facts have to hold before
it and which facts hold after it.

The tracked sets are always *lower bounds* on the state, which is all that is needed because all
preconditions of the action model of the encoding are positive.
-/

namespace HTN

namespace TMEnc

open TM ActionModel

variable {Q Γ : Type}

/-- The action model of the encoding, with its type arguments made explicit. -/
abbrev am (Q Γ : Type) : ActionModel (TMFact Q Γ) (TMAct Q Γ) := actionModel

/-- The fact that reports the presence of the head. -/
def headF (Q Γ : Type) : Bool → TMFact Q Γ
  | true => TMFact.head
  | false => TMFact.noHead

@[simp] lemma headF_true : headF Q Γ true = TMFact.head := rfl

@[simp] lemma headF_false : headF Q Γ false = TMFact.noHead := rfl

/-- One step of a run: the precondition of the action has to be guaranteed, the new invariant
has to be covered by what survives the action and what it adds. -/
lemma runs_step_of {T T' U : Set (TMFact Q Γ)} {a : TMAct Q Γ} {as : List (TMAct Q Γ)}
    (hp : prec a ⊆ T) (hT' : T' ⊆ (T \ del a) ∪ add a) (h : (am Q Γ).Runs T' as U) :
    (am Q Γ).Runs T (a :: as) U := by
  have h₁ : (am Q Γ).Runs T [a] T' := ActionModel.runs_single hp hT'
  simpa using h₁.trans h

lemma runs_last {T U : Set (TMFact Q Γ)} {a : TMAct Q Γ}
    (hp : prec a ⊆ T) (hU : U ⊆ (T \ del a) ∪ add a) : (am Q Γ).Runs T [a] U :=
  ActionModel.runs_single hp hU

/-! ### The single actions -/

lemma runs_assert {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {c : Option Γ}
    (hU : U ⊆ insert (TMFact.sym c) {f ∈ T | ∀ d, f ≠ TMFact.sym d})
    (h : (am Q Γ).Runs U as V) : (am Q Γ).Runs T (TMAct.assert c :: as) V := by
  refine runs_step_of (a := TMAct.assert c) (by simp [prec]) ?_ h
  intro f hf
  rcases hU hf with hf' | hf'
  · exact Or.inr (by simp [add, hf'])
  · refine Or.inl ⟨hf'.1, ?_⟩
    rintro ⟨d, rfl, -⟩
    exact hf'.2 d rfl

lemma runs_check {T : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {f : TMFact Q Γ}
    (hf : f ∈ T) (h : (am Q Γ).Runs T as V) : (am Q Γ).Runs T (TMAct.check f :: as) V := by
  refine runs_step_of (a := TMAct.check f) (by simpa [prec] using hf) ?_ h
  intro g hg
  exact Or.inl ⟨hg, by simp [del]⟩

lemma runs_call {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {x : SyncKind}
    (hU : U ⊆ insert (TMFact.stepF x) T) (h : (am Q Γ).Runs U as V) :
    (am Q Γ).Runs T (TMAct.call x :: as) V := by
  refine runs_step_of (a := TMAct.call x) (by simp [prec]) ?_ h
  intro f hf
  rcases hU hf with hf' | hf'
  · exact Or.inr (by simp [add, hf'])
  · exact Or.inl ⟨hf', by simp [del]⟩

lemma runs_start {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {x : SyncKind}
    (hp : TMFact.stepF x ∈ T) (hU : U ⊆ T \ {TMFact.stepF x})
    (h : (am Q Γ).Runs U as V) : (am Q Γ).Runs T (TMAct.start x :: as) V := by
  refine runs_step_of (a := TMAct.start x) (by simpa [prec] using hp) ?_ h
  intro f hf
  exact Or.inl ⟨(hU hf).1, by simpa [del] using (hU hf).2⟩

lemma runs_respond {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {x : SyncKind}
    (hU : U ⊆ insert (TMFact.steppedF x) T) (h : (am Q Γ).Runs U as V) :
    (am Q Γ).Runs T (TMAct.respond x :: as) V := by
  refine runs_step_of (a := TMAct.respond x) (by simp [prec]) ?_ h
  intro f hf
  rcases hU hf with hf' | hf'
  · exact Or.inr (by simp [add, hf'])
  · exact Or.inl ⟨hf', by simp [del]⟩

lemma runs_wait {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {x : SyncKind}
    (hp : TMFact.steppedF x ∈ T) (hU : U ⊆ T \ {TMFact.steppedF x})
    (h : (am Q Γ).Runs U as V) : (am Q Γ).Runs T (TMAct.wait x :: as) V := by
  refine runs_step_of (a := TMAct.wait x) (by simpa [prec] using hp) ?_ h
  intro f hf
  exact Or.inl ⟨(hU hf).1, by simpa [del] using (hU hf).2⟩

lemma runs_headMark {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {b : Bool}
    (hU : U ⊆ insert (headF Q Γ b) (T \ {TMFact.head, TMFact.noHead}))
    (h : (am Q Γ).Runs U as V) :
    (am Q Γ).Runs T ((if b then TMAct.assertHead else TMAct.retractHead) :: as) V := by
  cases b with
  | true =>
      refine runs_step_of (a := TMAct.assertHead) (by simp [prec]) ?_ (by simpa using h)
      intro f hf
      rcases hU hf with hf' | hf'
      · exact Or.inr (by simp [add, hf'])
      · refine Or.inl ⟨hf'.1, ?_⟩
        simp only [del, Set.mem_singleton_iff]
        rintro rfl
        exact hf'.2 (by simp)
  | false =>
      refine runs_step_of (a := TMAct.retractHead) (by simp [prec]) ?_ (by simpa using h)
      intro f hf
      rcases hU hf with hf' | hf'
      · exact Or.inr (by simp [add, hf'])
      · refine Or.inl ⟨hf'.1, ?_⟩
        simp only [del, Set.mem_singleton_iff]
        rintro rfl
        exact hf'.2 (by simp)

lemma runs_machineStep {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {q q' : Q}
    {c c' : Option Γ} (hh : TMFact.head ∈ T) (hs : TMFact.sym c ∈ T) (hq : TMFact.st q ∈ T)
    (hU : U ⊆ insert (TMFact.sym c') (insert (TMFact.st q')
      {f ∈ T | f ≠ TMFact.sym c ∧ f ≠ TMFact.st q}))
    (h : (am Q Γ).Runs U as V) : (am Q Γ).Runs T (TMAct.step q c q' c' :: as) V := by
  refine runs_step_of (a := TMAct.step q c q' c') ?_ ?_ h
  · intro f hf
    rcases hf with rfl | rfl | rfl
    · exact hh
    · exact hs
    · exact hq
  · intro f hf
    rcases hU hf with rfl | hf' | hf'
    · exact Or.inr (by simp [add])
    · exact Or.inr (by simp [add, hf'])
    · exact Or.inl ⟨hf'.1, by
        simp only [del, Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (rfl | rfl)
        · exact hf'.2.1 rfl
        · exact hf'.2.2 rfl⟩

/-! ### The groups of actions that always occur together -/

/-- **Answering a request on the channel `x`.** -/
lemma runs_release {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {x : SyncKind}
    (hp : TMFact.stepF x ∈ T)
    (hU : U ⊆ insert (TMFact.steppedF x) (T \ {TMFact.stepF x}))
    (h : (am Q Γ).Runs U as V) :
    (am Q Γ).Runs T (TMAct.start x :: TMAct.respond x :: as) V :=
  runs_start hp le_rfl (runs_respond hU h)

/-- **One unit of the head counter**: it answers one request on the `head` channel and reports
whether the head is at the cell that issued it. -/
lemma runs_headUnit {T U : Set (TMFact Q Γ)} {as : List (TMAct Q Γ)} {b : Bool}
    (hp : TMFact.stepF SyncKind.head ∈ T)
    (hU : U ⊆ insert (headF Q Γ b) (insert (TMFact.steppedF SyncKind.head)
      ((T \ {TMFact.stepF SyncKind.head}) \ {TMFact.head, TMFact.noHead})))
    (h : (am Q Γ).Runs U as V) :
    (am Q Γ).Runs T (headUnitActs Q Γ b ++ as) V := by
  refine runs_start (x := SyncKind.head) hp le_rfl (runs_headMark (b := b) le_rfl
    (runs_respond ?_ h))
  refine hU.trans ?_
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff] at hf ⊢
  tauto

end TMEnc

end HTN
