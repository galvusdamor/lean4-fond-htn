import HtnPlanning.Core.Classical
import HtnComplexity.TMEnc.TMEncFixSchedule
/-!
# A Hoare-style calculus for the executability of a plan

Proving that a long, explicitly constructed action sequence is executable means checking a
precondition after every single action.  This file provides the bookkeeping for that: the
relation

`δ.Runs T as U` — *from every state that contains `T`, the sequence `as` is applicable and
leads to a state that contains `U`*

together with its calculus (`HTN.ActionModel.Runs.trans`, `HTN.ActionModel.runs_single`,
`HTN.ActionModel.Runs.mono`, …).  Only *lower bounds* on the states are tracked, which is all
that is needed because preconditions are positive; the price is that a fact that an action
deletes has to be dropped from the invariant, which the side condition
`U ⊆ (T \ del a) ∪ add a` of `HTN.ActionModel.runs_single` takes care of.

`HTN.ActionModel.runs_roundStream` is the induction principle for a plan that is given as a
stream of segments — the shape in which the plans of the encodings of this development are
built.
-/

namespace HTN

namespace ActionModel

variable {F A : Type} {δ : ActionModel F A}

lemma transition_mono (a : A) {s s' : Set F} (h : s ⊆ s') :
    δ.transition a s ⊆ δ.transition a s' := by
  intro f hf
  rcases hf with hf | hf
  · exact Or.inl ⟨h hf.1, hf.2⟩
  · exact Or.inr hf

lemma transitionSeq_mono : ∀ (as : List A) {s s' : Set F}, s ⊆ s' →
    δ.transitionSeq as s ⊆ δ.transitionSeq as s' := by
  intro as
  induction as with
  | nil => intro s s' h; exact h
  | cons a as ih => intro s s' h; exact ih (transition_mono a h)

lemma seqApplicable_mono : ∀ (as : List A) {s s' : Set F}, s ⊆ s' →
    δ.SeqApplicable as s → δ.SeqApplicable as s' := by
  intro as
  induction as with
  | nil => intro s s' _ _; trivial
  | cons a as ih =>
      intro s s' h happ
      exact ⟨fun f hf => h (happ.1 hf), ih (transition_mono a h) happ.2⟩

/-- **`δ.Runs T as U`**: from every state containing `T`, the action sequence `as` is applicable
and leads to a state containing `U`. -/
def Runs (δ : ActionModel F A) (T : Set F) (as : List A) (U : Set F) : Prop :=
  ∀ s, T ⊆ s → δ.SeqApplicable as s ∧ U ⊆ δ.transitionSeq as s

lemma runs_nil (T : Set F) : δ.Runs T [] T := fun _ hs => ⟨trivial, hs⟩

/-- A run of a single action: its precondition must be guaranteed, and the postcondition must be
covered by what survives the action and what it adds. -/
lemma runs_single {T U : Set F} {a : A} (hp : δ.prec a ⊆ T)
    (hu : U ⊆ (T \ δ.del a) ∪ δ.add a) : δ.Runs T [a] U := by
  intro s hs
  refine ⟨⟨fun f hf => hs (hp hf), trivial⟩, ?_⟩
  intro f hf
  rcases hu hf with hf' | hf'
  · exact Or.inl ⟨hs hf'.1, hf'.2⟩
  · exact Or.inr hf'

lemma Runs.trans {T U V : Set F} {as bs : List A} (h₁ : δ.Runs T as U) (h₂ : δ.Runs U bs V) :
    δ.Runs T (as ++ bs) V := by
  intro s hs
  obtain ⟨happ₁, hsub₁⟩ := h₁ s hs
  obtain ⟨happ₂, hsub₂⟩ := h₂ _ hsub₁
  refine ⟨(δ.seqApplicable_append as bs s).2 ⟨happ₁, happ₂⟩, ?_⟩
  rw [δ.transitionSeq_append]
  exact hsub₂

lemma Runs.mono {T T' U U' : Set F} {as : List A} (h : δ.Runs T as U) (hT : T ⊆ T')
    (hU : U' ⊆ U) : δ.Runs T' as U' := by
  intro s hs
  obtain ⟨happ, hsub⟩ := h s (hT.trans hs)
  exact ⟨happ, hU.trans hsub⟩

lemma Runs.weaken_pre {T T' U : Set F} {as : List A} (h : δ.Runs T as U) (hT : T ⊆ T') :
    δ.Runs T' as U := h.mono hT le_rfl

lemma Runs.weaken_post {T U U' : Set F} {as : List A} (h : δ.Runs T as U) (hU : U' ⊆ U) :
    δ.Runs T as U' := h.mono le_rfl hU

/-- A run of a sequence, one action at a time. -/
lemma Runs.cons {T U : Set F} {a : A} {as : List A} (hp : δ.prec a ⊆ T)
    (h : δ.Runs ((T \ δ.del a) ∪ δ.add a) as U) : δ.Runs T (a :: as) U := by
  have h₁ : δ.Runs T [a] ((T \ δ.del a) ∪ δ.add a) := runs_single hp le_rfl
  simpa using h₁.trans h

/-- **The induction principle for a plan given as a stream of segments.** -/
lemma runs_roundStream (S : ℕ → Set F) (seg : ℕ → List A) :
    ∀ R : ℕ, (∀ r < R, δ.Runs (S r) (seg r) (S (r + 1))) →
      δ.Runs (S 0) (roundStream R seg) (S R) := by
  intro R
  induction R with
  | zero => intro _; exact runs_nil _
  | succ R ih =>
      intro h
      rw [roundStream_succ]
      exact (ih fun r hr => h r (by omega)).trans (h R (by omega))

end ActionModel

end HTN
