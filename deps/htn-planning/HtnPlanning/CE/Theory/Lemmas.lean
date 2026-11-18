import HtnPlanning.CE.Basic
/-!
# Basic lemmas on classical planning with conditional effects

Lemmas about the definitions of `HtnPlanning/CE/Basic.lean`.
-/

namespace HTN

namespace CE

universe u v w

/-! ### Literals -/

namespace Lits

variable {F : Type u}

@[simp] lemma pos_empty : (∅ : Lits F).pos = ∅ := rfl

@[simp] lemma neg_empty : (∅ : Lits F).neg = ∅ := rfl

@[simp] lemma holds_empty (s : Set F) : (∅ : Lits F).Holds s := ⟨by simp, by simp⟩

lemma holds_union {L L' : Lits F} {s : Set F} :
    (L.union L').Holds s ↔ L.Holds s ∧ L'.Holds s := by
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨⟨fun _ hf => hp (Or.inl hf), fun f hf => hn f (Or.inl hf)⟩,
      ⟨fun _ hf => hp (Or.inr hf), fun f hf => hn f (Or.inr hf)⟩⟩
  · rintro ⟨⟨hp, hn⟩, ⟨hp', hn'⟩⟩
    exact ⟨fun f hf => hf.elim (fun h => hp h) (fun h => hp' h),
      fun f hf => hf.elim (fun h => hn f h) (fun h => hn' f h)⟩

/-- Whether a set of literals holds only depends on the truth values of its atoms. -/
lemma holds_congr {L : Lits F} {s t : Set F} (h : ∀ f ∈ L.atoms, (f ∈ s ↔ f ∈ t)) :
    L.Holds s ↔ L.Holds t := by
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨fun f hf => (h f (Or.inl hf)).1 (hp hf),
      fun f hf hmem => hn f hf ((h f (Or.inr hf)).2 hmem)⟩
  · rintro ⟨hp, hn⟩
    exact ⟨fun f hf => (h f (Or.inl hf)).2 (hp hf),
      fun f hf hmem => hn f hf ((h f (Or.inr hf)).1 hmem)⟩

/-- A set of literals that does not hold has a witness: either a positive literal that is false
or a negative literal that is true. -/
lemma exists_of_not_holds {L : Lits F} {s : Set F} (h : ¬ L.Holds s) :
    (∃ f ∈ L.pos, f ∉ s) ∨ (∃ f ∈ L.neg, f ∈ s) := by
  by_contra hc
  push_neg at hc
  exact h ⟨fun f hf => hc.1 f hf, fun f hf hmem => hc.2 f hf hmem⟩

end Lits

/-! ### Actions with conditional effects -/

namespace Action

variable {F : Type u}

lemma mem_succ {a : Action F} {s : Set F} {f : F} :
    f ∈ a.succ s ↔ f ∈ a.adds s ∨ (f ∈ s ∧ f ∉ a.dels s) := by
  simp only [succ, Set.mem_union, Set.mem_diff]
  tauto

/-! #### The semantics does not depend on the order of the conditional effects -/

lemma adds_congr_perm {a a' : Action F} (h : a.post.Perm a'.post) (s : Set F) :
    a.adds s = a'.adds s := by
  ext f
  simp only [adds, Set.mem_setOf_eq]
  exact ⟨fun ⟨e, he, h₁, h₂⟩ => ⟨e, h.mem_iff.1 he, h₁, h₂⟩,
    fun ⟨e, he, h₁, h₂⟩ => ⟨e, h.mem_iff.2 he, h₁, h₂⟩⟩

lemma dels_congr_perm {a a' : Action F} (h : a.post.Perm a'.post) (s : Set F) :
    a.dels s = a'.dels s := by
  ext f
  simp only [dels, Set.mem_setOf_eq]
  exact ⟨fun ⟨e, he, h₁, h₂⟩ => ⟨e, h.mem_iff.1 he, h₁, h₂⟩,
    fun ⟨e, he, h₁, h₂⟩ => ⟨e, h.mem_iff.2 he, h₁, h₂⟩⟩

lemma succ_congr_perm {a a' : Action F} (h : a.post.Perm a'.post) (s : Set F) :
    a.succ s = a'.succ s := by
  simp only [succ, adds_congr_perm h, dels_congr_perm h]

end Action

/-! ### Effect interference -/

variable {F : Type u}

/-- A simple action is effect acyclic. -/
lemma Action.EffectAcyclic.of_isSimple {a : Action F} (h : a.IsSimple) : a.EffectAcyclic := by
  refine ⟨a.post, List.Perm.refl _, ?_⟩
  refine List.pairwise_iff_forall_sublist.2 ?_
  intro e e' hsub
  have he' : e' ∈ a.post := hsub.subset (by simp)
  have hce : e'.cond = (∅ : Lits F) := h e' he'
  simp [Lits.atoms, hce]

/-! ### Planning problems -/

namespace Problem

variable {A : Type v} (P : Problem F A)

@[simp] lemma transitionSeq_nil (s : Set F) : P.transitionSeq [] s = s := rfl

@[simp] lemma transitionSeq_cons (a : A) (as : List A) (s : Set F) :
    P.transitionSeq (a :: as) s = P.transitionSeq as ((P.act a).succ s) := rfl

@[simp] lemma seqApplicable_nil (s : Set F) : P.SeqApplicable [] s := trivial

@[simp] lemma seqApplicable_cons {a : A} {as : List A} {s : Set F} :
    P.SeqApplicable (a :: as) s ↔
      (P.act a).Applicable s ∧ P.SeqApplicable as ((P.act a).succ s) := Iff.rfl

lemma transitionSeq_append (as bs : List A) (s : Set F) :
    P.transitionSeq (as ++ bs) s = P.transitionSeq bs (P.transitionSeq as s) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => simp [ih]

lemma seqApplicable_append (as bs : List A) (s : Set F) :
    P.SeqApplicable (as ++ bs) s ↔
      P.SeqApplicable as s ∧ P.SeqApplicable bs (P.transitionSeq as s) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => simp [ih, and_assoc]

lemma IsSimple.isAcyclic {P : Problem F A} (h : P.IsSimple) : P.IsAcyclic :=
  fun a => Action.EffectAcyclic.of_isSimple (h a)

end Problem

end CE

end HTN
