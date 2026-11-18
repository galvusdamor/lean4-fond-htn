import HtnComplexity.ToHtnAc.ToHtnAc
/-!
# The copies of the state stay consistent

The compilation of totally ordered problems into acyclic ones
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`) represents each copy `v^i` of a fact `v` of the source
problem by **two** facts, `pos v i` and `neg v i`, because the action model of this development
has no negative preconditions.  The representation is only faithful as long as the two are
complementary, and the actions are designed so that they are: `setV` adds `pos` and deletes
`neg`, `delV` adds `neg` and deletes `pos`, and the compiled source operator `op2 o` flips the
first copy of every fact `o` adds or deletes — the last one only if `o` does not add and delete
the same fact, which is exactly the hypothesis `HTN.Classes.NoAddDel` of the source class.

This file proves the invariant:

* `HTN.ToAc.Consistent s` — no fact has both copies of the same index true in `s`;
* `HTN.ToAc.consistent_transition`, `HTN.ToAc.consistent_transitionSeq` — the compiled actions
  preserve it;
* `HTN.ToAc.consistent_init`, `HTN.ToAc.consistent_reached` — the compiled initial state
  satisfies it (only the `neg` facts hold there), hence so does every state a plan of the
  compiled problem reaches;
* `HTN.ToAc.Total`, `HTN.ToAc.total_transition`, `HTN.ToAc.total_reached` — the other half: every
  copy has *at least* one of its two representatives true, since an action that deletes one adds
  the other.  Together: `HTN.ToAc.neg_mem_iff_pos_notMem`, the negative copy holds exactly when
  the positive one does not.

The invariant is what a *verification phase* appended to the compiled problem needs: a test with
the two methods "`neg v 0` holds" and "`pos v 0` holds and the instance licensed `v`" then says
exactly `pos v 0 → v ∈ init`, which is the closed-world half of the compiled goal — the only
part of it that an instance description cannot write down without knowing the vocabulary of the
domain.  See `NOTES.md`.
-/

namespace HTN

namespace ToAc

variable {F A C : Type} {D : ActionModel F A} {s : Set (AcFact F A C)}

/-- **Consistency of a state of the compiled problem**: no fact of the source problem has both
its positive and its negative copy true, for any of the five copies. -/
def Consistent (s : Set (AcFact F A C)) : Prop :=
  ∀ (v : F) (i : Fin 5), ¬ (AcFact.pos v i ∈ s ∧ AcFact.neg v i ∈ s)

/-- **The compiled actions preserve consistency**, provided no operator of the source adds and
deletes the same fact. -/
theorem consistent_transition (hD : ∀ o, ∀ v ∈ D.add o, v ∉ D.del o)
    (a : AcAct F A C) (h : Consistent s) :
    Consistent ((actionModel (C := C) D).transition a s) := by
  -- an action that adds no copy of a fact cannot break the invariant
  have inert : ∀ b : AcAct F A C, (∀ (w : F) (j : Fin 5),
      AcFact.pos w j ∉ add D b ∧ AcFact.neg w j ∉ add D b) →
      Consistent ((actionModel (C := C) D).transition b s) := by
    rintro b hb v i ⟨hpos, hneg⟩
    simp only [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff] at hpos hneg
    rcases hpos with ⟨hp, -⟩ | hp
    · rcases hneg with ⟨hn, -⟩ | hn
      · exact h v i ⟨hp, hn⟩
      · exact (hb v i).2 hn
    · exact (hb v i).1 hp
  cases a with
  | setV w j =>
    rintro v i ⟨hpos, hneg⟩
    simp only [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff] at hpos hneg
    rcases hneg with ⟨hneg, hnd⟩ | hneg
    · refine hnd ?_
      rcases hpos with ⟨hp, -⟩ | hp
      · exact absurd ⟨hp, hneg⟩ (h v i)
      · obtain ⟨rfl, rfl⟩ : v = w ∧ i = j := by
          cases (hp : AcFact.pos v i = AcFact.pos w j)
          exact ⟨rfl, rfl⟩
        rfl
    · exact absurd hneg (by simp [add])
  | delV w j =>
    rintro v i ⟨hpos, hneg⟩
    simp only [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff] at hpos hneg
    rcases hpos with ⟨hpos, hnd⟩ | hpos
    · refine hnd ?_
      rcases hneg with ⟨hn, -⟩ | hn
      · exact absurd ⟨hpos, hn⟩ (h v i)
      · obtain ⟨rfl, rfl⟩ : v = w ∧ i = j := by
          cases (hn : AcFact.neg v i = AcFact.neg w j)
          exact ⟨rfl, rfl⟩
        rfl
    · exact absurd hpos (by simp [add])
  | op2 o =>
    -- the compiled operator flips the first copy of every fact the source operator touches
    have hadd : ∀ f : AcFact F A C, f ∈ add D (AcAct.op2 (C := C) o) ↔
        (∃ w ∈ D.add o, f = AcFact.pos w 1) ∨ ∃ w ∈ D.del o, f = AcFact.neg w 1 := by
      intro f
      simp only [add, Set.mem_union, Set.mem_image]
      constructor
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
    have hdel : ∀ f : AcFact F A C, f ∈ del D (AcAct.op2 (C := C) o) ↔
        (∃ w ∈ D.add o, f = AcFact.neg w 1) ∨ ∃ w ∈ D.del o, f = AcFact.pos w 1 := by
      intro f
      simp only [del, Set.mem_union, Set.mem_image]
      constructor
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
    rintro v i ⟨hpos, hneg⟩
    simp only [ActionModel.transition, actionModel, Set.mem_union, Set.mem_diff] at hpos hneg
    rcases hpos with ⟨hp, hpd⟩ | hp
    · rcases hneg with ⟨hn, -⟩ | hn
      · exact absurd ⟨hp, hn⟩ (h v i)
      · -- the negative copy was added, so the positive one was deleted
        rcases (hadd _).1 hn with ⟨w, hw, hwv⟩ | ⟨w, hw, hwv⟩
        · exact absurd hwv (by simp)
        · obtain ⟨rfl, rfl⟩ : v = w ∧ i = 1 := by
            cases hwv
            exact ⟨rfl, rfl⟩
          exact hpd ((hdel _).2 (Or.inr ⟨v, hw, rfl⟩))
    · rcases (hadd _).1 hp with ⟨w, hw, hwv⟩ | ⟨w, hw, hwv⟩
      · obtain ⟨rfl, rfl⟩ : v = w ∧ i = 1 := by
          cases hwv
          exact ⟨rfl, rfl⟩
        rcases hneg with ⟨-, hnd⟩ | hn
        · exact hnd ((hdel _).2 (Or.inl ⟨v, hw, rfl⟩))
        · rcases (hadd _).1 hn with ⟨w', hw', hwv'⟩ | ⟨w', hw', hwv'⟩
          · exact absurd hwv' (by simp)
          · obtain ⟨rfl, -⟩ : v = w' ∧ (1 : Fin 5) = 1 := by
              cases hwv'
              exact ⟨rfl, rfl⟩
            exact hD o v hw hw'
      · exact absurd hwv (by simp)
  | prePV w j k => exact inert _ (by simp [add])
  | preNV w j k => exact inert _ (by simp [add])
  | setC t => exact inert _ (by simp [add])
  | preC t => exact inert _ (by simp [add])
  | lock => exact inert _ (by simp [add])
  | unlock => exact inert _ (by simp [add])
  | ask x => exact inert _ (by simp [add])
  | accept x => exact inert _ (by simp [add])
  | doneA x => exact inert _ (by simp [add])
  | waitA x => exact inert _ (by simp [add])

/-! ### The other half: every copy has a truth value -/

/-- **Totality of a state of the compiled problem**: every copy of every fact of the source
problem has at least one of its two representatives true. -/
def Total (s : Set (AcFact F A C)) : Prop :=
  ∀ (v : F) (i : Fin 5), AcFact.pos v i ∈ s ∨ AcFact.neg v i ∈ s

/-- **The compiled actions preserve totality**: an action that deletes one representative of a
copy adds the other one. -/
theorem total_transition (a : AcAct F A C) (h : Total s) :
    Total ((actionModel (C := C) D).transition a s) := by
  -- an action that deletes no copy of a fact cannot break totality
  have inert : ∀ b : AcAct F A C, (∀ (w : F) (j : Fin 5),
      AcFact.pos w j ∉ del D b ∧ AcFact.neg w j ∉ del D b) →
      Total ((actionModel (C := C) D).transition b s) := by
    intro b hb v i
    rcases h v i with hp | hn
    · exact Or.inl (Or.inl ⟨hp, (hb v i).1⟩)
    · exact Or.inr (Or.inl ⟨hn, (hb v i).2⟩)
  cases a with
  | setV w j =>
    intro v i
    by_cases hvw : (AcFact.pos v i : AcFact F A C) = AcFact.pos w j
    · exact Or.inl (Or.inr (by rw [hvw]; rfl))
    · rcases h v i with hp | hn
      · exact Or.inl (Or.inl ⟨hp, by simp [actionModel, del]⟩)
      · refine Or.inr (Or.inl ⟨hn, ?_⟩)
        simp only [actionModel, del]
        intro hmem
        obtain ⟨rfl, rfl⟩ : v = w ∧ i = j := by
          cases (hmem : AcFact.neg v i = AcFact.neg w j)
          exact ⟨rfl, rfl⟩
        exact hvw rfl
  | delV w j =>
    intro v i
    by_cases hvw : (AcFact.neg v i : AcFact F A C) = AcFact.neg w j
    · exact Or.inr (Or.inr (by rw [hvw]; rfl))
    · rcases h v i with hp | hn
      · refine Or.inl (Or.inl ⟨hp, ?_⟩)
        simp only [actionModel, del]
        intro hmem
        obtain ⟨rfl, rfl⟩ : v = w ∧ i = j := by
          cases (hmem : AcFact.pos v i = AcFact.pos w j)
          exact ⟨rfl, rfl⟩
        exact hvw rfl
      · exact Or.inr (Or.inl ⟨hn, by simp [actionModel, del]⟩)
  | op2 o =>
    have hadd : ∀ f : AcFact F A C, f ∈ add D (AcAct.op2 (C := C) o) ↔
        (∃ w ∈ D.add o, f = AcFact.pos w 1) ∨ ∃ w ∈ D.del o, f = AcFact.neg w 1 := by
      intro f
      simp only [add, Set.mem_union, Set.mem_image]
      constructor
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
    have hdel : ∀ f : AcFact F A C, f ∈ del D (AcAct.op2 (C := C) o) ↔
        (∃ w ∈ D.add o, f = AcFact.neg w 1) ∨ ∃ w ∈ D.del o, f = AcFact.pos w 1 := by
      intro f
      simp only [del, Set.mem_union, Set.mem_image]
      constructor
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
      · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
    intro v i
    by_cases hv : (∃ w ∈ D.add o, (AcFact.pos v i : AcFact F A C) = AcFact.pos w 1) ∨
        ∃ w ∈ D.del o, (AcFact.neg v i : AcFact F A C) = AcFact.neg w 1
    · rcases hv with ⟨w, hw, hwv⟩ | ⟨w, hw, hwv⟩
      · exact Or.inl (Or.inr ((hadd _).2 (Or.inl ⟨w, hw, hwv⟩)))
      · exact Or.inr (Or.inr ((hadd _).2 (Or.inr ⟨w, hw, hwv⟩)))
    · push_neg at hv
      rcases h v i with hp | hn
      · refine Or.inl (Or.inl ⟨hp, ?_⟩)
        intro hmem
        rcases (hdel _).1 hmem with ⟨w, hw, hwv⟩ | ⟨w, hw, hwv⟩
        · exact absurd hwv (by simp)
        · exact absurd hwv (by
            obtain ⟨rfl, rfl⟩ : v = w ∧ i = 1 := by
              cases hwv
              exact ⟨rfl, rfl⟩
            exact fun _ => (hv.2 v hw) rfl)
      · refine Or.inr (Or.inl ⟨hn, ?_⟩)
        intro hmem
        rcases (hdel _).1 hmem with ⟨w, hw, hwv⟩ | ⟨w, hw, hwv⟩
        · obtain ⟨rfl, rfl⟩ : v = w ∧ i = 1 := by
            cases hwv
            exact ⟨rfl, rfl⟩
          exact (hv.1 v hw) rfl
        · exact absurd hwv (by simp)
  | prePV w j k => exact inert _ (by simp [del])
  | preNV w j k => exact inert _ (by simp [del])
  | setC t => exact inert _ (by simp [del])
  | preC t => exact inert _ (by simp [del])
  | lock => exact inert _ (by simp [del])
  | unlock => exact inert _ (by simp [del])
  | ask x => exact inert _ (by simp [del])
  | accept x => exact inert _ (by simp [del])
  | doneA x => exact inert _ (by simp [del])
  | waitA x => exact inert _ (by simp [del])

/-- **A plan of the compiled problem preserves totality.** -/
theorem total_transitionSeq (as : List (AcAct F A C)) (h : Total s) :
    Total ((actionModel (C := C) D).transitionSeq as s) := by
  induction as generalizing s with
  | nil => simpa using h
  | cons a as ih =>
    rw [ActionModel.transitionSeq_cons]
    exact ih (total_transition a h)

/-- **The compiled initial state is total**: every negative copy holds there. -/
theorem total_init {I : Type} (Q : Instance F A C I) (tI0 : C) :
    Total (instance_ Q tI0).init := fun v i => Or.inr (Or.inr ⟨v, i, rfl⟩)

/-- **A plan of the compiled problem preserves consistency.** -/
theorem consistent_transitionSeq (hD : ∀ o, ∀ v ∈ D.add o, v ∉ D.del o)
    (as : List (AcAct F A C)) (h : Consistent s) :
    Consistent ((actionModel (C := C) D).transitionSeq as s) := by
  induction as generalizing s with
  | nil => simpa using h
  | cons a as ih =>
    rw [ActionModel.transitionSeq_cons]
    exact ih (consistent_transition hD a h)

/-- **The compiled initial state is consistent**: only the negative copies hold there. -/
theorem consistent_init {I : Type} (Q : Instance F A C I) (tI0 : C) :
    Consistent (instance_ Q tI0).init := by
  rintro v i ⟨hpos, -⟩
  rcases hpos with hpos | ⟨w, j, hwj⟩
  · exact absurd hpos (by simp)
  · exact absurd hwj (by simp)

/-- **Every state a plan of the compiled problem reaches is consistent.** -/
theorem consistent_reached {I : Type} (Dom : Domain F A C I) (Q : Instance F A C I)
    (vars : List F) (bound : ℕ) (tI0 : C)
    (hD : ∀ o, ∀ v ∈ Dom.add o, v ∉ Dom.del o) (as : List (AcAct F A C)) :
    Consistent ((problem Dom Q vars bound tI0).transitionSeq as
      (problem Dom Q vars bound tI0).init) :=
  consistent_transitionSeq hD as (consistent_init Q tI0)

/-- **Every state a plan of the compiled problem reaches is total.** -/
theorem total_reached {I : Type} (Dom : Domain F A C I) (Q : Instance F A C I)
    (vars : List F) (bound : ℕ) (tI0 : C) (as : List (AcAct F A C)) :
    Total ((problem Dom Q vars bound tI0).transitionSeq as
      (problem Dom Q vars bound tI0).init) :=
  total_transitionSeq as (total_init Q tI0)

/-- **The two representatives of a copy are complementary along every plan of the compiled
problem**: the negative copy holds exactly when the positive one does not. -/
theorem neg_mem_iff_pos_notMem {I : Type} (Dom : Domain F A C I) (Q : Instance F A C I)
    (vars : List F) (bound : ℕ) (tI0 : C)
    (hD : ∀ o, ∀ v ∈ Dom.add o, v ∉ Dom.del o) (as : List (AcAct F A C)) (v : F) (i : Fin 5) :
    AcFact.neg v i ∈ (problem Dom Q vars bound tI0).transitionSeq as
        (problem Dom Q vars bound tI0).init ↔
      AcFact.pos v i ∉ (problem Dom Q vars bound tI0).transitionSeq as
        (problem Dom Q vars bound tI0).init := by
  constructor
  · intro hn hp
    exact consistent_reached Dom Q vars bound tI0 hD as v i ⟨hp, hn⟩
  · intro hp
    exact (total_reached Dom Q vars bound tI0 as v i).resolve_left hp

end ToAc

end HTN
