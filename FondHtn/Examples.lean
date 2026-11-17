import FondHtn.FixedMethodsRelations
/-!
# Examples from [CB21] and [CB22]

* `FOND.Examples.prop_2_13_converse_fails` — **[CB21, Prop. 2.13], second half**: the problem of
  the proof of Prop. 2.13 (`a` adds `1` or `2`; `b` needs `1`, `c` needs `2`; `a ≺ b`, `a ≺ c`)
  has a strong OD solution but no strong LD solution.
-/

namespace FOND

namespace Examples

open HTN

/-- The three primitive task names `a`, `b`, `c`. -/
inductive Act
  | a
  | b
  | c
  deriving DecidableEq

/-- `a ↦ (∅, {({1}, ∅), ({2}, ∅)})`. -/
def actA : Action ℕ := ⟨∅, ∅, {({1}, ∅), ({2}, ∅)}⟩

/-- `b ↦ ({1}, {2}, ∅)`. -/
def actB : Action ℕ := ⟨{1}, ∅, {({2}, ∅)}⟩

/-- `c ↦ ({2}, {1}, ∅)`. -/
def actC : Action ℕ := ⟨{2}, ∅, {({1}, ∅)}⟩

/-- The action mapping. -/
def δabc : Act → Action ℕ
  | .a => actA
  | .b => actB
  | .c => actC

/-! ## [CB21, Prop. 2.13] -/

/-- `tn_I = ⟨{1, 2, 3}, {(1, 2), (1, 3)}, 1 ↦ a, 2 ↦ b, 3 ↦ c⟩`. -/
def tn213 : TaskNetwork ℕ Act Empty where
  T := {1, 2, 3}
  ord := fun x y => x = 1 ∧ (y = 2 ∨ y = 3)
  α := fun x => if x = 1 then .inl .a else if x = 2 then .inl .b else .inl .c

/-- The problem of the proof of [CB21, Prop. 2.13] (no methods, `s_I = ∅`). -/
def P213 : Problem ℕ Act Empty ℕ where
  δ := δabc
  methods := ∅
  init := ∅
  tnI := tn213

lemma P213_decomposesTo {tn : TaskNetwork ℕ Act Empty} (h : P213.DecomposesTo tn213 tn) :
    tn = tn213 := by
  induction h with
  | refl => rfl
  | tail _ hstep _ =>
    obtain ⟨_, _, hm, -⟩ := hstep
    exact absurd hm (Set.notMem_empty _)

lemma outcomes_A {s s' : Set ℕ} (h : s' ∈ actA.outcomes s) : s' = s ∪ {1} ∨ s' = s ∪ {2} := by
  obtain ⟨e, he, rfl⟩ := h
  rcases he with rfl | rfl <;> simp [Action.applyEff]

lemma outcomes_B {s s' : Set ℕ} (h : s' ∈ actB.outcomes s) : s' = s ∪ {2} := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp [Action.applyEff]

lemma outcomes_C {s s' : Set ℕ} (h : s' ∈ actC.outcomes s) : s' = s ∪ {1} := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp [Action.applyEff]

lemma solvable_after_a (s : Set ℕ) (hs : 1 ∈ s ∨ 2 ∈ s) :
    P213.BeliefSolvable (tn213.progress 1) s := by
  rcases hs with hs | hs
  · refine .step (t := 2) (a := .b) ⟨by decide, ?_⟩ rfl ⟨by simpa [actB, δabc, P213] using hs,
      by simp [actB, δabc, P213]⟩ fun s' hs' => ?_
    · intro t' ht' h; simp [tn213] at ht' h
    · obtain rfl := outcomes_B hs'
      refine .step (t := 3) (a := .c) ⟨by decide, ?_⟩ rfl
        ⟨by simp [actC, δabc, P213], by simp [actC, δabc, P213]⟩ fun s'' _ => .empty (by decide)
      intro t' ht' h; simp [tn213] at ht' h
  · refine .step (t := 3) (a := .c) ⟨by decide, ?_⟩ rfl ⟨by simpa [actC, δabc, P213] using hs,
      by simp [actC, δabc, P213]⟩ fun s' hs' => ?_
    · intro t' ht' h; simp [tn213] at ht' h
    · obtain rfl := outcomes_C hs'
      refine .step (t := 2) (a := .b) ⟨by decide, ?_⟩ rfl
        ⟨by simp [actB, δabc, P213], by simp [actB, δabc, P213]⟩ fun s'' _ => .empty (by decide)
      intro t' ht' h; simp [tn213] at ht' h

theorem P213_strongODSolvable : P213.StrongODSolvable := by
  refine (Problem.strongODSolvable_iff_fmSolvableDB).2 ⟨tn213, ⟨Relation.ReflTransGen.refl, ?_⟩, ?_⟩
  · intro t ht
    simp only [tn213, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> simp [TaskNetwork.IsPrimitiveId, tn213]
  · refine .step (t := 1) (a := .a) ⟨by decide, ?_⟩ rfl
      ⟨by simp [actA, δabc, P213], by simp [actA, δabc, P213]⟩ fun s' hs' => ?_
    · intro t' _ h; simp [tn213] at h
    · rcases outcomes_A hs' with rfl | rfl <;> exact solvable_after_a _ (by simp)

theorem P213_not_strongLDSolvable : ¬ P213.StrongLDSolvable := by
  rintro ⟨tn, l, ⟨hd, -⟩, hl, as, has, hex⟩
  obtain rfl := P213_decomposesTo hd
  have hirr : ∀ x, ¬ tn213.ord x x := by intro x h; simp [tn213] at h; omega
  match l, hl, has with
  | [], hl, _ => exact absurd (TaskNetwork.isLinearization_nil.1 hl) (by decide)
  | x :: l', hl, has =>
    obtain ⟨hux, hl'⟩ := TaskNetwork.of_isLinearization_cons hirr hl
    have hx1 : x = 1 := by
      have hxT := hux.1
      simp only [tn213, Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with h | h | h
      · exact h
      · exact absurd (by simp [tn213, h]) (hux.2 1 (by decide))
      · exact absurd (by simp [tn213, h]) (hux.2 1 (by decide))
    subst hx1
    obtain ⟨a₁, as', rfl, hα₁, has'⟩ := TaskNetwork.isActionSeq_cons.1 has
    match l', hl', has' with
    | [], hl', _ => exact absurd (TaskNetwork.isLinearization_nil.1 hl') (by decide)
    | y :: l'', hl', has' =>
      obtain ⟨huy, -⟩ := TaskNetwork.of_isLinearization_cons
        (TaskNetwork.irrefl_progress hirr 1) hl'
      obtain ⟨a₂, as'', rfl, hα₂, -⟩ := TaskNetwork.isActionSeq_cons.1 has'
      have ha₁ : a₁ = .a := by simpa [tn213] using hα₁.symm
      subst ha₁
      obtain ⟨-, happ, -⟩ := hex
      have hyT := huy.1
      simp only [HTN.TaskNetwork.progress_T, tn213, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at hyT
      rcases hyT with ⟨hne, h | h | h⟩
      · exact absurd h hne
      · subst h
        have ha₂ : a₂ = .b := by simpa [tn213] using hα₂.symm
        subst ha₂
        have := (happ {2} ⟨∅, rfl, ({2}, ∅), by simp [P213, δabc, actA], by
          simp [Action.applyEff]⟩).1
        simp [P213, δabc, actB] at this
      · subst h
        have ha₂ : a₂ = .c := by simpa [tn213] using hα₂.symm
        subst ha₂
        have := (happ {1} ⟨∅, rfl, ({1}, ∅), by simp [P213, δabc, actA], by
          simp [Action.applyEff]⟩).1
        simp [P213, δabc, actC] at this

/-- **[CB21, Prop. 2.13], second half.** Strong OD solvability does not imply strong LD
solvability. -/
theorem prop_2_13_converse_fails : P213.StrongODSolvable ∧ ¬ P213.StrongLDSolvable :=
  ⟨P213_strongODSolvable, P213_not_strongLDSolvable⟩

end Examples

end FOND
