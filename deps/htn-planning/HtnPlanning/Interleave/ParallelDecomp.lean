import HtnPlanning.Interleave.ParallelNet
/-!
# Decomposing a composed task network

This file continues `HtnPlanning/Interleave/ParallelNet.lean` and describes how decomposition
interacts with the parallel composition `tn₁ ∥ tn₂` (`HTN.TaskNetwork.IsPar`) and the
sequential composition `tn₁ ; tn₂` (`HTN.TaskNetwork.IsSeries`).

* `HTN.decomposeWith_isPar_left` / `HTN.decomposeWith_isSeries_left` and their right-hand
  counterparts: decomposing a task of one part of a composition decomposes that part;
* `HTN.StepsN`: derivations counted by their number of decomposition steps, and
  `HTN.decomposesTo_iff_exists_stepsN`;
* `HTN.DecompStep.iso_avoiding` and `HTN.StepsN.iso_avoiding`: a decomposition step (a
  derivation) can be replayed on an isomorphic task network in such a way that the identifiers
  it creates avoid a prescribed finite set.  This is the technical ingredient that makes it
  possible to run a derivation of one part of a composition inside the composition;
* `HTN.TaskNetwork.IsPar.stepsN_split` / `HTN.TaskNetwork.IsSeries.stepsN_split`: every
  derivation of a composition splits into derivations of the two parts, with the number of
  steps adding up;
* `HTN.TaskNetwork.IsPar.exists_stepsN_of_parts` / `HTN.TaskNetwork.IsSeries.exists_stepsN_of_parts`:
  conversely, derivations of the two parts can be combined into one of the composition (up to
  renaming of the identifiers created by them).
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

open TaskNetwork

/-! ### Decomposing one part of a composition -/

section Distribute

variable [DecidableEq I] {tn tn₁ tn₂ u : TaskNetwork I A C} {t : I}

/-- **Decomposing a task of the left part of a parallel composition.** -/
lemma decomposeWith_isPar_left (h : IsPar tn tn₁ tn₂) (hw₂ : tn₂.WF)
    (ht : t ∈ tn₁.T) (hdisj : Disjoint tn.T u.T) :
    IsPar (decomposeWith tn t u) (decomposeWith tn₁ t u) tn₂ := by
  have hu₂ : Disjoint u.T tn₂.T := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx₂
    exact (Finset.disjoint_right.1 hdisj hx) ((h.memT x).2 (Or.inr hx₂))
  have hut : ∀ x ∈ tn₂.T, x ∉ u.T := fun x hx hc => (Finset.disjoint_left.1 hu₂ hc) hx
  have htn₂ : t ∉ tn₂.T := h.not_mem_right ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    intro x hx hx₂
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, -⟩ | hxu
    · exact h.not_mem_right hx₁ hx₂
    · exact hut x hx₂ hxu
  · intro x
    rw [mem_decomposeWith_T, mem_decomposeWith_T, h.memT x]
    constructor
    · rintro (⟨hx₁ | hx₂, hxt⟩ | hxu)
      · exact Or.inl (Or.inl ⟨hx₁, hxt⟩)
      · exact Or.inr hx₂
      · exact Or.inl (Or.inr hxu)
    · rintro ((⟨hx₁, hxt⟩ | hxu) | hx₂)
      · exact Or.inl ⟨Or.inl hx₁, hxt⟩
      · exact Or.inr hxu
      · exact Or.inl ⟨Or.inr hx₂, by rintro rfl; exact htn₂ hx₂⟩
  · intro x hx
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, -⟩ | hxu
    · have hxu : x ∉ u.T := Finset.disjoint_left.1 hdisj ((h.memT x).2 (Or.inl hx₁))
      simp only [decomposeWith_α, if_neg hxu]
      exact h.α₁ x hx₁
    · simp only [decomposeWith_α, if_pos hxu]
  · intro x hx
    have hxu : x ∉ u.T := hut x hx
    simp only [decomposeWith_α, if_neg hxu]
    exact h.α₂ x hx
  · intro a b
    rw [decomposeWith_ord_iff, decomposeWith_ord_iff]
    constructor
    · rintro (hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩)
      · exact Or.inl (Or.inl hab)
      · rcases (h.ord a t).1 hat with hh | hh
        · exact Or.inl (Or.inr (Or.inl ⟨hh, hb⟩))
        · exact absurd (hw₂.mem_right hh) (h.not_mem_right ht)
      · rcases (h.ord t b).1 htb with hh | hh
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hh, ha⟩)))
        · exact absurd (hw₂.mem_left hh) (h.not_mem_right ht)
      · rcases (h.ord a b).1 hab with hh | hh
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hh, hat, hbt⟩)))
        · exact Or.inr hh
    · rintro ((hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩) | hab)
      · exact Or.inl hab
      · exact Or.inr (Or.inl ⟨(h.ord a t).2 (Or.inl hat), hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(h.ord t b).2 (Or.inl htb), ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inl hab), hat, hbt⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inr hab), ?_, ?_⟩))
        · rintro rfl; exact htn₂ (hw₂.mem_left hab)
        · rintro rfl; exact htn₂ (hw₂.mem_right hab)

/-- **Decomposing a task of the right part of a parallel composition.** -/
lemma decomposeWith_isPar_right (h : IsPar tn tn₁ tn₂) (hw₁ : tn₁.WF)
    (ht : t ∈ tn₂.T) (hdisj : Disjoint tn.T u.T) :
    IsPar (decomposeWith tn t u) tn₁ (decomposeWith tn₂ t u) :=
  (decomposeWith_isPar_left h.symm hw₁ ht hdisj).symm

/-- **Decomposing a task of the left part of a sequential composition.** -/
lemma decomposeWith_isSeries_left (h : IsSeries tn tn₁ tn₂) (hw₂ : tn₂.WF)
    (ht : t ∈ tn₁.T) (hdisj : Disjoint tn.T u.T) :
    IsSeries (decomposeWith tn t u) (decomposeWith tn₁ t u) tn₂ := by
  have hu₂ : Disjoint u.T tn₂.T := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx₂
    exact (Finset.disjoint_right.1 hdisj hx) ((h.memT x).2 (Or.inr hx₂))
  have hut : ∀ x ∈ tn₂.T, x ∉ u.T := fun x hx hc => (Finset.disjoint_left.1 hu₂ hc) hx
  have htn₂ : t ∉ tn₂.T := h.not_mem_right ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    intro x hx hx₂
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, -⟩ | hxu
    · exact h.not_mem_right hx₁ hx₂
    · exact hut x hx₂ hxu
  · intro x
    rw [mem_decomposeWith_T, mem_decomposeWith_T, h.memT x]
    constructor
    · rintro (⟨hx₁ | hx₂, hxt⟩ | hxu)
      · exact Or.inl (Or.inl ⟨hx₁, hxt⟩)
      · exact Or.inr hx₂
      · exact Or.inl (Or.inr hxu)
    · rintro ((⟨hx₁, hxt⟩ | hxu) | hx₂)
      · exact Or.inl ⟨Or.inl hx₁, hxt⟩
      · exact Or.inr hxu
      · exact Or.inl ⟨Or.inr hx₂, by rintro rfl; exact htn₂ hx₂⟩
  · intro x hx
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, -⟩ | hxu
    · have hxu : x ∉ u.T := Finset.disjoint_left.1 hdisj ((h.memT x).2 (Or.inl hx₁))
      simp only [decomposeWith_α, if_neg hxu]
      exact h.α₁ x hx₁
    · simp only [decomposeWith_α, if_pos hxu]
  · intro x hx
    have hxu : x ∉ u.T := hut x hx
    simp only [decomposeWith_α, if_neg hxu]
    exact h.α₂ x hx
  · intro a b
    rw [decomposeWith_ord_iff]
    constructor
    · rintro (hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩)
      · exact Or.inl (Or.inl hab)
      · rcases (h.ord a t).1 hat with hh | hh | ⟨ha₁, ht₂⟩
        · exact Or.inl (Or.inr (Or.inl ⟨hh, hb⟩))
        · exact absurd (hw₂.mem_right hh) (h.not_mem_right ht)
        · exact absurd ht₂ (h.not_mem_right ht)
      · rcases (h.ord t b).1 htb with hh | hh | ⟨-, hb₂⟩
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hh, ha⟩)))
        · exact absurd (hw₂.mem_left hh) (h.not_mem_right ht)
        · exact Or.inr (Or.inr ⟨mem_decomposeWith_T.2 (Or.inr ha), hb₂⟩)
      · rcases (h.ord a b).1 hab with hh | hh | ⟨ha₁, hb₂⟩
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hh, hat, hbt⟩)))
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ⟨mem_decomposeWith_T.2 (Or.inl ⟨ha₁, hat⟩), hb₂⟩)
    · rintro ((hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩) | hab | ⟨ha, hb₂⟩)
      · exact Or.inl hab
      · exact Or.inr (Or.inl ⟨(h.ord a t).2 (Or.inl hat), hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(h.ord t b).2 (Or.inl htb), ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inl hab), hat, hbt⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inr (Or.inl hab)), ?_, ?_⟩))
        · rintro rfl; exact htn₂ (hw₂.mem_left hab)
        · rintro rfl; exact htn₂ (hw₂.mem_right hab)
      · rcases mem_decomposeWith_T.1 ha with ⟨ha₁, hat⟩ | hau
        · refine Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inr (Or.inr ⟨ha₁, hb₂⟩)), hat, ?_⟩))
          rintro rfl; exact htn₂ hb₂
        · exact Or.inr (Or.inr (Or.inl ⟨(h.ord t b).2 (Or.inr (Or.inr ⟨ht, hb₂⟩)), hau⟩))

/-- **Decomposing a task of the right part of a sequential composition.** -/
lemma decomposeWith_isSeries_right (h : IsSeries tn tn₁ tn₂) (hw₁ : tn₁.WF)
    (ht : t ∈ tn₂.T) (hdisj : Disjoint tn.T u.T) :
    IsSeries (decomposeWith tn t u) tn₁ (decomposeWith tn₂ t u) := by
  have hu₁ : Disjoint u.T tn₁.T := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx₁
    exact (Finset.disjoint_right.1 hdisj hx) ((h.memT x).2 (Or.inl hx₁))
  have hut : ∀ x ∈ tn₁.T, x ∉ u.T := fun x hx hc => (Finset.disjoint_left.1 hu₁ hc) hx
  have htn₁ : t ∉ tn₁.T := h.not_mem_left ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    intro x hx hx₂
    rcases mem_decomposeWith_T.1 hx₂ with ⟨hx₁, -⟩ | hxu
    · exact h.not_mem_right hx hx₁
    · exact hut x hx hxu
  · intro x
    rw [mem_decomposeWith_T, mem_decomposeWith_T, h.memT x]
    constructor
    · rintro (⟨hx₁ | hx₂, hxt⟩ | hxu)
      · exact Or.inl hx₁
      · exact Or.inr (Or.inl ⟨hx₂, hxt⟩)
      · exact Or.inr (Or.inr hxu)
    · rintro (hx₁ | (⟨hx₂, hxt⟩ | hxu))
      · exact Or.inl ⟨Or.inl hx₁, by rintro rfl; exact htn₁ hx₁⟩
      · exact Or.inl ⟨Or.inr hx₂, hxt⟩
      · exact Or.inr hxu
  · intro x hx
    have hxu : x ∉ u.T := hut x hx
    simp only [decomposeWith_α, if_neg hxu]
    exact h.α₁ x hx
  · intro x hx
    rcases mem_decomposeWith_T.1 hx with ⟨hx₂, -⟩ | hxu
    · have hxu : x ∉ u.T := Finset.disjoint_left.1 hdisj ((h.memT x).2 (Or.inr hx₂))
      simp only [decomposeWith_α, if_neg hxu]
      exact h.α₂ x hx₂
    · simp only [decomposeWith_α, if_pos hxu]
  · intro a b
    rw [decomposeWith_ord_iff]
    constructor
    · rintro (hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩)
      · exact Or.inr (Or.inl (Or.inl hab))
      · rcases (h.ord a t).1 hat with hh | hh | ⟨ha₁, -⟩
        · exact absurd (hw₁.mem_right hh) (h.not_mem_left ht)
        · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hh, hb⟩)))
        · exact Or.inr (Or.inr ⟨ha₁, mem_decomposeWith_T.2 (Or.inr hb)⟩)
      · rcases (h.ord t b).1 htb with hh | hh | ⟨ht₁, -⟩
        · exact absurd (hw₁.mem_left hh) (h.not_mem_left ht)
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hh, ha⟩))))
        · exact absurd ht₁ (h.not_mem_left ht)
      · rcases (h.ord a b).1 hab with hh | hh | ⟨ha₁, hb₂⟩
        · exact Or.inl hh
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hh, hat, hbt⟩))))
        · exact Or.inr (Or.inr ⟨ha₁, mem_decomposeWith_T.2 (Or.inl ⟨hb₂, hbt⟩)⟩)
    · rintro (hab | (hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩) | ⟨ha₁, hb⟩)
      · refine Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inl hab), ?_, ?_⟩))
        · rintro rfl; exact htn₁ (hw₁.mem_left hab)
        · rintro rfl; exact htn₁ (hw₁.mem_right hab)
      · exact Or.inl hab
      · exact Or.inr (Or.inl ⟨(h.ord a t).2 (Or.inr (Or.inl hat)), hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(h.ord t b).2 (Or.inr (Or.inl htb)), ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inr (Or.inl hab)), hat, hbt⟩))
      · rcases mem_decomposeWith_T.1 hb with ⟨hb₂, hbt⟩ | hbu
        · refine Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inr (Or.inr ⟨ha₁, hb₂⟩)), ?_, hbt⟩))
          rintro rfl; exact htn₁ ha₁
        · exact Or.inr (Or.inl ⟨(h.ord a t).2 (Or.inr (Or.inr ⟨ha₁, ht⟩)), hbu⟩)

end Distribute

/-! ### Counting decomposition steps -/

/-- `StepsN M n tn tn'`: the task network `tn` decomposes into `tn'` in exactly `n`
decomposition steps. -/
inductive StepsN [DecidableEq I] (M : Set (Method I A C)) :
    ℕ → TaskNetwork I A C → TaskNetwork I A C → Prop
  /-- The empty derivation. -/
  | refl (tn : TaskNetwork I A C) : StepsN M 0 tn tn
  /-- One more decomposition step at the end of a derivation. -/
  | tail {n : ℕ} {tn tn' tn'' : TaskNetwork I A C} (h : StepsN M n tn tn')
      (hs : DecompStep' M tn' tn'') : StepsN M (n + 1) tn tn''

namespace StepsN

variable [DecidableEq I] {M : Set (Method I A C)}

lemma decomposesTo {n : ℕ} {tn tn' : TaskNetwork I A C} (h : StepsN M n tn tn') :
    DecomposesTo M tn tn' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih hs

lemma wf {n : ℕ} {tn tn' : TaskNetwork I A C} (h : StepsN M n tn tn') (hwf : tn.WF) : tn'.WF :=
  HTN.DecomposesTo.wf h.decomposesTo hwf

lemma trans {m n : ℕ} {a b c : TaskNetwork I A C} (h₁ : StepsN M m a b) (h₂ : StepsN M n b c) :
    StepsN M (m + n) a c := by
  induction h₂ with
  | refl => simpa using h₁
  | @tail k x y z _ hs ih =>
      have : StepsN M (m + k + 1) a z := StepsN.tail (ih h₁) hs
      simpa [Nat.add_assoc] using this

lemma head {n : ℕ} {tn tn' tn'' : TaskNetwork I A C} (hs : DecompStep' M tn tn')
    (h : StepsN M n tn' tn'') : StepsN M (n + 1) tn tn'' := by
  have h₁ : StepsN M 1 tn tn' := StepsN.tail (StepsN.refl tn) hs
  simpa [Nat.add_comm] using h₁.trans h

/-- **A nonempty derivation starts with a decomposition step.** -/
lemma exists_head {n : ℕ} {tn tn'' : TaskNetwork I A C} (h : StepsN M (n + 1) tn tn'') :
    ∃ tn', DecompStep' M tn tn' ∧ StepsN M n tn' tn'' := by
  induction n generalizing tn'' with
  | zero =>
      cases h with
      | tail h hs =>
          cases h with
          | refl => exact ⟨_, hs, StepsN.refl _⟩
  | succ k ih =>
      cases h with
      | tail h hs =>
          obtain ⟨x, hx, hrest⟩ := ih h
          exact ⟨x, hx, hrest.tail hs⟩

end StepsN

/-- Every decomposition sequence has a length. -/
lemma exists_stepsN [DecidableEq I] {M : Set (Method I A C)} {tn tn' : TaskNetwork I A C}
    (h : DecomposesTo M tn tn') : ∃ n, StepsN M n tn tn' := by
  induction h with
  | refl => exact ⟨0, StepsN.refl _⟩
  | tail _ hs ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, hn.tail hs⟩

lemma decomposesTo_iff_exists_stepsN [DecidableEq I] {M : Set (Method I A C)}
    {tn tn' : TaskNetwork I A C} : DecomposesTo M tn tn' ↔ ∃ n, StepsN M n tn tn' :=
  ⟨exists_stepsN, fun ⟨_, h⟩ => h.decomposesTo⟩

/-! ### Derivations avoiding a set of identifiers -/

/-- A decomposition step that inserts a copy avoiding the finite set `S` of identifiers. -/
def DecompStepAv [DecidableEq I] (S : Finset I) (M : Set (Method I A C))
    (tn tn' : TaskNetwork I A C) : Prop :=
  ∃ (t : I) (m : Method I A C) (u : TaskNetwork I A C), m ∈ M ∧ t ∈ tn.T ∧
    tn.α t = Sum.inr m.abstractTask ∧ u.WF ∧ u.Iso m.subtasks ∧ Disjoint tn.T u.T ∧
    Disjoint S u.T ∧ tn' = decomposeWith tn t u

lemma DecompStepAv.decompStep' [DecidableEq I] {S : Finset I} {M : Set (Method I A C)}
    {tn tn' : TaskNetwork I A C} (h : DecompStepAv S M tn tn') : DecompStep' M tn tn' := by
  obtain ⟨t, m, u, hm, ht, hα, hu, hiso, hdisj, -, rfl⟩ := h
  exact ⟨t, m, hm, ht, hα, u, hu, hiso, hdisj, rfl⟩

/-- Derivations all of whose steps avoid the finite set `S`, counted by their length. -/
inductive StepsNAv [DecidableEq I] (S : Finset I) (M : Set (Method I A C)) :
    ℕ → TaskNetwork I A C → TaskNetwork I A C → Prop
  /-- The empty derivation. -/
  | refl (tn : TaskNetwork I A C) : StepsNAv S M 0 tn tn
  /-- One more avoiding decomposition step at the end of a derivation. -/
  | tail {n : ℕ} {tn tn' tn'' : TaskNetwork I A C} (h : StepsNAv S M n tn tn')
      (hs : DecompStepAv S M tn' tn'') : StepsNAv S M (n + 1) tn tn''

namespace StepsNAv

variable [DecidableEq I] {S : Finset I} {M : Set (Method I A C)}

lemma stepsN {n : ℕ} {tn tn' : TaskNetwork I A C} (h : StepsNAv S M n tn tn') :
    StepsN M n tn tn' := by
  induction h with
  | refl => exact StepsN.refl _
  | tail _ hs ih => exact ih.tail hs.decompStep'

/-- An avoiding derivation starting outside `S` stays outside `S`. -/
lemma disjoint {n : ℕ} {tn tn' : TaskNetwork I A C} (h : StepsNAv S M n tn tn')
    (hS : Disjoint tn.T S) : Disjoint tn'.T S := by
  induction h with
  | refl => exact hS
  | @tail n a b c _ hs ih =>
      obtain ⟨t, m, u, -, -, -, -, -, -, huS, rfl⟩ := hs
      refine Finset.disjoint_left.2 ?_
      intro x hx hxS
      rcases mem_decomposeWith_T.1 hx with ⟨hxb, -⟩ | hxu
      · exact (Finset.disjoint_left.1 (ih hS) hxb) hxS
      · exact (Finset.disjoint_left.1 huS hxS) hxu

end StepsNAv

/-- **A decomposition step can be replayed on an isomorphic task network with a copy avoiding a
prescribed finite set of identifiers.** -/
theorem DecompStep.iso_avoiding [DecidableEq I] [Infinite I] {M : Set (Method I A C)}
    {x x' y : TaskNetwork I A C} {t : I} {m : Method I A C} (hstep : DecompStep M x t m y)
    (hx : x.WF) (hx' : x'.WF) (hiso : x.Iso x') (S : Finset I) :
    ∃ y' : TaskNetwork I A C, DecompStepAv S M x' y' ∧ y.Iso y' := by
  classical
  obtain ⟨hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hstep
  obtain ⟨σ, hσbij, hσord, hσα⟩ := hiso
  have hσmaps : ∀ z ∈ x.T, σ z ∈ x'.T := fun z hz => by
    simpa using hσbij.mapsTo (by simpa using hz)
  obtain ⟨u', hu', hu'iso, hdisjS⟩ := TaskNetwork.exists_fresh_iso_copy u hu (x'.T ∪ S)
  rw [Finset.disjoint_union_left] at hdisjS
  obtain ⟨ρ, hρbij, hρord, hρα⟩ := hu'iso.symm
  refine ⟨decomposeWith x' (σ t) u',
    ⟨σ t, m, u', hmM, hσmaps t htT, ?_, hu', hu'iso.trans huiso, hdisjS.1, hdisjS.2, rfl⟩, ?_⟩
  · rw [← hσα t htT]; exact hαt
  · exact decomposeWith_iso_congr hx hx' hu hu' hdisj hdisjS.1 htT hσbij hσord hσα
      hρbij hρord hρα

/-- **A whole derivation can be replayed on an isomorphic task network in such a way that all
the identifiers it creates avoid a prescribed finite set.** -/
theorem StepsN.iso_avoiding [DecidableEq I] [Infinite I] {M : Set (Method I A C)} {n : ℕ}
    {x y : TaskNetwork I A C} (h : StepsN M n x y) :
    ∀ (x' : TaskNetwork I A C), x.WF → x'.WF → x.Iso x' → ∀ S : Finset I,
      ∃ y' : TaskNetwork I A C, StepsNAv S M n x' y' ∧ y.Iso y' := by
  induction h with
  | refl => exact fun x' _ _ hiso _ => ⟨x', StepsNAv.refl _, hiso⟩
  | @tail k a b c hab hbc ih =>
      intro x' hx hx' hiso S
      obtain ⟨b', hb', hbiso⟩ := ih x' hx hx' hiso S
      obtain ⟨t, m, hstep⟩ := hbc
      have hbwf : b.WF := hab.wf hx
      have hb'wf : b'.WF := hb'.stepsN.wf hx'
      obtain ⟨c', hstep', hciso⟩ := hstep.iso_avoiding hbwf hb'wf hbiso S
      exact ⟨c', hb'.tail hstep', hciso⟩

/-! ### Splitting and combining derivations of a composition -/

namespace TaskNetwork

variable [DecidableEq I] {M : Set (Method I A C)}

/-- **A derivation of the left part can be carried out inside a parallel composition**, as long
as it avoids the identifiers of the right part. -/
theorem IsPar.stepsN_lift_left {n : ℕ} {tn tn₁ tn₂ tn₁' : TaskNetwork I A C}
    (h : IsPar tn tn₁ tn₂) (hw₂ : tn₂.WF) (hd : StepsNAv tn₂.T M n tn₁ tn₁') :
    ∃ tn' : TaskNetwork I A C, StepsN M n tn tn' ∧ IsPar tn' tn₁' tn₂ := by
  induction hd with
  | refl => exact ⟨tn, StepsN.refl _, h⟩
  | @tail k a b c hab hbc ih =>
      obtain ⟨tn', hsteps, hpar⟩ := ih h
      obtain ⟨t, m, u, hm, ht, hα, hu, huiso, hdisjb, hdisj₂, rfl⟩ := hbc
      have hdisj : Disjoint tn'.T u.T := by
        refine Finset.disjoint_left.2 ?_
        intro x hx hxu
        rcases (hpar.memT x).1 hx with hx' | hx'
        · exact (Finset.disjoint_left.1 hdisjb hx') hxu
        · exact (Finset.disjoint_left.1 hdisj₂ hx') hxu
      refine ⟨decomposeWith tn' t u, hsteps.tail ⟨t, m, hm, (hpar.memT t).2 (Or.inl ht), ?_, u,
        hu, huiso, hdisj, rfl⟩, decomposeWith_isPar_left hpar hw₂ ht hdisj⟩
      rw [hpar.α₁ t ht]; exact hα

/-- **A derivation of the right part can be carried out inside a parallel composition.** -/
theorem IsPar.stepsN_lift_right {n : ℕ} {tn tn₁ tn₂ tn₂' : TaskNetwork I A C}
    (h : IsPar tn tn₁ tn₂) (hw₁ : tn₁.WF) (hd : StepsNAv tn₁.T M n tn₂ tn₂') :
    ∃ tn' : TaskNetwork I A C, StepsN M n tn tn' ∧ IsPar tn' tn₁ tn₂' := by
  obtain ⟨tn', hsteps, hpar⟩ := IsPar.stepsN_lift_left h.symm hw₁ hd
  exact ⟨tn', hsteps, hpar.symm⟩

/-- **A derivation of the left part can be carried out inside a sequential composition.** -/
theorem IsSeries.stepsN_lift_left {n : ℕ} {tn tn₁ tn₂ tn₁' : TaskNetwork I A C}
    (h : IsSeries tn tn₁ tn₂) (hw₂ : tn₂.WF) (hd : StepsNAv tn₂.T M n tn₁ tn₁') :
    ∃ tn' : TaskNetwork I A C, StepsN M n tn tn' ∧ IsSeries tn' tn₁' tn₂ := by
  induction hd with
  | refl => exact ⟨tn, StepsN.refl _, h⟩
  | @tail k a b c hab hbc ih =>
      obtain ⟨tn', hsteps, hser⟩ := ih h
      obtain ⟨t, m, u, hm, ht, hα, hu, huiso, hdisjb, hdisj₂, rfl⟩ := hbc
      have hdisj : Disjoint tn'.T u.T := by
        refine Finset.disjoint_left.2 ?_
        intro x hx hxu
        rcases (hser.memT x).1 hx with hx' | hx'
        · exact (Finset.disjoint_left.1 hdisjb hx') hxu
        · exact (Finset.disjoint_left.1 hdisj₂ hx') hxu
      refine ⟨decomposeWith tn' t u, hsteps.tail ⟨t, m, hm, (hser.memT t).2 (Or.inl ht), ?_, u,
        hu, huiso, hdisj, rfl⟩, decomposeWith_isSeries_left hser hw₂ ht hdisj⟩
      rw [hser.α₁ t ht]; exact hα

/-- **A derivation of the right part can be carried out inside a sequential composition.** -/
theorem IsSeries.stepsN_lift_right {n : ℕ} {tn tn₁ tn₂ tn₂' : TaskNetwork I A C}
    (h : IsSeries tn tn₁ tn₂) (hw₁ : tn₁.WF) (hd : StepsNAv tn₁.T M n tn₂ tn₂') :
    ∃ tn' : TaskNetwork I A C, StepsN M n tn tn' ∧ IsSeries tn' tn₁ tn₂' := by
  induction hd with
  | refl => exact ⟨tn, StepsN.refl _, h⟩
  | @tail k a b c hab hbc ih =>
      obtain ⟨tn', hsteps, hser⟩ := ih h
      obtain ⟨t, m, u, hm, ht, hα, hu, huiso, hdisjb, hdisj₁, rfl⟩ := hbc
      have hdisj : Disjoint tn'.T u.T := by
        refine Finset.disjoint_left.2 ?_
        intro x hx hxu
        rcases (hser.memT x).1 hx with hx' | hx'
        · exact (Finset.disjoint_left.1 hdisj₁ hx') hxu
        · exact (Finset.disjoint_left.1 hdisjb hx') hxu
      refine ⟨decomposeWith tn' t u, hsteps.tail ⟨t, m, hm, (hser.memT t).2 (Or.inr ht), ?_, u,
        hu, huiso, hdisj, rfl⟩, decomposeWith_isSeries_right hser hw₁ ht hdisj⟩
      rw [hser.α₂ t ht]; exact hα

/-- **Every derivation of a parallel composition splits into derivations of the two parts.** -/
theorem IsPar.stepsN_split {n : ℕ} {tn tn₁ tn₂ tn' : TaskNetwork I A C}
    (h : IsPar tn tn₁ tn₂) (hw₁ : tn₁.WF) (hw₂ : tn₂.WF) (hd : StepsN M n tn tn') :
    ∃ (n₁ n₂ : ℕ) (a b : TaskNetwork I A C), n = n₁ + n₂ ∧ StepsN M n₁ tn₁ a ∧
      StepsN M n₂ tn₂ b ∧ IsPar tn' a b := by
  induction hd with
  | refl => exact ⟨0, 0, tn₁, tn₂, rfl, StepsN.refl _, StepsN.refl _, h⟩
  | @tail k x y z hxy hstep ih =>
      obtain ⟨n₁, n₂, a, b, rfl, ha, hb, hpar⟩ := ih h
      obtain ⟨t, m, hm, ht, hα, u, hu, huiso, hdisj, rfl⟩ := hstep
      have hawf : a.WF := ha.wf hw₁
      have hbwf : b.WF := hb.wf hw₂
      rcases (hpar.memT t).1 ht with ht' | ht'
      · have hdisja : Disjoint a.T u.T :=
          Finset.disjoint_left.2 fun z hz =>
            Finset.disjoint_left.1 hdisj ((hpar.memT z).2 (Or.inl hz))
        refine ⟨n₁ + 1, n₂, decomposeWith a t u, b, by omega,
          ha.tail ⟨t, m, hm, ht', ?_, u, hu, huiso, hdisja, rfl⟩, hb,
          decomposeWith_isPar_left hpar hbwf ht' hdisj⟩
        rw [← hpar.α₁ t ht']; exact hα
      · have hdisjb : Disjoint b.T u.T :=
          Finset.disjoint_left.2 fun z hz =>
            Finset.disjoint_left.1 hdisj ((hpar.memT z).2 (Or.inr hz))
        refine ⟨n₁, n₂ + 1, a, decomposeWith b t u, by omega, ha,
          hb.tail ⟨t, m, hm, ht', ?_, u, hu, huiso, hdisjb, rfl⟩,
          decomposeWith_isPar_right hpar hawf ht' hdisj⟩
        rw [← hpar.α₂ t ht']; exact hα

/-- **Every derivation of a sequential composition splits into derivations of the two
parts.** -/
theorem IsSeries.stepsN_split {n : ℕ} {tn tn₁ tn₂ tn' : TaskNetwork I A C}
    (h : IsSeries tn tn₁ tn₂) (hw₁ : tn₁.WF) (hw₂ : tn₂.WF) (hd : StepsN M n tn tn') :
    ∃ (n₁ n₂ : ℕ) (a b : TaskNetwork I A C), n = n₁ + n₂ ∧ StepsN M n₁ tn₁ a ∧
      StepsN M n₂ tn₂ b ∧ IsSeries tn' a b := by
  induction hd with
  | refl => exact ⟨0, 0, tn₁, tn₂, rfl, StepsN.refl _, StepsN.refl _, h⟩
  | @tail k x y z hxy hstep ih =>
      obtain ⟨n₁, n₂, a, b, rfl, ha, hb, hser⟩ := ih h
      obtain ⟨t, m, hm, ht, hα, u, hu, huiso, hdisj, rfl⟩ := hstep
      have hawf : a.WF := ha.wf hw₁
      have hbwf : b.WF := hb.wf hw₂
      rcases (hser.memT t).1 ht with ht' | ht'
      · have hdisja : Disjoint a.T u.T :=
          Finset.disjoint_left.2 fun z hz =>
            Finset.disjoint_left.1 hdisj ((hser.memT z).2 (Or.inl hz))
        refine ⟨n₁ + 1, n₂, decomposeWith a t u, b, by omega,
          ha.tail ⟨t, m, hm, ht', ?_, u, hu, huiso, hdisja, rfl⟩, hb,
          decomposeWith_isSeries_left hser hbwf ht' hdisj⟩
        rw [← hser.α₁ t ht']; exact hα
      · have hdisjb : Disjoint b.T u.T :=
          Finset.disjoint_left.2 fun z hz =>
            Finset.disjoint_left.1 hdisj ((hser.memT z).2 (Or.inr hz))
        refine ⟨n₁, n₂ + 1, a, decomposeWith b t u, by omega, ha,
          hb.tail ⟨t, m, hm, ht', ?_, u, hu, huiso, hdisjb, rfl⟩,
          decomposeWith_isSeries_right hser hawf ht' hdisj⟩
        rw [← hser.α₂ t ht']; exact hα

end TaskNetwork

end HTN
