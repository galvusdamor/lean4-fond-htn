import HtnPlanning.Core.TaskNetwork
import HtnPlanning.Basic
/-!
# Decomposition methods and task decomposition

This file formalises decomposition methods and the decomposition relation of

  D. Höller, P. Bercher, G. Behnke, S. Biundo,
  *HTN Planning as Heuristic Progression Search*, JAIR 67 (2020), Section 3.2.

A method is a pair `(c, tn)` of an abstract task name and its subtask network.  A method
`(c, tn)` decomposes a task network `tn₁ = (T₁, ≺₁, α₁)` into `tn₂ = (T₂, ≺₂, α₂)` if there is
`t ∈ T₁` with `α₁(t) = c` and a task network `tn' = (T', ≺', α') ≅ tn` with `T₁ ∩ T' = ∅` and

```
tn₂ = ((T₁ \ {t}) ∪ T', ≺' ∪ ≺_D, (α₁ \ {t ↦ c}) ∪ α')
≺_D = {(t₁, t₂) | (t₁, t) ∈ ≺₁, t₂ ∈ T'}
    ∪ {(t₁, t₂) | (t, t₂) ∈ ≺₁, t₁ ∈ T'}
    ∪ {(t₁, t₂) | (t₁, t₂) ∈ ≺₁, t₁ ≠ t ∧ t₂ ≠ t}
```

We write `tn --t,m--> tn'` (`DecompStep`) for a single decomposition step and `tn →* tn'`
(`DecomposesTo`) for its reflexive transitive closure.

The main results are that decomposition preserves well-formedness
(`HTN.decomposeWith_wf`, `HTN.DecomposesTo.wf`) and the explicit description of the tasks of a
decomposed network.
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

@[simp] lemma decomposeWith_T [DecidableEq I] (tn₁ : TaskNetwork I A C) (t : I)
    (tn' : TaskNetwork I A C) :
    (decomposeWith tn₁ t tn').T = (tn₁.T.erase t) ∪ tn'.T := rfl

@[simp] lemma decomposeWith_α [DecidableEq I] (tn₁ : TaskNetwork I A C) (t : I)
    (tn' : TaskNetwork I A C) (x : I) :
    (decomposeWith tn₁ t tn').α x = if x ∈ tn'.T then tn'.α x else tn₁.α x := rfl

lemma mem_decomposeWith_T [DecidableEq I] {tn₁ : TaskNetwork I A C} {t : I}
    {tn' : TaskNetwork I A C} {x : I} :
    x ∈ (decomposeWith tn₁ t tn').T ↔ (x ∈ tn₁.T ∧ x ≠ t) ∨ x ∈ tn'.T := by
  simp [decomposeWith, Finset.mem_union, Finset.mem_erase, and_comm]

lemma decomposeWith_ord_iff [DecidableEq I] {tn₁ tn' : TaskNetwork I A C} {t a b : I} :
    (decomposeWith tn₁ t tn').ord a b ↔
      tn'.ord a b ∨ (tn₁.ord a t ∧ b ∈ tn'.T) ∨ (tn₁.ord t b ∧ a ∈ tn'.T) ∨
        (tn₁.ord a b ∧ a ≠ t ∧ b ≠ t) := Iff.rfl

/-! ### The shape of the ordering of a decomposed task network

For a fresh insertion the ordering of `decomposeWith tn₁ t tn'` decomposes into four cases,
according to whether the two ids come from the remaining old tasks or from the inserted
subtask network. -/

section OrdShape

variable [DecidableEq I] {tn₁ tn' : TaskNetwork I A C} {t x y : I}

/-- Two remaining old tasks are ordered exactly as before. -/
lemma decomposeWith_ord_old_old (h' : tn'.WF) (hdisj : Disjoint tn₁.T tn'.T)
    (hx : x ∈ tn₁.T) (hxt : x ≠ t) (hy : y ∈ tn₁.T) (hyt : y ≠ t) :
    (decomposeWith tn₁ t tn').ord x y ↔ tn₁.ord x y := by
  have hxu : x ∉ tn'.T := Finset.disjoint_left.1 hdisj hx
  have hyu : y ∉ tn'.T := Finset.disjoint_left.1 hdisj hy
  refine ⟨?_, fun h => Or.inr (Or.inr (Or.inr ⟨h, hxt, hyt⟩))⟩
  rintro (h | ⟨-, hy'⟩ | ⟨-, hx'⟩ | ⟨h, -, -⟩)
  · exact absurd (h'.mem_left h) hxu
  · exact absurd hy' hyu
  · exact absurd hx' hxu
  · exact h

/-- An old task precedes an inserted task iff it preceded the decomposed task. -/
lemma decomposeWith_ord_old_new (h₁ : tn₁.WF) (h' : tn'.WF) (hdisj : Disjoint tn₁.T tn'.T)
    (hx : x ∈ tn₁.T) (hy : y ∈ tn'.T) :
    (decomposeWith tn₁ t tn').ord x y ↔ tn₁.ord x t := by
  have hxu : x ∉ tn'.T := Finset.disjoint_left.1 hdisj hx
  have hy₁ : y ∉ tn₁.T := fun hc => (Finset.disjoint_left.1 hdisj hc) hy
  refine ⟨?_, fun h => Or.inr (Or.inl ⟨h, hy⟩)⟩
  rintro (h | ⟨h, -⟩ | ⟨-, hx'⟩ | ⟨h, -, -⟩)
  · exact absurd (h'.mem_left h) hxu
  · exact h
  · exact absurd hx' hxu
  · exact absurd (h₁.mem_right h) hy₁

/-- An inserted task precedes an old task iff the decomposed task preceded it. -/
lemma decomposeWith_ord_new_old (h₁ : tn₁.WF) (h' : tn'.WF) (hdisj : Disjoint tn₁.T tn'.T)
    (hx : x ∈ tn'.T) (hy : y ∈ tn₁.T) :
    (decomposeWith tn₁ t tn').ord x y ↔ tn₁.ord t y := by
  have hyu : y ∉ tn'.T := Finset.disjoint_left.1 hdisj hy
  have hx₁ : x ∉ tn₁.T := fun hc => (Finset.disjoint_left.1 hdisj hc) hx
  refine ⟨?_, fun h => Or.inr (Or.inr (Or.inl ⟨h, hx⟩))⟩
  rintro (h | ⟨-, hy'⟩ | ⟨h, -⟩ | ⟨h, -, -⟩)
  · exact absurd (h'.mem_right h) hyu
  · exact absurd hy' hyu
  · exact h
  · exact absurd (h₁.mem_left h) hx₁

/-- Two inserted tasks are ordered as in the inserted subtask network. -/
lemma decomposeWith_ord_new_new (h₁ : tn₁.WF) (hdisj : Disjoint tn₁.T tn'.T)
    (hx : x ∈ tn'.T) (hy : y ∈ tn'.T) :
    (decomposeWith tn₁ t tn').ord x y ↔ tn'.ord x y := by
  have hx₁ : x ∉ tn₁.T := fun hc => (Finset.disjoint_left.1 hdisj hc) hx
  have hy₁ : y ∉ tn₁.T := fun hc => (Finset.disjoint_left.1 hdisj hc) hy
  refine ⟨?_, fun h => Or.inl h⟩
  rintro (h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩)
  · exact h
  · exact absurd (h₁.mem_left h) hx₁
  · exact absurd (h₁.mem_right h) hy₁
  · exact absurd (h₁.mem_left h) hx₁

end OrdShape

/-- **Decomposition preserves well-formedness.** If `tn₁` and the inserted network `tn'` are
well formed and their identifiers are disjoint, then the decomposed network is well formed. -/
theorem decomposeWith_wf [DecidableEq I] {tn₁ tn' : TaskNetwork I A C} {t : I}
    (h₁ : tn₁.WF) (h' : tn'.WF) (hdisj : Disjoint tn₁.T tn'.T) :
    (decomposeWith tn₁ t tn').WF := by
  have hnot : ∀ x, x ∈ tn₁.T → x ∈ tn'.T → False := by
    intro x hx hx'
    exact (Finset.disjoint_left.1 hdisj hx) hx'
  constructor
  · rintro a b (hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩)
    · exact mem_decomposeWith_T.2 (Or.inr (h'.mem_left hab))
    · refine mem_decomposeWith_T.2 (Or.inl ⟨h₁.mem_left hat, ?_⟩)
      rintro rfl
      exact h₁.irrefl a hat
    · exact mem_decomposeWith_T.2 (Or.inr ha)
    · exact mem_decomposeWith_T.2 (Or.inl ⟨h₁.mem_left hab, hat⟩)
  · rintro a b (hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩)
    · exact mem_decomposeWith_T.2 (Or.inr (h'.mem_right hab))
    · exact mem_decomposeWith_T.2 (Or.inr hb)
    · refine mem_decomposeWith_T.2 (Or.inl ⟨h₁.mem_right htb, ?_⟩)
      rintro rfl
      exact h₁.irrefl b htb
    · exact mem_decomposeWith_T.2 (Or.inl ⟨h₁.mem_right hab, hbt⟩)
  · rintro a (haa | ⟨hat, ha⟩ | ⟨hta, ha⟩ | ⟨haa, -, -⟩)
    · exact h'.irrefl a haa
    · exact hnot a (h₁.mem_left hat) ha
    · exact hnot a (h₁.mem_right hta) ha
    · exact h₁.irrefl a haa
  · rintro a b c (hab | ⟨hat, hb⟩ | ⟨htb, ha⟩ | ⟨hab, hat, hbt⟩) hbc
    · -- `a ≺' b`, so `b ∈ tn'.T`
      have hb' : b ∈ tn'.T := h'.mem_right hab
      rcases hbc with (hbc | ⟨hbt, hc⟩ | ⟨htc, -⟩ | ⟨hbc, -, -⟩)
      · exact Or.inl (h'.trans hab hbc)
      · exact absurd hb' (fun hb'' => hnot b (h₁.mem_left hbt) hb'')
      · exact Or.inr (Or.inr (Or.inl ⟨htc, h'.mem_left hab⟩))
      · exact absurd hb' (fun hb'' => hnot b (h₁.mem_left hbc) hb'')
    · -- `a ≺₁ t` and `b ∈ T'`
      rcases hbc with (hbc | ⟨hbt, hc⟩ | ⟨htc, -⟩ | ⟨hbc, -, -⟩)
      · exact Or.inr (Or.inl ⟨hat, h'.mem_right hbc⟩)
      · exact absurd hb (fun hb'' => hnot b (h₁.mem_left hbt) hb'')
      · refine Or.inr (Or.inr (Or.inr ⟨h₁.trans hat htc, ?_, ?_⟩))
        · rintro rfl; exact h₁.irrefl a hat
        · rintro rfl; exact h₁.irrefl c htc
      · exact absurd hb (fun hb'' => hnot b (h₁.mem_left hbc) hb'')
    · -- `t ≺₁ b` and `a ∈ T'`
      have hbT : b ∈ tn₁.T := h₁.mem_right htb
      rcases hbc with (hbc | ⟨hbt, hc⟩ | ⟨htc, hb'⟩ | ⟨hbc, -, hct⟩)
      · exact absurd (h'.mem_left hbc) (fun hb'' => hnot b hbT hb'')
      · exact absurd (h₁.trans htb hbt) (h₁.irrefl t)
      · exact absurd hb' (fun hb'' => hnot b hbT hb'')
      · exact Or.inr (Or.inr (Or.inl ⟨h₁.trans htb hbc, ha⟩))
    · -- `a ≺₁ b` with `a ≠ t ≠ b`
      have hbT : b ∈ tn₁.T := h₁.mem_right hab
      rcases hbc with (hbc | ⟨hbt, hc⟩ | ⟨htc, hb'⟩ | ⟨hbc, -, hct⟩)
      · exact absurd (h'.mem_left hbc) (fun hb'' => hnot b hbT hb'')
      · exact Or.inr (Or.inl ⟨h₁.trans hab hbt, hc⟩)
      · exact absurd hb' (fun hb'' => hnot b hbT hb'')
      · exact Or.inr (Or.inr (Or.inr ⟨h₁.trans hab hbc, hat, hct⟩))

namespace DecomposesTo

variable [DecidableEq I] {M : Set (Method I A C)}

@[refl] lemma refl (tn : TaskNetwork I A C) : DecomposesTo M tn tn := Relation.ReflTransGen.refl

lemma single {tn tn' : TaskNetwork I A C} (h : DecompStep' M tn tn') : DecomposesTo M tn tn' :=
  Relation.ReflTransGen.single h

lemma trans {tn₁ tn₂ tn₃ : TaskNetwork I A C} (h₁ : DecomposesTo M tn₁ tn₂)
    (h₂ : DecomposesTo M tn₂ tn₃) : DecomposesTo M tn₁ tn₃ := Relation.ReflTransGen.trans h₁ h₂

lemma tail {tn₁ tn₂ tn₃ : TaskNetwork I A C} (h₁ : DecomposesTo M tn₁ tn₂)
    (h₂ : DecompStep' M tn₂ tn₃) : DecomposesTo M tn₁ tn₃ := Relation.ReflTransGen.tail h₁ h₂

end DecomposesTo

/-- **Well-formedness is preserved by a single decomposition step.** -/
theorem DecompStep.wf [DecidableEq I] {M : Set (Method I A C)} {tn₁ tn₂ : TaskNetwork I A C}
    {t : I} {m : Method I A C} (hstep : DecompStep M tn₁ t m tn₂) (h₁ : tn₁.WF) : tn₂.WF := by
  obtain ⟨-, -, -, tn', h', -, hdisj, rfl⟩ := hstep
  exact decomposeWith_wf h₁ h' hdisj

/-- **Well-formedness is preserved by arbitrary sequences of decompositions.** -/
theorem DecomposesTo.wf [DecidableEq I] {M : Set (Method I A C)} {tn₁ tn₂ : TaskNetwork I A C}
    (h : DecomposesTo M tn₁ tn₂) (h₁ : tn₁.WF) : tn₂.WF := by
  induction h with
  | refl => exact h₁
  | tail _ hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact hs.wf ih

end HTN
