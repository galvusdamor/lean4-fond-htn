import HtnPlanning.Interleave.ParallelDecomp
/-!
# Productive compound tasks

A compound task is **productive** for a set of methods if it can be refined into a primitive
task network — the hierarchy, read as a context-free grammar, derives a terminal word from it.
This file defines productivity, both inductively (`HTN.Productive`) and with an explicit bound
on the depth of the refinement (`HTN.ProductiveAt`), and proves the characterisation

`HTN.exists_primitive_iff_productive` :
  a well-formed task network can be decomposed into a primitive one **iff** every compound task
  it contains is productive.

The left-to-right half is an induction on the number of decomposition steps: the first step
decomposes one task, and productivity of the decomposed task is exactly what the induction
hypothesis provides for the inserted body.  The right-to-left half is a double induction — on
the depth bound, and inside it on the number of tasks that still need the full depth.

Nothing here depends on the actions: this is the combinatorics of the hierarchy alone, and it
is what solvability of a **no-op** problem reduces to (`HTN.Problem.IsNoop.solvable_iff`).
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

/-- **A productive compound task**: some method decomposes it into a body all of whose compound
tasks are productive. -/
inductive Productive (M : Set (Method I A C)) : C → Prop
  | intro (m : Method I A C) (hm : m ∈ M)
      (h : ∀ t ∈ m.subtasks.T, ∀ c, m.subtasks.α t = Sum.inr c → Productive M c) :
      Productive M m.abstractTask

/-- **Productivity with a bound on the depth** of the refinement. -/
def ProductiveAt (M : Set (Method I A C)) : ℕ → C → Prop
  | 0, _ => False
  | k + 1, c => ∃ m ∈ M, m.abstractTask = c ∧
      ∀ t ∈ m.subtasks.T, ∀ c', m.subtasks.α t = Sum.inr c' → ProductiveAt M k c'

variable {M : Set (Method I A C)}

theorem ProductiveAt.mono {k k' : ℕ} {c : C} (hle : k ≤ k') (h : ProductiveAt M k c) :
    ProductiveAt M k' c := by
  induction k generalizing k' c with
  | zero => exact absurd h (by simp [ProductiveAt])
  | succ k ih =>
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    obtain ⟨m, hm, hab, hbody⟩ := h
    exact ⟨m, hm, hab, fun t ht c' hc' => ih (by omega) (hbody t ht c' hc')⟩

theorem ProductiveAt.productive {k : ℕ} {c : C} (h : ProductiveAt M k c) : Productive M c := by
  induction k generalizing c with
  | zero => exact absurd h (by simp [ProductiveAt])
  | succ k ih =>
    obtain ⟨m, hm, rfl, hbody⟩ := h
    exact Productive.intro m hm fun t ht c' hc' => ih (hbody t ht c' hc')

/-- A uniform depth bound for the compound tasks of a finite set of tasks. -/
theorem exists_uniform_level [DecidableEq I] {T : Finset I} {α : I → A ⊕ C}
    (h : ∀ t ∈ T, ∀ c, α t = Sum.inr c → ∃ k, ProductiveAt M k c) :
    ∃ k, ∀ t ∈ T, ∀ c, α t = Sum.inr c → ProductiveAt M k c := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k₁, hk₁⟩ := ih fun t ht => h t (Finset.mem_insert_of_mem ht)
    by_cases hc : ∃ c, α a = Sum.inr c
    · obtain ⟨c, hcc⟩ := hc
      obtain ⟨k₂, hk₂⟩ := h a (Finset.mem_insert_self _ _) c hcc
      refine ⟨max k₁ k₂, fun t ht c' hc' => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · rw [hcc] at hc'
        cases hc'
        exact hk₂.mono (le_max_right _ _)
      · exact (hk₁ t ht c' hc').mono (le_max_left _ _)
    · refine ⟨k₁, fun t ht c' hc' => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact absurd ⟨c', hc'⟩ hc
      · exact hk₁ t ht c' hc'

theorem Productive.exists_level [DecidableEq I] {c : C} (h : Productive M c) :
    ∃ k, ProductiveAt M k c := by
  induction h with
  | intro m hm hbody ih =>
    obtain ⟨k, hk⟩ := exists_uniform_level (M := M) (T := m.subtasks.T) (α := m.subtasks.α) ih
    exact ⟨k + 1, m, hm, rfl, hk⟩

/-! ### From a decomposition to productivity -/

section Sound

variable [DecidableEq I]

/-- **Every compound task of a network that decomposes into a primitive one is productive.** -/
theorem productive_of_stepsN {n : ℕ} {tn tn' : TaskNetwork I A C} (h : StepsN M n tn tn')
    (hprim : tn'.IsPrimitive) :
    ∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → Productive M c := by
  induction n generalizing tn with
  | zero =>
    cases h with
    | refl =>
      intro t ht c hc
      obtain ⟨a, ha⟩ := hprim t ht
      rw [hc] at ha
      exact absurd ha (by simp)
  | succ n ih =>
    obtain ⟨tn₂, hstep, hrest⟩ := h.exists_head
    obtain ⟨t₀, m, hm, ht₀, hα₀, u, hwfu, hisou, hdisj, rfl⟩ := hstep
    have hih := ih hrest
    intro t ht c hc
    by_cases hne : t = t₀
    · subst hne
      rw [hα₀] at hc
      have hc' : m.abstractTask = c := by
        exact (Sum.inr_injective hc)
      subst hc'
      refine Productive.intro m hm fun x hx c' hc' => ?_
      -- transport along the isomorphism `u ≅ m.subtasks`
      obtain ⟨σ, hbij, -, hα⟩ := hisou
      obtain ⟨y, hy, rfl⟩ : ∃ y ∈ u.T, σ y = x := by
        obtain ⟨y, hy, hyx⟩ := hbij.surjOn (by simpa using hx)
        exact ⟨y, by simpa using hy, hyx⟩
      have hyT : y ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inr hy)
      have hyα : (decomposeWith tn t u).α y = Sum.inr c' := by
        rw [decomposeWith_α, if_pos hy, hα y hy, hc']
      exact hih y hyT c' hyα
    · have htT : t ∈ (decomposeWith tn t₀ u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht, hne⟩)
      have htu : t ∉ u.T := fun hc' => (Finset.disjoint_left.1 hdisj ht) hc'
      have : (decomposeWith tn t₀ u).α t = Sum.inr c := by
        rw [decomposeWith_α, if_neg htu, hc]
      exact hih t htT c this

/-- The same, for the decomposition relation. -/
theorem productive_of_decomposesTo {tn tn' : TaskNetwork I A C} (h : DecomposesTo M tn tn')
    (hprim : tn'.IsPrimitive) :
    ∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → Productive M c := by
  obtain ⟨n, hn⟩ := exists_stepsN h
  exact productive_of_stepsN hn hprim

end Sound

/-! ### From productivity to a decomposition -/

section Complete

variable [DecidableEq I] [Infinite I]

open Classical in
/-- The tasks of `tn` whose compound name is not productive within depth `N`. -/
noncomputable def badSet (M : Set (Method I A C)) (N : ℕ) (tn : TaskNetwork I A C) : Finset I :=
  tn.T.filter fun t => ∃ c, tn.α t = Sum.inr c ∧ ¬ ProductiveAt M N c

theorem exists_primitive_of_productiveAt (hM : ∀ m ∈ M, m.subtasks.WF) :
    ∀ (N : ℕ) (tn : TaskNetwork I A C), tn.WF →
      (∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → ProductiveAt M N c) →
      ∃ tn', DecomposesTo M tn tn' ∧ tn'.IsPrimitive := by
  classical
  intro N
  induction N with
  | zero =>
    intro tn _ hlev
    refine ⟨tn, Relation.ReflTransGen.refl, fun t ht => ?_⟩
    rcases h : tn.α t with a | c
    · exact ⟨a, h⟩
    · exact absurd (hlev t ht c h) (by simp [ProductiveAt])
  | succ N ih =>
    -- an inner induction on the number of tasks that still need the full depth
    suffices h : ∀ (n : ℕ) (tn : TaskNetwork I A C), (badSet M N tn).card ≤ n → tn.WF →
        (∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → ProductiveAt M (N + 1) c) →
        ∃ tn', DecomposesTo M tn tn' ∧ tn'.IsPrimitive by
      intro tn hwf hlev
      exact h (badSet M N tn).card tn le_rfl hwf hlev
    have hgood : ∀ tn : TaskNetwork I A C, badSet M N tn = ∅ → tn.WF →
        ∃ tn', DecomposesTo M tn tn' ∧ tn'.IsPrimitive := by
      intro tn hbad hwf
      refine ih tn hwf fun t ht c hc => ?_
      by_contra hcon
      have hmem : t ∈ badSet M N tn := by
        simp only [badSet, Finset.mem_filter]
        exact ⟨ht, c, hc, hcon⟩
      rw [hbad] at hmem
      exact absurd hmem (Finset.notMem_empty t)
    intro n
    induction n with
    | zero =>
      intro tn hcard hwf _
      exact hgood tn (Finset.card_eq_zero.1 (by omega)) hwf
    | succ n ihn =>
      intro tn hcard hwf hlev
      by_cases hempty : badSet M N tn = ∅
      · exact hgood tn hempty hwf
      obtain ⟨t₀, ht₀⟩ := Finset.nonempty_iff_ne_empty.2 hempty
      have ht₀' := ht₀
      simp only [badSet, Finset.mem_filter] at ht₀'
      obtain ⟨ht₀T, c₀, hc₀, hnp⟩ := ht₀'
      obtain ⟨m, hm, hab, hbody⟩ := hlev t₀ ht₀T c₀ hc₀
      obtain ⟨u, hwfu, hisou, hdisj⟩ :=
        TaskNetwork.exists_fresh_iso_copy m.subtasks (hM m hm) tn.T
      have hαt₀ : tn.α t₀ = Sum.inr m.abstractTask := by rw [hc₀, hab]
      have hstep : DecompStep' M tn (decomposeWith tn t₀ u) :=
        ⟨t₀, m, hm, ht₀T, hαt₀, u, hwfu, hisou, hdisj, rfl⟩
      have hwf₂ : (decomposeWith tn t₀ u).WF := decomposeWith_wf hwf hwfu hdisj
      obtain ⟨σ, hbij, -, hσα⟩ := hisou
      have hnew : ∀ x ∈ u.T, ∀ c, u.α x = Sum.inr c → ProductiveAt M N c := by
        intro x hx c hc
        have hmemT : σ x ∈ m.subtasks.T := by simpa using hbij.mapsTo (by simpa using hx)
        have hlbl : m.subtasks.α (σ x) = Sum.inr c := by rw [← hσα x hx]; exact hc
        exact hbody _ hmemT c hlbl
      have hlab : ∀ x ∈ (decomposeWith tn t₀ u).T, ∀ c,
          (decomposeWith tn t₀ u).α x = Sum.inr c →
          (ProductiveAt M N c) ∨ (x ∈ tn.T ∧ x ≠ t₀ ∧ tn.α x = Sum.inr c) := by
        intro x hx c hc
        by_cases hxu : x ∈ u.T
        · refine Or.inl (hnew x hxu c ?_)
          rw [decomposeWith_α, if_pos hxu] at hc
          exact hc
        · rcases mem_decomposeWith_T.1 hx with ⟨hxT, hxne⟩ | hxu'
          · refine Or.inr ⟨hxT, hxne, ?_⟩
            rw [decomposeWith_α, if_neg hxu] at hc
            exact hc
          · exact absurd hxu' hxu
      have hlev₂ : ∀ x ∈ (decomposeWith tn t₀ u).T, ∀ c,
          (decomposeWith tn t₀ u).α x = Sum.inr c → ProductiveAt M (N + 1) c := by
        intro x hx c hc
        rcases hlab x hx c hc with h | ⟨hxT, -, hxα⟩
        · exact h.mono (by omega)
        · exact hlev x hxT c hxα
      have hsub : badSet M N (decomposeWith tn t₀ u) ⊆ (badSet M N tn).erase t₀ := by
        intro x hx
        simp only [badSet, Finset.mem_filter] at hx
        obtain ⟨hxT, c, hxα, hxnp⟩ := hx
        rcases hlab x hxT c hxα with h | ⟨hxTn, hxne, hxα'⟩
        · exact absurd h hxnp
        · refine Finset.mem_erase.2 ⟨hxne, ?_⟩
          simp only [badSet, Finset.mem_filter]
          exact ⟨hxTn, c, hxα', hxnp⟩
      have hcard₂ : (badSet M N (decomposeWith tn t₀ u)).card ≤ n := by
        have h1 := Finset.card_le_card hsub
        have h2 : ((badSet M N tn).erase t₀).card = (badSet M N tn).card - 1 :=
          Finset.card_erase_of_mem ht₀
        have h3 : 1 ≤ (badSet M N tn).card := Finset.card_pos.2 ⟨t₀, ht₀⟩
        omega
      obtain ⟨tn', hreach, hprim⟩ := ihn (decomposeWith tn t₀ u) hcard₂ hwf₂ hlev₂
      exact ⟨tn', Relation.ReflTransGen.head hstep hreach, hprim⟩

/-- **A well-formed network can be decomposed into a primitive one exactly when all its
compound tasks are productive.** -/
theorem exists_primitive_iff_productive (hM : ∀ m ∈ M, m.subtasks.WF)
    {tn : TaskNetwork I A C} (hwf : tn.WF) :
    (∃ tn', DecomposesTo M tn tn' ∧ tn'.IsPrimitive) ↔
      ∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → Productive M c := by
  constructor
  · rintro ⟨tn', hreach, hprim⟩
    exact productive_of_decomposesTo hreach hprim
  · intro h
    obtain ⟨N, hN⟩ := exists_uniform_level (M := M) (T := tn.T) (α := tn.α)
      fun t ht c hc => (h t ht c hc).exists_level
    exact exists_primitive_of_productiveAt hM N tn hwf hN

end Complete

end HTN
