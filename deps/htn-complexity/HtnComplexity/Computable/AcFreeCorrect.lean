import HtnComplexity.Computable.AcFreeSplit
import HtnComplexity.Computable.Monotone
/-!
# Correctness of the vocabulary-free wrapper

This file assembles the three phases of `HtnComplexity/Computable/AcFreeWrap.lean` into

> `HTN.Syn.AcFree.solvable_wrap_iff` — the wrapped problem is solvable exactly when the goal
> facts outside the vocabulary already hold initially and the **compiled** problem of the
> acyclic construction is solvable for *some* initial state contained in the initial state of
> the source.

The under-approximation is the point of the construction: the compiled instance cannot say which
facts of the vocabulary are false in the source, so the wrapped problem is free to guess a
smaller initial state — which is sound because solvability is monotone in the initial state
(`HtnComplexity/Computable/Monotone.lean`).
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

variable {V : List ℕ} {d₀ : DomDesc} {q : InstDesc}

/-! ### The facts of the wrapper that survive the boot action -/

lemma fLic_mem_wrapExtra {v : ℕ} : fLic v ∈ wrapExtra V q ↔ v ∈ q.initList := by
  constructor
  · rintro (⟨u, hu, heq⟩ | ⟨u, -, -, heq⟩)
    · exact fLic_injective heq ▸ hu
    · exact absurd heq (fLic_ne_fRes v u)
  · exact fun hv => Or.inl ⟨v, hv, rfl⟩

lemma fRes_mem_wrapExtra {u : ℕ} : fRes u ∈ wrapExtra V q ↔ u ∈ q.initList ∧ u ∉ V := by
  constructor
  · rintro (⟨w, -, heq⟩ | ⟨w, hw, hwV, heq⟩)
    · exact absurd heq.symm (fLic_ne_fRes w u)
    · exact fRes_injective heq ▸ ⟨hw, hwV⟩
  · rintro ⟨hu, huV⟩
    exact Or.inr ⟨u, hu, huV, rfl⟩

/-- A base-shaped fact of the state after the middle phase belongs to the state of the acyclic
construction. -/
lemma mem_of_baseFact {Y : Set ℕ} {f : ℕ} (hf : BaseFact f) (h : f ∈ Y ∪ wrapExtra V q) :
    f ∈ Y := by
  rcases h with h | h
  · exact h
  · exact absurd hf (not_baseFact_wrapExtra f h)

/-! ### The two goal facts of the wrapped instance -/

lemma mem_wrapInst_goalList_res {u : ℕ} (hu : u ∈ q.goalList) :
    fRes u ∈ (wrapInst q).goalList := by
  rw [wrapInst_goalList]
  exact List.mem_append_left _ (List.mem_map_of_mem hu)

lemma mem_wrapInst_goalList_task :
    fTask (nC (rootName q)) ∈ (wrapInst q).goalList := by
  rw [wrapInst_goalList]
  exact List.mem_append_right _ (by simp)

/-! ### Correctness -/

/-- **The wrapper is correct.**  The wrapped problem is solvable exactly when every goal fact
outside the vocabulary already holds initially and the compiled acyclic problem is solvable for
some initial state contained in that of the source. -/
theorem solvable_wrap_iff (hshape : BaseShaped d₀) (q : InstDesc) :
    Solvable (wrapDom V d₀) (wrapInst q) ↔
      (∀ u ∈ q.goalList, u ∉ V → u ∈ q.initList) ∧
      ∃ S : List ℕ, (∀ u ∈ S, u ∈ q.initList ∧ u ∈ V) ∧
        Solvable d₀ (acInstOf V S (q.goalList.filter fun u => memB V u) (rootName q)) := by
  classical
  have hlab : ∀ t ∈ (netSingle (Nat.pair 0 1) (Sum.inr tTI)).T,
      GoodLabel ((netSingle (Nat.pair 0 1) (Sum.inr tTI)).α t) := fun _ _ => baseTask_tTI
  rw [solvable_wrap_split hshape q]
  constructor
  · rintro ⟨bs, hy, happ, hcond, hgoal⟩
    set Y := d₀.toDomain.transitionSeq bs (acStart V) with hYdef
    have hbs : ∀ a ∈ bs, BaseAct a := baseAct_of_netYield hshape hlab hy
    have hY : Y ⊆ baseFacts :=
      transitionSeq_subset_baseFacts hshape hbs acStart_subset_baseFacts
    -- what a goal fact of the source becomes
    have hres : ∀ u ∈ q.goalList, (u ∈ q.initList ∧ u ∉ V) ∨ (u ∈ V ∧ fPos u 2 ∈ Y) := by
      intro u hu
      rcases hgoal (mem_wrapInst_goalList_res hu) with h | ⟨v, hv, heq, hp⟩
      · rcases h with h | h
        · exact absurd (hY h) (not_baseFact_fRes u)
        · exact Or.inl (fRes_mem_wrapExtra.1 h)
      · have huv : u = v := fRes_injective heq
        subst huv
        exact Or.inr ⟨hv, mem_of_baseFact (baseFact_fPos u 2) hp⟩
    -- the compiled goal task
    have hrt : fTask (nC (rootName q)) ∈ Y := by
      rcases hgoal mem_wrapInst_goalList_task with h | ⟨v, -, heq, -⟩
      · exact mem_of_baseFact (baseFact_fTask _) h
      · exact absurd (heq ▸ baseFact_fTask (nC (rootName q))) (not_baseFact_fRes v)
    refine ⟨fun u hu huV => ?_, ?_⟩
    · rcases hres u hu with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h huV
    refine ⟨V.filter fun v => decide (v ∈ q.initList ∧ fPos v 0 ∈ Y), ?_, ?_⟩
    · intro u hu
      rw [List.mem_filter, decide_eq_true_iff] at hu
      exact ⟨hu.2.1, hu.1⟩
    · rw [solvable_gridSingle_iff (Nat.pair 0 1) rfl, acStart_eq]
      refine ⟨bs, hy, happ, ?_⟩
      intro f hf
      rcases mem_acInstOf_goalList.1 hf with ⟨u, hu, rfl⟩ | ⟨u, hu, hus, rfl⟩ |
        ⟨u, hu, rfl⟩ | rfl
      · rw [List.mem_filter, decide_eq_true_iff] at hu
        exact hu.2.2
      · rcases hcond u hu with h | ⟨hp, hl⟩
        · exact mem_of_baseFact (baseFact_fNeg u 0) h
        · exfalso
          refine hus ?_
          rw [List.mem_filter, decide_eq_true_iff]
          exact ⟨hu, fLic_mem_wrapExtra.1 (by
            rcases hl with hl | hl
            · exact absurd (hY hl) (not_baseFact_fLic u)
            · exact hl), mem_of_baseFact (baseFact_fPos u 0) hp⟩
      · rw [List.mem_filter, memB_iff] at hu
        rcases hres u hu.1 with ⟨-, h⟩ | ⟨-, h⟩
        · exact absurd hu.2 h
        · exact h
      · exact hrt
  · rintro ⟨hout, S, hS, hsolv⟩
    rw [solvable_gridSingle_iff (Nat.pair 0 1) rfl, acStart_eq] at hsolv
    obtain ⟨bs, hy, happ, hsub⟩ := hsolv
    set Y := d₀.toDomain.transitionSeq bs (acStart V) with hYdef
    refine ⟨bs, hy, happ, ?_, ?_⟩
    · intro v hv
      by_cases hvS : v ∈ S
      · refine Or.inr ⟨Or.inl (hsub (mem_acInstOf_goalList.2 (Or.inl ⟨v, hvS, rfl⟩))), ?_⟩
        exact Or.inr (fLic_mem_wrapExtra.2 (hS v hvS).1)
      · exact Or.inl (Or.inl (hsub (mem_acInstOf_goalList.2
          (Or.inr (Or.inl ⟨v, hv, hvS, rfl⟩)))))
    · intro f hf
      rw [Set.mem_setOf_eq, wrapInst_goalList, List.mem_append] at hf
      rcases hf with hf | hf
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hf
        by_cases huV : u ∈ V
        · refine Or.inr ⟨u, huV, rfl, Or.inl (hsub (mem_acInstOf_goalList.2
            (Or.inr (Or.inr (Or.inl ⟨u, ?_, rfl⟩)))))⟩
          rw [List.mem_filter, memB_iff]
          exact ⟨hu, huV⟩
        · exact Or.inl (Or.inr (fRes_mem_wrapExtra.2 ⟨hout u hu huV, huV⟩))
      · rw [List.mem_singleton] at hf
        subst hf
        exact Or.inl (Or.inl (hsub (mem_acInstOf_goalList.2 (Or.inr (Or.inr (Or.inr rfl))))))

end AcFree

end Syn

end HTN
