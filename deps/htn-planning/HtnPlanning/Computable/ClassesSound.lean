import HtnPlanning.Classes.Basic
/-!
# Soundness of the conditions on descriptions

The syntactic classes of `HtnPlanning/SynClasses/Basic.lean` carry a proof that every
description satisfying their conditions denotes a problem of the corresponding semantic class.
This file proves these soundness facts; it depends only on the definitions.
-/

namespace HTN

namespace Syn

namespace MethodDesc

@[simp] lemma toMethod_abstractTask (m : MethodDesc) : m.toMethod.abstractTask = m.1 := rfl

end MethodDesc

namespace InstDesc

/-- A `STRIPS` instance description is totally ordered. -/
theorem IsStrips.isTO {q : InstDesc} (h : q.IsStrips) : q.IsTO := by
  obtain ⟨t, hT, -⟩ := h
  intro x hx y hy hxy
  rw [hT] at hx hy
  simp only [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hxy

/-- A rooted instance description is totally ordered. -/
theorem IsRooted.isTO {q : InstDesc} (h : q.IsRooted) : q.IsTO := by
  obtain ⟨t, c, hT, -⟩ := h
  intro x hx y hy hxy
  rw [hT] at hx hy
  simp only [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hxy

/-- A rooted instance description is regular. -/
theorem IsRooted.isRegular {q : InstDesc} (h : q.IsRooted) : q.IsRegular := by
  obtain ⟨t, c, hT, -⟩ := h
  refine ⟨fun x hx y hy _ _ => ?_, fun x hx _ y hy hyx => ?_⟩
  · rw [hT] at hx hy
    simp only [Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm
  · rw [hT] at hx hy
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hy.trans hx.symm) hyx

/-- A `STRIPS` instance description is regular. -/
theorem IsStrips.isRegular {q : InstDesc} (h : q.IsStrips) : q.IsRegular := by
  obtain ⟨t, hT, hα⟩ := h
  exact IsRooted.isRegular ⟨t, 0, hT, hα⟩

end InstDesc

/-! ### Soundness of the conditions -/

section Sound

variable {d : DomDesc} {q : InstDesc}

/-- A reachable method of a described problem is a listed method. -/
theorem exists_methodDesc_of_reachable {m : Method ℕ ℕ ℕ}
    (h : (problem d q).ReachableMethod m) : ∃ e ∈ d.methods, e.toMethod = m := h.1

/-- **`MethodsTO` and `IsTO` are sound**: they describe a totally ordered problem. -/
theorem isTO_problem (hd : d.MethodsTO) (hq : q.IsTO) : (problem d q).IsTO := by
  refine ⟨hq, ?_⟩
  intro m hm
  obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
  exact hd e he

/-- **`IsNoop` is sound**. -/
theorem isNoop_problem (hd : d.IsNoop) : (problem d q).IsNoop := hd

/-- **`MethodsReg` is sound for the methods**: all reachable methods are regular. -/
theorem isRegularM_problem (hd : d.MethodsReg) : (problem d q).IsRegularM := by
  intro m hm
  obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
  exact hd e he

/-- **`MethodsReg` and `InstDesc.IsRegular` are sound**: they describe a regular problem. -/
theorem isRegular_problem (hd : d.MethodsReg) (hq : q.IsRegular) : (problem d q).IsRegular :=
  ⟨hq, isRegularM_problem hd⟩

/-- The stratification a rank function induces for tail recursion: compare the ranks. -/
theorem isTailRecursive_problem (hd : d.IsTailRec) : (problem d q).IsTailRecursive := by
  obtain ⟨rk, hrk⟩ := hd
  refine ⟨fun c c' => rk c ≤ rk c', ⟨⟨fun _ _ => le_rfl, fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂,
    fun c₁ c₂ _ _ => le_total (rk c₁) (rk c₂)⟩, ?_, ?_⟩⟩
  · intro m hm t ht hlast c hc
    obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
    exact (hrk e he t ht c hc).1 hlast
  · intro m hm t ht hlast c hc
    obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
    have h := (hrk e he t ht c hc).2 hlast
    exact ⟨h.le, by simp only [MethodDesc.toMethod_abstractTask]; omega⟩

/-- The stratification a rank function induces for acyclicity: compare the ranks, breaking ties
by the task name, so that the strata are singletons as `Def. 3.5` requires. -/
theorem isAcyclic_problem (hd : d.IsAcyclic) : (problem d q).IsAcyclic := by
  obtain ⟨rk, hrk⟩ := hd
  refine ⟨fun c c' => rk c < rk c' ∨ (rk c = rk c' ∧ c ≤ c'), ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro c _
    exact Or.inr ⟨rfl, le_rfl⟩
  · intro c₁ c₂ c₃ _ _ _ h₁ h₂
    rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inl (h₂ ▸ h₁)
    · exact Or.inl (h₁ ▸ h₂)
    · exact Or.inr ⟨h₁.trans h₂, h₁'.trans h₂'⟩
  · intro c₁ c₂ _ _
    rcases lt_trichotomy (rk c₁) (rk c₂) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total c₁ c₂ with hc | hc
      · exact Or.inl (Or.inr ⟨h, hc⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hc⟩)
    · exact Or.inr (Or.inl h)
  · intro c₁ c₂ _ _ h₁ h₂
    rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩ <;> omega
  · intro m hm t ht c hc
    obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
    have h := hrk e he t ht c hc
    refine ⟨Or.inl h, ?_⟩
    simp only [MethodDesc.toMethod_abstractTask]
    omega

/-- **`IsStrips` is sound**. -/
theorem isStripsLike_problem (hd : d.IsStrips) (hq : q.IsStrips) :
    (problem d q).IsStripsLike := by
  refine ⟨0, ?_, ?_⟩
  · obtain ⟨t, hT, hα⟩ := hq
    exact ⟨t, hT, hα⟩
  · intro m hm
    obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
    exact hd e he

end Sound

end Syn

end HTN
