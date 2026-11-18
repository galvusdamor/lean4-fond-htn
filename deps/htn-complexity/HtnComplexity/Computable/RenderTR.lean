import HtnComplexity.Computable.RenderClass
/-!
# Tail recursion of a rendering

`HTN.Syn.Rendering.isTailRec_domDesc` (`HtnComplexity/Computable/RenderClass.lean`) gets
tail recursion from acyclicity.  A domain with loops — a method `X → [Y, X]` — is tail recursive
without being acyclic, and this file reads tail recursion off the lists of a rendering directly:

* `HTN.Syn.Rendering.isTailRec_domDesc_of` — a rank function on the compound task names such
  that every compound cell of a listed body has a smaller rank than the decomposed task, except
  possibly the *last cell of a body consisting of a single row*, which may keep the rank, makes
  the described domain tail recursive.
-/

namespace HTN

namespace Syn

open TaskNetwork

variable {F A C : Type} [Inhabited A]

namespace Rendering

variable {P : Problem F A C (ℕ × ℕ)} (R : Rendering P)

/-- **The described domain is tail recursive**, given a rank function on the compound task names
that every compound cell of a listed body decreases, except possibly the last cell of a body
consisting of a single row with no ordering constraint added, which may keep it. -/
theorem isTailRec_domDesc_of [Nonempty C] (rk : C → ℕ)
    (hrk : ∀ p ∈ R.bodies, ∀ i j : ℕ, i < p.2.rows.length → j < (p.2.rows.getD i []).length →
      ∀ c : C, (p.2.rows.getD i []).getD j (Sum.inl default) = Sum.inr c →
        rk c < rk p.1 ∨ (rk c ≤ rk p.1 ∧ p.2.after = 0 ∧ p.2.rows.length = 1 ∧
          j + 1 = (p.2.rows.getD i []).length)) :
    DomDesc.IsTailRec R.domDesc := by
  classical
  refine ⟨fun k => rk (Function.invFun R.eC k), ?_⟩
  have hinv : ∀ c : C, Function.invFun R.eC (R.eC c) = c :=
    Function.leftInverse_invFun R.eC_inj
  rintro e he t ht c hc
  simp only [domDesc, DomDesc.methods, List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  -- the identifier is a cell of the grid
  have ht' : t ∈ (gridDescOf R.eA R.eC p.2.rows).ids := by
    have h := ht
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, Shape.desc_ids] at h
    exact h
  simp only [gridDescOf, gridDesc_ids, mem_cellIds] at ht'
  obtain ⟨i, j, hi, hj, rfl⟩ := ht'
  rw [length_gridRow_map] at hj
  have hi' : i < p.2.rows.length := by simpa using hi
  have hlab := label_gridDescOf (eA := R.eA) (eC := R.eC) (ls := p.2.rows) hi' hj
  have hc' : (gridDescOf R.eA R.eC p.2.rows).label (Nat.pair i j) = Sum.inr c := by
    rw [← Shape.desc_label]; exact hc
  rw [hlab] at hc'
  -- so the cell carries a compound task
  rcases hxsum : (p.2.rows.getD i []).getD j (Sum.inl default) with a | c₀
  · rw [hxsum] at hc'; exact absurd hc' (by simp)
  · have hcc : R.eC c₀ = c := by
      rw [hxsum] at hc'
      simpa using hc'
    have hrk' : rk (Function.invFun R.eC c) = rk c₀ := by rw [← hcc, hinv]
    have hrk1 : rk (Function.invFun R.eC (R.eC p.1)) = rk p.1 := by rw [hinv]
    show (_ → rk (Function.invFun R.eC c) ≤ rk (Function.invFun R.eC (R.eC p.1))) ∧
      (_ → rk (Function.invFun R.eC c) < rk (Function.invFun R.eC (R.eC p.1)))
    rw [hrk', hrk1]
    rcases hrk p hp i j hi' hj c₀ hxsum with hlt | ⟨hle, haft, hlen, hlast⟩
    · exact ⟨fun _ => hlt.le, fun _ => hlt⟩
    · refine ⟨fun _ => hle, fun hnot => absurd ?_ hnot⟩
      -- the cell is the last one of the only row
      have hi0 : i = 0 := by omega
      subst hi0
      refine ⟨ht, fun t' ht'' hne => ?_⟩
      have ht2 : t' ∈ (gridDescOf R.eA R.eC p.2.rows).ids := by
        have h := ht''
        rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, Shape.desc_ids] at h
        exact h
      simp only [gridDescOf, gridDesc_ids, mem_cellIds] at ht2
      obtain ⟨i', j', hi'', hj', rfl⟩ := ht2
      rw [length_gridRow_map] at hj'
      have hi0' : i' = 0 := by simp at hi''; omega
      subst hi0'
      have hjj : j' < j := by
        rcases lt_trichotomy j' j with h | rfl | h
        · exact h
        · exact absurd rfl hne
        · omega
      show (gridAfterDesc _ p.2.after).toTaskNetwork.ord _ _
      rw [gridAfterDesc_ord]
      refine Or.inl ⟨0, j', j, by simpa using hi', hjj, ?_, rfl, rfl⟩
      rw [length_gridRow_map]; exact hj

end Rendering

end Syn

end HTN
