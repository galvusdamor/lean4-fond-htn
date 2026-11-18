import HtnComplexity.Computable.Render
import HtnComplexity.Computable.Rooted
import HtnComplexity.Computable.GridDesc
import HtnComplexity.Computable.TailDesc
import HtnPlanning.Computable.Classes
/-!
# The class of a rendering

`HtnComplexity/Computable/Render.lean` writes a semantic problem down as a pair of
descriptions.  A hardness family also has to *place* those descriptions in a class, and for the
two source classes of the three open cells of Table 3 — `HTN-AC-1` and `HTN-TR-1` — that means

* the described domain is acyclic (`HTN.Syn.DomDesc.IsAcyclic`), respectively tail recursive,
  and
* the described instance is rooted (`HTN.Syn.InstDesc.IsRooted`).

Both are read off the lists the rendering carries, and neither needs the semantics again:

* `HTN.Syn.Rendering.isAcyclic_domDesc` — a rank function on the compound task names which every
  listed body decreases makes the described domain acyclic.  Numbering the names transports the
  rank to the numbers, which is what a described rank function is;
* `HTN.Syn.Rendering.isTailRec_domDesc` — hence tail recursive;
* `HTN.Syn.Rendering.isRooted_instDesc` — an initial task network consisting of a single
  compound task makes the described instance rooted.
-/

namespace HTN

namespace Syn

open TaskNetwork

variable {F A C : Type} [Inhabited A]

namespace Rendering

variable {P : Problem F A C (ℕ × ℕ)} (R : Rendering P)

/-! ### The class of a rendering

A hardness family has to place its descriptions in a class, and for the two source classes of
the open cells of Table 3 — `HTN-AC-1` and `HTN-TR-1` — that means acyclicity, respectively tail
recursion, of the described domain and a rooted instance description.  Both are read off the
lists of the rendering: a rank function on the compound task names that decreases along the
listed bodies, and an initial task network consisting of a single compound task. -/

/-- **The described domain is acyclic**, given a rank function on the compound task names that
every listed body decreases. -/
theorem isAcyclic_domDesc [Nonempty C] (rk : C → ℕ)
    (hrk : ∀ p ∈ R.bodies, ∀ row ∈ p.2.rows, ∀ x ∈ row, ∀ c : C,
      x = Sum.inr c → rk c < rk p.1) :
    DomDesc.IsAcyclic R.domDesc := by
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
  have hlab := label_gridDescOf (eA := R.eA) (eC := R.eC) (ls := p.2.rows)
    (by simpa using hi) hj
  have hc' : (gridDescOf R.eA R.eC p.2.rows).label (Nat.pair i j) = Sum.inr c := by
    rw [← Shape.desc_label]; exact hc
  rw [hlab] at hc'
  -- so the cell carries a compound task
  set x := (p.2.rows.getD i []).getD j (Sum.inl default) with hx
  have hxmem : x ∈ p.2.rows.getD i [] := by
    rw [hx, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hrowmem : p.2.rows.getD i [] ∈ p.2.rows := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    exact List.getElem_mem _
  rcases hxsum : x with a | c₀
  · rw [hxsum] at hc'; exact absurd hc' (by simp)
  · have hcc : R.eC c₀ = c := by
      rw [hxsum] at hc'
      simpa using hc'
    have hlt : rk c₀ < rk p.1 := hrk p hp _ hrowmem x hxmem c₀ hxsum
    show rk (Function.invFun R.eC c) < rk (Function.invFun R.eC (R.eC p.1))
    rw [hinv, ← hcc, hinv]
    exact hlt

/-- **The described domain is tail recursive** under the same hypothesis, acyclicity being the
stronger condition. -/
theorem isTailRec_domDesc [Nonempty C] (rk : C → ℕ)
    (hrk : ∀ p ∈ R.bodies, ∀ row ∈ p.2.rows, ∀ x ∈ row, ∀ c : C,
      x = Sum.inr c → rk c < rk p.1) :
    DomDesc.IsTailRec R.domDesc :=
  SynClass.isAcyclic_isTailRec (R.isAcyclic_domDesc rk hrk)

/-- **The described instance is rooted**, when the initial task network of the rendering is a
single compound task. -/
theorem isRooted_instDesc {c : C} (h : R.tnIshape = ⟨[[Sum.inr c]], 0⟩) :
    InstDesc.IsRooted R.instDesc := by
  refine ⟨Nat.pair 0 0, R.eC c, ?_, ?_⟩
  · have hT : (R.tnIshape.desc R.eA R.eC).toTaskNetwork.T =
        (R.tnIshape.desc R.eA R.eC).ids.toFinset := TnDesc.toTaskNetwork_T _
    show (R.tnIshape.desc R.eA R.eC).toTaskNetwork.T = {Nat.pair 0 0}
    rw [hT, h]
    simp [Shape.desc, gridAfterDescOf, gridAfterDesc, TnDesc.ids, cellIds, gridRow]
  · show (R.tnIshape.desc R.eA R.eC).label (Nat.pair 0 0) = Sum.inr (R.eC c)
    rw [h]
    show (gridDescOf R.eA R.eC [[Sum.inr c]]).label (Nat.pair 0 0) = Sum.inr (R.eC c)
    rw [label_gridDescOf (ls := [[Sum.inr c]]) (by simp) (by simp)]
    rfl

end Rendering

end Syn

end HTN
