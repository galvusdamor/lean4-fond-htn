import HtnPlanning.Core.Relabel
import HtnPlanning.Core.Construction
/-!
# Relabelling the grid networks of a construction

`HtnPlanning/Core/Relabel.lean` transports a task network along a change of signature, and
`HtnPlanning/Core/Transfer.lean` transports solvability along it.  Every concrete construction
of this development builds its method bodies with `HTN.TaskNetwork.grid` and its initial network
with `HTN.TaskNetwork.gridTail`, so to use those transport theorems one needs to know what the
change of signature does to a grid.  The answer is the obvious one — it relabels the chains —
and this file proves it.

The one hypothesis worth naming is `eA default = default`: the label function of a grid is total,
and outside the grid it returns the dummy `Sum.inl default`.  Two grids over different action
types are therefore equal *as functions* only when the dummies correspond.  Every relabelling
used here is an injection into a sum type whose `Inhabited` instance is inherited from the left
summand, so the hypothesis is discharged by `rfl`.

## Main results

* `HTN.TaskNetwork.relabel_grid`, `HTN.TaskNetwork.relabel_gridTail`, `HTN.TaskNetwork.relabel_seq`
  — the image of a grid, of a grid with a tail chain and of a chain;
* `HTN.Method.relabel_grid` — the image of a method whose body is a grid.
-/

namespace HTN

universe v v' w w'

variable {A : Type v} {A' : Type v'} {C : Type w} {C' : Type w'}

namespace TaskNetwork

/-- Reading a list of lists at an index commutes with mapping each inner list. -/
lemma getD_map_map_nil {α β : Type*} (g : α → β) (ls : List (List α)) (i : ℕ) :
    (ls.map (List.map g)).getD i [] = (ls.getD i []).map g := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : ls[i]? with
  | none => simp
  | some l => simp

/-- Reading a list at an index commutes with mapping it, provided the two defaults correspond. -/
lemma getD_map_of_default {α β : Type*} (g : α → β) (l : List α) (j : ℕ) (d : α) (d' : β)
    (hd : g d = d') : (l.map g).getD j d' = g (l.getD j d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[j]? with
  | none => simp [hd]
  | some a => simp

variable [Inhabited A] [Inhabited A']

/-- **The image of a grid network** under a change of signature is the grid of the relabelled
chains. -/
lemma relabel_grid (eA : A → A') (eC : C → C') (hdef : eA default = default)
    (ls : List (List (A ⊕ C))) :
    relabel eA eC (Equiv.refl (ℕ × ℕ)) (grid ls)
      = grid (ls.map (List.map (Sum.map eA eC))) := by
  have hlen : ∀ i, ((ls.map (List.map (Sum.map eA eC))).getD i []).length
      = (ls.getD i []).length := by
    intro i; rw [getD_map_map_nil]; simp
  refine ext' ?_ ?_ ?_
  · simp only [relabel_T, Equiv.coe_refl, Finset.image_id]
    ext p
    simp only [mem_grid_T, List.length_map, hlen]
  · funext p q
    simp only [relabel_ord, Equiv.refl_symm, Equiv.coe_refl, id_eq, grid_ord, hlen]
  · funext p
    show Sum.map eA eC ((grid ls).α ((Equiv.refl (ℕ × ℕ)).symm p)) = _
    simp only [Equiv.refl_symm, Equiv.coe_refl, id_eq, grid_α, getD_map_map_nil]
    exact (getD_map_of_default (Sum.map eA eC) _ p.2 (Sum.inl default) (Sum.inl default)
      (by simp [hdef])).symm

/-- **The image of a chain network.** -/
lemma relabel_seq (eA : A → A') (eC : C → C') (hdef : eA default = default)
    (l : List (A ⊕ C)) :
    relabel eA eC (Equiv.refl (ℕ × ℕ)) (seq l) = seq (l.map (Sum.map eA eC)) := by
  simp [seq, relabel_grid eA eC hdef]

/-- **The image of a grid network with a tail chain.** -/
lemma relabel_gridTail (eA : A → A') (eC : C → C') (hdef : eA default = default)
    (ls : List (List (A ⊕ C))) (tl : List (A ⊕ C)) :
    relabel eA eC (Equiv.refl (ℕ × ℕ)) (gridTail ls tl)
      = gridTail (ls.map (List.map (Sum.map eA eC))) (tl.map (Sum.map eA eC)) := by
  have happ : (ls ++ [tl]).map (List.map (Sum.map eA eC))
      = ls.map (List.map (Sum.map eA eC)) ++ [tl.map (Sum.map eA eC)] := by simp
  have hgrid := relabel_grid eA eC hdef (ls ++ [tl])
  rw [happ] at hgrid
  refine ext' ?_ ?_ ?_
  · have : (relabel eA eC (Equiv.refl (ℕ × ℕ)) (gridTail ls tl)).T
        = (relabel eA eC (Equiv.refl (ℕ × ℕ)) (grid (ls ++ [tl]))).T := rfl
    rw [this, hgrid]
    rfl
  · funext p q
    show (gridTail ls tl).ord p q = _
    have hT : ∀ r : ℕ × ℕ, (r ∈ (grid (ls ++ [tl])).T) =
        (r ∈ (grid (ls.map (List.map (Sum.map eA eC)) ++
          [tl.map (Sum.map eA eC)])).T) := by
      intro r
      rw [← hgrid]
      simp only [relabel_T, Equiv.coe_refl, Finset.image_id]
    have hord : (grid (ls ++ [tl])).ord p q =
        (grid (ls.map (List.map (Sum.map eA eC)) ++ [tl.map (Sum.map eA eC)])).ord p q := by
      rw [← hgrid]; rfl
    simp only [gridTail, hord, hT, List.length_map]
  · funext p
    show Sum.map eA eC ((grid (ls ++ [tl])).α p) = _
    have : (relabel eA eC (Equiv.refl (ℕ × ℕ)) (grid (ls ++ [tl]))).α p
        = Sum.map eA eC ((grid (ls ++ [tl])).α p) := rfl
    rw [← this, hgrid]
    rfl

end TaskNetwork

open TaskNetwork

/-- **The image of a method whose body is a grid.** -/
lemma Method.relabel_grid [Inhabited A] [Inhabited A'] (eA : A → A') (eC : C → C')
    (hdef : eA default = default) (c : C) (ls : List (List (A ⊕ C))) :
    Method.relabel eA eC (Equiv.refl (ℕ × ℕ)) ⟨c, grid ls⟩
      = ⟨eC c, grid (ls.map (List.map (Sum.map eA eC)))⟩ := by
  simp [Method.relabel, TaskNetwork.relabel_grid eA eC hdef]

end HTN
