import HtnComplexity.Computable.GridDesc
import HtnComplexity.Article.PlanEx
/-!
# Grid descriptions with the full ordering

A well-formed description in the sense of the article (`HTN.Article.TnValid`) lists the strict
partial order `≺` itself, not a generating set.  `HTN.Syn.gridDesc` lists only the consecutive
pairs of each row; `HTN.Article.gridDescFull` lists all pairs of a row in order.  Both denote the
same task network (`HTN.Article.toTaskNetwork_gridDescFull`), so everything proved about
`gridDesc` transfers, and the full one is well formed (`HTN.Article.tnValid_gridDescFull`).
-/

namespace HTN

namespace Article

open Syn

variable {ls : List (List (Bool × ℕ))}

/-- All ordering pairs of a described grid: `(i, j) ≺ (i, j')` for `j < j'` in each row. -/
def cellOrdFull (ls : List (List (Bool × ℕ))) : List (ℕ × ℕ) :=
  (List.range ls.length).flatMap fun i =>
    (List.range (gridRow ls i).length).flatMap fun j =>
      (List.range ((gridRow ls i).length - j - 1)).map fun d =>
        (Nat.pair i j, Nat.pair i (j + d + 1))

/-- **The description of a grid with the full ordering.** -/
def gridDescFull (ls : List (List (Bool × ℕ))) : TnDesc := (cellIds ls, cellOrdFull ls, cellLbl ls)

/-- The description of the grid `ls` of task names, with the full ordering. -/
def gridDescFullOf {A C : Type} (eA : A → ℕ) (eC : C → ℕ) (ls : List (List (A ⊕ C))) : TnDesc :=
  gridDescFull (ls.map fun row => row.map (encLabel eA eC))

theorem mem_cellOrdFull {p : ℕ × ℕ} :
    p ∈ cellOrdFull ls ↔ ∃ i j j', i < ls.length ∧ j < j' ∧ j' < (gridRow ls i).length ∧
      p = (Nat.pair i j, Nat.pair i j') := by
  simp only [cellOrdFull, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, d, hd, rfl⟩
    exact ⟨i, j, j + d + 1, hi, by omega, by omega, rfl⟩
  · rintro ⟨i, j, j', hi, hjj, hj', rfl⟩
    exact ⟨i, hi, j, by omega, j' - j - 1, by omega, by rw [show j + (j' - j - 1) + 1 = j' by omega]⟩

theorem preOrd_gridDescFull {x y : ℕ} :
    (gridDescFull ls).preOrd x y ↔ (gridDesc ls).preOrd x y := by
  rw [preOrd_cell]
  constructor
  · intro h
    induction h with
    | single h =>
      obtain ⟨i, j, j', hi, hjj, hj', hp⟩ := mem_cellOrdFull.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      exact ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩
    | tail _ h ih =>
      obtain ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩ := ih
      obtain ⟨i₂, j₂, j₃, hi₂, hjj₂, hj₃, hp⟩ := mem_cellOrdFull.1 h
      obtain ⟨h1, rfl⟩ := Prod.mk.inj hp
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h1
      exact ⟨i, j, j₃, hi, by omega, hj₃, rfl, rfl⟩
  · rintro ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩
    exact Relation.TransGen.single (mem_cellOrdFull.2 ⟨i, j, j', hi, hjj, hj', rfl⟩)

/-- **The full description denotes the same task network as `gridDesc`.** -/
theorem toTaskNetwork_gridDescFull : (gridDescFull ls).toTaskNetwork = (gridDesc ls).toTaskNetwork := by
  refine TaskNetwork.ext' rfl ?_ rfl
  funext x y
  apply propext
  show (gridDescFull ls).ordOf x y ↔ (gridDesc ls).ordOf x y
  unfold TnDesc.ordOf
  rw [preOrd_gridDescFull, preOrd_gridDescFull]
  rfl

theorem toTaskNetwork_gridDescFullOf {A C : Type} (eA : A → ℕ) (eC : C → ℕ)
    (ls : List (List (A ⊕ C))) :
    (gridDescFullOf eA eC ls).toTaskNetwork = (gridDescOf eA eC ls).toTaskNetwork :=
  toTaskNetwork_gridDescFull

/-- **The full grid description is well formed**, provided its primitive labels are accepted. -/
theorem tnValid_gridDescFull {prim : ℕ → Prop}
    (hprim : ∀ row ∈ ls, ∀ n, (false, n) ∈ row → prim n) : TnValid prim (gridDescFull ls) where
  nodup := nodup_cellIds
  ord_mem := by
    intro q hq
    obtain ⟨i, j, j', hi, hjj, hj', rfl⟩ := mem_cellOrdFull.1 hq
    exact ⟨mem_cellIds.2 ⟨i, j, hi, by omega, rfl⟩, mem_cellIds.2 ⟨i, j', hi, hj', rfl⟩⟩
  irrefl := by
    intro a ha
    obtain ⟨i, j, j', -, hjj, -, hp⟩ := mem_cellOrdFull.1 ha
    obtain ⟨h1, h2⟩ := Prod.mk.inj hp
    have := (Nat.pair_eq_pair.1 (h1.symm.trans h2)).2
    omega
  trans := by
    intro a b c hab hbc
    obtain ⟨i, j, j', hi, hjj, hj', hp⟩ := mem_cellOrdFull.1 hab
    obtain ⟨i₂, j₂, j₃, -, hjj₂, hj₃, hp₂⟩ := mem_cellOrdFull.1 hbc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    obtain ⟨h1, rfl⟩ := Prod.mk.inj hp₂
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h1
    exact mem_cellOrdFull.2 ⟨i, j, j₃, hi, by omega, hj₃, rfl⟩
  lbl_perm := by
    show ((cellLbl ls).map Prod.fst).Perm (cellIds ls)
    rw [map_fst_cellLbl]
  prim_ok := by
    intro q hq hq'
    simp only [gridDescFull, TnDesc.lbl, cellLbl, List.mem_flatMap, List.mem_map,
      List.mem_range] at hq
    obtain ⟨i, hi, j, hj, rfl⟩ := hq
    simp only at hq' ⊢
    have hmem : (gridRow ls i).getD j (false, 0) ∈ gridRow ls i := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have hrow : gridRow ls i ∈ ls := by
      unfold gridRow; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    generalize hx : (gridRow ls i).getD j (false, 0) = x at hq' hmem
    obtain ⟨b, n⟩ := x
    simp only at hq'
    subst hq'
    exact hprim _ hrow n hmem

end Article

end HTN
