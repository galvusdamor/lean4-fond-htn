import HtnComplexity.Computable.TailDesc
import HtnComplexity.Guard.GuardGrid
/-!
# The guarded body is a shape

`HTN.GuardTask.guardMethod` adds one isolated primitive subtask to a method body:
`addTask m.subtasks k (gact m)`.  `HtnComplexity/Guard/GuardGrid.lean` shows that a guarded
*grid* is the grid with one extra row, up to isomorphism.  The construction of Theorem 4.3.7 has
one body that is not a grid — the body of its fresh initial task, three parallel chains followed
by the task `done` — so what is needed is the same statement for the shapes of
`HtnComplexity/Computable/TailDesc.lean`:

> `HTN.GuardTask.iso_addTask_gridAfter` — for a fresh identifier `(k, 0)` and a row index
> `m < ls.length`, the guarded body `addTask (gridAfter ls m) (k, 0) a` is isomorphic to
> `gridAfter (ls ++ [[Sum.inl a]]) m`: the guard becomes one more free row, and the row `m`
> still follows exactly the rows before it.

`HTN.Syn.Shape.iso_addTask` states it in the language of shapes, covering the grid
(`after = 0`) through the theorem of `GuardGrid.lean`.  That is the relation under which
`HTN.Syn.Rendering` compares a listed body with a method of the problem, so a description of a
guarded construction may list the guarded bodies as shapes.
-/

namespace HTN

namespace GuardTask

open TaskNetwork

variable {A C : Type} [Inhabited A]

omit [Inhabited A] in
/-- The extended list has the guard row at the index just past the rows of `ls`. -/
private lemma getD_self (ls : List (List (A ⊕ C))) (a : A) :
    (ls ++ [[Sum.inl a]]).getD ls.length [] = [Sum.inl a] := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

omit [Inhabited A] in
/-- Below that index the extended list has the rows of `ls`. -/
private lemma getD_lt {ls : List (List (A ⊕ C))} {a : A} {i : ℕ} (hi : i < ls.length) :
    (ls ++ [[Sum.inl a]]).getD i [] = ls.getD i [] := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

omit [Inhabited A] in
/-- The identifier map: the guard cell goes to the cell of the extra row, every other
identifier stays where it is. -/
private def smap (ls : List (List (A ⊕ C))) (k : ℕ) : ℕ × ℕ → ℕ × ℕ :=
  fun p => if p = (k, 0) then (ls.length, 0) else p

omit [Inhabited A] in
private lemma smap_self (ls : List (List (A ⊕ C))) (k : ℕ) :
    smap ls k (k, 0) = (ls.length, 0) := if_pos rfl

omit [Inhabited A] in
private lemma smap_of_ne {ls : List (List (A ⊕ C))} {k : ℕ} {p : ℕ × ℕ} (h : p ≠ (k, 0)) :
    smap ls k p = p := if_neg h

/-- **The guarded body of a shape is the shape with one extra free row**, up to isomorphism. -/
theorem iso_addTask_gridAfter (ls : List (List (A ⊕ C))) (k m : ℕ) (a : A)
    (hk : (k, 0) ∉ (grid ls).T) (hm : m < ls.length) :
    (addTask (gridAfter ls m) (k, 0) a).Iso (gridAfter (ls ++ [[Sum.inl a]]) m) := by
  classical
  have hnew : ((ls.length, 0) : ℕ × ℕ) ∉ (grid ls).T := by
    simp only [mem_grid_T, not_and]
    intro h
    exact absurd h (by omega)
  have hrow : ∀ p ∈ (grid ls).T, (ls ++ [[Sum.inl a]]).getD p.1 [] = ls.getD p.1 [] := by
    intro p hp
    rw [mem_grid_T] at hp
    exact getD_lt hp.1
  have hmemnew : ∀ p ∈ (grid ls).T, p ∈ (grid (ls ++ [[Sum.inl a]])).T := by
    intro p hp
    have hp' := hp
    rw [mem_grid_T] at hp' ⊢
    refine ⟨by simp; omega, ?_⟩
    rw [hrow p hp]
    exact hp'.2
  have hmemold : ∀ p ∈ (grid (ls ++ [[Sum.inl a]])).T, p.1 < ls.length → p ∈ (grid ls).T := by
    intro p hp hlt
    rw [mem_grid_T] at hp ⊢
    refine ⟨hlt, ?_⟩
    rw [← getD_lt (a := a) hlt]
    exact hp.2
  have hguard : ((ls.length, 0) : ℕ × ℕ) ∈ (grid (ls ++ [[Sum.inl a]])).T := by
    rw [mem_grid_T]
    refine ⟨by simp, ?_⟩
    rw [getD_self]
    simp
  -- no old cell is ordered with respect to the guard cell
  have hfalse_left : ∀ y : ℕ × ℕ, ¬ (gridAfter ls m).ord (k, 0) y := by
    rintro y (hy | ⟨-, -, hy, -⟩)
    · obtain ⟨-, h2, h3⟩ := hy
      simp only at h2 h3
      have hlen : 0 < (ls.getD k []).length := by omega
      have hk' : k < ls.length := by
        by_contra hcon
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hcon)] at hlen
        simp at hlen
      exact hk (mem_grid_T.2 ⟨hk', by simpa using hlen⟩)
    · exact hk hy
  have hfalse_right : ∀ x : ℕ × ℕ, ¬ (gridAfter ls m).ord x (k, 0) := by
    rintro x (hx | ⟨-, -, -, hx⟩)
    · obtain ⟨-, h2, -⟩ := hx
      simp only at h2
      omega
    · exact hk hx
  refine ⟨smap ls k, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- the map sends identifiers to identifiers
    intro p hp
    simp only [gridAfter_T, addTask_T, Finset.coe_insert, Set.mem_insert_iff,
      Finset.mem_coe] at hp
    rcases hp with rfl | hp
    · rw [smap_self]
      exact hguard
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      rw [smap_of_ne hne]
      exact hmemnew p hp
  · -- it is injective there
    intro p hp q hq hpq
    simp only [gridAfter_T, addTask_T, Finset.coe_insert, Set.mem_insert_iff,
      Finset.mem_coe] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · have hne : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      rw [smap_self, smap_of_ne hne] at hpq
      exact absurd (hpq ▸ hq) hnew
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      rw [smap_of_ne hne, smap_self] at hpq
      exact absurd (hpq ▸ hp) hnew
    · have hnep : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      have hneq : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      rwa [smap_of_ne hnep, smap_of_ne hneq] at hpq
  · -- and onto
    intro q hq
    have hq' : q ∈ (grid (ls ++ [[Sum.inl a]])).T := hq
    by_cases hql : q.1 < ls.length
    · have hqT : q ∈ (grid ls).T := hmemold q hq' hql
      have hne : q ≠ (k, 0) := fun h => hk (h ▸ hqT)
      refine ⟨q, ?_, ?_⟩
      · simp only [gridAfter_T, addTask_T, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
        exact Or.inr hqT
      · exact smap_of_ne hne
    · rw [mem_grid_T] at hq'
      have hq1 : q.1 = ls.length := by
        have h := hq'.1
        simp only [List.length_append, List.length_singleton] at h
        omega
      have hq2 : q.2 = 0 := by
        have h := hq'.2
        rw [hq1, getD_self] at h
        simpa using h
      refine ⟨(k, 0), by simp, ?_⟩
      rw [smap_self]
      exact Prod.ext hq1.symm hq2.symm
  · -- the ordering
    intro p hp q hq
    simp only [gridAfter_T, addTask_T, Finset.mem_insert] at hp hq
    have hord : (addTask (gridAfter ls m) (k, 0) a).ord = (gridAfter ls m).ord := rfl
    rw [hord]
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · constructor
      · intro h
        exact absurd h (hfalse_left _)
      · intro h
        rw [smap_self] at h
        rcases h with ⟨-, h2, -⟩ | ⟨h1, -, -, -⟩ <;> simp only at * <;> omega
    · have hne : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      constructor
      · intro h
        exact absurd h (hfalse_left _)
      · intro h
        rw [smap_self, smap_of_ne hne] at h
        rw [mem_grid_T] at hq
        rcases h with ⟨h1, -, -⟩ | ⟨h1, -, -, -⟩ <;> simp only at h1 <;> omega
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      constructor
      · intro h
        exact absurd h (hfalse_right _)
      · intro h
        rw [smap_of_ne hne, smap_self] at h
        rw [mem_grid_T] at hp
        rcases h with ⟨h1, -, -⟩ | ⟨-, h2, -, -⟩ <;> simp only at * <;> omega
    · have hnep : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      have hneq : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      rw [smap_of_ne hnep, smap_of_ne hneq]
      simp only [gridAfter_ord, grid_ord]
      rw [hrow p hp]
      constructor
      · rintro (h | ⟨h1, h2, -, -⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, hmemnew p hp, hmemnew q hq⟩
      · rintro (h | ⟨h1, h2, -, -⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, hp, hq⟩
  · -- the labels
    intro p hp
    simp only [gridAfter_T, addTask_T, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · rw [smap_self, gridAfter_α, addTask_α_self]
      show (Sum.inl a : A ⊕ C) = ((ls ++ [[Sum.inl a]]).getD ls.length []).getD 0 (Sum.inl default)
      rw [getD_self]
      rfl
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      rw [smap_of_ne hne, gridAfter_α, addTask_α_of_ne _ _ hne]
      show (ls.getD p.1 []).getD p.2 (Sum.inl default) =
        ((ls ++ [[Sum.inl a]]).getD p.1 []).getD p.2 (Sum.inl default)
      rw [hrow p hp]

end GuardTask

namespace Syn

namespace Shape

open TaskNetwork

variable {A C : Type} [Inhabited A]

/-- **The guarded body of a shape is the shape with one extra free row**, up to isomorphism.
The row that follows the others is either the first one — in which case there is none and the
shape is a grid — or a row of the shape, which the extra row leaves where it is. -/
theorem iso_addTask (s : Shape A C) (k : ℕ) (a : A) (hk : (k, 0) ∉ s.net.T)
    (hm : s.after = 0 ∨ s.after < s.rows.length) :
    (GuardTask.addTask s.net (k, 0) a).Iso (Shape.mk (s.rows ++ [[Sum.inl a]]) s.after).net := by
  obtain ⟨ls, m⟩ := s
  rcases hm with rfl | hm
  · rw [net_zero] at hk ⊢
    rw [show (Shape.mk (ls ++ [[Sum.inl a]]) 0).net = TaskNetwork.grid (ls ++ [[Sum.inl a]]) from
      net_zero _]
    exact GuardTask.iso_addTask_grid ls k a hk
  · exact GuardTask.iso_addTask_gridAfter ls k m a hk hm

end Shape

end Syn

end HTN
