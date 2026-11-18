import HtnComplexity.Guard.TaskExt
import HtnPlanning.Core.Construction
/-!
# The guarded body is a grid

`HTN.GuardTask.guardMethod` adds one isolated primitive subtask to a method body:
`addTask (grid ls) k (gact m)`.  Every body of the constructions of this development is a grid
(`HTN.TaskNetwork.grid`), and a grid with one extra *unordered* task is the grid with one extra
row — but only **up to isomorphism**, because the fresh identifier the guard uses need not be the
one the grid of `ls ++ [[a]]` gives that row.

> `HTN.GuardTask.iso_addTask_grid` — for a fresh identifier `(k, 0)`, the guarded body
> `addTask (grid ls) (k, 0) a` is isomorphic to `grid (ls ++ [[Sum.inl a]])`.

That is exactly the relation under which `HTN.Syn.Rendering`
(`HtnComplexity/Computable/Render.lean`) compares a listed body with a method of the
problem, so a description of a guarded construction may list the guarded bodies as grids.
-/

namespace HTN

namespace GuardTask

open TaskNetwork

variable {A C : Type} [Inhabited A]

omit [Inhabited A] in
/-- The extended list has the guard row at the index just past the rows of `ls`. -/
private lemma getD_append_self (ls : List (List (A ⊕ C))) (a : A) :
    (ls ++ [[Sum.inl a]]).getD ls.length [] = [Sum.inl a] := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

omit [Inhabited A] in
/-- Below that index the extended list has the rows of `ls`. -/
private lemma getD_append_lt {ls : List (List (A ⊕ C))} {a : A} {i : ℕ} (hi : i < ls.length) :
    (ls ++ [[Sum.inl a]]).getD i [] = ls.getD i [] := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

omit [Inhabited A] in
/-- The identifier map of the isomorphism: the guard cell goes to the cell of the extra row,
every other identifier stays where it is. -/
private def gmap (ls : List (List (A ⊕ C))) (k : ℕ) : ℕ × ℕ → ℕ × ℕ :=
  fun p => if p = (k, 0) then (ls.length, 0) else p

omit [Inhabited A] in
private lemma gmap_self (ls : List (List (A ⊕ C))) (k : ℕ) :
    gmap ls k (k, 0) = (ls.length, 0) := if_pos rfl

omit [Inhabited A] in
private lemma gmap_of_ne {ls : List (List (A ⊕ C))} {k : ℕ} {p : ℕ × ℕ} (h : p ≠ (k, 0)) :
    gmap ls k p = p := if_neg h

/-- **The guarded body is the grid with one extra row**, up to isomorphism. -/
theorem iso_addTask_grid (ls : List (List (A ⊕ C))) (k : ℕ) (a : A)
    (hk : (k, 0) ∉ (grid ls).T) :
    (addTask (grid ls) (k, 0) a).Iso (grid (ls ++ [[Sum.inl a]])) := by
  classical
  have hnew : ((ls.length, 0) : ℕ × ℕ) ∉ (grid ls).T := by
    simp only [mem_grid_T, not_and]
    intro h
    exact absurd h (by omega)
  have hrow : ∀ p ∈ (grid ls).T, (ls ++ [[Sum.inl a]]).getD p.1 [] = ls.getD p.1 [] := by
    intro p hp
    rw [mem_grid_T] at hp
    exact getD_append_lt hp.1
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
    rw [← getD_append_lt (a := a) hlt]
    exact hp.2
  have hguard : ((ls.length, 0) : ℕ × ℕ) ∈ (grid (ls ++ [[Sum.inl a]])).T := by
    rw [mem_grid_T]
    refine ⟨by simp, ?_⟩
    rw [getD_append_self]
    simp
  -- no old cell is ordered with respect to the guard cell
  have hfalse_left : ∀ y : ℕ × ℕ, ¬ (grid ls).ord (k, 0) y := by
    intro y hy
    obtain ⟨-, h2, h3⟩ := hy
    simp only at h2 h3
    have hlen : 0 < (ls.getD k []).length := by omega
    have hk' : k < ls.length := by
      by_contra hcon
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hcon)] at hlen
      simp at hlen
    exact hk (mem_grid_T.2 ⟨hk', by simpa using hlen⟩)
  have hfalse_right : ∀ x : ℕ × ℕ, ¬ (grid ls).ord x (k, 0) := by
    intro x hx
    obtain ⟨-, h2, -⟩ := hx
    simp only at h2
    omega
  refine ⟨gmap ls k, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- the map sends identifiers to identifiers
    intro p hp
    simp only [addTask_T, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hp
    rcases hp with rfl | hp
    · rw [gmap_self]
      exact hguard
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      rw [gmap_of_ne hne]
      exact hmemnew p hp
  · -- it is injective there
    intro p hp q hq hpq
    simp only [addTask_T, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · have hne : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      rw [gmap_self, gmap_of_ne hne] at hpq
      exact absurd (hpq ▸ hq) hnew
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      rw [gmap_of_ne hne, gmap_self] at hpq
      exact absurd (hpq ▸ hp) hnew
    · have hnep : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      have hneq : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      rwa [gmap_of_ne hnep, gmap_of_ne hneq] at hpq
  · -- and onto
    intro q hq
    have hq' : q ∈ (grid (ls ++ [[Sum.inl a]])).T := hq
    by_cases hql : q.1 < ls.length
    · have hqT : q ∈ (grid ls).T := hmemold q hq' hql
      have hne : q ≠ (k, 0) := fun h => hk (h ▸ hqT)
      refine ⟨q, ?_, ?_⟩
      · simp only [addTask_T, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
        exact Or.inr hqT
      · exact gmap_of_ne hne
    · rw [mem_grid_T] at hq'
      have hq1 : q.1 = ls.length := by
        have h := hq'.1
        simp only [List.length_append, List.length_singleton] at h
        omega
      have hq2 : q.2 = 0 := by
        have h := hq'.2
        rw [hq1, getD_append_self] at h
        simpa using h
      refine ⟨(k, 0), by simp, ?_⟩
      rw [gmap_self]
      exact Prod.ext hq1.symm hq2.symm
  · -- the ordering
    intro p hp q hq
    simp only [addTask_T, Finset.mem_insert] at hp hq
    have hord : (addTask (grid ls) (k, 0) a).ord = (grid ls).ord := rfl
    rw [hord]
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · constructor
      · intro h
        exact absurd h (hfalse_left _)
      · intro h
        rw [gmap_self] at h
        obtain ⟨-, h2, -⟩ := h
        simp only at h2
        omega
    · have hne : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      constructor
      · intro h
        exact absurd h (hfalse_left _)
      · intro h
        rw [gmap_self, gmap_of_ne hne] at h
        obtain ⟨h1, -, -⟩ := h
        rw [mem_grid_T] at hq
        simp only at h1
        omega
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      constructor
      · intro h
        exact absurd h (hfalse_right _)
      · intro h
        rw [gmap_of_ne hne, gmap_self] at h
        obtain ⟨h1, -, -⟩ := h
        rw [mem_grid_T] at hp
        simp only at h1
        omega
    · have hnep : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      have hneq : q ≠ (k, 0) := fun h => hk (h ▸ hq)
      rw [gmap_of_ne hnep, gmap_of_ne hneq]
      simp only [grid_ord]
      rw [hrow p hp]
  · -- the labels
    intro p hp
    simp only [addTask_T, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · rw [gmap_self, addTask_α_self]
      show (Sum.inl a : A ⊕ C) = ((ls ++ [[Sum.inl a]]).getD ls.length []).getD 0 (Sum.inl default)
      rw [getD_append_self]
      rfl
    · have hne : p ≠ (k, 0) := fun h => hk (h ▸ hp)
      rw [gmap_of_ne hne, addTask_α_of_ne _ _ hne]
      show (ls.getD p.1 []).getD p.2 (Sum.inl default) =
        ((ls ++ [[Sum.inl a]]).getD p.1 []).getD p.2 (Sum.inl default)
      rw [hrow p hp]

end GuardTask

end HTN
