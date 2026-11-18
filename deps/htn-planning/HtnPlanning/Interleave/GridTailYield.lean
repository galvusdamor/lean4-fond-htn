import HtnPlanning.Interleave.GridYield
/-!
# Refinements of a grid with a tail

`HTN.TaskNetwork.gridTail ls tl` is the task network of the parallel chains `ls`, all of them
ordered before the chain `tl`; it is the shape of the initial task network of the
Turing-machine encoding (the three chains of `HTN.TMEnc.initChains`, all ordered before the
task `done`).  It is *not* a grid, so `HTN.Domain.netYield_grid_iff` does not apply to it.

This file supplies the missing rule:

* `HTN.TaskNetwork.rowNet n tl` — the chain `tl` placed on the row `n`, and its isomorphism
  with `HTN.TaskNetwork.seq tl`;
* `HTN.TaskNetwork.isSeries_gridTail` — `gridTail ls tl` is the sequential composition of the
  grid `ls` and of that chain;
* `HTN.Domain.netYield_gridTail_iff` — **a refinement of `gridTail ls tl` is a refinement of
  the grid followed by a refinement of the tail**.
-/

namespace HTN

namespace TaskNetwork

universe v w

variable {A : Type v} {C : Type w} [Inhabited A]

/-! ### A chain placed on a row -/

/-- The chain `tl` placed on the row `n` of the grid. -/
def rowNet (n : ℕ) (tl : List (A ⊕ C)) : TaskNetwork (ℕ × ℕ) A C where
  T := (Finset.range tl.length).image fun j => (n, j)
  ord := fun p q => p.1 = n ∧ q.1 = n ∧ p.2 < q.2 ∧ q.2 < tl.length
  α := fun p => tl.getD p.2 (Sum.inl default)

variable {n : ℕ} {tl : List (A ⊕ C)} {p q : ℕ × ℕ}

@[simp] lemma mem_rowNet_T : p ∈ (rowNet n tl).T ↔ p.1 = n ∧ p.2 < tl.length := by
  obtain ⟨i, j⟩ := p
  simp only [rowNet, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, hj⟩
    exact ⟨j, hj, rfl, rfl⟩

@[simp] lemma rowNet_ord :
    (rowNet n tl).ord p q ↔ p.1 = n ∧ q.1 = n ∧ p.2 < q.2 ∧ q.2 < tl.length := Iff.rfl

@[simp] lemma rowNet_α : (rowNet n tl).α p = tl.getD p.2 (Sum.inl default) := rfl

lemma rowNet_wf : (rowNet n tl : TaskNetwork (ℕ × ℕ) A C).WF where
  irrefl := by rintro ⟨i, j⟩ ⟨-, -, h, -⟩; exact absurd h (lt_irrefl _)
  trans := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨i'', j''⟩ ⟨rfl, rfl, h1, -⟩ ⟨-, rfl, h2, h3⟩
    exact ⟨rfl, rfl, h1.trans h2, h3⟩
  mem_left := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨rfl, rfl, h1, h2⟩
    simpa using by omega
  mem_right := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨rfl, rfl, h1, h2⟩
    simpa using h2

/-- A chain placed on a row is a renaming of the chain. -/
lemma rowNet_iso : (rowNet n tl : TaskNetwork (ℕ × ℕ) A C).Iso (seq tl) := by
  refine ⟨fun p => (0, p.2), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_coe, mem_rowNet_T] at hp
    simpa using hp.2
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' heq
    simp only [Finset.mem_coe, mem_rowNet_T] at hp hp'
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_coe, mem_seq_T] at hp
    obtain ⟨rfl, hj⟩ := hp
    exact ⟨(n, j), by simp [hj], by simp⟩
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp'
    simp only [mem_rowNet_T] at hp hp'
    obtain ⟨rfl, hj⟩ := hp
    obtain ⟨rfl, hj'⟩ := hp'
    simp only [rowNet_ord, seq, grid_ord, List.getD_cons_zero, true_and]
  · rintro ⟨i, j⟩ hp
    simp [seq]

/-! ### The tail of a grid -/

omit [Inhabited A] in
lemma getD_append_singleton_lt {ls : List (List (A ⊕ C))} {i : ℕ} (h : i < ls.length) :
    (ls ++ [tl]).getD i [] = ls.getD i [] := by
  simp [List.getD, List.getElem?_append_left h]

omit [Inhabited A] in
lemma getD_append_singleton_eq {ls : List (List (A ⊕ C))} :
    (ls ++ [tl]).getD ls.length [] = tl := by
  simp [List.getD]

omit [Inhabited A] in
lemma getD_append_singleton_gt {ls : List (List (A ⊕ C))} {i : ℕ} (h : ls.length < i) :
    (ls ++ [tl]).getD i ([] : List (A ⊕ C)) = [] := by
  simp [List.getD, h]

/-- The tasks of a grid with one extra chain. -/
lemma mem_grid_append_T {ls : List (List (A ⊕ C))} {tl : List (A ⊕ C)} {p : ℕ × ℕ} :
    p ∈ (grid (ls ++ [tl])).T ↔
      (p.1 < ls.length ∧ p.2 < (ls.getD p.1 []).length) ∨ (p.1 = ls.length ∧ p.2 < tl.length) := by
  rw [mem_grid_T]
  simp only [List.length_append, List.length_singleton]
  rcases lt_trichotomy p.1 ls.length with h | h | h
  · rw [getD_append_singleton_lt h]; omega
  · rw [h, getD_append_singleton_eq]; omega
  · rw [getD_append_singleton_gt h]; simp only [List.length_nil]; omega

/-- The ordering of a grid with one extra chain. -/
lemma grid_append_ord {ls : List (List (A ⊕ C))} {tl : List (A ⊕ C)} {p q : ℕ × ℕ} :
    (grid (ls ++ [tl])).ord p q ↔ p.1 = q.1 ∧ p.2 < q.2 ∧
      ((p.1 < ls.length ∧ q.2 < (ls.getD p.1 []).length) ∨
        (p.1 = ls.length ∧ q.2 < tl.length)) := by
  rw [grid_ord]
  rcases lt_trichotomy p.1 ls.length with h | h | h
  · rw [getD_append_singleton_lt h]; omega
  · rw [h, getD_append_singleton_eq]; omega
  · rw [getD_append_singleton_gt h]; simp only [List.length_nil]; omega

/-- **A grid with a tail is the sequential composition of the grid and of the tail.** -/
lemma isSeries_gridTail (ls : List (List (A ⊕ C))) (tl : List (A ⊕ C)) :
    IsSeries (gridTail ls tl) (grid ls) (rowNet ls.length tl) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [mem_grid_T, mem_rowNet_T] at h1 h2
    omega
  · intro t
    rw [gridTail_T, mem_grid_append_T, mem_grid_T, mem_rowNet_T]
  · intro t ht
    rw [mem_grid_T] at ht
    simp only [gridTail_α, grid_α]
    rw [getD_append_singleton_lt ht.1]
  · intro t ht
    rw [mem_rowNet_T] at ht
    simp only [gridTail_α, grid_α, rowNet_α]
    rw [ht.1, getD_append_singleton_eq]
  · intro a b
    show ((grid (ls ++ [tl])).ord a b ∨
      (a.1 < ls.length ∧ b.1 = ls.length ∧ a ∈ (grid (ls ++ [tl])).T ∧
        b ∈ (grid (ls ++ [tl])).T)) ↔ _
    rw [grid_append_ord, mem_grid_append_T, mem_grid_append_T, grid_ord, rowNet_ord,
      mem_grid_T, mem_rowNet_T]
    rcases Nat.lt_or_ge a.1 ls.length with h | h
    · omega
    · rw [List.getD_eq_default _ _ h]
      simp only [List.length_nil]
      omega

end TaskNetwork

namespace Domain

universe u v w

variable {F : Type u} {A : Type v} {C : Type w} [Inhabited A]

/-- **Refinements of a grid with a tail are the refinements of the grid followed by the
refinements of the tail.** -/
theorem netYield_gridTail_iff {D : Domain F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {ls : List (List (A ⊕ C))} {tl : List (A ⊕ C)} {as : List A} :
    D.NetYield (TaskNetwork.gridTail ls tl) as ↔
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ D.GridYield ls as₁ ∧ D.ChainYield tl as₂ := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨n₁, n₂, as₁, as₂, -, rfl, h₁, h₂⟩ :=
      (netYieldN_isSeries_iff (TaskNetwork.isSeries_gridTail ls tl) TaskNetwork.grid_wf
        TaskNetwork.rowNet_wf).1 hn
    refine ⟨as₁, as₂, rfl, (netYield_grid_iff hgrid).1 ⟨n₁, h₁⟩, (netYield_seq_iff hgrid).1 ?_⟩
    exact ⟨n₂, h₂.iso TaskNetwork.rowNet_wf TaskNetwork.grid_wf TaskNetwork.rowNet_iso⟩
  · rintro ⟨as₁, as₂, rfl, h₁, h₂⟩
    obtain ⟨n₁, h₁⟩ := (netYield_grid_iff hgrid).2 h₁
    obtain ⟨n₂, h₂⟩ := (netYield_seq_iff hgrid).2 h₂
    refine ⟨n₁ + n₂, (netYieldN_isSeries_iff (TaskNetwork.isSeries_gridTail ls tl)
      TaskNetwork.grid_wf TaskNetwork.rowNet_wf).2 ⟨n₁, n₂, as₁, as₂, rfl, rfl, h₁, ?_⟩⟩
    exact h₂.iso TaskNetwork.grid_wf TaskNetwork.rowNet_wf TaskNetwork.rowNet_iso.symm

end Domain

end HTN
