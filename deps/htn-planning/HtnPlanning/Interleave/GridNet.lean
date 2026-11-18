import HtnPlanning.Interleave.NetYield
import HtnPlanning.Core.Construction
/-!
# Grids as compositions

The method bodies of the compilations formalised in this project are *grids*
(`HTN.TaskNetwork.grid ls`): parallel compositions of totally ordered chains.  This file
decomposes a grid structurally, so that the results of `HtnPlanning/Interleave/NetYield.lean` can be
applied to it:

* `HTN.TaskNetwork.gridShift ls` — the grid `ls` placed at the chain indices `1, 2, …`; it is
  isomorphic to `grid ls` (`HTN.TaskNetwork.gridShift_iso`) and
  `HTN.TaskNetwork.isPar_grid_cons` shows that `grid (l :: ls)` is the parallel composition of
  the chain `l` and of `gridShift ls`;
* `HTN.TaskNetwork.seqShift xs` — the chain `xs` placed at the positions `1, 2, …` of chain `0`;
  it is isomorphic to `seq xs` (`HTN.TaskNetwork.seqShift_iso`) and
  `HTN.TaskNetwork.isSeries_seq_cons` shows that `seq (x :: xs)` is the sequential composition
  of the single task `x` and of `seqShift xs`;
* `HTN.TaskNetwork.isSingle_seq_singleton` — a one-element chain is a one-task network;
* `HTN.TaskNetwork.grid_nil_T`, `HTN.TaskNetwork.seq_nil_T` — the empty grid and the empty chain
  have no tasks.
-/

namespace HTN

namespace TaskNetwork

universe v w

variable {A : Type v} {C : Type w} [Inhabited A]

/-! ### The tail of a grid -/

/-- The grid `ls` placed at the chain indices `1, 2, …`: the tasks of `grid (l :: ls)` that do
not belong to the first chain. -/
def gridShift (ls : List (List (A ⊕ C))) : TaskNetwork (ℕ × ℕ) A C where
  T := (Finset.range ls.length).biUnion
    fun i => (Finset.range (ls.getD i []).length).image fun j => (i + 1, j)
  ord := fun p q => 1 ≤ p.1 ∧ p.1 = q.1 ∧ p.2 < q.2 ∧ q.2 < (ls.getD (p.1 - 1) []).length
  α := fun p => (ls.getD (p.1 - 1) []).getD p.2 (Sum.inl default)

variable {ls : List (List (A ⊕ C))} {p : ℕ × ℕ}

@[simp] lemma mem_gridShift_T :
    p ∈ (gridShift ls).T ↔ 1 ≤ p.1 ∧ p.1 - 1 < ls.length ∧ p.2 < (ls.getD (p.1 - 1) []).length := by
  obtain ⟨i, j⟩ := p
  simp only [gridShift, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨by omega, by simpa using ha, by simpa using hb⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨i - 1, h2, j, h3, by omega, rfl⟩

@[simp] lemma gridShift_ord {q : ℕ × ℕ} :
    (gridShift ls).ord p q ↔
      1 ≤ p.1 ∧ p.1 = q.1 ∧ p.2 < q.2 ∧ q.2 < (ls.getD (p.1 - 1) []).length := Iff.rfl

@[simp] lemma gridShift_α : (gridShift ls).α p = (ls.getD (p.1 - 1) []).getD p.2 (Sum.inl default) :=
  rfl

lemma gridShift_wf : (gridShift ls).WF where
  irrefl := by rintro ⟨i, j⟩ ⟨-, -, h, -⟩; exact absurd h (lt_irrefl _)
  trans := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨i'', j''⟩ ⟨h0, rfl, h1, -⟩ ⟨-, rfl, h2, h3⟩
    exact ⟨h0, rfl, h1.trans h2, h3⟩
  mem_left := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨h0, rfl, h1, h2⟩
    have hj : j < (ls.getD (i - 1) []).length := h1.trans h2
    have : i - 1 < ls.length := by
      by_contra hi
      rw [List.getD_eq_default _ _ (by omega)] at hj
      simp at hj
    simpa using ⟨h0, this, hj⟩
  mem_right := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨h0, rfl, -, h2⟩
    have : i - 1 < ls.length := by
      by_contra hi
      rw [List.getD_eq_default _ _ (by omega)] at h2
      simp at h2
    simpa using ⟨h0, this, h2⟩

/-- The shifted grid is a renaming of the grid. -/
lemma gridShift_iso : (gridShift ls).Iso (grid ls) := by
  refine ⟨fun p => (p.1 - 1, p.2), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_coe, mem_gridShift_T] at hp
    simpa using ⟨hp.2.1, hp.2.2⟩
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' heq
    simp only [Finset.mem_coe, mem_gridShift_T] at hp hp'
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) heq.2
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_coe, mem_grid_T] at hp
    refine ⟨(i + 1, j), ?_, by simp⟩
    simp only [Finset.mem_coe, mem_gridShift_T]
    exact ⟨by omega, by simpa using hp.1, by simpa using hp.2⟩
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp'
    simp only [mem_gridShift_T] at hp hp'
    simp only [gridShift_ord, grid_ord]
    constructor
    · rintro ⟨h0, heq, h1, h2⟩
      exact ⟨by omega, h1, h2⟩
    · rintro ⟨heq, h1, h2⟩
      exact ⟨hp.1, by omega, h1, h2⟩
  · rintro ⟨i, j⟩ hp
    simp [gridShift_α]

/-- **A grid is the parallel composition of its first chain and of the remaining chains.** -/
lemma isPar_grid_cons (l : List (A ⊕ C)) (ls : List (List (A ⊕ C))) :
    IsPar (grid (l :: ls)) (seq l) (gridShift ls) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    rintro ⟨i, j⟩ hp hq
    simp only [mem_seq_T] at hp
    simp only [mem_gridShift_T] at hq
    omega
  · rintro ⟨i, j⟩
    simp only [mem_grid_T, mem_seq_T, mem_gridShift_T]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [List.getD_cons_succ, List.length_cons]
      constructor
      · rintro ⟨h1, h2⟩
        exact Or.inr ⟨by omega, by simpa using ⟨by omega, h2⟩⟩
      · rintro (⟨h1, -⟩ | ⟨-, h2, h3⟩)
        · omega
        · simp only [Nat.add_sub_cancel] at h2 h3
          exact ⟨by omega, h3⟩
  · rintro ⟨i, j⟩ hp
    simp only [mem_seq_T] at hp
    obtain ⟨rfl, hj⟩ := hp
    simp [grid_α, seq]
  · rintro ⟨i, j⟩ hp
    simp only [mem_gridShift_T] at hp
    obtain ⟨h0, h1, h2⟩ := hp
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp [grid_α, gridShift_α]
  · rintro ⟨i, j⟩ ⟨i', j'⟩
    simp only [grid_ord, gridShift_ord, seq, grid_ord]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      constructor
      · rintro ⟨rfl, h1, h2⟩
        refine Or.inr ⟨by omega, rfl, h1, ?_⟩
        simpa using h2
      · rintro (⟨-, -, h3⟩ | ⟨-, rfl, h1, h2⟩)
        · rw [List.getD_eq_default _ _ (by simp)] at h3
          simp at h3
        · exact ⟨rfl, h1, by simpa using h2⟩

/-! ### The tail of a chain -/

/-- The chain `xs` placed at the positions `1, 2, …` of chain `0`. -/
def seqShift (xs : List (A ⊕ C)) : TaskNetwork (ℕ × ℕ) A C where
  T := (Finset.range xs.length).image fun j => (0, j + 1)
  ord := fun p q => p.1 = 0 ∧ q.1 = 0 ∧ 1 ≤ p.2 ∧ p.2 < q.2 ∧ q.2 < xs.length + 1
  α := fun p => xs.getD (p.2 - 1) (Sum.inl default)

variable {xs : List (A ⊕ C)}

@[simp] lemma mem_seqShift_T :
    p ∈ (seqShift xs).T ↔ p.1 = 0 ∧ 1 ≤ p.2 ∧ p.2 - 1 < xs.length := by
  obtain ⟨i, j⟩ := p
  simp only [seqShift, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨rfl, by omega, by simpa using hb⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨j - 1, h2, rfl, by omega⟩

@[simp] lemma seqShift_ord {q : ℕ × ℕ} :
    (seqShift xs).ord p q ↔
      p.1 = 0 ∧ q.1 = 0 ∧ 1 ≤ p.2 ∧ p.2 < q.2 ∧ q.2 < xs.length + 1 := Iff.rfl

@[simp] lemma seqShift_α : (seqShift xs).α p = xs.getD (p.2 - 1) (Sum.inl default) := rfl

lemma seqShift_wf : (seqShift xs).WF where
  irrefl := by rintro ⟨i, j⟩ ⟨-, -, -, h, -⟩; exact absurd h (lt_irrefl _)
  trans := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨i'', j''⟩ ⟨rfl, rfl, h0, h1, -⟩ ⟨-, rfl, -, h2, h3⟩
    exact ⟨rfl, rfl, h0, h1.trans h2, h3⟩
  mem_left := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨rfl, rfl, h0, h1, h2⟩
    simpa using ⟨h0, by omega⟩
  mem_right := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨rfl, rfl, h0, h1, h2⟩
    simpa using ⟨by omega, by omega⟩

/-- The shifted chain is a renaming of the chain. -/
lemma seqShift_iso : (seqShift xs).Iso (seq xs) := by
  refine ⟨fun p => (0, p.2 - 1), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_coe, mem_seqShift_T] at hp
    simpa using hp.2.2
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' heq
    simp only [Finset.mem_coe, mem_seqShift_T] at hp hp'
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_coe, mem_seq_T] at hp
    obtain ⟨rfl, hj⟩ := hp
    refine ⟨(0, j + 1), ?_, by simp⟩
    simp only [Finset.mem_coe, mem_seqShift_T]
    exact ⟨trivial, by omega, by omega⟩
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp'
    simp only [mem_seqShift_T] at hp hp'
    obtain ⟨rfl, hj0, hj⟩ := hp
    obtain ⟨rfl, hj0', hj'⟩ := hp'
    simp only [seqShift_ord, seq, grid_ord, List.getD_cons_zero, true_and]
    omega
  · rintro ⟨i, j⟩ hp
    simp only [mem_seqShift_T] at hp
    obtain ⟨rfl, hj0, hj⟩ := hp
    simp [seq, grid_α, List.getD_eq_getElem?_getD]

/-- A one-element chain is a network with a single task. -/
lemma isSingle_seq_singleton (x : A ⊕ C) : IsSingle (seq [x]) (0, 0) where
  memT := by
    rintro ⟨i, j⟩
    simp only [mem_seq_T, List.length_singleton, Prod.mk.injEq]
    omega
  ord := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    have hlen : ([[x]].getD i []).length ≤ 1 := by cases i <;> simp
    simp only [seq, grid_ord]
    omega

@[simp] lemma seq_singleton_α (x : A ⊕ C) : (seq [x]).α (0, 0) = x := by
  simp [seq, grid_α]

/-- **A chain is the sequential composition of its first task and of the remaining tasks.** -/
lemma isSeries_seq_cons (x : A ⊕ C) (xs : List (A ⊕ C)) :
    IsSeries (seq (x :: xs)) (seq [x]) (seqShift xs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    rintro ⟨i, j⟩ hp hq
    simp only [mem_seq_T, List.length_singleton] at hp
    simp only [mem_seqShift_T] at hq
    omega
  · rintro ⟨i, j⟩
    simp only [mem_seq_T, mem_seqShift_T, List.length_cons, List.length_nil]
    omega
  · rintro ⟨i, j⟩ hp
    simp only [mem_seq_T, List.length_singleton] at hp
    obtain ⟨rfl, hj⟩ := hp
    have : j = 0 := by omega
    subst this
    simp [seq, grid_α]
  · rintro ⟨i, j⟩ hp
    simp only [mem_seqShift_T] at hp
    obtain ⟨rfl, hj0, hj⟩ := hp
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp [seq, grid_α, seqShift_α]
  · rintro ⟨i, j⟩ ⟨i', j'⟩
    rcases i with _ | i
    · simp only [seq, grid_ord, seqShift_ord, mem_grid_T, mem_seqShift_T, List.getD_cons_zero,
        List.length_cons, List.length_nil, true_and]
      omega
    · have h1 : ([x :: xs].getD (i + 1) ([] : List (A ⊕ C))).length = 0 := by
        rw [List.getD_eq_default _ _ (by simp)]
        simp
      have h2 : ([[x]].getD (i + 1) ([] : List (A ⊕ C))).length = 0 := by
        rw [List.getD_eq_default _ _ (by simp)]
        simp
      simp only [seq, grid_ord, seqShift_ord, mem_grid_T, mem_seqShift_T, h1, h2,
        List.length_cons, List.length_nil]
      omega

@[simp] lemma grid_nil_T : (grid ([] : List (List (A ⊕ C)))).T = ∅ := by
  ext p
  simp

/-- The empty grid and the grid with one empty chain are the same network. -/
lemma grid_nil_eq_grid_cons_nil :
    grid ([] : List (List (A ⊕ C))) = grid [([] : List (A ⊕ C))] := by
  refine ext' ?_ ?_ ?_
  · ext p
    simp
  · funext p q
    simp only [grid_ord, eq_iff_iff]
    constructor
    · rintro ⟨-, h1, h2⟩
      rw [List.getD_eq_default _ _ (by simp)] at h2
      simp at h2
    · rintro ⟨-, h1, h2⟩
      rcases p with ⟨i, j⟩
      rcases i with _ | i
      · simp at h2
      · rw [List.getD_eq_default _ _ (by simp)] at h2
        simp at h2
  · funext p
    rcases p with ⟨i, j⟩
    rcases i with _ | i <;> simp [grid]

/-- A one-chain grid determines its chain. -/
lemma grid_single_inj {l l' : List (A ⊕ C)} (h : grid [l] = grid [l']) : l = l' := by
  have hmem : ∀ j : ℕ, j < l.length ↔ j < l'.length := by
    intro j
    have h1 : ((0, j) ∈ (grid [l]).T) ↔ ((0, j) ∈ (grid [l']).T) := by rw [h]
    simpa using h1
  have hlen : l.length = l'.length := by
    by_contra hne
    rcases Nat.lt_or_ge l.length l'.length with hlt | hge
    · exact absurd ((hmem l.length).2 hlt) (by omega)
    · have : l'.length < l.length := by omega
      exact absurd ((hmem l'.length).1 this) (by omega)
  refine List.ext_getElem hlen ?_
  intro i h1 h2
  have hα : (grid [l]).α (0, i) = (grid [l']).α (0, i) := by rw [h]
  rw [grid_α_of_lt (ls := [l]) (i := 0) (j := i) (by simpa using h1),
    grid_α_of_lt (ls := [l']) (i := 0) (j := i) (by simpa using h2)] at hα
  simpa using hα

@[simp] lemma seq_nil_T : (seq ([] : List (A ⊕ C))).T = ∅ := by
  ext p
  simp

end TaskNetwork

end HTN
