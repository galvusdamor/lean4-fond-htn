import HtnPlanning.Core.Size
/-!
# Building blocks for constructing HTN domains

The compilability proofs of the project construct HTN domains "by hand": a method is given by
a list of *parallel chains* of task names, as in the brace notation of Bercher et al.,

```
c → ({b, c}{c, d})     -- two parallel chains, each of two tasks
c → (a, b, c)          -- one chain
```

This file provides

* `HTN.TaskNetwork.grid ls` — the task network whose tasks are the entries of the lists `ls`,
  where the entries of one list are totally ordered and entries of different lists are
  unordered.  Task identifiers are pairs `(i, j)` (chain `i`, position `j`).  The two special
  cases are `HTN.TaskNetwork.seq l = grid [l]` (a totally ordered sequence) and
  `HTN.TaskNetwork.par l` (a totally unordered set of tasks);
* the basic API of `grid`: membership, labelling, well-formedness, total orderedness, size;
* `HTN.Problem.isAcyclic_of_rank` — a *rank function* criterion for acyclicity: if every
  compound subtask of a reachable method has a strictly smaller natural number rank than the
  task decomposed by the method, then the problem is acyclic.  (The definition of acyclicity
  asks for a total *order* on the compound task names; the ties of the rank function are
  broken by an arbitrary well-ordering of the type of compound task names.)
-/

namespace HTN

universe u v w x

namespace TaskNetwork

variable {A : Type v} {C : Type w} [Inhabited A]

/-- The task network consisting of the parallel chains `ls`: the tasks of one chain are totally
ordered, tasks of different chains are unordered.  The identifier of the `j`-th task of the
`i`-th chain is `(i, j)`. -/
def grid (ls : List (List (A ⊕ C))) : TaskNetwork (ℕ × ℕ) A C where
  T := (Finset.range ls.length).biUnion
    fun i => (Finset.range (ls.getD i []).length).image fun j => (i, j)
  ord := fun p q => p.1 = q.1 ∧ p.2 < q.2 ∧ q.2 < (ls.getD p.1 []).length
  α := fun p => (ls.getD p.1 []).getD p.2 (Sum.inl default)

variable {ls : List (List (A ⊕ C))} {p q : ℕ × ℕ}

@[simp] lemma mem_grid_T :
    p ∈ (grid ls).T ↔ p.1 < ls.length ∧ p.2 < (ls.getD p.1 []).length := by
  obtain ⟨i, j⟩ := p
  simp only [grid, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩; exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩; exact ⟨i, h1, j, h2, rfl, rfl⟩

@[simp] lemma grid_ord :
    (grid ls).ord p q ↔ p.1 = q.1 ∧ p.2 < q.2 ∧ q.2 < (ls.getD p.1 []).length := Iff.rfl

@[simp] lemma grid_α (p : ℕ × ℕ) :
    (grid ls).α p = (ls.getD p.1 []).getD p.2 (Sum.inl default) := rfl

lemma grid_α_of_lt {i j : ℕ} (h : j < (ls.getD i []).length) :
    (grid ls).α (i, j) = (ls.getD i [])[j] := by
  rw [grid_α, List.getD_eq_getElem _ _ h]

lemma grid_wf : (grid ls).WF where
  irrefl := by rintro ⟨i, j⟩ ⟨-, h, -⟩; exact absurd h (lt_irrefl _)
  trans := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨i'', j''⟩ ⟨rfl, h1, -⟩ ⟨rfl, h2, h3⟩
    exact ⟨rfl, h1.trans h2, h3⟩
  mem_left := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨rfl, h1, h2⟩
    have hj : j < (ls.getD i []).length := h1.trans h2
    have : i < ls.length := by
      by_contra hi
      rw [List.getD_eq_default _ _ (by omega)] at hj
      simp at hj
    simpa using ⟨this, hj⟩
  mem_right := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨rfl, h1, h2⟩
    have : i < ls.length := by
      by_contra hi
      rw [List.getD_eq_default _ _ (by omega)] at h2
      simp at h2
    simpa using ⟨this, h2⟩

/-- The task network of a single totally ordered chain of tasks. -/
def seq (l : List (A ⊕ C)) : TaskNetwork (ℕ × ℕ) A C := grid [l]

/-- The totally unordered task network with the given tasks. -/
def par (l : List (A ⊕ C)) : TaskNetwork (ℕ × ℕ) A C := grid (l.map fun a => [a])

@[simp] lemma mem_seq_T {l : List (A ⊕ C)} : p ∈ (seq l).T ↔ p.1 = 0 ∧ p.2 < l.length := by
  obtain ⟨i, j⟩ := p
  simp only [seq, mem_grid_T, List.length_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    have hi : i = 0 := by omega
    subst hi
    simpa using h2
  · rintro ⟨rfl, h⟩
    simpa using h

lemma seq_α {l : List (A ⊕ C)} {j : ℕ} (h : j < l.length) :
    (seq l).α (0, j) = l[j] := by
  simpa [seq] using grid_α_of_lt (ls := [l]) (i := 0) (j := j) (by simpa using h)

lemma seq_wf {l : List (A ⊕ C)} : (seq l).WF := grid_wf

lemma seq_isTotallyOrdered {l : List (A ⊕ C)} : (seq l).IsTotallyOrdered := by
  rintro ⟨i, j⟩ hp ⟨i', j'⟩ hq hne
  rw [mem_seq_T] at hp hq
  obtain ⟨rfl, hj⟩ := hp
  obtain ⟨rfl, hj'⟩ := hq
  rcases lt_trichotomy j j' with h | h | h
  · exact Or.inl ⟨rfl, h, by simpa [seq] using hj'⟩
  · exact absurd (by simp [h]) hne
  · exact Or.inr ⟨rfl, h, by simpa [seq] using hj⟩

lemma par_wf {l : List (A ⊕ C)} : (par l).WF := grid_wf

@[simp] lemma mem_par_T {l : List (A ⊕ C)} : p ∈ (par l).T ↔ p.1 < l.length ∧ p.2 = 0 := by
  obtain ⟨i, j⟩ := p
  simp only [par, mem_grid_T, List.length_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using h1)] at h2
    simp only [List.getElem_map, List.length_singleton] at h2
    omega
  · rintro ⟨h1, rfl⟩
    refine ⟨h1, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    simp

lemma par_α {l : List (A ⊕ C)} {i : ℕ} (h : i < l.length) :
    (par l).α (i, 0) = l[i] := by
  have h' : i < (l.map fun a => [a]).length := by simpa using h
  rw [par, grid_α]
  rw [List.getD_eq_getElem _ _ h']
  simp

/-- The tasks of a chain network are exactly the entries of the list. -/
lemma grid_α_mem {i j : ℕ} (h : (i, j) ∈ (grid ls).T) :
    (grid ls).α (i, j) ∈ (ls.getD i []) := by
  rw [mem_grid_T] at h
  rw [grid_α_of_lt h.2]
  exact List.getElem_mem _

/-- Every label of a task of `grid ls` occurs in `ls`. -/
lemma grid_α_mem_flatten (h : p ∈ (grid ls).T) : (grid ls).α p ∈ ls.flatten := by
  obtain ⟨i, j⟩ := p
  have hmem := grid_α_mem h
  rw [mem_grid_T] at h
  refine List.mem_flatten.2 ⟨ls.getD i [], ?_, hmem⟩
  rw [List.getD_eq_getElem _ _ h.1]
  exact List.getElem_mem _

/-! ### Parallel chains followed by a final chain -/

/-- The task network consisting of the parallel chains `ls`, followed by the chain `tl`: the
tasks of `tl` are ordered after all tasks of all chains of `ls`.  This is the shape
`({(…), (…), (…)}, t)` of the initial task network of Theorem 4.3.7. -/
def gridTail (ls : List (List (A ⊕ C))) (tl : List (A ⊕ C)) : TaskNetwork (ℕ × ℕ) A C where
  T := (grid (ls ++ [tl])).T
  ord := fun p q => (grid (ls ++ [tl])).ord p q ∨
    (p.1 < ls.length ∧ q.1 = ls.length ∧ p ∈ (grid (ls ++ [tl])).T ∧
      q ∈ (grid (ls ++ [tl])).T)
  α := (grid (ls ++ [tl])).α

variable {tl : List (A ⊕ C)}

@[simp] lemma gridTail_T : (gridTail ls tl).T = (grid (ls ++ [tl])).T := rfl

@[simp] lemma gridTail_α (p : ℕ × ℕ) : (gridTail ls tl).α p = (grid (ls ++ [tl])).α p := rfl

lemma gridTail_wf : (gridTail ls tl).WF where
  irrefl := by
    rintro p (h | ⟨h1, h2, -, -⟩)
    · exact grid_wf.irrefl p h
    · omega
  trans := by
    rintro p q r (h | ⟨h1, h2, h3, h4⟩) (h' | ⟨h1', h2', h3', h4'⟩)
    · exact Or.inl (grid_wf.trans h h')
    · exact Or.inr ⟨h.1 ▸ h1', h2', grid_wf.mem_left h, h4'⟩
    · exact Or.inr ⟨h1, h'.1 ▸ h2, h3, grid_wf.mem_right h'⟩
    · omega
  mem_left := by
    rintro p q (h | ⟨-, -, h3, -⟩)
    · exact grid_wf.mem_left h
    · exact h3
  mem_right := by
    rintro p q (h | ⟨-, -, -, h4⟩)
    · exact grid_wf.mem_right h
    · exact h4

lemma gridTail_α_mem_flatten (h : p ∈ (gridTail ls tl).T) :
    (gridTail ls tl).α p ∈ (ls ++ [tl]).flatten :=
  grid_α_mem_flatten h

end TaskNetwork

/-! ### Sizes of the constructed task networks -/

namespace TaskNetwork

variable {A : Type v} {C : Type w} [Inhabited A] {ls : List (List (A ⊕ C))}

/-- If every chain of `ls` has at most `m` tasks, then `grid ls` has at most `|ls| * m`
tasks. -/
lemma grid_card_le {m : ℕ} (h : ∀ l ∈ ls, l.length ≤ m) :
    (grid ls).T.card ≤ ls.length * m := by
  classical
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum (f := fun i =>
      ((Finset.range (ls.getD i []).length).image fun j => (i, j)).card)
      (g := fun _ => m) ?_) ?_
  · intro i hi
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_range]
    rcases lt_or_ge i ls.length with hlt | hge
    · rw [List.getD_eq_getElem _ _ hlt]
      exact h _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ hge]
      simp
  · simp [Finset.sum_const, mul_comm]

lemma gridTail_card_le {m : ℕ} {tl : List (A ⊕ C)} (h : ∀ l ∈ ls, l.length ≤ m)
    (htl : tl.length ≤ m) : (gridTail ls tl).T.card ≤ (ls.length + 1) * m := by
  have : (gridTail ls tl).T = (grid (ls ++ [tl])).T := rfl
  rw [this]
  refine le_trans (grid_card_le (m := m) ?_) (by simp)
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact h l hl
  · simpa [List.mem_singleton.1 hl] using htl

end TaskNetwork

/-! ### The halving closure: counting tasks need only logarithmically many task names

The counting gadgets of the compilability proofs generate `k` copies of a task with
`O(log k)` methods, by the recursion `C^{2k} ↦ C^k C^k` and `C^{2k+1} ↦ T C^{2k}`.  The task
names that this recursion mentions are the elements of the *halving closure* of `k`. -/

/-- The halving closure of `k`: the set of indices reachable from `k` by repeatedly halving an
even number and decrementing an odd one. -/
def halvingClosure : ℕ → Finset ℕ
  | 0 => {0}
  | 1 => {1}
  | (k + 2) =>
      insert (k + 2)
        (if (k + 2) % 2 = 0 then halvingClosure ((k + 2) / 2) else halvingClosure (k + 1))
  decreasing_by all_goals omega

@[simp] lemma halvingClosure_zero : halvingClosure 0 = {0} := by rw [halvingClosure]
@[simp] lemma halvingClosure_one : halvingClosure 1 = {1} := by rw [halvingClosure]

lemma halvingClosure_succ_succ (k : ℕ) :
    halvingClosure (k + 2) = insert (k + 2)
      (if (k + 2) % 2 = 0 then halvingClosure ((k + 2) / 2) else halvingClosure (k + 1)) := by
  rw [halvingClosure]

lemma self_mem_halvingClosure (k : ℕ) : k ∈ halvingClosure k := by
  match k with
  | 0 => simp
  | 1 => simp
  | (k + 2) => rw [halvingClosure_succ_succ]; exact Finset.mem_insert_self _ _

/-- The unique index that the counting methods for `k ≥ 2` refer to. -/
def halvingChild (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 else k - 1

lemma halvingChild_mem_halvingClosure {k : ℕ} (hk : 2 ≤ k) :
    halvingChild k ∈ halvingClosure k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [halvingClosure_succ_succ, halvingChild]
  by_cases h : (j + 2) % 2 = 0
  · simp only [h, if_true]
    exact Finset.mem_insert_of_mem (self_mem_halvingClosure _)
  · simp only [h, if_false]
    have : j + 2 - 1 = j + 1 := by omega
    rw [this]
    exact Finset.mem_insert_of_mem (self_mem_halvingClosure _)

/-- The halving closure is transitive. -/
lemma halvingClosure_subset_of_mem : ∀ {k j : ℕ}, j ∈ halvingClosure k →
    halvingClosure j ⊆ halvingClosure k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      match k with
      | 0 => intro j hj; simp only [halvingClosure_zero, Finset.mem_singleton] at hj; subst hj; rfl
      | 1 => intro j hj; simp only [halvingClosure_one, Finset.mem_singleton] at hj; subst hj; rfl
      | (k + 2) =>
          intro j hj
          rw [halvingClosure_succ_succ] at hj ⊢
          rcases Finset.mem_insert.1 hj with rfl | hj
          · rw [halvingClosure_succ_succ]
          · by_cases h : (k + 2) % 2 = 0
            · simp only [h, if_true] at hj ⊢
              exact (ih ((k + 2) / 2) (by omega) hj).trans (Finset.subset_insert _ _)
            · simp only [h, if_false] at hj ⊢
              exact (ih (k + 1) (by omega) hj).trans (Finset.subset_insert _ _)

/-- **The counting gadget only needs logarithmically many task names.** -/
lemma card_halvingClosure_le : ∀ k : ℕ, (halvingClosure k).card ≤ 2 * Nat.log 2 k + 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      match k with
      | 0 => simp
      | 1 => simp
      | (k + 2) =>
          rw [halvingClosure_succ_succ]
          have hlog : Nat.log 2 ((k + 2) / 2) + 1 = Nat.log 2 (k + 2) := by
            rw [Nat.log_div_base]
            have : 1 ≤ Nat.log 2 (k + 2) := by
              have := Nat.log_mono_right (b := 2) (show 2 ≤ k + 2 by omega)
              simpa using this
            omega
          by_cases h : (k + 2) % 2 = 0
          · simp only [h, if_true]
            have h1 := ih ((k + 2) / 2) (by omega)
            have := Finset.card_insert_le (k + 2) (halvingClosure ((k + 2) / 2))
            omega
          · simp only [h, if_false]
            -- `k + 1` is even, so we unfold one more step
            have hk1 : 2 ≤ k + 1 := by omega
            obtain ⟨j, hj⟩ : ∃ j, k + 1 = j + 2 := ⟨k - 1, by omega⟩
            rw [hj, halvingClosure_succ_succ]
            have hpar : (j + 2) % 2 = 0 := by omega
            simp only [hpar, if_true]
            have h1 := ih ((j + 2) / 2) (by omega)
            have hc1 := Finset.card_insert_le (j + 2) (halvingClosure ((j + 2) / 2))
            have hc2 := Finset.card_insert_le (k + 2)
              (insert (j + 2) (halvingClosure ((j + 2) / 2)))
            have hmono : Nat.log 2 ((j + 2) / 2) ≤ Nat.log 2 ((k + 2) / 2) :=
              Nat.log_mono_right (by omega)
            omega

/-! ### A rank criterion for acyclicity -/

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

open Classical in
/-- **Rank criterion for acyclicity.**  If there is a function `rk : C → ℕ` that strictly
decreases along every reachable method — every compound subtask has a smaller rank than the
task the method decomposes — then the problem is acyclic.  (Ties of the rank function are
broken by an arbitrary well-ordering of `C`, so that the resulting stratification is a total
order, as `HTN.Problem.IsStrat0` requires.) -/
theorem isAcyclic_of_rank (P : Problem F A C I) (rk : C → ℕ)
    (h : ∀ m : Method I A C, P.ReachableMethod m → ∀ t ∈ m.subtasks.T, ∀ c : C,
      m.subtasks.α t = Sum.inr c → rk c < rk m.abstractTask) :
    P.IsAcyclic := by
  letI : LinearOrder C := IsWellOrder.linearOrder (α := C) WellOrderingRel
  refine ⟨fun c c' => rk c < rk c' ∨ (rk c = rk c' ∧ c ≤ c'), ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro c _; exact Or.inr ⟨rfl, le_rfl⟩
  · rintro c₁ c₂ c₃ - - - (h₁ | ⟨h₁, h₁'⟩) (h₂ | ⟨h₂, h₂'⟩)
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inl (h₂ ▸ h₁)
    · exact Or.inl (h₁ ▸ h₂)
    · exact Or.inr ⟨h₁.trans h₂, h₁'.trans h₂'⟩
  · intro c₁ c₂ _ _
    rcases lt_trichotomy (rk c₁) (rk c₂) with h' | h' | h'
    · exact Or.inl (Or.inl h')
    · rcases le_total c₁ c₂ with hle | hle
      · exact Or.inl (Or.inr ⟨h', hle⟩)
      · exact Or.inr (Or.inr ⟨h'.symm, hle⟩)
    · exact Or.inr (Or.inl h')
  · rintro c₁ c₂ - - (h₁ | ⟨h₁, h₁'⟩) (h₂ | ⟨h₂, h₂'⟩)
    · omega
    · omega
    · omega
    · exact le_antisymm h₁' h₂'
  · intro m hm t ht c hc
    have := h m hm t ht c hc
    exact ⟨Or.inl this, by rintro (h' | ⟨h', -⟩) <;> omega⟩

end Problem

end HTN
