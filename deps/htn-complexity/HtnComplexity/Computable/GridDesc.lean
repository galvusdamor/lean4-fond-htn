import HtnPlanning.Core.Construction
import HtnPlanning.Core.Relabel
import HtnPlanning.Computable.Syntax
import HtnComplexity.Hypotheses.Planning
/-!
# Describing a grid of tasks

The method bodies of the compilation of totally ordered problems into acyclic ones
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`) are `TaskNetwork.grid ls`: a list `ls` of *rows*, each row
a chain of tasks, different rows unordered.  A description of such a method body has to list

* its identifiers — here `Nat.pair i j` for the task in row `i`, column `j`, so that the
  described network has *exactly* the identifiers of `grid ls` relabelled along
  `Nat.pairEquiv`;
* its ordering pairs — the consecutive pairs of each row are enough, since a described network
  is ordered by the transitive closure of the pairs it lists;
* its labels.

`HTN.Syn.gridDesc` is that description and `HTN.Syn.gridDesc_iso` is the theorem that it
denotes the grid: the described network is isomorphic — by the identity on identifiers — to the
image of `TaskNetwork.grid ls` under the numbering of the names and `Nat.pairEquiv`.

Isomorphism is the right relation here, and not equality: the labelling function of a task
network is total, and off the network the two disagree (`TnDesc.label` defaults to the action
`0`, `TaskNetwork.grid` to `Sum.inl default`).  By
`HTN.Problem.solvable_congr_methods` that is enough for the compiled problems to agree.
-/

namespace HTN

namespace Syn

open TaskNetwork

/-! ### The description -/

variable {ls : List (List (Bool × ℕ))}

@[simp] lemma gridDesc_ids : (gridDesc ls).ids = cellIds ls := rfl

@[simp] lemma gridDesc_ordList : (gridDesc ls).ordList = cellOrd ls := rfl

@[simp] lemma gridDesc_lbl : (gridDesc ls).lbl = cellLbl ls := rfl

lemma mem_cellIds {x : ℕ} :
    x ∈ cellIds ls ↔ ∃ i j, i < ls.length ∧ j < (gridRow ls i).length ∧ Nat.pair i j = x := by
  simp only [cellIds, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, j, hi, hj, rfl⟩
  · rintro ⟨i, j, hi, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩

lemma mem_cellOrd {p : ℕ × ℕ} :
    p ∈ cellOrd ls ↔ ∃ i j, i < ls.length ∧ j + 1 < (gridRow ls i).length ∧
      p = (Nat.pair i j, Nat.pair i (j + 1)) := by
  simp only [cellOrd, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, j, hi, by omega, rfl⟩
  · rintro ⟨i, j, hi, hj, rfl⟩
    exact ⟨i, hi, j, by omega, rfl⟩

/-! ### The labels -/

private lemma lookup_of_nodupKeys {β : Type} {l : List (ℕ × β)} (hnd : (l.map Prod.fst).Nodup)
    {k : ℕ} {v : β} (h : (k, v) ∈ l) : l.lookup k = some v := by
  induction l with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.1 h with rfl | h'
    · simp
    · have hne : k ≠ p.1 := by
        rintro rfl
        exact hnd.1 ⟨(p.1, v), h', rfl⟩
      rw [show p = (p.1, p.2) from rfl, List.lookup_cons, show (k == p.1) = false by simp [hne]]
      exact ih hnd.2 h'

lemma map_fst_cellLbl : (cellLbl ls).map Prod.fst = cellIds ls := by
  simp only [cellLbl, cellIds, List.map_flatMap, List.map_map]
  rfl

lemma nodup_cellIds : (cellIds ls).Nodup := by
  rw [cellIds, List.nodup_flatMap]
  constructor
  · intro i _
    refine List.Nodup.map (fun x y h => ?_) (List.nodup_range)
    exact (Nat.pair_eq_pair.1 h).2
  · refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := ls.length))
    intro i i' hlt
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range]
    rintro x ⟨j, -, rfl⟩ ⟨j', -, hx⟩
    have := (Nat.pair_eq_pair.1 hx).1
    omega

lemma lookup_cellLbl {i j : ℕ} (hi : i < ls.length) (hj : j < (gridRow ls i).length) :
    (cellLbl ls).lookup (Nat.pair i j) = some ((gridRow ls i).getD j (false, 0)) := by
  refine lookup_of_nodupKeys ?_ ?_
  · rw [map_fst_cellLbl]; exact nodup_cellIds
  · simp only [cellLbl, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨i, hi, j, hj, rfl⟩

/-! ### The ordering -/

lemma preOrd_cell {x y : ℕ} :
    (gridDesc ls).preOrd x y ↔ ∃ i j j', i < ls.length ∧ j < j' ∧ j' < (gridRow ls i).length ∧
      x = Nat.pair i j ∧ y = Nat.pair i j' := by
  constructor
  · intro h
    induction h with
    | @single b hb =>
      obtain ⟨i, j, hi, hj, hp⟩ := mem_cellOrd (ls := ls) (p := (x, b)) |>.1 hb
      exact ⟨i, j, j + 1, hi, by omega, hj, by simpa using congrArg Prod.fst hp,
        by simpa using congrArg Prod.snd hp⟩
    | @tail b c _ hbc ih =>
      obtain ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩ := ih
      obtain ⟨i₂, j₂, hi₂, hj₂, hp⟩ := mem_cellOrd (ls := ls) (p := (Nat.pair i j', c)) |>.1 hbc
      have h1 : Nat.pair i j' = Nat.pair i₂ j₂ := by simpa using congrArg Prod.fst hp
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h1
      exact ⟨i, j, j' + 1, hi, by omega, hj₂, rfl, by simpa using congrArg Prod.snd hp⟩
  · rintro ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩
    -- a chain of single steps from `j` to `j'`
    have key : ∀ k, j + k + 1 ≤ j' → (gridDesc ls).preOrd (Nat.pair i j) (Nat.pair i (j + k + 1)) := by
      intro k
      induction k with
      | zero =>
        intro hk
        refine Relation.TransGen.single ?_
        show (Nat.pair i j, Nat.pair i (j + 1)) ∈ (gridDesc ls).ordList
        rw [gridDesc_ordList]
        exact mem_cellOrd.2 ⟨i, j, hi, by omega, by simp⟩
      | succ k ih =>
        intro hk
        refine Relation.TransGen.tail (ih (by omega)) ?_
        show (Nat.pair i (j + k + 1), Nat.pair i (j + k + 1 + 1)) ∈ (gridDesc ls).ordList
        rw [gridDesc_ordList]
        exact mem_cellOrd.2 ⟨i, j + k + 1, hi, by omega, by simp⟩
    have := key (j' - j - 1) (by omega)
    rwa [show j + (j' - j - 1) + 1 = j' by omega] at this

lemma gridDesc_ord {x y : ℕ} :
    (gridDesc ls).toTaskNetwork.ord x y ↔ ∃ i j j', i < ls.length ∧ j < j' ∧
      j' < (gridRow ls i).length ∧ x = Nat.pair i j ∧ y = Nat.pair i j' := by
  rw [TnDesc.toTaskNetwork_ord]
  constructor
  · rintro ⟨-, -, h, -⟩
    exact preOrd_cell.1 h
  · rintro ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩
    refine ⟨mem_cellIds.2 ⟨i, j, hi, by omega, rfl⟩, mem_cellIds.2 ⟨i, j', hi, hj', rfl⟩,
      preOrd_cell.2 ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩, fun hc => ?_⟩
    obtain ⟨i₂, j₂, j₃, -, hlt, -, h1, h2⟩ := preOrd_cell.1 hc
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h1
    obtain ⟨-, rfl⟩ := Nat.pair_eq_pair.1 h2
    omega

/-! ### The description denotes the grid -/

section Denotes

variable {A C : Type} [Inhabited A]

variable {eA : A → ℕ} {eC : C → ℕ} {ls : List (List (A ⊕ C))}

omit [Inhabited A] in
lemma length_rows : (ls.map fun row => row.map (encLabel eA eC)).length = ls.length := by simp

omit [Inhabited A] in
lemma gridRow_map (i : ℕ) :
    gridRow (ls.map fun row => row.map (encLabel eA eC)) i =
      (ls.getD i []).map (encLabel eA eC) := by
  by_cases hi : i < ls.length
  · rw [gridRow, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ hi, List.getElem_map]
  · rw [gridRow, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    simp

omit [Inhabited A] in
lemma length_gridRow_map (i : ℕ) :
    (gridRow (ls.map fun row => row.map (encLabel eA eC)) i).length = (ls.getD i []).length := by
  rw [gridRow_map, List.length_map]

lemma label_gridDescOf {i j : ℕ} (hi : i < ls.length) (hj : j < (ls.getD i []).length) :
    (gridDescOf eA eC ls).label (Nat.pair i j) =
      Sum.map eA eC ((ls.getD i []).getD j (Sum.inl default)) := by
  have hrow : (gridRow (ls.map fun row => row.map (encLabel eA eC)) i).getD j (false, 0) =
      encLabel eA eC ((ls.getD i []).getD j (Sum.inl default)) := by
    rw [gridRow_map, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj]
  rw [TnDesc.label, gridDescOf, gridDesc_lbl,
    lookup_cellLbl (by simpa using hi) (by rw [length_gridRow_map]; exact hj), hrow]
  rcases (ls.getD i []).getD j (Sum.inl default) with a | c <;> rfl

/-- **The described grid is the grid.**  The described network and the image of
`TaskNetwork.grid ls` under the numbering of the names and `Nat.pairEquiv` have the same
identifiers, the same ordering and the same labels on those identifiers. -/
theorem gridDesc_iso (eA : A → ℕ) (eC : C → ℕ) (ls : List (List (A ⊕ C))) :
    (gridDescOf eA eC ls).toTaskNetwork.Iso
      (TaskNetwork.relabel eA eC Nat.pairEquiv (TaskNetwork.grid ls)) := by
  have hT : ∀ x : ℕ, x ∈ (gridDescOf eA eC ls).toTaskNetwork.T ↔
      x ∈ (TaskNetwork.relabel eA eC Nat.pairEquiv (TaskNetwork.grid ls)).T := by
    intro x
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridDescOf, gridDesc_ids, mem_cellIds,
      TaskNetwork.mem_relabel_T, TaskNetwork.mem_grid_T]
    constructor
    · rintro ⟨i, j, hi, hj, rfl⟩
      rw [length_gridRow_map] at hj
      simpa using ⟨by simpa using hi, hj⟩
    · intro h
      refine ⟨(Nat.unpair x).1, (Nat.unpair x).2, ?_, ?_, ?_⟩
      · simpa using h.1
      · rw [length_gridRow_map]; exact h.2
      · simp
  have hTfin : (gridDescOf eA eC ls).toTaskNetwork.T =
      (TaskNetwork.relabel eA eC Nat.pairEquiv (TaskNetwork.grid ls)).T := by
    ext x; exact hT x
  refine ⟨id, ?_, ?_, ?_⟩
  · rw [hTfin]; exact Set.bijOn_id _
  · intro x hx y hy
    have hx' : x ∈ (gridDescOf eA eC ls).toTaskNetwork.T := by simpa using hx
    have hy' : y ∈ (gridDescOf eA eC ls).toTaskNetwork.T := by simpa using hy
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridDescOf, gridDesc_ids, mem_cellIds] at hx' hy'
    obtain ⟨i, j, hi, hj, rfl⟩ := hx'
    obtain ⟨i', j', hi', hj', rfl⟩ := hy'
    rw [length_gridRow_map] at hj hj'
    simp only [id, gridDescOf, gridDesc_ord, TaskNetwork.relabel_ord, TaskNetwork.grid_ord]
    constructor
    · rintro ⟨i₂, j₂, j₃, -, hlt, hlen, h1, h2⟩
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h1
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h2
      rw [length_gridRow_map] at hlen
      refine ⟨by simp, by simpa using hlt, ?_⟩
      simpa using hlen
    · rintro ⟨he, hlt, hlen⟩
      simp only [Nat.pairEquiv, Equiv.coe_fn_symm_mk, Nat.unpair_pair] at he hlt hlen
      subst he
      exact ⟨i, j, j', by simpa using hi, hlt, by rw [length_gridRow_map]; simpa using hlen,
        rfl, rfl⟩
  · intro x hx
    have hx' : x ∈ (gridDescOf eA eC ls).toTaskNetwork.T := by simpa using hx
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridDescOf, gridDesc_ids, mem_cellIds] at hx'
    obtain ⟨i, j, hi, hj, rfl⟩ := hx'
    rw [length_gridRow_map] at hj
    rw [show ((gridDescOf eA eC ls).toTaskNetwork.α (Nat.pair i j)) =
      (gridDescOf eA eC ls).label (Nat.pair i j) from rfl,
      label_gridDescOf (by simpa using hi) hj]
    simp [TaskNetwork.relabel_α, TaskNetwork.grid_α]

end Denotes

end Syn

end HTN
