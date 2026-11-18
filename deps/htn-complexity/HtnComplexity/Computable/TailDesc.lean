import HtnComplexity.Computable.GridDesc
/-!
# Describing a grid of tasks with one row after the others

`HtnComplexity/Computable/GridDesc.lean` describes `TaskNetwork.grid ls`: a list of rows,
each row a chain, different rows unordered.  The construction of Theorem 4.3.7 needs one shape
more, `TaskNetwork.gridTail ls tl` — the rows `ls` in parallel, *all* of them ordered before the
final chain `tl`.  That is the shape of the initial task network of the encoding (three parallel
chains, then the task `done`), and hence of the body of the method for its fresh initial task,
so no rendering of the encoding is possible without it.  Guarding a method
(`HtnComplexity/Guard/TaskExt.lean`) adds one *isolated* cell to a body, which is a further
row after the final chain, so the notion that closes under both is

* `TaskNetwork.gridAfter ls k` — the parallel rows `ls`, of which the row `k` is ordered after
  every row before it, every other row being free.  `TaskNetwork.gridAfter ls 0` is the grid and
  `TaskNetwork.gridAfter (ls ++ [tl]) ls.length` is `TaskNetwork.gridTail ls tl`.

Its description is the description of the grid `ls` with one extra ordering pair per row before
`k`: the last cell of the row before the first cell of the row `k`.  Since a described network
is ordered by the *transitive closure* of the pairs it lists, those pairs put every cell of
every earlier row before every cell of the row `k`, and nothing else.

* `HTN.Syn.gridAfterDesc` — the description, over described labels;
* `HTN.Syn.preOrd_gridAfterDesc` — its order, in closed form: either two cells of one row, or a
  cell of a row `i < k` and a cell of the row `k`;
* `HTN.Syn.gridAfterDescOf`, `HTN.Syn.gridAfterDesc_iso` — **the described network is
  `TaskNetwork.gridAfter ls k`**, relabelled along the numbering of the names and
  `Nat.pairEquiv`.

The file then packages the data into `HTN.Syn.Shape`, a row list together with the index of the
row that comes after the others, with `HTN.Syn.Shape.net` its task network, `HTN.Syn.Shape.desc`
its description, `HTN.Syn.Shape.desc_iso` the theorem that the second denotes the first, and
`HTN.Syn.Shape.size_desc_le` its size.  That is the form in which
`HtnComplexity/Computable/Render.lean` takes the body of a method.
-/


namespace HTN

/-! ### The task network -/

namespace TaskNetwork

variable {A C : Type} [Inhabited A]

/-- **The parallel rows `ls` with the row `k` ordered after every row before it.**  For `k = 0`
this is `TaskNetwork.grid ls`, and for `k = ls.length - 1` with `ls = ls' ++ [tl]` it is
`TaskNetwork.gridTail ls' tl`. -/
def gridAfter (ls : List (List (A ⊕ C))) (k : ℕ) : TaskNetwork (ℕ × ℕ) A C where
  T := (grid ls).T
  ord := fun p q => (grid ls).ord p q ∨
    (p.1 < k ∧ q.1 = k ∧ p ∈ (grid ls).T ∧ q ∈ (grid ls).T)
  α := (grid ls).α

variable {ls : List (List (A ⊕ C))} {k : ℕ} {tl : List (A ⊕ C)}

@[simp] lemma gridAfter_T : (gridAfter ls k).T = (grid ls).T := rfl

@[simp] lemma gridAfter_α (p : ℕ × ℕ) : (gridAfter ls k).α p = (grid ls).α p := rfl

@[simp] lemma gridAfter_ord (p q : ℕ × ℕ) :
    (gridAfter ls k).ord p q ↔ (grid ls).ord p q ∨
      (p.1 < k ∧ q.1 = k ∧ p ∈ (grid ls).T ∧ q ∈ (grid ls).T) := Iff.rfl

/-- **A grid with a final chain is a grid with one row after the others.** -/
lemma gridAfter_length (ls : List (List (A ⊕ C))) (tl : List (A ⊕ C)) :
    gridAfter (ls ++ [tl]) ls.length = gridTail ls tl := rfl

/-- **A grid with no row after the others is the grid.** -/
lemma gridAfter_zero (ls : List (List (A ⊕ C))) : gridAfter ls 0 = grid ls := by
  unfold gridAfter
  congr 1
  funext p q
  simp

lemma gridAfter_wf : (gridAfter ls k).WF where
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

end TaskNetwork

namespace Syn

open TaskNetwork

/-! ### Reading a row off an appended list -/

theorem getD_append_lt {α : Type} {l l' : List α} {i : ℕ} (h : i < l.length) (d : α) :
    (l ++ l').getD i d = l.getD i d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
    List.getElem_append_left h]

theorem getD_append_self {α : Type} (l : List α) (r : α) (d : α) :
    (l ++ [r]).getD l.length d = r := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-! ### The description -/

/-- The extra ordering pairs of a grid with a final chain: the last cell of each row `i < m`
before the first cell of the row `m`.  Empty rows, and an empty final chain, contribute
nothing. -/
def tailOrd (ls : List (List (Bool × ℕ))) (m : ℕ) : List (ℕ × ℕ) :=
  if (gridRow ls m).length = 0 then []
  else (List.range m).filterMap fun i =>
    if (gridRow ls i).length = 0 then none
    else some (Nat.pair i ((gridRow ls i).length - 1), Nat.pair m 0)

theorem mem_tailOrd {ls : List (List (Bool × ℕ))} {m : ℕ} {p : ℕ × ℕ} :
    p ∈ tailOrd ls m ↔ ∃ i, i < m ∧ 0 < (gridRow ls i).length ∧ 0 < (gridRow ls m).length ∧
      p = (Nat.pair i ((gridRow ls i).length - 1), Nat.pair m 0) := by
  rw [tailOrd]
  by_cases hm : (gridRow ls m).length = 0
  · simp only [hm, if_pos]
    simp only [List.not_mem_nil, false_iff, not_exists]
    rintro i ⟨-, -, hlt, -⟩
    omega
  · rw [if_neg hm]
    simp only [List.mem_filterMap, List.mem_range]
    constructor
    · rintro ⟨i, hi, hp⟩
      by_cases hr : (gridRow ls i).length = 0
      · rw [if_pos hr] at hp; exact absurd hp (by simp)
      · rw [if_neg hr] at hp
        exact ⟨i, hi, by omega, by omega, by simpa using hp.symm⟩
    · rintro ⟨i, hi, hr, -, rfl⟩
      exact ⟨i, hi, by rw [if_neg (by omega)]⟩

/-- **The description of a grid of tasks with a final chain**: the row `m` of `ls` is ordered
after all rows before it. -/
def gridAfterDesc (ls : List (List (Bool × ℕ))) (m : ℕ) : TnDesc :=
  (cellIds ls, cellOrd ls ++ tailOrd ls m, cellLbl ls)

variable {ls : List (List (Bool × ℕ))} {m : ℕ}

@[simp] lemma gridAfterDesc_ids : (gridAfterDesc ls m).ids = cellIds ls := rfl

@[simp] lemma gridAfterDesc_ordList :
    (gridAfterDesc ls m).ordList = cellOrd ls ++ tailOrd ls m := rfl

@[simp] lemma gridAfterDesc_lbl : (gridAfterDesc ls m).lbl = cellLbl ls := rfl

/-! ### The order of the description -/

private lemma preOrd_mono {d d' : TnDesc} (h : ∀ p ∈ d.ordList, p ∈ d'.ordList) {x y : ℕ}
    (hxy : d.preOrd x y) : d'.preOrd x y :=
  Relation.TransGen.mono (fun a b hab => h (a, b) hab) hxy

/-- A step inside one row. -/
theorem preOrd_gridAfterDesc_row {i j j' : ℕ} (hi : i < ls.length) (hjj : j < j')
    (hj' : j' < (gridRow ls i).length) :
    (gridAfterDesc ls m).preOrd (Nat.pair i j) (Nat.pair i j') :=
  preOrd_mono (d := gridDesc ls) (fun p hp => List.mem_append_left _ (by simpa using hp))
    (preOrd_cell.2 ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩)

/-- **The order of a described grid with a final chain**: either two cells of one row, or a cell
of a row before the final one and a cell of the final row. -/
theorem preOrd_gridAfterDesc {x y : ℕ} :
    (gridAfterDesc ls m).preOrd x y ↔
      (∃ i j j', i < ls.length ∧ j < j' ∧ j' < (gridRow ls i).length ∧
          x = Nat.pair i j ∧ y = Nat.pair i j') ∨
      (∃ i j j', i < m ∧ j < (gridRow ls i).length ∧ j' < (gridRow ls m).length ∧
          x = Nat.pair i j ∧ y = Nat.pair m j') := by
  constructor
  · intro h
    induction h with
    | @single b hb =>
      rcases List.mem_append.1 (show (x, b) ∈ cellOrd ls ++ tailOrd ls m from hb) with hb' | hb'
      · obtain ⟨i, j, hi, hj, hp⟩ := mem_cellOrd (ls := ls) (p := (x, b)) |>.1 hb'
        exact Or.inl ⟨i, j, j + 1, hi, by omega, hj, by simpa using congrArg Prod.fst hp,
          by simpa using congrArg Prod.snd hp⟩
      · obtain ⟨i, hi, hr, hm, hp⟩ := mem_tailOrd.1 hb'
        exact Or.inr ⟨i, (gridRow ls i).length - 1, 0, hi, by omega, by omega,
          by simpa using congrArg Prod.fst hp, by simpa using congrArg Prod.snd hp⟩
    | @tail b c _ hbc ih =>
      rcases List.mem_append.1 (show (b, c) ∈ cellOrd ls ++ tailOrd ls m from hbc) with
        hbc' | hbc'
      · obtain ⟨i₂, j₂, hi₂, hj₂, hp⟩ := mem_cellOrd (ls := ls) (p := (b, c)) |>.1 hbc'
        have hb : b = Nat.pair i₂ j₂ := by simpa using congrArg Prod.fst hp
        have hc : c = Nat.pair i₂ (j₂ + 1) := by simpa using congrArg Prod.snd hp
        rcases ih with ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩ | ⟨i, j, j', hi, hj, hj', rfl, rfl⟩
        · obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 hb
          exact Or.inl ⟨i₂, j, j₂ + 1, h1 ▸ hi, by omega, hj₂, by rw [h1], hc⟩
        · obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 hb
          exact Or.inr ⟨i, j, j₂ + 1, hi, hj, by rw [h1]; exact hj₂, rfl, by rw [hc, h1]⟩
      · obtain ⟨i₂, hi₂, hr₂, hm₂, hp⟩ := mem_tailOrd.1 hbc'
        have hb : b = Nat.pair i₂ ((gridRow ls i₂).length - 1) := by
          simpa using congrArg Prod.fst hp
        have hc : c = Nat.pair m 0 := by simpa using congrArg Prod.snd hp
        rcases ih with ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩ | ⟨i, j, j', hi, hj, hj', rfl, rfl⟩
        · obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 hb
          exact Or.inr ⟨i, j, 0, by rw [h1]; exact hi₂, by rw [h1]; omega, hm₂, rfl, hc⟩
        · obtain ⟨h1, -⟩ := Nat.pair_eq_pair.1 hb
          omega
  · rintro (⟨i, j, j', hi, hjj, hj', rfl, rfl⟩ | ⟨i, j, j', hi, hj, hj', rfl, rfl⟩)
    · exact preOrd_gridAfterDesc_row hi hjj hj'
    · have hmlen : m < ls.length := by
        by_contra hc
        rw [gridRow, List.getD_eq_default _ _ (by omega)] at hj'
        simp at hj'
      have hilen : i < ls.length := by omega
      have hedge : (gridAfterDesc ls m).listRel
          (Nat.pair i ((gridRow ls i).length - 1)) (Nat.pair m 0) := by
        show _ ∈ (gridAfterDesc ls m).ordList
        rw [gridAfterDesc_ordList]
        exact List.mem_append_right _ (mem_tailOrd.2 ⟨i, hi, by omega, by omega, rfl⟩)
      have hstart : (gridAfterDesc ls m).preOrd (Nat.pair i j) (Nat.pair m 0) := by
        rcases Nat.lt_or_ge j ((gridRow ls i).length - 1) with hlt | hge
        · exact Relation.TransGen.tail
            (preOrd_gridAfterDesc_row hilen hlt (by omega)) hedge
        · have : j = (gridRow ls i).length - 1 := by omega
          subst this
          exact Relation.TransGen.single hedge
      rcases Nat.eq_zero_or_pos j' with rfl | hpos
      · exact hstart
      · exact hstart.trans (preOrd_gridAfterDesc_row hmlen hpos hj')

/-- **The ordering of the described network**: the order of the description, which is already
antisymmetric. -/
theorem gridAfterDesc_ord {x y : ℕ} :
    (gridAfterDesc ls m).toTaskNetwork.ord x y ↔
      (∃ i j j', i < ls.length ∧ j < j' ∧ j' < (gridRow ls i).length ∧
          x = Nat.pair i j ∧ y = Nat.pair i j') ∨
      (∃ i j j', i < m ∧ j < (gridRow ls i).length ∧ j' < (gridRow ls m).length ∧
          x = Nat.pair i j ∧ y = Nat.pair m j') := by
  rw [TnDesc.toTaskNetwork_ord]
  constructor
  · rintro ⟨-, -, h, -⟩
    exact preOrd_gridAfterDesc.1 h
  · intro h
    have hmem : x ∈ cellIds ls ∧ y ∈ cellIds ls := by
      rcases h with ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩ | ⟨i, j, j', hi, hj, hj', rfl, rfl⟩
      · exact ⟨mem_cellIds.2 ⟨i, j, hi, by omega, rfl⟩, mem_cellIds.2 ⟨i, j', hi, hj', rfl⟩⟩
      · have hmlen : m < ls.length := by
          by_contra hc
          rw [gridRow, List.getD_eq_default _ _ (by omega)] at hj'
          simp at hj'
        exact ⟨mem_cellIds.2 ⟨i, j, by omega, hj, rfl⟩, mem_cellIds.2 ⟨m, j', hmlen, hj', rfl⟩⟩
    refine ⟨hmem.1, hmem.2, preOrd_gridAfterDesc.2 h, fun hc => ?_⟩
    rcases h with ⟨i, j, j', -, hjj, -, rfl, rfl⟩ | ⟨i, j, j', hi, -, -, rfl, rfl⟩
    · rcases preOrd_gridAfterDesc.1 hc with
        ⟨i₂, j₂, j₃, -, hlt, -, h1, h2⟩ | ⟨i₂, j₂, j₃, hi₂, -, -, h1, h2⟩
      · obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h1
        obtain ⟨-, rfl⟩ := Nat.pair_eq_pair.1 h2
        omega
      · obtain ⟨rfl, -⟩ := Nat.pair_eq_pair.1 h1
        obtain ⟨rfl, -⟩ := Nat.pair_eq_pair.1 h2
        omega
    · rcases preOrd_gridAfterDesc.1 hc with
        ⟨i₂, j₂, j₃, -, -, -, h1, h2⟩ | ⟨i₂, j₂, j₃, hi₂, -, -, h1, h2⟩
      · obtain ⟨rfl, -⟩ := Nat.pair_eq_pair.1 h1
        obtain ⟨rfl, -⟩ := Nat.pair_eq_pair.1 h2
        omega
      · obtain ⟨rfl, -⟩ := Nat.pair_eq_pair.1 h1
        obtain ⟨rfl, -⟩ := Nat.pair_eq_pair.1 h2
        omega

/-! ### The description denotes the grid with a final chain -/

section Denotes

variable {A C : Type} [Inhabited A]

/-- **The description of `TaskNetwork.gridAfter ls k`**, with the names numbered by `eA` and
`eC`. -/
def gridAfterDescOf (eA : A → ℕ) (eC : C → ℕ) (ls : List (List (A ⊕ C))) (k : ℕ) : TnDesc :=
  gridAfterDesc (ls.map fun row => row.map (encLabel eA eC)) k

variable {eA : A → ℕ} {eC : C → ℕ} {ls : List (List (A ⊕ C))} {k : ℕ}

omit [Inhabited A] in
lemma gridAfterDescOf_ids :
    (gridAfterDescOf eA eC ls k).ids = (gridDescOf eA eC ls).ids := rfl

omit [Inhabited A] in
lemma gridAfterDescOf_lbl :
    (gridAfterDescOf eA eC ls k).lbl = (gridDescOf eA eC ls).lbl := rfl

omit [Inhabited A] in
lemma gridAfterDescOf_label (x : ℕ) :
    (gridAfterDescOf eA eC ls k).label x = (gridDescOf eA eC ls).label x := rfl

/-- **The described network is the grid whose row `k` follows the rows before it.** -/
theorem gridAfterDesc_iso (eA : A → ℕ) (eC : C → ℕ) (ls : List (List (A ⊕ C))) (k : ℕ) :
    (gridAfterDescOf eA eC ls k).toTaskNetwork.Iso
      (TaskNetwork.relabel eA eC Nat.pairEquiv (TaskNetwork.gridAfter ls k)) := by
  set L := ls.map fun row => row.map (encLabel eA eC) with hL
  have hrow : ∀ i, (gridRow L i).length = (ls.getD i []).length := fun i =>
    length_gridRow_map (eA := eA) (eC := eC) (ls := ls) i
  have hLlen : L.length = ls.length := by simp [hL]
  have hT : ∀ x : ℕ, x ∈ (gridAfterDescOf eA eC ls k).toTaskNetwork.T ↔
      x ∈ (TaskNetwork.relabel eA eC Nat.pairEquiv (TaskNetwork.gridAfter ls k)).T := by
    intro x
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridAfterDescOf_ids, gridDescOf, gridDesc_ids,
      mem_cellIds, TaskNetwork.mem_relabel_T, TaskNetwork.gridAfter_T, TaskNetwork.mem_grid_T]
    constructor
    · rintro ⟨i, j, hi, hj, rfl⟩
      rw [length_gridRow_map] at hj
      simpa using ⟨by simpa [hL] using hi, hj⟩
    · intro h
      refine ⟨(Nat.unpair x).1, (Nat.unpair x).2, ?_, ?_, ?_⟩
      · simpa [hLlen] using h.1
      · rw [length_gridRow_map]; exact h.2
      · simp
  have hTfin : (gridAfterDescOf eA eC ls k).toTaskNetwork.T =
      (TaskNetwork.relabel eA eC Nat.pairEquiv (TaskNetwork.gridAfter ls k)).T := by
    ext x; exact hT x
  refine ⟨id, ?_, ?_, ?_⟩
  · rw [hTfin]; exact Set.bijOn_id _
  · intro x hx y hy
    have hx' : x ∈ (gridAfterDescOf eA eC ls k).toTaskNetwork.T := by simpa using hx
    have hy' : y ∈ (gridAfterDescOf eA eC ls k).toTaskNetwork.T := by simpa using hy
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridAfterDescOf_ids, gridDescOf, gridDesc_ids,
      mem_cellIds] at hx' hy'
    obtain ⟨i, j, hi, hj, rfl⟩ := hx'
    obtain ⟨i', j', hi', hj', rfl⟩ := hy'
    rw [length_gridRow_map] at hj hj'
    rw [hLlen] at hi hi'
    show (gridAfterDesc L k).toTaskNetwork.ord _ _ ↔ _
    rw [gridAfterDesc_ord, TaskNetwork.relabel_ord]
    simp only [id_eq, TaskNetwork.gridAfter_ord, Nat.pairEquiv, Equiv.coe_fn_symm_mk,
      Nat.unpair_pair, TaskNetwork.mem_grid_T, TaskNetwork.grid_ord, hLlen, hrow]
    constructor
    · rintro (⟨i₂, j₂, j₃, -, hlt, hlen, h1, h2⟩ | ⟨i₂, j₂, j₃, hlt, hj₂, hj₃, h1, h2⟩)
      · obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h1
        obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h2
        exact Or.inl ⟨rfl, hlt, hlen⟩
      · obtain ⟨e1, e2⟩ := Nat.pair_eq_pair.1 h1
        obtain ⟨e3, e4⟩ := Nat.pair_eq_pair.1 h2
        have hk : k < ls.length := by
          by_contra hcon
          rw [List.getD_eq_default _ _ (by omega)] at hj₃
          simp at hj₃
        refine Or.inr ⟨by omega, e3, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩
        · rw [e1, e2]; exact hj₂
        · rw [e3, e4]; exact hj₃
    · rintro (⟨rfl, hlt, hlen⟩ | ⟨hlt, heq, ⟨-, hj₂⟩, ⟨-, hj₃⟩⟩)
      · exact Or.inl ⟨i, j, j', hi, hlt, hlen, rfl, rfl⟩
      · subst heq
        exact Or.inr ⟨i, j, j', hlt, hj₂, hj₃, rfl, rfl⟩
  · intro x hx
    have hx' : x ∈ (gridAfterDescOf eA eC ls k).toTaskNetwork.T := by simpa using hx
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, gridAfterDescOf_ids, gridDescOf, gridDesc_ids,
      mem_cellIds] at hx'
    obtain ⟨i, j, hi, hj, rfl⟩ := hx'
    rw [length_gridRow_map] at hj
    rw [hLlen] at hi
    rw [show ((gridAfterDescOf eA eC ls k).toTaskNetwork.α (Nat.pair i j)) =
      (gridDescOf eA eC ls).label (Nat.pair i j) from rfl,
      label_gridDescOf (by simpa using hi) hj]
    simp [TaskNetwork.relabel_α, TaskNetwork.gridAfter_α, TaskNetwork.grid_α]

end Denotes

/-! ### The shape of a method body -/

section Shape

variable {A C : Type} [Inhabited A]

/-- **The shape of a method body of this development**: a list of rows, each a chain, together
with the index of the row that is ordered after all the rows before it — `0` when there is no
such row, so that a plain grid is the shape `⟨ls, 0⟩`. -/
structure Shape (A C : Type) where
  /-- The parallel rows. -/
  rows : List (List (A ⊕ C))
  /-- The index of the row ordered after every row before it. -/
  after : ℕ

namespace Shape

/-- **The task network of a shape.** -/
def net (s : Shape A C) : TaskNetwork (ℕ × ℕ) A C := TaskNetwork.gridAfter s.rows s.after

/-- **The description of a shape.** -/
def desc (s : Shape A C) (eA : A → ℕ) (eC : C → ℕ) : TnDesc :=
  gridAfterDescOf eA eC s.rows s.after

/-- The number of cells of a shape. -/
def cells (s : Shape A C) : ℕ := (s.rows.map List.length).sum

variable {eA : A → ℕ} {eC : C → ℕ}

omit [Inhabited A] in
@[simp] lemma desc_ids (s : Shape A C) :
    (s.desc eA eC).ids = (gridDescOf eA eC s.rows).ids := rfl

omit [Inhabited A] in
@[simp] lemma desc_label (s : Shape A C) (x : ℕ) :
    (s.desc eA eC).label x = (gridDescOf eA eC s.rows).label x := rfl

/-- The grid, as a shape. -/
lemma net_zero (ls : List (List (A ⊕ C))) :
    (Shape.mk ls 0).net = TaskNetwork.grid ls := TaskNetwork.gridAfter_zero ls

/-- The grid with a final chain, as a shape. -/
lemma net_length (ls : List (List (A ⊕ C))) (tl : List (A ⊕ C)) :
    (Shape.mk (ls ++ [tl]) ls.length).net = TaskNetwork.gridTail ls tl :=
  TaskNetwork.gridAfter_length ls tl

/-- The network of a shape is well formed. -/
theorem net_wf (s : Shape A C) : s.net.WF := TaskNetwork.gridAfter_wf

/-- **The description of a shape denotes its network.** -/
theorem desc_iso (eA : A → ℕ) (eC : C → ℕ) (s : Shape A C) :
    (s.desc eA eC).toTaskNetwork.Iso (TaskNetwork.relabel eA eC Nat.pairEquiv s.net) :=
  gridAfterDesc_iso eA eC s.rows s.after

/-! ### The size of a described shape

A hardness family bounds the *size* of its descriptions, so the bridge has to say how large the
description of a shape is: one identifier and one label per cell, fewer ordering pairs than
cells, and at most one more per row. -/

omit [Inhabited A] in
theorem sum_range_getD_length {α : Type} (l : List (List α)) :
    ((List.range l.length).map fun i => (l.getD i []).length).sum = (l.map List.length).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ (by simpa using h₁)]

omit [Inhabited A] in
/-- The description of a grid has one identifier and one label per cell, and fewer ordering
pairs than cells. -/
theorem size_gridDescOf_le (eA : A → ℕ) (eC : C → ℕ) (ls : List (List (A ⊕ C))) :
    (gridDescOf eA eC ls).size ≤ 3 * (ls.map List.length).sum := by
  classical
  set ls' := ls.map fun row => row.map (encLabel eA eC) with hls'
  have hlen : ls'.length = ls.length := by simp [hls']
  have hrow : ∀ i, (gridRow ls' i).length = (ls.getD i []).length :=
    fun i => length_gridRow_map (eA := eA) (eC := eC) (ls := ls) i
  have hids : (cellIds ls').length = (ls.map List.length).sum := by
    rw [cellIds, List.length_flatMap]
    simp only [List.length_map, List.length_range, hlen]
    simp only [hrow]
    exact sum_range_getD_length ls
  have hlbl : (cellLbl ls').length = (ls.map List.length).sum := by
    rw [cellLbl, List.length_flatMap]
    simp only [List.length_map, List.length_range, hlen]
    simp only [hrow]
    exact sum_range_getD_length ls
  have hord : (cellOrd ls').length ≤ (ls.map List.length).sum := by
    rw [cellOrd, List.length_flatMap]
    simp only [List.length_map, List.length_range, hlen]
    have hle : ∀ i ∈ List.range ls.length,
        (gridRow ls' i).length - 1 ≤ (ls.getD i []).length := by
      intro i _
      rw [hrow]
      omega
    refine le_trans (List.sum_le_sum (l := List.range ls.length)
      (f := fun i => (gridRow ls' i).length - 1) (g := fun i => (ls.getD i []).length) hle) ?_
    exact le_of_eq (sum_range_getD_length ls)
  show (cellIds ls').length + (cellOrd ls').length + (cellLbl ls').length ≤ _
  omega

omit [Inhabited A] in
/-- There is at most one extra ordering pair per row. -/
theorem length_tailOrd_le (ls : List (List (Bool × ℕ))) (m : ℕ) : (tailOrd ls m).length ≤ m := by
  rw [tailOrd]
  split
  · simp
  · exact le_trans (List.length_filterMap_le _ _) (by simp)

omit [Inhabited A] in
/-- **The size of the description of a shape.** -/
theorem size_desc_le (eA : A → ℕ) (eC : C → ℕ) (s : Shape A C) :
    (s.desc eA eC).size ≤ 3 * s.cells + s.after := by
  have hgrid := size_gridDescOf_le eA eC s.rows
  have hlen := length_tailOrd_le
    (s.rows.map fun row => row.map (encLabel eA eC)) s.after
  have h1 : (s.desc eA eC).size =
      (gridDescOf eA eC s.rows).size +
        (tailOrd (s.rows.map fun row => row.map (encLabel eA eC)) s.after).length := by
    simp only [desc, TnDesc.size, gridAfterDescOf, gridAfterDesc, gridDescOf, gridDesc,
      TnDesc.ids, TnDesc.ordList, TnDesc.lbl, List.length_append]
    omega
  show (s.desc eA eC).size ≤ 3 * (s.rows.map List.length).sum + s.after
  omega

end Shape

end Shape

end Syn

end HTN
