import HtnComplexity.Space.Advice
/-!
# Alternating reachability in an action table with calls

Plan existence for totally ordered HTN is not reachability in a transition system of polynomially
bounded states — the stack of pending method bodies is unbounded — but it is reachability with
**calls**: from a state in the middle of a method body, a compound task is *called*, its
refinement runs from the current world state to some world state, and the caller continues from
there.  An alternating machine checks such a call by guessing the world state the callee
returns in and branching universally into the callee and the continuation, so no stack is ever
stored.

This file gives the table-level form of that computation, in two presentations.

* `HTN.Space.CReach P C` — reachability with plain rows `P` and call pairs `C`: a pair `(p, r)`
  is a *push* row `p`, which starts the callee, and a *return* row `r`, which resumes the caller
  once the callee has finished;
* `HTN.Space.AReach kp kr tbl` — the same computation on a single indexed table, the form the
  machine reads off its advice.  A row whose delete list contains the marker `kp` is a push row,
  and its return row is the next row; a row whose delete list contains `kr` is a return row; all
  other rows are plain.  Markers are facts no state ever contains, so deleting them is harmless.

Results:

* `HTN.Space.aReach_layout_iff` — laying the pairs out as consecutive marked rows turns the first
  presentation into the second;
* `HTN.Space.AReach.subset_union_adds` — a reachable state only contains facts of the start
  state and facts some row adds, which is what bounds the configurations of the machine;
* `HTN.Space.aSolvable_map_iff` — solvability is invariant under a renaming of facts that is
  injective on the facts that matter, which is what allows the advice to carry short numerals.
-/

namespace HTN

namespace Space

open Syn

/-! ### Rows acting on states -/

/-- A row is applicable in a state. -/
def RowOk (r : Row) (s : Set ℕ) : Prop := ∀ f ∈ r.1, f ∈ s

/-- The state a row leaves behind. -/
def rowApp (r : Row) (s : Set ℕ) : Set ℕ := {f | f ∈ r.2.1 ∨ (f ∈ s ∧ f ∉ r.2.2)}

theorem mem_rowApp {r : Row} {s : Set ℕ} {f : ℕ} :
    f ∈ rowApp r s ↔ f ∈ r.2.1 ∨ (f ∈ s ∧ f ∉ r.2.2) := Iff.rfl

/-! ### Reachability with calls -/

/-- **Reachability with calls**: plain rows `P` are applied one at a time; a call pair
`(p, r) ∈ C` applies `p`, runs a callee from there to some state `t`, applies `r` to `t`, and
continues. -/
inductive CReach (P : List Row) (C : List (Row × Row)) : Set ℕ → Set ℕ → Prop
  | refl (s : Set ℕ) : CReach P C s s
  | plain {r : Row} {s s' : Set ℕ} : r ∈ P → RowOk r s → CReach P C (rowApp r s) s' →
      CReach P C s s'
  | call {p r : Row} {s t s' : Set ℕ} : (p, r) ∈ C → RowOk p s → CReach P C (rowApp p s) t →
      RowOk r t → CReach P C (rowApp r t) s' → CReach P C s s'

/-- **Reachability with calls on an indexed table**: a row with the marker `kp` in its delete
list is a push row, whose return row is the next one; rows with neither marker are plain. -/
inductive AReach (kp kr : ℕ) (tbl : List Row) : Set ℕ → Set ℕ → Prop
  | refl (s : Set ℕ) : AReach kp kr tbl s s
  | plain {i : ℕ} {s s' : Set ℕ} : i < tbl.length → kp ∉ (rowOf tbl i).2.2 →
      kr ∉ (rowOf tbl i).2.2 → RowOk (rowOf tbl i) s →
      AReach kp kr tbl (rowApp (rowOf tbl i) s) s' → AReach kp kr tbl s s'
  | call {i : ℕ} {s t s' : Set ℕ} : i + 1 < tbl.length → kp ∈ (rowOf tbl i).2.2 →
      RowOk (rowOf tbl i) s → AReach kp kr tbl (rowApp (rowOf tbl i) s) t →
      RowOk (rowOf tbl (i + 1)) t → AReach kp kr tbl (rowApp (rowOf tbl (i + 1)) t) s' →
      AReach kp kr tbl s s'

/-- **Solvability** of a table with calls: the goal holds in some state reachable from the
initial one. -/
def ASolvable (kp kr : ℕ) (tbl : List Row) (s₀ g : Set ℕ) : Prop :=
  ∃ s, AReach kp kr tbl s₀ s ∧ g ⊆ s

/-! ### Reachable states only contain added facts -/

theorem rowApp_subset (r : Row) (s : Set ℕ) : rowApp r s ⊆ s ∪ {f | f ∈ r.2.1} := by
  intro f hf
  rcases hf with hf | ⟨hf, -⟩
  · exact Or.inr hf
  · exact Or.inl hf

theorem mem_addFacts_of_rowOf {tbl : List Row} {i : ℕ} (hi : i < tbl.length) {f : ℕ}
    (hf : f ∈ (rowOf tbl i).2.1) : f ∈ addFacts tbl :=
  List.mem_flatMap.2 ⟨_, rowOf_mem hi, hf⟩

/-- **A reachable state only contains facts of the start state and facts some row adds.** -/
theorem AReach.subset_union_adds {kp kr : ℕ} {tbl : List Row} {s s' : Set ℕ}
    (h : AReach kp kr tbl s s') : s' ⊆ s ∪ {f | f ∈ addFacts tbl} := by
  induction h with
  | refl s => exact Set.subset_union_left
  | @plain i s s' hi _ _ _ _ ih =>
    refine ih.trans (Set.union_subset ?_ Set.subset_union_right)
    refine (rowApp_subset _ _).trans (Set.union_subset Set.subset_union_left ?_)
    intro f hf
    exact Or.inr (mem_addFacts_of_rowOf hi hf)
  | @call i s t s' hi _ _ _ _ _ iht ihs =>
    have hi' : i < tbl.length := by omega
    have h1 : rowApp (rowOf tbl i) s ⊆ s ∪ {f | f ∈ addFacts tbl} :=
      (rowApp_subset _ _).trans (Set.union_subset Set.subset_union_left
        fun f hf => Or.inr (mem_addFacts_of_rowOf hi' hf))
    have ht : t ⊆ s ∪ {f | f ∈ addFacts tbl} :=
      iht.trans (Set.union_subset h1 Set.subset_union_right)
    have h2 : rowApp (rowOf tbl (i + 1)) t ⊆ s ∪ {f | f ∈ addFacts tbl} :=
      (rowApp_subset _ _).trans (Set.union_subset ht
        fun f hf => Or.inr (mem_addFacts_of_rowOf hi hf))
    exact ihs.trans (Set.union_subset h2 Set.subset_union_right)

/-! ### Laying the call pairs out as consecutive marked rows -/

/-- Add a marker to the delete list of a row. -/
def markRow (k : ℕ) (r : Row) : Row := (r.1, r.2.1, k :: r.2.2)

/-- **The layout**: the plain rows, followed by each call pair as two consecutive rows, the push
row marked by `kp` and the return row marked by `kr`. -/
def layout (kp kr : ℕ) (P : List Row) (C : List (Row × Row)) : List Row :=
  P ++ C.flatMap fun pr => [markRow kp pr.1, markRow kr pr.2]

theorem length_flatMap_pair {α β : Type*} (C : List α) (g h : α → β) :
    (C.flatMap fun x => [g x, h x]).length = 2 * C.length := by
  induction C with
  | nil => simp
  | cons x C ih => simp [List.flatMap_cons, ih]; ring

theorem getD_flatMap_pair {α β : Type*} (C : List α) (g h : α → β) (d : β) (dα : α) :
    ∀ k, k < C.length →
      (C.flatMap fun x => [g x, h x]).getD (2 * k) d = g (C.getD k dα) ∧
      (C.flatMap fun x => [g x, h x]).getD (2 * k + 1) d = h (C.getD k dα) := by
  induction C with
  | nil => intro k hk; simp at hk
  | cons x C ih =>
    intro k hk
    rcases k with _ | k
    · simp [List.flatMap_cons]
    · have hk' : k < C.length := by simpa using hk
      obtain ⟨h1, h2⟩ := ih k hk'
      simp only [List.flatMap_cons, List.getD_cons_succ]
      rw [show 2 * (k + 1) = (2 * k) + 1 + 1 by ring,
        show 2 * k + 1 + 1 + 1 = (2 * k + 1) + 1 + 1 by ring]
      simp only [List.cons_append, List.getD_cons_succ, List.nil_append]
      exact ⟨h1, h2⟩

theorem rowOf_layout_lt {kp kr : ℕ} {P : List Row} {C : List (Row × Row)} {i : ℕ}
    (hi : i < P.length) : rowOf (layout kp kr P C) i = P.getD i ([], [], []) := by
  rw [rowOf, layout, List.getD_append _ _ _ _ hi]

theorem rowOf_layout_push {kp kr : ℕ} {P : List Row} {C : List (Row × Row)} {k : ℕ}
    (hk : k < C.length) :
    rowOf (layout kp kr P C) (P.length + 2 * k) =
      markRow kp (C.getD k (([], [], []), ([], [], []))).1 := by
  rw [rowOf, layout, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  exact (getD_flatMap_pair C _ _ _ _ k hk).1

theorem rowOf_layout_ret {kp kr : ℕ} {P : List Row} {C : List (Row × Row)} {k : ℕ}
    (hk : k < C.length) :
    rowOf (layout kp kr P C) (P.length + 2 * k + 1) =
      markRow kr (C.getD k (([], [], []), ([], [], []))).2 := by
  rw [rowOf, layout, List.getD_append_right _ _ _ _ (by omega),
    show P.length + 2 * k + 1 - P.length = 2 * k + 1 by omega]
  exact (getD_flatMap_pair C _ _ _ _ k hk).2

theorem length_layout (kp kr : ℕ) (P : List Row) (C : List (Row × Row)) :
    (layout kp kr P C).length = P.length + 2 * C.length := by
  rw [layout, List.length_append, length_flatMap_pair]

section Layout

variable {kp kr : ℕ} {P : List Row} {C : List (Row × Row)}

/-- The side conditions of the layout: the markers are distinct, occur in no delete list of the
plain rows or of the call pairs, and in no add list. -/
structure LayoutOk (kp kr : ℕ) (P : List Row) (C : List (Row × Row)) : Prop where
  ne : kp ≠ kr
  plain : ∀ r ∈ P, kp ∉ r.2.2 ∧ kr ∉ r.2.2 ∧ kp ∉ r.2.1 ∧ kr ∉ r.2.1
  push : ∀ pr ∈ C, kp ∉ pr.1.2.1 ∧ kr ∉ pr.1.2.1 ∧ kr ∉ pr.1.2.2
  ret : ∀ pr ∈ C, kp ∉ pr.2.2.1 ∧ kr ∉ pr.2.2.1 ∧ kp ∉ pr.2.2.2

/-- A state without markers. -/
def MarkFree (kp kr : ℕ) (s : Set ℕ) : Prop := kp ∉ s ∧ kr ∉ s

theorem rowApp_markRow {k : ℕ} {r : Row} {s : Set ℕ} (hks : k ∉ s) (hka : k ∉ r.2.1) :
    rowApp (markRow k r) s = rowApp r s := by
  ext f
  simp only [mem_rowApp, markRow, List.mem_cons]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, fun h => h2 (Or.inr h)⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      rintro (rfl | h)
      · exact hks h1
      · exact h2 h

theorem markFree_rowApp {r : Row} {s : Set ℕ} (hs : MarkFree kp kr s) (hp : kp ∉ r.2.1)
    (hr : kr ∉ r.2.1) : MarkFree kp kr (rowApp r s) := by
  refine ⟨?_, ?_⟩
  · rintro (h | ⟨h, -⟩)
    · exact hp h
    · exact hs.1 h
  · rintro (h | ⟨h, -⟩)
    · exact hr h
    · exact hs.2 h

theorem layout_adds_markFree (hok : LayoutOk kp kr P C) :
    MarkFree kp kr {f | f ∈ addFacts (layout kp kr P C)} := by
  constructor
  · intro h
    obtain ⟨r, hr, hf⟩ := List.mem_flatMap.1 h
    rcases List.mem_append.1 hr with hr | hr
    · exact (hok.plain r hr).2.2.1 hf
    · obtain ⟨pr, hpr, hr⟩ := List.mem_flatMap.1 hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hok.push pr hpr).1 hf
      · exact (hok.ret pr hpr).1 hf
  · intro h
    obtain ⟨r, hr, hf⟩ := List.mem_flatMap.1 h
    rcases List.mem_append.1 hr with hr | hr
    · exact (hok.plain r hr).2.2.2 hf
    · obtain ⟨pr, hpr, hr⟩ := List.mem_flatMap.1 hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hok.push pr hpr).2.1 hf
      · exact (hok.ret pr hpr).2.1 hf

theorem AReach.markFree (hok : LayoutOk kp kr P C) {s s' : Set ℕ}
    (h : AReach kp kr (layout kp kr P C) s s') (hs : MarkFree kp kr s) : MarkFree kp kr s' := by
  have hsub := h.subset_union_adds
  have hadd := layout_adds_markFree hok
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rcases hsub hk with h1 | h1
    · exact hs.1 h1
    · exact hadd.1 h1
  · rcases hsub hk with h1 | h1
    · exact hs.2 h1
    · exact hadd.2 h1

/-- The rows of the layout, classified. -/
theorem rowOf_layout_cases (i : ℕ) (hi : i < (layout kp kr P C).length) :
    (i < P.length ∧ rowOf (layout kp kr P C) i ∈ P) ∨
    (∃ k < C.length, i = P.length + 2 * k ∧
      rowOf (layout kp kr P C) i = markRow kp (C.getD k (([], [], []), ([], [], []))).1 ∧
      rowOf (layout kp kr P C) (i + 1) = markRow kr (C.getD k (([], [], []), ([], [], []))).2) ∨
    (∃ k < C.length, i = P.length + 2 * k + 1 ∧
      rowOf (layout kp kr P C) i = markRow kr (C.getD k (([], [], []), ([], [], []))).2) := by
  rw [length_layout] at hi
  by_cases hP : i < P.length
  · left
    refine ⟨hP, ?_⟩
    rw [rowOf_layout_lt hP, List.getD_eq_getElem _ _ hP]
    exact List.getElem_mem hP
  · right
    obtain ⟨k, hk⟩ : ∃ k, i - P.length = 2 * k ∨ i - P.length = 2 * k + 1 :=
      ⟨(i - P.length) / 2, by omega⟩
    rcases hk with hk | hk
    · have hkC : k < C.length := by omega
      left
      refine ⟨k, hkC, by omega, ?_, ?_⟩
      · rw [show i = P.length + 2 * k by omega, rowOf_layout_push hkC]
      · rw [show i + 1 = P.length + 2 * k + 1 by omega, rowOf_layout_ret hkC]
    · have hkC : k < C.length := by omega
      right
      refine ⟨k, hkC, by omega, ?_⟩
      rw [show i = P.length + 2 * k + 1 by omega, rowOf_layout_ret hkC]

theorem getD_mem_pairs {k : ℕ} (hk : k < C.length) :
    C.getD k (([], [], []), ([], [], [])) ∈ C := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- **Reachability with calls is reachability in the layout.** -/
theorem aReach_layout_iff (hok : LayoutOk kp kr P C) {s s' : Set ℕ} (hs : MarkFree kp kr s) :
    AReach kp kr (layout kp kr P C) s s' ↔ CReach P C s s' := by
  constructor
  · intro h
    induction h with
    | refl s => exact CReach.refl s
    | @plain i s s' hi hkp hkr hok' hrest ih =>
      rcases rowOf_layout_cases i hi with ⟨-, hmem⟩ | ⟨k, hk, -, hrow, -⟩ |
          ⟨k, hk, -, hrow⟩
      · refine CReach.plain hmem hok' (ih ?_)
        exact markFree_rowApp hs (hok.plain _ hmem).2.2.1 (hok.plain _ hmem).2.2.2
      · rw [hrow] at hkp
        exact absurd (List.mem_cons_self) hkp
      · rw [hrow] at hkr
        exact absurd (List.mem_cons_self) hkr
    | @call i s t s' hi hkp hok1 h1 hok2 h2 ih1 ih2 =>
      have hi' : i < (layout kp kr P C).length := by omega
      rcases rowOf_layout_cases i hi' with ⟨-, hmem⟩ | ⟨k, hk, -, hrow, hrow'⟩ |
          ⟨k, hk, -, hrow⟩
      · exact absurd hkp (hok.plain _ hmem).1
      · set pr := C.getD k (([], [], []), ([], [], [])) with hpr
        have hmem : pr ∈ C := getD_mem_pairs hk
        have hpa := (hok.push pr hmem)
        have hra := (hok.ret pr hmem)
        rw [hrow] at hok1 h1 ih1
        rw [hrow'] at hok2 h2 ih2
        rw [rowApp_markRow hs.1 hpa.1] at h1 ih1
        have hs1 : MarkFree kp kr (rowApp pr.1 s) := markFree_rowApp hs hpa.1 hpa.2.1
        have ht : MarkFree kp kr t := by
          have h1' : AReach kp kr (layout kp kr P C) (rowApp (markRow kp pr.1) s) t := by
            rw [rowApp_markRow hs.1 hpa.1]; exact h1
          exact h1.markFree hok hs1
        rw [rowApp_markRow ht.2 hra.2.1] at h2 ih2
        exact CReach.call hmem hok1 (ih1 hs1) hok2
          (ih2 (markFree_rowApp ht hra.1 hra.2.1))
      · rw [hrow] at hkp
        rcases List.mem_cons.1 hkp with h | h
        · exact absurd h hok.ne
        · exact absurd h (hok.ret _ (getD_mem_pairs hk)).2.2
  · intro h
    induction h with
    | refl s => exact AReach.refl s
    | @plain r s s' hr hok' _ ih =>
      obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
      have hrow : rowOf (layout kp kr P C) i = r := by
        rw [rowOf_layout_lt hi, List.getD_eq_getElem _ _ hi, hri]
      have hlen : i < (layout kp kr P C).length := by rw [length_layout]; omega
      refine AReach.plain hlen (by rw [hrow]; exact (hok.plain r hr).1)
        (by rw [hrow]; exact (hok.plain r hr).2.1) (by rw [hrow]; exact hok') ?_
      rw [hrow]
      exact ih (markFree_rowApp hs (hok.plain r hr).2.2.1 (hok.plain r hr).2.2.2)
    | @call p r s t s' hpr hok1 h1 hok2 h2 ih1 ih2 =>
      obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hpr
      have hgk : C.getD k (([], [], []), ([], [], [])) = (p, r) := by
        rw [List.getD_eq_getElem _ _ hk, hkp]
      have hrow := rowOf_layout_push (kp := kp) (kr := kr) (P := P) hk
      have hrow' := rowOf_layout_ret (kp := kp) (kr := kr) (P := P) hk
      rw [hgk] at hrow hrow'
      have hpa := hok.push _ hpr
      have hra := hok.ret _ hpr
      have hs1 : MarkFree kp kr (rowApp p s) := markFree_rowApp hs hpa.1 hpa.2.1
      have ht : MarkFree kp kr t := by
        have := ih1 hs1
        exact this.markFree hok hs1
      have hlen : P.length + 2 * k + 1 < (layout kp kr P C).length := by
        rw [length_layout]; omega
      refine AReach.call hlen (by rw [hrow]; exact List.mem_cons_self)
        (by rw [hrow]; exact hok1) ?_ (by rw [hrow']; exact hok2) ?_
      · rw [hrow, rowApp_markRow hs.1 hpa.1]
        exact ih1 hs1
      · rw [hrow', rowApp_markRow ht.2 hra.2.1]
        exact ih2 (markFree_rowApp ht hra.1 hra.2.1)

end Layout

/-! ### Renaming the facts -/

section Rename

variable {ρ : ℕ → ℕ} {X : Set ℕ}

/-- The facts of a row lie in `X`. -/
def RowIn (X : Set ℕ) (r : Row) : Prop := ∀ f, f ∈ r.1 ∨ f ∈ r.2.1 ∨ f ∈ r.2.2 → f ∈ X

theorem rowOf_map (tbl : List Row) (i : ℕ) :
    rowOf (tbl.map (mapRow ρ)) i = mapRow ρ (rowOf tbl i) := by
  rw [rowOf, rowOf]
  by_cases hi : i < tbl.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rfl

theorem rowIn_rowOf {tbl : List Row} (hX : ∀ f ∈ tblFacts tbl, f ∈ X) (i : ℕ) :
    RowIn X (rowOf tbl i) := by
  intro f hf
  by_cases hi : i < tbl.length
  · have hr := rowOf_mem hi
    rcases hf with hf | hf | hf
    · exact hX f (mem_tblFacts_of_prec hr hf)
    · exact hX f (mem_tblFacts_of_add hr hf)
    · exact hX f (mem_tblFacts_of_del hr hf)
  · rw [rowOf, List.getD_eq_default _ _ (by omega)] at hf
    simp at hf

variable (hinj : ∀ a ∈ X, ∀ b ∈ X, ρ a = ρ b → a = b)
include hinj

theorem mem_image_iff_of_inj {s : Set ℕ} (hs : s ⊆ X) {a : ℕ} (ha : a ∈ X) :
    ρ a ∈ ρ '' s ↔ a ∈ s := by
  constructor
  · rintro ⟨b, hb, hba⟩
    rw [← hinj b (hs hb) a ha hba]
    exact hb
  · intro h
    exact ⟨a, h, rfl⟩

theorem mem_map_iff_of_inj {l : List ℕ} (hl : ∀ f ∈ l, f ∈ X) {a : ℕ} (ha : a ∈ X) :
    ρ a ∈ l.map ρ ↔ a ∈ l := by
  constructor
  · intro h
    obtain ⟨b, hb, hba⟩ := List.mem_map.1 h
    rw [← hinj b (hl b hb) a ha hba]
    exact hb
  · intro h
    exact List.mem_map_of_mem h

theorem rowOk_map_iff {r : Row} (hr : RowIn X r) {s : Set ℕ} (hs : s ⊆ X) :
    RowOk (mapRow ρ r) (ρ '' s) ↔ RowOk r s := by
  constructor
  · intro h f hf
    have := h (ρ f) (List.mem_map_of_mem hf)
    exact (mem_image_iff_of_inj hinj hs (hr f (Or.inl hf))).1 this
  · intro h f hf
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hf
    exact ⟨a, h a ha, rfl⟩

omit hinj in
theorem rowApp_subset_X {r : Row} (hr : RowIn X r) {s : Set ℕ} (hs : s ⊆ X) :
    rowApp r s ⊆ X := by
  rintro f (hf | ⟨hf, -⟩)
  · exact hr f (Or.inr (Or.inl hf))
  · exact hs hf

theorem rowApp_map {r : Row} (hr : RowIn X r) {s : Set ℕ} (hs : s ⊆ X) :
    rowApp (mapRow ρ r) (ρ '' s) = ρ '' rowApp r s := by
  ext f
  simp only [mem_rowApp, mapRow, Set.mem_image]
  constructor
  · rintro (hf | ⟨⟨a, ha, rfl⟩, hnd⟩)
    · obtain ⟨a, ha', rfl⟩ := List.mem_map.1 hf
      exact ⟨a, Or.inl ha', rfl⟩
    · refine ⟨a, Or.inr ⟨ha, fun had => hnd (List.mem_map_of_mem had)⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ha | ⟨ha, hnd⟩
    · exact Or.inl (List.mem_map_of_mem ha)
    · refine Or.inr ⟨⟨a, ha, rfl⟩, fun h => hnd ?_⟩
      exact (mem_map_iff_of_inj hinj (fun f hf => hr f (Or.inr (Or.inr hf))) (hs ha)).1 h

theorem marker_map_iff {r : Row} (hr : RowIn X r) {k : ℕ} (hk : k ∈ X) :
    ρ k ∈ (mapRow ρ r).2.2 ↔ k ∈ r.2.2 :=
  mem_map_iff_of_inj hinj (fun f hf => hr f (Or.inr (Or.inr hf))) hk

variable {kp kr : ℕ} {tbl : List Row}

theorem AReach.map (hX : ∀ f ∈ tblFacts tbl, f ∈ X) (hkp : kp ∈ X) (hkr : kr ∈ X)
    {s s' : Set ℕ} (h : AReach kp kr tbl s s') (hs : s ⊆ X) :
    AReach (ρ kp) (ρ kr) (tbl.map (mapRow ρ)) (ρ '' s) (ρ '' s') := by
  induction h with
  | refl s => exact AReach.refl _
  | @plain i s s' hi hp hr hok _ ih =>
    have hin := rowIn_rowOf hX i
    refine AReach.plain (by simpa using hi) ?_ ?_ ?_ ?_
    · rw [rowOf_map, marker_map_iff hinj hin hkp]; exact hp
    · rw [rowOf_map, marker_map_iff hinj hin hkr]; exact hr
    · rw [rowOf_map, rowOk_map_iff hinj hin hs]; exact hok
    · rw [rowOf_map, rowApp_map hinj hin hs]
      exact ih (rowApp_subset_X hin hs)
  | @call i s t s' hi hp hok1 h1 hok2 _ ih1 ih2 =>
    have hin := rowIn_rowOf hX i
    have hin' := rowIn_rowOf hX (i + 1)
    have hs1 := rowApp_subset_X hin hs
    have ht : t ⊆ X := by
      intro f hf
      rcases h1.subset_union_adds hf with hf | hf
      · exact hs1 hf
      · obtain ⟨r, hr, hfr⟩ := List.mem_flatMap.1 hf
        obtain ⟨j, hj, rfl⟩ := exists_rowOf hr
        exact rowIn_rowOf hX j f (Or.inr (Or.inl hfr))
    refine AReach.call (t := ρ '' t) (by simpa using hi) ?_ ?_ ?_ ?_ ?_
    · rw [rowOf_map, marker_map_iff hinj hin hkp]; exact hp
    · rw [rowOf_map, rowOk_map_iff hinj hin hs]; exact hok1
    · rw [rowOf_map, rowApp_map hinj hin hs]; exact ih1 hs1
    · rw [rowOf_map, rowOk_map_iff hinj hin' ht]; exact hok2
    · rw [rowOf_map, rowApp_map hinj hin' ht]; exact ih2 (rowApp_subset_X hin' ht)

theorem AReach.pull (hX : ∀ f ∈ tblFacts tbl, f ∈ X) (hkp : kp ∈ X) (hkr : kr ∈ X)
    {s₁ s₂ : Set ℕ} (h : AReach (ρ kp) (ρ kr) (tbl.map (mapRow ρ)) s₁ s₂) :
    ∀ s, s ⊆ X → s₁ = ρ '' s → ∃ s', s' ⊆ X ∧ s₂ = ρ '' s' ∧ AReach kp kr tbl s s' := by
  induction h with
  | refl s₁ =>
    intro s hs hs₁
    exact ⟨s, hs, hs₁, AReach.refl s⟩
  | @plain i s₁ s₂ hi hp hr hok _ ih =>
    intro s hs hs₁
    subst hs₁
    have hin := rowIn_rowOf hX i
    have hi' : i < tbl.length := by simpa using hi
    rw [rowOf_map, marker_map_iff hinj hin hkp] at hp
    rw [rowOf_map, marker_map_iff hinj hin hkr] at hr
    rw [rowOf_map, rowOk_map_iff hinj hin hs] at hok
    obtain ⟨s', hs', rfl, h'⟩ := ih (rowApp (rowOf tbl i) s) (rowApp_subset_X hin hs)
      (by rw [rowOf_map, rowApp_map hinj hin hs])
    exact ⟨s', hs', rfl, AReach.plain hi' hp hr hok h'⟩
  | @call i s₁ t s₂ hi hp hok1 _ hok2 _ ih1 ih2 =>
    intro s hs hs₁
    subst hs₁
    have hin := rowIn_rowOf hX i
    have hin' := rowIn_rowOf hX (i + 1)
    have hi' : i + 1 < tbl.length := by simpa using hi
    rw [rowOf_map, marker_map_iff hinj hin hkp] at hp
    rw [rowOf_map, rowOk_map_iff hinj hin hs] at hok1
    obtain ⟨t', ht', rfl, h1'⟩ := ih1 (rowApp (rowOf tbl i) s) (rowApp_subset_X hin hs)
      (by rw [rowOf_map, rowApp_map hinj hin hs])
    rw [rowOf_map, rowOk_map_iff hinj hin' ht'] at hok2
    obtain ⟨s', hs', rfl, h2'⟩ := ih2 (rowApp (rowOf tbl (i + 1)) t')
      (rowApp_subset_X hin' ht') (by rw [rowOf_map, rowApp_map hinj hin' ht'])
    exact ⟨s', hs', rfl, AReach.call hi' hp hok1 h1' hok2 h2'⟩

/-- **Solvability is invariant under a renaming injective on the facts that matter.** -/
theorem aSolvable_map_iff (hX : ∀ f ∈ tblFacts tbl, f ∈ X) (hkp : kp ∈ X) (hkr : kr ∈ X)
    {s₀ g : Set ℕ} (hs₀ : s₀ ⊆ X) (hg : g ⊆ X) :
    ASolvable (ρ kp) (ρ kr) (tbl.map (mapRow ρ)) (ρ '' s₀) (ρ '' g) ↔
      ASolvable kp kr tbl s₀ g := by
  constructor
  · rintro ⟨s₂, h, hgs⟩
    obtain ⟨s', hs', rfl, h'⟩ := h.pull hinj hX hkp hkr s₀ hs₀ rfl
    refine ⟨s', h', fun f hf => ?_⟩
    exact (mem_image_iff_of_inj hinj hs' (hg hf)).1 (hgs ⟨f, hf, rfl⟩)
  · rintro ⟨s', h, hgs⟩
    have hs' : s' ⊆ X := by
      intro f hf
      rcases h.subset_union_adds hf with hf | hf
      · exact hs₀ hf
      · obtain ⟨r, hr, hfr⟩ := List.mem_flatMap.1 hf
        obtain ⟨j, hj, rfl⟩ := exists_rowOf hr
        exact rowIn_rowOf hX j f (Or.inr (Or.inl hfr))
    exact ⟨ρ '' s', h.map hinj hX hkp hkr hs₀, Set.image_mono hgs⟩

end Rename

end Space

end HTN
