import HtnComplexity.PolyInst.Kit
/-!
# Emission over the entries of a serialised list

`HTN.PTime.cobham_fmTailsC` emits one chunk per *position* of a string.  On a serialised list
`y = blist (l.map f) ++ z` the positions that matter are the starts of the entries, recognised
by the test `HTN.Syn.TOPlan.entPos y`.  This file proves that emitting a chunk at exactly those
positions is a `flatMap` over the entries of `l`, in order:

* `HTN.Syn.PolyInst.filter_entPos_tails` — the suffixes of `y` at which an entry starts are, in
  order, the serialisations of the nonempty suffixes of `l`;
* `HTN.Syn.PolyInst.flatMap_entPos` — hence a chunk emitted at the entry positions is a
  `flatMap` over the decompositions `l = l₁ ++ a :: l₂` (`HTN.Syn.PolyInst.splits`), and the
  chunk may look at the prefix `cutS y s = entriesEnc (l₁.map f)` that precedes the entry.

It also provides the transducer `HTN.Syn.PolyInst.undbl` that undoes the doubling `dbl`.
-/

namespace HTN

namespace Syn

namespace PolyInst

open PTime Compress TOPlan

/-! ### Sublists of the suffixes of a string -/

theorem sublist_tails_of_pairwise {α : Type} :
    ∀ (y : List α) (L : List (List α)), (∀ s ∈ L, s <:+ y) →
      L.Pairwise (fun a b => b.length < a.length) → List.Sublist L y.tails := by
  intro y
  induction y with
  | nil =>
    intro L hsuf hpw
    rcases L with _ | ⟨s, L⟩
    · exact List.nil_sublist _
    · have hs : s = [] := List.suffix_nil.1 (hsuf s (by simp))
      rcases L with _ | ⟨s', L⟩
      · simp [hs]
      · have hs' : s' = [] := List.suffix_nil.1 (hsuf s' (by simp))
        have := List.rel_of_pairwise_cons hpw (List.mem_cons_self)
        simp [hs, hs'] at this
  | cons b y ih =>
    intro L hsuf hpw
    rw [List.tails_cons]
    rcases L with _ | ⟨s, L⟩
    · exact List.nil_sublist _
    · by_cases hs : s = b :: y
      · subst hs
        refine List.Sublist.cons₂ _ (ih L (fun t ht => ?_) (List.pairwise_cons.1 hpw).2)
        have ht' : t <:+ b :: y := hsuf t (by simp [ht])
        have hlen : t.length < (b :: y).length := (List.pairwise_cons.1 hpw).1 t ht
        rcases List.suffix_cons_iff.1 ht' with h | h
        · rw [h] at hlen; omega
        · exact h
      · refine List.Sublist.cons _ (ih (s :: L) (fun t ht => ?_) hpw)
        have ht' : t <:+ b :: y := hsuf t ht
        rcases List.suffix_cons_iff.1 ht' with h | h
        · exfalso
          rcases List.mem_cons.1 ht with rfl | ht
          · exact hs h
          · have hlen : t.length < s.length := (List.pairwise_cons.1 hpw).1 t ht
            have hsl : s.length ≤ (b :: y).length := (hsuf s (by simp)).length_le
            rw [h] at hlen; omega
        · exact h

theorem pairwise_tails {α : Type} (y : List α) :
    y.tails.Pairwise (fun a b => b.length < a.length) := by
  induction y with
  | nil => simp
  | cons b y ih =>
    rw [List.tails_cons, List.pairwise_cons]
    refine ⟨fun t ht => ?_, ih⟩
    have := ((List.mem_tails _ _).1 ht).length_le
    simp; omega

theorem Pairwise.sublist_ext {α : Type} {L L₁ L₂ : List (List α)}
    (hL : L.Pairwise (fun a b => b.length < a.length)) (h₁ : List.Sublist L₁ L)
    (h₂ : List.Sublist L₂ L)
    (hmem : ∀ s, s ∈ L₁ ↔ s ∈ L₂) : L₁ = L₂ := by
  induction L generalizing L₁ L₂ with
  | nil => rw [List.sublist_nil.1 h₁, List.sublist_nil.1 h₂]
  | cons x L ih =>
    have hx : ∀ t ∈ L, t.length < x.length := (List.pairwise_cons.1 hL).1
    have hxL : x ∉ L := fun h => by have := hx x h; omega
    cases h₁ with
    | cons _ h₁ =>
      cases h₂ with
      | cons _ h₂ => exact ih (List.pairwise_cons.1 hL).2 h₁ h₂ hmem
      | cons₂ _ h₂ =>
        exact absurd (h₁.subset ((hmem x).2 (by simp))) hxL
    | cons₂ _ h₁ =>
      cases h₂ with
      | cons _ h₂ =>
        exact absurd (h₂.subset ((hmem x).1 (by simp))) hxL
      | cons₂ _ h₂ =>
        congr 1
        refine ih (List.pairwise_cons.1 hL).2 h₁ h₂ fun s => ?_
        have hs1 : s ∈ _ → s ≠ x := fun h hsx => hxL (hsx ▸ h₁.subset h)
        have hs2 : s ∈ _ → s ≠ x := fun h hsx => hxL (hsx ▸ h₂.subset h)
        constructor
        · intro h
          rcases List.mem_cons.1 ((hmem s).1 (List.mem_cons_of_mem _ h)) with h' | h'
          · exact absurd h' (hs1 h)
          · exact h'
        · intro h
          rcases List.mem_cons.1 ((hmem s).2 (List.mem_cons_of_mem _ h)) with h' | h'
          · exact absurd h' (hs2 h)
          · exact h'

/-! ### The decompositions of a list -/

/-- The decompositions `l = l₁ ++ a :: l₂` of a list, in order. -/
def splits {α : Type} : List α → List (List α × α × List α)
  | [] => []
  | a :: l => ([], a, l) :: (splits l).map fun p => (a :: p.1, p.2.1, p.2.2)

theorem mem_splits {α : Type} {l : List α} {p : List α × α × List α} :
    p ∈ splits l ↔ l = p.1 ++ p.2.1 :: p.2.2 := by
  induction l generalizing p with
  | nil =>
    simp only [splits, List.not_mem_nil, false_iff]
    intro h; cases p.1 <;> simp at h
  | cons a l ih =>
    obtain ⟨l₁, b, l₂⟩ := p
    simp only [splits, List.mem_cons, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨⟨m₁, c, m₂⟩, hm, h1, h2, h3⟩)
      · rfl
      · subst h1 h2 h3
        have := ih.1 hm
        simp [this]
    · intro h
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
      | cons c m₁ =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        exact Or.inr ⟨(m₁, b, l₂), ih.2 h, rfl, rfl, rfl⟩

theorem splits_suffix_pairwise {α : Type} (l : List α) :
    ((splits l).map fun p => p.2.1 :: p.2.2).Pairwise (fun a b => b.length < a.length) := by
  induction l with
  | nil => simp [splits]
  | cons a l ih =>
    simp only [splits, List.map_cons, List.map_map, List.pairwise_cons]
    refine ⟨fun t ht => ?_, by simpa [Function.comp_def] using ih⟩
    simp only [List.mem_map, Function.comp_apply] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    have := mem_splits.1 hp
    simp only [List.length_cons]
    have h2 := congrArg List.length this
    simp at h2; omega

/-! ### The entry positions of a serialised list -/

theorem length_blist_map_lt {α : Type} (f : α → List Bool) {t t' : List α}
    (h : t'.length < t.length) (z : List Bool) (ht : t' <:+ t) :
    (blist (t'.map f) ++ z).length < (blist (t.map f) ++ z).length := by
  obtain ⟨u, rfl⟩ := ht
  rw [List.map_append, blist_append_eq, List.append_assoc, List.length_append]
  have : 0 < (entriesEnc (u.map f)).length := by
    cases u with
    | nil => simp at h
    | cons a u => simp [entriesEnc_cons]
  simp only [List.length_append] at this ⊢
  omega

/-- **The entry positions of a serialised list, in order.** -/
theorem filter_entPos_tails {α : Type} (f : α → List Bool) (l : List α) (z : List Bool) :
    (blist (l.map f) ++ z).tails.filter (fun s => entPos (blist (l.map f) ++ z) s) =
      (splits l).map fun p => blist ((p.2.1 :: p.2.2).map f) ++ z := by
  set y := blist (l.map f) ++ z with hy
  have hsufR : ∀ p ∈ splits l, blist ((p.2.1 :: p.2.2).map f) ++ z <:+ y := by
    intro p hp
    rw [hy, mem_splits.1 hp, List.map_append, blist_append_eq, List.append_assoc]
    exact List.suffix_append _ _
  refine Pairwise.sublist_ext (pairwise_tails y) (List.filter_sublist) ?_ fun s => ?_
  · refine sublist_tails_of_pairwise y _ (fun s hs => ?_) ?_
    · simp only [List.mem_map] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      exact hsufR p hp
    · have hpw := splits_suffix_pairwise l
      rw [List.pairwise_map] at hpw ⊢
      refine List.Pairwise.imp_of_mem ?_ hpw
      intro p p' hp hp' hlt
      refine length_blist_map_lt f (by simpa using hlt) z ?_
      have e1 := mem_splits.1 hp
      have e2 := mem_splits.1 hp'
      -- both are suffixes of `l`, the second shorter
      have s1 : (p.2.1 :: p.2.2) <:+ l := ⟨p.1, e1.symm⟩
      have s2 : (p'.2.1 :: p'.2.2) <:+ l := ⟨p'.1, e2.symm⟩
      exact (List.suffix_of_suffix_length_le s2 s1 (by simp at hlt ⊢; omega))
  · simp only [List.mem_filter, List.mem_tails, List.mem_map]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨l₁, a, l₂, hl, rfl⟩ := (entPos_iff f l z s).1 h
      exact ⟨(l₁, a, l₂), mem_splits.2 hl, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hsufR p hp, (entPos_iff f l z _).2 ⟨p.1, p.2.1, p.2.2, mem_splits.1 hp, rfl⟩⟩

theorem flatMap_ite_eq_filter {β : Type} (L : List β) (P : β → Bool) (H : β → List Bool) :
    (L.flatMap fun s => if P s = true then H s else []) = (L.filter P).flatMap H := by
  induction L with
  | nil => rfl
  | cons s L ih => by_cases h : P s = true <;> simp [List.filter_cons, h, ih]

/-- **A chunk emitted at the entry positions of a serialised list is a `flatMap` over its
entries.** -/
theorem flatMap_entPos {α : Type} (f : α → List Bool) (l : List α) (z : List Bool)
    (H : List Bool → List Bool) :
    ((blist (l.map f) ++ z).tails.flatMap fun s =>
        if entPos (blist (l.map f) ++ z) s = true then H s else []) =
      (splits l).flatMap fun p => H (blist ((p.2.1 :: p.2.2).map f) ++ z) := by
  rw [flatMap_ite_eq_filter, filter_entPos_tails, List.flatMap_map]

/-- The prefix that precedes an entry position. -/
theorem cutS_entry {α : Type} (f : α → List Bool) {l l₁ l₂ : List α} {a : α}
    (hl : l = l₁ ++ a :: l₂) (z : List Bool) :
    cutS (blist (l.map f) ++ z) (blist ((a :: l₂).map f) ++ z) = entriesEnc (l₁.map f) := by
  rw [hl, List.map_append, blist_append_eq, List.append_assoc, cutS_append]

/-- A `flatMap` over the decompositions that only looks at the entry is a `flatMap` over the
list. -/
theorem flatMap_splits_entry {α : Type} (l : List α) (G : α → List Bool) :
    ((splits l).flatMap fun p => G p.2.1) = l.flatMap G := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [splits, List.flatMap_map, ih]

/-! ### Undoing the doubling -/

/-- The transducer that keeps every second bit. -/
def undblM : Mealy Bool where
  step := fun s _ => !s
  out := fun s b => if s then [b] else []

/-- **Undoing `dbl`**: keep every second bit. -/
def undbl (y : List Bool) : List Bool := undblM.outs false y

theorem undbl_dbl (u : List Bool) : undbl (dbl u) = u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [undbl, dbl_cons] at ih ⊢
    simp only [List.cons_append, Mealy.outs_cons,
      show ∀ s b, undblM.step s b = !s from fun _ _ => rfl,
      show ∀ b, undblM.out true b = [b] from fun _ => rfl,
      show ∀ b, undblM.out false b = [] from fun _ => rfl, Bool.not_false, Bool.not_true, ih]
    rfl

theorem cobham_undbl {a : Fn} (ha : Cobham a) : Cobham fun args => undbl (a args) :=
  (undblM.cobham_mealy [false, true] false (fun _ => []) (by simp) (by intro s b _; cases s <;> simp)
    ha).of_eq' fun args => by simp [undbl]

end PolyInst

end Syn

end HTN
