import HtnPlanning.Core.ProofTuples
/-!
# Proof lists: derivations of the proof-tuple calculus **with sharing**

`HtnPlanning/Core/ProofTuples.lean` defines `HTN.Domain.Provable`, the inductive derivability
of a proof tuple `(s, x, s')`, and proves it equivalent to the existence of a refinement of `x`
into an executable action sequence leading from `s` to `s'`.  Being inductive, a derivation of
`Provable` is a **tree**: if the triple `(s, x, s')` is used twice, its derivation is duplicated,
and the tree of a provable triple can be exponentially larger than the number of triples.

The source of the compilation of totally ordered problems into acyclic ones phrases the same
notion as a *list*:

> The proof that a plan for a TO-HTN problem exists can be viewed as an ordered list of triples
> `(s, T, s')` … such that if `T` is compound then there is a method `T ↦ A B` and a state `s''`
> such that the triples `(s, A, s'')` and `(s'', B, s')` occur **before** `(s, T, s')` in the
> list.  As there are only exponentially many states, this list can be at most exponentially
> long.

A list is a derivation **with sharing**: an entry may be used by arbitrarily many later entries.
That is what makes the compilation polynomial — the number of memory cells of the compiled
problem is exponential, but only exponential, and it enters the size of the compiled domain
through its logarithm.

This file formalises proof lists and proves

* `HTN.Domain.ProofList.provable_of_mem` — every entry of a proof list is provable;
* `HTN.Domain.exists_proofList_cons` — conversely, every provable triple heads a proof list;
* `HTN.Domain.exists_proofList_nodup` — the list can be taken duplicate-free, hence of length at
  most the number of triples;
* `HTN.Domain.exists_proofList_length_le` — the resulting explicit bound
  `2^{|F|} · (|A| + |C|) · 2^{|F|}` for a finite signature.

Lists are stored in **reverse chronological order**: the head is the last entry, and an entry is
justified by the entries of the tail.  This makes `ProofList` a plain inductive predicate and
makes induction along it the same thing as processing the proof in chronological order.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- A proof tuple `(s, x, s')` of the proof-tuple calculus. -/
abbrev Trip (F : Type u) (A : Type v) (C : Type w) : Type _ := Set F × (A ⊕ C) × Set F

namespace Domain

variable (D : Domain F A C I)

/-- `D.Justified pre t`: the triple `t` follows by one rule of the proof-tuple calculus from
triples occurring in `pre`. -/
inductive Justified (pre : List (Trip F A C)) : Trip F A C → Prop
  /-- A primitive task: `s' = γ(s, a)`, provided `a` is applicable in `s`. -/
  | prim {a : A} {s : Set F} (h : D.Applicable a s) :
      Justified pre (s, Sum.inl a, D.transition a s)
  /-- A method without subtasks does not change the state. -/
  | zero {c : C} {s : Set F} (h : D.SeqBody c []) : Justified pre (s, Sum.inr c, s)
  /-- A method with one subtask, whose triple occurs earlier. -/
  | one {c : C} {x : A ⊕ C} {s s' : Set F} (h : D.SeqBody c [x]) (hx : (s, x, s') ∈ pre) :
      Justified pre (s, Sum.inr c, s')
  /-- A method with two subtasks, whose triples occur earlier. -/
  | two {c : C} {x y : A ⊕ C} {s s'' s' : Set F} (h : D.SeqBody c [x, y])
      (hx : (s, x, s'') ∈ pre) (hy : (s'', y, s') ∈ pre) : Justified pre (s, Sum.inr c, s')

variable {D}

/-- **Justification only depends on which triples occur earlier.** -/
lemma Justified.mono {pre pre' : List (Trip F A C)} {t : Trip F A C}
    (hsub : ∀ u ∈ pre, u ∈ pre') (h : D.Justified pre t) : D.Justified pre' t := by
  cases h with
  | prim h => exact Justified.prim h
  | zero h => exact Justified.zero h
  | one h hx => exact Justified.one h (hsub _ hx)
  | two h hx hy => exact Justified.two h (hsub _ hx) (hsub _ hy)

variable (D)

/-- `D.ProofList l`: `l` is a valid proof list, written in reverse chronological order — every
entry is justified by the entries after it. -/
inductive ProofList : List (Trip F A C) → Prop
  /-- The empty proof list. -/
  | nil : ProofList []
  /-- One more entry, justified by the entries derived before it. -/
  | cons {t : Trip F A C} {l : List (Trip F A C)} (hl : ProofList l) (h : D.Justified l t) :
      ProofList (t :: l)

variable {D}

/-- **Every entry of a proof list is provable.** -/
lemma ProofList.provable_of_mem : ∀ {l : List (Trip F A C)}, D.ProofList l →
    ∀ t ∈ l, D.Provable t.1 t.2.1 t.2.2 := by
  intro l h
  induction h with
  | nil => intro t ht; simp at ht
  | @cons t l hl hj ih =>
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · cases hj with
        | prim h => exact Provable.prim h
        | zero h => exact Provable.zero h
        | one h hx => exact Provable.one h (ih _ hx)
        | two h hx hy => exact Provable.two h (ih _ hx) (ih _ hy)
      · exact ih _ hu

/-- **Two proof lists concatenate to a proof list.**  (Recall that the head is the *last*
entry, so `l₂ ++ l₁` runs the proof `l₁` first and then the proof `l₂`.) -/
lemma ProofList.append {l₁ : List (Trip F A C)} (h₁ : D.ProofList l₁) :
    ∀ {l₂ : List (Trip F A C)}, D.ProofList l₂ → D.ProofList (l₂ ++ l₁) := by
  intro l₂ h₂
  induction h₂ with
  | nil => simpa using h₁
  | @cons t l hl hj ih =>
      exact ProofList.cons ih (hj.mono fun u hu => by simp [hu])

/-- **Every entry of a proof list is justified by the whole list.** -/
lemma ProofList.justified_of_mem : ∀ {l : List (Trip F A C)}, D.ProofList l →
    ∀ t ∈ l, D.Justified l t := by
  intro l h
  induction h with
  | nil => simp
  | @cons u l hl hj ih =>
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hj.mono fun v hv => by simp [hv]
      · exact (ih t ht).mono fun v hv => by simp [hv]

/-- **A triple that occurs in a proof list may be repeated at its end.** -/
lemma ProofList.cons_of_mem {l : List (Trip F A C)} (h : D.ProofList l) {t : Trip F A C}
    (ht : t ∈ l) : D.ProofList (t :: l) :=
  ProofList.cons h (h.justified_of_mem t ht)

/-- **Every provable triple heads a proof list.** -/
lemma exists_proofList_cons {s s' : Set F} {x : A ⊕ C} (h : D.Provable s x s') :
    ∃ l : List (Trip F A C), D.ProofList ((s, x, s') :: l) := by
  induction h with
  | @prim a s hp => exact ⟨[], ProofList.cons ProofList.nil (Justified.prim hp)⟩
  | @zero c s hb => exact ⟨[], ProofList.cons ProofList.nil (Justified.zero hb)⟩
  | @one c x s s' hb _ ih =>
      obtain ⟨l, hl⟩ := ih
      exact ⟨(s, x, s') :: l, ProofList.cons hl (Justified.one hb (by simp))⟩
  | @two c x y s s'' s' hb _ _ ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      refine ⟨((s'', y, s') :: ly) ++ ((s, x, s'') :: lx), ProofList.cons (hlx.append hly) ?_⟩
      exact Justified.two (s'' := s'') hb (by simp) (by simp)

/-! ### Removing duplicates

Since a justification only refers to *membership* in the earlier part of the list, duplicate
entries can be deleted. -/

open scoped Classical in
/-- **A proof list can be made duplicate-free**, keeping exactly the same entries. -/
lemma ProofList.dedup {l : List (Trip F A C)} (h : D.ProofList l) : D.ProofList l.dedup := by
  induction h with
  | nil => simpa using ProofList.nil
  | @cons t l hl hj ih =>
      by_cases ht : t ∈ l
      · rwa [List.dedup_cons_of_mem ht]
      · rw [List.dedup_cons_of_notMem ht]
        exact ProofList.cons ih (hj.mono fun u hu => List.mem_dedup.2 hu)

open scoped Classical in
/-- **Every provable triple occurs in a duplicate-free proof list.** -/
lemma exists_proofList_nodup {s s' : Set F} {x : A ⊕ C} (h : D.Provable s x s') :
    ∃ l : List (Trip F A C), D.ProofList l ∧ l.Nodup ∧ (s, x, s') ∈ l := by
  obtain ⟨l, hl⟩ := exists_proofList_cons h
  refine ⟨((s, x, s') :: l).dedup, hl.dedup, List.nodup_dedup _, ?_⟩
  exact List.mem_dedup.2 (by simp)

/-- **The number of proof tuples of a finite signature.** -/
lemma card_trip [Fintype F] [Fintype A] [Fintype C] :
    Fintype.card (Trip F A C) = 2 ^ Fintype.card F * ((Fintype.card A + Fintype.card C) *
      2 ^ Fintype.card F) := by
  simp [Fintype.card_set]

open scoped Classical in
/-- **Every provable triple occurs in a proof list of at most exponential length.**  This is the
statement of the source: "as there are only exponentially many states, this list can be at most
exponentially long".  The bound is the number of triples. -/
theorem exists_proofList_length_le [Fintype F] [Fintype A] [Fintype C] {s s' : Set F}
    {x : A ⊕ C} (h : D.Provable s x s') :
    ∃ l : List (Trip F A C), D.ProofList l ∧ (s, x, s') ∈ l ∧
      l.length ≤ 2 ^ Fintype.card F * ((Fintype.card A + Fintype.card C) *
        2 ^ Fintype.card F) := by
  obtain ⟨l, hl, hnd, hmem⟩ := exists_proofList_nodup h
  exact ⟨l, hl, hmem, card_trip (F := F) (A := A) (C := C) ▸ hnd.length_le_card⟩

end Domain

end HTN
