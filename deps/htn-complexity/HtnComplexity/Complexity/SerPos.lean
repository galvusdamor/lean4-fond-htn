import HtnComplexity.Complexity.SerScan
/-!
# Positions inside a serialised description

A *position* in a bit string is named here by a suffix `s` of it; the part that precedes the
position is then the complementary prefix `y.take (y.length - s.length)`.  This file assembles the
three facts that make positions usable on a serialised description:

* the alignment lemmas `HTN.Syn.entriesEnc_align` and `HTN.Syn.entry_split` — a prefix of a
  serialised list that is a sequence of complete entries really stops at an entry boundary, and
  an entry found there really is an entry of the list.  Both come from the prefix-freeness of the
  two layers (`HTN.Syn.bstr_parse`, `HTN.Syn.blist_parse`);
* `HTN.Syn.occB y E` — *does the entry `E` occur at an entry boundary of the serialised list that
  starts `y`?*  It is a nesting of `HTN.PTime.anyTailsB` over the positions of `y`, hence a
  predicate of Cobham's class (`HTN.Syn.cobhamB_occB`), and `HTN.Syn.occB_iff` identifies it with
  membership in the list: this is the *unbounded* comparison a finite-state scan cannot do.
-/

namespace HTN

namespace Syn

open PTime

/-! ### Cutting a string at a position -/

theorem take_compl (p s : List Bool) : (p ++ s).take ((p ++ s).length - s.length) = p := by
  simp

theorem suffix_take_append {s y : List Bool} (h : s <:+ y) :
    y.take (y.length - s.length) ++ s = y := by
  conv_rhs => rw [← List.take_append_drop (y.length - s.length) y]
  rw [← List.suffix_iff_eq_drop.1 h]

/-! ### Alignment -/

theorem blist_append_eq (l₁ l₂ : List (List Bool)) :
    blist (l₁ ++ l₂) = entriesEnc l₁ ++ blist l₂ := by
  induction l₁ with
  | nil => simp
  | cons x l ih => simp [blist_cons, entriesEnc_cons, ih]

/-- A prefix of a serialised list that is a sequence of complete entries stops at an entry
boundary. -/
theorem entriesEnc_align : ∀ (a : List (List Bool)) (r : List Bool) (l : List (List Bool))
    (z : List Bool), entriesEnc a ++ r = blist l ++ z →
      ∃ l₂, l = a ++ l₂ ∧ r = blist l₂ ++ z := by
  intro a
  induction a with
  | nil => exact fun r l z h => ⟨l, rfl, by simpa using h⟩
  | cons x a ih =>
    intro r l z h
    cases l with
    | nil =>
      rw [entriesEnc_cons] at h
      simp at h
    | cons y l =>
      rw [entriesEnc_cons, blist_cons] at h
      simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨hxy, hrest⟩ := bstr_parse h
      obtain ⟨l₂, hl, hr⟩ := ih r l z hrest
      exact ⟨l₂, by rw [hl, hxy]; rfl, hr⟩

/-- An entry found at an entry boundary of a serialised list is the first entry of what is left of
the list. -/
theorem entry_split {w s : List Bool} {l : List (List Bool)} {z : List Bool}
    (h : (true :: bstr w) ++ s = blist l ++ z) : ∃ l', l = w :: l' ∧ s = blist l' ++ z := by
  cases l with
  | nil => simp at h
  | cons y l =>
    rw [blist_cons] at h
    simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨hwy, hs⟩ := bstr_parse h
    exact ⟨l, by rw [hwy], hs⟩

/-- An entry that is a prefix of what a serialised list leaves at an entry boundary is an entry of
the list. -/
theorem mem_of_prefix_entry {w s : List Bool} {l : List (List Bool)} {z : List Bool}
    (hs : s = blist l ++ z) (hp : (true :: bstr w) <+: s) : w ∈ l := by
  obtain ⟨r, hr⟩ := hp
  rw [hs] at hr
  obtain ⟨l', hl, -⟩ := entry_split (by simpa using hr)
  rw [hl]
  exact List.mem_cons_self

/-! ### Occurrence of an entry -/

/-- The body of the occurrence test: the position `s` of `y` is an entry boundary, and the entry
`E` starts there. -/
def occTest (args : Args) : Bool :=
  entriesB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    decide (args.getD 2 [] <+: args.getD 0 [])

/-- **Does the entry `E` occur at an entry boundary of the serialised list that starts `y`?** -/
def occB (y E : List Bool) : Bool := anyTailsB occTest [y, E] y

theorem occB_eq_true {y E : List Bool} :
    occB y E = true ↔ ∃ s, s <:+ y ∧
      entriesB (y.take (y.length - s.length)) = true ∧ E <+: s := by
  rw [occB, anyTailsB_eq_true]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [occTest] at h
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨s, hs, h.1, h.2⟩
  · rintro ⟨s, hs, h1, h2⟩
    refine ⟨s, hs, ?_⟩
    rw [occTest]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-- **The occurrence test decides membership in the serialised list.** -/
theorem occB_iff (l : List (List Bool)) (z w : List Bool) :
    occB (blist l ++ z) (true :: bstr w) = true ↔ w ∈ l := by
  rw [occB_eq_true]
  constructor
  · rintro ⟨s, hs, hent, hpre⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 hent
    have hsplit : entriesEnc a ++ s = blist l ++ z := by
      rw [← ha]
      exact suffix_take_append hs
    obtain ⟨l₂, hl, hr⟩ := entriesEnc_align a s l z hsplit
    have : w ∈ l₂ := mem_of_prefix_entry hr hpre
    rw [hl]
    exact List.mem_append_right a this
  · intro hw
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hw
    refine ⟨blist (w :: l₂) ++ z, ?_, ?_, ?_⟩
    · refine ⟨entriesEnc l₁, ?_⟩
      rw [hl, blist_append_eq, List.append_assoc]
    · have hy : blist l ++ z = entriesEnc l₁ ++ (blist (w :: l₂) ++ z) := by
        rw [hl, blist_append_eq, List.append_assoc]
      rw [hy, take_compl]
      exact entriesB_iff.2 ⟨l₁, rfl⟩
    · refine ⟨blist l₂ ++ z, ?_⟩
      rw [blist_cons]
      simp

/-! ### Occurrence of a key -/

/-- The doubling that the self-delimiting form performs: every bit `b` becomes `true, b`. -/
def dbl (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

@[simp] theorem dbl_nil : dbl [] = [] := rfl

theorem dbl_cons (b : Bool) (w : List Bool) : dbl (b :: w) = true :: b :: dbl w := by
  simp [dbl]

theorem dbl_append (u v : List Bool) : dbl (u ++ v) = dbl u ++ dbl v := by
  simp [dbl]

theorem bstr_eq_dbl (w : List Bool) : bstr w = dbl w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [bstr_cons, dbl_cons, ih]; rfl

/-- A doubled string is a prefix of a doubled string followed by the terminator exactly when the
undoubled ones are prefixes. -/
theorem dbl_prefix_iff : ∀ (u v r : List Bool),
    dbl u <+: dbl v ++ false :: r ↔ u <+: v := by
  intro u
  induction u with
  | nil => exact fun v r => ⟨fun _ => List.nil_prefix, fun _ => by simp⟩
  | cons b u ih =>
    intro v r
    cases v with
    | nil =>
      constructor
      · intro h
        rw [dbl_cons] at h
        simp at h
      · intro h
        simp at h
    | cons a v =>
      rw [dbl_cons, dbl_cons]
      constructor
      · intro h
        obtain ⟨s, hs⟩ := h
        simp only [List.cons_append, List.cons.injEq, true_and] at hs
        obtain ⟨hba, hrest⟩ := hs
        have : dbl u <+: dbl v ++ false :: r := ⟨s, hrest⟩
        exact List.cons_prefix_cons.2 ⟨hba, (ih v r).1 this⟩
      · intro h
        obtain ⟨hba, hu⟩ := List.cons_prefix_cons.1 h
        obtain ⟨s, hs⟩ := (ih v r).2 hu
        exact ⟨s, by simp [hba, hs]⟩

/-- **The occurrence test with a key pattern decides whether some entry of the list starts with
the key.** -/
theorem occB_key_iff (l : List (List Bool)) (z u : List Bool) :
    occB (blist l ++ z) (true :: dbl u) = true ↔ ∃ v ∈ l, u <+: v := by
  rw [occB_eq_true]
  constructor
  · rintro ⟨s, hs, hent, hpre⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 hent
    have hsplit : entriesEnc a ++ s = blist l ++ z := by
      rw [← ha]
      exact suffix_take_append hs
    obtain ⟨l₂, hl, hr⟩ := entriesEnc_align a s l z hsplit
    cases l₂ with
    | nil =>
      rw [hr] at hpre
      simp only [blist_nil, List.cons_append, List.nil_append] at hpre
      obtain ⟨t, ht⟩ := hpre
      simp at ht
    | cons y l₂' =>
      rw [hr, blist_cons] at hpre
      obtain ⟨t, ht⟩ := hpre
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      have hy : dbl u <+: dbl y ++ false :: (blist l₂' ++ z) := by
        refine ⟨t, ?_⟩
        rw [ht, bstr_eq_dbl]
        simp
      refine ⟨y, ?_, (dbl_prefix_iff u y _).1 hy⟩
      rw [hl]
      exact List.mem_append_right a List.mem_cons_self
  · rintro ⟨v, hv, hu⟩
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hv
    refine ⟨blist (v :: l₂) ++ z, ?_, ?_, ?_⟩
    · refine ⟨entriesEnc l₁, ?_⟩
      rw [hl, blist_append_eq, List.append_assoc]
    · have hy : blist l ++ z = entriesEnc l₁ ++ (blist (v :: l₂) ++ z) := by
        rw [hl, blist_append_eq, List.append_assoc]
      rw [hy, take_compl]
      exact entriesB_iff.2 ⟨l₁, rfl⟩
    · have hpre : dbl u <+: dbl v ++ false :: (blist l₂ ++ z) := (dbl_prefix_iff u v _).2 hu
      obtain ⟨t, ht⟩ := hpre
      refine ⟨t, ?_⟩
      rw [blist_cons, bstr_eq_dbl]
      simp only [List.cons_append, List.cons.injEq, true_and]
      rw [ht]
      simp

/-! ### The occurrence test is a predicate of Cobham's class -/

theorem cobhamB_occTest : CobhamB occTest :=
  ((cobhamB_entriesB (cobham_trunc (Cobham.proj 0) (Cobham.proj 1))).and
      (cobhamB_isPrefix (Cobham.proj 2) (Cobham.proj 0))).of_eq fun args => by
    simp [occTest, proj]

theorem argDep_occTest : ArgDep 3 occTest := by
  intro args
  simp only [occTest, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

/-! ### Doubling is a function of Cobham's class -/

theorem length_dbl (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [dbl_cons]; simp [ih]; omega

/-- The doubling of the first argument. -/
def dblFn : Fn :=
  brnFn (fun _ => []) (compFn (consFn true) [compFn (consFn false) [proj 1]])
    (compFn (consFn true) [compFn (consFn true) [proj 1]])

theorem brnAux_dbl (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => []) (compFn (consFn true) [compFn (consFn false) [proj 1]])
      (compFn (consFn true) [compFn (consFn true) [proj 1]]) x v = dbl x := by
  intro x
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h : brnAux (fun _ => []) (compFn (consFn true) [compFn (consFn false) [proj 1]])
        (compFn (consFn true) [compFn (consFn true) [proj 1]]) (b :: x) v
        = true :: b :: brnAux (fun _ => []) (compFn (consFn true) [compFn (consFn false) [proj 1]])
          (compFn (consFn true) [compFn (consFn true) [proj 1]]) x v := by
      cases b <;> simp [brnAux, compFn, consFn, proj]
    rw [h, ih, dbl_cons]

theorem dblFn_apply (args : Args) : dblFn args = dbl (args.getD 0 []) := by
  show brnAux _ _ _ (args.getD 0 []) args.tail = _
  rw [brnAux_dbl]

theorem cobham_dblFn : Cobham dblFn := by
  have hstep : ∀ b : Bool, Cobham (compFn (consFn true) [compFn (consFn b) [proj 1]]) :=
    fun b => cobham_c1 (Cobham.cons true) (cobham_c1 (Cobham.cons b) (Cobham.proj 1))
  have hbd : Cobham (compFn (fun args : Args => args.getD 0 [] ++ args.getD 1 [])
      [proj 0, proj 0]) :=
    cobham_c2 cobham_append (Cobham.proj 0) (Cobham.proj 0)
  refine Cobham.brn Cobham.empty (hstep false) (hstep true) hbd ?_
  intro args
  rw [show brnFn (fun _ => ([] : List Bool))
    (compFn (consFn true) [compFn (consFn false) [proj 1]])
    (compFn (consFn true) [compFn (consFn true) [proj 1]]) = dblFn from rfl, dblFn_apply]
  simp [compFn, proj, length_dbl]
  omega

/-- **Doubling**, as a closure property. -/
theorem cobham_dbl {a : Fn} (ha : Cobham a) : Cobham fun args => dbl (a args) :=
  (cobham_c1 cobham_dblFn ha).of_eq' fun args => by simp [compFn, dblFn_apply]

/-- **The self-delimiting form of a computed string**. -/
theorem cobham_bstr {a : Fn} (ha : Cobham a) : Cobham fun args => bstr (a args) :=
  (cobham_c2 cobham_append (cobham_dbl ha) (cobham_const [false])).of_eq' fun args => by
    simp [compFn, bstr_eq_dbl]

theorem cobhamB_occB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => occB (a args) (b args) := by
  have h := cobhamB_anyTails cobhamB_occTest argDep_occTest
  exact (h.comp3 ha ha hb).of_eq fun args => by simp [occB]

end Syn

end HTN
