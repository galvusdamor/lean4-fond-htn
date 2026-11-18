import HtnComplexity.Complexity.SerIncl
/-!
# Looking a label up in polynomial time

The third component of the bounded profile `HTN.Syn.profB` compares a fixed compound task name
with the *root name* of the instance, and the root name is read off the label list of the initial
task network by a **lookup**: `HTN.Syn.TnDesc.labelList` takes the *first* entry of the label list
whose key is the identifier asked for.

This file decides a lookup on the serialisation.  A label is serialised as
`bstr (bits i) ++ b :: bstr (bits n)`, so an entry of the label list with key `i` is one whose
content starts with `bstr (bits i)`; the *first* such entry is the one at whose position no
earlier entry has that key, and the earlier entries form the serialised list
`prefix ++ [false]`.  `HTN.Syn.firstLabelB K y w` implements this:

> there is an entry boundary of the serialised list `y` at which the content starts with `w ++ K`,
> and no entry of the list of earlier entries has a content starting with `w`.

`HTN.Syn.firstLabelB_lookup_iff` identifies it with `List.lookup`, and
`HTN.Syn.cobhamB_firstLabelB` places it in Cobham's class.
-/

namespace HTN

namespace Syn

open PTime

/-! ### Prefixes of the two layers -/

/-- A self-delimiting string is a prefix of another one, possibly followed by junk, exactly when
the two strings are equal. -/
theorem bstr_prefix_iff (u v r : List Bool) : bstr u <+: bstr v ++ r ↔ u = v := by
  constructor
  · rintro ⟨t, ht⟩
    exact (bstr_parse ht).1
  · rintro rfl
    exact List.prefix_append _ _

/-- A key pattern is a prefix of a serialised list exactly when the list begins with an entry
having that key. -/
theorem key_prefix_iff (u : List Bool) (l : List (List Bool)) (z : List Bool) :
    (true :: dbl u) <+: blist l ++ z ↔ ∃ v l', l = v :: l' ∧ u <+: v := by
  cases l with
  | nil =>
    constructor
    · rintro ⟨t, ht⟩
      simp at ht
    · rintro ⟨v, l', hv, -⟩
      simp at hv
  | cons v l' =>
    constructor
    · rintro ⟨t, ht⟩
      rw [blist_cons] at ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      refine ⟨v, l', rfl, (dbl_prefix_iff u v (blist l' ++ z)).1 ⟨t, ?_⟩⟩
      rw [ht, bstr_eq_dbl]
      simp
    · rintro ⟨v₀, l₀, hv, hu⟩
      obtain ⟨hv1, hv2⟩ := List.cons_eq_cons.mp hv
      subst hv1
      subst hv2
      obtain ⟨t, ht⟩ := (dbl_prefix_iff u v (blist l' ++ z)).2 hu
      refine ⟨t, ?_⟩
      rw [blist_cons, bstr_eq_dbl]
      simp only [List.cons_append, List.cons.injEq, true_and]
      rw [ht]
      simp

/-! ### The lookup test -/

/-- The body of the lookup test.  Arguments: the position `t`, the serialised list `y`, the key
`w`. -/
def lblTest (K : List Bool) (args : Args) : Bool :=
  entriesB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    decide ((true :: dbl (args.getD 2 [] ++ K)) <+: args.getD 0 []) &&
    !(occB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) ++ [false])
      (true :: dbl (args.getD 2 [])))

/-- **The first entry of the serialised list `y` whose content starts with the key `w` has a
content starting with `w ++ K`.** -/
def firstLabelB (K y w : List Bool) : Bool := anyTailsB (lblTest K) [y, w] y

theorem firstLabelB_eq_true {K y w : List Bool} :
    firstLabelB K y w = true ↔ ∃ t, t <:+ y ∧
      entriesB (y.take (y.length - t.length)) = true ∧
      (true :: dbl (w ++ K)) <+: t ∧
      occB (y.take (y.length - t.length) ++ [false]) (true :: dbl w) = false := by
  rw [firstLabelB, anyTailsB_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    rw [lblTest] at h
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact ⟨t, ht, h.1.1, h.1.2, h.2⟩
  · rintro ⟨t, ht, h1, h2, h3⟩
    refine ⟨t, ht, ?_⟩
    rw [lblTest]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨⟨h1, h2⟩, h3⟩

/-- **The lookup test finds the first entry with the given key.** -/
theorem firstLabelB_iff (K : List Bool) (l : List (List Bool)) (w : List Bool) :
    firstLabelB K (blist l) w = true ↔
      ∃ l₁ v l₂, l = l₁ ++ v :: l₂ ∧ (w ++ K) <+: v ∧ ∀ v' ∈ l₁, ¬ (w <+: v') := by
  rw [firstLabelB_eq_true]
  constructor
  · rintro ⟨t, ht, hent, hpre, hocc⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 hent
    have hsplit : entriesEnc a ++ t = blist l ++ [] := by
      rw [← ha, List.append_nil]
      exact suffix_take_append ht
    obtain ⟨l₂, hl, hr⟩ := entriesEnc_align a t l [] hsplit
    rw [hr] at hpre
    obtain ⟨v, l₂', hl₂, hv⟩ := (key_prefix_iff _ l₂ []).1 hpre
    refine ⟨a, v, l₂', by rw [hl, hl₂], hv, ?_⟩
    intro v' hv' hvw
    have hpre' : (blist l).take ((blist l).length - t.length) ++ [false] = blist a := by
      rw [ha, blist_eq_entriesEnc]
    rw [hpre'] at hocc
    have : occB (blist a ++ []) (true :: dbl w) = true :=
      (occB_key_iff a [] w).2 ⟨v', hv', hvw⟩
    rw [List.append_nil] at this
    rw [this] at hocc
    exact absurd hocc (by simp)
  · rintro ⟨l₁, v, l₂, hl, hv, hno⟩
    have hy : blist l = entriesEnc l₁ ++ blist (v :: l₂) := by
      rw [hl, blist_append_eq]
    refine ⟨blist (v :: l₂), ⟨entriesEnc l₁, hy.symm⟩, ?_, ?_, ?_⟩
    · rw [hy, take_compl]
      exact entriesB_iff.2 ⟨l₁, rfl⟩
    · have hk := (key_prefix_iff (w ++ K) (v :: l₂) []).2 ⟨v, l₂, rfl, hv⟩
      simpa using hk
    · rw [hy, take_compl, ← blist_eq_entriesEnc]
      have : ¬ (occB (blist l₁ ++ []) (true :: dbl w) = true) := by
        rw [occB_key_iff]
        rintro ⟨v', hv', hvw⟩
        exact hno v' hv' hvw
      simpa using this

/-! ### The lookup test is the lookup -/

theorem serLbl_eq (j : ℕ) (b : Bool) (n : ℕ) :
    serLbl (j, b, n) = bstr (bitsOfNat j) ++ b :: bstr (bitsOfNat n) := rfl

theorem bstr_prefix_serLbl_iff (i j : ℕ) (b : Bool) (n : ℕ) :
    bstr (bitsOfNat i) <+: serLbl (j, b, n) ↔ i = j := by
  rw [serLbl_eq, bstr_prefix_iff]
  exact ⟨fun h => bitsOfNat_injective h, fun h => by rw [h]⟩

theorem bstr_append_prefix_serLbl_iff (i j : ℕ) (b : Bool) (n : ℕ) (K : List Bool) :
    (bstr (bitsOfNat i) ++ K) <+: serLbl (j, b, n) ↔
      i = j ∧ K <+: (b :: bstr (bitsOfNat n)) := by
  rw [serLbl_eq]
  constructor
  · intro h
    have h0 : bstr (bitsOfNat i) <+: bstr (bitsOfNat j) ++ (b :: bstr (bitsOfNat n)) :=
      (List.prefix_append _ _).trans h
    have hij : i = j := bitsOfNat_injective ((bstr_prefix_iff _ _ _).1 h0)
    subst hij
    exact ⟨rfl, (List.prefix_append_right_inj _).1 h⟩
  · rintro ⟨rfl, hK⟩
    exact (List.prefix_append_right_inj _).2 hK

/-- **The string-level first match is the lookup in the label list.** -/
theorem serLbl_first_iff (lbl : List (ℕ × Bool × ℕ)) (i : ℕ) (K : List Bool) :
    (∃ l₁ v l₂, lbl.map serLbl = l₁ ++ v :: l₂ ∧ (bstr (bitsOfNat i) ++ K) <+: v ∧
      ∀ v' ∈ l₁, ¬ (bstr (bitsOfNat i) <+: v')) ↔
      (match lbl.lookup i with
        | some (b, n) => K <+: (b :: bstr (bitsOfNat n))
        | none => False) := by
  induction lbl with
  | nil =>
    constructor
    · rintro ⟨l₁, v, l₂, hl, -, -⟩
      exact absurd hl (by cases l₁ <;> simp)
    · intro h
      exact h.elim
  | cons p rest ih =>
    obtain ⟨j, b, n⟩ := p
    by_cases hij : j = i
    · subst hij
      rw [show ((j, b, n) :: rest).lookup j = some (b, n) from by simp]
      constructor
      · rintro ⟨l₁, v, l₂, hl, hv, hno⟩
        cases l₁ with
        | nil =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at hl
          rw [← hl.1] at hv
          exact ((bstr_append_prefix_serLbl_iff j j b n K).1 hv).2
        | cons v' l₁' =>
          exfalso
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at hl
          refine hno v' (by simp) ?_
          rw [← hl.1]
          exact (bstr_prefix_serLbl_iff j j b n).2 rfl
      · intro h
        exact ⟨[], serLbl (j, b, n), rest.map serLbl, by simp,
          (bstr_append_prefix_serLbl_iff j j b n K).2 ⟨rfl, h⟩, by simp⟩
    · have hne : (i == j) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => hij h.symm
      rw [show ((j, b, n) :: rest).lookup i = rest.lookup i from by
        simp [List.lookup_cons, hne], ← ih]
      constructor
      · rintro ⟨l₁, v, l₂, hl, hv, hno⟩
        cases l₁ with
        | nil =>
          exfalso
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at hl
          rw [← hl.1] at hv
          exact hij (((bstr_append_prefix_serLbl_iff i j b n K).1 hv).1).symm
        | cons v' l₁' =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at hl
          exact ⟨l₁', v, l₂, hl.2, hv, fun v'' hv'' => hno v'' (by simp [hv''])⟩
      · rintro ⟨l₁, v, l₂, hl, hv, hno⟩
        refine ⟨serLbl (j, b, n) :: l₁, v, l₂, by simp [hl], hv, ?_⟩
        intro v'' hv''
        rcases List.mem_cons.1 hv'' with rfl | hv''
        · intro hc
          exact hij ((bstr_prefix_serLbl_iff i j b n).1 hc).symm
        · exact hno v'' hv''

/-- **Is the identifier labelled with a compound task?** -/
def compoundB (ylbl w : List Bool) : Bool := firstLabelB [true] ylbl w

/-- **Is the identifier labelled with the compound task `c`?** -/
def namedB (c : ℕ) (ylbl w : List Bool) : Bool :=
  firstLabelB (true :: bstr (bitsOfNat c)) ylbl w

theorem compoundB_iff (lbl : List (ℕ × Bool × ℕ)) (i : ℕ) :
    compoundB (blist (lbl.map serLbl)) (bstr (bitsOfNat i)) = true ↔
      TnDesc.labelList true lbl i ≠ [] := by
  rw [compoundB, firstLabelB_iff, serLbl_first_iff, TnDesc.labelList_eq]
  rcases h : lbl.lookup i with _ | ⟨b, n⟩
  · simp
  · cases b <;> simp [List.cons_prefix_cons]

theorem namedB_iff (lbl : List (ℕ × Bool × ℕ)) (i c : ℕ) :
    namedB c (blist (lbl.map serLbl)) (bstr (bitsOfNat i)) = true ↔
      TnDesc.labelList true lbl i = [c] := by
  rw [namedB, firstLabelB_iff, serLbl_first_iff, TnDesc.labelList_eq]
  rcases h : lbl.lookup i with _ | ⟨b, n⟩
  · simp
  · have hb : bstr (bitsOfNat c) <+: bstr (bitsOfNat n) ↔ c = n := by
      rw [show bstr (bitsOfNat n) = bstr (bitsOfNat n) ++ [] from (List.append_nil _).symm,
        bstr_prefix_iff]
      exact ⟨fun h => bitsOfNat_injective h, fun h => by rw [h]⟩
    cases b
    · simp [List.cons_prefix_cons]
    · simp [List.cons_prefix_cons, hb, eq_comm]

/-! ### The lookup test is a predicate of Cobham's class -/

theorem cobham_consTrue {a : Fn} (ha : Cobham a) : Cobham fun args => true :: a args :=
  (cobham_c1 (Cobham.cons true) ha).of_eq' fun args => by simp [compFn, consFn]

theorem cobhamB_lblTest (K : List Bool) : CobhamB (lblTest K) := by
  have hpre : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  have hpat : Cobham fun args : Args => true :: dbl (args.getD 2 [] ++ K) :=
    cobham_consTrue (cobham_dbl ((cobham_c2 cobham_append (Cobham.proj 2)
      (cobham_const K)).of_eq' fun args => by simp [compFn, proj]))
  have hkey : Cobham fun args : Args => true :: dbl (args.getD 2 []) :=
    cobham_consTrue (cobham_dbl ((Cobham.proj 2).of_eq' fun args => by simp [proj]))
  have hregion : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) ++ [false] :=
    (cobham_c2 cobham_append hpre (cobham_const [false])).of_eq' fun args => by simp [compFn]
  have h1 : CobhamB fun args : Args =>
      entriesB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) :=
    cobhamB_entriesB hpre
  have h2 : CobhamB fun args : Args =>
      decide ((true :: dbl (args.getD 2 [] ++ K)) <+: args.getD 0 []) :=
    (cobhamB_isPrefix hpat (Cobham.proj 0)).of_eq fun args => by simp [proj]
  have h3 : CobhamB fun args : Args =>
      occB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) ++ [false])
        (true :: dbl (args.getD 2 [])) := cobhamB_occB hregion hkey
  exact ((h1.and h2).and h3.not).of_eq fun args => by simp [lblTest]

theorem argDep_lblTest (K : List Bool) : ArgDep 3 (lblTest K) := by
  intro args
  simp only [lblTest, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_firstLabelB (K : List Bool) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => firstLabelB K (a args) (b args) :=
  ((cobhamB_anyTails (cobhamB_lblTest K) (argDep_lblTest K)).comp3 ha ha hb).of_eq
    fun args => by simp [firstLabelB]

theorem cobhamB_compoundB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => compoundB (a args) (b args) := cobhamB_firstLabelB _ ha hb

theorem cobhamB_namedB (c : ℕ) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => namedB c (a args) (b args) := cobhamB_firstLabelB _ ha hb

end Syn

end HTN
