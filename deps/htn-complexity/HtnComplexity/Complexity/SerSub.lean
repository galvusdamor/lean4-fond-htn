import HtnComplexity.Complexity.SerIncl
/-!
# Inclusion of one serialised list in another, in polynomial time

`HtnComplexity/Complexity/SerIncl.lean` decides one concrete inclusion — the last bit of the
bounded profile — with the pattern "quantify over the positions of the code, cut out an entry
there, and test it".  The machine of `ComplexityTheory/Space/Model.lean` needs the *general*
primitive behind it, for **computed** arguments:

    HTN.Syn.subListB y z  —  does every entry of the serialised list that starts `y` occur in the
                             serialised list that starts `z`?

* `HTN.Syn.missB_iff` — on serialised lists it is what it should be:
  `missB (blist l ++ z₁) (blist m ++ z₂) = true ↔ ∃ w ∈ l, w ∉ m`, hence
  `HTN.Syn.subListB_iff : subListB (blist l ++ z₁) (blist m ++ z₂) = true ↔ ∀ w ∈ l, w ∈ m`;
* `HTN.Syn.cobhamB_subListB` — it is a predicate of Cobham's class, in the closure form: the two
  arguments may be any functions of the class.

This is the test the acceptance condition of the planner ("the goal facts are all in the
configuration") and its transition relation ("the precondition of the row is in the
configuration") are built from.
-/

namespace HTN

namespace Syn

open PTime

/-! ### The algorithm -/

/-- The inner test: the piece cut out between the positions `s₃ ⊑ s₂` is a single entry and it
does not occur in the serialised list that starts `z`.  Arguments: `s₃`, `s₂`, `z`. -/
def subTest2 (args : Args) : Bool :=
  entryB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    !(occB (args.getD 2 [])
      ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)))

/-- The outer test: the piece before `s₂` is a sequence of complete entries, and some position of
`s₂` cuts out a missing entry.  Arguments: `s₂`, `y`, `z`. -/
def subTest1 (args : Args) : Bool :=
  entriesB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    anyTailsB subTest2 [args.getD 0 [], args.getD 2 []] (args.getD 0 [])

/-- **Is some entry of the serialised list that starts `y` missing from the one that starts
`z`?** -/
def missB (y z : List Bool) : Bool := anyTailsB subTest1 [y, z] y

/-- **Does every entry of the serialised list that starts `y` occur in the one that starts
`z`?** -/
def subListB (y z : List Bool) : Bool := !missB y z

/-! ### Correctness -/

theorem missB_eq_true {y z : List Bool} :
    missB y z = true ↔ ∃ s₂, s₂ <:+ y ∧ entriesB (y.take (y.length - s₂.length)) = true ∧
      ∃ s₃, s₃ <:+ s₂ ∧ entryB (s₂.take (s₂.length - s₃.length)) = true ∧
        occB z (s₂.take (s₂.length - s₃.length)) = false := by
  rw [missB, anyTailsB_eq_true]
  constructor
  · rintro ⟨s₂, hs₂, h⟩
    rw [subTest1] at h
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
    obtain ⟨he, h3⟩ := h
    rw [anyTailsB_eq_true] at h3
    obtain ⟨s₃, hs₃, h3⟩ := h3
    rw [subTest2] at h3
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h3
    exact ⟨s₂, hs₂, he, s₃, hs₃, h3.1, h3.2⟩
  · rintro ⟨s₂, hs₂, he, s₃, hs₃, h1, h2⟩
    refine ⟨s₂, hs₂, ?_⟩
    rw [subTest1]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
    refine ⟨he, ?_⟩
    rw [anyTailsB_eq_true]
    refine ⟨s₃, hs₃, ?_⟩
    rw [subTest2]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨h1, h2⟩

/-- **The algorithm finds a missing entry exactly when one of the entries of the first list is
not an entry of the second.** -/
theorem missB_iff (l m : List (List Bool)) (z₁ z₂ : List Bool) :
    missB (blist l ++ z₁) (blist m ++ z₂) = true ↔ ∃ w ∈ l, w ∉ m := by
  rw [missB_eq_true]
  constructor
  · rintro ⟨s₂, hs₂, he, s₃, hs₃, hent, hocc⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 he
    have hcut₂ : entriesEnc a ++ s₂ = blist l ++ z₁ := by
      rw [← ha]
      exact suffix_take_append hs₂
    obtain ⟨l₂, hleq, hs₂eq⟩ := entriesEnc_align a s₂ l z₁ hcut₂
    obtain ⟨w, hw⟩ := entryB_iff.1 hent
    rw [hw] at hocc
    have hcut₃ : (true :: bstr w) ++ s₃ = blist l₂ ++ z₁ := by
      rw [← hw, ← hs₂eq]
      exact suffix_take_append hs₃
    obtain ⟨l₂', hl₂, -⟩ := entry_split hcut₃
    have hwl : w ∈ l := by
      rw [hleq, hl₂]
      exact List.mem_append_right a List.mem_cons_self
    refine ⟨w, hwl, fun hwm => ?_⟩
    rw [(occB_iff m z₂ w).2 hwm] at hocc
    exact absurd hocc (by simp)
  · rintro ⟨w, hwl, hwm⟩
    obtain ⟨l₁, l₂, hlsplit⟩ := List.append_of_mem hwl
    have hlist : blist l ++ z₁ = entriesEnc l₁ ++ (blist (w :: l₂) ++ z₁) := by
      rw [hlsplit, blist_append_eq, List.append_assoc]
    have hentry : blist (w :: l₂) ++ z₁ = (true :: bstr w) ++ (blist l₂ ++ z₁) := by
      rw [blist_cons]
      simp
    refine ⟨blist (w :: l₂) ++ z₁, ⟨entriesEnc l₁, hlist.symm⟩, ?_,
      blist l₂ ++ z₁, ⟨true :: bstr w, hentry.symm⟩, ?_, ?_⟩
    · rw [hlist, take_compl]
      exact entriesB_iff.2 ⟨l₁, rfl⟩
    · rw [hentry, take_compl]
      exact entryB_iff.2 ⟨w, rfl⟩
    · rw [hentry, take_compl]
      simpa using fun hc => hwm ((occB_iff m z₂ w).1 hc)

/-- **The inclusion test is what it should be on serialised lists.** -/
theorem subListB_iff (l m : List (List Bool)) (z₁ z₂ : List Bool) :
    subListB (blist l ++ z₁) (blist m ++ z₂) = true ↔ ∀ w ∈ l, w ∈ m := by
  rw [subListB, Bool.not_eq_true', ← Bool.not_eq_true, missB_iff]
  push_neg
  rfl

/-! ### The algorithm is a predicate of Cobham's class -/

theorem cobhamB_subTest2 : CobhamB subTest2 := by
  have hE : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  exact ((cobhamB_entryB hE).and (cobhamB_occB (Cobham.proj 2) hE).not).of_eq fun args => by
    simp [subTest2, proj]

theorem argDep_subTest2 : ArgDep 3 subTest2 := by
  intro args
  simp only [subTest2, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_subTest1 : CobhamB subTest1 := by
  have hpre : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  have hany := (cobhamB_anyTails cobhamB_subTest2 argDep_subTest2).comp3
    (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 2)
  exact ((cobhamB_entriesB hpre).and hany).of_eq fun args => by simp [subTest1, proj]

theorem argDep_subTest1 : ArgDep 3 subTest1 := by
  intro args
  simp only [subTest1, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_missB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => missB (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_subTest1 argDep_subTest1).comp3 ha ha hb).of_eq fun args => by
    simp [missB]

/-- **The inclusion of one serialised list in another is decided in polynomial time**, for
computed arguments. -/
theorem cobhamB_subListB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => subListB (a args) (b args) :=
  (cobhamB_missB ha hb).not.of_eq fun args => by simp [subListB]

end Syn

end HTN
