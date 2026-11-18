import HtnComplexity.Complexity.SerPos
/-!
# Reading the inclusion bit of the profile in polynomial time

The last component of the bounded profile `HTN.Syn.profB` of
`HtnCompilability/Computable/RootedDecide.lean` is the bit

    every goal fact outside the vocabulary of the domain already holds initially

(`HTN.Syn.profB_out_iff`).  Deciding it means comparing each numeral of the goal list with every
numeral of the initial list, which is exactly the kind of unbounded comparison that
`HtnComplexity/Complexity/SerPos.lean` made available inside Cobham's class.

`HTN.Syn.inclB facts x` is the algorithm, written as a nest of quantifiers over the positions of
the code `x`:

> there is **no** position of `x` at which a complete serialised list ends (so the position is the
> start of the goal list), followed by a sequence of complete entries (so we are at an entry
> boundary of the goal list), followed by one entry `E` which is neither one of the finitely many
> entries of `facts` nor occurs at an entry boundary of the list that starts `x` (the initial
> list).

`HTN.Syn.inclB_iff` proves that on a serialised description this is the bit above, and
`HTN.Syn.cobhamB_inclB` that it is a predicate of Cobham's class.
-/

namespace HTN

namespace Syn

open PTime

/-! ### The entry of a number -/

/-- A number as it appears inside a serialised list: an entry marker and the self-delimiting form
of its binary digits. -/
def entryEnc (n : ℕ) : List Bool := true :: bstr (bitsOfNat n)

theorem entryEnc_injective : Function.Injective entryEnc := by
  intro m n h
  rw [entryEnc, entryEnc, List.cons.injEq] at h
  obtain ⟨hb, -⟩ := bstr_parse (r := ([] : List Bool)) (s := ([] : List Bool)) (by simpa using h.2)
  exact bitsOfNat_injective hb

theorem serNatList_eq (l : List ℕ) : serNatList l = blist (l.map bitsOfNat) := rfl

/-! ### The algorithm -/

/-- The innermost test: the piece cut out between the positions `s₃ ⊑ s₂` is a single entry, that
entry is none of the fixed ones, and it does not occur in the list that starts `x`.  Arguments:
`s₃`, `s₂`, `x`. -/
def inclTest3 (df : List (List Bool)) (args : Args) : Bool :=
  entryB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    !(df.any fun e =>
      decide (e = (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length))) &&
    !(occB (args.getD 2 [])
      ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)))

/-- The middle test: the piece between `s₂ ⊑ s₁` is a sequence of complete entries, and some
position of `s₂` cuts out a bad entry.  Arguments: `s₂`, `s₁`, `x`. -/
def inclTest2 (df : List (List Bool)) (args : Args) : Bool :=
  entriesB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    anyTailsB (inclTest3 df) [args.getD 0 [], args.getD 2 []] (args.getD 0 [])

/-- The outer test: the piece before `s₁` is a complete serialised list.  Arguments: `s₁`, `x`. -/
def inclTest1 (df : List (List Bool)) (args : Args) : Bool :=
  blistB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    anyTailsB (inclTest2 df) [args.getD 0 [], args.getD 1 []] (args.getD 0 [])

/-- **Is there a bad entry?** -/
def badB (df : List (List Bool)) (x : List Bool) : Bool := anyTailsB (inclTest1 df) [x] x

/-- **The inclusion bit.** -/
def inclB (df : List (List Bool)) (x : List Bool) : Bool := !badB df x

/-! ### Correctness -/

theorem badB_eq_true {df : List (List Bool)} {x : List Bool} :
    badB df x = true ↔ ∃ s₁, s₁ <:+ x ∧
      blistB (x.take (x.length - s₁.length)) = true ∧
      ∃ s₂, s₂ <:+ s₁ ∧ entriesB (s₁.take (s₁.length - s₂.length)) = true ∧
        ∃ s₃, s₃ <:+ s₂ ∧
          (entryB (s₂.take (s₂.length - s₃.length)) = true ∧
            (df.any fun e => decide (e = s₂.take (s₂.length - s₃.length))) = false ∧
            occB x (s₂.take (s₂.length - s₃.length)) = false) := by
  rw [badB, anyTailsB_eq_true]
  constructor
  · rintro ⟨s₁, hs₁, h⟩
    rw [inclTest1] at h
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
    obtain ⟨hb, h2⟩ := h
    rw [anyTailsB_eq_true] at h2
    obtain ⟨s₂, hs₂, h2⟩ := h2
    rw [inclTest2] at h2
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h2
    obtain ⟨he, h3⟩ := h2
    rw [anyTailsB_eq_true] at h3
    obtain ⟨s₃, hs₃, h3⟩ := h3
    rw [inclTest3] at h3
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h3
    exact ⟨s₁, hs₁, hb, s₂, hs₂, he, s₃, hs₃, h3.1.1, h3.1.2, h3.2⟩
  · rintro ⟨s₁, hs₁, hb, s₂, hs₂, he, s₃, hs₃, h1, h2, h3⟩
    refine ⟨s₁, hs₁, ?_⟩
    rw [inclTest1]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
    refine ⟨hb, ?_⟩
    rw [anyTailsB_eq_true]
    refine ⟨s₂, hs₂, ?_⟩
    rw [inclTest2]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
    refine ⟨he, ?_⟩
    rw [anyTailsB_eq_true]
    refine ⟨s₃, hs₃, ?_⟩
    rw [inclTest3]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨⟨h1, h2⟩, h3⟩

/-- **The algorithm finds a bad entry exactly when there is a goal fact that neither belongs to
the fixed list nor holds initially.** -/
theorem badB_iff (facts : List ℕ) (q : InstDesc) :
    badB (facts.map entryEnc) (instSer q) = true ↔
      ∃ f ∈ q.goalList, f ∉ facts ∧ f ∉ q.initList := by
  set I : List (List Bool) := q.initList.map bitsOfNat with hI
  set G : List (List Bool) := q.goalList.map bitsOfNat with hG
  set z : List Bool := tnSer q.tnI with hz
  have hx : instSer q = blist I ++ (blist G ++ z) := by
    rw [instSer, serNatList_eq, serNatList_eq]
    simp [hI, hG, hz]
  rw [badB_eq_true]
  constructor
  · rintro ⟨s₁, hs₁, hb, s₂, hs₂, he, s₃, hs₃, hent, hdf, hocc⟩
    -- the first cut is the end of the initial list
    obtain ⟨l, hl⟩ := blistB_iff.1 hb
    have hcut₁ : blist l ++ s₁ = blist I ++ (blist G ++ z) := by
      rw [← hl, ← hx]
      exact suffix_take_append hs₁
    obtain ⟨-, hs₁eq⟩ := blist_parse hcut₁
    -- the second cut is an entry boundary of the goal list
    obtain ⟨a, ha⟩ := entriesB_iff.1 he
    have hcut₂ : entriesEnc a ++ s₂ = blist G ++ z := by
      rw [← ha, ← hs₁eq]
      exact suffix_take_append hs₂
    obtain ⟨G₂, hGeq, hs₂eq⟩ := entriesEnc_align a s₂ G z hcut₂
    -- the entry found there is an entry of the goal list
    obtain ⟨w, hw⟩ := entryB_iff.1 hent
    rw [hw] at hdf hocc
    have hcut₃ : (true :: bstr w) ++ s₃ = blist G₂ ++ z := by
      rw [← hw, ← hs₂eq]
      exact suffix_take_append hs₃
    obtain ⟨G₂', hG₂, -⟩ := entry_split hcut₃
    have hwG : w ∈ G := by
      rw [hGeq, hG₂]
      exact List.mem_append_right a List.mem_cons_self
    obtain ⟨f, hf, hfw⟩ := List.mem_map.1 (hG ▸ hwG)
    refine ⟨f, hf, ?_, ?_⟩
    · intro hfacts
      have hany : ((facts.map entryEnc).any fun e => decide (e = true :: bstr w)) = true :=
        List.any_eq_true.2 ⟨entryEnc f, List.mem_map_of_mem hfacts, by
          simp [entryEnc, hfw]⟩
      rw [hany] at hdf
      exact absurd hdf (by simp)
    · intro hinit
      have hwI : w ∈ I := by
        rw [hI, ← hfw]
        exact List.mem_map_of_mem hinit
      have hoc : occB (instSer q) (true :: bstr w) = true := by
        rw [hx]
        exact (occB_iff I (blist G ++ z) w).2 hwI
      rw [hoc] at hocc
      exact absurd hocc (by simp)
  · rintro ⟨f, hf, hfacts, hinit⟩
    set w : List Bool := bitsOfNat f with hwdef
    have hwG : w ∈ G := by
      rw [hG, hwdef]
      exact List.mem_map_of_mem hf
    obtain ⟨G₁, G₂', hGsplit⟩ := List.append_of_mem hwG
    have hs₁eq : instSer q = blist I ++ (blist G ++ z) := hx
    have hgoal : blist G ++ z = entriesEnc G₁ ++ (blist (w :: G₂') ++ z) := by
      rw [hGsplit, blist_append_eq, List.append_assoc]
    have hentry : blist (w :: G₂') ++ z = (true :: bstr w) ++ (blist G₂' ++ z) := by
      rw [blist_cons]
      simp
    refine ⟨blist G ++ z, ⟨blist I, hs₁eq.symm⟩, ?_,
      blist (w :: G₂') ++ z, ⟨entriesEnc G₁, hgoal.symm⟩, ?_,
      blist G₂' ++ z, ⟨true :: bstr w, hentry.symm⟩, ?_, ?_, ?_⟩
    · rw [hs₁eq, take_compl]
      exact blistB_iff.2 ⟨I, rfl⟩
    · rw [hgoal, take_compl]
      exact entriesB_iff.2 ⟨G₁, rfl⟩
    · rw [hentry, take_compl]
      exact entryB_iff.2 ⟨w, rfl⟩
    · rw [hentry, take_compl]
      refine List.any_eq_false.2 ?_
      rintro e he
      obtain ⟨f', hf', rfl⟩ := List.mem_map.1 he
      simp only [decide_eq_true_eq]
      intro hEq
      exact hfacts (by
        have : entryEnc f' = entryEnc f := by rw [hEq, entryEnc, hwdef]
        rw [← entryEnc_injective this]
        exact hf')
    · rw [hentry, take_compl, hx]
      have hnI : ¬ (w ∈ I) := by
        intro hwI
        obtain ⟨f', hf', hfe⟩ := List.mem_map.1 (hI ▸ hwI)
        have hff : f' = f := bitsOfNat_injective (by rw [hfe, hwdef])
        exact hinit (hff ▸ hf')
      simpa using fun hc => hnI ((occB_iff I (blist G ++ z) w).1 hc)

/-- **The inclusion bit is what the profile asks for.** -/
theorem inclB_iff (facts : List ℕ) (q : InstDesc) :
    inclB (facts.map entryEnc) (instSer q) = true ↔
      ∀ f ∈ q.goalList, f ∉ facts → f ∈ q.initList := by
  rw [inclB, Bool.not_eq_true', ← Bool.not_eq_true, badB_iff]
  push_neg
  rfl

/-! ### The algorithm is a predicate of Cobham's class -/

/-- Comparison with finitely many fixed strings. -/
theorem cobhamB_anyConst (df : List (List Bool)) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => df.any fun e => decide (e = a args) := by
  induction df with
  | nil => exact (cobhamB_const false).of_eq fun args => by simp
  | cons e df ih =>
    exact ((cobhamB_eqStr (cobham_const e) ha).or ih).of_eq fun args => by simp

theorem cobhamB_inclTest3 (df : List (List Bool)) : CobhamB (inclTest3 df) := by
  have hE : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  exact (((cobhamB_entryB hE).and (cobhamB_anyConst df hE).not).and
    (cobhamB_occB (Cobham.proj 2) hE).not).of_eq fun args => by simp [inclTest3, proj]

theorem argDep_inclTest3 (df : List (List Bool)) : ArgDep 3 (inclTest3 df) := by
  intro args
  simp only [inclTest3, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_inclTest2 (df : List (List Bool)) : CobhamB (inclTest2 df) := by
  have hpre : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  have hany := (cobhamB_anyTails (cobhamB_inclTest3 df) (argDep_inclTest3 df)).comp3
    (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 2)
  exact ((cobhamB_entriesB hpre).and hany).of_eq fun args => by simp [inclTest2, proj]

theorem argDep_inclTest2 (df : List (List Bool)) : ArgDep 3 (inclTest2 df) := by
  intro args
  simp only [inclTest2, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_inclTest1 (df : List (List Bool)) : CobhamB (inclTest1 df) := by
  have hpre : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  have hany := (cobhamB_anyTails (cobhamB_inclTest2 df) (argDep_inclTest2 df)).comp3
    (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 1)
  exact ((cobhamB_blistB hpre).and hany).of_eq fun args => by simp [inclTest1, proj]

theorem argDep_inclTest1 (df : List (List Bool)) : ArgDep 2 (inclTest1 df) := by
  intro args
  simp only [inclTest1, getD_padArgs (by norm_num : (0 : ℕ) < 2),
    getD_padArgs (by norm_num : (1 : ℕ) < 2)]

theorem cobhamB_badB (df : List (List Bool)) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => badB df (a args) :=
  ((cobhamB_anyTails (cobhamB_inclTest1 df) (argDep_inclTest1 df)).comp2 ha ha).of_eq
    fun args => by simp [badB]

/-- **The inclusion bit is decided in polynomial time.** -/
theorem cobhamB_inclB (df : List (List Bool)) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => inclB df (a args) :=
  (cobhamB_badB df ha).not.of_eq fun args => by simp [inclB]

end Syn

end HTN
