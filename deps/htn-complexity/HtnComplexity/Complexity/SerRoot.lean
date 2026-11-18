import HtnComplexity.Complexity.SerLookup
import HtnComplexity.Complexity.SerialMember
import HtnComplexity.Computable.Rooted
/-!
# Reading the root name in polynomial time

The third component of the bounded profile `HTN.Syn.profB` compares the fixed method heads of a
domain description with the **root name** of the instance,

    rootName q = (q.tnI.ids.flatMap (TnDesc.labelList true q.tnI.lbl)).headI,

the name of the first identifier of the initial task network that carries a compound label.  This
is a *join* of two of the five lists of the serialisation: the identifier list and the label
list.

The algorithm of this file quantifies over the positions of the code:

* four nested quantifiers cut the code into its five self-delimiting lists, which pins down the
  suffix `yids` that begins with the identifier list and the suffix `ylbl` that *is* the label
  list (`HTN.Syn.blist_cut_iff` — a cut guarded by `blistB` is unique);
* `HTN.Syn.anyCompound ylbl y` asks whether some identifier of the list `y` carries a compound
  label, which is `HTN.Syn.compoundB` of `HtnComplexity/Complexity/SerLookup.lean` applied
  at every entry boundary of `y`;
* `HTN.Syn.rootFound c yids ylbl` asks for an entry boundary of the identifier list at which the
  entry is labelled with the compound name `c` (`HTN.Syn.namedB`) while no *earlier* identifier
  carries a compound label — the earlier region being `prefix ++ [false]`, which is exactly the
  serialised list of the earlier entries;
* `HTN.Syn.rootNone c yids ylbl` covers the default: no identifier carries a compound label and
  `c` is `0`.

`HTN.Syn.rootB_iff` proves that on a serialised description the resulting bit is
`decide (rootName q = c)`, and `HTN.Syn.cobhamB_rootB` that the bit is computed by a predicate of
Cobham's class.
-/

namespace HTN

namespace Syn

open PTime

/-! ### The head of a flattened list of labels -/

/-- The label list of an identifier is empty or a singleton. -/
theorem labelList_true_cases (lbl : List (ℕ × Bool × ℕ)) (i : ℕ) :
    TnDesc.labelList true lbl i = [] ∨ ∃ a, TnDesc.labelList true lbl i = [a] := by
  rw [TnDesc.labelList_eq]
  rcases lbl.lookup i with _ | ⟨b, n⟩
  · exact Or.inl rfl
  · cases b
    · exact Or.inl (by simp)
    · exact Or.inr ⟨n, by simp⟩

/-- **The head of a flattened list**, when every block is empty or a singleton: either some
identifier contributes `c` and all earlier ones contribute nothing, or every block is empty and
`c` is the default. -/
theorem headI_flatMap_iff {f : ℕ → List ℕ} (hf : ∀ i, f i = [] ∨ ∃ a, f i = [a]) (c : ℕ) :
    ∀ ids : List ℕ, (ids.flatMap f).headI = c ↔
      (∃ ids₁ i ids₂, ids = ids₁ ++ i :: ids₂ ∧ f i = [c] ∧ ∀ j ∈ ids₁, f j = []) ∨
        (c = 0 ∧ ∀ j ∈ ids, f j = []) := by
  intro ids
  induction ids with
  | nil =>
    simp only [List.flatMap_nil, List.headI_nil, List.not_mem_nil, false_implies,
      implies_true, and_true]
    constructor
    · intro h; exact Or.inr h.symm
    · rintro (⟨ids₁, i, ids₂, hl, -, -⟩ | ⟨rfl, -⟩)
      · exact absurd hl.symm (by cases ids₁ <;> simp)
      · rfl
  | cons i ids ih =>
    rw [List.flatMap_cons]
    rcases hf i with h0 | ⟨a, ha⟩
    · rw [h0, List.nil_append, ih]
      constructor
      · rintro (⟨ids₁, j, ids₂, hl, hj, hno⟩ | ⟨hc, hall⟩)
        · exact Or.inl ⟨i :: ids₁, j, ids₂, by rw [hl]; rfl, hj, by
            intro k hk
            rcases List.mem_cons.1 hk with rfl | hk
            · exact h0
            · exact hno k hk⟩
        · exact Or.inr ⟨hc, by
            intro k hk
            rcases List.mem_cons.1 hk with rfl | hk
            · exact h0
            · exact hall k hk⟩
      · rintro (⟨ids₁, j, ids₂, hl, hj, hno⟩ | ⟨hc, hall⟩)
        · cases ids₁ with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hl
            exact absurd hj (by rw [← hl.1, h0]; simp)
          | cons k ids₁' =>
            simp only [List.cons_append, List.cons.injEq] at hl
            exact Or.inl ⟨ids₁', j, ids₂, hl.2, hj, fun m hm => hno m (by simp [hm])⟩
        · exact Or.inr ⟨hc, fun k hk => hall k (by simp [hk])⟩
    · rw [ha]
      simp only [List.cons_append, List.headI_cons]
      constructor
      · intro hac
        exact Or.inl ⟨[], i, ids, rfl, by rw [ha, hac], by simp⟩
      · rintro (⟨ids₁, j, ids₂, hl, hj, hno⟩ | ⟨-, hall⟩)
        · cases ids₁ with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hl
            rw [← hl.1, ha] at hj
            exact (List.cons.injEq _ _ _ _ ▸ hj).1
          | cons k ids₁' =>
            exfalso
            simp only [List.cons_append, List.cons.injEq] at hl
            have := hno k (by simp)
            rw [← hl.1, ha] at this
            simp at this
        · exact absurd (hall i (by simp)) (by rw [ha]; simp)

/-! ### Is some identifier of a region labelled with a compound task? -/

/-- The piece of the second argument that precedes the first. -/
def cutFn (args : Args) : List Bool :=
  (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)

/-- The inner test: the piece cut out between `s' ⊑ s` is a single entry whose identifier carries
a compound label.  Arguments: `s'`, `s`, `ylbl`. -/
def cmpTest2 (args : Args) : Bool :=
  entryB (cutFn args) && compoundB (args.getD 2 []) (cutFn args).tail

/-- The outer test: the piece before `s` is a sequence of complete entries, and some entry of `s`
carries a compound label.  Arguments: `s`, `y`, `ylbl`. -/
def cmpTest1 (args : Args) : Bool :=
  entriesB (cutFn args) && anyTailsB cmpTest2 [args.getD 0 [], args.getD 2 []] (args.getD 0 [])

/-- **Does some identifier of the serialised list `y` carry a compound label?** -/
def anyCompound (ylbl y : List Bool) : Bool := anyTailsB cmpTest1 [y, ylbl] y

theorem cmpTest2_eq (s' s ylbl : List Bool) :
    cmpTest2 [s', s, ylbl] =
      (entryB (s.take (s.length - s'.length)) &&
        compoundB ylbl (s.take (s.length - s'.length)).tail) := by
  simp [cmpTest2, cutFn]

theorem cmpTest1_eq (s y ylbl : List Bool) :
    cmpTest1 [s, y, ylbl] =
      (entriesB (y.take (y.length - s.length)) && anyTailsB cmpTest2 [s, ylbl] s) := by
  simp [cmpTest1, cutFn]

theorem anyCompound_eq_true {ylbl y : List Bool} :
    anyCompound ylbl y = true ↔ ∃ s, s <:+ y ∧
      entriesB (y.take (y.length - s.length)) = true ∧
      ∃ s', s' <:+ s ∧ entryB (s.take (s.length - s'.length)) = true ∧
        compoundB ylbl (s.take (s.length - s'.length)).tail = true := by
  rw [anyCompound, anyTailsB_eq_true]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [cmpTest1_eq, Bool.and_eq_true, anyTailsB_eq_true]
  refine and_congr_right fun _ => exists_congr fun s' => and_congr_right fun _ => ?_
  rw [cmpTest2_eq, Bool.and_eq_true]

/-- **The scan finds a compound label exactly when some identifier of the list has one.** -/
theorem anyCompound_iff (lbl : List (ℕ × Bool × ℕ)) (ids : List ℕ) (z : List Bool) :
    anyCompound (blist (lbl.map serLbl)) (blist (ids.map bitsOfNat) ++ z) = true ↔
      ∃ i ∈ ids, TnDesc.labelList true lbl i ≠ [] := by
  rw [anyCompound_eq_true]
  constructor
  · rintro ⟨s, hs, hent, s', hs', hE, hcmp⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 hent
    have hcut : entriesEnc a ++ s = blist (ids.map bitsOfNat) ++ z := by
      rw [← ha]
      exact suffix_take_append hs
    obtain ⟨l₂, hl, hseq⟩ := entriesEnc_align a s (ids.map bitsOfNat) z hcut
    obtain ⟨w, hw⟩ := entryB_iff.1 hE
    rw [hw] at hcmp
    have hcut₂ : (true :: bstr w) ++ s' = blist l₂ ++ z := by
      rw [← hw, ← hseq]
      exact suffix_take_append hs'
    obtain ⟨l', hl₂, -⟩ := entry_split hcut₂
    have hwmem : w ∈ ids.map bitsOfNat := by
      rw [hl, hl₂]
      exact List.mem_append_right a List.mem_cons_self
    obtain ⟨i, hi, hiw⟩ := List.mem_map.1 hwmem
    refine ⟨i, hi, ?_⟩
    rw [← compoundB_iff]
    rw [hiw]
    simpa using hcmp
  · rintro ⟨i, hi, hne⟩
    set w : List Bool := bitsOfNat i with hwdef
    have hwmem : w ∈ ids.map bitsOfNat := List.mem_map_of_mem hi
    obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hwmem
    have hy : blist (ids.map bitsOfNat) ++ z
        = entriesEnc L₁ ++ (blist (w :: L₂) ++ z) := by
      rw [hsplit, blist_append_eq, List.append_assoc]
    have hentry : blist (w :: L₂) ++ z = (true :: bstr w) ++ (blist L₂ ++ z) := by
      rw [blist_cons]
      simp
    refine ⟨blist (w :: L₂) ++ z, ⟨entriesEnc L₁, hy.symm⟩, ?_,
      blist L₂ ++ z, ⟨true :: bstr w, hentry.symm⟩, ?_, ?_⟩
    · rw [hy, take_compl]
      exact entriesB_iff.2 ⟨L₁, rfl⟩
    · rw [hentry, take_compl]
      exact entryB_iff.2 ⟨w, rfl⟩
    · rw [hentry, take_compl]
      simpa [hwdef] using compoundB_iff lbl i |>.2 hne

/-! ### The root name -/

/-- The inner test of the root scan: the entry cut out between `s' ⊑ s` is labelled with the
compound name `c`.  Arguments: `s'`, `s`, `ylbl`. -/
def rootTest2 (c : ℕ) (args : Args) : Bool :=
  entryB (cutFn args) && namedB c (args.getD 2 []) (cutFn args).tail

/-- The outer test of the root scan: `s` is an entry boundary of the identifier list, an entry of
`s` is labelled with `c`, and no earlier identifier carries a compound label.  Arguments: `s`,
`yids`, `ylbl`. -/
def rootTest1 (c : ℕ) (args : Args) : Bool :=
  entriesB (cutFn args) &&
      anyTailsB (rootTest2 c) [args.getD 0 [], args.getD 2 []] (args.getD 0 []) &&
    !(anyCompound (args.getD 2 []) (cutFn args ++ [false]))

/-- **Is the first compound label of the identifier list the name `c`?** -/
def rootFound (c : ℕ) (yids ylbl : List Bool) : Bool := anyTailsB (rootTest1 c) [yids, ylbl] yids

/-- **Is there no compound label at all, the default root name being `0`?** -/
def rootNone (c : ℕ) (yids ylbl : List Bool) : Bool :=
  decide (c = 0) && !(anyCompound ylbl yids)

theorem rootTest2_eq (c : ℕ) (s' s ylbl : List Bool) :
    rootTest2 c [s', s, ylbl] =
      (entryB (s.take (s.length - s'.length)) &&
        namedB c ylbl (s.take (s.length - s'.length)).tail) := by
  simp [rootTest2, cutFn]

theorem rootTest1_eq (c : ℕ) (s yids ylbl : List Bool) :
    rootTest1 c [s, yids, ylbl] =
      (entriesB (yids.take (yids.length - s.length)) &&
          anyTailsB (rootTest2 c) [s, ylbl] s &&
        !(anyCompound ylbl (yids.take (yids.length - s.length) ++ [false]))) := by
  simp [rootTest1, cutFn]

theorem rootFound_eq_true {c : ℕ} {yids ylbl : List Bool} :
    rootFound c yids ylbl = true ↔ ∃ s, s <:+ yids ∧
      entriesB (yids.take (yids.length - s.length)) = true ∧
      (∃ s', s' <:+ s ∧ entryB (s.take (s.length - s'.length)) = true ∧
        namedB c ylbl (s.take (s.length - s'.length)).tail = true) ∧
      anyCompound ylbl (yids.take (yids.length - s.length) ++ [false]) = false := by
  rw [rootFound, anyTailsB_eq_true]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [rootTest1_eq, Bool.and_eq_true, Bool.and_eq_true, anyTailsB_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  exact exists_congr fun s' => and_congr_right fun _ => by rw [rootTest2_eq, Bool.and_eq_true]

/-- **The root scan finds the name `c` exactly when some identifier is labelled `c` and no
earlier one carries a compound label.** -/
theorem rootFound_iff (c : ℕ) (lbl : List (ℕ × Bool × ℕ)) (ids : List ℕ) (z : List Bool) :
    rootFound c (blist (ids.map bitsOfNat) ++ z) (blist (lbl.map serLbl)) = true ↔
      ∃ ids₁ i ids₂, ids = ids₁ ++ i :: ids₂ ∧ TnDesc.labelList true lbl i = [c] ∧
        ∀ j ∈ ids₁, TnDesc.labelList true lbl j = [] := by
  rw [rootFound_eq_true]
  constructor
  · rintro ⟨s, hs, hent, ⟨s', hs', hE, hnm⟩, hno⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 hent
    have hcut : entriesEnc a ++ s = blist (ids.map bitsOfNat) ++ z := by
      rw [← ha]
      exact suffix_take_append hs
    obtain ⟨l₂, hl, hseq⟩ := entriesEnc_align a s (ids.map bitsOfNat) z hcut
    obtain ⟨w, hw⟩ := entryB_iff.1 hE
    rw [hw] at hnm
    have hcut₂ : (true :: bstr w) ++ s' = blist l₂ ++ z := by
      rw [← hw, ← hseq]
      exact suffix_take_append hs'
    obtain ⟨l', hl₂, -⟩ := entry_split hcut₂
    obtain ⟨ids₁, idsr, hids, hmap₁, hmap₂⟩ := List.map_eq_append_iff.1 hl
    -- the entry found is the first identifier of `idsr`
    have hidsr : idsr.map bitsOfNat = w :: l' := by rw [hmap₂, hl₂]
    obtain ⟨i, ids₂, rfl⟩ : ∃ i ids₂, idsr = i :: ids₂ := by
      cases idsr with
      | nil => simp at hidsr
      | cons i ids₂ => exact ⟨i, ids₂, rfl⟩
    have hiw : bitsOfNat i = w := by
      simpa using (List.cons.injEq _ _ _ _ ▸ hidsr : bitsOfNat i = w ∧ _).1
    refine ⟨ids₁, i, ids₂, hids, ?_, ?_⟩
    · rw [← namedB_iff]
      rw [hiw]
      simpa using hnm
    · intro j hj
      by_contra hne
      have hregion : (blist (ids.map bitsOfNat) ++ z).take
          ((blist (ids.map bitsOfNat) ++ z).length - s.length) ++ [false]
          = blist (ids₁.map bitsOfNat) := by
        rw [ha, hmap₁, blist_eq_entriesEnc]
      rw [hregion] at hno
      have : anyCompound (blist (lbl.map serLbl)) (blist (ids₁.map bitsOfNat) ++ []) = true :=
        (anyCompound_iff lbl ids₁ []).2 ⟨j, hj, hne⟩
      rw [List.append_nil] at this
      rw [this] at hno
      exact absurd hno (by simp)
  · rintro ⟨ids₁, i, ids₂, rfl, hlbl, hno⟩
    set w : List Bool := bitsOfNat i with hwdef
    have hy : blist ((ids₁ ++ i :: ids₂).map bitsOfNat) ++ z
        = entriesEnc (ids₁.map bitsOfNat) ++ (blist (w :: ids₂.map bitsOfNat) ++ z) := by
      rw [List.map_append, List.map_cons, blist_append_eq, List.append_assoc]
    have hentry : blist (w :: ids₂.map bitsOfNat) ++ z
        = (true :: bstr w) ++ (blist (ids₂.map bitsOfNat) ++ z) := by
      rw [blist_cons]
      simp
    refine ⟨blist (w :: ids₂.map bitsOfNat) ++ z,
      ⟨entriesEnc (ids₁.map bitsOfNat), hy.symm⟩, ?_, ⟨blist (ids₂.map bitsOfNat) ++ z,
      ⟨true :: bstr w, hentry.symm⟩, ?_, ?_⟩, ?_⟩
    · rw [hy, take_compl]
      exact entriesB_iff.2 ⟨ids₁.map bitsOfNat, rfl⟩
    · rw [hentry, take_compl]
      exact entryB_iff.2 ⟨w, rfl⟩
    · rw [hentry, take_compl]
      simpa [hwdef] using (namedB_iff lbl i c).2 hlbl
    · rw [hy, take_compl, ← blist_eq_entriesEnc]
      have : ¬ (anyCompound (blist (lbl.map serLbl)) (blist (ids₁.map bitsOfNat) ++ []) = true) := by
        rw [anyCompound_iff]
        rintro ⟨j, hj, hne⟩
        exact hne (hno j hj)
      simpa using this

/-! ### Cutting the code into its five lists -/

/-- **A cut guarded by the list test is unique**: a suffix preceded by a complete serialised list
is the rest of the code. -/
theorem blist_cut_iff {p : List Bool → Bool} (l : List (List Bool)) (z : List Bool) :
    (∃ s, s <:+ blist l ++ z ∧
        (blistB ((blist l ++ z).take ((blist l ++ z).length - s.length)) && p s) = true) ↔
      p z = true := by
  constructor
  · rintro ⟨s, hs, h⟩
    rw [Bool.and_eq_true] at h
    obtain ⟨l', hl'⟩ := blistB_iff.1 h.1
    have hcut : blist l' ++ s = blist l ++ z := by
      rw [← hl']
      exact suffix_take_append hs
    obtain ⟨-, hsz⟩ := blist_parse hcut
    rw [← hsz]
    exact h.2
  · intro h
    refine ⟨z, ⟨blist l, rfl⟩, ?_⟩
    rw [take_compl, Bool.and_eq_true]
    exact ⟨blistB_iff.2 ⟨l, rfl⟩, h⟩

/-- The innermost cut: the label list is what follows the ordering list.  Arguments: `y₄`, `y₃`,
`yids`. -/
def cutTest4 (c : ℕ) (args : Args) : Bool :=
  blistB (cutFn args) &&
    (rootFound c (args.getD 2 []) (args.getD 0 []) || rootNone c (args.getD 2 []) (args.getD 0 []))

/-- The third cut: the ordering list follows the identifier list.  Arguments: `y₃`, `yids`. -/
def cutTest3 (c : ℕ) (args : Args) : Bool :=
  blistB (cutFn args) && anyTailsB (cutTest4 c) [args.getD 0 [], args.getD 1 []] (args.getD 0 [])

/-- The second cut: the identifier list follows the goal.  Arguments: `yids`, `y₁`. -/
def cutTest2 (c : ℕ) (args : Args) : Bool :=
  blistB (cutFn args) && anyTailsB (cutTest3 c) [args.getD 0 []] (args.getD 0 [])

/-- The first cut: the goal follows the initial state.  Arguments: `y₁`, `x`. -/
def cutTest1 (c : ℕ) (args : Args) : Bool :=
  blistB (cutFn args) && anyTailsB (cutTest2 c) [args.getD 0 []] (args.getD 0 [])

/-- **The root-name bit.** -/
def rootB (c : ℕ) (x : List Bool) : Bool := anyTailsB (cutTest1 c) [x] x

theorem cutTest4_eq (c : ℕ) (s y₃ yids : List Bool) :
    cutTest4 c [s, y₃, yids] =
      (blistB (y₃.take (y₃.length - s.length)) &&
        (rootFound c yids s || rootNone c yids s)) := by
  simp [cutTest4, cutFn]

theorem cutTest3_eq (c : ℕ) (s yids : List Bool) :
    cutTest3 c [s, yids] =
      (blistB (yids.take (yids.length - s.length)) &&
        anyTailsB (cutTest4 c) [s, yids] s) := by
  simp [cutTest3, cutFn]

theorem cutTest2_eq (c : ℕ) (s y₁ : List Bool) :
    cutTest2 c [s, y₁] =
      (blistB (y₁.take (y₁.length - s.length)) && anyTailsB (cutTest3 c) [s] s) := by
  simp [cutTest2, cutFn]

theorem cutTest1_eq (c : ℕ) (s x : List Bool) :
    cutTest1 c [s, x] =
      (blistB (x.take (x.length - s.length)) && anyTailsB (cutTest2 c) [s] s) := by
  simp [cutTest1, cutFn]

/-- **The root-name bit of a serialised description.** -/
theorem rootB_iff (c : ℕ) (q : InstDesc) : rootB c (instSer q) = true ↔ rootName q = c := by
  set I : List (List Bool) := q.initList.map bitsOfNat with hI
  set G : List (List Bool) := q.goalList.map bitsOfNat with hG
  set D : List (List Bool) := q.tnI.ids.map bitsOfNat with hD
  set O : List (List Bool) := q.tnI.ordList.map serPair with hO
  set L : List (List Bool) := q.tnI.lbl.map serLbl with hL
  have hx : instSer q = blist I ++ (blist G ++ (blist D ++ (blist O ++ blist L))) :=
    instSer_eq_blists q
  -- peel the four cuts
  have h1 : rootB c (instSer q) = true ↔
      anyTailsB (cutTest2 c) [blist G ++ (blist D ++ (blist O ++ blist L))]
        (blist G ++ (blist D ++ (blist O ++ blist L))) = true := by
    rw [rootB, hx, anyTailsB_eq_true]
    simp only [cutTest1_eq]
    exact blist_cut_iff I _
  have h2 : ∀ y : List Bool,
      anyTailsB (cutTest2 c) [blist G ++ y] (blist G ++ y) = true ↔
        anyTailsB (cutTest3 c) [y] y = true := by
    intro y
    rw [anyTailsB_eq_true]
    simp only [cutTest2_eq]
    exact blist_cut_iff G y
  have h3 : ∀ y : List Bool,
      anyTailsB (cutTest3 c) [blist D ++ y] (blist D ++ y) = true ↔
        anyTailsB (cutTest4 c) [y, blist D ++ y] y = true := by
    intro y
    rw [anyTailsB_eq_true]
    simp only [cutTest3_eq]
    exact blist_cut_iff (p := fun s => anyTailsB (cutTest4 c) [s, blist D ++ y] s) D y
  have h4 : ∀ yids : List Bool,
      anyTailsB (cutTest4 c) [blist O ++ blist L, yids] (blist O ++ blist L) = true ↔
        (rootFound c yids (blist L) || rootNone c yids (blist L)) = true := by
    intro yids
    rw [anyTailsB_eq_true]
    simp only [cutTest4_eq]
    exact blist_cut_iff (p := fun s => rootFound c yids s || rootNone c yids s) O (blist L)
  rw [h1, h2, h3, h4, Bool.or_eq_true]
  -- identify the two cases with the head of the flattened label list
  have hroot : rootName q = (q.tnI.ids.flatMap (TnDesc.labelList true q.tnI.lbl)).headI := rfl
  rw [hroot, headI_flatMap_iff (labelList_true_cases q.tnI.lbl) c]
  have hz : blist D ++ (blist O ++ blist L) = blist D ++ (blist O ++ blist L) := rfl
  constructor
  · rintro (hf | hn)
    · exact Or.inl ((rootFound_iff c q.tnI.lbl q.tnI.ids (blist O ++ blist L)).1 (by
        rw [hD] at hf; exact hf))
    · rw [rootNone, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true] at hn
      refine Or.inr ⟨hn.1, ?_⟩
      intro j hj
      by_contra hne
      have : anyCompound (blist L) (blist D ++ (blist O ++ blist L)) = true := by
        rw [hD]
        exact (anyCompound_iff q.tnI.lbl q.tnI.ids (blist O ++ blist L)).2 ⟨j, hj, hne⟩
      rw [this] at hn
      exact absurd hn.2 (by simp)
  · rintro (hf | ⟨hc, hall⟩)
    · refine Or.inl ?_
      rw [hD]
      exact (rootFound_iff c q.tnI.lbl q.tnI.ids (blist O ++ blist L)).2 hf
    · refine Or.inr ?_
      rw [rootNone, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
      refine ⟨hc, ?_⟩
      have : ¬ (anyCompound (blist L) (blist D ++ (blist O ++ blist L)) = true) := by
        rw [hD, anyCompound_iff]
        rintro ⟨j, hj, hne⟩
        exact hne (hall j hj)
      simpa using this

/-! ### The algorithm is a predicate of Cobham's class -/

theorem cobham_cutFn : Cobham cutFn :=
  (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj, cutFn]

theorem cobham_tail {a : Fn} (ha : Cobham a) : Cobham fun args => (a args).tail :=
  (cobham_c1 cobham_tailFn ha).of_eq' fun args => by simp [compFn, tailFn_apply]

theorem cobhamB_cmpTest2 : CobhamB cmpTest2 :=
  ((cobhamB_entryB cobham_cutFn).and
    (cobhamB_compoundB (Cobham.proj 2) (cobham_tail cobham_cutFn))).of_eq fun args => by
      simp [cmpTest2, proj]

theorem argDep_cmpTest2 : ArgDep 3 cmpTest2 := by
  intro args
  simp only [cmpTest2, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_cmpTest1 : CobhamB cmpTest1 :=
  ((cobhamB_entriesB cobham_cutFn).and
    ((cobhamB_anyTails cobhamB_cmpTest2 argDep_cmpTest2).comp3 (Cobham.proj 0) (Cobham.proj 0)
      (Cobham.proj 2))).of_eq fun args => by simp [cmpTest1, proj]

theorem argDep_cmpTest1 : ArgDep 3 cmpTest1 := by
  intro args
  simp only [cmpTest1, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_anyCompound {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => anyCompound (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_cmpTest1 argDep_cmpTest1).comp3 hb hb ha).of_eq fun args => by
    simp [anyCompound]

theorem cobhamB_rootTest2 (c : ℕ) : CobhamB (rootTest2 c) :=
  ((cobhamB_entryB cobham_cutFn).and
    (cobhamB_namedB c (Cobham.proj 2) (cobham_tail cobham_cutFn))).of_eq fun args => by
      simp [rootTest2, proj]

theorem argDep_rootTest2 (c : ℕ) : ArgDep 3 (rootTest2 c) := by
  intro args
  simp only [rootTest2, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_rootTest1 (c : ℕ) : CobhamB (rootTest1 c) := by
  have hregion : Cobham fun args : Args => cutFn args ++ [false] :=
    (cobham_c2 cobham_append cobham_cutFn (cobham_const [false])).of_eq' fun args => by
      simp [compFn]
  exact (((cobhamB_entriesB cobham_cutFn).and
    ((cobhamB_anyTails (cobhamB_rootTest2 c) (argDep_rootTest2 c)).comp3 (Cobham.proj 0)
      (Cobham.proj 0) (Cobham.proj 2))).and
    (cobhamB_anyCompound (Cobham.proj 2) hregion).not).of_eq fun args => by
      simp [rootTest1, proj]

theorem argDep_rootTest1 (c : ℕ) : ArgDep 3 (rootTest1 c) := by
  intro args
  simp only [rootTest1, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_rootFound (c : ℕ) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => rootFound c (a args) (b args) :=
  ((cobhamB_anyTails (cobhamB_rootTest1 c) (argDep_rootTest1 c)).comp3 ha ha hb).of_eq
    fun args => by simp [rootFound]

theorem cobhamB_rootNone (c : ℕ) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => rootNone c (a args) (b args) :=
  ((cobhamB_const (decide (c = 0))).and (cobhamB_anyCompound hb ha).not).of_eq fun args => by
    simp [rootNone]

theorem cobhamB_cutTest4 (c : ℕ) : CobhamB (cutTest4 c) :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_rootFound c (Cobham.proj 2) (Cobham.proj 0)).or
      (cobhamB_rootNone c (Cobham.proj 2) (Cobham.proj 0)))).of_eq fun args => by
        simp [cutTest4, proj]

theorem argDep_cutTest4 (c : ℕ) : ArgDep 3 (cutTest4 c) := by
  intro args
  simp only [cutTest4, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_cutTest3 (c : ℕ) : CobhamB (cutTest3 c) :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_anyTails (cobhamB_cutTest4 c) (argDep_cutTest4 c)).comp3 (Cobham.proj 0)
      (Cobham.proj 0) (Cobham.proj 1))).of_eq fun args => by simp [cutTest3, proj]

theorem argDep_cutTest3 (c : ℕ) : ArgDep 2 (cutTest3 c) := by
  intro args
  simp only [cutTest3, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 2),
    getD_padArgs (by norm_num : (1 : ℕ) < 2)]

theorem cobhamB_cutTest2 (c : ℕ) : CobhamB (cutTest2 c) :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_anyTails (cobhamB_cutTest3 c) (argDep_cutTest3 c)).comp2 (Cobham.proj 0)
      (Cobham.proj 0))).of_eq fun args => by simp [cutTest2, proj]

theorem argDep_cutTest2 (c : ℕ) : ArgDep 2 (cutTest2 c) := by
  intro args
  simp only [cutTest2, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 2),
    getD_padArgs (by norm_num : (1 : ℕ) < 2)]

theorem cobhamB_cutTest1 (c : ℕ) : CobhamB (cutTest1 c) :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_anyTails (cobhamB_cutTest2 c) (argDep_cutTest2 c)).comp2 (Cobham.proj 0)
      (Cobham.proj 0))).of_eq fun args => by simp [cutTest1, proj]

theorem argDep_cutTest1 (c : ℕ) : ArgDep 2 (cutTest1 c) := by
  intro args
  simp only [cutTest1, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 2),
    getD_padArgs (by norm_num : (1 : ℕ) < 2)]

/-- **The root-name bit is decided in polynomial time.** -/
theorem cobhamB_rootB (c : ℕ) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => rootB c (a args) :=
  ((cobhamB_anyTails (cobhamB_cutTest1 c) (argDep_cutTest1 c)).comp2 ha ha).of_eq fun args => by
    simp [rootB]

end Syn

end HTN
