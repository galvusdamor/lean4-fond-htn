import HtnComplexity.Complexity.SerRoot
/-!
# Reading the root name against a *computed* key

`HtnComplexity/Complexity/SerRoot.lean` decides, for a **fixed** number `c`, whether the
root name of a serialised instance description is `c`: `HTN.Syn.rootB c` is a predicate of
Cobham's class for every `c`, but the family is not uniform in `c` — the numeral of `c` enters
the algorithm as a constant string.

The target-side machine of `HtnComplexity/Space/` needs the uniform version: it holds a
configuration in which one entry is meant to be the numeral of the root name, and it has to
*check* that entry against the code of the instance.  The key is then a string the test reads,
not a constant.

This file repeats the chain of `SerRoot.lean` with the key as the **last argument** of every
test:

* `HTN.Syn.lblTestK`, `HTN.Syn.firstLabelS` — the lookup of `SerLookup.lean` with a computed
  key `K`;
* `HTN.Syn.namedD`, `HTN.Syn.rootFoundS`, `HTN.Syn.rootNoneS`, `HTN.Syn.rootS` — the root scan;
* `HTN.Syn.rootS_eq` — at a key that *is* a numeral, the uniform test is the test of
  `SerRoot.lean`, so its correctness `HTN.Syn.rootB_iff` transfers, giving
  `HTN.Syn.rootS_iff_of_canon`;
* `HTN.Syn.cobhamB_rootS` — the uniform test is a predicate of Cobham's class, the key being any
  computed string.
-/

namespace HTN

namespace Syn

open PTime

/-! ### A congruence for the suffix quantifier -/

theorem anyTailsB_congr {p p' : Args → Bool} {v v' : Args} {x : List Bool}
    (h : ∀ s, p (s :: v) = p' (s :: v')) : anyTailsB p v x = anyTailsB p' v' x := by
  simp only [anyTailsB]
  congr 1
  funext s
  exact h s

/-! ### The lookup with a computed key -/

/-- The body of `HTN.Syn.firstLabelS`: `HTN.Syn.lblTest` with the key read off the fourth
argument. -/
def lblTestK (args : Args) : Bool :=
  entriesB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) &&
    decide ((true :: dbl (args.getD 2 [] ++ args.getD 3 [])) <+: args.getD 0 []) &&
    !(occB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) ++ [false])
      (true :: dbl (args.getD 2 [])))

theorem lblTestK_eq (K t y w : List Bool) : lblTestK [t, y, w, K] = lblTest K [t, y, w] := by
  simp [lblTestK, lblTest]

/-- **The lookup of `HTN.Syn.firstLabelB` with the key given as a string.** -/
def firstLabelS (K y w : List Bool) : Bool := anyTailsB lblTestK [y, w, K] y

theorem firstLabelS_eq (K y w : List Bool) : firstLabelS K y w = firstLabelB K y w :=
  anyTailsB_congr fun s => lblTestK_eq K s y w

/-! ### The root scan with a computed key -/

/-- **Is the identifier labelled with the compound task whose numeral is `u`?**  The key is not
the numeral `u` but its self-delimiting form `HTN.Syn.bstr u`, which is the form in which a
numeral occurs inside an entry of a serialised list: a machine holding an entry can cut the key
out of it, while it could not recover `u` itself, the coding `dbl` being an interleaving. -/
def namedD (k ylbl w : List Bool) : Bool := firstLabelS (true :: k) ylbl w

theorem namedD_eq (c : ℕ) (ylbl w : List Bool) :
    namedD (bstr (bitsOfNat c)) ylbl w = namedB c ylbl w := firstLabelS_eq _ _ _

/-- The inner test of the root scan.  Arguments: `s'`, `s`, `ylbl`, `k`. -/
def rootTest2K (args : Args) : Bool :=
  entryB (cutFn args) && namedD (args.getD 3 []) (args.getD 2 []) (cutFn args).tail

/-- The outer test of the root scan.  Arguments: `s`, `yids`, `ylbl`, `u`. -/
def rootTest1K (args : Args) : Bool :=
  entriesB (cutFn args) &&
      anyTailsB rootTest2K [args.getD 0 [], args.getD 2 [], args.getD 3 []] (args.getD 0 []) &&
    !(anyCompound (args.getD 2 []) (cutFn args ++ [false]))

/-- **Is the first compound label of the identifier list the name whose numeral is `u`?** -/
def rootFoundS (u yids ylbl : List Bool) : Bool := anyTailsB rootTest1K [yids, ylbl, u] yids

/-- **Is there no compound label at all, the default root name being `0`?**  The key of `0` is
`bstr [] = [false]`. -/
def rootNoneS (k yids ylbl : List Bool) : Bool :=
  decide (k = [false]) && !(anyCompound ylbl yids)

/-- The innermost cut.  Arguments: `y₄`, `y₃`, `yids`, `u`. -/
def cutTest4K (args : Args) : Bool :=
  blistB (cutFn args) &&
    (rootFoundS (args.getD 3 []) (args.getD 2 []) (args.getD 0 []) ||
      rootNoneS (args.getD 3 []) (args.getD 2 []) (args.getD 0 []))

/-- The third cut.  Arguments: `y₃`, `yids`, `u`. -/
def cutTest3K (args : Args) : Bool :=
  blistB (cutFn args) &&
    anyTailsB cutTest4K [args.getD 0 [], args.getD 1 [], args.getD 2 []] (args.getD 0 [])

/-- The second cut.  Arguments: `yids`, `y₁`, `u`. -/
def cutTest2K (args : Args) : Bool :=
  blistB (cutFn args) && anyTailsB cutTest3K [args.getD 0 [], args.getD 2 []] (args.getD 0 [])

/-- The first cut.  Arguments: `y₁`, `x`, `u`. -/
def cutTest1K (args : Args) : Bool :=
  blistB (cutFn args) && anyTailsB cutTest2K [args.getD 0 [], args.getD 2 []] (args.getD 0 [])

/-- **The root-name bit against a key given as a string.** -/
def rootS (u x : List Bool) : Bool := anyTailsB cutTest1K [x, u] x

/-! ### At a numeral the uniform test is the test of `SerRoot.lean` -/

theorem rootTest2K_eq (c : ℕ) (s' s ylbl : List Bool) :
    rootTest2K [s', s, ylbl, bstr (bitsOfNat c)] = rootTest2 c [s', s, ylbl] := by
  simp [rootTest2K, rootTest2, cutFn, namedD_eq]

theorem rootTest1K_eq (c : ℕ) (s yids ylbl : List Bool) :
    rootTest1K [s, yids, ylbl, bstr (bitsOfNat c)] = rootTest1 c [s, yids, ylbl] := by
  have h : anyTailsB rootTest2K [s, ylbl, bstr (bitsOfNat c)] s
      = anyTailsB (rootTest2 c) [s, ylbl] s :=
    anyTailsB_congr fun t => rootTest2K_eq c t s ylbl
  simp only [rootTest1K, rootTest1, cutFn, List.getD_cons_zero, List.getD_cons_succ, h]

theorem rootFoundS_eq (c : ℕ) (yids ylbl : List Bool) :
    rootFoundS (bstr (bitsOfNat c)) yids ylbl = rootFound c yids ylbl :=
  anyTailsB_congr fun s => rootTest1K_eq c s yids ylbl

theorem rootNoneS_eq (c : ℕ) (yids ylbl : List Bool) :
    rootNoneS (bstr (bitsOfNat c)) yids ylbl = rootNone c yids ylbl := by
  simp only [rootNoneS, rootNone]
  congr 1
  have key : ∀ w : List Bool, (dbl w ++ [false] = [false]) ↔ w = [] := by
    intro w
    cases w with
    | nil => simp [dbl]
    | cons b t => simp [dbl]
  simp only [decide_eq_decide, bstr_eq_dbl, key]
  constructor
  · intro h
    have h2 := congrArg natOfBits h
    simpa [natOfBits_bitsOfNat] using h2
  · rintro rfl
    simp

theorem cutTest4K_eq (c : ℕ) (y₄ y₃ yids : List Bool) :
    cutTest4K [y₄, y₃, yids, bstr (bitsOfNat c)] = cutTest4 c [y₄, y₃, yids] := by
  simp [cutTest4K, cutTest4, cutFn, rootFoundS_eq, rootNoneS_eq]

theorem cutTest3K_eq (c : ℕ) (y₃ yids : List Bool) :
    cutTest3K [y₃, yids, bstr (bitsOfNat c)] = cutTest3 c [y₃, yids] := by
  simp only [cutTest3K, cutTest3, cutFn, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  exact anyTailsB_congr fun s => cutTest4K_eq c s y₃ yids

theorem cutTest2K_eq (c : ℕ) (yids y₁ : List Bool) :
    cutTest2K [yids, y₁, bstr (bitsOfNat c)] = cutTest2 c [yids, y₁] := by
  simp only [cutTest2K, cutTest2, cutFn, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  exact anyTailsB_congr fun s => cutTest3K_eq c s yids

theorem cutTest1K_eq (c : ℕ) (y₁ x : List Bool) :
    cutTest1K [y₁, x, bstr (bitsOfNat c)] = cutTest1 c [y₁, x] := by
  simp only [cutTest1K, cutTest1, cutFn, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  exact anyTailsB_congr fun s => cutTest2K_eq c s y₁

/-- **At a key that is a numeral the uniform root test is the root test of
`HtnComplexity/Complexity/SerRoot.lean`.** -/
theorem rootS_eq (c : ℕ) (x : List Bool) : rootS (bstr (bitsOfNat c)) x = rootB c x :=
  anyTailsB_congr fun s => cutTest1K_eq c s x

/-- **The uniform root test on a serialised description**: it accepts exactly the numeral of the
root name.  The key is assumed canonical — the numeral of the number it codes — which is what the
machine's well-formedness test guarantees of the entries of a configuration. -/
theorem rootS_iff_of_canon {u : List Bool} (hu : bitsOfNat (natOfBits u) = u) (q : InstDesc) :
    rootS (bstr u) (instSer q) = true ↔ bitsOfNat (rootName q) = u := by
  rw [← hu, rootS_eq, rootB_iff]
  exact ⟨fun h => by rw [h], fun h => bitsOfNat_injective h⟩

/-! ### The uniform test is a predicate of Cobham's class -/

theorem cobhamB_lblTestK : CobhamB lblTestK := by
  have hpre : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  have hpat : Cobham fun args : Args => true :: dbl (args.getD 2 [] ++ args.getD 3 []) :=
    cobham_consTrue (cobham_dbl ((cobham_c2 cobham_append (Cobham.proj 2)
      (Cobham.proj 3)).of_eq' fun args => by simp [compFn, proj]))
  have hkey : Cobham fun args : Args => true :: dbl (args.getD 2 []) :=
    cobham_consTrue (cobham_dbl ((Cobham.proj 2).of_eq' fun args => by simp [proj]))
  have hregion : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) ++ [false] :=
    (cobham_c2 cobham_append hpre (cobham_const [false])).of_eq' fun args => by simp [compFn]
  have h1 : CobhamB fun args : Args =>
      entriesB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length)) :=
    cobhamB_entriesB hpre
  have h2 : CobhamB fun args : Args =>
      decide ((true :: dbl (args.getD 2 [] ++ args.getD 3 [])) <+: args.getD 0 []) :=
    (cobhamB_isPrefix hpat (Cobham.proj 0)).of_eq fun args => by simp [proj]
  have h3 : CobhamB fun args : Args =>
      occB ((args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) ++ [false])
        (true :: dbl (args.getD 2 [])) := cobhamB_occB hregion hkey
  exact ((h1.and h2).and h3.not).of_eq fun args => by simp [lblTestK]

theorem argDep_lblTestK : ArgDep 4 lblTestK := by
  intro args
  simp only [lblTestK, getD_padArgs (by norm_num : (0 : ℕ) < 4),
    getD_padArgs (by norm_num : (1 : ℕ) < 4), getD_padArgs (by norm_num : (2 : ℕ) < 4),
    getD_padArgs (by norm_num : (3 : ℕ) < 4)]

theorem cobhamB_firstLabelS {k a b : Fn} (hk : Cobham k) (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => firstLabelS (k args) (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_lblTestK argDep_lblTestK).comp4 ha ha hb hk).of_eq
    fun args => by simp [firstLabelS]

theorem cobhamB_namedD {k a b : Fn} (hk : Cobham k) (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => namedD (k args) (a args) (b args) :=
  cobhamB_firstLabelS (cobham_consTrue hk) ha hb

theorem cobhamB_rootTest2K : CobhamB rootTest2K :=
  ((cobhamB_entryB cobham_cutFn).and
    (cobhamB_namedD (Cobham.proj 3) (Cobham.proj 2) (cobham_tail cobham_cutFn))).of_eq
      fun args => by simp [rootTest2K, proj]

theorem argDep_rootTest2K : ArgDep 4 rootTest2K := by
  intro args
  simp only [rootTest2K, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 4),
    getD_padArgs (by norm_num : (1 : ℕ) < 4), getD_padArgs (by norm_num : (2 : ℕ) < 4),
    getD_padArgs (by norm_num : (3 : ℕ) < 4)]

theorem cobhamB_rootTest1K : CobhamB rootTest1K := by
  have hregion : Cobham fun args : Args => cutFn args ++ [false] :=
    (cobham_c2 cobham_append cobham_cutFn (cobham_const [false])).of_eq' fun args => by
      simp [compFn]
  exact (((cobhamB_entriesB cobham_cutFn).and
    ((cobhamB_anyTails cobhamB_rootTest2K argDep_rootTest2K).comp4 (Cobham.proj 0)
      (Cobham.proj 0) (Cobham.proj 2) (Cobham.proj 3))).and
    (cobhamB_anyCompound (Cobham.proj 2) hregion).not).of_eq fun args => by
      simp [rootTest1K, proj]

theorem argDep_rootTest1K : ArgDep 4 rootTest1K := by
  intro args
  simp only [rootTest1K, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 4),
    getD_padArgs (by norm_num : (1 : ℕ) < 4), getD_padArgs (by norm_num : (2 : ℕ) < 4),
    getD_padArgs (by norm_num : (3 : ℕ) < 4)]

theorem cobhamB_rootFoundS {k a b : Fn} (hk : Cobham k) (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => rootFoundS (k args) (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_rootTest1K argDep_rootTest1K).comp4 ha ha hb hk).of_eq
    fun args => by simp [rootFoundS]

theorem cobhamB_rootNoneS {k a b : Fn} (hk : Cobham k) (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => rootNoneS (k args) (a args) (b args) :=
  ((cobhamB_eqStr hk (cobham_const [false])).and (cobhamB_anyCompound hb ha).not).of_eq
    fun args => by simp [rootNoneS]

theorem cobhamB_cutTest4K : CobhamB cutTest4K :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_rootFoundS (Cobham.proj 3) (Cobham.proj 2) (Cobham.proj 0)).or
      (cobhamB_rootNoneS (Cobham.proj 3) (Cobham.proj 2) (Cobham.proj 0)))).of_eq
        fun args => by simp [cutTest4K, proj]

theorem argDep_cutTest4K : ArgDep 4 cutTest4K := by
  intro args
  simp only [cutTest4K, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 4),
    getD_padArgs (by norm_num : (1 : ℕ) < 4), getD_padArgs (by norm_num : (2 : ℕ) < 4),
    getD_padArgs (by norm_num : (3 : ℕ) < 4)]

theorem cobhamB_cutTest3K : CobhamB cutTest3K :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_anyTails cobhamB_cutTest4K argDep_cutTest4K).comp4 (Cobham.proj 0)
      (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2))).of_eq fun args => by
        simp [cutTest3K, proj]

theorem argDep_cutTest3K : ArgDep 3 cutTest3K := by
  intro args
  simp only [cutTest3K, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_cutTest2K : CobhamB cutTest2K :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_anyTails cobhamB_cutTest3K argDep_cutTest3K).comp3 (Cobham.proj 0)
      (Cobham.proj 0) (Cobham.proj 2))).of_eq fun args => by simp [cutTest2K, proj]

theorem argDep_cutTest2K : ArgDep 3 cutTest2K := by
  intro args
  simp only [cutTest2K, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_cutTest1K : CobhamB cutTest1K :=
  ((cobhamB_blistB cobham_cutFn).and
    ((cobhamB_anyTails cobhamB_cutTest2K argDep_cutTest2K).comp3 (Cobham.proj 0)
      (Cobham.proj 0) (Cobham.proj 2))).of_eq fun args => by simp [cutTest1K, proj]

theorem argDep_cutTest1K : ArgDep 3 cutTest1K := by
  intro args
  simp only [cutTest1K, cutFn, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

/-- **The uniform root test is decided in polynomial time.** -/
theorem cobhamB_rootS {k a : Fn} (hk : Cobham k) (ha : Cobham a) :
    CobhamB fun args => rootS (k args) (a args) :=
  ((cobhamB_anyTails cobhamB_cutTest1K argDep_cutTest1K).comp3 ha ha hk).of_eq fun args => by
    simp [rootS]

end Syn

end HTN
