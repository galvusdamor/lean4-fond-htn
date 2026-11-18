import HtnComplexity.Space.TestsSem
import HtnComplexity.Space.TestsCobham
import HtnComplexity.Space.InstBound
import HtnComplexity.Complexity.SerRootKey
/-!
# Reading the compiled instance off the code of the instance

The machine of `HtnComplexity/Space/TblMachine.lean` reads the initial state and the goal of
its table problem off an input in the shape `HTN.Space.encProblem`.  For the target side of
Table 3 the input is the **code of an instance description**, `HTN.Syn.instSer q`, and the table
problem is the compiled one: initial state `HTN.Space.regInitR q` and goal
`HTN.Space.regGoalR q`.  Turning the first string into the second is a *function*, and functions
are awkward inside Cobham's class; this file avoids building one, by giving the machine two new
tests that read the code directly.

That this is possible at all rests on the renaming of `HtnComplexity/Space/Rename.lean`: in
the renamed vocabulary a fact `v` of the instance becomes `4 v + 2` and the initial compound task
`c` becomes `4 c + 3`, and the numeral of `4 v + 2` is the numeral of `v` with two constant bits
in front — *at every argument*.  So a fact of the compiled problem is an entry of the code with a
two-bit tag prefixed, which is the string surgery `HTN.Space.mkEnt` of
`HtnComplexity/Space/Tests.lean` already performs.

Three of the four conditions are plain quantifications over entries.  The fourth — that the
configuration carries the fact of the *initial compound task* — needs the name of that task,
which is not written anywhere in the code as such: it is the label of the first identifier of the
initial task network that carries a compound label.  That is what
`HtnComplexity/Complexity/SerRootKey.lean` decides, the key being read off the entry of the
configuration.

The tests are `HTN.Space.initCoreR` and `HTN.Space.accCoreR`; their meaning is
`HTN.Space.initCoreR_iff` and `HTN.Space.accCoreR_iff`, and their membership in Cobham's class is
`HTN.Space.cobhamB_initCoreR` and `HTN.Space.cobhamB_accCoreR`.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### Entry surgeries with an empty row name -/

/-- The encoded entry of the empty numeral.  Used as the "row name" argument of the surgeries of
`HtnComplexity/Space/Tests.lean`, which then act on the whole numeral of an entry. -/
def nilEnt : List Bool := [true, false]

theorem nilEnt_eq : nilEnt = true :: bstr [] := rfl

/-- The tag of a fact of the instance: `v ↦ 4 v + 2`. -/
def tagFact : List Bool := [false, true]

/-- The tag of the initial compound task: `c ↦ 4 c + 3`. -/
def tagRoot : List Bool := [true, true]

/-- The entry `E` with the two bits `t` prefixed to its numeral. -/
def preEnt (t E : List Bool) : List Bool := mkEnt t nilEnt E

/-- The numeral of the entry `E` without its two leading bits, in self-delimiting form. -/
def bodyOf (E : List Bool) : List Bool := (factOf nilEnt E).tail

/-- **Does the numeral of the entry `E` start with the two bits `t`?** -/
def preIsB (t E : List Bool) : Bool := tagIsB t nilEnt E

theorem preEnt_eq (t w : List Bool) : preEnt t (true :: bstr w) = true :: bstr (t ++ w) := by
  rw [preEnt, nilEnt_eq, mkEnt_eq]
  simp

theorem preIsB_iff (t w : List Bool) : preIsB t (true :: bstr w) = true ↔ t <+: w := by
  rw [preIsB, tagIsB, restOf, nilEnt]
  simp only [List.length_cons, List.length_nil, decide_eq_true_eq]
  rw [show (true :: bstr w).drop (1 + 1 - 1) = bstr w from rfl, bstr_eq_dbl]
  exact dbl_prefix_iff t w []

theorem factOf_nilEnt {t : List Bool} (ht : t.length = 2) (v : List Bool) :
    factOf nilEnt (true :: bstr (t ++ v)) = true :: bstr v := by
  rw [nilEnt_eq]
  simpa using factOf_eq ht [] v

theorem bodyOf_eq {t : List Bool} (ht : t.length = 2) (v : List Bool) :
    bodyOf (true :: bstr (t ++ v)) = bstr v := by
  rw [bodyOf, factOf_nilEnt ht]
  rfl

/-! ### Two small facts about numerals -/

theorem bitsOfNat_tagFact (v : ℕ) : bitsOfNat (4 * v + 2) = tagFact ++ bitsOfNat v := by
  rw [bitsOfNat_four_add_two, tagFact]
  rfl

theorem bitsOfNat_tagRoot (v : ℕ) : bitsOfNat (4 * v + 3) = tagRoot ++ bitsOfNat v := by
  rw [bitsOfNat_four_add_three, tagRoot]
  rfl

theorem isCanon_drop_prefix {t u : List Bool} (h : IsCanon (t ++ u)) : IsCanon u := by
  rcases eq_or_ne u [] with rfl | hu
  · exact isCanon_of_getLast (Or.inl rfl)
  · refine isCanon_of_getLast (Or.inr ?_)
    rcases (isCanon_iff_getLast _).1 h with h' | h'
    · exact absurd (List.append_eq_nil_iff.1 h').2 hu
    · rwa [List.getLast?_append_of_ne_nil t hu] at h'

/-! ### The tests -/

/-- Every fact of the initial state of the input, with the fact tag prefixed, is in the
configuration. -/
def initInB (x c : List Bool) : Bool :=
  allEntB (fun args => occB (args.getD 1 []) (preEnt tagFact (args.getD 0 []))) x c [] []

/-- Some entry of the configuration is the initial compound task of the input. -/
def rootInB (c x : List Bool) : Bool :=
  anyEntB (fun args => preIsB tagRoot (args.getD 0 []) &&
    rootS (bodyOf (args.getD 0 [])) (args.getD 1 [])) c x [] []

/-- Every entry of the configuration is a tagged fact of the initial state of the input, or the
initial compound task. -/
def initOnlyB (c x : List Bool) : Bool :=
  allEntB (fun args =>
    (preIsB tagFact (args.getD 0 []) && occB (args.getD 1 []) (factOf nilEnt (args.getD 0 []))) ||
      (preIsB tagRoot (args.getD 0 []) && rootS (bodyOf (args.getD 0 [])) (args.getD 1 [])))
    c x [] []

/-- **The configuration carries exactly the facts of the compiled initial state of the instance
the input codes.** -/
def initCoreR (c x : List Bool) : Bool := initInB x c && rootInB c x && initOnlyB c x

/-- Every fact of the goal of the input, with the fact tag prefixed, is in the configuration. -/
def goalInB (x c : List Bool) : Bool :=
  afterB (fun args => allEntB (fun args2 =>
      occB (args2.getD 1 []) (preEnt tagFact (args2.getD 0 []))) (args.getD 0 [])
    (args.getD 1 []) [] []) x c [] []

/-- **The flag bit of the advice is set and the compiled goal of the instance is reached.** -/
def accCoreR (c x a : List Bool) : Bool :=
  (a.reverse.headD false) && goalInB x c && occB c nilEnt

/-! ### What the tests mean -/

theorem initInB_iff (S : List (List Bool)) (q : InstDesc) :
    initInB (instSer q) (blist S) = true ↔ ∀ v ∈ q.initList, tagFact ++ bitsOfNat v ∈ S := by
  rw [initInB, instSer_eq_blists q, allEntB_iff]
  constructor
  · intro h v hv
    have := h (bitsOfNat v) (List.mem_map_of_mem hv)
    simp only [List.getD_cons_zero, List.getD_cons_succ, preEnt_eq] at this
    exact (occB_blist S _).1 this
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    simp only [List.getD_cons_zero, List.getD_cons_succ, preEnt_eq]
    exact (occB_blist S _).2 (h v hv)

theorem rootInB_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (q : InstDesc) :
    rootInB (blist S) (instSer q) = true ↔ tagRoot ++ bitsOfNat (rootName q) ∈ S := by
  rw [rootInB, show blist S = blist S ++ [] from (List.append_nil _).symm, anyEntB_iff]
  constructor
  · rintro ⟨w, hw, h⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
    obtain ⟨hpre, hroot⟩ := h
    obtain ⟨u, rfl⟩ := (preIsB_iff tagRoot w).1 hpre
    rw [bodyOf_eq (by rfl) u] at hroot
    have hcan : IsCanon u := isCanon_drop_prefix (hS _ hw)
    rw [rootS_iff_of_canon hcan q] at hroot
    rwa [hroot]
  · intro h
    refine ⟨tagRoot ++ bitsOfNat (rootName q), h, ?_⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
    refine ⟨(preIsB_iff _ _).2 ⟨_, rfl⟩, ?_⟩
    rw [bodyOf_eq (by rfl) (bitsOfNat (rootName q))]
    exact (rootS_iff_of_canon (isCanon_bitsOfNat _) q).2 rfl

theorem initOnlyB_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (q : InstDesc) :
    initOnlyB (blist S) (instSer q) = true ↔
      ∀ w ∈ S, (∃ v ∈ q.initList, w = tagFact ++ bitsOfNat v) ∨
        w = tagRoot ++ bitsOfNat (rootName q) := by
  rw [initOnlyB, show blist S = blist S ++ [] from (List.append_nil _).symm, allEntB_iff]
  refine forall₂_congr fun w hw => ?_
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro (⟨hpre, hocc⟩ | ⟨hpre, hroot⟩)
    · obtain ⟨u, rfl⟩ := (preIsB_iff tagFact w).1 hpre
      rw [factOf_nilEnt (by rfl) u] at hocc
      rw [instSer_eq_blists q] at hocc
      have hu : u ∈ q.initList.map bitsOfNat := (occB_iff _ _ u).1 hocc
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
      exact Or.inl ⟨v, hv, rfl⟩
    · obtain ⟨u, rfl⟩ := (preIsB_iff tagRoot w).1 hpre
      rw [bodyOf_eq (by rfl) u] at hroot
      have hcan : IsCanon u := isCanon_drop_prefix (hS _ hw)
      rw [rootS_iff_of_canon hcan q] at hroot
      exact Or.inr (by rw [hroot])
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · refine Or.inl ⟨(preIsB_iff _ _).2 ⟨_, rfl⟩, ?_⟩
      rw [factOf_nilEnt (by rfl) (bitsOfNat v), instSer_eq_blists q]
      exact (occB_iff _ _ _).2 (List.mem_map_of_mem hv)
    · refine Or.inr ⟨(preIsB_iff _ _).2 ⟨_, rfl⟩, ?_⟩
      rw [bodyOf_eq (by rfl) (bitsOfNat (rootName q))]
      exact (rootS_iff_of_canon (isCanon_bitsOfNat _) q).2 rfl

/-- **The initial test**: the configuration carries exactly the facts of the initial state of the
compiled problem of the instance the input codes. -/
theorem initCoreR_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (q : InstDesc) :
    initCoreR (blist S) (instSer q) = true ↔ ∀ f, f ∈ decSt S ↔ f ∈ regInitR q := by
  rw [initCoreR, Bool.and_eq_true, Bool.and_eq_true, initInB_iff, rootInB_iff hS,
    initOnlyB_iff hS]
  constructor
  · rintro ⟨⟨hin, hroot⟩, honly⟩ f
    rw [mem_decSt_iff hS f, regInitR, List.mem_append]
    constructor
    · intro hf
      rcases honly _ hf with ⟨v, hv, he⟩ | he
      · refine Or.inl (List.mem_map.2 ⟨v, hv, ?_⟩)
        exact bitsOfNat_injective (by rw [he, bitsOfNat_tagFact])
      · refine Or.inr (List.mem_singleton.2 ?_)
        exact bitsOfNat_injective (by rw [he, bitsOfNat_tagRoot])
    · rintro (hf | hf)
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hf
        rw [bitsOfNat_tagFact]
        exact hin v hv
      · rw [List.mem_singleton.1 hf, bitsOfNat_tagRoot]
        exact hroot
  · intro h
    refine ⟨⟨fun v hv => ?_, ?_⟩, fun w hw => ?_⟩
    · rw [← bitsOfNat_tagFact, ← mem_decSt_iff hS, h]
      exact List.mem_append_left _ (List.mem_map_of_mem hv)
    · rw [← bitsOfNat_tagRoot, ← mem_decSt_iff hS, h]
      exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    · have hcan : bitsOfNat (natOfBits w) = w := hS w hw
      have hmem : natOfBits w ∈ regInitR q := by
        rw [← h, mem_decSt_iff hS, hcan]
        exact hw
      rw [regInitR, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨v, hv, hveq⟩ := List.mem_map.1 hmem
        refine Or.inl ⟨v, hv, ?_⟩
        rw [← hcan, ← hveq, bitsOfNat_tagFact]
      · rw [List.mem_singleton.1 hmem] at hcan
        refine Or.inr ?_
        rw [← hcan, bitsOfNat_tagRoot]

theorem goalInB_iff (S : List (List Bool)) (q : InstDesc) :
    goalInB (instSer q) (blist S) = true ↔ ∀ v ∈ q.goalList, tagFact ++ bitsOfNat v ∈ S := by
  rw [goalInB, instSer_eq_blists q, afterB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [allEntB_iff]
  constructor
  · intro h v hv
    have := h (bitsOfNat v) (List.mem_map_of_mem hv)
    simp only [List.getD_cons_zero, List.getD_cons_succ, preEnt_eq] at this
    exact (occB_blist S _).1 this
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    simp only [List.getD_cons_zero, List.getD_cons_succ, preEnt_eq]
    exact (occB_blist S _).2 (h v hv)

/-- **The accepting test**: the flag bit of the advice is set and the configuration carries the
goal of the compiled problem. -/
theorem accCoreR_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (q : InstDesc) (b : Bool)
    (tbl : List Row) :
    accCoreR (blist S) (instSer q) (tblAdv b tbl) = true ↔
      (b = true ∧ ∀ f ∈ regGoalR q, f ∈ decSt S) := by
  have hrev : ((tblAdv b tbl).reverse.headD false) = b := by simp [tblAdv]
  rw [accCoreR, hrev, Bool.and_eq_true, Bool.and_eq_true, goalInB_iff]
  have hnil : occB (blist S) nilEnt = true ↔ ([] : List Bool) ∈ S := by
    rw [nilEnt_eq]
    exact occB_blist S []
  rw [hnil, and_assoc]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨hgoal, hzero⟩ f hf
    rw [regGoalR, List.mem_append] at hf
    rw [mem_decSt_iff hS]
    rcases hf with hf | hf
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hf
      rw [bitsOfNat_tagFact]
      exact hgoal v hv
    · rw [List.mem_singleton.1 hf]
      simpa using hzero
  · intro h
    refine ⟨fun v hv => ?_, ?_⟩
    · rw [← bitsOfNat_tagFact, ← mem_decSt_iff hS]
      exact h _ (List.mem_append_left _ (List.mem_map_of_mem hv))
    · have := h 0 (List.mem_append_right _ (List.mem_singleton.2 rfl))
      rw [mem_decSt_iff hS] at this
      simpa using this

/-! ### The tests are predicates of Cobham's class -/

theorem cobham_preEnt (t : List Bool) {b : Fn} (hb : Cobham b) :
    Cobham fun args => preEnt t (b args) := cobham_mkEnt t (cobham_const nilEnt) hb

theorem cobham_bodyOf {b : Fn} (hb : Cobham b) : Cobham fun args => bodyOf (b args) :=
  cobham_tl (cobham_factOf (cobham_const nilEnt) hb)

theorem cobhamB_preIsB (t : List Bool) {b : Fn} (hb : Cobham b) :
    CobhamB fun args => preIsB t (b args) := cobhamB_tagIsB t (cobham_const nilEnt) hb

theorem cobhamB_initInB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => initInB (a args) (b args) :=
  (cobhamB_allEntB
    (cobhamB_occB (Cobham.proj 1) (cobham_preEnt tagFact (Cobham.proj 0)))
    ha hb Cobham.empty Cobham.empty).of_eq fun args => by simp [initInB, proj]

theorem cobhamB_rootInB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => rootInB (a args) (b args) :=
  (cobhamB_anyEntB
    ((cobhamB_preIsB tagRoot (Cobham.proj 0)).and
      (cobhamB_rootS (cobham_bodyOf (Cobham.proj 0)) (Cobham.proj 1)))
    ha hb Cobham.empty Cobham.empty).of_eq fun args => by simp [rootInB, proj]

theorem cobhamB_initOnlyB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => initOnlyB (a args) (b args) :=
  (cobhamB_allEntB
    (((cobhamB_preIsB tagFact (Cobham.proj 0)).and
        (cobhamB_occB (Cobham.proj 1) (cobham_factOf (cobham_const nilEnt) (Cobham.proj 0)))).or
      ((cobhamB_preIsB tagRoot (Cobham.proj 0)).and
        (cobhamB_rootS (cobham_bodyOf (Cobham.proj 0)) (Cobham.proj 1))))
    ha hb Cobham.empty Cobham.empty).of_eq fun args => by simp [initOnlyB, proj]

theorem cobhamB_initCoreR {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => initCoreR (a args) (b args) :=
  (((cobhamB_initInB hb ha).and (cobhamB_rootInB ha hb)).and
    (cobhamB_initOnlyB ha hb)).of_eq fun _ => rfl

theorem cobhamB_goalInB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => goalInB (a args) (b args) := by
  have hbody : CobhamB fun args : Args =>
      allEntB (fun args2 => occB (args2.getD 1 []) (preEnt tagFact (args2.getD 0 [])))
        (args.getD 0 []) (args.getD 1 []) [] [] :=
    (cobhamB_allEntB (cobhamB_occB (Cobham.proj 1) (cobham_preEnt tagFact (Cobham.proj 0)))
      (Cobham.proj 0) (Cobham.proj 1) Cobham.empty Cobham.empty).of_eq fun args => by simp [proj]
  exact (cobhamB_afterB hbody ha hb Cobham.empty Cobham.empty).of_eq fun _ => rfl

theorem cobhamB_accCoreR {a b c : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => accCoreR (a args) (b args) (c args) :=
  (((cobhamB_head (cobham_rev hc)).and (cobhamB_goalInB hb ha)).and
    (cobhamB_occB ha (cobham_const nilEnt))).of_eq fun _ => rfl

end Space

end HTN
