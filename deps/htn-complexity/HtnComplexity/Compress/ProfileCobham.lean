import HtnComplexity.Complexity.SerIncl
/-!
# Reading a `STRIPS` profile relative to an advice list, in polynomial time

The compression argument of `HtnCompilability/Compress/Cell.lean` needs the profile of a
compiled `STRIPS` instance relative to the facts `V` of the compiled domain to be computable in
polynomial time **uniformly**, with the facts handed over as an advice string.  This file
provides that function.

The advice is the serialised list `A = serNatList W` of the facts.  The function
`HTN.Syn.Compress.profG` reads the advice `A` and the serialisation `Y = instSer q` of an
instance description and returns

* the bit "every goal fact outside `W` holds initially" (`HTN.Syn.Compress.flagB`), followed by
* for every entry boundary of `A`, two bits: whether the entry that starts there is an initial
  fact of `q`, and whether it is a goal fact of `q` (`HTN.Syn.Compress.emitL`).

The number of output bits is `2 |W| + 3`, independently of how long the fact names are
(`HTN.Syn.Compress.length_profG_le`), and equal outputs mean equal profiles
(`HTN.Syn.Compress.profG_eq_imp`).  The function is a member of Cobham's class
(`HTN.Syn.Compress.cobham_profG`).
-/

namespace HTN

namespace Syn

namespace Compress

open PTime

/-! ### A string-valued case distinction (a copy of the selector of the Savitch files) -/

/-- The selector: the second argument if the first one starts with `1`, the third otherwise. -/
def selC : Fn := brnFn (proj 1) (proj 3) (proj 2)

theorem selC_apply (args : Args) :
    selC args = if (args.getD 0 []).headD false = true then args.getD 1 [] else args.getD 2 [] := by
  rcases hb : args.getD 0 [] with _ | ⟨b, t⟩
  · show brnAux (proj 1) (proj 3) (proj 2) (args.getD 0 []) args.tail = _
    rw [hb]
    simp only [brnAux, proj, List.headD_nil]
    rw [if_neg (by simp)]
    simp
  · show brnAux (proj 1) (proj 3) (proj 2) (args.getD 0 []) args.tail = _
    rw [hb]
    have hstep : brnAux (proj 1) (proj 3) (proj 2) (b :: t) args.tail
        = (bif b then (proj 2 : Fn) else proj 3)
          (t :: brnAux (proj 1) (proj 3) (proj 2) t args.tail :: args.tail) := rfl
    rw [hstep]
    rcases b with _ | _
    · simp only [cond_false, proj, List.headD_cons, Bool.false_eq_true, if_false]
      simp
    · simp only [cond_true, proj, List.headD_cons, if_true]
      simp

theorem cobham_selC : Cobham selC := by
  refine Cobham.brn (Cobham.proj 1) (Cobham.proj 3) (Cobham.proj 2)
    (cobham_c2 cobham_append (Cobham.proj 1) (Cobham.proj 2)) fun args => ?_
  have hb : (compFn (fun args : Args => args.getD 0 [] ++ args.getD 1 []) [proj 1, proj 2]
      args).length = (args.getD 1 []).length + (args.getD 2 []).length := by
    simp [compFn, proj]
  rw [show brnFn (proj 1) (proj 3) (proj 2) = selC from rfl, selC_apply, hb]
  by_cases h : (args.getD 0 []).headD false = true
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- A case distinction on a predicate of the class. -/
theorem cobham_iteC {p : Args → Bool} (hp : CobhamB p) {f g : Fn} (hf : Cobham f)
    (hg : Cobham g) : Cobham (fun args => if p args = true then f args else g args) :=
  (cobham_c3 cobham_selC hp hf hg).of_eq' fun args => by
    simp only [compFn, selC_apply]
    by_cases h : p args = true
    · rw [if_pos h, if_pos (by simp [h])]
      simp
    · have hpf : p args = false := by simpa using h
      rw [if_neg h, if_neg (by simp [hpf])]
      simp

/-- Prepending a computed bit. -/
theorem cobham_consB {p : Args → Bool} (hp : CobhamB p) {f : Fn} (hf : Cobham f) :
    Cobham (fun args => p args :: f args) :=
  (cobham_c2 cobham_append hp hf).of_eq' fun args => by simp [compFn]

/-! ### The tests -/

/-- The piece of `s` before its suffix `t`. -/
def cutS (s t : List Bool) : List Bool := s.take (s.length - t.length)

theorem cobham_cut {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => cutS (a args) (b args) := by
  have hT : Cobham fun args : Args =>
      (args.getD 1 []).take ((args.getD 1 []).length - (args.getD 0 []).length) :=
    (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj]
  exact (cobham_c2 hT hb ha).of_eq' fun args => by simp [compFn, cutS]

/-- The initial-state test, arguments `t, s, Y`: the piece of `s` before `t` is one entry, and
it occurs in the list that starts `Y` (the initial state). -/
def initTest (args : Args) : Bool :=
  entryB (cutS (args.getD 1 []) (args.getD 0 [])) &&
    occB (args.getD 2 []) (cutS (args.getD 1 []) (args.getD 0 []))

/-- **Is the entry that starts `s` an initial fact of the instance serialised as `Y`?** -/
def initB (s Y : List Bool) : Bool := anyTailsB initTest [s, Y] s

/-- The goal test, arguments `g, Y, E`: the piece of `Y` before `g` is a complete serialised
list (so `g` is where the goal list starts), and the entry `E` occurs in the list starting `g`. -/
def goalInner (args : Args) : Bool :=
  blistB (cutS (args.getD 1 []) (args.getD 0 [])) && occB (args.getD 0 []) (args.getD 2 [])

/-- Does the entry `E` occur in the goal list of the instance serialised as `Y`? -/
def goalOccB (Y E : List Bool) : Bool := anyTailsB goalInner [Y, E] Y

/-- Arguments `t, s, Y`. -/
def goalTest (args : Args) : Bool :=
  entryB (cutS (args.getD 1 []) (args.getD 0 [])) &&
    goalOccB (args.getD 2 []) (cutS (args.getD 1 []) (args.getD 0 []))

/-- **Is the entry that starts `s` a goal fact of the instance serialised as `Y`?** -/
def goalB (s Y : List Bool) : Bool := anyTailsB goalTest [s, Y] s

/-- The innermost test of the flag, arguments `s₃, s₂, x, A`: the piece between `s₃ ⊑ s₂` is a
single entry, it is not an entry of the advice list `A`, and it does not occur in the initial
list. -/
def aTest3 (args : Args) : Bool :=
  entryB (cutS (args.getD 1 []) (args.getD 0 [])) &&
    !occB (args.getD 3 []) (cutS (args.getD 1 []) (args.getD 0 [])) &&
    !occB (args.getD 2 []) (cutS (args.getD 1 []) (args.getD 0 []))

/-- Arguments `s₂, s₁, x, A`. -/
def aTest2 (args : Args) : Bool :=
  entriesB (cutS (args.getD 1 []) (args.getD 0 [])) &&
    anyTailsB aTest3 [args.getD 0 [], args.getD 2 [], args.getD 3 []] (args.getD 0 [])

/-- Arguments `s₁, x, A`. -/
def aTest1 (args : Args) : Bool :=
  blistB (cutS (args.getD 1 []) (args.getD 0 [])) &&
    anyTailsB aTest2 [args.getD 0 [], args.getD 1 [], args.getD 2 []] (args.getD 0 [])

/-- Is there a goal fact that is neither in the advice list nor initial? -/
def aBadB (A x : List Bool) : Bool := anyTailsB aTest1 [x, A] x

/-- **The flag**: every goal fact outside the advice list holds initially. -/
def flagB (A x : List Bool) : Bool := !aBadB A x

/-! ### The emitted bits -/

/-- A suffix `s` of the advice `A` is an entry boundary. -/
def bnd (A s : List Bool) : Bool := !s.isEmpty && entriesB (cutS A s)

/-- The bits emitted for the suffixes of `x` that are entry boundaries of `A`. -/
def emitL (A Y x : List Bool) : List Bool :=
  (x.tails.filter (bnd A)).flatMap fun s => [initB s Y, goalB s Y]

/-- The step of the recursion, arguments `x, r, A, Y`. -/
def emitStep (b : Bool) (args : Args) : List Bool :=
  if entriesB (cutS (args.getD 2 []) (b :: args.getD 0 [])) = true then
    initB (b :: args.getD 0 []) (args.getD 3 []) ::
      goalB (b :: args.getD 0 []) (args.getD 3 []) :: args.getD 1 []
  else args.getD 1 []

/-- The recursion computing the emitted bits, arguments `x, A, Y`. -/
def emitFn : Fn := brnFn (fun _ => []) (emitStep false) (emitStep true)

/-- **The profile reader**, arguments `A, Y`. -/
def profG (args : Args) : List Bool :=
  flagB (args.getD 0 []) (args.getD 1 []) ::
    emitL (args.getD 0 []) (args.getD 1 []) (args.getD 0 [])

/-! ### The recursion computes the emitted bits -/

theorem emitL_nil (A Y : List Bool) : emitL A Y [] = [] := by
  simp [emitL, bnd]

theorem emitL_cons (A Y : List Bool) (b : Bool) (x : List Bool) :
    emitL A Y (b :: x) =
      (if entriesB (cutS A (b :: x)) = true then [initB (b :: x) Y, goalB (b :: x) Y] else []) ++
        emitL A Y x := by
  unfold emitL
  rw [List.tails_cons, List.filter_cons]
  by_cases h : entriesB (cutS A (b :: x)) = true
  · simp [bnd, h]
  · simp [bnd, h]

theorem brnAux_emit (A Y : List Bool) : ∀ x : List Bool,
    brnAux (fun _ => []) (emitStep false) (emitStep true) x [A, Y] = emitL A Y x := by
  intro x
  induction x with
  | nil => simp [brnAux, emitL_nil]
  | cons b x ih =>
    have hstep : brnAux (fun _ => []) (emitStep false) (emitStep true) (b :: x) [A, Y]
        = emitStep b (x :: brnAux (fun _ => []) (emitStep false) (emitStep true) x [A, Y] ::
            [A, Y]) := by
      cases b <;> rfl
    rw [hstep, ih, emitL_cons]
    by_cases h : entriesB (cutS A (b :: x)) = true
    · simp [emitStep, h]
    · simp [emitStep, h]

theorem emitFn_apply (A Y : List Bool) (x : List Bool) : emitFn [x, A, Y] = emitL A Y x :=
  brnAux_emit A Y x

theorem length_emitL_le (A Y : List Bool) : ∀ x, (emitL A Y x).length ≤ 2 * x.length := by
  intro x
  induction x with
  | nil => simp [emitL_nil]
  | cons b x ih =>
    rw [emitL_cons]
    split <;> simp <;> omega

/-! ### Membership in Cobham's class -/

theorem cobhamB_initTest : CobhamB initTest := by
  have hE := cobham_cut (Cobham.proj 1) (Cobham.proj 0)
  exact ((cobhamB_entryB hE).and (cobhamB_occB (Cobham.proj 2) hE)).of_eq fun args => by
    simp [initTest, proj]

theorem argDep_initTest : ArgDep 3 initTest := by
  intro args
  simp only [initTest, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_initB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => initB (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_initTest argDep_initTest).comp3 ha ha hb).of_eq fun args => by
    simp [initB]

theorem cobhamB_goalInner : CobhamB goalInner := by
  have hE := cobham_cut (Cobham.proj 1) (Cobham.proj 0)
  exact ((cobhamB_blistB hE).and (cobhamB_occB (Cobham.proj 0) (Cobham.proj 2))).of_eq
    fun args => by simp [goalInner, proj]

theorem argDep_goalInner : ArgDep 3 goalInner := by
  intro args
  simp only [goalInner, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_goalOccB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => goalOccB (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_goalInner argDep_goalInner).comp3 ha ha hb).of_eq fun args => by
    simp [goalOccB]

theorem cobhamB_goalTest : CobhamB goalTest := by
  have hE := cobham_cut (Cobham.proj 1) (Cobham.proj 0)
  exact ((cobhamB_entryB hE).and (cobhamB_goalOccB (Cobham.proj 2) hE)).of_eq fun args => by
    simp [goalTest, proj]

theorem argDep_goalTest : ArgDep 3 goalTest := by
  intro args
  simp only [goalTest, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_goalB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => goalB (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_goalTest argDep_goalTest).comp3 ha ha hb).of_eq fun args => by
    simp [goalB]

theorem cobhamB_aTest3 : CobhamB aTest3 := by
  have hE := cobham_cut (Cobham.proj 1) (Cobham.proj 0)
  exact (((cobhamB_entryB hE).and (cobhamB_occB (Cobham.proj 3) hE).not).and
    (cobhamB_occB (Cobham.proj 2) hE).not).of_eq fun args => by simp [aTest3, proj]

theorem argDep_aTest3 : ArgDep 4 aTest3 := by
  intro args
  simp only [aTest3, getD_padArgs (by norm_num : (0 : ℕ) < 4),
    getD_padArgs (by norm_num : (1 : ℕ) < 4), getD_padArgs (by norm_num : (2 : ℕ) < 4),
    getD_padArgs (by norm_num : (3 : ℕ) < 4)]

theorem cobhamB_aTest2 : CobhamB aTest2 := by
  have hpre := cobham_cut (Cobham.proj 1) (Cobham.proj 0)
  have hany := (cobhamB_anyTails cobhamB_aTest3 argDep_aTest3).comp4
    (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 2) (Cobham.proj 3)
  exact ((cobhamB_entriesB hpre).and hany).of_eq fun args => by simp [aTest2, proj]

theorem argDep_aTest2 : ArgDep 4 aTest2 := by
  intro args
  simp only [aTest2, getD_padArgs (by norm_num : (0 : ℕ) < 4),
    getD_padArgs (by norm_num : (1 : ℕ) < 4), getD_padArgs (by norm_num : (2 : ℕ) < 4),
    getD_padArgs (by norm_num : (3 : ℕ) < 4)]

theorem cobhamB_aTest1 : CobhamB aTest1 := by
  have hpre := cobham_cut (Cobham.proj 1) (Cobham.proj 0)
  have hany := (cobhamB_anyTails cobhamB_aTest2 argDep_aTest2).comp4
    (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2)
  exact ((cobhamB_blistB hpre).and hany).of_eq fun args => by simp [aTest1, proj]

theorem argDep_aTest1 : ArgDep 3 aTest1 := by
  intro args
  simp only [aTest1, getD_padArgs (by norm_num : (0 : ℕ) < 3),
    getD_padArgs (by norm_num : (1 : ℕ) < 3), getD_padArgs (by norm_num : (2 : ℕ) < 3)]

theorem cobhamB_flagB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => flagB (a args) (b args) :=
  ((cobhamB_anyTails cobhamB_aTest1 argDep_aTest1).comp3 hb hb ha).not.of_eq fun args => by
    simp [flagB, aBadB]

theorem cobham_emitStep (b : Bool) : Cobham (emitStep b) := by
  have hs : Cobham fun args : Args => b :: args.getD 0 [] :=
    (cobham_c1 (Cobham.cons b) (Cobham.proj 0)).of_eq' fun args => by simp [compFn, consFn, proj]
  have hc := cobhamB_entriesB (cobham_cut (Cobham.proj 2) hs)
  have hthen := cobham_consB (cobhamB_initB hs (Cobham.proj 3))
    (cobham_consB (cobhamB_goalB hs (Cobham.proj 3)) (Cobham.proj 1))
  exact (cobham_iteC hc hthen (Cobham.proj 1)).of_eq' fun args => by
    simp [emitStep, proj]

theorem cobham_emitFn : Cobham emitFn := by
  refine Cobham.brn Cobham.empty (cobham_emitStep false) (cobham_emitStep true)
    (cobham_c2 cobham_append (Cobham.proj 0) (Cobham.proj 0)) fun args => ?_
  have hlen : ∀ x v, (brnAux (fun _ => []) (emitStep false) (emitStep true) x v).length
      ≤ 2 * x.length := by
    intro x v
    induction x with
    | nil => simp [brnAux]
    | cons b x ih =>
      have hstep : brnAux (fun _ => []) (emitStep false) (emitStep true) (b :: x) v
          = emitStep b (x :: brnAux (fun _ => []) (emitStep false) (emitStep true) x v :: v) := by
        cases b <;> rfl
      rw [hstep, emitStep]
      split <;> simp <;> omega
  have := hlen (args.getD 0 []) args.tail
  simp only [compFn, proj, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    List.length_append]
  exact le_trans this (by omega)

/-- **The profile reader is a function of Cobham's class.** -/
theorem cobham_profG : Cobham profG := by
  have hemit : Cobham fun args : Args =>
      emitL (args.getD 0 []) (args.getD 1 []) (args.getD 0 []) :=
    (cobham_c3 cobham_emitFn (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 1)).of_eq'
      fun args => by simp [compFn, proj, emitFn_apply]
  exact (cobham_consB (cobhamB_flagB (Cobham.proj 0) (Cobham.proj 1)) hemit).of_eq'
    fun args => by simp [profG, proj]

/-! ### Correctness -/

theorem cutS_append (p s : List Bool) : cutS (p ++ s) s = p := take_compl p s

theorem instSer_split (q : InstDesc) :
    instSer q = blist (q.initList.map bitsOfNat) ++
      (blist (q.goalList.map bitsOfNat) ++ tnSer q.tnI) := by
  rw [instSer, serNatList_eq, serNatList_eq]
  simp

theorem occB_adv (W : List ℕ) (w : List Bool) :
    occB (serNatList W) (true :: bstr w) = true ↔ w ∈ W.map bitsOfNat := by
  have := occB_iff (W.map bitsOfNat) [] w
  rwa [List.append_nil, ← serNatList_eq] at this

theorem mem_map_bitsOfNat {f : ℕ} {l : List ℕ} : bitsOfNat f ∈ l.map bitsOfNat ↔ f ∈ l := by
  constructor
  · intro h
    obtain ⟨g, hg, he⟩ := List.mem_map.1 h
    rwa [← bitsOfNat_injective he]
  · exact List.mem_map_of_mem

/-- The entry that starts a serialised list is cut out uniquely. -/
theorem entry_cut {w : List Bool} {rest : List (List Bool)} {t : List Bool}
    (ht : t <:+ blist (w :: rest)) (he : entryB (cutS (blist (w :: rest)) t) = true) :
    cutS (blist (w :: rest)) t = true :: bstr w := by
  obtain ⟨w', hw'⟩ := entryB_iff.1 he
  have hsplit : cutS (blist (w :: rest)) t ++ t = blist (w :: rest) := suffix_take_append ht
  rw [hw', blist_cons] at hsplit
  simp only [List.cons_append, List.cons.injEq, true_and] at hsplit
  obtain ⟨h, -⟩ := bstr_parse hsplit
  rw [hw', h]

theorem cutS_blist_cons (w : List Bool) (rest : List (List Bool)) :
    cutS (blist (w :: rest)) (blist rest) = true :: bstr w := by
  rw [blist_cons, show true :: (bstr w ++ blist rest) = (true :: bstr w) ++ blist rest from rfl,
    cutS_append]

theorem suffix_blist_cons (w : List Bool) (rest : List (List Bool)) :
    blist rest <:+ blist (w :: rest) := ⟨true :: bstr w, by simp⟩

/-- **The initial-state bit.** -/
theorem initB_iff (w : List Bool) (rest : List (List Bool)) (q : InstDesc) :
    initB (blist (w :: rest)) (instSer q) = true ↔ w ∈ q.initList.map bitsOfNat := by
  rw [initB, anyTailsB_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    simp only [initTest, List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
    rw [entry_cut ht h.1, instSer_split] at h
    exact (occB_iff _ _ w).1 h.2
  · intro hw
    refine ⟨blist rest, suffix_blist_cons w rest, ?_⟩
    simp only [initTest, List.getD_cons_zero, List.getD_cons_succ, cutS_blist_cons,
      Bool.and_eq_true]
    exact ⟨entryB_iff.2 ⟨w, rfl⟩, by rw [instSer_split]; exact (occB_iff _ _ w).2 hw⟩

theorem goalOccB_iff (q : InstDesc) (w : List Bool) :
    goalOccB (instSer q) (true :: bstr w) = true ↔ w ∈ q.goalList.map bitsOfNat := by
  rw [goalOccB, anyTailsB_eq_true]
  constructor
  · rintro ⟨g, hg, h⟩
    simp only [goalInner, List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
    obtain ⟨l, hl⟩ := blistB_iff.1 h.1
    have hsplit : cutS (instSer q) g ++ g = instSer q := suffix_take_append hg
    rw [hl] at hsplit
    rw [instSer_split] at hsplit
    obtain ⟨-, hg'⟩ := blist_parse hsplit
    have h2 := h.2
    rw [hg'] at h2
    exact (occB_iff _ _ w).1 h2
  · intro hw
    refine ⟨blist (q.goalList.map bitsOfNat) ++ tnSer q.tnI, ?_, ?_⟩
    · rw [instSer_split]
      exact List.suffix_append _ _
    · simp only [goalInner, List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
      rw [instSer_split, cutS_append]
      exact ⟨blistB_iff.2 ⟨_, rfl⟩, (occB_iff _ _ w).2 hw⟩

/-- **The goal bit.** -/
theorem goalB_iff (w : List Bool) (rest : List (List Bool)) (q : InstDesc) :
    goalB (blist (w :: rest)) (instSer q) = true ↔ w ∈ q.goalList.map bitsOfNat := by
  rw [goalB, anyTailsB_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    simp only [goalTest, List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
    rw [entry_cut ht h.1] at h
    exact (goalOccB_iff q w).1 h.2
  · intro hw
    refine ⟨blist rest, suffix_blist_cons w rest, ?_⟩
    simp only [goalTest, List.getD_cons_zero, List.getD_cons_succ, cutS_blist_cons,
      Bool.and_eq_true]
    exact ⟨entryB_iff.2 ⟨w, rfl⟩, (goalOccB_iff q w).2 hw⟩

theorem aBadB_eq_true {A x : List Bool} :
    aBadB A x = true ↔ ∃ s₁, s₁ <:+ x ∧ blistB (cutS x s₁) = true ∧
      ∃ s₂, s₂ <:+ s₁ ∧ entriesB (cutS s₁ s₂) = true ∧
        ∃ s₃, s₃ <:+ s₂ ∧ entryB (cutS s₂ s₃) = true ∧ occB A (cutS s₂ s₃) = false ∧
          occB x (cutS s₂ s₃) = false := by
  simp only [aBadB, aTest1, aTest2, aTest3, anyTailsB_eq_true, List.getD_cons_zero,
    List.getD_cons_succ, Bool.and_eq_true, Bool.not_eq_true', and_assoc]

/-- **The flag finds a bad goal fact exactly when there is one.** -/
theorem aBadB_iff (W : List ℕ) (q : InstDesc) :
    aBadB (serNatList W) (instSer q) = true ↔ ∃ f ∈ q.goalList, f ∉ W ∧ f ∉ q.initList := by
  set I : List (List Bool) := q.initList.map bitsOfNat with hI
  set G : List (List Bool) := q.goalList.map bitsOfNat with hG
  set z : List Bool := tnSer q.tnI with hz
  have hx : instSer q = blist I ++ (blist G ++ z) := instSer_split q
  rw [aBadB_eq_true]
  constructor
  · rintro ⟨s₁, hs₁, hb, s₂, hs₂, he, s₃, hs₃, hent, hA, hocc⟩
    obtain ⟨l, hl⟩ := blistB_iff.1 hb
    have hcut₁ : blist l ++ s₁ = blist I ++ (blist G ++ z) := by
      rw [← hl, ← hx]
      exact suffix_take_append hs₁
    obtain ⟨-, hs₁eq⟩ := blist_parse hcut₁
    obtain ⟨a, ha⟩ := entriesB_iff.1 he
    have hcut₂ : entriesEnc a ++ s₂ = blist G ++ z := by
      rw [← ha, ← hs₁eq]
      exact suffix_take_append hs₂
    obtain ⟨G₂, hGeq, hs₂eq⟩ := entriesEnc_align a s₂ G z hcut₂
    obtain ⟨w, hw⟩ := entryB_iff.1 hent
    rw [hw] at hA hocc
    have hcut₃ : (true :: bstr w) ++ s₃ = blist G₂ ++ z := by
      rw [← hw, ← hs₂eq]
      exact suffix_take_append hs₃
    obtain ⟨G₂', hG₂, -⟩ := entry_split hcut₃
    have hwG : w ∈ G := by
      rw [hGeq, hG₂]
      exact List.mem_append_right a List.mem_cons_self
    obtain ⟨f, hf, hfw⟩ := List.mem_map.1 hwG
    subst hfw
    refine ⟨f, hf, fun hfW => ?_, fun hinit => ?_⟩
    · have : occB (serNatList W) (true :: bstr (bitsOfNat f)) = true :=
        (occB_adv W _).2 (List.mem_map_of_mem hfW)
      rw [this] at hA
      exact absurd hA (by simp)
    · have hoc : occB (instSer q) (true :: bstr (bitsOfNat f)) = true := by
        rw [hx]
        exact (occB_iff I (blist G ++ z) _).2 (List.mem_map_of_mem hinit)
      rw [hoc] at hocc
      exact absurd hocc (by simp)
  · rintro ⟨f, hf, hfW, hinit⟩
    set w : List Bool := bitsOfNat f with hwdef
    have hwG : w ∈ G := List.mem_map_of_mem hf
    obtain ⟨G₁, G₂', hGsplit⟩ := List.append_of_mem hwG
    have hgoal : blist G ++ z = entriesEnc G₁ ++ (blist (w :: G₂') ++ z) := by
      rw [hGsplit, blist_append_eq, List.append_assoc]
    have hentry : blist (w :: G₂') ++ z = (true :: bstr w) ++ (blist G₂' ++ z) := by
      rw [blist_cons]
      simp
    refine ⟨blist G ++ z, ⟨blist I, hx.symm⟩, ?_,
      blist (w :: G₂') ++ z, ⟨entriesEnc G₁, hgoal.symm⟩, ?_,
      blist G₂' ++ z, ⟨true :: bstr w, hentry.symm⟩, ?_, ?_, ?_⟩
    · rw [hx, cutS_append]
      exact blistB_iff.2 ⟨I, rfl⟩
    · rw [hgoal, cutS_append]
      exact entriesB_iff.2 ⟨G₁, rfl⟩
    · rw [hentry, cutS_append]
      exact entryB_iff.2 ⟨w, rfl⟩
    · rw [hentry, cutS_append]
      cases h : occB (serNatList W) (true :: bstr w)
      · rfl
      · exact absurd (mem_map_bitsOfNat.1 ((occB_adv W w).1 h)) hfW
    · rw [hentry, cutS_append, hx]
      cases h : occB (blist I ++ (blist G ++ z)) (true :: bstr w)
      · rfl
      · exact absurd (mem_map_bitsOfNat.1 ((occB_iff I _ w).1 h)) hinit

/-- **The flag bit.** -/
theorem flagB_iff (W : List ℕ) (q : InstDesc) :
    flagB (serNatList W) (instSer q) = true ↔ ∀ f ∈ q.goalList, f ∉ W → f ∈ q.initList := by
  rw [flagB, Bool.not_eq_true', ← Bool.not_eq_true, aBadB_iff]
  push_neg
  rfl

theorem flatMap_pair_eq {L : List (List Bool)} {a b a' b' : List Bool → Bool}
    (h : L.flatMap (fun s => [a s, b s]) = L.flatMap (fun s => [a' s, b' s])) :
    ∀ s ∈ L, a s = a' s ∧ b s = b' s := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact ⟨h.1, h.2.1⟩
    · exact ih h.2.2 s' hs'

theorem length_flatMap_pair (L : List (List Bool)) (a b : List Bool → Bool) :
    (L.flatMap fun s => [a s, b s]).length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    ring

theorem mem_bnd_of_mem (W : List ℕ) {f : ℕ} (hf : f ∈ W) :
    ∃ rest, blist (bitsOfNat f :: rest) ∈ (serNatList W).tails.filter (bnd (serNatList W)) := by
  obtain ⟨W₁, rest, hsplit⟩ := List.append_of_mem (List.mem_map_of_mem (f := bitsOfNat) hf)
  have hA : serNatList W = entriesEnc W₁ ++ blist (bitsOfNat f :: rest) := by
    rw [serNatList_eq, hsplit, blist_append_eq]
  refine ⟨rest, List.mem_filter.2 ⟨(List.mem_tails _ _).2 ⟨entriesEnc W₁, hA.symm⟩, ?_⟩⟩
  rw [hA, bnd, cutS_append, entriesB_iff.2 ⟨W₁, rfl⟩]
  simp

/-- **Equal outputs of the profile reader mean equal profiles.** -/
theorem profG_eq_imp (W : List ℕ) {q q' : InstDesc}
    (h : profG [serNatList W, instSer q] = profG [serNatList W, instSer q']) :
    (∀ f ∈ W, (f ∈ q.initList ↔ f ∈ q'.initList) ∧ (f ∈ q.goalList ↔ f ∈ q'.goalList)) ∧
      ((∀ f ∈ q.goalList, f ∉ W → f ∈ q.initList) ↔
        (∀ f ∈ q'.goalList, f ∉ W → f ∈ q'.initList)) := by
  simp only [profG, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, emitL] at h
  obtain ⟨hflag, hemit⟩ := h
  have hpt := flatMap_pair_eq hemit
  refine ⟨fun f hf => ?_, by rw [← flagB_iff, ← flagB_iff, hflag]⟩
  obtain ⟨rest, hmem⟩ := mem_bnd_of_mem W hf
  obtain ⟨hI, hG⟩ := hpt _ hmem
  constructor
  · rw [← mem_map_bitsOfNat (l := q.initList), ← mem_map_bitsOfNat (l := q'.initList),
      ← initB_iff _ rest, ← initB_iff _ rest, hI]
  · rw [← mem_map_bitsOfNat (l := q.goalList), ← mem_map_bitsOfNat (l := q'.goalList),
      ← goalB_iff _ rest, ← goalB_iff _ rest, hG]

theorem nodup_tails_bool : ∀ l : List Bool, l.tails.Nodup
  | [] => by simp
  | b :: l => by
    rw [List.tails_cons, List.nodup_cons]
    refine ⟨fun h => ?_, nodup_tails_bool l⟩
    have := ((List.mem_tails _ _).1 h).length_le
    simp at this

theorem bnd_subset (W : List ℕ) :
    (serNatList W).tails.filter (bnd (serNatList W)) ⊆ (W.map bitsOfNat).tails.map blist := by
  intro s hs
  obtain ⟨hs₁, hb⟩ := List.mem_filter.1 hs
  have hsuf := (List.mem_tails _ _).1 hs₁
  simp only [bnd, Bool.and_eq_true] at hb
  obtain ⟨a, ha⟩ := entriesB_iff.1 hb.2
  have hcut : entriesEnc a ++ s = blist (W.map bitsOfNat) ++ [] := by
    rw [List.append_nil, ← ha, ← serNatList_eq]
    exact suffix_take_append hsuf
  obtain ⟨l₂, hl, hs'⟩ := entriesEnc_align a s _ [] hcut
  refine List.mem_map.2 ⟨l₂, (List.mem_tails _ _).2 ⟨a, hl.symm⟩, ?_⟩
  simpa using hs'.symm

/-- **The output of the profile reader has `2 |W| + 3` bits**, however long the facts are. -/
theorem length_profG_le (W : List ℕ) (Y : List Bool) :
    (profG [serNatList W, Y]).length ≤ 2 * W.length + 3 := by
  have hnd : ((serNatList W).tails.filter (bnd (serNatList W))).Nodup :=
    (nodup_tails_bool _).filter _
  have hle := (hnd.subperm (bnd_subset W)).length_le
  simp only [List.length_map, List.length_tails] at hle
  simp only [profG, List.getD_cons_zero, List.getD_cons_succ, List.length_cons, emitL,
    length_flatMap_pair]
  omega

end Compress

end Syn

end HTN
