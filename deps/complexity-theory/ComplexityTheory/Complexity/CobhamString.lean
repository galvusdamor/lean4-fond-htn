import ComplexityTheory.Complexity.CobhamDFA
import ComplexityTheory.Complexity.PolyTimeTM
import ComplexityTheory.Complexity.Basic
/-!
# A string toolkit inside Cobham's class

`ComplexityTheory/Complexity/CobhamDFA.lean` shows that a *finite-state* scan of a bit string
is polynomial time.  That is not enough to read a description off its serialisation: the
remaining components of the bounded profile of
`HtnCompilability/Computable/RootedDecide.lean` compare two unbounded numerals that sit at
different places of the code, which no finite-state scan can do.

This file supplies the missing primitives, all of them as **closure properties** of Cobham's
class, so that they compose:

* `HTN.PTime.cobham_tailFn`, `HTN.PTime.cobham_dropFn` — dropping one character, and dropping as
  many characters as a second string is long.  Positions in a string are named in this
  development by *suffixes*, and `dropFn` is what turns a suffix into a position;
* `HTN.PTime.cobham_trunc`, `HTN.PTime.cobham_take` — the complementary prefix of a suffix, and
  the prefix of a given length.  Both are dropping conjugated by reversal;
* `HTN.PTime.CobhamB` — a *predicate* of Cobham's class: one whose one-bit answer is computed by
  a function of the class.  Closed under Boolean operations (`HTN.PTime.CobhamB.op2`), and with
  the primitive tests `HTN.PTime.cobhamB_head` (the first character), `…_null` (emptiness),
  `…_lenLE` (a comparison of lengths) and `…_isSuffix` / `…_eqStr` / `…_isPrefix` (comparison of
  two computed strings);
* `HTN.PTime.cobhamB_anyTails` — **bounded existential quantification over the suffixes of a
  string**.  This is what replaces the finite-state scan: the body may be any predicate of the
  class, applied to the suffix and to the ambient arguments, so quantifiers nest.

Together they express any algorithm of the shape "there are positions `p₁ … pₖ` in the input
such that the substrings they cut out satisfy a test built from string comparisons", which is
what reading a self-delimiting serialisation amounts to.
-/

namespace HTN

namespace PTime

/-! ### Composition helpers -/

theorem cobham_c1 {g f : Fn} (hg : Cobham g) (hf : Cobham f) : Cobham (compFn g [f]) :=
  Cobham.comp hg (by intro h hh; rw [List.mem_singleton.1 hh]; exact hf)

theorem cobham_c2 {g f₁ f₂ : Fn} (hg : Cobham g) (h₁ : Cobham f₁) (h₂ : Cobham f₂) :
    Cobham (compFn g [f₁, f₂]) := by
  refine Cobham.comp hg ?_
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact h₁
  · exact h₂

theorem cobham_c3 {g f₁ f₂ f₃ : Fn} (hg : Cobham g) (h₁ : Cobham f₁) (h₂ : Cobham f₂)
    (h₃ : Cobham f₃) : Cobham (compFn g [f₁, f₂, f₃]) := by
  refine Cobham.comp hg ?_
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃

theorem cobham_c4 {g f₁ f₂ f₃ f₄ : Fn} (hg : Cobham g) (h₁ : Cobham f₁) (h₂ : Cobham f₂)
    (h₃ : Cobham f₃) (h₄ : Cobham f₄) : Cobham (compFn g [f₁, f₂, f₃, f₄]) := by
  refine Cobham.comp hg ?_
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

/-- Cobham membership only depends on the function. -/
theorem Cobham.of_eq' {f g : Fn} (hf : Cobham f) (h : ∀ args, f args = g args) : Cobham g := by
  have : f = g := funext h
  rwa [this] at hf

/-! ### Dropping characters -/

/-- The first argument without its first character. -/
def tailFn : Fn := brnFn (fun _ => []) (proj 0) (proj 0)

theorem tailFn_apply (args : Args) : tailFn args = (args.getD 0 []).tail := by
  show brnAux _ _ _ (args.getD 0 []) args.tail = _
  cases h : (args.getD 0 []) with
  | nil => rfl
  | cons b x => cases b <;> rfl

theorem cobham_tailFn : Cobham tailFn := by
  refine Cobham.brn Cobham.empty (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 0) ?_
  intro args
  show (brnFn _ _ _ args).length ≤ _
  rw [show brnFn (fun _ => ([] : List Bool)) (proj 0) (proj 0) = tailFn from rfl, tailFn_apply]
  simp [proj]

/-- The second argument with as many characters removed from the front as the first argument is
long. -/
def dropFn : Fn := brnFn (proj 0) (compFn tailFn [proj 1]) (compFn tailFn [proj 1])

theorem brnAux_drop (v : Args) : ∀ x : List Bool,
    brnAux (proj 0) (compFn tailFn [proj 1]) (compFn tailFn [proj 1]) x v
      = (v.getD 0 []).drop x.length := by
  intro x
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h : brnAux (proj 0) (compFn tailFn [proj 1]) (compFn tailFn [proj 1]) (b :: x) v
        = (brnAux (proj 0) (compFn tailFn [proj 1]) (compFn tailFn [proj 1]) x v).tail := by
      cases b <;> simp [brnAux, compFn, proj, tailFn_apply]
    rw [h, ih, List.length_cons, ← List.drop_drop]
    simp

theorem dropFn_apply (args : Args) :
    dropFn args = (args.getD 1 []).drop (args.getD 0 []).length := by
  show brnAux _ _ _ (args.getD 0 []) args.tail = _
  rw [brnAux_drop]
  cases args with
  | nil => rfl
  | cons a as => rfl

theorem cobham_dropFn : Cobham dropFn := by
  have h : Cobham (compFn tailFn [proj 1]) := cobham_c1 cobham_tailFn (Cobham.proj 1)
  refine Cobham.brn (Cobham.proj 0) h h (Cobham.proj 1) ?_
  intro args
  rw [show brnFn (proj 0) (compFn tailFn [proj 1]) (compFn tailFn [proj 1]) = dropFn from rfl,
    dropFn_apply]
  simp [proj]

/-- **Dropping a computed number of characters**, as a closure property. -/
theorem cobham_drop {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham (fun args => (b args).drop (a args).length) :=
  (cobham_c2 cobham_dropFn ha hb).of_eq' fun args => by simp [compFn, dropFn_apply]

/-- **Reversal**, as a closure property. -/
theorem cobham_rev {a : Fn} (ha : Cobham a) : Cobham (fun args => (a args).reverse) :=
  (cobham_c1 cobham_revFn ha).of_eq' fun args => by simp [compFn, revFn_apply]

theorem reverse_drop_reverse (y : List Bool) (k : ℕ) :
    (y.reverse.drop k).reverse = y.take (y.length - k) := by
  rw [List.reverse_drop]
  simp

/-- **The complementary prefix**: the second argument with as many characters removed from the
*end* as the first argument is long.  If the first argument is a suffix of the second, this is
the prefix that precedes it. -/
theorem cobham_trunc {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham (fun args => (b args).take ((b args).length - (a args).length)) :=
  (cobham_rev (cobham_drop ha (cobham_rev hb))).of_eq' fun args => by
    rw [reverse_drop_reverse]

/-- **The prefix of a computed length**. -/
theorem cobham_take {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham (fun args => (b args).take (a args).length) :=
  (cobham_trunc (cobham_drop ha hb) hb).of_eq' fun args => by
    rcases le_total (a args).length (b args).length with h | h
    · rw [List.length_drop, Nat.sub_sub_self h]
    · rw [List.drop_eq_nil_of_le h]
      simp [List.take_of_length_le h]

/-! ### Predicates of the class -/

theorem CobhamB.of_eq {p q : Args → Bool} (hp : CobhamB p) (h : ∀ args, q args = p args) :
    CobhamB q := hp.of_eq' fun args => by rw [h]

theorem cobhamB_const (b : Bool) : CobhamB (fun _ => b) := cobham_const [b]

/-- Two one-bit answers may be combined by any Boolean operation. -/
theorem CobhamB.op2 {p q : Args → Bool} (hp : CobhamB p) (hq : CobhamB q)
    (op : Bool → Bool → Bool) : CobhamB (fun args => op (p args) (q args)) := by
  set T : List Bool → List Bool := fun z => [op (z.getD 0 false) (z.getD 1 false)] with hT
  have hdep : ∀ x, T x = T (x.take 2) := by
    intro x
    match x with
    | [] => rfl
    | [a] => rfl
    | a :: b :: t => rfl
  have htab : Cobham (fun args : Args => T (args.getD 0 [])) :=
    cobham_ofTake 2 1 T hdep (fun x => by simp [hT])
  have happ : Cobham (fun args : Args => [p args] ++ [q args]) :=
    (cobham_c2 cobham_append hp hq).of_eq' fun args => by simp [compFn]
  exact (cobham_c1 htab happ).of_eq' fun args => by simp [compFn, hT]

theorem CobhamB.not {p : Args → Bool} (hp : CobhamB p) : CobhamB (fun args => !p args) :=
  (hp.op2 hp (fun a _ => !a)).of_eq fun _ => rfl

theorem CobhamB.and {p q : Args → Bool} (hp : CobhamB p) (hq : CobhamB q) :
    CobhamB (fun args => p args && q args) := hp.op2 hq (· && ·)

theorem CobhamB.or {p q : Args → Bool} (hp : CobhamB p) (hq : CobhamB q) :
    CobhamB (fun args => p args || q args) := hp.op2 hq (· || ·)

/-- The first character of a computed string. -/
theorem cobhamB_head {a : Fn} (ha : Cobham a) : CobhamB (fun args => (a args).headD false) := by
  set T : List Bool → List Bool := fun z => [z.headD false] with hT
  have hdep : ∀ x, T x = T (x.take 1) := by
    intro x
    match x with
    | [] => rfl
    | a :: t => rfl
  have htab : Cobham (fun args : Args => T (args.getD 0 [])) :=
    cobham_ofTake 1 1 T hdep (fun x => by simp [hT])
  exact (cobham_c1 htab ha).of_eq' fun args => by simp [compFn, hT]

/-- Emptiness of a computed string. -/
theorem cobhamB_null {a : Fn} (ha : Cobham a) : CobhamB (fun args => decide (a args = [])) := by
  set T : List Bool → List Bool := fun z => [decide (z = [])] with hT
  have hdep : ∀ x, T x = T (x.take 1) := by
    intro x
    match x with
    | [] => rfl
    | a :: t => rfl
  have htab : Cobham (fun args : Args => T (args.getD 0 [])) :=
    cobham_ofTake 1 1 T hdep (fun x => by simp [hT])
  exact (cobham_c1 htab ha).of_eq' fun args => by simp [compFn, hT]

/-- A comparison of lengths. -/
theorem cobhamB_lenLE {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB (fun args => decide ((a args).length ≤ (b args).length)) :=
  (cobhamB_null (cobham_drop hb ha)).of_eq fun args => by
    simp [List.drop_eq_nil_iff]

/-! ### Comparing two computed strings -/

/-- The step of the recursion deciding "is the first argument a suffix of the second". -/
def sufStep (b : Bool) (args : Args) : Bool :=
  ((args.getD 1 []).headD false) &&
    decide ((b :: args.getD 0 []).length ≤ (args.getD 2 []).length) &&
    decide (((args.getD 2 []).drop
      ((args.getD 2 []).length - (b :: args.getD 0 []).length)).headD false = b)

theorem cobhamB_sufStep (b : Bool) : CobhamB (sufStep b) := by
  have hU : Cobham (consFn b) := Cobham.cons b
  have hV : Cobham (proj 2) := Cobham.proj 2
  have h1 : CobhamB (fun args : Args => (args.getD 1 []).headD false) :=
    (cobhamB_head (Cobham.proj 1)).of_eq fun args => by simp [proj]
  have h2 : CobhamB (fun args : Args =>
      decide ((b :: args.getD 0 []).length ≤ (args.getD 2 []).length)) :=
    (cobhamB_lenLE hU hV).of_eq fun args => by simp [consFn, proj]
  have hlast : Cobham (fun args : Args =>
      (args.getD 2 []).drop ((args.getD 2 []).length - (b :: args.getD 0 []).length)) :=
    (cobham_drop (cobham_drop hU hV) hV).of_eq' fun args => by simp [consFn, proj]
  have h3 : CobhamB (fun args : Args =>
      decide (((args.getD 2 []).drop
        ((args.getD 2 []).length - (b :: args.getD 0 []).length)).headD false = b)) :=
    ((cobhamB_head hlast).op2 (cobhamB_const b) (fun x y => decide (x = y))).of_eq fun args => rfl
  exact ((h1.and h2).and h3)

/-- Deciding "the first argument is a suffix of the second". -/
def sufFn : Fn :=
  brnFn (fun _ => [true]) (fun args => [sufStep false args]) (fun args => [sufStep true args])

theorem suffix_cons_iff (b : Bool) (u v : List Bool) :
    (b :: u) <:+ v ↔ u <:+ v ∧ (b :: u).length ≤ v.length ∧
      (v.drop (v.length - (b :: u).length)).headD false = b := by
  constructor
  · intro h
    have hlen : (b :: u).length ≤ v.length := h.length_le
    refine ⟨(List.suffix_cons _ _).trans h, hlen, ?_⟩
    have hd : v.drop (v.length - (b :: u).length) = b :: u :=
      (List.suffix_iff_eq_drop.1 h).symm
    rw [hd]
    rfl
  · rintro ⟨hu, hlen, hhead⟩
    have hu' : u = v.drop (v.length - u.length) := List.suffix_iff_eq_drop.1 hu
    have hk : v.length - (b :: u).length + 1 = v.length - u.length := by
      simp only [List.length_cons] at hlen ⊢
      omega
    have hsuf : v.drop (v.length - (b :: u).length) <:+ v := List.drop_suffix _ _
    have hlt : v.length - (b :: u).length < v.length := by
      simp only [List.length_cons] at hlen ⊢
      omega
    have hdrop := List.drop_eq_getElem_cons hlt
    rw [hdrop] at hhead
    simp only [List.headD_cons] at hhead
    have hcons : v.drop (v.length - (b :: u).length) = b :: u := by
      rw [hdrop, hhead, hk, ← hu']
    rwa [hcons] at hsuf

theorem sufStep_apply (b : Bool) (u : List Bool) (v : Args) :
    sufStep b (u :: [decide (u <:+ v.getD 0 [])] :: v)
      = decide ((b :: u) <:+ v.getD 0 []) := by
  have h : sufStep b (u :: [decide (u <:+ v.getD 0 [])] :: v)
      = (decide (u <:+ v.getD 0 []) &&
          decide ((b :: u).length ≤ (v.getD 0 []).length) &&
          decide (((v.getD 0 []).drop
            ((v.getD 0 []).length - (b :: u).length)).headD false = b)) := by
    simp only [sufStep, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons]
  rw [h]
  simp only [suffix_cons_iff b u (v.getD 0 []), Bool.decide_and, Bool.and_assoc]

theorem brnAux_suf (v : Args) : ∀ u : List Bool,
    brnAux (fun _ => [true]) (fun args => [sufStep false args]) (fun args => [sufStep true args])
      u v = [decide (u <:+ v.getD 0 [])] := by
  intro u
  induction u with
  | nil => simp [brnAux]
  | cons b u ih =>
    have hstep : brnAux (fun _ => [true]) (fun args => [sufStep false args])
        (fun args => [sufStep true args]) (b :: u) v
        = [sufStep b (u :: brnAux (fun _ => [true]) (fun args => [sufStep false args])
            (fun args => [sufStep true args]) u v :: v)] := by
      cases b <;> rfl
    rw [hstep, ih, sufStep_apply]

theorem sufFn_apply (args : Args) :
    sufFn args = [decide (args.getD 0 [] <:+ args.getD 1 [])] := by
  show brnAux _ _ _ (args.getD 0 []) args.tail = _
  rw [brnAux_suf]
  cases args with
  | nil => rfl
  | cons a as => rfl

theorem cobham_sufFn : Cobham sufFn := by
  refine Cobham.brn (cobham_const [true]) (cobhamB_sufStep false) (cobhamB_sufStep true)
    (cobham_const [false]) ?_
  intro args
  rw [show brnFn (fun _ => [true]) (fun args => [sufStep false args])
    (fun args => [sufStep true args]) = sufFn from rfl, sufFn_apply]
  simp

/-- **The suffix test**, as a closure property. -/
theorem cobhamB_isSuffix {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB (fun args => decide (a args <:+ b args)) :=
  (cobham_c2 cobham_sufFn ha hb).of_eq' fun args => by simp [compFn, sufFn_apply]

/-- **Equality of two computed strings**. -/
theorem cobhamB_eqStr {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB (fun args => decide (a args = b args)) :=
  ((cobhamB_isSuffix ha hb).and (cobhamB_lenLE hb ha)).of_eq fun args => by
    by_cases h : a args = b args
    · simp [h]
    · by_cases h1 : a args <:+ b args
      · have hle : (a args).length ≤ (b args).length := h1.length_le
        have : ¬ (b args).length ≤ (a args).length := by
          intro hge
          exact h (h1.eq_of_length (by omega))
        simp [h, h1, this]
      · simp [h, h1]

/-- **The prefix test**. -/
theorem cobhamB_isPrefix {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB (fun args => decide (a args <+: b args)) :=
  (cobhamB_isSuffix (cobham_rev ha) (cobham_rev hb)).of_eq fun args => by
    simp [List.reverse_suffix]

/-! ### Quantifying over the suffixes of a string -/

/-- The arguments an `n`-ary function of the class reads. -/
def padArgs (n : ℕ) (args : Args) : Args := (List.range n).map fun i => args.getD i []

/-- A function that reads only its first `n` arguments. -/
def ArgDep (n : ℕ) (p : Args → Bool) : Prop := ∀ args, p args = p (padArgs n args)

@[simp] theorem getD_padArgs {n i : ℕ} (h : i < n) (args : Args) :
    (padArgs n args).getD i [] = args.getD i [] := by
  rw [padArgs, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h]
  rfl

theorem padArgs_cons (n : ℕ) (x : List Bool) (args : Args) :
    padArgs (n + 1) (x :: args) = x :: padArgs n args := by
  rw [padArgs, padArgs, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- **Existential quantification over the suffixes of a string.** -/
def anyTailsB (p : Args → Bool) (v : Args) (x : List Bool) : Bool :=
  x.tails.any fun s => p (s :: v)

@[simp] theorem anyTailsB_nil (p : Args → Bool) (v : Args) : anyTailsB p v [] = p ([] :: v) := by
  simp [anyTailsB]

theorem anyTailsB_cons (p : Args → Bool) (v : Args) (b : Bool) (x : List Bool) :
    anyTailsB p v (b :: x) = (p ((b :: x) :: v) || anyTailsB p v x) := by
  simp [anyTailsB]

theorem anyTailsB_eq_true {p : Args → Bool} {v : Args} {x : List Bool} :
    anyTailsB p v x = true ↔ ∃ s, s <:+ x ∧ p (s :: v) = true := by
  simp [anyTailsB, List.mem_tails]

theorem cobham_relay (n k : ℕ) :
    ∀ f ∈ (List.range n).map (fun i => proj (i + k)), Cobham f := by
  intro f hf
  simp only [List.mem_map, List.mem_range] at hf
  obtain ⟨i, -, rfl⟩ := hf
  exact Cobham.proj _

theorem map_relay (n k : ℕ) (args : Args) :
    ((List.range n).map (fun i => proj (i + k))).map (fun h => h args)
      = padArgs n (args.drop k) := by
  rw [List.map_map, padArgs]
  refine List.map_congr_left fun i hi => ?_
  simp [proj, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

/-- **Quantifying over the suffixes of the first argument is a closure property of Cobham's
class.**  The body sees the suffix as its first argument and the ambient arguments after it, so
the quantifiers nest. -/
theorem cobhamB_anyTails {p : Args → Bool} {n : ℕ} (hp : CobhamB p) (hdep : ArgDep (n + 1) p) :
    CobhamB (fun args => anyTailsB p args.tail (args.getD 0 [])) := by
  -- the base case: the empty suffix
  have hbase : Cobham (compFn (fun args => [p args])
      ((fun _ => []) :: (List.range n).map (fun i => proj (i + 0)))) := by
    refine Cobham.comp hp ?_
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact Cobham.empty
    · exact cobham_relay n 0 f hf
  have hbase_apply : ∀ v : Args,
      compFn (fun args => [p args]) ((fun _ => []) :: (List.range n).map (fun i => proj (i + 0))) v
        = [p ([] :: v)] := by
    intro v
    have h1 : (((fun _ => []) :: (List.range n).map (fun i => proj (i + 0))) :
        List (Args → List Bool)).map (fun h => h v) = [] :: padArgs n v := by
      rw [List.map_cons, map_relay n 0 v]
      simp
    show [p (((((fun _ => []) : Args → List Bool) ::
      (List.range n).map (fun i => proj (i + 0))).map (fun h => h v)))] = _
    rw [h1, hdep ([] :: v), padArgs_cons]
  -- the step: the suffix `b :: x`
  have hstepB : ∀ b : Bool, CobhamB (fun args : Args =>
      p ((b :: args.getD 0 []) :: padArgs n (args.drop 2)) || (args.getD 1 []).headD false) := by
    intro b
    have h1 : Cobham (compFn (fun args => [p args])
        (consFn b :: (List.range n).map (fun i => proj (i + 2)))) := by
      refine Cobham.comp hp ?_
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact Cobham.cons b
      · exact cobham_relay n 2 f hf
    have h1' : CobhamB (fun args : Args =>
        p ((b :: args.getD 0 []) :: padArgs n (args.drop 2))) := by
      refine h1.of_eq' fun args => ?_
      show [p ((consFn b :: (List.range n).map (fun i => proj (i + 2))).map (fun h => h args))] = _
      rw [List.map_cons, map_relay n 2 args]
      rfl
    have h2 : CobhamB (fun args : Args => (args.getD 1 []).headD false) :=
      (cobhamB_head (Cobham.proj 1)).of_eq fun args => by simp [proj]
    exact h1'.or h2
  have hstep_apply : ∀ (b : Bool) (x : List Bool) (c : Bool) (v : Args),
      (p ((b :: x) :: padArgs n v) || c) = (p ((b :: x) :: v) || c) := by
    intro b x c v
    rw [hdep ((b :: x) :: v), padArgs_cons]
  -- the recursion
  set g : Fn := compFn (fun args => [p args])
    ((fun _ => []) :: (List.range n).map (fun i => proj (i + 0))) with hg
  set h : Bool → Fn := fun b => fun args : Args =>
    [p ((b :: args.getD 0 []) :: padArgs n (args.drop 2)) || (args.getD 1 []).headD false] with hh
  have haux : ∀ (v : Args) (x : List Bool),
      brnAux g (h false) (h true) x v = [anyTailsB p v x] := by
    intro v x
    induction x with
    | nil => simpa [anyTailsB] using hbase_apply v
    | cons b x ih =>
      have hb : brnAux g (h false) (h true) (b :: x) v
          = h b (x :: brnAux g (h false) (h true) x v :: v) := by
        cases b <;> rfl
      rw [hb, ih]
      show [p ((b :: x) :: padArgs n ((x :: [anyTailsB p v x] :: v).drop 2)) ||
        (((x :: [anyTailsB p v x] :: v).getD 1 []).headD false)] = _
      simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_succ, List.getD_cons_zero,
        List.headD_cons]
      rw [hstep_apply b x (anyTailsB p v x) v, anyTailsB_cons]
  have hfin : brnFn g (h false) (h true) = fun args => [anyTailsB p args.tail (args.getD 0 [])] := by
    funext args
    rw [brnFn, haux]
  have hcob : Cobham (brnFn g (h false) (h true)) := by
    refine Cobham.brn hbase (hstepB false) (hstepB true) (cobham_const [false]) ?_
    intro args
    rw [hfin]
    simp
  rwa [hfin] at hcob

/-! ### Applying a predicate of the class to computed arguments -/

theorem CobhamB.comp2 {p : Args → Bool} (hp : CobhamB p) {a b : Fn} (ha : Cobham a)
    (hb : Cobham b) : CobhamB fun args => p [a args, b args] :=
  (cobham_c2 hp ha hb).of_eq' fun args => by simp [compFn]

theorem CobhamB.comp3 {p : Args → Bool} (hp : CobhamB p) {a b c : Fn} (ha : Cobham a)
    (hb : Cobham b) (hc : Cobham c) : CobhamB fun args => p [a args, b args, c args] :=
  (cobham_c3 hp ha hb hc).of_eq' fun args => by simp [compFn]

theorem CobhamB.comp4 {p : Args → Bool} (hp : CobhamB p) {a b c d : Fn} (ha : Cobham a)
    (hb : Cobham b) (hc : Cobham c) (hd : Cobham d) :
    CobhamB fun args => p [a args, b args, c args, d args] :=
  (cobham_c4 hp ha hb hc hd).of_eq' fun args => by simp [compFn]

/-! ### From a predicate of the class to a polynomial-time function -/

theorem polyTimeFun_of_cobhamB {p : Args → Bool} (hp : CobhamB p) :
    PolyTimeFun (fun x : List Bool => [p [x]]) :=
  CobhamFun.polyTimeFun ⟨fun args => [p args], hp, fun _ => rfl⟩

end PTime

end HTN
