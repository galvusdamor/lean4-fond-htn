import HtnComplexity.Compress.ProfileCobham
import HtnComplexity.Complexity.SerRootKey
/-!
# A programming kit for Cobham's class: substitution, loops over suffixes, iteration

The string toolkit of `ComplexityTheory/Complexity/CobhamString.lean` states its closure
properties for functions of a *fixed* shape, and every use of a binder (the quantifier over
suffixes `HTN.PTime.cobhamB_anyTails`) has to carry an explicit "reads only its first `n`
arguments" side condition.  This file removes that bookkeeping once and for all and adds the
loop constructs the polynomial-time planner of `HtnComplexity/Complexity/TOPlan/` needs.

* `HTN.PTime.Cobham.readsFirst` — **every function of Cobham's class reads only finitely many
  of its arguments**.  Consequently
* `HTN.PTime.Cobham.subst` — a function of the class may be applied to any argument list whose
  entries are functions of the class (`HTN.PTime.cobham_bind`, `HTN.PTime.cobhamB_bind`: bind a
  computed string as a new first argument);
* `HTN.PTime.cobhamB_anyTailsC`, `HTN.PTime.cobhamB_allTailsC` — the quantifiers over the
  suffixes of a *computed* string;
* `HTN.PTime.cobham_mapTailsC` — the bit vector `x.tails.map p` of a predicate over the suffixes
  of a computed string `x` (one bit per position), read back with `HTN.PTime.bitAt`;
* `HTN.PTime.cobham_findTailC` — the longest suffix of a computed string satisfying a predicate;
* `HTN.PTime.cobham_iterateC` — **iteration** of a step function of the class, as many times as
  a computed string is long, provided the step keeps the state below a bound of the class;
* `HTN.PTime.cobham_mapList`, `HTN.PTime.cobhamB_anyList`, `HTN.PTime.cobhamB_allList` — finite
  vectors and finite disjunctions/conjunctions of predicates of the class.
-/

namespace HTN

namespace PTime

/-! ### Reading finitely many arguments -/

/-- `f` reads only its first `n` arguments. -/
def ReadsFirst (n : ℕ) (f : Fn) : Prop := ∀ args, f args = f (padArgs n args)

theorem padArgs_padArgs {n m : ℕ} (h : n ≤ m) (args : Args) :
    padArgs n (padArgs m args) = padArgs n args := by
  simp only [padArgs]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  exact getD_padArgs (by omega) args

theorem ReadsFirst.mono {n m : ℕ} {f : Fn} (h : ReadsFirst n f) (hnm : n ≤ m) :
    ReadsFirst m f := fun args => by
  rw [h (padArgs m args), padArgs_padArgs hnm]
  exact h args

theorem padArgs_succ_tail (n : ℕ) (args : Args) :
    (padArgs (n + 1) args).tail = padArgs n args.tail := by
  cases args with
  | nil =>
    rw [padArgs, padArgs, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp
  | cons x xs => rw [padArgs_cons]; rfl

theorem padArgs_getD_zero (n : ℕ) (args : Args) :
    (padArgs (n + 1) args).getD 0 [] = args.getD 0 [] :=
  getD_padArgs (by omega) args

/-- **Every function of Cobham's class reads only finitely many of its arguments.** -/
theorem Cobham.readsFirst {f : Fn} (hf : Cobham f) : ∃ n, ReadsFirst n f := by
  induction hf with
  | empty => exact ⟨0, fun _ => rfl⟩
  | proj k => exact ⟨k + 1, fun args => by simp only [PTime.proj]; rw [getD_padArgs (by omega)]⟩
  | cons b => exact ⟨1, fun args => by simp only [consFn]; rw [getD_padArgs (by omega)]⟩
  | smash =>
    exact ⟨2, fun args => by
      simp only [smashFn]; rw [getD_padArgs (by omega), getD_padArgs (by omega)]⟩
  | @comp g hs _ _ _ ihs =>
    have key : ∀ hs' : List Fn, (∀ h ∈ hs', ∃ n, ReadsFirst n h) →
        ∃ N, ∀ h ∈ hs', ReadsFirst N h := by
      intro hs' hh
      induction hs' with
      | nil => exact ⟨0, by simp⟩
      | cons h t ih =>
        obtain ⟨N, hN⟩ := ih fun k hk => hh k (by simp [hk])
        obtain ⟨n, hn⟩ := hh h (by simp)
        refine ⟨N + n, fun k hk => ?_⟩
        rcases List.mem_cons.1 hk with rfl | hk
        · exact hn.mono (by omega)
        · exact (hN k hk).mono (by omega)
    obtain ⟨N, hN⟩ := key hs ihs
    refine ⟨N, fun args => ?_⟩
    simp only [compFn]
    congr 1
    exact List.map_congr_left fun h hh => hN h hh args
  | @brn g h0 h1 bd _ _ _ _ _ ihg ih0 ih1 _ =>
    obtain ⟨ng, hng⟩ := ihg
    obtain ⟨n0, hn0⟩ := ih0
    obtain ⟨n1, hn1⟩ := ih1
    set M := ng + n0 + n1 with hM
    have hg : ReadsFirst M g := hng.mono (by omega)
    have h0' : ReadsFirst (M + 2) h0 := hn0.mono (by omega)
    have h1' : ReadsFirst (M + 2) h1 := hn1.mono (by omega)
    have claim : ∀ (x : List Bool) (v : Args),
        brnAux g h0 h1 x v = brnAux g h0 h1 x (padArgs M v) := by
      intro x
      induction x with
      | nil => intro v; exact hg v
      | cons b x ih =>
        intro v
        have hb : ∀ w : Args, brnAux g h0 h1 (b :: x) w
            = (bif b then h1 else h0) (x :: brnAux g h0 h1 x w :: w) := fun _ => rfl
        rw [hb, hb, ← ih v]
        cases b
        · show h0 _ = h0 _
          rw [h0' (x :: brnAux g h0 h1 x v :: v), padArgs_cons, padArgs_cons]
        · show h1 _ = h1 _
          rw [h1' (x :: brnAux g h0 h1 x v :: v), padArgs_cons, padArgs_cons]
    refine ⟨M + 1, fun args => ?_⟩
    simp only [brnFn]
    rw [padArgs_getD_zero, padArgs_succ_tail]
    exact claim _ _

theorem CobhamB.readsFirst {p : Args → Bool} (hp : CobhamB p) :
    ∃ n, ∀ args, p args = p (padArgs n args) := by
  obtain ⟨n, hn⟩ := Cobham.readsFirst hp
  exact ⟨n, fun args => by simpa using hn args⟩

/-! ### Substitution -/

/-- **Substitution.**  A function of the class applied to an argument list whose entries are
functions of the class is a function of the class. -/
theorem Cobham.subst {F : Fn} (hF : Cobham F) {T : Args → Args}
    (hT : ∀ i, Cobham fun args => (T args).getD i []) : Cobham fun args => F (T args) := by
  obtain ⟨n, hn⟩ := hF.readsFirst
  have hc : Cobham (compFn F ((List.range n).map fun i => fun args => (T args).getD i [])) := by
    refine Cobham.comp hF fun h hh => ?_
    simp only [List.mem_map, List.mem_range] at hh
    obtain ⟨i, -, rfl⟩ := hh
    exact hT i
  refine hc.of_eq' fun args => ?_
  simp only [compFn, List.map_map]
  rw [hn (T args)]
  rfl

theorem CobhamB.subst {p : Args → Bool} (hp : CobhamB p) {T : Args → Args}
    (hT : ∀ i, Cobham fun args => (T args).getD i []) : CobhamB fun args => p (T args) :=
  Cobham.subst (F := fun args => [p args]) hp hT

theorem cobham_getD_cons {a : Fn} (ha : Cobham a) (i : ℕ) :
    Cobham fun args => (a args :: args).getD i [] := by
  cases i with
  | zero => simpa using ha
  | succ i => exact (Cobham.proj i).of_eq' fun args => by simp [proj]

/-- Binding a computed string as a new first argument. -/
theorem cobham_bind {F : Fn} (hF : Cobham F) {a : Fn} (ha : Cobham a) :
    Cobham fun args => F (a args :: args) :=
  hF.subst (cobham_getD_cons ha)

theorem cobhamB_bind {p : Args → Bool} (hp : CobhamB p) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => p (a args :: args) :=
  hp.subst (cobham_getD_cons ha)

/-- Dropping the first `k` arguments. -/
theorem cobham_dropArgs {F : Fn} (hF : Cobham F) (k : ℕ) : Cobham fun args => F (args.drop k) :=
  hF.subst fun i => (Cobham.proj (k + i)).of_eq' fun args => by
    simp [proj, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem cobham_tailArgs {F : Fn} (hF : Cobham F) : Cobham fun args => F args.tail :=
  (cobham_dropArgs hF 1).of_eq' fun args => by rw [List.drop_one]

theorem cobhamB_dropArgs {p : Args → Bool} (hp : CobhamB p) (k : ℕ) :
    CobhamB fun args => p (args.drop k) :=
  cobham_dropArgs (F := fun args => [p args]) hp k

/-! ### Quantifying over the suffixes of a computed string -/

theorem cobhamB_anyTails0 {p : Args → Bool} (hp : CobhamB p) :
    CobhamB fun args => anyTailsB p args.tail (args.getD 0 []) := by
  obtain ⟨n, hn⟩ := hp.readsFirst
  have hdep' : ArgDep (n + 1) p := fun args => by
    rw [hn args, hn (padArgs (n + 1) args), padArgs_padArgs (by omega)]
  exact cobhamB_anyTails hp hdep'

/-- **The quantifier over the suffixes of a computed string.**  The body sees the suffix as its
first argument, followed by the ambient arguments. -/
theorem cobhamB_anyTailsC {p : Args → Bool} (hp : CobhamB p) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => anyTailsB p args (a args) :=
  (cobhamB_bind (cobhamB_anyTails0 hp) ha).of_eq fun args => by simp

/-- The universal quantifier over the suffixes of a computed string. -/
def allTailsB (p : Args → Bool) (v : Args) (x : List Bool) : Bool :=
  x.tails.all fun s => p (s :: v)

theorem allTailsB_eq (p : Args → Bool) (v : Args) (x : List Bool) :
    allTailsB p v x = !anyTailsB (fun args => !p args) v x := by
  simp [allTailsB, anyTailsB, List.all_eq_not_any_not]

theorem allTailsB_eq_true {p : Args → Bool} {v : Args} {x : List Bool} :
    allTailsB p v x = true ↔ ∀ s, s <:+ x → p (s :: v) = true := by
  simp [allTailsB, List.mem_tails]

theorem cobhamB_allTailsC {p : Args → Bool} (hp : CobhamB p) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => allTailsB p args (a args) :=
  ((cobhamB_anyTailsC hp.not ha).not).of_eq fun args => allTailsB_eq p args (a args)

/-! ### Bit vectors indexed by the suffixes of a string -/

/-- The bit vector of a predicate over the suffixes of `x`: one bit per suffix, the longest
first. -/
def mapTailsL (p : Args → Bool) (v : Args) (x : List Bool) : List Bool :=
  x.tails.map fun s => p (s :: v)

@[simp] theorem length_mapTailsL (p : Args → Bool) (v : Args) (x : List Bool) :
    (mapTailsL p v x).length = x.length + 1 := by
  simp [mapTailsL]

/-- Prepending a computed bit (a local copy of `HTN.Syn.cobham_consB`). -/
theorem cobham_consBit {p : Args → Bool} (hp : CobhamB p) {f : Fn} (hf : Cobham f) :
    Cobham (fun args => p args :: f args) :=
  (cobham_c2 cobham_append hp hf).of_eq' fun args => by simp [compFn]

theorem cobham_mapTails0 {p : Args → Bool} (hp : CobhamB p) :
    Cobham fun args => mapTailsL p args.tail (args.getD 0 []) := by
  set g : Fn := fun args => [p ([] :: args)] with hg
  set h : Bool → Fn := fun b args =>
    p ((b :: args.getD 0 []) :: args.drop 2) :: args.getD 1 [] with hh
  have hgC : Cobham g := hp.subst fun i => by
    cases i with
    | zero => exact (cobham_const []).of_eq' fun _ => by simp
    | succ i => exact (Cobham.proj i).of_eq' fun args => by simp [proj]
  have hhC : ∀ b, Cobham (h b) := fun b => by
    refine cobham_consBit (hp.subst fun i => ?_) (Cobham.proj 1)
    cases i with
    | zero => exact (Cobham.cons b).of_eq' fun args => by simp [consFn]
    | succ i =>
      refine (Cobham.proj (i + 2)).of_eq' fun args => ?_
      simp [proj, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
  have haux : ∀ (v : Args) (x : List Bool), brnAux g (h false) (h true) x v = mapTailsL p v x := by
    intro v x
    induction x with
    | nil => simp [brnAux, hg, mapTailsL]
    | cons b x ih =>
      have hb : brnAux g (h false) (h true) (b :: x) v
          = h b (x :: brnAux g (h false) (h true) x v :: v) := by cases b <;> rfl
      rw [hb, ih]
      simp [hh, mapTailsL]
  have hfin : brnFn g (h false) (h true) = fun args => mapTailsL p args.tail (args.getD 0 []) := by
    funext args; rw [brnFn, haux]
  have hcob : Cobham (brnFn g (h false) (h true)) := by
    refine Cobham.brn hgC (hhC false) (hhC true) (Cobham.cons true) fun args => ?_
    rw [hfin]; simp [consFn]
  rwa [hfin] at hcob

/-- **The bit vector of a predicate over the suffixes of a computed string.** -/
theorem cobham_mapTailsC {p : Args → Bool} (hp : CobhamB p) {a : Fn} (ha : Cobham a) :
    Cobham fun args => mapTailsL p args (a args) :=
  (cobham_bind (cobham_mapTails0 hp) ha).of_eq' fun args => by simp

/-- The bit of a vector at the position of a suffix `s` of `x`. -/
def bitAt (V x s : List Bool) : Bool := (V.drop (x.length - s.length)).headD false

theorem bitAt_mapTailsL (p : Args → Bool) (v : Args) {x s : List Bool} (hs : s <:+ x) :
    bitAt (mapTailsL p v x) x s = p (s :: v) := by
  obtain ⟨t, rfl⟩ := hs
  simp only [bitAt, mapTailsL, List.length_append]
  rw [show t.length + s.length - s.length = t.length by omega, ← List.map_drop]
  induction t with
  | nil => cases s <;> simp
  | cons b t ih => simpa using ih

theorem cobhamB_bitAt {V x s : Fn} (hV : Cobham V) (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => bitAt (V args) (x args) (s args) :=
  (cobhamB_head (cobham_drop (cobham_trunc hs hx) hV)).of_eq fun args => by
    simp [bitAt]

/-! ### The longest suffix satisfying a predicate -/

/-- The longest suffix of `x` satisfying `P` (the empty string if there is none). -/
def findTail (P : List Bool → Bool) (x : List Bool) : List Bool := (x.tails.find? P).getD []

theorem findTail_cons (P : List Bool → Bool) (b : Bool) (x : List Bool) :
    findTail P (b :: x) = if P (b :: x) = true then b :: x else findTail P x := by
  by_cases h : P (b :: x) = true <;> simp [findTail, h]

/-- What the longest suffix satisfying a predicate is: if `t` is a suffix of `x` satisfying `P`,
and no strictly longer suffix of `x` does, then it is `t`. -/
theorem findTail_eq {P : List Bool → Bool} {x t : List Bool} (ht : t <:+ x)
    (hPt : P t = true) (hlong : ∀ s, s <:+ x → t.length < s.length → P s = false) :
    findTail P x = t := by
  induction x with
  | nil =>
    rw [List.suffix_nil] at ht
    subst ht
    simp [findTail, hPt]
  | cons b x ih =>
    rw [findTail_cons]
    by_cases hbx : t = b :: x
    · subst hbx; simp [hPt]
    · have ht' : t <:+ x := by
        rcases List.suffix_cons_iff.1 ht with h | h
        · exact absurd h hbx
        · exact h
      have hlen := ht'.length_le
      rw [if_neg (by rw [hlong (b :: x) List.suffix_rfl (by simp; omega)]; simp)]
      exact ih ht' fun s hs hl => hlong s (hs.trans (List.suffix_cons b x)) hl

/-- The longest suffix of `x` satisfying `p`, the predicate reading the suffix and the ambient
arguments `v`. -/
def findTailL (p : Args → Bool) (v : Args) (x : List Bool) : List Bool :=
  findTail (fun s => p (s :: v)) x

theorem findTailL_cons (p : Args → Bool) (v : Args) (b : Bool) (x : List Bool) :
    findTailL p v (b :: x) = if p ((b :: x) :: v) = true then b :: x else findTailL p v x :=
  findTail_cons _ b x

theorem length_findTail_le (P : List Bool → Bool) (x : List Bool) :
    (findTail P x).length ≤ x.length := by
  unfold findTail
  cases h : x.tails.find? P with
  | none => simp
  | some s => simpa using ((List.mem_tails _ _).1 (List.mem_of_find?_eq_some h)).length_le

theorem length_findTailL_le (p : Args → Bool) (v : Args) (x : List Bool) :
    (findTailL p v x).length ≤ x.length :=
  length_findTail_le _ _

theorem cobham_findTail0 {p : Args → Bool} (hp : CobhamB p) :
    Cobham fun args => findTailL p args.tail (args.getD 0 []) := by
  set g : Fn := fun _ => [] with hg
  set h : Bool → Fn := fun b args =>
    if p ((b :: args.getD 0 []) :: args.drop 2) = true then b :: args.getD 0 []
    else args.getD 1 [] with hh
  have hhC : ∀ b, Cobham (h b) := fun b => by
    refine Syn.Compress.cobham_iteC (hp.subst fun i => ?_) (Cobham.cons b) (Cobham.proj 1)
    cases i with
    | zero => exact (Cobham.cons b).of_eq' fun args => by simp [consFn]
    | succ i =>
      refine (Cobham.proj (i + 2)).of_eq' fun args => ?_
      simp [proj, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
  have haux : ∀ (v : Args) (x : List Bool),
      brnAux g (h false) (h true) x v = findTailL p v x := by
    intro v x
    induction x with
    | nil => by_cases h0 : p ([] :: v) = true <;> simp [brnAux, hg, findTailL, findTail, h0]
    | cons b x ih =>
      have hb : brnAux g (h false) (h true) (b :: x) v
          = h b (x :: brnAux g (h false) (h true) x v :: v) := by cases b <;> rfl
      rw [hb, ih, findTailL_cons]
      simp [hh]
  have hfin : brnFn g (h false) (h true) =
      fun args => findTailL p args.tail (args.getD 0 []) := by
    funext args; rw [brnFn, haux]
  have hcob : Cobham (brnFn g (h false) (h true)) := by
    refine Cobham.brn Cobham.empty (hhC false) (hhC true) (Cobham.proj 0) fun args => ?_
    rw [hfin]; exact length_findTailL_le _ _ _
  rwa [hfin] at hcob

/-- **The longest suffix of a computed string satisfying a predicate of the class.** -/
theorem cobham_findTailC {p : Args → Bool} (hp : CobhamB p) {a : Fn} (ha : Cobham a) :
    Cobham fun args => findTailL p args (a args) :=
  (cobham_bind (cobham_findTail0 hp) ha).of_eq' fun args => by simp

/-! ### Iteration -/

/-- **Iteration of a step function of the class**, as many times as a computed counter string is
long, provided the initial value and every step stay below a bound of the class. -/
theorem cobham_iterateC {init step cnt bd : Fn} (hinit : Cobham init) (hstep : Cobham step)
    (hcnt : Cobham cnt) (hbd : Cobham bd) (hb1 : ∀ args, (init args).length ≤ (bd args).length)
    (hb2 : ∀ c args, (step (c :: args)).length ≤ (bd args).length) :
    Cobham fun args => (fun c => step (c :: args))^[(cnt args).length] (init args) := by
  set h : Fn := fun args => step (args.drop 1) with hh
  have hhC : Cobham h := cobham_dropArgs hstep 1
  have haux : ∀ (v : Args) (x : List Bool),
      brnAux init h h x v = (fun c => step (c :: v))^[x.length] (init v) := by
    intro v x
    induction x with
    | nil => rfl
    | cons b x ih =>
      have hb : brnAux init h h (b :: x) v = h (x :: brnAux init h h x v :: v) := by
        cases b <;> rfl
      rw [hb, ih, List.length_cons, Function.iterate_succ_apply']
      rfl
  have hcob : Cobham (brnFn init h h) := by
    refine Cobham.brn hinit hhC hhC (cobham_dropArgs hbd 1) fun args => ?_
    simp only [brnFn]
    rw [haux]
    cases hx : (args.getD 0 []).length with
    | zero => simpa using hb1 args.tail
    | succ n =>
      rw [Function.iterate_succ_apply']
      simpa [List.drop_one] using hb2 _ args.tail
  refine (cobham_bind hcob hcnt).of_eq' fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  exact haux args (cnt args)

/-! ### Finite vectors and finite Boolean combinations -/

theorem cobham_mapList {α : Type} (L : List α) (P : α → Args → Bool)
    (h : ∀ a ∈ L, CobhamB (P a)) : Cobham fun args => L.map fun a => P a args := by
  induction L with
  | nil => exact (cobham_const []).of_eq' fun _ => rfl
  | cons a L ih =>
    exact (cobham_consBit (h a (by simp)) (ih fun b hb => h b (by simp [hb]))).of_eq'
      fun _ => rfl

theorem cobhamB_anyList {α : Type} (L : List α) (P : α → Args → Bool)
    (h : ∀ a ∈ L, CobhamB (P a)) : CobhamB fun args => L.any fun a => P a args := by
  induction L with
  | nil => exact (cobhamB_const false).of_eq fun _ => rfl
  | cons a L ih =>
    exact ((h a (by simp)).or (ih fun b hb => h b (by simp [hb]))).of_eq fun _ => by simp

theorem cobhamB_allList {α : Type} (L : List α) (P : α → Args → Bool)
    (h : ∀ a ∈ L, CobhamB (P a)) : CobhamB fun args => L.all fun a => P a args := by
  induction L with
  | nil => exact (cobhamB_const true).of_eq fun _ => rfl
  | cons a L ih =>
    exact ((h a (by simp)).and (ih fun b hb => h b (by simp [hb]))).of_eq fun _ => by simp

/-! ### Binder forms with an explicit body -/

/-- The bound variable of a binder (the first argument). -/
theorem cobham_var0 : Cobham fun args : Args => args.getD 0 [] := Cobham.proj 0

theorem cobhamB_anyTailsF {P : Args → List Bool → Bool}
    (hP : CobhamB fun a => P a.tail (a.getD 0 [])) {X : Fn} (hX : Cobham X) :
    CobhamB fun args => (X args).tails.any (P args) :=
  (cobhamB_anyTailsC hP hX).of_eq fun args => by simp [anyTailsB]

theorem cobhamB_allTailsF {P : Args → List Bool → Bool}
    (hP : CobhamB fun a => P a.tail (a.getD 0 [])) {X : Fn} (hX : Cobham X) :
    CobhamB fun args => (X args).tails.all (P args) :=
  (cobhamB_allTailsC hP hX).of_eq fun args => by simp [allTailsB]

theorem cobham_mapTailsF {P : Args → List Bool → Bool}
    (hP : CobhamB fun a => P a.tail (a.getD 0 [])) {X : Fn} (hX : Cobham X) :
    Cobham fun args => (X args).tails.map (P args) :=
  (cobham_mapTailsC hP hX).of_eq' fun args => by simp [mapTailsL]

theorem bitAt_map_tails (f : List Bool → Bool) {x s : List Bool} (hs : s <:+ x) :
    bitAt (x.tails.map f) x s = f s := by
  have h := bitAt_mapTailsL (fun a => f (a.getD 0 [])) [] hs
  simpa [mapTailsL] using h

/-! ### Bits at fixed indices -/

/-- The bit of a vector at a fixed index. -/
def bitI (V : List Bool) (i : ℕ) : Bool := (V.drop i).headD false

theorem bitI_map {α : Type} (l : List α) (f : α → Bool) {i : ℕ} (hi : i < l.length) :
    bitI (l.map f) i = f l[i] := by
  simp only [bitI, ← List.map_drop]
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem bitI_append_left {V W : List Bool} {i : ℕ} (hi : i < V.length) :
    bitI (V ++ W) i = bitI V i := by
  simp only [bitI, List.drop_append_of_le_length hi.le]
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem cobhamB_bitI {V : Fn} (hV : Cobham V) (i : ℕ) : CobhamB fun args => bitI (V args) i :=
  (cobhamB_head (cobham_drop (cobham_const (List.replicate i false)) hV)).of_eq fun args => by
    simp [bitI]

end PTime

end HTN
