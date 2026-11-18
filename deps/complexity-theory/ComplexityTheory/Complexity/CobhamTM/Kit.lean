import ComplexityTheory.Complexity.CobhamExamples
/-!
# A self-contained toolkit for Cobham's class (for Cobham's theorem)

This file collects the closure properties of Cobham's class `HTN.PTime.Cobham` that the
simulation of a Turing machine (`ComplexityTheory/Complexity/CobhamTM/Simulate.lean`) needs.  It depends
only on the definition of the class (`ComplexityTheory/Complexity/Cobham.lean`) and on the
two basic examples of `ComplexityTheory/Complexity/CobhamExamples.lean`, so that the
Turing-machine characterisation of polynomial time does not depend on the HTN development.

Main items:
* `Cobham.readsFirst'`, `cobham_subst` — substitution of functions of the class for arguments;
* `cobham_ite` — definition by cases on a predicate of the class;
* `cobham_dropBy`, `cobham_rev`, `cobham_takeBy` — string surgery;
* `cobB_startsWith`, `cobB_null`, `cobB_lenLE` — basic tests;
* `cobham_dispatch` — definition by cases on a finite observation;
* `cobham_iterate` and `cobham_iterVec` — iteration of a (vector of) step function(s) as many
  times as a computed string is long, as long as the iterates stay below a bound of the class.
-/

namespace HTN.PTime.CobhamTM

open HTN.PTime

/-! ### Composition helpers -/

theorem _root_.HTN.PTime.Cobham.of_fun_eq {f g : Fn} (hf : Cobham f) (h : ∀ args, f args = g args) : Cobham g := by
  have : f = g := funext h
  exact this ▸ hf

theorem cobham_c1 {g f : Fn} (hg : Cobham g) (hf : Cobham f) :
    Cobham (fun args => g [f args]) :=
  (Cobham.comp hg (hs := [f]) (by simpa using hf)).of_fun_eq fun _ => rfl

theorem cobham_c2 {g f₁ f₂ : Fn} (hg : Cobham g) (h₁ : Cobham f₁) (h₂ : Cobham f₂) :
    Cobham (fun args => g [f₁ args, f₂ args]) :=
  (Cobham.comp hg (hs := [f₁, f₂]) (by simp [h₁, h₂])).of_fun_eq fun _ => rfl

theorem cobham_c3 {g f₁ f₂ f₃ : Fn} (hg : Cobham g) (h₁ : Cobham f₁) (h₂ : Cobham f₂)
    (h₃ : Cobham f₃) : Cobham (fun args => g [f₁ args, f₂ args, f₃ args]) :=
  (Cobham.comp hg (hs := [f₁, f₂, f₃]) (by simp [h₁, h₂, h₃])).of_fun_eq fun _ => rfl

theorem cobham_proj' (n : ℕ) : Cobham (fun args => args.getD n []) := Cobham.proj n

theorem cobham_append' {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham (fun args => a args ++ b args) :=
  (cobham_c2 cobham_append ha hb).of_fun_eq fun _ => rfl

theorem cobham_cons' (x : Bool) {a : Fn} (ha : Cobham a) :
    Cobham (fun args => x :: a args) :=
  (cobham_c1 (Cobham.cons x) ha).of_fun_eq fun _ => rfl

theorem cobham_tail' {a : Fn} (ha : Cobham a) : Cobham (fun args => (a args).tail) :=
  (cobham_c1 cobham_tail ha).of_fun_eq fun _ => rfl

theorem cobham_appendConst {a : Fn} (ha : Cobham a) (y : List Bool) :
    Cobham (fun args => a args ++ y) := cobham_append' ha (cobham_const y)

theorem cobham_constAppend {a : Fn} (ha : Cobham a) (y : List Bool) :
    Cobham (fun args => y ++ a args) := cobham_append' (cobham_const y) ha

/-! ### Reading finitely many arguments, and substitution -/

/-- The first `n` arguments, padded with empty strings. -/
def padArgs (n : ℕ) (args : Args) : Args := (List.range n).map fun i => args.getD i []

@[simp] theorem getD_padArgs {n i : ℕ} (h : i < n) (args : Args) :
    (padArgs n args).getD i [] = args.getD i [] := by
  rw [padArgs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem padArgs_cons (n : ℕ) (x : List Bool) (args : Args) :
    padArgs (n + 1) (x :: args) = x :: padArgs n args := by
  rw [padArgs, padArgs, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

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
theorem _root_.HTN.PTime.Cobham.readsFirst_tm {f : Fn} (hf : Cobham f) : ∃ n, ReadsFirst n f := by
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

/-- **Substitution.**  A function of the class applied to an argument list whose entries are
functions of the class is a function of the class. -/
theorem cobham_subst {F : Fn} (hF : Cobham F) {T : Args → Args}
    (hT : ∀ i, Cobham fun args => (T args).getD i []) : Cobham fun args => F (T args) := by
  obtain ⟨n, hn⟩ := hF.readsFirst_tm
  have hc : Cobham (compFn F ((List.range n).map fun i => fun args => (T args).getD i [])) := by
    refine Cobham.comp hF fun h hh => ?_
    simp only [List.mem_map, List.mem_range] at hh
    obtain ⟨i, -, rfl⟩ := hh
    exact hT i
  refine hc.of_fun_eq fun args => ?_
  simp only [compFn, List.map_map]
  rw [hn (T args)]
  rfl

/-- Dropping the first `k` arguments. -/
theorem cobham_dropArgs {F : Fn} (hF : Cobham F) (k : ℕ) :
    Cobham fun args => F (args.drop k) :=
  cobham_subst hF fun i => (Cobham.proj (k + i)).of_fun_eq fun args => by
    simp [PTime.proj, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Prepending computed arguments. -/
theorem cobham_prepend {F : Fn} (hF : Cobham F) (hs : List Fn) (hhs : ∀ h ∈ hs, Cobham h) :
    Cobham fun args => F (hs.map (fun h => h args) ++ args) := by
  refine cobham_subst hF fun i => ?_
  by_cases hi : i < hs.length
  · refine (hhs (hs[i]) (List.getElem_mem hi)).of_fun_eq fun args => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_eq_getElem hi]
  · refine (Cobham.proj (i - hs.length)).of_fun_eq fun args => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp [PTime.proj, List.getD_eq_getElem?_getD]

/-- Binding a computed string as a new first argument. -/
theorem cobham_bind {F : Fn} (hF : Cobham F) {a : Fn} (ha : Cobham a) :
    Cobham fun args => F (a args :: args) :=
  (cobham_prepend hF [a] (by simpa using ha)).of_fun_eq fun _ => rfl

/-! ### Predicates of the class and definition by cases -/

/-- A predicate of the class: its one-bit answer is computed by a function of the class. -/
def CobB (p : Args → Bool) : Prop := Cobham (fun args => [p args])

theorem CobB.of_eq {p q : Args → Bool} (hp : CobB p) (h : ∀ args, p args = q args) :
    CobB q := Cobham.of_fun_eq hp fun args => by rw [h]

theorem cobB_const (b : Bool) : CobB (fun _ => b) := cobham_const [b]

/-- **Definition by cases** on a predicate of the class. -/
theorem cobham_ite {p : Args → Bool} (hp : CobB p) {F G : Fn} (hF : Cobham F)
    (hG : Cobham G) : Cobham fun args => if p args then F args else G args := by
  have hb : Cobham (brnFn (fun _ => []) (fun args => G (args.drop 2))
      (fun args => F (args.drop 2))) := by
    refine Cobham.brn Cobham.empty (cobham_dropArgs hG 2) (cobham_dropArgs hF 2)
      (cobham_dropArgs (cobham_append' hF hG) 1) fun args => ?_
    simp only [brnFn]
    rcases args with _ | ⟨x, v⟩
    · simp [brnAux]
    · rcases x with _ | ⟨b, x⟩
      · simp [brnAux]
      · cases b <;> simp [brnAux]
  refine (cobham_bind hb hp).of_fun_eq fun args => ?_
  cases h : p args <;> simp [brnFn, brnAux]

theorem cobB_ite {p q r : Args → Bool} (hp : CobB p) (hq : CobB q) (hr : CobB r) :
    CobB fun args => if p args then q args else r args :=
  (cobham_ite hp hq hr).of_fun_eq fun args => by by_cases h : p args <;> simp [h]

theorem CobB.not {p : Args → Bool} (hp : CobB p) : CobB fun args => !p args :=
  (cobB_ite hp (cobB_const false) (cobB_const true)).of_eq fun args => by
    cases p args <;> rfl

theorem CobB.and {p q : Args → Bool} (hp : CobB p) (hq : CobB q) :
    CobB fun args => p args && q args :=
  (cobB_ite hp hq (cobB_const false)).of_eq fun args => by cases p args <;> rfl

theorem CobB.or {p q : Args → Bool} (hp : CobB p) (hq : CobB q) :
    CobB fun args => p args || q args :=
  (cobB_ite hp (cobB_const true) hq).of_eq fun args => by cases p args <;> rfl

theorem cobB_allList {α : Type} (L : List α) (P : α → Args → Bool)
    (h : ∀ a ∈ L, CobB (P a)) : CobB fun args => L.all fun a => P a args := by
  induction L with
  | nil => exact (cobB_const true).of_eq fun _ => rfl
  | cons a L ih =>
    exact ((h a (by simp)).and (ih fun b hb => h b (by simp [hb]))).of_eq fun _ => by simp

theorem cobB_anyList {α : Type} (L : List α) (P : α → Args → Bool)
    (h : ∀ a ∈ L, CobB (P a)) : CobB fun args => L.any fun a => P a args := by
  induction L with
  | nil => exact (cobB_const false).of_eq fun _ => rfl
  | cons a L ih =>
    exact ((h a (by simp)).or (ih fun b hb => h b (by simp [hb]))).of_eq fun _ => by simp

theorem CobB.subst {p : Args → Bool} (hp : CobB p) {T : Args → Args}
    (hT : ∀ i, Cobham fun args => (T args).getD i []) : CobB fun args => p (T args) :=
  cobham_subst (F := fun args => [p args]) hp hT

theorem CobB.comp1 {p : Args → Bool} (hp : CobB p) {a : Fn} (ha : Cobham a) :
    CobB fun args => p [a args] :=
  cobham_c1 hp ha

/-! ### String surgery -/

/-- The emptiness test. -/
theorem cobB_null {a : Fn} (ha : Cobham a) : CobB fun args => (a args).isEmpty := by
  have hb : Cobham (brnFn (fun _ => [true]) (fun _ => [false]) (fun _ => [false])) :=
    Cobham.brn (cobham_const _) (cobham_const _) (cobham_const _) (cobham_const [true])
      fun args => by
        simp only [brnFn]
        rcases args.getD 0 [] with _ | ⟨b, x⟩
        · simp [brnAux]
        · cases b <;> simp [brnAux]
  refine (cobham_c1 hb ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero]
  rcases a args with _ | ⟨b, x⟩
  · simp [brnAux]
  · cases b <;> simp [brnAux]

/-- The test "the first bit is `b`". -/
theorem cobB_headIs (b : Bool) {a : Fn} (ha : Cobham a) :
    CobB fun args => (a args).head? == some b := by
  have hb : Cobham (brnFn (fun _ => [false]) (fun _ => [!b]) (fun _ => [b])) :=
    Cobham.brn (cobham_const _) (cobham_const _) (cobham_const _) (cobham_const [true])
      fun args => by
        simp only [brnFn]
        rcases args.getD 0 [] with _ | ⟨c, x⟩
        · simp [brnAux]
        · cases c <;> simp [brnAux]
  refine (cobham_c1 hb ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero]
  rcases a args with _ | ⟨c, x⟩
  · simp [brnAux]
  · cases b <;> cases c <;> simp [brnAux]

/-- The test "the computed string starts with the constant `c`". -/
theorem cobB_startsWith (c : List Bool) {a : Fn} (ha : Cobham a) :
    CobB fun args => decide (c <+: a args) := by
  induction c generalizing a with
  | nil => exact (cobB_const true).of_eq fun _ => by simp
  | cons b c ih =>
    refine ((cobB_headIs b ha).and (ih (cobham_tail' ha))).of_eq fun args => ?_
    rcases a args with _ | ⟨d, x⟩
    · simp
    · by_cases hdb : d = b
      · subst hdb; simp [List.cons_prefix_cons]
      · simp [List.cons_prefix_cons, hdb, Ne.symm hdb]

/-- Dropping as many characters from `a` as `y` is long. -/
theorem cobham_dropBy {y a : Fn} (hy : Cobham y) (ha : Cobham a) :
    Cobham fun args => (a args).drop (y args).length := by
  have hb : Cobham (brnFn (proj 0) (fun args => (args.getD 1 []).tail)
      (fun args => (args.getD 1 []).tail)) := by
    refine Cobham.brn (Cobham.proj 0) (cobham_tail' (Cobham.proj 1)) (cobham_tail' (Cobham.proj 1))
      (Cobham.proj 1) fun args => ?_
    simp only [brnFn]
    suffices ∀ x v, (brnAux (proj 0) (fun args => (args.getD 1 []).tail)
        (fun args => (args.getD 1 []).tail) x v) = (v.getD 0 []).drop x.length by
      rw [this]; rcases args with _ | ⟨x, v⟩ <;> simp [PTime.proj]
    intro x v
    induction x with
    | nil => simp [brnAux, PTime.proj]
    | cons b x ih =>
      cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ,
        List.getD_cons_zero]; rw [ih]; simp [List.tail_drop])
  refine (cobham_c2 hb hy ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  generalize y args = x
  induction x with
  | nil => simp [brnAux, PTime.proj]
  | cons b x ih =>
    cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ,
        List.getD_cons_zero] at ih ⊢; rw [ih]; simp [List.tail_drop])

/-- Dropping a constant number of characters. -/
theorem cobham_dropConst (n : ℕ) {a : Fn} (ha : Cobham a) :
    Cobham fun args => (a args).drop n :=
  (cobham_dropBy (cobham_const (List.replicate n false)) ha).of_fun_eq fun _ => by simp

/-- Reversal. -/
theorem cobham_rev {a : Fn} (ha : Cobham a) : Cobham fun args => (a args).reverse := by
  have hb : Cobham (brnFn (fun _ => []) (fun args => args.getD 1 [] ++ [false])
      (fun args => args.getD 1 [] ++ [true])) := by
    refine Cobham.brn Cobham.empty (cobham_appendConst (Cobham.proj 1) _)
      (cobham_appendConst (Cobham.proj 1) _) (Cobham.proj 0) fun args => ?_
    simp only [brnFn]
    suffices ∀ x v, (brnAux (fun _ => []) (fun args => args.getD 1 [] ++ [false])
        (fun args => args.getD 1 [] ++ [true]) x v) = x.reverse by
      rw [this]; simp [PTime.proj]
    intro x v
    induction x with
    | nil => simp [brnAux]
    | cons b x ih => cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ, List.getD_cons_zero, ih]; simp)
  refine (cobham_c1 hb ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  generalize a args = x
  induction x with
  | nil => simp [brnAux]
  | cons b x ih => cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ, List.getD_cons_zero, ih]; simp)

/-- The prefix of `a` that is as long as `y`. -/
theorem cobham_takeBy {y a : Fn} (hy : Cobham y) (ha : Cobham a) :
    Cobham fun args => (a args).take (y args).length := by
  refine (cobham_rev (cobham_dropBy (cobham_dropBy hy ha) (cobham_rev ha))).of_fun_eq fun args => ?_
  rw [List.length_drop, List.drop_reverse, List.reverse_reverse]
  by_cases h : (y args).length ≤ (a args).length
  · congr 1; omega
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- A string of `false`s as long as `a`. -/
theorem cobham_falses {a : Fn} (ha : Cobham a) :
    Cobham fun args => List.replicate (a args).length false := by
  have hb : Cobham (brnFn (fun _ => []) (fun args => false :: args.getD 1 [])
      (fun args => false :: args.getD 1 [])) := by
    refine Cobham.brn Cobham.empty (cobham_cons' _ (Cobham.proj 1))
      (cobham_cons' _ (Cobham.proj 1)) (Cobham.proj 0) fun args => ?_
    simp only [brnFn]
    suffices ∀ x v, (brnAux (fun _ => []) (fun args => false :: args.getD 1 [])
        (fun args => false :: args.getD 1 []) x v) = List.replicate x.length false by
      rw [this]; simp [PTime.proj]
    intro x v
    induction x with
    | nil => simp [brnAux]
    | cons b x ih => cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ, List.getD_cons_zero, ih]; simp [List.replicate_succ])
  refine (cobham_c1 hb ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  generalize a args = x
  induction x with
  | nil => simp [brnAux]
  | cons b x ih => cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ, List.getD_cons_zero, ih]; simp [List.replicate_succ])

/-- The comparison of lengths. -/
theorem cobB_lenLE {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobB fun args => decide ((a args).length ≤ (b args).length) :=
  (cobB_null (cobham_dropBy hb ha)).of_eq fun args => by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.drop_eq_nil_iff]; simp

/-- Dropping the leading `false`s. -/
theorem cobham_dropFalses {a : Fn} (ha : Cobham a) :
    Cobham fun args => (a args).dropWhile (fun b => !b) := by
  have hb : Cobham (brnFn (fun _ => []) (proj 1) (fun args => true :: args.getD 0 [])) := by
    refine Cobham.brn Cobham.empty (Cobham.proj 1) (cobham_cons' _ (Cobham.proj 0))
      (Cobham.proj 0) fun args => ?_
    simp only [brnFn]
    suffices ∀ x v, (brnAux (fun _ => []) (proj 1) (fun args => true :: args.getD 0 [])
        x v) = x.dropWhile (fun b => !b) by
      rw [this]
      exact le_trans ((List.dropWhile_suffix _).length_le) (by simp [PTime.proj])
    intro x v
    induction x with
    | nil => simp [brnAux]
    | cons b x ih => cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ, List.getD_cons_zero, ih]; try simp [PTime.proj])
  refine (cobham_c1 hb ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  generalize a args = x
  induction x with
  | nil => simp [brnAux]
  | cons b x ih => cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ, List.getD_cons_zero, ih]; try simp [PTime.proj])

/-! ### Definition by cases on a finite observation -/

/-- **Definition by cases on a finite observation.**  If the observation `obs` takes values in a
finite type and each of its level sets is decided in the class, then a function that chooses a
function of the class according to the observation is in the class. -/
theorem cobham_dispatch {α : Type} [Fintype α] [DecidableEq α] (obs : Args → α)
    (hobs : ∀ a, CobB fun args => decide (obs args = a)) (Φ : α → Fn)
    (hΦ : ∀ a, Cobham (Φ a)) : Cobham fun args => Φ (obs args) args := by
  have key : ∀ L : List α, Cobham fun args =>
      L.foldr (fun a r => if obs args = a then Φ a args else r) [] := by
    intro L
    induction L with
    | nil => exact Cobham.empty
    | cons a L ih =>
      exact (cobham_ite (hobs a) (hΦ a) ih).of_fun_eq fun args => by simp
  refine (key Finset.univ.toList).of_fun_eq fun args => ?_
  have hmem : obs args ∈ (Finset.univ : Finset α).toList := by simp
  generalize (Finset.univ : Finset α).toList = L at hmem
  induction L with
  | nil => simp at hmem
  | cons a L ih =>
    by_cases h : obs args = a
    · simp [h]
    · simp only [List.foldr_cons, h, if_false]
      exact ih (by simpa [h] using hmem)

/-- The predicate form of `cobham_dispatch`. -/
theorem cobB_dispatch {α : Type} [Fintype α] [DecidableEq α] (obs : Args → α)
    (hobs : ∀ a, CobB fun args => decide (obs args = a)) (P : α → Args → Bool)
    (hP : ∀ a, CobB (P a)) : CobB fun args => P (obs args) args :=
  cobham_dispatch obs hobs (fun a args => [P a args]) hP

/-- Observations decided in the class are closed under post-composition. -/
theorem cobhamObs_map {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β] (obs : Args → α)
    (hobs : ∀ a, CobB fun args => decide (obs args = a)) (g : α → β) (b : β) :
    CobB fun args => decide (g (obs args) = b) :=
  cobB_dispatch obs hobs (fun a _ => decide (g a = b)) fun _ => cobB_const _

/-- Observations decided in the class are closed under pairing. -/
theorem cobhamObs_pair {α β : Type} [DecidableEq α] [DecidableEq β] (o₁ : Args → α)
    (o₂ : Args → β) (h₁ : ∀ a, CobB fun args => decide (o₁ args = a))
    (h₂ : ∀ b, CobB fun args => decide (o₂ args = b)) (c : α × β) :
    CobB fun args => decide ((o₁ args, o₂ args) = c) :=
  ((h₁ c.1).and (h₂ c.2)).of_eq fun args => by
    obtain ⟨c1, c2⟩ := c; simp [Prod.ext_iff]

/-- Observations decided in the class are closed under finite products. -/
theorem cobhamObs_pi {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type}
    [∀ i, DecidableEq (β i)] (o : ∀ i, Args → β i)
    (h : ∀ i b, CobB fun args => decide (o i args = b)) (c : ∀ i, β i) :
    CobB fun args => decide ((fun i => o i args) = c) :=
  (cobB_allList (Finset.univ : Finset ι).toList (fun i args => decide (o i args = c i))
    fun i _ => h i (c i)).of_eq fun args => by
      rw [Bool.eq_iff_iff]; simp [funext_iff]

/-! ### Iteration -/

/-- **Iteration of a step function of the class**, as many times as a computed counter string is
long, provided the initial value and every step stay below a bound of the class. -/
theorem cobham_iterate {init step cnt bd : Fn} (hinit : Cobham init) (hstep : Cobham step)
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
  refine (cobham_bind hcob hcnt).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  exact haux args (cnt args)

end HTN.PTime.CobhamTM
