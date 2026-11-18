import HtnComplexity.PolyInst.Kit
import ComplexityTheory.Complexity.Counter
/-!
# Unary list comprehensions in Cobham's class

A small toolkit for writing polynomial-time reductions whose intermediate data are lists of
polynomially bounded numbers.  Numbers are written in unary (`un n = true^n`), lists of numbers
as `unl l` (each entry `n` written `false :: true^n`).

* `CobN f` — the number `f args` is computed in unary by a function of Cobham's class;
  closed under the arithmetic operations, definition by cases, bounded sums, division;
* `cobham_forRange` — emission over a range given in unary;
* `CobList L` — the list `L args` is computed (as `unl`);
  `cobham_forItems` — emission over the entries of a computed list, with their index;
* `cobN_getD`, `cobN_length` — reading a computed list.
-/

namespace HTN.NPHard

open HTN.PTime HTN.PTime.CobhamTM

/-- A number in unary. -/
def un (n : ℕ) : List Bool := List.replicate n true

@[simp] theorem length_un (n : ℕ) : (un n).length = n := by simp [un]

/-- **A number computed in unary by a function of Cobham's class.** -/
def CobN (f : Args → ℕ) : Prop := Cobham fun args => un (f args)

theorem CobN.of_eq {f g : Args → ℕ} (hf : CobN f) (h : ∀ args, f args = g args) : CobN g :=
  Cobham.of_fun_eq hf fun args => by rw [h]

/-- The unary value of a string's length. -/
theorem cobN_len {a : Fn} (ha : Cobham a) : CobN fun args => (a args).length :=
  (cobham_flatMapBits (fun _ => [true]) ha).of_fun_eq fun args => by
    simp only [un]
    generalize a args = x
    induction x with
    | nil => rfl
    | cons b x ih =>
      rw [List.flatMap_cons, ih, List.length_cons, List.replicate_succ]; rfl

theorem cobN_const (c : ℕ) : CobN fun _ => c := cobham_const (un c)

theorem cobN_arg (i : ℕ) : CobN fun args => (args.getD i []).length := cobN_len (Cobham.proj i)

theorem CobN.cobham {f : Args → ℕ} (hf : CobN f) : Cobham fun args => un (f args) := hf

theorem cobN_add {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) : CobN fun args => f args + g args :=
  (cobham_append' hf hg).of_fun_eq fun args => by simp only [un, List.replicate_add]

theorem cobN_sub {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) : CobN fun args => f args - g args :=
  (cobham_dropBy hg hf).of_fun_eq fun args => by simp [un, List.drop_replicate]

theorem cobN_mul {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) : CobN fun args => f args * g args :=
  (cobN_len (CobhamTM.cobham_c2 Cobham.smash hf hg)).of_eq fun args => by simp [smashFn]

theorem cobN_bind {F : Args → ℕ} (hF : CobN F) {a : Fn} (ha : Cobham a) :
    CobN fun args => F (a args :: args) := CobhamTM.cobham_bind hF ha

/-- Comparisons. -/
theorem cobB_le {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) :
    CobB fun args => decide (f args ≤ g args) :=
  (cobB_lenLE hf hg).of_eq fun args => by simp

theorem cobB_lt {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) :
    CobB fun args => decide (f args < g args) :=
  (cobB_le (cobN_add hf (cobN_const 1)) hg).of_eq fun args => by
    simp only [decide_eq_decide]; omega

theorem cobB_eq {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) :
    CobB fun args => decide (f args = g args) :=
  ((cobB_le hf hg).and (cobB_le hg hf)).of_eq fun args => by
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

theorem cobN_ite {p : Args → Bool} (hp : CobB p) {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) :
    CobN fun args => if p args then f args else g args :=
  (cobham_ite hp hf hg).of_fun_eq fun args => by by_cases h : p args <;> simp [h]

/-! ### Emission over a range -/

theorem tails_un (n : ℕ) : (un n).tails = (List.range (n + 1)).reverse.map un := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.map_append, ← ih]
    simp [un, List.replicate_succ]

theorem reverse_range_eq (n : ℕ) : (List.range n).reverse = (List.range n).map (fun k => n - 1 - k) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_reverse]

theorem flatMap_range_rev (n : ℕ) (F : ℕ → List Bool) :
    ((List.range (n + 1)).reverse.flatMap fun i => if i = 0 then [] else F (n - i)) =
      (List.range n).flatMap F := by
  rw [reverse_range_eq, List.flatMap_map, List.range_succ, List.flatMap_append]
  simp only [Nat.add_sub_cancel, Nat.sub_self, List.flatMap_cons, ↓reduceIte, List.flatMap_nil,
    List.append_nil]
  refine List.flatMap_congr fun i hi => ?_
  rw [List.mem_range] at hi
  rw [if_neg (by omega)]
  congr 1; omega

/-- **Emission over a range given in unary.**  The chunk sees the index in unary as its first
argument, followed by the ambient arguments. -/
theorem cobham_forRange {N : Args → ℕ} (hN : CobN N) {G : Fn} (hG : Cobham G) :
    Cobham fun args => (List.range (N args)).flatMap fun i => G (un i :: args) := by
  set G' : Fn := fun args =>
    if (args.getD 0 []).isEmpty then [] else
      G (un (N args.tail - (args.getD 0 []).length) :: args.tail) with hG'
  have hG'c : Cobham G' := by
    refine cobham_ite (cobB_null (Cobham.proj 0)) Cobham.empty ?_
    refine cobham_subst hG fun i => ?_
    cases i with
    | zero =>
      exact (cobN_sub (CobhamTM.cobham_dropArgs hN 1) (cobN_arg 0)).of_fun_eq fun args => by
        rcases args with _ | ⟨a, args⟩ <;> rfl
    | succ i =>
      exact (Cobham.proj (i + 1)).of_fun_eq fun args => by
        rcases args with _ | ⟨a, args⟩ <;> simp [PTime.proj]
  refine (cobham_fmTailsC hG'c hN).of_fun_eq fun args => ?_
  simp only [fmTailsL, tails_un, List.flatMap_map, hG', List.getD_cons_zero, List.tail_cons]
  rw [← flatMap_range_rev]
  refine List.flatMap_congr fun i _ => ?_
  cases i <;> simp [un]

/-- **Bounded sums.** -/
theorem cobN_sum {N : Args → ℕ} (hN : CobN N) {F : Args → ℕ} (hF : CobN F) :
    CobN fun args => ((List.range (N args)).map fun i => F (un i :: args)).sum := by
  refine (cobham_forRange hN hF).of_fun_eq fun args => ?_
  show _ = un (List.map _ (List.range (N args))).sum
  generalize List.range (N args) = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.flatMap_cons, ih, List.map_cons, List.sum_cons]; simp only [un, List.replicate_add]

/-- **Bounded counting.** -/
theorem cobN_count {N : Args → ℕ} (hN : CobN N) {p : Args → Bool} (hp : CobB p) :
    CobN fun args => ((List.range (N args)).filter fun i => p (un i :: args)).length := by
  refine (cobN_sum hN (cobN_ite hp (cobN_const 1) (cobN_const 0))).of_eq fun args => ?_
  generalize List.range (N args) = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    split <;> simp_all <;> omega

/-! ### Division -/

theorem length_filter_lt_range (f c : ℕ) :
    ((List.range f).filter fun k => decide (k < c)).length = min f c := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : f < c
    · simp [h]; omega
    · simp [h]; omega

theorem count_div (f d : ℕ) (hd : 0 < d) :
    ((List.range f).filter fun k => decide ((k + 1) * d ≤ f)).length = f / d := by
  have : ∀ k, decide ((k + 1) * d ≤ f) = decide (k < f / d) := fun k => by
    rw [decide_eq_decide, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hd]
  simp only [this]
  rw [length_filter_lt_range]
  exact min_eq_right (Nat.div_le_self _ _)

/-- Shifting a number to see one more (leading) argument. -/
theorem CobN.drop1 {f : Args → ℕ} (hf : CobN f) : CobN fun args => f args.tail :=
  (CobhamTM.cobham_dropArgs hf 1).of_fun_eq fun args => by rcases args with _ | ⟨a, args⟩ <;> rfl

theorem cobN_div {f d : Args → ℕ} (hf : CobN f) (hd : CobN d) :
    CobN fun args => f args / d args := by
  have hc := cobN_count hf (p := fun args => decide (((args.getD 0 []).length + 1) * d args.tail
    ≤ f args.tail)) (cobB_le (cobN_mul (cobN_add (cobN_arg 0) (cobN_const 1)) hd.drop1) hf.drop1)
  refine (cobN_ite (cobB_eq hd (cobN_const 0)) (cobN_const 0) hc).of_eq fun args => ?_
  by_cases h : d args = 0
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, List.getD_cons_zero, length_un,
      List.tail_cons]
    exact count_div _ _ (Nat.pos_of_ne_zero h)

theorem cobN_mod {f d : Args → ℕ} (hf : CobN f) (hd : CobN d) :
    CobN fun args => f args % d args :=
  (cobN_sub hf (cobN_mul hd (cobN_div hf hd))).of_eq fun args => by
    rw [Nat.mod_eq_sub_mul_div]

/-! ### Lists of numbers -/

/-- A list of numbers in unary: each entry `n` is written `false :: true^n`. -/
def unl (l : List ℕ) : List Bool := l.flatMap fun n => false :: un n

@[simp] theorem unl_nil : unl [] = [] := rfl

@[simp] theorem unl_cons (n : ℕ) (l : List ℕ) : unl (n :: l) = false :: (un n ++ unl l) := rfl

theorem unl_append (l l' : List ℕ) : unl (l ++ l') = unl l ++ unl l' := by
  simp [unl, List.flatMap_append]

theorem unl_flatMap {α : Type} (l : List α) (f : α → List ℕ) :
    unl (l.flatMap f) = l.flatMap fun a => unl (f a) := by
  simp [unl, List.flatMap_assoc]

/-- **A list of numbers computed by a function of Cobham's class** (in unary). -/
def CobList (L : Args → List ℕ) : Prop := Cobham fun args => unl (L args)

theorem CobList.of_eq {L L' : Args → List ℕ} (hL : CobList L) (h : ∀ args, L args = L' args) :
    CobList L' := Cobham.of_fun_eq hL fun args => by rw [h]

theorem cobList_nil : CobList fun _ => [] := Cobham.empty

theorem cobList_single {f : Args → ℕ} (hf : CobN f) : CobList fun args => [f args] :=
  (cobham_cons' false hf).of_fun_eq fun args => by simp [unl]

theorem cobList_append {L L' : Args → List ℕ} (hL : CobList L) (hL' : CobList L') :
    CobList fun args => L args ++ L' args :=
  (cobham_append' hL hL').of_fun_eq fun args => by rw [unl_append]

theorem cobList_cons {f : Args → ℕ} (hf : CobN f) {L : Args → List ℕ} (hL : CobList L) :
    CobList fun args => f args :: L args :=
  (cobList_append (cobList_single hf) hL).of_eq fun _ => rfl

theorem cobList_ite {p : Args → Bool} (hp : CobB p) {L L' : Args → List ℕ} (hL : CobList L)
    (hL' : CobList L') : CobList fun args => if p args then L args else L' args :=
  (cobham_ite hp hL hL').of_fun_eq fun args => by by_cases h : p args <;> simp [h]

theorem cobList_forRange {N : Args → ℕ} (hN : CobN N) {F : Args → List ℕ} (hF : CobList F) :
    CobList fun args => (List.range (N args)).flatMap fun i => F (un i :: args) :=
  (cobham_forRange hN hF).of_fun_eq fun args => by rw [unl_flatMap]

theorem cobList_flatMapFin {α : Type} (l : List α) {F : α → Args → List ℕ}
    (hF : ∀ a ∈ l, CobList (F a)) : CobList fun args => l.flatMap fun a => F a args :=
  (cobham_flatMapFin l (fun a args => unl (F a args)) hF).of_fun_eq fun args => by
    rw [unl_flatMap]

theorem CobList.drop1 {L : Args → List ℕ} (hL : CobList L) : CobList fun args => L args.tail :=
  (CobhamTM.cobham_dropArgs hL 1).of_fun_eq fun args => by rcases args with _ | ⟨a, args⟩ <;> rfl

theorem cobList_bind {L : Args → List ℕ} (hL : CobList L) {a : Fn} (ha : Cobham a) :
    CobList fun args => L (a args :: args) := CobhamTM.cobham_bind hL ha

/-! ### Emission over the entries of a computed list -/

/-- The leading `true`s of a string. -/
theorem cobham_takeTrues {a : Fn} (ha : Cobham a) :
    Cobham fun args => (a args).takeWhile id := by
  have hb : Cobham (brnFn (fun _ => []) (fun _ => []) (fun args => true :: args.getD 1 [])) := by
    refine Cobham.brn Cobham.empty Cobham.empty (cobham_cons' _ (Cobham.proj 1))
      (Cobham.proj 0) fun args => ?_
    simp only [brnFn]
    suffices ∀ x v, (brnAux (fun _ => []) (fun _ => []) (fun args => true :: args.getD 1 [])
        x v) = x.takeWhile id by
      rw [this]
      exact le_trans (List.takeWhile_prefix _).length_le (by simp [PTime.proj])
    intro x v
    induction x with
    | nil => simp [brnAux]
    | cons b x ih =>
      cases b <;> simp only [brnAux, cond_false, cond_true, List.getD_cons_succ,
        List.getD_cons_zero, ih] <;> simp
  refine (CobhamTM.cobham_c1 hb ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  generalize a args = x
  induction x with
  | nil => simp [brnAux]
  | cons b x ih =>
    cases b <;> simp only [brnAux, cond_false, cond_true, List.getD_cons_succ,
      List.getD_cons_zero, ih] <;> simp

/-- The number of `false`s of a string. -/
def cntF (x : List Bool) : ℕ := (x.filter fun b => !b).length

theorem cobN_cntF {a : Fn} (ha : Cobham a) : CobN fun args => cntF (a args) :=
  (cobham_flatMapBits (fun b => if b then [] else [true]) ha).of_fun_eq fun args => by
    simp only [cntF, un]
    generalize a args = x
    induction x with
    | nil => rfl
    | cons b x ih =>
      cases b
      · rw [List.flatMap_cons, ih]; simp [List.replicate_succ]
      · rw [List.flatMap_cons, ih]; simp

@[simp] theorem cntF_un (n : ℕ) : cntF (un n) = 0 := by
  simp [cntF, un, List.filter_replicate]

theorem cntF_append (x y : List Bool) : cntF (x ++ y) = cntF x + cntF y := by
  simp [cntF, List.filter_append]

theorem cntF_false_cons (x : List Bool) : cntF (false :: x) = cntF x + 1 := by
  simp [cntF]

theorem cntF_unl (l : List ℕ) : cntF (unl l) = l.length := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    rw [unl_cons, cntF_false_cons, cntF_append, cntF_un, ih]; simp

theorem takeWhile_un_append (n : ℕ) (l : List ℕ) : (un n ++ unl l).takeWhile id = un n := by
  induction n with
  | zero => cases l <;> simp [un]
  | succ n ih => simp only [un, List.replicate_succ, List.cons_append] at ih ⊢; simp [ih]

/-- The chunks at the starts of entries. -/
def atStarts (H : List Bool → List Bool) (x : List Bool) : List Bool :=
  x.tails.flatMap fun s => if (s.head? == some false) = true then H s else []

theorem atStarts_un_append (H : List Bool → List Bool) (n : ℕ) (y : List Bool) :
    atStarts H (un n ++ y) = atStarts H y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    simp only [atStarts, un, List.replicate_succ, List.cons_append, List.tails_cons,
      List.flatMap_cons, List.head?_cons]
    simp

theorem atStarts_unl (H : List Bool → List Bool) (l : List ℕ) :
    atStarts H (unl l) = (List.range l.length).flatMap fun i => H (unl (l.drop i)) := by
  induction l with
  | nil => simp [atStarts]
  | cons n l ih =>
    rw [unl_cons]
    have h1 : atStarts H (false :: (un n ++ unl l)) =
        H (false :: (un n ++ unl l)) ++ atStarts H (un n ++ unl l) := by
      simp [atStarts]
    rw [h1, atStarts_un_append, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

theorem unl_drop_eq {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    unl (l.drop i) = false :: (un (l.getD i 0) ++ unl (l.drop (i + 1))) := by
  rw [List.drop_eq_getElem_cons hi, unl_cons, List.getD_eq_getElem _ _ hi]

/-- **Emission over the entries of a computed list.**  The chunk sees the index and the value of
the entry, in unary, followed by the ambient arguments. -/
theorem cobham_forItems {L : Args → List ℕ} (hL : CobList L) {G : Fn} (hG : Cobham G) :
    Cobham fun args => (List.range (L args).length).flatMap fun i =>
      G (un i :: un ((L args).getD i 0) :: args) := by
  set G' : Fn := fun args =>
    if ((args.getD 0 []).head? == some false) = true then
      G (un (cntF (unl (L args.tail)) - cntF (args.getD 0 [])) ::
        ((args.getD 0 []).tail.takeWhile id) :: args.tail) else [] with hG'
  have hG'c : Cobham G' := by
    refine cobham_ite (cobB_headIs false (Cobham.proj 0)) ?_ Cobham.empty
    refine cobham_subst hG fun i => ?_
    rcases i with _ | _ | i
    · exact (cobN_sub (cobN_cntF hL.drop1) (cobN_cntF (Cobham.proj 0))).of_fun_eq fun _ => rfl
    · exact (cobham_takeTrues (cobham_tail' (Cobham.proj 0))).of_fun_eq fun _ => rfl
    · exact (Cobham.proj (i + 1)).of_fun_eq fun args => by
        rcases args with _ | ⟨a, args⟩ <;> simp [PTime.proj]
  refine (cobham_fmTailsC hG'c hL).of_fun_eq fun args => ?_
  have e : fmTailsL G' args (unl (L args)) = atStarts (fun s => G (un (cntF (unl (L args)) -
      cntF s) :: (s.tail.takeWhile id) :: args)) (unl (L args)) := by
    simp only [fmTailsL, atStarts, hG', List.getD_cons_zero, List.tail_cons]
  rw [e, atStarts_unl]
  refine List.flatMap_congr fun i hi => ?_
  rw [List.mem_range] at hi
  rw [unl_drop_eq hi, cntF_unl, List.tail_cons, takeWhile_un_append]
  congr 3
  rw [cntF_false_cons, cntF_append, cntF_un, cntF_unl, List.length_drop]
  omega

theorem flatMap_range_sel (n K : ℕ) (F : ℕ → List Bool) :
    ((List.range n).flatMap fun i => if i = K then F i else []) = if K < n then F K else [] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases h : K < n
    · simp [h, show K < n + 1 by omega, show n ≠ K by omega]
    · by_cases h' : n = K
      · subst h'; simp
      · simp [h, h', show ¬ K < n + 1 by omega]

/-- The length of a computed list. -/
theorem cobN_length {L : Args → List ℕ} (hL : CobList L) : CobN fun args => (L args).length :=
  (cobN_cntF hL).of_eq fun args => cntF_unl _

/-- **Reading an entry of a computed list.** -/
theorem cobN_getD {L : Args → List ℕ} (hL : CobList L) {K : Args → ℕ} (hK : CobN K) :
    CobN fun args => (L args).getD (K args) 0 := by
  set G : Fn := fun args =>
    if decide ((args.getD 0 []).length = K (args.drop 2)) = true then args.getD 1 [] else []
    with hG
  have hGc : Cobham G :=
    (cobham_ite (cobB_eq (cobN_arg 0) (CobhamTM.cobham_dropArgs hK 2)) (Cobham.proj 1)
      Cobham.empty).of_fun_eq fun _ => rfl
  refine (cobham_forItems hL hGc).of_fun_eq fun args => ?_
  simp only [hG, List.getD_cons_zero, length_un, List.drop_succ_cons, List.drop_zero,
    List.getD_cons_succ, decide_eq_true_eq]
  rw [flatMap_range_sel]
  split
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

end HTN.NPHard
