import ComplexityTheory.Collapse.Bool
import ComplexityTheory.Complexity.Basic
/-!
# Quantifying over all bit strings of a given length, in polynomial space

This is the one programming device the advice-elimination argument needs beyond composition:

> **`HTN.PSpace.psBigOr` / `HTN.PSpace.psBigAnd`.**  If `p` is a predicate of the
> polynomial-space class reading its first `n + 1` arguments, then so are
>
>     args ↦ ∃ y, |y| = |args₀| ∧ p (y :: args₁ …)      and      args ↦ ∀ y, …
>
> — a quantifier over *exponentially many* strings, the first argument serving as the template
> fixing their length.

Polynomial time cannot do this (Cobham's class only quantifies over the polynomially many
suffixes of a string, `HTN.PTime.cobhamB_anyTails`); polynomial space can, by running through
the candidates one after another, which is exactly the iteration scheme of
`ComplexityTheory/Collapse/Fun.lean`.  The enumeration is the binary successor `succB`, whose
orbit through `0…0` is all of the strings of that length.

With these two lemmas every "for all configurations …, for all counters …, there is an advice
string such that …" of the collapse argument is a *term*, and no further machine has to be
built by hand.
-/

namespace HTN

namespace PSpace

open PTime

/-! ### The binary successor -/

/-- The successor of a bit string read as a binary numeral, least significant bit first; the
last successor of a string of length `m` wraps around to `0…0`. -/
def succB : List Bool → List Bool
  | [] => []
  | false :: x => true :: x
  | true :: x => false :: succB x

@[simp] theorem succB_nil : succB [] = [] := rfl

@[simp] theorem succB_cons_false (x : List Bool) : succB (false :: x) = true :: x := rfl

@[simp] theorem succB_cons_true (x : List Bool) : succB (true :: x) = false :: succB x := rfl

@[simp] theorem length_succB : ∀ x : List Bool, (succB x).length = x.length
  | [] => rfl
  | false :: _ => rfl
  | true :: x => by simp [length_succB x]

theorem val_succB : ∀ x : List Bool, val (succB x) = (val x + 1) % 2 ^ x.length
  | [] => by simp
  | false :: x => by
    have h := val_lt_two_pow x
    have : 2 * val x + 1 < 2 ^ (x.length + 1) := by
      have : (2:ℕ) ^ (x.length + 1) = 2 ^ x.length + 2 ^ x.length := by ring
      omega
    rw [succB_cons_false, val_cons_true, val_cons_false, List.length_cons,
      Nat.mod_eq_of_lt (by omega)]
    omega
  | true :: x => by
    have ih := val_succB x
    rw [succB_cons_true, val_cons_false, val_cons_true, List.length_cons, ih, pow_succ]
    have h : (1 + 2 * val x + 1) = 2 * (val x + 1) := by ring
    rw [h, Nat.mul_comm (2 ^ x.length) 2, Nat.mul_mod_mul_left]

/-- Two strings of the same length with the same value are equal. -/
theorem val_inj_of_length_eq : ∀ x y : List Bool, x.length = y.length → val x = val y → x = y
  | [], [], _, _ => rfl
  | b :: x, c :: y, hl, hv => by
    have hl' : x.length = y.length := by simpa using hl
    have hx := val_lt_two_pow x
    have hy := val_lt_two_pow y
    have hbc : b = c := by
      rcases b with _ | _ <;> rcases c with _ | _ <;> simp_all <;> omega
    subst hbc
    have hxy : val x = val y := by
      rcases b with _ | _ <;> simp only [val_cons_false, val_cons_true] at hv <;> omega
    rw [val_inj_of_length_eq x y hl' hxy]

/-! ### The enumeration of all strings of a given length -/

/-- The all-zero string of a given length. -/
def zeros (m : ℕ) : List Bool := List.replicate m false

@[simp] theorem length_zeros (m : ℕ) : (zeros m).length = m := by simp [zeros]

@[simp] theorem val_zeros : ∀ m : ℕ, val (zeros m) = 0
  | 0 => rfl
  | m + 1 => by
    have h : zeros (m + 1) = false :: zeros m := by simp [zeros, List.replicate_succ]
    rw [h, val_cons_false, val_zeros m]

/-- The all-one string of a given length, the largest binary numeral of that length. -/
theorem val_replicate_true : ∀ m : ℕ, val (List.replicate m true) = 2 ^ m - 1
  | 0 => rfl
  | m + 1 => by
    have h := val_replicate_true m
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [List.replicate_succ, val_cons_true, h, pow_succ]
    omega

@[simp] theorem length_succB_iter (m : ℕ) : ∀ j : ℕ, (succB^[j] (zeros m)).length = m
  | 0 => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply', length_succB, length_succB_iter m j]

theorem val_succB_iter (m : ℕ) : ∀ j : ℕ, val (succB^[j] (zeros m)) = j % 2 ^ m
  | 0 => by simp [Nat.zero_mod]
  | j + 1 => by
    have ih := val_succB_iter m j
    rw [Function.iterate_succ_apply', val_succB, length_succB_iter, ih, Nat.mod_add_mod]

/-- **Every string of length `m` occurs in the orbit of `0…0` under the successor.** -/
theorem succB_iter_val (y : List Bool) : succB^[val y] (zeros y.length) = y := by
  refine val_inj_of_length_eq _ _ (by simp) ?_
  rw [val_succB_iter, Nat.mod_eq_of_lt (by simpa using val_lt_two_pow y)]

/-! ### The strings of a given length, as a list -/

theorem mem_allLen : ∀ (m : ℕ) (y : List Bool), y ∈ allLen m ↔ y.length = m
  | 0, y => by
    constructor
    · rintro hy
      simp only [allLen, List.mem_singleton] at hy
      simp [hy]
    · intro hy
      simp [allLen, List.length_eq_zero_iff.1 hy]
  | m + 1, y => by
    constructor
    · intro hy
      simp only [allLen, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hy
      obtain ⟨z, hz, hy⟩ := hy
      have hzl := (mem_allLen m z).1 hz
      rcases hy with rfl | rfl <;> simp [hzl]
    · intro hy
      match y with
      | b :: z =>
        have hzl : z.length = m := by simpa using hy
        refine List.mem_flatMap.2 ⟨z, (mem_allLen m z).2 hzl, ?_⟩
        cases b <;> simp

theorem anyLen_eq_true {m : ℕ} {q : List Bool → Bool} :
    anyLen m q = true ↔ ∃ y : List Bool, y.length = m ∧ q y = true := by
  simp only [anyLen, List.any_eq_true, mem_allLen]

theorem allLenB_eq_true {m : ℕ} {q : List Bool → Bool} :
    allLenB m q = true ↔ ∀ y : List Bool, y.length = m → q y = true := by
  simp only [allLenB, List.all_eq_true, mem_allLen]

/-! ### The enumeration functions belong to Cobham's class -/

/-- The binary successor, as a function of Cobham's class. -/
def succFn : Fn :=
  brnFn (fun _ => []) (compFn (consFn true) [proj 0]) (compFn (consFn false) [proj 1])

theorem brnAux_succ (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => []) (compFn (consFn true) [proj 0]) (compFn (consFn false) [proj 1]) x v
      = succB x
  | [] => rfl
  | false :: x => by simp [brnAux, compFn, consFn, proj]
  | true :: x => by
    simp only [brnAux, cond_true, compFn, consFn, proj, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ, succB_cons_true]
    rw [brnAux_succ v x]

theorem succFn_apply (args : Args) : succFn args = succB (args.getD 0 []) := by
  rw [succFn, brnFn, brnAux_succ]

theorem cobham_succFn : Cobham succFn := by
  refine Cobham.brn Cobham.empty (cobham_c1 (Cobham.cons true) (Cobham.proj 0))
    (cobham_c1 (Cobham.cons false) (Cobham.proj 1)) (Cobham.proj 0) fun args => ?_
  have h : brnFn (fun _ => []) (compFn (consFn true) [proj 0]) (compFn (consFn false) [proj 1])
      = succFn := rfl
  rw [h, succFn_apply, length_succB]
  simp [proj]

/-- The all-zero string of the length of the first argument. -/
def zerosFn : Fn := compFn smashFn [proj 0, fun _ => [false]]

theorem zerosFn_apply (args : Args) : zerosFn args = zeros (args.getD 0 []).length := by
  simp [zerosFn, compFn, smashFn, proj, zeros]

theorem cobham_zerosFn : Cobham zerosFn :=
  cobham_c2 Cobham.smash (Cobham.proj 0) (cobham_const [false])

/-- The all-one string, one bit longer than the first argument: a counter large enough to run
through every string of the length of the first argument. -/
def onesFn : Fn :=
  brnFn (fun _ => [true]) (compFn (consFn true) [proj 1]) (compFn (consFn true) [proj 1])

theorem brnAux_ones (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => [true]) (compFn (consFn true) [proj 1]) (compFn (consFn true) [proj 1]) x v
      = List.replicate (x.length + 1) true
  | [] => rfl
  | b :: x => by
    have hb : brnAux (fun _ => [true]) (compFn (consFn true) [proj 1])
        (compFn (consFn true) [proj 1]) (b :: x) v
        = compFn (consFn true) [proj 1]
          (x :: brnAux (fun _ => [true]) (compFn (consFn true) [proj 1])
            (compFn (consFn true) [proj 1]) x v :: v) := by
      cases b <;> rfl
    rw [hb, brnAux_ones v x]
    simp [compFn, consFn, proj, List.replicate_succ]

theorem onesFn_apply (args : Args) :
    onesFn args = List.replicate ((args.getD 0 []).length + 1) true := by
  rw [onesFn, brnFn, brnAux_ones]

theorem cobham_onesFn : Cobham onesFn := by
  refine Cobham.brn (cobham_const [true]) (cobham_c1 (Cobham.cons true) (Cobham.proj 1))
    (cobham_c1 (Cobham.cons true) (Cobham.proj 1))
    (cobham_c1 (Cobham.cons false) (Cobham.proj 0)) fun args => ?_
  have h : brnFn (fun _ => [true]) (compFn (consFn true) [proj 1])
      (compFn (consFn true) [proj 1]) = onesFn := rfl
  rw [h, onesFn_apply]
  simp [compFn, consFn, proj]

/-- The initial state of the enumeration: the flag `false` in front of the all-zero string. -/
def enumInitFn : Fn := compFn (fun args => args.getD 0 [] ++ args.getD 1 []) [fun _ => [false],
  zerosFn]

theorem enumInitFn_apply (args : Args) :
    enumInitFn args = false :: zeros (args.getD 0 []).length := by
  simp [enumInitFn, compFn, zerosFn_apply, proj]

theorem cobham_enumInitFn : Cobham enumInitFn :=
  cobham_c2 cobham_append (cobham_const [false]) cobham_zerosFn

/-! ### The head of a computed string -/

theorem psHead {a : Fn} (ha : PSpaceF a) : PSpaceB (fun args => (a args).headD false) := by
  have htab : Cobham (fun args : Args => [(args.getD 0 []).headD false]) :=
    cobhamB_head (Cobham.proj 0) |>.of_eq' fun args => by simp [proj]
  exact PSpaceF.of_eq (psC1 (PSpaceF.cobham htab) ha) fun args => by simp [compFn]

/-! ### The relay of the ambient arguments -/

theorem psSpace_relay (n k : ℕ) :
    ∀ f ∈ (List.range n).map (fun i => proj (i + k)), PSpaceF f := by
  intro f hf
  exact PSpaceF.cobham (cobham_relay n k f hf)

/-! ### Quantification over all strings of a given length -/

/-- **Existential quantification over all bit strings of the length of the first argument** is a
closure property of the polynomial-space class. -/
theorem psBigOr {p : Args → Bool} {n : ℕ} (hp : PSpaceB p) (hdep : ArgDep (n + 1) p) :
    PSpaceB (fun args =>
      anyLen (args.getD 0 []).length (fun y => p (y :: args.tail))) := by
  -- the body, with the ambient arguments relayed
  have hpv : ∀ (y : List Bool) (w : Args), p (y :: padArgs n w) = p (y :: w) := by
    intro y w
    rw [hdep (y :: w), padArgs_cons]
  have hbody : PSpaceB (fun args : Args =>
      p ((args.getD 0 []).tail :: padArgs n (args.drop 1))) := by
    have hcomp : PSpaceF (compFn (fun args => [p args])
        (compFn tailFn [proj 0] :: (List.range n).map (fun i => proj (i + 1)))) := by
      refine PSpaceF.comp hp ?_
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact PSpaceF.cobham (cobham_c1 cobham_tailFn (Cobham.proj 0))
      · exact psSpace_relay n 1 f hf
    refine PSpaceF.of_eq hcomp fun args => ?_
    show [p ((compFn tailFn [proj 0] :: (List.range n).map (fun i => proj (i + 1))).map
      (fun h => h args))] = _
    rw [List.map_cons, map_relay n 1 args]
    simp [compFn, tailFn_apply, proj]
  have hhead : PSpaceB (fun args : Args => (args.getD 0 []).headD false) :=
    PSpaceB.of_cobhamB ((cobhamB_head (Cobham.proj 0)).of_eq fun args => by simp [proj])
  -- the update of the enumeration
  set F : Fn := fun args =>
    [((args.getD 0 []).headD false || p ((args.getD 0 []).tail :: padArgs n (args.drop 1)))]
      ++ succB ((args.getD 0 []).tail) with hFdef
  have hFmem : PSpaceF F := by
    refine psAppend (hhead.or hbody) ?_
    exact PSpaceF.cobham ((cobham_c1 cobham_succFn (cobham_c1 cobham_tailFn (Cobham.proj 0))).of_eq'
      fun args => by simp [compFn, succFn_apply, tailFn_apply, proj])
  -- the state stays short
  have hlen : ∀ (v : Args) (k : ℕ) (st : List Bool),
      (loopAux F v k st).length ≤ st.length + 1 := by
    intro v k st
    induction k with
    | zero => simp
    | succ k ih =>
      rw [loopAux_succ]
      have hstep : (F (loopAux F v k st :: v)).length
          = (loopAux F v k st).tail.length + 1 := by
        rw [hFdef]
        simp only [List.getD_cons_zero, List.singleton_append, List.length_cons, length_succB]
      rw [hstep, List.length_tail]
      omega
  have hloop : PSpaceF (loopFn F) := by
    refine PSpaceF.loop hFmem (PSpaceF.cobham (cobham_c2 cobham_append (cobham_const [false])
      (Cobham.proj 1))) fun args => ?_
    have h1 := hlen args.tail.tail (val (args.getD 0 [])) (args.getD 1 [])
    have h2 : compFn (fun args : Args => args.getD 0 [] ++ args.getD 1 [])
        [fun _ => [false], proj 1] args = false :: args.getD 1 [] := by
      simp [compFn, proj]
    rw [h2, List.length_cons]
    simpa only [loopFn] using h1
  -- what the loop computes
  have hsem : ∀ (v : Args) (m k : ℕ),
      loopAux F v k (false :: zeros m)
        = (decide (∃ j, j < k ∧ p (succB^[j] (zeros m) :: v) = true)) :: succB^[k] (zeros m) := by
    intro v m k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [loopAux_succ, ih, hFdef]
      simp only [List.getD_cons_zero, List.headD_cons, List.tail_cons, List.drop_succ_cons,
        List.drop_zero, List.singleton_append]
      rw [hpv, Function.iterate_succ_apply']
      congr 1
      by_cases hk : ∃ j, j < k ∧ p (succB^[j] (zeros m) :: v) = true
      · simp only [hk, decide_true, Bool.true_or]
        refine (decide_eq_true ?_).symm
        obtain ⟨j, hj, hjp⟩ := hk
        exact ⟨j, by omega, hjp⟩
      · simp only [hk, decide_false, Bool.false_or]
        by_cases hp' : p (succB^[k] (zeros m) :: v) = true
        · simp only [hp', decide_true]
          exact (decide_eq_true ⟨k, by omega, hp'⟩).symm
        · simp only [hp', decide_false]
          refine (decide_eq_false ?_).symm
          rintro ⟨j, hj, hjp⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
          · exact hk ⟨j, hj', hjp⟩
          · exact hp' hjp
  -- the assembled function
  set G : Fn := compFn (loopFn F)
    (onesFn :: enumInitFn :: (List.range n).map (fun i => proj (i + 1))) with hGdef
  have hG : PSpaceF G := by
    refine PSpaceF.comp hloop ?_
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact PSpaceF.cobham cobham_onesFn
    rcases List.mem_cons.1 hf with rfl | hf
    · exact PSpaceF.cobham cobham_enumInitFn
    · exact psSpace_relay n 1 f hf
  have hGapply : ∀ args : Args, G args
      = loopAux F (padArgs n (args.drop 1)) (val (onesFn args))
        (false :: zeros (args.getD 0 []).length) := by
    intro args
    show loopFn F ((onesFn :: enumInitFn :: (List.range n).map (fun i => proj (i + 1))).map
      (fun h => h args)) = _
    rw [List.map_cons, List.map_cons, map_relay n 1 args, enumInitFn_apply]
    rfl
  -- reading the flag
  refine PSpaceB.of_eq (psHead hG) fun args => ?_
  rw [hGapply, hsem]
  simp only [List.headD_cons]
  have hKge : 2 ^ (args.getD 0 []).length ≤ val (onesFn args) := by
    rw [onesFn_apply, val_replicate_true]
    have h1 : (1:ℕ) ≤ 2 ^ (args.getD 0 []).length := Nat.one_le_two_pow
    have h2 : (2:ℕ) ^ ((args.getD 0 []).length + 1)
        = 2 ^ (args.getD 0 []).length + 2 ^ (args.getD 0 []).length := by ring
    omega
  have hdrop : args.drop 1 = args.tail := by simp
  rw [Bool.eq_iff_iff, anyLen_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨y, hy, hyp⟩
    refine ⟨val y, lt_of_lt_of_le ?_ hKge, ?_⟩
    · simpa [hy] using val_lt_two_pow y
    · rw [← hy, succB_iter_val y, hpv, hdrop]
      exact hyp
  · rintro ⟨j, -, hj⟩
    refine ⟨succB^[j] (zeros (args.getD 0 []).length), by simp, ?_⟩
    rw [← hdrop, ← hpv]
    exact hj

/-- **Universal quantification over all bit strings of the length of the first argument**, by
negating the existential one. -/
theorem psBigAnd {p : Args → Bool} {n : ℕ} (hp : PSpaceB p) (hdep : ArgDep (n + 1) p) :
    PSpaceB (fun args =>
      allLenB (args.getD 0 []).length (fun y => p (y :: args.tail))) := by
  have hdep' : ArgDep (n + 1) (fun args => !p args) := by
    intro args
    simp [hdep args]
  refine PSpaceB.of_eq (psBigOr hp.not hdep').not fun args => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', Bool.not_eq_true, allLenB_eq_true, ← Bool.not_eq_true,
    Bool.not_eq_true']
  constructor
  · intro hall
    have : ¬ anyLen (args.getD 0 []).length (fun y => !p (y :: args.tail)) = true := by
      rw [anyLen_eq_true]
      rintro ⟨y, hy, hyp⟩
      rw [hall y hy] at hyp
      simp at hyp
    simpa using this
  · intro hne y hy
    by_contra hc
    have : anyLen (args.getD 0 []).length (fun y => !p (y :: args.tail)) = true := by
      rw [anyLen_eq_true]
      exact ⟨y, hy, by simp [hc]⟩
    rw [this] at hne
    simp at hne

end PSpace

end HTN
