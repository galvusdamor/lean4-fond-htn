import ComplexityTheory.Complexity.CobhamTM.ProgTM
/-!
# Realizing functions of Cobham's class by stack programs

`Prog.Realizer f` packages a *program scheme* for a function `f` of Cobham's class: for every
placement of the inputs (`inp i`, `i < A`), of the output stack `out` and of the first scratch
stack `base`, a program that writes `f` of the inputs onto the (empty) output stack, leaves every
other stack as it was, and runs in time polynomial in the size of the inputs.

This file provides the realizers of the basic functions (`realizer_empty`, `realizer_proj`,
`realizer_cons`, `realizer_smash`) and of composition (`realizer_comp`, through
`MultiRealizer`, which computes a list of functions into consecutive stacks).
-/

namespace HTN.PTime.CobhamTM

open HTN.PTime

namespace Prog

/-! ### Arguments on stacks -/

/-- The arguments read from the stacks `inp 0, …, inp (A - 1)`. -/
def argsOf (A : ℕ) (inp : ℕ → ℕ) (S : Store) : Args := (List.range A).map fun i => S (inp i)

/-- All stacks from `base` on are empty. -/
def Clean (base : ℕ) (S : Store) : Prop := ∀ j, base ≤ j → S j = []

theorem getD_argsOf {A i : ℕ} (hi : i < A) (inp : ℕ → ℕ) (S : Store) :
    (argsOf A inp S).getD i [] = S (inp i) := by
  simp [argsOf, List.getD_eq_getElem?_getD, hi]

theorem argSize_le_of {L : Args} {n : ℕ} (h : ∀ x ∈ L, x.length ≤ n) : argSize L ≤ n := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [argSize_cons]
    exact max_le (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem length_le_argSize_argsOf {A i : ℕ} (hi : i < A) (inp : ℕ → ℕ) (S : Store) :
    (S (inp i)).length ≤ argSize (argsOf A inp S) :=
  length_le_argSize (by simp only [argsOf, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)

theorem argsOf_congr {A : ℕ} {inp inp' : ℕ → ℕ} {S S' : Store}
    (h : ∀ i < A, S (inp i) = S' (inp' i)) : argsOf A inp S = argsOf A inp' S' := by
  simp only [argsOf]
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

theorem argSize_argsOf_mono {A A' : ℕ} (hA : A ≤ A') (inp : ℕ → ℕ) (S : Store) :
    argSize (argsOf A inp S) ≤ argSize (argsOf A' inp S) :=
  argSize_le_of fun x hx => by
    simp only [argsOf, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact length_le_argSize_argsOf (by omega) inp S

theorem argSize_padArgs_le (n : ℕ) (L : Args) : argSize (padArgs n L) ≤ argSize L :=
  argSize_le_of fun x hx => by
    simp only [padArgs, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact length_getD_le_argSize L i

/-- Two argument lists that agree on the first `n` entries give the same value to a function
reading only its first `n` arguments. -/
theorem _root_.HTN.PTime.CobhamTM.ReadsFirst.congr {n : ℕ} {f : Fn} (hf : ReadsFirst n f) {L₁ L₂ : Args}
    (h : ∀ i < n, L₁.getD i [] = L₂.getD i []) : f L₁ = f L₂ := by
  rw [hf L₁, hf L₂]
  congr 1
  simp only [padArgs]
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

theorem readsFirst_argsOf {A A' : ℕ} {f : Fn} (hf : ReadsFirst A f) (hA : A ≤ A')
    (inp : ℕ → ℕ) (S : Store) : f (argsOf A' inp S) = f (argsOf A inp S) :=
  hf.congr fun i hi => by rw [getD_argsOf (by omega), getD_argsOf hi]

noncomputable section

/-! ### Realizers -/

/-- **A realizer of `f`**: a program scheme computing `f` in polynomial time, for any placement
of inputs, output and scratch stacks. -/
structure Realizer (f : Fn) where
  /-- the number of arguments read -/
  A : ℕ
  /-- the program, given the input stacks, the output stack and the first scratch stack -/
  P : (ℕ → ℕ) → ℕ → ℕ → Prog
  /-- the number of scratch stacks -/
  W : ℕ
  /-- the running time, a polynomial in the size of the inputs -/
  time : Polynomial ℕ
  reads : ReadsFirst A f
  bound : ∀ inp out base, (∀ i < A, inp i < base) → out < base →
    maxStack (P inp out base) ≤ base + W
  spec : ∀ inp out base (S : Store), (∀ i < A, inp i < base) → out < base →
    (∀ i < A, inp i ≠ out) → S out = [] → Clean base S →
    Runs (P inp out base) S (Function.update S out (f (argsOf A inp S)))
      (time.eval (argSize (argsOf A inp S)))

/-- A realizer may claim to read more arguments. -/
def Realizer.lift {f : Fn} (R : Realizer f) (A' : ℕ) (hA : R.A ≤ A') : Realizer f where
  A := A'
  P := R.P
  W := R.W
  time := R.time
  reads := R.reads.mono hA
  bound inp out base hinp hout := R.bound inp out base (fun i hi => hinp i (by omega)) hout
  spec inp out base S hinp hout hne hS hc := by
    have := R.spec inp out base S (fun i hi => hinp i (by omega)) hout (fun i hi => hne i (by omega))
      hS hc
    rw [readsFirst_argsOf R.reads hA]
    exact this.mono (Polynomial.eval_mono_nat _ (argSize_argsOf_mono hA inp S))

theorem Realizer.lift_A {f : Fn} (R : Realizer f) (A' : ℕ) (hA : R.A ≤ A') :
    (R.lift A' hA).A = A' := rfl

/-! ### Maximal stack indices of the basic programs -/

theorem maxStack_clear (k : ℕ) : maxStack (clear k) = k := by simp [clear, maxStack]

theorem maxStack_moveRev (a b : ℕ) : maxStack (moveRev a b) = max a b := by
  simp only [moveRev, move1, maxStack]; omega

theorem maxStack_copy (a b c : ℕ) : maxStack (copy a b c) = max a (max b c) := by
  simp only [copy, moveRev, move1, moveRev2, move2, maxStack]; omega

/-! ### The basic functions -/

/-- The constant empty string. -/
def realizer_empty : Realizer (fun _ => []) where
  A := 0
  P _ _ _ := skip
  W := 0
  time := 0
  reads _ := rfl
  bound _ _ _ _ _ := by simp [maxStack]
  spec inp out base S _ _ _ hS _ := by
    refine ((Runs.skip S).mono (Nat.zero_le _)).of_eq ?_
    rw [← hS, update_eq_self']

/-- The projections. -/
def realizer_proj (n : ℕ) : Realizer (proj n) where
  A := n + 1
  P inp out base := copy (inp n) out base
  W := 0
  time := 9 * Polynomial.X + 2
  reads := fun args => by simp only [PTime.proj]; rw [getD_padArgs (by omega)]
  bound inp out base hinp hout := by
    rw [maxStack_copy]; have := hinp n (by omega); omega
  spec inp out base S hinp hout hne hS hc := by
    have h := runs_copy (hne n (by omega)) (by have := hinp n (by omega); omega) (by omega) S
      (hc base le_rfl)
    rw [hS, List.append_nil] at h
    refine (h.mono ?_).of_eq ?_
    · have := length_le_argSize_argsOf (show n < n + 1 by omega) inp S
      simp; omega
    · show _ = Function.update S out ((argsOf (n + 1) inp S).getD n [])
      rw [getD_argsOf (by omega)]

/-- The successors. -/
def realizer_cons (b : Bool) : Realizer (consFn b) where
  A := 1
  P inp out base := seq (copy (inp 0) out base) (push out b)
  W := 0
  time := 9 * Polynomial.X + 3
  reads := fun args => by simp only [consFn]; rw [getD_padArgs (by omega)]
  bound inp out base hinp hout := by
    simp only [maxStack, maxStack_copy]; have := hinp 0 (by omega); omega
  spec inp out base S hinp hout hne hS hc := by
    have h := runs_copy (hne 0 (by omega)) (by have := hinp 0 (by omega); omega) (by omega) S
      (hc base le_rfl)
    rw [hS, List.append_nil] at h
    have h2 := h.seq (Runs.push out b _)
    refine (h2.mono ?_).of_eq ?_
    · have := length_le_argSize_argsOf (show 0 < 1 by omega) inp S
      simp; omega
    · show _ = Function.update S out (b :: (argsOf 1 inp S).getD 0 [])
      rw [getD_argsOf (by omega)]
      simp [Function.update_idem]

/-! ### Smash -/

/-- Pop `src` until it is empty, pushing a `false` on `dst` for every bit. -/
def drainF (src dst : ℕ) : Prog := loop src (seq (pop src) (push dst false))

theorem runs_drainF {src dst : ℕ} (hne : src ≠ dst) (S : Store) :
    Runs (drainF src dst) S
      (Function.update (Function.update S src []) dst
        (List.replicate (S src).length false ++ S dst))
      (3 * (S src).length + 1) := by
  generalize hl : S src = l
  induction l generalizing S with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update S src []) dst
        (List.replicate ([] : List Bool).length false ++ S dst) = S := by
      simp only [List.length_nil, List.replicate_zero, List.nil_append]
      rw [← hl, update_eq_self', update_eq_self']
    rw [this]; exact Eval.loopNil hl
  | cons b l ih =>
    set S₁ := Function.update (Function.update S src l) dst (false :: S dst) with hS₁
    obtain ⟨t, ht, e⟩ := ih S₁ (by rw [hS₁, update_ne' _ hne, update_same'])
    have hstep : Eval (seq (pop src) (push dst false)) S S₁ 2 := by
      have := Eval.seq (Eval.pop src S) (Eval.push dst false (Function.update S src (S src).tail))
      simpa [hl, hS₁, update_ne' _ (Ne.symm hne)] using this
    refine ⟨2 + t + 1, by simp; omega, ?_⟩
    have := Eval.loopCons (by rw [hl]; simp) hstep e
    convert this using 1
    funext j
    by_cases hjd : j = dst
    · subst hjd
      rw [update_same', update_same', hS₁, update_same']
      simp [List.replicate_succ', List.append_assoc]
    · rw [update_ne' _ hjd, update_ne' _ hjd]
      by_cases hjs : j = src
      · subst hjs; rw [update_same', update_same']
      · rw [update_ne' _ hjs, update_ne' _ hjs, hS₁, update_ne' _ hjd, update_ne' _ hjs]

/-- The body of the outer loop of smash. -/
def smashBody (T₁ T₂ tmp y out : ℕ) : Prog :=
  seq (pop T₁) (seq (copy y T₂ tmp) (drainF T₂ out))

theorem runs_smashLoop {T₁ T₂ tmp y out : ℕ} (h12 : T₁ ≠ T₂) (h1t : T₁ ≠ tmp) (h2t : T₂ ≠ tmp)
    (hy1 : y ≠ T₁) (hy2 : y ≠ T₂) (hyt : y ≠ tmp) (hyo : y ≠ out) (ho1 : out ≠ T₁)
    (ho2 : out ≠ T₂) (hot : out ≠ tmp) (S : Store) (h2 : S T₂ = []) (ht : S tmp = []) :
    Runs (loop T₁ (smashBody T₁ T₂ tmp y out)) S
      (Function.update (Function.update S T₁ [])
        out (List.replicate ((S T₁).length * (S y).length) false ++ S out))
      ((S T₁).length * (12 * (S y).length + 5) + 1) := by
  generalize hl : S T₁ = l
  induction l generalizing S with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update S T₁ []) out
        (List.replicate (([] : List Bool).length * (S y).length) false ++ S out) = S := by
      simp only [List.length_nil, Nat.zero_mul, List.replicate_zero, List.nil_append]
      rw [← hl, update_eq_self', update_eq_self']
    rw [this]; exact Eval.loopNil hl
  | cons b l ih =>
    set S₁ := Function.update S T₁ l with hS₁
    have r1 : Runs (pop T₁) S S₁ 1 := by
      have := Runs.pop T₁ S; rwa [hl] at this
    have hc := runs_copy hy2 hyt h2t S₁ (by simp [hS₁, Ne.symm h1t, ht])
    set S₂ := Function.update S₁ T₂ (S₁ y ++ S₁ T₂) with hS₂
    have hd := runs_drainF (Ne.symm ho2) S₂
    set S₃ := Function.update (Function.update S₂ T₂ []) out
      (List.replicate (S₂ T₂).length false ++ S₂ out) with hS₃
    have e₂2 : S₂ T₂ = S y := by simp [hS₂, hS₁, hy1, Ne.symm h12, h2]
    have hround : Runs (smashBody T₁ T₂ tmp y out) S S₃ (12 * (S y).length + 4) := by
      refine ((r1.seq (hc.seq hd))).mono ?_
      rw [e₂2]
      have : S₁ y = S y := by simp [hS₁, hy1]
      rw [this]; omega
    have hS₃1 : S₃ T₁ = l := by
      simp [hS₃, hS₂, hS₁, Function.update_apply, Ne.symm ho1, h12]
    have hS₃2 : S₃ T₂ = [] := by simp [hS₃, Ne.symm ho2]
    have hS₃t : S₃ tmp = [] := by
      simp [hS₃, hS₂, hS₁, Function.update_apply, Ne.symm hot, Ne.symm h2t, Ne.symm h1t, ht]
    have hS₃y : S₃ y = S y := by
      simp [hS₃, hS₂, hS₁, Function.update_apply, hyo, hy2, hy1]
    obtain ⟨t₁, ht₁, e₁⟩ := hround
    obtain ⟨t₂, ht₂, e₂⟩ := ih S₃ hS₃2 hS₃t hS₃1
    refine ⟨t₁ + t₂ + 1, ?_, ?_⟩
    · rw [hS₃y] at ht₂
      simp only [List.length_cons]
      nlinarith
    · have := Eval.loopCons (by rw [hl]; simp) e₁ e₂
      convert this using 1
      rw [hS₃y]
      have hS₃o : S₃ out = List.replicate (S y).length false ++ S out := by
        rw [hS₃, update_same', e₂2]
        congr 1
        simp [hS₂, hS₁, Function.update_apply, ho2, ho1]
      have hS₃j : ∀ j, j ≠ T₁ → j ≠ out → S₃ j = S j := by
        intro j hj1 hjo
        simp only [hS₃, hS₂, hS₁, Function.update_apply, hj1, hjo, if_false]
        split_ifs with h
        · subst h; exact h2.symm
        · rfl
      funext j
      by_cases hjo : j = out
      · subst hjo
        rw [update_same', update_same', hS₃o, ← List.append_assoc, ← List.replicate_add]
        congr 2
        simp only [List.length_cons]; ring
      · rw [update_ne' _ hjo, update_ne' _ hjo]
        by_cases hj1 : j = T₁
        · subst hj1; rw [update_same', update_same']
        · rw [update_ne' _ hj1, update_ne' _ hj1, hS₃j j hj1 hjo]

theorem maxStack_drainF (a b : ℕ) : maxStack (drainF a b) = max a b := by
  simp only [drainF, maxStack]; omega

/-- Smash. -/
def realizer_smash : Realizer smashFn where
  A := 2
  P inp out base := seq (copy (inp 0) base (base + 2))
    (loop base (smashBody base (base + 1) (base + 2) (inp 1) out))
  W := 2
  time := 12 * Polynomial.X ^ 2 + 14 * Polynomial.X + 3
  reads := fun args => by
    simp only [smashFn]; rw [getD_padArgs (by omega), getD_padArgs (by omega)]
  bound inp out base hinp hout := by
    have h0 := hinp 0 (by omega); have h1 := hinp 1 (by omega)
    simp only [maxStack, smashBody, maxStack_copy, maxStack_drainF]; omega
  spec inp out base S hinp hout hne hS hc := by
    have h0 := hinp 0 (by omega); have h1 := hinp 1 (by omega)
    have hn1 := hne 1 (by omega)
    have r1 := runs_copy (show inp 0 ≠ base by omega) (show inp 0 ≠ base + 2 by omega)
      (show base ≠ base + 2 by omega) S (hc _ (by omega))
    rw [hc base le_rfl, List.append_nil] at r1
    set S₁ := Function.update S base (S (inp 0)) with hS₁
    have r2 := runs_smashLoop (T₁ := base) (T₂ := base + 1) (tmp := base + 2) (y := inp 1)
      (out := out) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hn1
      (by omega) (by omega) (by omega) S₁
      (by rw [hS₁, update_ne' _ (by omega)]; exact hc _ (by omega))
      (by rw [hS₁, update_ne' _ (by omega)]; exact hc _ (by omega))
    have e1 : S₁ base = S (inp 0) := by rw [hS₁, update_same']
    have e2 : S₁ (inp 1) = S (inp 1) := by rw [hS₁, update_ne' _ (by omega)]
    have e3 : S₁ out = [] := by rw [hS₁, update_ne' _ (by omega)]; exact hS
    rw [e1, e2, e3, List.append_nil] at r2
    have hx0 := length_le_argSize_argsOf (show 0 < 2 by omega) inp S
    have hx1 := length_le_argSize_argsOf (show 1 < 2 by omega) inp S
    refine ((r1.seq r2).mono ?_).of_eq ?_
    · set n := argSize (argsOf 2 inp S)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      nlinarith [Nat.mul_le_mul hx0 hx1]
    · have : Function.update S₁ base [] = S := by
        rw [hS₁, Function.update_idem, ← hc base le_rfl, update_eq_self']
      rw [this]
      show _ = Function.update S out (List.replicate (((argsOf 2 inp S).getD 0 []).length *
        ((argsOf 2 inp S).getD 1 []).length) false)
      rw [getD_argsOf (by omega), getD_argsOf (by omega)]

/-! ### Writing a list of results into consecutive stacks -/

/-- Write the strings of `L` into the stacks `r, r + 1, …`. -/
def writeList : Store → ℕ → List (List Bool) → Store
  | S, _, [] => S
  | S, r, x :: L => writeList (Function.update S r x) (r + 1) L

theorem writeList_of_lt (S : Store) (r : ℕ) (L : List (List Bool)) {j : ℕ} (hj : j < r) :
    writeList S r L j = S j := by
  induction L generalizing S r with
  | nil => rfl
  | cons x L ih => rw [writeList, ih _ _ (by omega), update_ne' _ (by omega)]

theorem writeList_of_ge (S : Store) (r : ℕ) (L : List (List Bool)) {j : ℕ}
    (hj : r + L.length ≤ j) : writeList S r L j = S j := by
  induction L generalizing S r with
  | nil => rfl
  | cons x L ih =>
    rw [writeList, ih _ _ (by simp at hj; omega), update_ne' _ (by simp at hj; omega)]

theorem writeList_at (S : Store) (r : ℕ) (L : List (List Bool)) {i : ℕ} (hi : i < L.length) :
    writeList S r L (r + i) = L[i] := by
  induction L generalizing S r i with
  | nil => simp at hi
  | cons x L ih =>
    rw [writeList]
    cases i with
    | zero => rw [writeList_of_lt _ _ _ (by omega), Nat.add_zero, update_same']; rfl
    | succ i =>
      rw [show r + (i + 1) = (r + 1) + i by omega, ih _ _ (by simp at hi; omega)]
      rfl

theorem update_writeList (S : Store) (r : ℕ) (L : List (List Bool)) {k : ℕ} (hk : k < r)
    (y : List Bool) :
    Function.update (writeList S r L) k y = writeList (Function.update S k y) r L := by
  induction L generalizing S r with
  | nil => rfl
  | cons x L ih =>
    rw [writeList, writeList, ih _ _ (by omega), Function.update_comm (by omega)]

/-- Clear the stacks `r, …, r + m - 1`. -/
def clearFrom : ℕ → ℕ → Prog
  | _, 0 => skip
  | r, m + 1 => seq (clear r) (clearFrom (r + 1) m)

theorem maxStack_clearFrom (r m : ℕ) : maxStack (clearFrom r m) ≤ r + m := by
  induction m generalizing r with
  | zero => simp [clearFrom, maxStack]
  | succ m ih =>
    simp only [clearFrom, maxStack, maxStack_clear]
    have := ih (r + 1); omega

theorem runs_clearFrom (L : List (List Bool)) (S : Store) (r : ℕ)
    (hS : ∀ i < L.length, S (r + i) = []) :
    Runs (clearFrom r L.length) (writeList S r L) S (L.length * (2 * argSize L + 1)) := by
  induction L generalizing S r with
  | nil => exact Runs.skip S
  | cons x L ih =>
    have h1 := runs_clear r (writeList S r (x :: L))
    have e1 : writeList S r (x :: L) r = x := by
      have := writeList_at S r (x :: L) (i := 0) (by simp); simpa using this
    rw [e1] at h1
    have e2 : Function.update (writeList S r (x :: L)) r [] = writeList S (r + 1) L := by
      rw [writeList, update_writeList _ _ _ (by omega), Function.update_idem]
      have := hS 0 (by simp); rw [Nat.add_zero] at this
      rw [← this, update_eq_self']
    rw [e2] at h1
    have h2 := ih S (r + 1) fun i hi => by
      rw [show r + 1 + i = r + (i + 1) by omega]; exact hS (i + 1) (by simp; omega)
    refine (h1.seq h2).mono ?_
    have hx : x.length ≤ argSize (x :: L) := by rw [argSize_cons]; exact le_max_left _ _
    have hL : argSize L ≤ argSize (x :: L) := by rw [argSize_cons]; exact le_max_right _ _
    simp only [List.length_cons]
    nlinarith

/-! ### Computing a list of functions into consecutive stacks -/

/-- A program scheme computing a list of functions into consecutive stacks `r, r + 1, …`;
the stack `r + length` stays empty and the scratch stacks start at `r + length + 1`. -/
structure MultiRealizer (hs : List Fn) where
  A : ℕ
  P : (ℕ → ℕ) → ℕ → Prog
  W : ℕ
  time : Polynomial ℕ
  reads : ∀ h ∈ hs, ReadsFirst A h
  bound : ∀ inp r, (∀ i < A, inp i < r) → maxStack (P inp r) ≤ r + hs.length + 1 + W
  spec : ∀ inp r (S : Store), (∀ i < A, inp i < r) → Clean r S →
    Runs (P inp r) S (writeList S r (hs.map fun h => h (argsOf A inp S)))
      (time.eval (argSize (argsOf A inp S)))

/-- The empty list of functions. -/
def multi_nil : MultiRealizer [] where
  A := 0
  P _ _ := skip
  W := 0
  time := 0
  reads h hh := by simp at hh
  bound _ _ _ := by simp [maxStack]
  spec _ _ S _ _ := (Runs.skip S).mono (Nat.zero_le _)

/-- Adding a function in front of a list. -/
def multi_cons {h : Fn} {hs : List Fn} (Rh : Realizer h) (Rm : MultiRealizer hs) :
    MultiRealizer (h :: hs) where
  A := max Rh.A Rm.A
  P inp r := seq (Rh.P inp r (r + hs.length + 2)) (Rm.P inp (r + 1))
  W := max Rh.W Rm.W
  time := Rh.time + Rm.time
  reads k hk := by
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Rh.reads.mono (le_max_left _ _)
    · exact (Rm.reads k hk).mono (le_max_right _ _)
  bound inp r hinp := by
    have h1 := Rh.bound inp r (r + hs.length + 2) (fun i hi => by
      have := hinp i (by have := le_max_left Rh.A Rm.A; omega); omega) (by omega)
    have h2 := Rm.bound inp (r + 1) (fun i hi => by
      have := hinp i (by have := le_max_right Rh.A Rm.A; omega); omega)
    simp only [maxStack, List.length_cons]
    have := le_max_left Rh.W Rm.W; have := le_max_right Rh.W Rm.W
    omega
  spec inp r S hinp hc := by
    have hA1 : Rh.A ≤ max Rh.A Rm.A := le_max_left _ _
    have hA2 : Rm.A ≤ max Rh.A Rm.A := le_max_right _ _
    have r1 := Rh.spec inp r (r + hs.length + 2) S (fun i hi => by have := hinp i (by omega); omega)
      (by omega) (fun i hi => by have := hinp i (by omega); omega) (hc r le_rfl)
      (fun j hj => hc j (by omega))
    set S₁ := Function.update S r (h (argsOf Rh.A inp S)) with hS₁
    have hargs : ∀ A', A' ≤ max Rh.A Rm.A → argsOf A' inp S₁ = argsOf A' inp S := fun A' hA' =>
      argsOf_congr fun i hi => by
        rw [hS₁, update_ne' _ (by have := hinp i (by omega); omega)]
    have r2 := Rm.spec inp (r + 1) S₁ (fun i hi => by have := hinp i (by omega); omega)
      (fun j hj => by rw [hS₁, update_ne' _ (by omega)]; exact hc j (by omega))
    rw [hargs _ hA2] at r2
    refine ((r1.seq r2).mono ?_).of_eq ?_
    · simp only [Polynomial.eval_add]
      exact Nat.add_le_add (Polynomial.eval_mono_nat _ (argSize_argsOf_mono hA1 inp S))
        (Polynomial.eval_mono_nat _ (argSize_argsOf_mono hA2 inp S))
    · simp only [List.map_cons, writeList, hS₁]
      rw [readsFirst_argsOf Rh.reads hA1]
      congr 1
      exact List.map_congr_left fun k hk => (readsFirst_argsOf (Rm.reads k hk) hA2 inp S).symm

/-! ### Composition -/

theorem argSize_argsOf_writeList_le (A : ℕ) (S : Store) (base m : ℕ) (L : List (List Bool))
    (hL : L.length = m) (hS : S (base + m) = []) :
    argSize (argsOf A (fun i => base + min i m) (writeList S base L)) ≤ argSize L :=
  argSize_le_of fun x hx => by
    simp only [argsOf, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    by_cases hi : i < m
    · rw [min_eq_left hi.le, writeList_at _ _ _ (by omega)]
      exact length_le_argSize (List.getElem_mem _)
    · rw [min_eq_right (by omega), writeList_of_ge _ _ _ (by omega), hS]; simp

theorem getD_argsOf_writeList (A : ℕ) (S : Store) (base m : ℕ) (L : List (List Bool))
    (hL : L.length = m) (hS : S (base + m) = []) {i : ℕ} (hi : i < A) :
    (argsOf A (fun i => base + min i m) (writeList S base L)).getD i [] = L.getD i [] := by
  rw [getD_argsOf hi]
  by_cases him : i < m
  · rw [min_eq_left him.le, writeList_at _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [min_eq_right (by omega), writeList_of_ge _ _ _ (by omega), hS,
      List.getD_eq_default _ _ (by omega)]

/-- Composition, given a realizer of the outer function, a multi-realizer of the inner ones and
a common polynomial bound on the lengths of the inner results. -/
def realizer_comp {g : Fn} {hs : List Fn} (Rg : Realizer g) (Rm : MultiRealizer hs)
    (q : Polynomial ℕ) (hq : ∀ h ∈ hs, ∀ args, (h args).length ≤ q.eval (argSize args)) :
    Realizer (compFn g hs) where
  A := Rm.A
  P inp out base := seq (Rm.P inp base)
    (seq (Rg.P (fun i => base + min i hs.length) out (base + hs.length + 1))
      (clearFrom base hs.length))
  W := hs.length + 1 + max Rm.W Rg.W
  time := Rm.time + Rg.time.comp q + Polynomial.C hs.length * (2 * q + 1)
  reads := fun args => by
    simp only [compFn]
    congr 1
    exact List.map_congr_left fun h hh => Rm.reads h hh args
  bound inp out base hinp hout := by
    have h1 := Rm.bound inp base hinp
    have h2 := Rg.bound (fun i => base + min i hs.length) out (base + hs.length + 1)
      (fun i _ => by dsimp only; omega) (by omega)
    have h3 := maxStack_clearFrom base hs.length
    have := le_max_left Rm.W Rg.W; have := le_max_right Rm.W Rg.W
    simp only [maxStack]
    omega
  spec inp out base S hinp hout hne hS hc := by
    set m := hs.length
    set L := hs.map fun h => h (argsOf Rm.A inp S) with hLdef
    have hLm : L.length = m := by simp [hLdef, m]
    have r1 := Rm.spec inp base S hinp hc
    set S' := writeList S base L with hS'
    have hSm : S (base + m) = [] := hc _ (by omega)
    have r2 := Rg.spec (fun i => base + min i m) out (base + m + 1) S' (fun i _ => by dsimp only; omega)
      (by omega) (fun i _ => by dsimp only; omega) (by rw [hS', writeList_of_lt _ _ _ hout]; exact hS)
      (fun j hj => by rw [hS', writeList_of_ge _ _ _ (by omega)]; exact hc j (by omega))
    have hg : g (argsOf Rg.A (fun i => base + min i m) S') = g L :=
      Rg.reads.congr fun i hi => getD_argsOf_writeList Rg.A S base m L hLm hSm hi
    rw [hg] at r2
    have r3 := runs_clearFrom L (Function.update S out (g L)) base fun i hi => by
      rw [update_ne' _ (by omega)]; exact hc _ (by omega)
    rw [hLm, ← update_writeList _ _ _ hout] at r3
    refine ((r1.seq (r2.seq r3)).mono ?_)
    have hsz : argSize (argsOf Rg.A (fun i => base + min i m) S') ≤ argSize L :=
      argSize_argsOf_writeList_le Rg.A S base m L hLm hSm
    have hLq : argSize L ≤ q.eval (argSize (argsOf Rm.A inp S)) := argSize_map_le hq _
    set n := argSize (argsOf Rm.A inp S)
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    have e1 := Polynomial.eval_mono_nat Rg.time (hsz.trans hLq)
    rw [← hLm]
    have : L.length * (2 * argSize L + 1) ≤ L.length * (2 * q.eval n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [hLm] at this ⊢
    omega

end

end Prog

end HTN.PTime.CobhamTM
