import HtnComplexity.Space.AltTests
/-!
# The alternating target-side machine

This file builds the alternating polynomial-space machine (`HTN.Space.AltSpace`) that decides
solvability of a table with calls (`HTN.Space.ASolvable`) given as advice, reading the initial
state and the goal off the code of an instance description:

    HTN.Space.altMachine_accepts_iff :
      altMachine.Accepts (instSer q) (tblAdv true tbl) ↔
        ASolvable kPush kRet tbl {f | f ∈ regInitR q} {f | f ∈ regGoalR q}

## Configurations

A configuration has five components `[tag, u, A, B, C]`; `A`, `B`, `C` are states written as
serialised lists of canonical numerals, `u` is the name of a row.

* `E`-configurations `[tE, [], S, S', []]` ask *"is `S'` reachable from `S`?"*; they are
  existential, accept when `S` and `S'` carry the same facts, and move by a plain row
  (`[tE, [], S₁, S', []]`) or by a push row `u` to a `G`-configuration `[tG, u, S₁, T, S']`, the
  state `T` in which the callee returns being guessed.
* `G`-configurations are universal: their two successors are the callee `[tE, [], S₁, T, []]` and
  the continuation `[tR, u, T, S', []]`.
* `R`-configurations are existential and move by the return row after `u` to
  `[tE, [], T₂, S', []]`.

The initial configuration is `[tE, [], S₀, S', []]` with `S₀` the initial state of the instance
and `S'` any state containing its goal.  This is exactly the inductive definition of
`HTN.Space.AReach`, read as an alternating computation; no stack is stored.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### The machine -/

/-- The tag of existential reachability questions. -/
def tE : List Bool := [false]

/-- The tag of universal call configurations. -/
def tG : List Bool := [true]

/-- The tag of existential return configurations. -/
def tR : List Bool := [true, true]

/-- A plain step `E → E`. -/
def brPlain (args : Args) : Bool :=
  decide (args.getD 7 [] = tE) && decide (args.getD 2 [] = tE) && decide (args.getD 3 [] = []) &&
    decide (args.getD 6 [] = []) && wfB (args.getD 4 []) (cubeF 0 1 args) &&
    wfB (args.getD 5 []) (cubeF 0 1 args) && decide (args.getD 5 [] = args.getD 10 []) &&
    plainStepB (args.getD 1 []) (args.getD 9 []) (args.getD 4 [])

/-- A push step `E → G`. -/
def brPush (args : Args) : Bool :=
  decide (args.getD 7 [] = tE) && decide (args.getD 2 [] = tG) &&
    decide ((args.getD 3 []).length ≤ (args.getD 1 []).length) &&
    wfB (args.getD 4 []) (cubeF 0 1 args) && wfB (args.getD 5 []) (cubeF 0 1 args) &&
    wfB (args.getD 6 []) (cubeF 0 1 args) && decide (args.getD 6 [] = args.getD 10 []) &&
    pushStepB (args.getD 1 []) (args.getD 3 []) (args.getD 9 []) (args.getD 4 [])

/-- The callee branch `G → E`. -/
def brCallee (args : Args) : Bool :=
  decide (args.getD 7 [] = tG) && decide (args.getD 2 [] = tE) && decide (args.getD 3 [] = []) &&
    decide (args.getD 6 [] = []) && wfB (args.getD 4 []) (cubeF 0 1 args) &&
    wfB (args.getD 5 []) (cubeF 0 1 args) && decide (args.getD 4 [] = args.getD 9 []) &&
    decide (args.getD 5 [] = args.getD 10 [])

/-- The continuation branch `G → R`. -/
def brCont (args : Args) : Bool :=
  decide (args.getD 7 [] = tG) && decide (args.getD 2 [] = tR) &&
    decide ((args.getD 3 []).length ≤ (args.getD 1 []).length) &&
    decide (args.getD 3 [] = args.getD 8 []) && decide (args.getD 6 [] = []) &&
    wfB (args.getD 4 []) (cubeF 0 1 args) && wfB (args.getD 5 []) (cubeF 0 1 args) &&
    decide (args.getD 4 [] = args.getD 10 []) && decide (args.getD 5 [] = args.getD 11 [])

/-- A return step `R → E`. -/
def brRet (args : Args) : Bool :=
  decide (args.getD 7 [] = tR) && decide (args.getD 2 [] = tE) && decide (args.getD 3 [] = []) &&
    decide (args.getD 6 [] = []) && wfB (args.getD 4 []) (cubeF 0 1 args) &&
    wfB (args.getD 5 []) (cubeF 0 1 args) && decide (args.getD 5 [] = args.getD 10 []) &&
    retStepB (args.getD 1 []) (args.getD 8 []) (args.getD 9 []) (args.getD 4 [])

/-! ### Closure lemmas for the atoms -/

theorem cb_eqc (i : ℕ) (t : List Bool) : CobhamB fun args : Args => decide (args.getD i [] = t) :=
  (cobhamB_eqStr (Cobham.proj i) (cobham_const t)).of_eq fun args => by simp [proj]

theorem cb_eq (i j : ℕ) : CobhamB fun args : Args => decide (args.getD i [] = args.getD j []) :=
  (cobhamB_eqStr (Cobham.proj i) (Cobham.proj j)).of_eq fun args => by simp [proj]

theorem cb_le (i j : ℕ) :
    CobhamB fun args : Args => decide ((args.getD i []).length ≤ (args.getD j []).length) :=
  (cobhamB_lenLE (Cobham.proj i) (Cobham.proj j)).of_eq fun args => by simp [proj]

theorem cb_wf (i : ℕ) : CobhamB fun args : Args => wfB (args.getD i []) (cubeF 0 1 args) :=
  (cobhamB_wfB (Cobham.proj i) (cobham_cubeF 0 1)).of_eq fun args => by simp [proj]

theorem cobhamB_brPlain : CobhamB brPlain :=
  (((((((cb_eqc 7 tE).and (cb_eqc 2 tE)).and (cb_eqc 3 [])).and (cb_eqc 6 [])).and
    (cb_wf 4)).and (cb_wf 5)).and (cb_eq 5 10)).and
    (cobhamB_plainStepB (Cobham.proj 1) (Cobham.proj 9) (Cobham.proj 4)) |>.of_eq
    fun args => by simp [brPlain, proj]

theorem cobhamB_brPush : CobhamB brPush :=
  (((((((cb_eqc 7 tE).and (cb_eqc 2 tG)).and (cb_le 3 1)).and (cb_wf 4)).and
    (cb_wf 5)).and (cb_wf 6)).and (cb_eq 6 10)).and
    (cobhamB_pushStepB (Cobham.proj 1) (Cobham.proj 3) (Cobham.proj 9) (Cobham.proj 4)) |>.of_eq
    fun args => by simp [brPush, proj]

theorem cobhamB_brCallee : CobhamB brCallee :=
  (((((((cb_eqc 7 tG).and (cb_eqc 2 tE)).and (cb_eqc 3 [])).and (cb_eqc 6 [])).and
    (cb_wf 4)).and (cb_wf 5)).and (cb_eq 4 9)).and (cb_eq 5 10) |>.of_eq
    fun args => by simp [brCallee]

theorem cobhamB_brCont : CobhamB brCont :=
  ((((((((cb_eqc 7 tG).and (cb_eqc 2 tR)).and (cb_le 3 1)).and (cb_eq 3 8)).and
    (cb_eqc 6 [])).and (cb_wf 4)).and (cb_wf 5)).and (cb_eq 4 10)).and (cb_eq 5 11) |>.of_eq
    fun args => by simp [brCont]

theorem cobhamB_brRet : CobhamB brRet :=
  (((((((cb_eqc 7 tR).and (cb_eqc 2 tE)).and (cb_eqc 3 [])).and (cb_eqc 6 [])).and
    (cb_wf 4)).and (cb_wf 5)).and (cb_eq 5 10)).and
    (cobhamB_retStepB (Cobham.proj 1) (Cobham.proj 8) (Cobham.proj 9) (Cobham.proj 4)) |>.of_eq
    fun args => by simp [brRet, proj]

/-! ### Length bounds -/

theorem cubeF_cons (x a : List Bool) (rest : Args) :
    cubeF 0 1 (x :: a :: rest) = cubeF 0 1 [x, a] := by
  simp [cubeF, padF]

theorem length_le_of_wfB {X bnd : List Bool} (h : wfB X bnd = true) : X.length ≤ bnd.length := by
  obtain ⟨S, -, -, hlen⟩ := wfB_iff.1 h
  exact hlen

theorem cube_le_bound (x a : List Bool) :
    (cubeF 0 1 [x, a]).length ≤ ((Polynomial.X + 2) ^ 3 : Polynomial ℕ).eval (x.length + a.length) := by
  rw [length_cubeF]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  exact Nat.pow_le_pow_left (by omega) 3

theorem small_le_bound (x a : List Bool) {w : List Bool} (h : w.length ≤ 2 ∨ w.length ≤ a.length) :
    w.length ≤ ((Polynomial.X + 2) ^ 3 : Polynomial ℕ).eval (x.length + a.length) := by
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  have h1 : x.length + a.length + 2 ≤ (x.length + a.length + 2) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  omega

/-- **The alternating machine.** -/
noncomputable def altMachine : AltSpace where
  k := 5
  initB := fun args =>
    decide (args.getD 2 [] = tE) && decide (args.getD 3 [] = []) && decide (args.getD 6 [] = []) &&
      wfB (args.getD 4 []) (cubeF 0 1 args) && wfB (args.getD 5 []) (cubeF 0 1 args) &&
      initCoreR (args.getD 4 []) (args.getD 0 []) &&
      accCoreR (args.getD 5 []) (args.getD 0 []) (args.getD 1 [])
  accB := fun args =>
    decide (args.getD 2 [] = tE) && subEntB (args.getD 4 []) (args.getD 5 []) &&
      subEntB (args.getD 5 []) (args.getD 4 [])
  univB := fun args => decide (args.getD 2 [] = tG)
  stepB := fun args => brPlain args || brPush args || brCallee args || brCont args || brRet args
  cobham_initB :=
    ((((((cb_eqc 2 tE).and (cb_eqc 3 [])).and (cb_eqc 6 [])).and (cb_wf 4)).and (cb_wf 5)).and
      (cobhamB_initCoreR (Cobham.proj 4) (Cobham.proj 0))).and
      (cobhamB_accCoreR (Cobham.proj 5) (Cobham.proj 0) (Cobham.proj 1)) |>.of_eq
      fun args => by simp [proj]
  cobham_accB :=
    ((cb_eqc 2 tE).and (cobhamB_subEntB (Cobham.proj 4) (Cobham.proj 5))).and
      (cobhamB_subEntB (Cobham.proj 5) (Cobham.proj 4)) |>.of_eq fun args => by simp [proj]
  cobham_univB := cb_eqc 2 tG
  cobham_stepB :=
    (((cobhamB_brPlain.or cobhamB_brPush).or cobhamB_brCallee).or cobhamB_brCont).or
      cobhamB_brRet |>.of_eq fun _ => rfl
  bound := (Polynomial.X + 2) ^ 3
  initB_length := by
    intro x a c hc h w hw
    match c, hc with
    | [tg, u, A, B, C], _ =>
      simp only [List.getD_cons_succ, List.getD_cons_zero, Bool.and_eq_true,
        decide_eq_true_eq, cubeF_cons] at h
      obtain ⟨⟨⟨⟨⟨⟨htg, hu⟩, hC⟩, hA⟩, hB⟩, -⟩, -⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact small_le_bound x a (Or.inl (by rw [htg]; simp [tE]))
      · exact small_le_bound x a (Or.inl (by rw [hu]; simp))
      · exact (length_le_of_wfB hA).trans (cube_le_bound x a)
      · exact (length_le_of_wfB hB).trans (cube_le_bound x a)
      · exact small_le_bound x a (Or.inl (by rw [hC]; simp))
  stepB_length := by
    intro x a c' c hc' hc h w hw
    match c', hc', c, hc with
    | [tg', u', A', B', C'], _, [tg, u, A, B, C], _ =>
      simp only [List.cons_append, List.nil_append] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have hwf : ∀ X : List Bool, wfB X (cubeF 0 1 (x :: a :: tg' :: u' :: A' :: B' :: C' ::
          tg :: u :: A :: B :: C :: [])) = true →
          X.length ≤ ((Polynomial.X + 2) ^ 3 : Polynomial ℕ).eval (x.length + a.length) := by
        intro X hX
        rw [cubeF_cons] at hX
        exact (length_le_of_wfB hX).trans (cube_le_bound x a)
      have htag : ∀ t : List Bool, t = tE ∨ t = tG ∨ t = tR →
          t.length ≤ ((Polynomial.X + 2) ^ 3 : Polynomial ℕ).eval (x.length + a.length) := by
        rintro t (rfl | rfl | rfl) <;> exact small_le_bound x a (Or.inl (by simp [tE, tG, tR]))
      have hnil : ∀ t : List Bool, t = [] →
          t.length ≤ ((Polynomial.X + 2) ^ 3 : Polynomial ℕ).eval (x.length + a.length) := by
        rintro t rfl; simp
      have hua : ∀ t : List Bool, t.length ≤ a.length →
          t.length ≤ ((Polynomial.X + 2) ^ 3 : Polynomial ℕ).eval (x.length + a.length) :=
        fun t ht => small_le_bound x a (Or.inr ht)
      simp only [Bool.or_eq_true] at h
      rcases h with (((h | h) | h) | h) | h
      · simp only [brPlain, List.getD_cons_succ, List.getD_cons_zero, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h6⟩, h4⟩, h5⟩, -⟩, -⟩ := h
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact htag _ (Or.inl h2)
        · exact hnil _ h3
        · exact hwf _ h4
        · exact hwf _ h5
        · exact hnil _ h6
      · simp only [brPush, List.getD_cons_succ, List.getD_cons_zero, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩ := h
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact htag _ (Or.inr (Or.inl h2))
        · exact hua _ h3
        · exact hwf _ h4
        · exact hwf _ h5
        · exact hwf _ h6
      · simp only [brCallee, List.getD_cons_succ, List.getD_cons_zero, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h6⟩, h4⟩, h5⟩, -⟩, -⟩ := h
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact htag _ (Or.inl h2)
        · exact hnil _ h3
        · exact hwf _ h4
        · exact hwf _ h5
        · exact hnil _ h6
      · simp only [brCont, List.getD_cons_succ, List.getD_cons_zero, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, -⟩, h6⟩, h4⟩, h5⟩, -⟩, -⟩ := h
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact htag _ (Or.inr (Or.inr h2))
        · exact hua _ h3
        · exact hwf _ h4
        · exact hwf _ h5
        · exact hnil _ h6
      · simp only [brRet, List.getD_cons_succ, List.getD_cons_zero, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h6⟩, h4⟩, h5⟩, -⟩, -⟩ := h
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact htag _ (Or.inl h2)
        · exact hnil _ h3
        · exact hwf _ h4
        · exact hwf _ h5
        · exact hnil _ h6

end Space

end HTN
