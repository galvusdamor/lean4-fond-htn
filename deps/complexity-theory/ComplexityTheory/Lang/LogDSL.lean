import ComplexityTheory.Lang.Logspace
/-!
# A language of logarithmic-space folds

`HTN.Cx.LTerm` is a small functional language over natural numbers with read access to the
input: variables (de Bruijn), literals, the input length, input bits, saturating addition,
truncated subtraction, comparison, conditionals, `let` and bounded **folds**
(`fold n init body` iterates `body` over `i = 0, …, n - 1`, with the accumulator and `i` as its two
newest variables).  Values are saturated at `M = |x| + C`, so every value of a term fits a register
of `O(log |x|)` bits.

`HTN.Cx.LTerm.compile` translates a term into a register program (`HTN.Cx.LStmt`) that computes its
value with values bounded by `2 M + 1` (`HTN.Cx.LTerm.exec_compile`), hence:

* **`HTN.Cx.inL_of_term`** — a language decided by a closed term is in `L`.
-/

namespace HTN

namespace Cx

/-- **Terms** of the fold language. -/
inductive LTerm where
  | var (i : ℕ)
  | lit (c : ℕ)
  | len
  | bit (a : LTerm)
  | add (a b : LTerm)
  | sub (a b : LTerm)
  | lt (a b : LTerm)
  | ite (c a b : LTerm)
  | fold (n init body : LTerm)
  | let_ (a body : LTerm)

namespace LTerm

/-- **The value of a term**, with values saturated at `M`. -/
def eval (x : List Bool) (M : ℕ) : List ℕ → LTerm → ℕ
  | env, .var i => env.getD i 0
  | _, .lit c => c
  | _, .len => x.length
  | env, .bit a => if x.getD (eval x M env a) false then 1 else 0
  | env, .add a b => min (eval x M env a + eval x M env b) M
  | env, .sub a b => eval x M env a - eval x M env b
  | env, .lt a b => if eval x M env a < eval x M env b then 1 else 0
  | env, .ite c a b => if eval x M env c ≠ 0 then eval x M env a else eval x M env b
  | env, .fold n i b =>
      (List.range (eval x M env n)).foldl (fun acc j => eval x M (acc :: j :: env) b) (eval x M env i)
  | env, .let_ a b => eval x M (eval x M env a :: env) b

/-- The largest literal of a term. -/
def maxLit : LTerm → ℕ
  | .var _ => 0
  | .lit c => c
  | .len => 0
  | .bit a => maxLit a
  | .add a b => max (maxLit a) (maxLit b)
  | .sub a b => max (maxLit a) (maxLit b)
  | .lt a b => max (maxLit a) (maxLit b)
  | .ite c a b => max (maxLit c) (max (maxLit a) (maxLit b))
  | .fold n i b => max (maxLit n) (max (maxLit i) (maxLit b))
  | .let_ a b => max (maxLit a) (maxLit b)

/-- **Values are bounded by `M`** when the environment is and `M` exceeds the literals, the input
length and `1`. -/
theorem eval_le {x : List Bool} {M : ℕ} (hx : x.length ≤ M) (h1 : 1 ≤ M) :
    ∀ (t : LTerm) (env : List ℕ), t.maxLit ≤ M → (∀ v ∈ env, v ≤ M) → t.eval x M env ≤ M := by
  intro t
  induction t with
  | var i =>
    intro env _ henv
    simp only [eval]
    rcases Nat.lt_or_ge i env.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact henv _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; omega
  | lit c => intro env h _; simpa [eval, maxLit] using h
  | len => intro env _ _; simpa [eval] using hx
  | bit a _ => intro env _ _; simp only [eval]; split_ifs <;> omega
  | add a b _ _ => intro env _ _; simp only [eval]; omega
  | sub a b iha _ =>
    intro env h henv
    simp only [eval, maxLit] at h ⊢
    have := iha env (by omega) henv; omega
  | lt a b _ _ => intro env _ _; simp only [eval]; split_ifs <;> omega
  | ite c a b _ iha ihb =>
    intro env h henv
    simp only [eval, maxLit] at h ⊢
    split_ifs
    · exact iha env (by omega) henv
    · exact ihb env (by omega) henv
  | fold n i b ihn ihi ihb =>
    intro env h henv
    simp only [eval, maxLit] at h ⊢
    have hi := ihi env (by omega) henv
    have hl : ∀ j ∈ List.range (n.eval x M env), j ≤ M := fun j hj =>
      (List.mem_range.1 hj).le.trans (ihn env (by omega) henv)
    have key : ∀ (l : List ℕ), (∀ j ∈ l, j ≤ M) → ∀ a, a ≤ M →
        l.foldl (fun acc j => eval x M (acc :: j :: env) b) a ≤ M := by
      intro l
      induction l with
      | nil => intro _ a ha; simpa using ha
      | cons j l ih =>
        intro hl a ha
        rw [List.foldl_cons]
        refine ih (fun j' hj' => hl j' (by simp [hj'])) _ (ihb _ (by omega) ?_)
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | rfl | hv
        · exact ha
        · exact hl _ (by simp)
        · exact henv v hv
    exact key _ hl _ hi
  | let_ a b iha ihb =>
    intro env h henv
    simp only [eval, maxLit] at h ⊢
    refine ihb _ (by omega) ?_
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact iha env (by omega) henv
    · exact henv v hv

/-! ### Compilation -/

/-- **The compilation of a term**: the value goes to `dst`, the variables are in the registers
`envR`, `M` is in `mreg`, and the registers from `base` on are scratch. -/
def compile (mreg : ℕ) : LTerm → ℕ → List ℕ → ℕ → LStmt
  | .var i, dst, envR, _ =>
      match envR[i]? with
      | some r => .assign dst (.reg r)
      | none => .assign dst (.lit 0)
  | .lit c, dst, _, _ => .assign dst (.lit c)
  | .len, dst, _, _ => .assign dst .len
  | .bit a, dst, envR, base => .seq (compile mreg a base envR (base + 1)) (.assign dst (.bit (.reg base)))
  | .add a b, dst, envR, base =>
      .seq (.seq (compile mreg a base envR (base + 2)) (compile mreg b (base + 1) envR (base + 2)))
        (.seq (.assign dst (.add (.reg base) (.reg (base + 1))))
          (.ite (.lt (.reg dst) (.reg mreg)) (.assign dst (.reg dst)) (.assign dst (.reg mreg))))
  | .sub a b, dst, envR, base =>
      .seq (.seq (compile mreg a base envR (base + 2)) (compile mreg b (base + 1) envR (base + 2)))
        (.assign dst (.sub (.reg base) (.reg (base + 1))))
  | .lt a b, dst, envR, base =>
      .seq (.seq (compile mreg a base envR (base + 2)) (compile mreg b (base + 1) envR (base + 2)))
        (.assign dst (.lt (.reg base) (.reg (base + 1))))
  | .ite c a b, dst, envR, base =>
      .seq (compile mreg c base envR (base + 1))
        (.ite (.reg base) (compile mreg a dst envR (base + 1)) (compile mreg b dst envR (base + 1)))
  | .fold n i b, dst, envR, base =>
      .seq (.seq (compile mreg n base envR (base + 4)) (compile mreg i (base + 1) envR (base + 4)))
        (.seq (.assign (base + 2) (.lit 0))
          (.seq (.while (.lt (.reg (base + 2)) (.reg base))
            (.seq (compile mreg b (base + 3) ((base + 1) :: (base + 2) :: envR) (base + 4))
              (.seq (.assign (base + 1) (.reg (base + 3)))
                (.assign (base + 2) (.add (.reg (base + 2)) (.lit 1))))))
            (.assign dst (.reg (base + 1)))))
  | .let_ a b, dst, envR, base =>
      .seq (compile mreg a base envR (base + 1)) (compile mreg b dst (base :: envR) (base + 1))

/-! ### Correctness of the compilation -/

section Correct

variable {x : List Bool} {M mreg : ℕ}

theorem map_congr_frame {envR : List ℕ} {R R' : ℕ → ℕ} {base : ℕ} (henv : ∀ r ∈ envR, r < base)
    (h : ∀ r, r < base → R' r = R r) : envR.map R' = envR.map R :=
  List.map_congr_left fun r hr => h r (henv r hr)

/-- **The compiled program computes the value of the term**, within the bound `2 M + 1`, and
leaves the registers below `base` other than `dst` unchanged. -/
theorem exec_compile (hx : x.length ≤ M) (h1 : 1 ≤ M) :
    ∀ (t : LTerm) (dst : ℕ) (envR : List ℕ) (base : ℕ) (R : ℕ → ℕ),
      t.maxLit ≤ M → dst < base → mreg < base → dst ≠ mreg → (∀ r ∈ envR, r < base) → R mreg = M →
      (∀ r ∈ envR, R r ≤ M) →
      ∃ R', ExecB x (2 * M + 1) (compile mreg t dst envR base) R R' ∧
        R' dst = t.eval x M (envR.map R) ∧ ∀ r, r < base → r ≠ dst → R' r = R r := by
  intro t
  induction t with
  | var i =>
    intro dst envR base R _ hdst _ _ henv _ hval
    cases hi : envR[i]? with
    | some r =>
      have hr : r ∈ envR := List.mem_of_getElem? hi
      refine ⟨_, by simp only [compile, hi]; exact .assign (by have := hval r hr; simp [LExp.eval]; omega),
        ?_, fun r' _ hne => Function.update_of_ne hne _ _⟩
      simp only [Function.update_self, LExp.eval, eval]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hi]
      rfl
    | none =>
      refine ⟨_, by simp only [compile, hi]; exact .assign (by simp [LExp.eval]),
        ?_, fun r' _ hne => Function.update_of_ne hne _ _⟩
      simp only [Function.update_self, LExp.eval, eval]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hi]
      rfl
  | lit c =>
    intro dst envR base R hlit _ _ _ _ _ _
    refine ⟨_, .assign (by simp only [LExp.eval]; simp [maxLit] at hlit; omega), by simp [LExp.eval, eval],
      fun r' _ hne => Function.update_of_ne hne _ _⟩
  | len =>
    intro dst envR base R _ _ _ _ _ _ _
    exact ⟨_, .assign (by simp only [LExp.eval]; omega), by simp [LExp.eval, eval],
      fun r' _ hne => Function.update_of_ne hne _ _⟩
  | bit a iha =>
    intro dst envR base R hlit hdst hm hdm henv hM hval
    obtain ⟨R₁, h₁, e₁, f₁⟩ := iha base envR (base + 1) R (by simpa [maxLit] using hlit) (by omega)
      (by omega) (by omega) (fun r hr => by have := henv r hr; omega) hM hval
    refine ⟨_, .seq h₁ (.assign (by simp only [LExp.eval]; split_ifs <;> omega)), ?_,
      fun r hr hne => ?_⟩
    · simp only [Function.update_self, LExp.eval, eval, e₁]
    · rw [Function.update_of_ne hne]; exact f₁ r (by omega) (by omega)
  | add a b iha ihb =>
    intro dst envR base R hlit hdst hm hdm henv hM hval
    simp only [maxLit] at hlit
    obtain ⟨R₁, h₁, e₁, f₁⟩ := iha base envR (base + 2) R (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM hval
    have hM₁ : R₁ mreg = M := by rw [f₁ mreg (by omega) (by omega), hM]
    have hv₁ : ∀ r ∈ envR, R₁ r ≤ M := fun r hr => by
      rw [f₁ r (by have := henv r hr; omega) (by have := henv r hr; omega)]; exact hval r hr
    obtain ⟨R₂, h₂, e₂, f₂⟩ := ihb (base + 1) envR (base + 2) R₁ (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM₁ hv₁
    have hmap₁ : envR.map R₁ = envR.map R := map_congr_frame (base := base) henv
      (fun r hr => f₁ r (by omega) (by omega))
    have hA : R₂ base = a.eval x M (envR.map R) := by rw [f₂ base (by omega) (by omega), e₁]
    have hB : R₂ (base + 1) = b.eval x M (envR.map R) := by rw [e₂, hmap₁]
    have hAle := eval_le hx h1 a (envR.map R) (by omega) (by simpa using hval)
    have hBle := eval_le hx h1 b (envR.map R) (by omega) (by simpa using hval)
    set R₃ := Function.update R₂ dst (R₂ base + R₂ (base + 1))
    have hM₃ : R₃ mreg = M := by
      simp only [R₃]
      rw [Function.update_of_ne (show mreg ≠ dst by omega), f₂ mreg (by omega) (by omega), hM₁]
    have hA' : R₂ base ≤ M := hA ▸ hAle
    have hB' : R₂ (base + 1) ≤ M := hB ▸ hBle
    have hasg : ExecB x (2 * M + 1) (.assign dst (.add (.reg base) (.reg (base + 1)))) R₂ R₃ :=
      .assign (by simp only [LExp.eval]; omega)
    by_cases hlt : R₃ dst < M
    · refine ⟨R₃, .seq (.seq h₁ h₂) (.seq hasg (.iteT (by simp [LExp.eval, hM₃, hlt])
        ?_)), ?_, ?_⟩
      · have := ExecB.assign (x := x) (B := 2 * M + 1) (r := dst) (e := .reg dst) (R := R₃)
          (by simp only [LExp.eval]; omega)
        simpa [LExp.eval] using this
      · simp only [R₃, Function.update_self] at hlt ⊢
        simp only [eval, hA, hB] at hlt ⊢
        omega
      · intro r hr hne
        simp only [R₃]; rw [Function.update_of_ne hne, f₂ r (by omega) (by omega),
          f₁ r (by omega) (by omega)]
    · refine ⟨Function.update R₃ dst M, .seq (.seq h₁ h₂) (.seq hasg (.iteF
        (by simp [LExp.eval, hM₃, hlt]) ?_)), ?_, ?_⟩
      · have := ExecB.assign (x := x) (B := 2 * M + 1) (r := dst) (e := .reg mreg) (R := R₃)
          (by simp only [LExp.eval]; omega)
        simpa [LExp.eval, hM₃] using this
      · simp only [R₃, Function.update_self] at hlt ⊢
        simp only [eval, hA, hB] at hlt ⊢
        omega
      · intro r hr hne
        simp only [R₃]; rw [Function.update_of_ne hne, Function.update_of_ne hne,
          f₂ r (by omega) (by omega), f₁ r (by omega) (by omega)]
  | sub a b iha ihb =>
    intro dst envR base R hlit hdst hm hdm henv hM hval
    simp only [maxLit] at hlit
    obtain ⟨R₁, h₁, e₁, f₁⟩ := iha base envR (base + 2) R (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM hval
    have hM₁ : R₁ mreg = M := by rw [f₁ mreg (by omega) (by omega), hM]
    have hv₁ : ∀ r ∈ envR, R₁ r ≤ M := fun r hr => by
      rw [f₁ r (by have := henv r hr; omega) (by have := henv r hr; omega)]; exact hval r hr
    obtain ⟨R₂, h₂, e₂, f₂⟩ := ihb (base + 1) envR (base + 2) R₁ (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM₁ hv₁
    have hmap₁ : envR.map R₁ = envR.map R := map_congr_frame (base := base) henv
      (fun r hr => f₁ r (by omega) (by omega))
    have hA : R₂ base = a.eval x M (envR.map R) := by rw [f₂ base (by omega) (by omega), e₁]
    have hB : R₂ (base + 1) = b.eval x M (envR.map R) := by rw [e₂, hmap₁]
    have hAle := eval_le hx h1 a (envR.map R) (by omega) (by simpa using hval)
    refine ⟨_, .seq (.seq h₁ h₂) (.assign (by simp only [LExp.eval]; omega)), ?_, ?_⟩
    · simp [LExp.eval, eval, hA, hB]
    · intro r hr hne
      rw [Function.update_of_ne hne, f₂ r (by omega) (by omega), f₁ r (by omega) (by omega)]
  | lt a b iha ihb =>
    intro dst envR base R hlit hdst hm hdm henv hM hval
    simp only [maxLit] at hlit
    obtain ⟨R₁, h₁, e₁, f₁⟩ := iha base envR (base + 2) R (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM hval
    have hM₁ : R₁ mreg = M := by rw [f₁ mreg (by omega) (by omega), hM]
    have hv₁ : ∀ r ∈ envR, R₁ r ≤ M := fun r hr => by
      rw [f₁ r (by have := henv r hr; omega) (by have := henv r hr; omega)]; exact hval r hr
    obtain ⟨R₂, h₂, e₂, f₂⟩ := ihb (base + 1) envR (base + 2) R₁ (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM₁ hv₁
    have hmap₁ : envR.map R₁ = envR.map R := map_congr_frame (base := base) henv
      (fun r hr => f₁ r (by omega) (by omega))
    have hA : R₂ base = a.eval x M (envR.map R) := by rw [f₂ base (by omega) (by omega), e₁]
    have hB : R₂ (base + 1) = b.eval x M (envR.map R) := by rw [e₂, hmap₁]
    refine ⟨_, .seq (.seq h₁ h₂) (.assign (by simp only [LExp.eval]; split_ifs <;> omega)), ?_, ?_⟩
    · simp [LExp.eval, eval, hA, hB]
    · intro r hr hne
      rw [Function.update_of_ne hne, f₂ r (by omega) (by omega), f₁ r (by omega) (by omega)]
  | ite c a b ihc iha ihb =>
    intro dst envR base R hlit hdst hm hdm henv hM hval
    simp only [maxLit] at hlit
    obtain ⟨R₁, h₁, e₁, f₁⟩ := ihc base envR (base + 1) R (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM hval
    have hM₁ : R₁ mreg = M := by rw [f₁ mreg (by omega) (by omega), hM]
    have hv₁ : ∀ r ∈ envR, R₁ r ≤ M := fun r hr => by
      rw [f₁ r (by have := henv r hr; omega) (by have := henv r hr; omega)]; exact hval r hr
    have hmap₁ : envR.map R₁ = envR.map R := map_congr_frame (base := base) henv
      (fun r hr => f₁ r (by omega) (by omega))
    by_cases hc : c.eval x M (envR.map R) ≠ 0
    · obtain ⟨R₂, h₂, e₂, f₂⟩ := iha dst envR (base + 1) R₁ (by omega) (by omega) (by omega)
        (by omega) (fun r hr => by have := henv r hr; omega) hM₁ hv₁
      refine ⟨R₂, .seq h₁ (.iteT (by simp [LExp.eval, e₁, hc]) h₂), ?_, fun r hr hne => ?_⟩
      · rw [e₂, hmap₁]; simp [eval, hc]
      · rw [f₂ r (by omega) hne, f₁ r (by omega) (by omega)]
    · obtain ⟨R₂, h₂, e₂, f₂⟩ := ihb dst envR (base + 1) R₁ (by omega) (by omega) (by omega)
        (by omega) (fun r hr => by have := henv r hr; omega) hM₁ hv₁
      refine ⟨R₂, .seq h₁ (.iteF (by simp only [LExp.eval, e₁]; omega) h₂), ?_, fun r hr hne => ?_⟩
      · rw [e₂, hmap₁]; simp only [eval]; rw [if_neg hc]
      · rw [f₂ r (by omega) hne, f₁ r (by omega) (by omega)]
  | fold n i b ihn ihi ihb =>
    intro dst envR base R hlit hdst hm hdm henv hM hval
    simp only [maxLit] at hlit
    obtain ⟨R₁, h₁, e₁, f₁⟩ := ihn base envR (base + 4) R (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM hval
    have hM₁ : R₁ mreg = M := by rw [f₁ mreg (by omega) (by omega), hM]
    have hv₁ : ∀ r ∈ envR, R₁ r ≤ M := fun r hr => by
      rw [f₁ r (by have := henv r hr; omega) (by have := henv r hr; omega)]; exact hval r hr
    have hmap₁ : envR.map R₁ = envR.map R := map_congr_frame (base := base) henv
      (fun r hr => f₁ r (by omega) (by omega))
    obtain ⟨R₂, h₂, e₂, f₂⟩ := ihi (base + 1) envR (base + 4) R₁ (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM₁ hv₁
    set env := envR.map R with henv_def
    have hvenv : ∀ v ∈ env, v ≤ M := by simpa [env] using hval
    set nn := n.eval x M env with hnn_def
    set a0 := i.eval x M env with ha0_def
    set f : ℕ → ℕ → ℕ := fun acc j => b.eval x M (acc :: j :: env) with hf_def
    have hnn : R₂ base = nn := by rw [f₂ base (by omega) (by omega), e₁]
    have ha0 : R₂ (base + 1) = a0 := by rw [e₂, hmap₁]
    have hnnle : nn ≤ M := eval_le hx h1 n env (by omega) hvenv
    have ha0le : a0 ≤ M := eval_le hx h1 i env (by omega) hvenv
    have hM₂ : R₂ mreg = M := by rw [f₂ mreg (by omega) (by omega), hM₁]
    have accle : ∀ j, j ≤ nn → (List.range j).foldl f a0 ≤ M := by
      intro j
      induction j with
      | zero => intro _; simpa using ha0le
      | succ j ih =>
        intro hj
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        refine eval_le hx h1 b _ (by omega) ?_
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | rfl | hv
        · exact ih (by omega)
        · omega
        · exact hvenv v hv
    set body : LStmt := .seq (compile mreg b (base + 3) ((base + 1) :: (base + 2) :: envR) (base + 4))
      (.seq (.assign (base + 1) (.reg (base + 3)))
        (.assign (base + 2) (.add (.reg (base + 2)) (.lit 1)))) with hbody
    have loop : ∀ k (S : ℕ → ℕ), nn - S (base + 2) = k → S (base + 2) ≤ nn → S base = nn →
        S mreg = M → (∀ r, r < base → S r = R r) →
        S (base + 1) = (List.range (S (base + 2))).foldl f a0 →
        ∃ S', ExecB x (2 * M + 1) (.while (.lt (.reg (base + 2)) (.reg base)) body) S S' ∧
          S' (base + 1) = (List.range nn).foldl f a0 ∧ ∀ r, r < base → S' r = R r := by
      intro k
      induction k with
      | zero =>
        intro S hk hj hb hSM hfr hacc
        have hjn : S (base + 2) = nn := by omega
        refine ⟨S, .whileF (by simp [LExp.eval, hjn, hb]), by rw [hacc, hjn], hfr⟩
      | succ k ih =>
        intro S hk hj hb hSM hfr hacc
        have hjlt : S (base + 2) < nn := by omega
        have hmapS : envR.map S = env := map_congr_frame (base := base) henv hfr
        obtain ⟨S₁, hs₁, es₁, fs₁⟩ := ihb (base + 3) ((base + 1) :: (base + 2) :: envR) (base + 4) S
          (by omega) (by omega) (by omega) (by omega)
          (fun r hr => by
            simp only [List.mem_cons] at hr
            rcases hr with rfl | rfl | hr
            · omega
            · omega
            · have := henv r hr; omega) hSM
          (fun r hr => by
            simp only [List.mem_cons] at hr
            rcases hr with rfl | rfl | hr
            · rw [hacc]; exact accle _ hjlt.le
            · omega
            · rw [hfr r (henv r hr)]; exact hval r hr)
        have hstep : f ((List.range (S (base + 2))).foldl f a0) (S (base + 2)) =
            (List.range (S (base + 2) + 1)).foldl f a0 := by
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hv₃ : S₁ (base + 3) = (List.range (S (base + 2) + 1)).foldl f a0 := by
          rw [es₁, List.map_cons, List.map_cons, hmapS, hacc, ← hstep]
        have hv₃le : S₁ (base + 3) ≤ M := by rw [hv₃]; exact accle _ (by omega)
        have hj₁ : S₁ (base + 2) = S (base + 2) := fs₁ (base + 2) (by omega) (by omega)
        have hexec : ExecB x (2 * M + 1) body S
            (Function.update (Function.update S₁ (base + 1) (S₁ (base + 3))) (base + 2)
              (S (base + 2) + 1)) := by
          have h2 := ExecB.assign (x := x) (B := 2 * M + 1) (r := base + 2)
            (e := .add (.reg (base + 2)) (.lit 1))
            (R := Function.update S₁ (base + 1) (S₁ (base + 3)))
            (by simp only [LExp.eval]; rw [Function.update_of_ne (by omega), hj₁]; omega)
          have h2' : LExp.eval x (Function.update S₁ (base + 1) (S₁ (base + 3)))
              (.add (.reg (base + 2)) (.lit 1)) = S (base + 2) + 1 := by
            simp only [LExp.eval]; rw [Function.update_of_ne (by omega), hj₁]
          rw [h2'] at h2
          exact .seq hs₁ (.seq (.assign (by simp only [LExp.eval]; omega)) h2)
        obtain ⟨S', hS', e', f'⟩ := ih
          (Function.update (Function.update S₁ (base + 1) (S₁ (base + 3))) (base + 2)
            (S (base + 2) + 1))
          (by rw [Function.update_self]; omega) (by rw [Function.update_self]; omega)
          (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            fs₁ base (by omega) (by omega), hb])
          (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            fs₁ mreg (by omega) (by omega), hSM])
          (fun r hr => by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            fs₁ r (by omega) (by omega), hfr r hr])
          (by rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self, hv₃])
        exact ⟨S', .whileT (by simp only [LExp.eval, hb]; simp [hjlt]) hexec hS', e', f'⟩
    set R₃ := Function.update R₂ (base + 2) 0 with hR₃
    obtain ⟨R₄, h₄, e₄, f₄⟩ := loop nn R₃ (by simp [hR₃]) (by simp [hR₃])
      (by rw [hR₃, Function.update_of_ne (by omega), hnn])
      (by rw [hR₃, Function.update_of_ne (by omega), hM₂])
      (fun r hr => by rw [hR₃, Function.update_of_ne (by omega), f₂ r (by omega) (by omega),
        f₁ r (by omega) (by omega)])
      (by rw [hR₃, Function.update_self, Function.update_of_ne (by omega), ha0]; simp)
    have hfoldle : (List.range nn).foldl f a0 ≤ M := accle nn le_rfl
    refine ⟨Function.update R₄ dst (R₄ (base + 1)),
      .seq (.seq h₁ h₂) (.seq (.assign (by simp [LExp.eval]))
        (.seq h₄ (.assign (by simp only [LExp.eval]; omega)))), ?_, fun r hr hne => ?_⟩
    · rw [Function.update_self, e₄]; rfl
    · rw [Function.update_of_ne hne, f₄ r hr]
  | let_ a b iha ihb =>
    intro dst envR base R hlit hdst hm hdm henv hM hval
    simp only [maxLit] at hlit
    obtain ⟨R₁, h₁, e₁, f₁⟩ := iha base envR (base + 1) R (by omega) (by omega) (by omega)
      (by omega) (fun r hr => by have := henv r hr; omega) hM hval
    have hM₁ : R₁ mreg = M := by rw [f₁ mreg (by omega) (by omega), hM]
    have hmap₁ : envR.map R₁ = envR.map R := map_congr_frame (base := base) henv
      (fun r hr => f₁ r (by omega) (by omega))
    have hAle := eval_le hx h1 a (envR.map R) (by omega) (by simpa using hval)
    obtain ⟨R₂, h₂, e₂, f₂⟩ := ihb dst (base :: envR) (base + 1) R₁ (by omega) (by omega) (by omega) hdm
      (fun r hr => by
        simp only [List.mem_cons] at hr; rcases hr with rfl | hr
        · omega
        · have := henv r hr; omega) hM₁ (fun r hr => by
        simp only [List.mem_cons] at hr; rcases hr with rfl | hr
        · rw [e₁]; exact hAle
        · rw [f₁ r (by have := henv r hr; omega) (by have := henv r hr; omega)]; exact hval r hr)
    refine ⟨R₂, .seq h₁ h₂, ?_, fun r hr hne => ?_⟩
    · rw [e₂, List.map_cons, e₁, hmap₁]; rfl
    · rw [f₂ r (by omega) hne, f₁ r (by omega) (by omega)]

end Correct

/-- **A language decided by a closed term is in `L`.** -/
theorem _root_.HTN.Cx.inL_of_term {Lg : Language} (t : LTerm) (C : ℕ) (hC : t.maxLit + 1 ≤ C)
    (hL : ∀ x, Lg x ↔ t.eval x (x.length + C) [] ≠ 0) : L Lg := by
  refine ⟨.seq (.assign 1 (.add .len (.lit C))) (compile 1 t 0 [] 2),
    2 * (Polynomial.X + Polynomial.C C) + 1, fun x => ?_⟩
  set M := x.length + C
  have hB : (2 * (Polynomial.X + Polynomial.C C) + 1 : Polynomial ℕ).eval x.length = 2 * M + 1 := by
    simp [M]
  rw [hB]
  set R₁ : ℕ → ℕ := Function.update (fun _ => 0) 1 M
  have hR₁ : R₁ 1 = M := by simp [R₁]
  obtain ⟨R', h, e, -⟩ := exec_compile (x := x) (M := M) (mreg := 1) (by omega) (by omega) t 0 []
    2 R₁ (by omega) (by omega) (by omega) (by omega) (by simp) hR₁ (by simp)
  refine ⟨R', .seq ?_ h, ?_⟩
  · have := ExecB.assign (x := x) (B := 2 * M + 1) (r := 1) (e := .add .len (.lit C))
      (R := fun _ => 0) (by simp [LExp.eval, M]; omega)
    simpa [LExp.eval, R₁, M] using this
  · rw [hL x, e]; rfl

end LTerm

end Cx

end HTN
