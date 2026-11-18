import ComplexityTheory.Lang.LogDSL
/-!
# Programming in the fold language

Shifting of variables (`HTN.Cx.LTerm.shift`, so that a term can be used under binders), and
derived constructs with their meaning: Boolean connectives, equality, bounded quantifiers
(`forallB`, `existsB`) and the search for the least index with a property (`firstB`).
Booleans are `0`/`1`.
-/

namespace HTN

namespace Cx

namespace LTerm

/-- Shift the variables `≥ c` by `n`. -/
def shift (c n : ℕ) : LTerm → LTerm
  | .var i => if c ≤ i then .var (i + n) else .var i
  | .lit k => .lit k
  | .len => .len
  | .bit a => .bit (shift c n a)
  | .add a b => .add (shift c n a) (shift c n b)
  | .sub a b => .sub (shift c n a) (shift c n b)
  | .lt a b => .lt (shift c n a) (shift c n b)
  | .ite a b d => .ite (shift c n a) (shift c n b) (shift c n d)
  | .fold a b d => .fold (shift c n a) (shift c n b) (shift (c + 2) n d)
  | .let_ a b => .let_ (shift c n a) (shift (c + 1) n b)

theorem maxLit_shift (c n : ℕ) : ∀ t : LTerm, (shift c n t).maxLit = t.maxLit := by
  intro t
  induction t generalizing c with
  | var i => simp only [shift]; split_ifs <;> rfl
  | lit _ => rfl
  | len => rfl
  | bit a ih => simp [shift, maxLit, ih]
  | add a b iha ihb => simp [shift, maxLit, iha, ihb]
  | sub a b iha ihb => simp [shift, maxLit, iha, ihb]
  | lt a b iha ihb => simp [shift, maxLit, iha, ihb]
  | ite a b d iha ihb ihd => simp [shift, maxLit, iha, ihb, ihd]
  | fold a b d iha ihb ihd => simp [shift, maxLit, iha, ihb, ihd]
  | let_ a b iha ihb => simp [shift, maxLit, iha, ihb]

/-- **Shifting inserts variables.** -/
theorem eval_shift {x : List Bool} {M : ℕ} : ∀ (t : LTerm) (pre ins env : List ℕ),
    eval x M (pre ++ (ins ++ env)) (shift pre.length ins.length t) = eval x M (pre ++ env) t := by
  intro t
  induction t with
  | var i =>
    intro pre ins env
    simp only [shift, eval, List.getD_eq_getElem?_getD]
    by_cases h : pre.length ≤ i
    · rw [if_pos h]
      simp only [eval, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_append_right h]
      congr 2; omega
    · rw [if_neg h]
      simp only [eval, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  | lit _ => intro _ _ _; rfl
  | len => intro _ _ _; rfl
  | bit a ih => intro pre ins env; simp only [shift, eval, ih]
  | add a b iha ihb => intro pre ins env; simp only [shift, eval, iha, ihb]
  | sub a b iha ihb => intro pre ins env; simp only [shift, eval, iha, ihb]
  | lt a b iha ihb => intro pre ins env; simp only [shift, eval, iha, ihb]
  | ite a b d iha ihb ihd => intro pre ins env; simp only [shift, eval, iha, ihb, ihd]
  | fold a b d iha ihb ihd =>
    intro pre ins env
    simp only [shift, eval, iha, ihb]
    congr 1
    funext acc j
    have := ihd (acc :: j :: pre) ins env
    simpa using this
  | let_ a b iha ihb =>
    intro pre ins env
    simp only [shift, eval, iha]
    have := ihb (eval x M (pre ++ env) a :: pre) ins env
    simpa using this

/-- Lifting a term over `n` new variables. -/
def lift (n : ℕ) (t : LTerm) : LTerm := shift 0 n t

theorem eval_lift {x : List Bool} {M : ℕ} (t : LTerm) (ins env : List ℕ) :
    eval x M (ins ++ env) (lift ins.length t) = eval x M env t := by
  have := eval_shift (x := x) (M := M) t [] ins env
  simpa [lift] using this

theorem eval_lift2 {x : List Bool} {M : ℕ} (t : LTerm) (a b : ℕ) (env : List ℕ) :
    eval x M (a :: b :: env) (lift 2 t) = eval x M env t := by
  simpa using eval_lift (x := x) (M := M) t [a, b] env

theorem eval_lift1 {x : List Bool} {M : ℕ} (t : LTerm) (a : ℕ) (env : List ℕ) :
    eval x M (a :: env) (lift 1 t) = eval x M env t := by
  simpa using eval_lift (x := x) (M := M) t [a] env

theorem maxLit_lift (n : ℕ) (t : LTerm) : (lift n t).maxLit = t.maxLit := maxLit_shift 0 n t

/-! ### Derived constructs -/

/-- `1` iff the value is non-zero. -/
def tst (a : LTerm) : LTerm := .ite a (.lit 1) (.lit 0)
def not (a : LTerm) : LTerm := .ite a (.lit 0) (.lit 1)
def and (a b : LTerm) : LTerm := .ite a (tst b) (.lit 0)
def or (a b : LTerm) : LTerm := .ite a (.lit 1) (tst b)
def eq (a b : LTerm) : LTerm := not (.add (.lt a b) (.lt b a))

/-- `∀ i < n, body` (the body sees `i` as variable `1`, an accumulator as variable `0`). -/
def forallB (n body : LTerm) : LTerm := .fold n (.lit 1) (and (.var 0) body)
/-- `∃ i < n, body`. -/
def existsB (n body : LTerm) : LTerm := .fold n (.lit 0) (or (.var 0) body)
/-- The least `i < n` with `body`, or `n` if there is none.  The accumulator holds the answer
so far, `n` meaning "not found". -/
def firstB (n body : LTerm) : LTerm :=
  .let_ n (.fold (.var 0) (.var 0) (.ite (.lt (.var 0) (.var 2)) (.var 0)
    (.ite (lift 1 body) (.var 1) (.var 0))))

variable {x : List Bool} {M : ℕ}

@[simp] theorem eval_tst (env : List ℕ) (a : LTerm) :
    eval x M env (tst a) = if eval x M env a ≠ 0 then 1 else 0 := rfl
@[simp] theorem eval_not (env : List ℕ) (a : LTerm) :
    eval x M env (not a) = if eval x M env a ≠ 0 then 0 else 1 := rfl
@[simp] theorem eval_and (env : List ℕ) (a b : LTerm) :
    eval x M env (and a b) = if eval x M env a ≠ 0 ∧ eval x M env b ≠ 0 then 1 else 0 := by
  simp only [and, eval, eval_tst]; split_ifs <;> simp_all
@[simp] theorem eval_or (env : List ℕ) (a b : LTerm) :
    eval x M env (or a b) = if eval x M env a ≠ 0 ∨ eval x M env b ≠ 0 then 1 else 0 := by
  simp only [or, eval, eval_tst]; split_ifs <;> simp_all

theorem eval_eq (env : List ℕ) (a b : LTerm) (hM : 1 ≤ M) :
    eval x M env (eq a b) = if eval x M env a = eval x M env b then 1 else 0 := by
  simp only [eq, eval, eval_not]
  rcases lt_trichotomy (eval x M env a) (eval x M env b) with h | h | h
  · have h2 : ¬ eval x M env b < eval x M env a := Nat.not_lt.2 h.le
    simp only [h, h2, if_true, if_false]
    rw [if_pos (by omega), if_neg h.ne]
  · simp only [h, lt_irrefl, if_false]
    rw [if_neg (by omega)]; simp
  · have h2 : ¬ eval x M env a < eval x M env b := Nat.not_lt.2 h.le
    simp only [h, h2, if_true, if_false]
    rw [if_pos (by omega), if_neg h.ne']

theorem foldl_and (f : ℕ → ℕ → Prop) [DecidableRel f] (l : List ℕ) :
    ∀ a : ℕ, (a = 0 ∨ a = 1) →
      (l.foldl (fun acc j => if acc ≠ 0 ∧ f acc j then 1 else 0) a = 1 ↔ a = 1 ∧ ∀ j ∈ l, f 1 j) := by
  induction l with
  | nil => intro a _; simp
  | cons j l ih =>
    intro a ha
    rw [List.foldl_cons, ih _ (by split_ifs <;> simp)]
    rcases ha with rfl | rfl <;> simp

/-- **The meaning of `∀ i < n`.** -/
theorem eval_forallB (env : List ℕ) (n body : LTerm) :
    eval x M env (forallB n body) =
      if ∀ i < eval x M env n, eval x M (1 :: i :: env) body ≠ 0 then 1 else 0 := by
  simp only [forallB, eval]
  have key := foldl_and (fun acc j => eval x M (acc :: j :: env) body ≠ 0)
    (List.range (eval x M env n)) 1 (Or.inr rfl)
  have h01 : ∀ (l : List ℕ) (a : ℕ), (a = 0 ∨ a = 1) →
      l.foldl (fun acc j => if acc ≠ 0 ∧ eval x M (acc :: j :: env) body ≠ 0 then 1 else 0) a = 0 ∨
      l.foldl (fun acc j => if acc ≠ 0 ∧ eval x M (acc :: j :: env) body ≠ 0 then 1 else 0) a = 1 := by
    intro l
    induction l with
    | nil => intro a ha; simpa using ha
    | cons j l ih => intro a _; rw [List.foldl_cons]; exact ih _ (by split_ifs <;> simp)
  have hf : (fun acc j => eval x M (acc :: j :: env) (and (.var 0) body)) =
      fun acc j => if acc ≠ 0 ∧ eval x M (acc :: j :: env) body ≠ 0 then 1 else 0 := by
    funext acc j; simp [eval]
  rw [hf]
  split_ifs with h
  · exact key.2 ⟨rfl, fun j hj => h j (List.mem_range.1 hj)⟩
  · rcases h01 (List.range (eval x M env n)) 1 (Or.inr rfl) with h0 | h1
    · exact h0
    · exact absurd (fun i hi => (key.1 h1).2 i (List.mem_range.2 hi)) h

theorem foldl_or (f : ℕ → ℕ → Prop) [DecidableRel f] (l : List ℕ) :
    ∀ a : ℕ, (a = 0 ∨ a = 1) →
      (l.foldl (fun acc j => if acc ≠ 0 ∨ f acc j then 1 else 0) a = 0 ↔
        a = 0 ∧ ∀ j ∈ l, ¬ f 0 j) := by
  induction l with
  | nil => intro a _; simp
  | cons j l ih =>
    intro a ha
    rw [List.foldl_cons, ih _ (by split_ifs <;> simp)]
    rcases ha with rfl | rfl <;> simp

/-- **The meaning of `∃ i < n`.** -/
theorem eval_existsB (env : List ℕ) (n body : LTerm) :
    eval x M env (existsB n body) =
      if ∃ i < eval x M env n, eval x M (0 :: i :: env) body ≠ 0 then 1 else 0 := by
  simp only [existsB, eval]
  have key := foldl_or (fun acc j => eval x M (acc :: j :: env) body ≠ 0)
    (List.range (eval x M env n)) 0 (Or.inl rfl)
  have h01 : ∀ (l : List ℕ) (a : ℕ), (a = 0 ∨ a = 1) →
      l.foldl (fun acc j => if acc ≠ 0 ∨ eval x M (acc :: j :: env) body ≠ 0 then 1 else 0) a = 0 ∨
      l.foldl (fun acc j => if acc ≠ 0 ∨ eval x M (acc :: j :: env) body ≠ 0 then 1 else 0) a = 1 := by
    intro l
    induction l with
    | nil => intro a ha; simpa using ha
    | cons j l ih => intro a _; rw [List.foldl_cons]; exact ih _ (by split_ifs <;> simp)
  have hf : (fun acc j => eval x M (acc :: j :: env) (or (.var 0) body)) =
      fun acc j => if acc ≠ 0 ∨ eval x M (acc :: j :: env) body ≠ 0 then 1 else 0 := by
    funext acc j; simp [eval]
  rw [hf]
  split_ifs with h
  · rcases h01 (List.range (eval x M env n)) 0 (Or.inl rfl) with h0 | h1
    · obtain ⟨i, hi, hb⟩ := h
      exact absurd ((key.1 h0).2 i (List.mem_range.2 hi)) (by simpa using hb)
    · exact h1
  · push_neg at h
    exact key.2 ⟨rfl, fun j hj => by simpa using h j (List.mem_range.1 hj)⟩

theorem foldl_first (f : ℕ → Prop) [DecidablePred f] (N : ℕ) : ∀ (l : List ℕ) (a : ℕ),
    (∀ j ∈ l, j < N) →
    l.foldl (fun acc i => if acc < N then acc else if f i then i else acc) a =
      if a < N then a else (l.find? f).getD a := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons j l ih =>
    intro a hl
    rw [List.foldl_cons, ih _ (fun j' hj' => hl j' (by simp [hj']))]
    have hj := hl j (by simp)
    by_cases ha : a < N
    · simp [ha]
    · by_cases hf : f j
      · simp [ha, hf, hj]
      · simp [ha, hf]

/-- **The meaning of the search for the least index.** -/
theorem eval_firstB (env : List ℕ) (n body : LTerm) :
    eval x M env (firstB n body) =
      ((List.range (eval x M env n)).find? fun i => eval x M (i :: eval x M env n :: env) body ≠ 0).getD
        (eval x M env n) := by
  set N := eval x M env n
  have hf : ∀ acc i, eval x M (acc :: i :: N :: env)
      (.ite (.lt (.var 0) (.var 2)) (.var 0) (.ite (lift 1 body) (.var 1) (.var 0))) =
      if acc < N then acc else if eval x M (i :: N :: env) body ≠ 0 then i else acc := by
    intro acc i
    have hl := eval_lift1 (x := x) (M := M) body acc (i :: N :: env)
    by_cases h : acc < N
    · simp [eval, h]
    · simp only [eval, List.getD_cons_zero, List.getD_cons_succ, hl, h, if_false]
      by_cases hb : eval x M (i :: N :: env) body ≠ 0 <;> simp [hb]
  show (List.range N).foldl (fun acc i => eval x M (acc :: i :: N :: env)
      (.ite (.lt (.var 0) (.var 2)) (.var 0) (.ite (lift 1 body) (.var 1) (.var 0)))) N = _
  simp only [hf]
  rw [foldl_first (fun i => eval x M (i :: N :: env) body ≠ 0) N _ N
    (fun j hj => List.mem_range.1 hj)]
  simp

end LTerm

end Cx

end HTN
