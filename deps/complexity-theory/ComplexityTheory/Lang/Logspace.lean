import ComplexityTheory.Lang.Basic
/-!
# `L` (deterministic logarithmic space)

`HTN.Cx.L`: the languages decided by a deterministic **register program** whose registers stay
polynomially bounded in the input length.  A program (`HTN.Cx.LStmt`) is a while program over
finitely many natural-number registers; it reads the input only through the expressions `len`
(its length) and `bit e` (the bit at position `e`, `0` outside the input), and cannot write it.
A register bounded by `q(n)` holds `O(log n)` bits, so this is the classical characterisation of
deterministic logarithmic space by machines with a constant number of logarithmic-size
registers (equivalently, multi-head two-way automata).

* `HTN.Cx.LExp`, `HTN.Cx.LStmt` — expressions and statements;
* `HTN.Cx.ExecB x B s R R'` — the run of `s` on the input `x` from the registers `R` ends in
  `R'`, every value written being at most `B`;
* **`HTN.Cx.L`** — `x ∈ L` iff the run from all-zero registers ends with register `0` non-zero,
  the run existing for every input with the bound `q(|x|)`.
-/

namespace HTN

namespace Cx

/-- **Expressions** of register programs. -/
inductive LExp where
  | reg (r : ℕ)
  | lit (c : ℕ)
  | len
  | add (a b : LExp)
  | sub (a b : LExp)
  | lt (a b : LExp)
  | bit (a : LExp)

/-- **Statements** of register programs. -/
inductive LStmt where
  | assign (r : ℕ) (e : LExp)
  | seq (s t : LStmt)
  | ite (e : LExp) (s t : LStmt)
  | while (e : LExp) (s : LStmt)

/-- The value of an expression. -/
def LExp.eval (x : List Bool) (R : ℕ → ℕ) : LExp → ℕ
  | .reg r => R r
  | .lit c => c
  | .len => x.length
  | .add a b => a.eval x R + b.eval x R
  | .sub a b => a.eval x R - b.eval x R
  | .lt a b => if a.eval x R < b.eval x R then 1 else 0
  | .bit a => if x.getD (a.eval x R) false then 1 else 0

/-- **Bounded runs**: the run of `s` from `R` ends in `R'`, every value written being at most
`B`. -/
inductive ExecB (x : List Bool) (B : ℕ) : LStmt → (ℕ → ℕ) → (ℕ → ℕ) → Prop
  | assign {r : ℕ} {e : LExp} {R : ℕ → ℕ} (h : e.eval x R ≤ B) :
      ExecB x B (.assign r e) R (Function.update R r (e.eval x R))
  | seq {s t : LStmt} {R R₁ R' : ℕ → ℕ} (h₁ : ExecB x B s R R₁) (h₂ : ExecB x B t R₁ R') :
      ExecB x B (.seq s t) R R'
  | iteT {e : LExp} {s t : LStmt} {R R' : ℕ → ℕ} (hc : e.eval x R ≠ 0) (h : ExecB x B s R R') :
      ExecB x B (.ite e s t) R R'
  | iteF {e : LExp} {s t : LStmt} {R R' : ℕ → ℕ} (hc : e.eval x R = 0) (h : ExecB x B t R R') :
      ExecB x B (.ite e s t) R R'
  | whileT {e : LExp} {s : LStmt} {R R₁ R' : ℕ → ℕ} (hc : e.eval x R ≠ 0)
      (h₁ : ExecB x B s R R₁) (h₂ : ExecB x B (.while e s) R₁ R') :
      ExecB x B (.while e s) R R'
  | whileF {e : LExp} {s : LStmt} {R : ℕ → ℕ} (hc : e.eval x R = 0) :
      ExecB x B (.while e s) R R

/-- **`L`**: the languages decided by register programs with polynomially bounded registers. -/
def L : LangClass := fun Lg => ∃ (s : LStmt) (q : Polynomial ℕ), ∀ x,
  ∃ R', ExecB x (q.eval x.length) s (fun _ => 0) R' ∧ (Lg x ↔ R' 0 ≠ 0)

/-- Runs are deterministic. -/
theorem ExecB.det {x : List Bool} {B : ℕ} {s : LStmt} {R R₁ R₂ : ℕ → ℕ}
    (h₁ : ExecB x B s R R₁) (h₂ : ExecB x B s R R₂) : R₁ = R₂ := by
  induction h₁ generalizing R₂ with
  | assign => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁' h₂' => exact ih₂ (by rwa [ih₁ h₁'])
  | iteT hc _ ih =>
    cases h₂ with
    | iteT _ h => exact ih h
    | iteF hc' _ => exact absurd hc' hc
  | iteF hc _ ih =>
    cases h₂ with
    | iteT hc' _ => exact absurd hc hc'
    | iteF _ h => exact ih h
  | whileT hc _ _ ih₁ ih₂ =>
    cases h₂ with
    | whileT _ h₁' h₂' => exact ih₂ (by rwa [ih₁ h₁'])
    | whileF hc' => exact absurd hc' hc
  | whileF hc =>
    cases h₂ with
    | whileT hc' _ _ => exact absurd hc hc'
    | whileF _ => rfl

end Cx

end HTN
