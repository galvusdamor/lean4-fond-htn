import ComplexityTheory.PolyHier.Defs
import ComplexityTheory.Collapse.Code
/-!
# Strings of polynomial length, and pairing, inside Cobham's class

Two small tools for manipulating quantifier prefixes of the polynomial hierarchy
(`ComplexityTheory/PolyHier/Defs.lean`):

* `HTN.PH.cobham_zerosPoly` — for every polynomial `q`, the string of `q(|x|)` zeros is a function
  of Cobham's class of `x`.  It is used to *truncate* quantified strings to a polynomial length,
  which is how a quantifier over a longer string simulates one over a shorter string;
* `HTN.PH.pk`, `HTN.PH.pfst`, `HTN.PH.psnd` — a pairing of bit strings with projections of
  Cobham's class: `pk u v` is the unary length of `u`, a separator, `u` and then `v`.  It merges
  adjacent quantifiers of the same kind.
-/

namespace HTN

namespace PH

open PTime PSpace

/-! ### Closure forms of the basic functions -/

theorem cobham_app {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => a args ++ b args :=
  (cobham_c2 cobham_append ha hb).of_eq' fun args => by simp [compFn]

theorem cobham_smash {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => List.replicate ((a args).length * (b args).length) false :=
  (cobham_c2 Cobham.smash ha hb).of_eq' fun args => by simp [compFn, smashFn]

theorem cobham_onesPrefix {a : Fn} (ha : Cobham a) : Cobham fun args => onesPrefix (a args) :=
  (cobham_c1 cobham_onesPrefixFn ha).of_eq' fun args => by simp [compFn, onesPrefixFn_apply]

/-! ### Strings of polynomial length -/

/-- **A string of polynomial length.**  For a polynomial `q` and a function `a` of the class, the
string of `q(|a|)` zeros is a function of the class. -/
theorem cobham_zerosPoly (q : Polynomial ℕ) {a : Fn} (ha : Cobham a) :
    Cobham fun args => List.replicate (q.eval (a args).length) false := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      exact (cobham_app hp hr).of_eq' fun args => by rw [Polynomial.eval_add, List.replicate_add]
  | monomial i c =>
      -- the string of `|a| ^ i` zeros
      have hpow : ∀ i : ℕ, Cobham fun args => List.replicate ((a args).length ^ i) false := by
        intro i
        induction i with
        | zero => exact (cobham_const [false]).of_eq' fun args => by simp
        | succ i ih => exact (cobham_smash ih ha).of_eq' fun args => by simp [pow_succ]
      exact (cobham_smash (cobham_const (List.replicate c false)) (hpow i)).of_eq' fun args => by
        simp [Polynomial.eval_monomial]

/-- The truncation of a computed string to a polynomial length of another. -/
theorem cobham_truncPoly (q : Polynomial ℕ) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => (b args).take (q.eval (a args).length) :=
  (cobham_take (cobham_zerosPoly q ha) hb).of_eq' fun args => by simp

/-! ### Pairing -/

/-- **The pairing of two strings**: the length of the first in unary, a separator, the first
string, the second string. -/
def pk (u v : List Bool) : List Bool := ones u.length ++ false :: (u ++ v)

/-- The first component of a paired string. -/
def pfst (t : List Bool) : List Bool := (t.drop ((onesPrefix t).length + 1)).take (onesPrefix t).length

/-- The second component of a paired string. -/
def psnd (t : List Bool) : List Bool := t.drop (2 * (onesPrefix t).length + 1)

theorem onesPrefix_pk (u v : List Bool) : onesPrefix (pk u v) = ones u.length :=
  onesPrefix_ones_append _ _

@[simp] theorem pfst_pk (u v : List Bool) : pfst (pk u v) = u := by
  rw [pfst, onesPrefix_pk, length_ones, pk]
  have : (ones u.length ++ false :: (u ++ v)).drop (u.length + 1) = u ++ v := by
    rw [show ones u.length ++ false :: (u ++ v) = (ones u.length ++ [false]) ++ (u ++ v) by simp]
    exact List.drop_left' (by simp)
  rw [this]
  simp

@[simp] theorem psnd_pk (u v : List Bool) : psnd (pk u v) = v := by
  rw [psnd, onesPrefix_pk, length_ones, pk]
  rw [show ones u.length ++ false :: (u ++ v) = (ones u.length ++ [false] ++ u) ++ v by simp]
  exact List.drop_left' (by simp; ring)

@[simp] theorem length_pk (u v : List Bool) : (pk u v).length = 2 * u.length + 1 + v.length := by
  simp [pk]; ring

theorem cobham_pfst {a : Fn} (ha : Cobham a) : Cobham fun args => pfst (a args) := by
  have h1 : Cobham fun args => onesPrefix (a args) ++ [false] :=
    cobham_app (cobham_onesPrefix ha) (cobham_const [false])
  have h2 : Cobham fun args => (a args).drop (onesPrefix (a args) ++ [false]).length :=
    cobham_drop h1 ha
  exact (cobham_take (cobham_onesPrefix ha) h2).of_eq' fun args => by simp [pfst]

theorem cobham_psnd {a : Fn} (ha : Cobham a) : Cobham fun args => psnd (a args) := by
  have h1 : Cobham fun args => onesPrefix (a args) ++ (onesPrefix (a args) ++ [false]) :=
    cobham_app (cobham_onesPrefix ha) (cobham_app (cobham_onesPrefix ha) (cobham_const [false]))
  exact (cobham_drop h1 ha).of_eq' fun args => by simp [psnd]; ring_nf

end PH

end HTN
