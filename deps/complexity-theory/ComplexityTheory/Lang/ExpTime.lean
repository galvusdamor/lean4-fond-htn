import ComplexityTheory.Lang.Basic
/-!
# `EXPTIME`

`HTN.Cx.EXPTIME`: the languages `L` for which, for some polynomial `q`, the **padded language**

    { pairStr x 1^(2^q(|x|)) | x ∈ L }

is in `P`.  This is the classical padding characterisation of deterministic exponential time
(`EXPTIME = ⋃_k DTIME(2^(n^k))`): a machine running in time `2^q(n)` on `x` runs in time
polynomial in the length of the padded word, and conversely a polynomial-time decider of the
padded language, run on the padded word it writes first, decides `L` in exponential time.  It
is stated with the same notion of polynomial time as `HTN.Cx.P`.
-/

namespace HTN

namespace Cx

open Syn

/-- `x` padded with `2 ^ q(|x|)` ones. -/
def padExp (q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairStr x (List.replicate (2 ^ q.eval x.length) true)

/-- The padded language. -/
def padLang (q : Polynomial ℕ) (L : Language) : Language := fun y => ∃ x, y = padExp q x ∧ L x

/-- **`EXPTIME`**: some exponential padding of the language is in `P`. -/
def EXPTIME : LangClass := fun L => ∃ q : Polynomial ℕ, P (padLang q L)

end Cx

end HTN
