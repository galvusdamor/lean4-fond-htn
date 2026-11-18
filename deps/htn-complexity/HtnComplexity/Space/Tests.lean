import HtnComplexity.Space.Advice
import HtnComplexity.Space.StateTests
import ComplexityTheory.Complexity.CobhamExamples
/-!
# The tests of the target-side machine

The machine of `HtnComplexity/Space/TblMachine.lean` has a configuration which is a state
written as a serialised list of canonical numerals, an input which is the initial state and the
goal of a table problem, and an advice which is the action table
(`HtnComplexity/Space/Advice.lean`).  Its three tests are assembled here out of the
scanning toolkit of `HtnComplexity/Complexity/`, each with

* a **semantic** lemma reading it on well-formed strings, and
* a **closure** lemma placing it in Cobham's class for computed arguments.

The pieces are:

* `HTN.Space.afterB` — a new closure property: *the test holds at the suffix that follows the
  leading serialised list*.  It is what lets the machine address the second of two serialised
  lists written one after the other (the goal in the input, the fact entries in the advice)
  without computing where the first one ends: the position is pinned down by the requirement
  that what precedes it is a complete serialised list, which is unique (`HTN.Syn.blist_parse`);
* `HTN.Space.extB`, `HTN.Space.tagIsB`, `HTN.Space.factOf`, `HTN.Space.mkEnt` — reading and
  building the entries of the advice.  All four are string surgeries on the *encoded* form
  `true :: bstr w` of an entry, which is the form the quantifiers of
  `HtnComplexity/Complexity/SerAny.lean` and the membership test `HTN.Syn.occB` use, so
  nothing has to be re-encoded;
* `HTN.Space.canonEntB` — the entry is a canonical numeral (`HtnComplexity/Space/Canon.lean`);
* `HTN.Space.rowStepB` — the four conditions of one transition of the action table, and
  `HTN.Space.stepCoreB`, `HTN.Space.initCoreB`, `HTN.Space.accCoreB`, `HTN.Space.wfB`, the tests
  of the machine itself.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### The suffix after the leading serialised list -/

/-- The body of `HTN.Space.afterB`: the piece before the suffix is a complete serialised list,
and the test fails there. -/
def afterTest (p : Args → Bool) (args : Args) : Bool :=
  blistB (cutAt (args.getD 1 []) (args.getD 0 [])) &&
    !p [args.getD 0 [], args.getD 2 [], args.getD 3 [], args.getD 4 []]

/-- **Does `p` hold at the suffix that follows the leading serialised list of `y`?** -/
def afterB (p : Args → Bool) (y v₁ v₂ v₃ : List Bool) : Bool :=
  !anyTailsB (afterTest p) [y, v₁, v₂, v₃] y

/-! ### Reading and building the entries of the advice -/

/-- **The entry `E` belongs to the row named by the entry `U`.** -/
def extB (U E : List Bool) : Bool := decide (U.take (U.length - 1) <+: E)

/-- The part of the entry `E` that follows the name `U`. -/
def restOf (U E : List Bool) : List Bool := E.drop (U.length - 1)

/-- **The entry `E` of the row named by `U` carries the tag `t`.** -/
def tagIsB (t : List Bool) (U E : List Bool) : Bool := decide (dbl t <+: restOf U E)

/-- **The fact of the entry `E` of the row named by `U`**, in encoded form. -/
def factOf (U E : List Bool) : List Bool := true :: (restOf U E).drop 4

/-- **The entry of the row named by `U` with tag `t` and fact `E`** (the fact in encoded form). -/
def mkEnt (t : List Bool) (U E : List Bool) : List Bool := U.take (U.length - 1) ++ dbl t ++ E.tail

/-! ### Canonical entries -/

/-- **The entry is a canonical numeral.** -/
def canonEntB (E : List Bool) : Bool :=
  decide (E = [true, false]) || decide ([true, true, false] <:+ E)

/-! ### One transition of the action table -/

/-- Every entry of the fact list `y` that belongs to the row named by `U` and carries the tag
`t` has its fact in `c`. -/
def inOkB (t : List Bool) (U y c : List Bool) : Bool :=
  allEntB (fun args =>
    !(extB (args.getD 1 []) (args.getD 0 []) && tagIsB t (args.getD 1 []) (args.getD 0 [])) ||
      occB (args.getD 2 []) (factOf (args.getD 1 []) (args.getD 0 []))) y U c []

/-- Every fact of `c` is deleted by the row named by `U` or survives into `c'`. -/
def keepOkB (U y c c' : List Bool) : Bool :=
  allEntB (fun args =>
    occB (args.getD 2 []) (mkEnt tagDel (args.getD 1 []) (args.getD 0 [])) ||
      occB (args.getD 3 []) (args.getD 0 [])) c U y c'

/-- Every fact of `c'` is added by the row named by `U`, or was in `c` and is not deleted. -/
def postOkB (U y c c' : List Bool) : Bool :=
  allEntB (fun args =>
    occB (args.getD 2 []) (mkEnt tagAdd (args.getD 1 []) (args.getD 0 [])) ||
      (occB (args.getD 3 []) (args.getD 0 []) &&
        !occB (args.getD 2 []) (mkEnt tagDel (args.getD 1 []) (args.getD 0 [])))) c' U y c

/-- **One transition of the row named by `U`.** -/
def rowStepB (U y c c' : List Bool) : Bool :=
  inOkB tagPrec U y c && inOkB tagAdd U y c' && keepOkB U y c c' && postOkB U y c c'

/-- **The transition relation the advice describes.** -/
def stepCoreB (a c c' : List Bool) : Bool :=
  afterB (fun args =>
    anyEntB (fun args2 => rowStepB (args2.getD 0 []) (args2.getD 1 []) (args2.getD 2 [])
      (args2.getD 3 [])) (args.getD 1 []) (args.getD 0 []) (args.getD 2 []) (args.getD 3 []))
    a a c c'

/-- **The configuration carries the facts of the initial state of the input.** -/
def initCoreB (c x : List Bool) : Bool := subEntB c x && subEntB x c

/-- **The flag bit of the advice is set and the goal of the input is reached.** -/
def accCoreB (c x a : List Bool) : Bool :=
  (a.reverse.headD false) &&
    afterB (fun args => subEntB (args.getD 0 []) (args.getD 1 [])) x c [] []

/-- **The configuration is a serialised list of canonical numerals, and is short enough.** -/
def wfB (c bnd : List Bool) : Bool :=
  blistB c && allEntB (fun args => canonEntB (args.getD 0 [])) c [] [] [] &&
    decide (c.length ≤ bnd.length)

end Space

end HTN
