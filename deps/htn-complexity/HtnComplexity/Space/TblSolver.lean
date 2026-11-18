import HtnComplexity.Space.StripsSystem
import ComplexityTheory.Space.Model
import HtnComplexity.Complexity.Serial
/-!
# The machine for action tables, as an explicit hypothesis

`HtnComplexity/Space/StripsSystem.lean` and `HtnComplexity/Space/RegTable.lean` reduce
plan existence for the `PSPACE` targets of Table 3 to **reachability in an action table**, with
the table a function of the domain description alone and the initial state and the goal
functions of the instance description alone.  What is left of the target side is then a single
statement that mentions no planning at all:

> there is a nondeterministic polynomial-space machine which, given the initial state and the
> goal of a table problem as its input and (an encoding of) the table as its advice, accepts
> exactly the solvable problems.

`HTN.Space.TblSolver` is that statement.  Three details of its shape deserve a word.

* **The advice format is existentially quantified.**  The machine comes with its own encoding
  `enc` of a table into bits; only the *length* of the encoding is constrained, by a polynomial
  in the number of symbols of the table and in the parameter `L` below.  Nothing requires the
  encoding to be computable from the table — which is the whole point of the target side: the
  domain compilation may be arbitrarily expensive (`TABLE3-PLAN.md`).

* **The parameter `L` bounds the facts of the input.**  A table of few symbols may mention facts
  of astronomical magnitude, whose numerals no polynomially long advice can carry.  The
  correctness requirement is therefore restricted to problems whose initial state and goal
  mention only facts below `2 ^ L`, and the advice may depend on `L`: the encoding is free to
  compress the facts of the table that no admissible input can mention.  Without the
  restriction the statement would be false, for the reason recorded in
  `HtnComplexity/Space/Bridge.lean`.

* **The flag `b`** carries the part of the answer that depends on the domain description alone
  — for regular HTN, "the compiled domain has a method with an empty body".  It is one bit of
  the advice.

The statement is in the machine model of `ComplexityTheory/Space/Model.lean`.  It is a theorem
— `HTN.Space.tblSolver`, proved in `HtnComplexity/Space/TblMachine.lean`.  The variant the
target side of Table 3 actually uses, in which the input is the *code of an instance
description* rather than a written-out table problem, is `HTN.Space.instSolver`
(`HtnComplexity/Space/InstMachine.lean`).
-/

namespace HTN

namespace Space

open Syn PTime

/-- **A state, as a bit string**: the list of the binary numerals of its facts. -/
def encState (s : List ℕ) : List Bool := blist (s.map bitsOfNat)

/-- **The instance side of a table problem, as a bit string**: the initial state followed by the
goal. -/
def encProblem (s g : List ℕ) : List Bool := encState s ++ encState g

/-- **The number of symbols of an action table**: one per row plus one per fact listed. -/
def tblSize (tbl : List Row) : ℕ :=
  tbl.length + (tbl.map fun r => r.1.length + r.2.1.length + r.2.2.length).sum

@[simp] theorem tblSize_nil : tblSize [] = 0 := rfl

/-- **The target-side machine for action tables.**  Some nondeterministic polynomial-space
machine decides solvability of a table problem, reading the initial state and the goal off its
input and the table off its advice, the advice being polynomially long in the number of symbols
of the table and in the bound on the facts of the input. -/
def TblSolver : Prop :=
  ∃ (M : NSpace) (enc : Bool → ℕ → List Row → List Bool) (P : Polynomial ℕ),
    (∀ (b : Bool) (L : ℕ) (tbl : List Row), (enc b L tbl).length ≤ P.eval (tblSize tbl + L)) ∧
      ∀ (b : Bool) (L : ℕ) (tbl : List Row) (s g : List ℕ),
        (∀ f ∈ s, f < 2 ^ L) → (∀ f ∈ g, f < 2 ^ L) →
          (M.Accepts (encProblem s g) (enc b L tbl) ↔ (b = true ∧ SolvableTbl tbl s g))

end Space

end HTN
