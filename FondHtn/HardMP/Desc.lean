import FondHtn.HardMP.Rounds
import FondHtn.HardMP.Bridge
import HtnComplexity.Article.TOInd
/-!
# The FOND descriptions of the reductions

A list of programs `P` (`FOND.HardMP.prgs p`: the initial program, then the programs of one
round, `FOND.HardMP.rules`) is compiled into a hierarchy of *program states*: the compound task
`cN r pc` ("program `r` at instruction `pc`") has one method per alternative `alt` of the
instruction, `cN r pc → [aN r pc alt, cN r (pc + 1)]`, and the end state `cN r |P r|` has the
method `cN r |P r| → ex` (the *exit*).  The task `round` (`roundN`) has the methods
`round → [cN r 0]` for the programs `r ≥ 1` of a round.

* **`FOND.HardMP.descA`** (acyclic, totally ordered): exit `[]`; a clock `clk j → [clk (j-1),
  clk (j-1)]`, `clk 0 → [round]` produces `2 ^ N` rounds; `tn_I = [cN 0 0, clk N, fin]`, where
  the action `fin` requires `done`.
* **`FOND.HardMP.descR`** (regular): exit `[round]`, and additionally `round → [fin]`;
  `tn_I = [cN 0 0]`.

The initial state is the encoding of `FOND.HardMP.cfgInit`.
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

/-! ## Names -/

/-- The task `round` (`loop` in the regular construction). -/
def roundN : ℕ := 0

/-- The clock tasks. -/
def clkN (j : ℕ) : ℕ := 2 * j + 1

/-- The program states. -/
def cN (r pc : ℕ) : ℕ := 2 * Nat.pair r pc + 2

/-- The final check action. -/
def finN : ℕ := 0

/-- The actions of the programs. -/
def aN (r pc alt : ℕ) : ℕ := Nat.pair r (Nat.pair pc alt) + 1

/-! ## The description -/

/-- The specification of `fin`. -/
def finSpec : ASpec := ([fDone], [], noeff, [], [])

/-- The programs: the initial program, then the programs of a round. -/
def prgs (p : ProbDesc) : List (List (List ASpec)) := progInit p :: rules p

/-- The actions. -/
def acts (P : List (List (List ASpec))) : List FActDesc :=
  toFAct finN finSpec :: (List.range P.length).flatMap fun r =>
    (List.range (P.getI r).length).flatMap fun pc =>
      (List.range ((P.getI r).getI pc).length).map fun alt =>
        toFAct (aN r pc alt) (((P.getI r).getI pc).getI alt)

/-- A method with a sequence body. -/
def meth (c : ℕ) (body : List (Bool × ℕ)) : MethodDesc := (c, seqTn body)

/-- The methods of the program states. -/
def chainMeths (P : List (List (List ASpec))) (ex : List (Bool × ℕ)) : List MethodDesc :=
  (List.range P.length).flatMap fun r =>
    ((List.range (P.getI r).length).flatMap fun pc =>
      (List.range ((P.getI r).getI pc).length).map fun alt =>
        meth (cN r pc) [(false, aN r pc alt), (true, cN r (pc + 1))]) ++
    [meth (cN r (P.getI r).length) ex]

/-- The methods of `round`. -/
def roundMeths (P : List (List (List ASpec))) : List MethodDesc :=
  (List.range (P.length - 1)).map fun r => meth roundN [(true, cN (r + 1) 0)]

/-- The methods of the clock. -/
def clockMeths (N : ℕ) : List MethodDesc :=
  meth (clkN 0) [(true, roundN)] ::
    (List.range N).map fun j => meth (clkN (j + 1)) [(true, clkN j), (true, clkN j)]

/-- The number of clock levels: `2 ^ Nclk p` rounds suffice. -/
def Nclk (p : ProbDesc) : ℕ := 2 * (pfacts p).length + 2 * (numsOf p).length + 2

/-- The initial state (the encoding of `cfgInit p`). -/
def initFacts (p : ProbDesc) : List ℕ :=
  curF none :: ((List.range (pfacts p).length).filter fun j =>
    decide ((pfacts p).getI j ∈ p.init)).map fun j => fact (fSlot 0 j)

/-- **The acyclic totally ordered description.** -/
def descA (p : ProbDesc) : FProbDesc :=
  ((acts (prgs p), chainMeths (prgs p) [] ++ roundMeths (prgs p) ++ clockMeths (Nclk p)),
    (initFacts p, seqTn [(true, cN 0 0), (true, clkN (Nclk p)), (false, finN)]))

/-- **The regular description.** -/
def descR (p : ProbDesc) : FProbDesc :=
  ((acts (prgs p), chainMeths (prgs p) [(true, roundN)] ++ roundMeths (prgs p) ++
      [meth roundN [(false, finN)]]),
    (initFacts p, seqTn [(true, cN 0 0)]))

end HardMP

end FOND
