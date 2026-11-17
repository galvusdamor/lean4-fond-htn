import FondHtn.HardMP.Desc
/-!
# The regular construction with a round counter

For the *fair* reading of strong cyclic solutions the regular construction `FOND.HardMP.descR`
is not correct: a cyclic policy may circumvent nature (e.g. a triple `(c, s, s')` that is not
derivable can be "supported" by a cycle through other triples from which `done` is reachable).
`FOND.HardMP.descC` adds a binary counter of `Nc p` bits (bits `j` of slot `cslot p`): every round
program starts with the instruction `incI p` (increment the counter: the policy chooses the
lowest zero bit `i`, all lower bits must be set; the action clears them and sets bit `i`).  So at
most `2 ^ Nc p - 1` rounds are possible, every execution is finite, and the fair reading
coincides with the strong one.
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

/-- The counter slot (above all slots used by the round programs). -/
def cslot (p : ProbDesc) : ℕ := ((rules p).flatMap id).length + 3

/-- The number of counter bits. -/
def Nc (p : ProbDesc) : ℕ := Nclk p + 1

/-- **Increment the counter**: alternative `i` requires bits `j < i` set and bit `i` clear. -/
def incI (p : ProbDesc) : List ASpec :=
  (List.range (Nc p)).map fun i =>
    ((List.range i).map (fSlot (cslot p)), [fSlot (cslot p) i],
      [([fSlot (cslot p) i], (List.range i).map (fSlot (cslot p)))], [], [])

/-- The round programs, each preceded by the increment. -/
def rulesC (p : ProbDesc) : List (List (List ASpec)) := (rules p).map (incI p :: ·)

/-- The programs of the counter construction. -/
def prgsC (p : ProbDesc) : List (List (List ASpec)) := progInit p :: rulesC p

/-- **The regular description with a round counter.** -/
def descC (p : ProbDesc) : FProbDesc :=
  ((acts (prgsC p), chainMeths (prgsC p) [(true, roundN)] ++ roundMeths (prgsC p) ++
      [meth roundN [(false, finN)]]),
    (initFacts p, seqTn [(true, cN 0 0)]))

end HardMP

end FOND
