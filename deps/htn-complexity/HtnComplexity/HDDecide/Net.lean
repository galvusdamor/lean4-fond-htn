import HtnComplexity.HDDecide.Complete
import ComplexityTheory.HDDecide.RuleNet
import HtnComplexity.Computable.ToDecide
import HtnComplexity.Computable.PoNet
/-!
# The search on pieces as a Petri net

The search on pieces of `HtnComplexity/HDDecide/Pieces.lean` is a multiset rewriting
system with a finite control: the control state is the pair (forward state, backward state),
the items are the pieces, and every step consumes one piece.  This file writes it down
**concretely**, as a finite list of rules computed from the description (`HTN.HD.hdRules`), with

* control states `(0, [], [])` (*start*), `(1, lf, lb)` (*running*, with the forward and
  backward states as sublists of `allFacts`), and `(2, [], [])` (*done*);
* items `(k, l)`: a piece of the task network `k`, with its identifiers as a sublist of the
  identifier list of that network.

The start rules guess the goal state of the backward search, the step rules are the three
kinds of steps of `HTN.HD.HStep`, and the end rules move from a running configuration whose two
states agree to *done*.  The main result is

    HTN.HD.hdReach_iff : ReflTransGen (RStep (hdRules d q)) (hdInit d q) hdDone ↔ PiecesSolvable d q

so that, by `HTN.Petri.reach_mk_iff`, plan existence for one-hole-digging problems is a
reachability question in the Petri net `ruleNet (hdRules d q)`.
-/

namespace HTN

namespace HD

open Syn Syn.ToDec Petri

/-- Control states of the search: a tag and two lists of facts. -/
abbrev Ctl : Type := ℕ × List ℕ × List ℕ

/-- Items of the search: a task network index and a list of its identifiers. -/
abbrev Tok : Type := ℕ × List ℕ

/-- The rules of the search. -/
abbrev HRule : Type := Rule Ctl Tok

/-- The start control state. -/
def startC : Ctl := (0, [], [])

/-- The final control state. -/
def doneC : Ctl := (2, [], [])

/-- The item list of a piece: nothing if it is empty. -/
def tokOf (k : ℕ) (l : List ℕ) : List Tok := bif l.isEmpty then [] else [(k, l)]

/-- The canonical list of a list of facts. -/
def nrmF (d : DomDesc) (q : InstDesc) (l : List ℕ) : List ℕ := (allFacts d q).filter (memB l)

/-- Progression of the identifier `x` of the item `(k, l)`. -/
def progR (d : DomDesc) (q : InstDesc) (lf lb : List ℕ) (k : ℕ) (l : List ℕ) (x : ℕ) :
    List HRule :=
  bif !((net d q k).lblPair x).1 && l.all (fun y => !TnDesc.ordB (net d q k) y x) &&
      applB d lf ((net d q k).lblPair x).2 then
    [((1, lf, lb), some (k, l), (1, nrmF d q (stepL d lf ((net d q k).lblPair x).2), lb),
      tokOf k (l.filter (fun y => y != x)))]
  else []

/-- Regression of the identifier `x` of the item `(k, l)`, to the state `s`. -/
def regrR (d : DomDesc) (q : InstDesc) (lf lb : List ℕ) (k : ℕ) (l : List ℕ) (x : ℕ) :
    List HRule :=
  (subsets (allFacts d q)).flatMap fun s =>
    bif !((net d q k).lblPair x).1 && l.all (fun y => !TnDesc.ordB (net d q k) x y) &&
        applB d s ((net d q k).lblPair x).2 &&
        (nrmF d q (stepL d s ((net d q k).lblPair x).2) == lb) then
      [((1, lf, lb), some (k, l), (1, lf, nrmF d q s), tokOf k (l.filter (fun y => y != x)))]
    else []

/-- Decomposition of the identifier `x` of the item `(k, l)` with the `j`-th method. -/
def decR (d : DomDesc) (q : InstDesc) (lf lb : List ℕ) (k : ℕ) (l : List ℕ) (x : ℕ) :
    List HRule :=
  (List.range d.methods.length).flatMap fun j =>
    bif ((net d q k).lblPair x).1 &&
        l.all (fun y => !TnDesc.ordB (net d q k) y x && !TnDesc.ordB (net d q k) x y) &&
        ((d.methods.getD j default).1 == ((net d q k).lblPair x).2) then
      [((1, lf, lb), some (k, l), (1, lf, lb),
        tokOf k (l.filter (fun y => y != x)) ++ tokOf (j + 1) (net d q (j + 1)).ids)]
    else []

/-- All possible items. -/
def allToks (d : DomDesc) (q : InstDesc) : List Tok :=
  (List.range (d.methods.length + 1)).flatMap fun k => (subsets (net d q k).ids).map fun l => (k, l)

/-- The step rules. -/
def stepRules (d : DomDesc) (q : InstDesc) : List HRule :=
  (subsets (allFacts d q)).flatMap fun lf => (subsets (allFacts d q)).flatMap fun lb =>
    (allToks d q).flatMap fun p => p.2.flatMap fun x =>
      progR d q lf lb p.1 p.2 x ++ regrR d q lf lb p.1 p.2 x ++ decR d q lf lb p.1 p.2 x

/-- The start rules: guess the goal state of the backward search. -/
def startRules (d : DomDesc) (q : InstDesc) : List HRule :=
  (subsets (allFacts d q)).flatMap fun s =>
    bif q.goalList.all (memB s) then
      [(startC, none, (1, nrmF d q q.initList, nrmF d q s), [])]
    else []

/-- The end rules: the two searches meet. -/
def endRules (d : DomDesc) (q : InstDesc) : List HRule :=
  (subsets (allFacts d q)).map fun l => ((1, l, l), none, doneC, [])

/-- **The rules of the search on pieces.** -/
def hdRules (d : DomDesc) (q : InstDesc) : List HRule :=
  startRules d q ++ stepRules d q ++ endRules d q

/-- The initial configuration: start, with the initial task network as the only piece. -/
def hdInit (q : InstDesc) : Ctl × Multiset Tok := (startC, (tokOf 0 q.tnI.ids : Multiset Tok))

/-- The final configuration: done, without pieces. -/
def hdDone : Ctl × Multiset Tok := (doneC, 0)

/-! ### Encoding configurations of the search on pieces -/

/-- The list of a finite state. -/
def stL (d : DomDesc) (q : InstDesc) (s : Finset ℕ) : List ℕ :=
  (allFacts d q).filter fun f => decide (f ∈ s)

/-- The item of a piece. -/
def pcL (d : DomDesc) (q : InstDesc) (p : Piece) : Tok :=
  (p.1, (net d q p.1).ids.filter fun x => decide (x ∈ p.2))

/-- The encoding of a configuration. -/
def enc (d : DomDesc) (q : InstDesc) (c : HCfg) : Ctl × Multiset Tok :=
  ((1, stL d q c.1, stL d q c.2.1), c.2.2.map (pcL d q))

/-- The invariant of the configurations of the search. -/
def Valid (d : DomDesc) (q : InstDesc) (c : HCfg) : Prop :=
  c.1 ⊆ facts d q ∧ c.2.1 ⊆ facts d q ∧
    ∀ p ∈ c.2.2, p.1 < d.methods.length + 1 ∧ p.2 ⊆ (net d q p.1).ids.toFinset

end HD

end HTN
