import HtnComplexity.Space.ThrCanon
import HtnComplexity.Space.SeqTests
/-!
# The initial and accepting tests of the thread machine

Layer (C) of the planner P-REG (`NOTES.md` §64–66), the Cobham half.  The machine guesses its
initial configuration — a list of numerals of initial facts of the thread table (`enc`) — and
checks it with the test `HTN.Space.Thr.thrInitB` defined here, against the code of the instance
and the advice (whose table starts with the two marker rows of P-TR; only the vocabulary marker
is used).

The pieces for the facts shared with P-TR (facts of the instance, `cur 0`, witness, label,
`nop` and `len` entries) are those of `HtnComplexity/Space/SeqTests.lean`.  New are the
entries of the three pair kinds `edge x y`, `cl x y`, `nc x y` (tags `011`, `111`, `110`, then
two doubled unary positions): the shape test `pairEnd`, and the comparisons `pos21` (second
position of a pair entry = first position of another entry) and `pos22` (second positions of
two pair entries agree).  The witness conditions are those of `HTN.Syn.SeqG.WitR`: injective on
all nodes (`pInjAll`), all numbers downward closed (`pDownAll`), no monotonicity.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

/-! ### Constants -/

/-- The tag of an `edge` entry. -/
def tE3 : List Bool := [false, true, true]

/-- The tag of a `cl` entry. -/
def tC3 : List Bool := [true, true, true]

/-- The tag of an `nc` entry. -/
def tN3 : List Bool := [true, true, false]

/-- Thirteen filler bits followed by `t`: an entry whose position part is `t`. -/
def shR (t : List Bool) : List Bool := List.replicate 13 false ++ t

/-! ### Pair entries -/

def pairEndBody (t b _ _ : List Bool) : Bool := isPosD (cutAt b t) && posEnd (shR t)

/-- **The entry ends with two positions** (the shape of `edge`, `cl`, `nc`). -/
def pairEnd (E : List Bool) : Bool := tailsE pairEndBody (E.drop 13) (E.drop 13) [] []

def pos21Body (t b E' _ : List Bool) : Bool := isPosD (cutAt b t) && samePos (shR t) E'

/-- **The second position of the pair entry `E` is the position of `E'`.** -/
def pos21 (E E' : List Bool) : Bool := tailsE pos21Body (E.drop 13) (E.drop 13) E' []

def pos22Body (t b E' _ : List Bool) : Bool := isPosD (cutAt b t) && pos21 E' (shR t)

/-- **The second positions of the pair entries `E` and `E'` agree.** -/
def pos22 (E E' : List Bool) : Bool := tailsE pos22Body (E.drop 13) (E.drop 13) E' []

/-- The two pair entries carry the same pair of positions. -/
def samePair (E E' : List Bool) : Bool := samePos E E' && pos22 E E'

/-! ### The new kinds of entries -/

def kEdgeW2 (W E P _ : List Bool) : Bool := witSnd W P && pos21 E W

def kEdgeW1 (W E P c : List Bool) : Bool := witFst W P && samePos W E && anyE kEdgeW2 c E P []

def kEdgeBody (P E c _ : List Bool) : Bool := anyE kEdgeW1 c E P c

/-- An `edge` entry, justified by a listed pair and the witness entries of its endpoints. -/
def kEdge (E c x : List Bool) : Bool :=
  decide (kp tE3 <+: E) && pairEnd E && atL 3 (anyE kEdgeBody) x E c []

/-- A `cl` entry (its positions are checked by `pPos`). -/
def kCl (E : List Bool) : Bool := decide (kp tC3 <+: E) && pairEnd E

def kNcBody (C E _ _ : List Bool) : Bool := !(decide (kp tC3 <+: C) && samePair E C)

/-- An `nc` entry, for a pair without a `cl` entry. -/
def kNc (E c : List Bool) : Bool :=
  decide (kp tN3 <+: E) && pairEnd E && allE kNcBody c E [] []

/-- **Every entry of the configuration is of one of the admitted kinds.** -/
def entryOkR (E c x a : List Bool) : Bool :=
  kInst E x || kCur E || witAny E x || kLab E c x || kNop E c a || kLen E c ||
    kEdge E c x || kCl E || kNc E c

/-! ### The new presence conditions -/

def pInjAllBody2 (E' E _ _ : List Bool) : Bool :=
  !(decide (kp tWit <+: E) && decide (kp tWit <+: E') && samePos E E') || decide (E = E')

def pInjAllBody1 (E c _ _ : List Bool) : Bool := allE pInjAllBody2 c E [] []

/-- Two witness entries with the same position are equal. -/
def pInjAll (c : List Bool) : Bool := allE pInjAllBody1 c c [] []

def pDownAllBody2 (E' E _ _ : List Bool) : Bool := decide (kp tWit <+: E') && succPos E' E

def pDownAllBody1 (E c _ _ : List Bool) : Bool :=
  !(decide (kp tWit <+: E)) || posZero E || anyE pDownAllBody2 c E [] []

/-- Every positive witness position has a witness entry at the preceding position. -/
def pDownAll (c : List Bool) : Bool := allE pDownAllBody1 c c [] []

def pEdgeBody3 (E W1 W2 _ : List Bool) : Bool :=
  decide (kp tE3 <+: E) && samePos W1 E && pos21 E W2

def pEdgeBody2 (W2 W1 P c : List Bool) : Bool :=
  !(witFst W1 P && witSnd W2 P) || anyE pEdgeBody3 c W1 W2 []

def pEdgeBody1 (W1 P c _ : List Bool) : Bool := allE pEdgeBody2 c W1 P c

def pEdgeBody0 (P c _ _ : List Bool) : Bool := allE pEdgeBody1 c P c []

/-- Every listed pair has the `edge` entry of the positions of its endpoints. -/
def pEdge (c x : List Bool) : Bool := atL 3 (allE pEdgeBody0) x c [] []

def pCl1Body2 (C E _ _ : List Bool) : Bool := decide (kp tC3 <+: C) && samePair E C

def pCl1Body1 (E c _ _ : List Bool) : Bool :=
  !(decide (kp tE3 <+: E)) || anyE pCl1Body2 c E [] []

/-- Every `edge` entry has the `cl` entry of the same pair. -/
def pCl1 (c : List Bool) : Bool := allE pCl1Body1 c c [] []

def pCl2Body3 (C' C E _ : List Bool) : Bool :=
  decide (kp tC3 <+: C') && samePos C C' && pos22 E C'

def pCl2Body2 (E C c _ : List Bool) : Bool :=
  !(decide (kp tE3 <+: E) && pos21 C E) || anyE pCl2Body3 c C E []

def pCl2Body1 (C c _ _ : List Bool) : Bool :=
  !(decide (kp tC3 <+: C)) || allE pCl2Body2 c C c []

/-- The `cl` entries are closed under following an `edge` entry. -/
def pCl2 (c : List Bool) : Bool := allE pCl2Body1 c c [] []

def pPosW1 (W C _ _ : List Bool) : Bool := decide (kp tWit <+: W) && samePos W C

def pPosW2 (W C _ _ : List Bool) : Bool := decide (kp tWit <+: W) && pos21 C W

def pPosBody (C c _ _ : List Bool) : Bool :=
  !(decide (kp tC3 <+: C) || decide (kp tN3 <+: C)) ||
    (anyE pPosW1 c C [] [] && anyE pPosW2 c C [] [])

/-- Both positions of a `cl` or `nc` entry carry witness entries. -/
def pPos (c : List Bool) : Bool := allE pPosBody c c [] []

def entryOkRBody (E c x a : List Bool) : Bool := entryOkR E c x a

/-- **The initial test of the thread machine.** -/
def thrInitB (c x a : List Bool) : Bool :=
  allE entryOkRBody c c x a && pInst c x && pCur c && pTotal c x && pEndp c x && pFunc c &&
    pInjAll c && pDown c x && pDownAll c && pLab c x && pNop c a && pLen c && pEdge c x &&
    pCl1 c && pCl2 c && pPos c

/-- **The accepting test of the thread machine**: the configuration carries the goal facts of
the instance (tagged) and `done`. -/
def thrAccB (c x : List Bool) : Bool := atL 1 (allE pInstBody) x c [] [] && occB c entFin

/-! ### The tests are predicates of Cobham's class -/

section Cobham

variable {a b c d : Fn}

local notation "p0" => cobham_p0
local notation "p1" => cobham_p1
local notation "p2" => cobham_p2
local notation "p3" => cobham_p3
local notation "cst" => cobham_const

theorem cobham_shR (ha : Cobham a) : Cobham fun args => shR (a args) :=
  cobham_app (cst _) ha

theorem cobhamB4_pairEndBody : CobhamB4 pairEndBody :=
  CobhamB4.of ((cobhamB_isPosD (cobham_cutAt p1 p0)).and (cobhamB_posEnd (cobham_shR p0)))

theorem cobhamB_pairEnd (ha : Cobham a) : CobhamB fun args => pairEnd (a args) :=
  (cobhamB4_tailsE cobhamB4_pairEndBody).app (cobham_dropK 13 ha) (cobham_dropK 13 ha)
    (cst []) (cst [])

theorem cobhamB4_pos21Body : CobhamB4 pos21Body :=
  CobhamB4.of ((cobhamB_isPosD (cobham_cutAt p1 p0)).and (cobhamB_samePos (cobham_shR p0) p2))

theorem cobhamB_pos21 (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => pos21 (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_pos21Body).app (cobham_dropK 13 ha) (cobham_dropK 13 ha) hb (cst [])

theorem cobhamB4_pos22Body : CobhamB4 pos22Body :=
  CobhamB4.of ((cobhamB_isPosD (cobham_cutAt p1 p0)).and (cobhamB_pos21 p2 (cobham_shR p0)))

theorem cobhamB_pos22 (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => pos22 (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_pos22Body).app (cobham_dropK 13 ha) (cobham_dropK 13 ha) hb (cst [])

theorem cobhamB_samePair (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => samePair (a args) (b args) :=
  (cobhamB_samePos ha hb).and (cobhamB_pos22 ha hb)

theorem cobhamB4_kEdgeW2 : CobhamB4 kEdgeW2 :=
  CobhamB4.of ((cobhamB_witSnd p0 p2).and (cobhamB_pos21 p1 p0))

theorem cobhamB4_kEdgeW1 : CobhamB4 kEdgeW1 :=
  CobhamB4.of (((cobhamB_witFst p0 p2).and (cobhamB_samePos p0 p1)).and
    ((cobhamB4_anyE cobhamB4_kEdgeW2).app p3 p1 p2 (cst [])))

theorem cobhamB4_kEdgeBody : CobhamB4 kEdgeBody :=
  CobhamB4.of ((cobhamB4_anyE cobhamB4_kEdgeW1).app p2 p1 p0 p2)

theorem cobhamB_kEdge (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => kEdge (a args) (b args) (c args) :=
  ((cobhamB_isPrefix (cst (kp tE3)) ha).and (cobhamB_pairEnd ha)).and
    ((cobhamB4_atL 3 (cobhamB4_anyE cobhamB4_kEdgeBody)).app hc ha hb (cst []))

theorem cobhamB_kCl (ha : Cobham a) : CobhamB fun args => kCl (a args) :=
  (cobhamB_isPrefix (cst (kp tC3)) ha).and (cobhamB_pairEnd ha)

theorem cobhamB4_kNcBody : CobhamB4 kNcBody :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tC3)) p0).and (cobhamB_samePair p1 p0)).not

theorem cobhamB_kNc (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => kNc (a args) (b args) :=
  ((cobhamB_isPrefix (cst (kp tN3)) ha).and (cobhamB_pairEnd ha)).and
    ((cobhamB4_allE cobhamB4_kNcBody).app hb ha (cst []) (cst []))

theorem cobhamB4_entryOkR : CobhamB4 entryOkR :=
  CobhamB4.of (((((((((cobhamB_kInst p0 p2).or (cobhamB_kCur p0)).or
    (cobhamB_witAny p0 p2)).or (cobhamB_kLab p0 p1 p2)).or (cobhamB_kNop p0 p1 p3)).or
    (cobhamB_kLen p0 p1)).or (cobhamB_kEdge p0 p1 p2)).or (cobhamB_kCl p0)).or
    (cobhamB_kNc p0 p1))

theorem cobhamB4_pInjAllBody2 : CobhamB4 pInjAllBody2 :=
  CobhamB4.of ((((cobhamB_isPrefix (cst (kp tWit)) p1).and
    (cobhamB_isPrefix (cst (kp tWit)) p0)).and (cobhamB_samePos p1 p0)).not.or
    (cobhamB_eqStr p1 p0))

theorem cobhamB4_pInjAllBody1 : CobhamB4 pInjAllBody1 :=
  CobhamB4.of ((cobhamB4_allE cobhamB4_pInjAllBody2).app p1 p0 (cst []) (cst []))

theorem cobhamB4_pDownAllBody2 : CobhamB4 pDownAllBody2 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tWit)) p0).and (cobhamB_succPos p0 p1))

theorem cobhamB4_pDownAllBody1 : CobhamB4 pDownAllBody1 :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tWit)) p0).not.or (cobhamB_posZero p0)).or
    ((cobhamB4_anyE cobhamB4_pDownAllBody2).app p1 p0 (cst []) (cst [])))

theorem cobhamB4_pEdgeBody3 : CobhamB4 pEdgeBody3 :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tE3)) p0).and (cobhamB_samePos p1 p0)).and
    (cobhamB_pos21 p0 p2))

theorem cobhamB4_pEdgeBody2 : CobhamB4 pEdgeBody2 :=
  CobhamB4.of (((cobhamB_witFst p1 p2).and (cobhamB_witSnd p0 p2)).not.or
    ((cobhamB4_anyE cobhamB4_pEdgeBody3).app p3 p1 p0 (cst [])))

theorem cobhamB4_pEdgeBody1 : CobhamB4 pEdgeBody1 :=
  CobhamB4.of ((cobhamB4_allE cobhamB4_pEdgeBody2).app p2 p0 p1 p2)

theorem cobhamB4_pEdgeBody0 : CobhamB4 pEdgeBody0 :=
  CobhamB4.of ((cobhamB4_allE cobhamB4_pEdgeBody1).app p1 p0 p1 (cst []))

theorem cobhamB4_pCl1Body2 : CobhamB4 pCl1Body2 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tC3)) p0).and (cobhamB_samePair p1 p0))

theorem cobhamB4_pCl1Body1 : CobhamB4 pCl1Body1 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tE3)) p0).not.or
    ((cobhamB4_anyE cobhamB4_pCl1Body2).app p1 p0 (cst []) (cst [])))

theorem cobhamB4_pCl2Body3 : CobhamB4 pCl2Body3 :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tC3)) p0).and (cobhamB_samePos p1 p0)).and
    (cobhamB_pos22 p2 p0))

theorem cobhamB4_pCl2Body2 : CobhamB4 pCl2Body2 :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tE3)) p0).and (cobhamB_pos21 p1 p0)).not.or
    ((cobhamB4_anyE cobhamB4_pCl2Body3).app p2 p1 p0 (cst [])))

theorem cobhamB4_pCl2Body1 : CobhamB4 pCl2Body1 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tC3)) p0).not.or
    ((cobhamB4_allE cobhamB4_pCl2Body2).app p1 p0 p1 (cst [])))

theorem cobhamB4_pPosW1 : CobhamB4 pPosW1 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tWit)) p0).and (cobhamB_samePos p0 p1))

theorem cobhamB4_pPosW2 : CobhamB4 pPosW2 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tWit)) p0).and (cobhamB_pos21 p1 p0))

theorem cobhamB4_pPosBody : CobhamB4 pPosBody :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tC3)) p0).or
    (cobhamB_isPrefix (cst (kp tN3)) p0)).not.or
    (((cobhamB4_anyE cobhamB4_pPosW1).app p1 p0 (cst []) (cst [])).and
      ((cobhamB4_anyE cobhamB4_pPosW2).app p1 p0 (cst []) (cst []))))

/-- **The initial test is a predicate of Cobham's class.** -/
theorem cobhamB_thrInitB (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => thrInitB (a args) (b args) (c args) := by
  have h1 := (cobhamB4_allE (CobhamB4.of (P := entryOkRBody)
    (cobhamB4_entryOkR.app p0 p1 p2 p3))).app ha ha hb hc
  have h2 := (cobhamB4_allE cobhamB4_pInstBody).app hb ha (cst []) (cst [])
  have h4 := cobhamB_occB ha (cst entCur0)
  have h5 := (cobhamB4_atL 2 (cobhamB4_allE cobhamB4_pTotalBody1)).app hb ha (cst []) (cst [])
  have h6 := (cobhamB4_atL 3 (cobhamB4_allE cobhamB4_pEndpBody)).app hb ha (cst []) (cst [])
  have h7 := (cobhamB4_allE cobhamB4_pFuncBody1).app ha ha (cst []) (cst [])
  have h8 := (cobhamB4_allE cobhamB4_pInjAllBody1).app ha ha (cst []) (cst [])
  have h9 := (cobhamB4_allE cobhamB4_pDownBody1).app ha ha hb (cst [])
  have h10 := (cobhamB4_allE cobhamB4_pDownAllBody1).app ha ha (cst []) (cst [])
  have h11 := (cobhamB4_allE cobhamB4_pLabBody1).app ha ha hb (cst [])
  have h12 := (cobhamB4_allE cobhamB4_pNopBody1).app ha ha hc (cst [])
  have h13 := (cobhamB4_anyE cobhamB4_pLenBody).app ha (cst []) (cst []) (cst [])
  have h14 := (cobhamB4_atL 3 (cobhamB4_allE cobhamB4_pEdgeBody0)).app hb ha (cst []) (cst [])
  have h15 := (cobhamB4_allE cobhamB4_pCl1Body1).app ha ha (cst []) (cst [])
  have h16 := (cobhamB4_allE cobhamB4_pCl2Body1).app ha ha (cst []) (cst [])
  have h17 := (cobhamB4_allE cobhamB4_pPosBody).app ha ha (cst []) (cst [])
  exact h1.and h2 |>.and h4 |>.and h5 |>.and h6 |>.and h7 |>.and h8 |>.and h9 |>.and h10
    |>.and h11 |>.and h12 |>.and h13 |>.and h14 |>.and h15 |>.and h16 |>.and h17

/-- **The accepting test is a predicate of Cobham's class.** -/
theorem cobhamB_thrAccB (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => thrAccB (a args) (b args) :=
  ((cobhamB4_atL 1 (cobhamB4_allE cobhamB4_pInstBody)).app hb ha (cst []) (cst [])).and
    (cobhamB_occB ha (cst entFin))

end Cobham

end Thr

end Space

end HTN
