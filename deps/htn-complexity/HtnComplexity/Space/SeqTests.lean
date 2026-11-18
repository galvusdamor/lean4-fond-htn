import HtnComplexity.Space.SeqStr
/-!
# The initial and accepting tests of the gadget machine

Step A3 of `TABLE4-PLAN.md`, the Cobham half.  The machine for unrooted totally ordered
instances guesses its initial configuration — the compiled initial state of a gadget instance,
rank witnesses included — and checks it with the test `HTN.Space.SeqM.seqInitB` defined here.
The test reads three strings: the configuration `c` (a serialised list of canonical numerals),
the code `x` of the instance, and the advice `a` (the action table, whose first two rows are
no-op *marker rows* announcing the root task of the gadget and the primitive names the domain
mentions).

The test is a conjunction of quantifications over entries (`HTN.Space.SeqM.entryOk` for every
entry of the configuration, and twelve presence conditions).  This file defines the tests and
proves that they are predicates of Cobham's class; what they mean is
`HtnComplexity/Space/SeqSem1.lean` … `SeqSem7.lean`.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### Constants -/

/-- The tag of a compiled gadget fact: `4 · gf g + 2` is `[false, true, false] ++ gbits g`. -/
def gT : List Bool := [false, true, false]

/-- The tag of a compiled fact of the instance. -/
def tagI3 : List Bool := [false, true, true]

def tCur : List Bool := [false, false, false]
def tLen : List Bool := [true, false, false]
def tNop : List Bool := [false, true, false]
def tLab : List Bool := [false, false, true]
def tWit : List Bool := [true, false, true]

/-- The encoded prefix of the entries of one kind of gadget fact (13 bits). -/
def kp (tg : List Bool) : List Bool := true :: dbl (gT ++ tg)

/-- The closing bits `dbl [true] ++ [false]` of a label or witness entry. -/
def ttf : List Bool := [true, true, false]

/-- The name of the first marker row (the root marker). -/
def U0 : List Bool := [true, true, false, false]

/-- The encoded prefix of an entry of the second marker row (the vocabulary marker). -/
def markA : List Bool := true :: dbl [true, false, false, false]

/-- The entry of the fact `cur 0`. -/
def entCur0 : List Bool := true :: bstr (gT ++ gbits (.cur 0))

/-- The entry of the fact `fin`. -/
def entFin : List Bool := true :: bstr (gT ++ gbits .fin)

/-! ### Witness entries -/

/-- **The entry `E` is a witness entry whose node is serialised, doubled, as `D`.** -/
def witNode (E D : List Bool) : Bool :=
  decide (kp tWit <+: E) && decide ((D ++ ttf) <:+ E) && isPosD (cutAt (E.drop 13) (D ++ ttf))

def witIdBody (I E _ _ : List Bool) : Bool := witNode E (dbl I.tail)

/-- **The node of the witness entry `E` is an identifier of the instance coded by `x`.** -/
def witId (E x : List Bool) : Bool := atL 2 (anyE witIdBody) x E [] []

def witFstBody (t Pt E _ : List Bool) : Bool := isBD (cutAt Pt t) && witNode E (cutAt Pt t)

/-- The node of `E` is the first endpoint of the ordering pair entry `P`. -/
def witFst (E P : List Bool) : Bool := tailsE witFstBody P.tail P.tail E []

def witSndBody (t Pt E _ : List Bool) : Bool :=
  isBD (cutAt Pt t) && isBD (t.take (t.length - 1)) && decide ([false] <:+ t) &&
    witNode E (t.take (t.length - 1))

/-- The node of `E` is the second endpoint of the ordering pair entry `P`. -/
def witSnd (E P : List Bool) : Bool := tailsE witSndBody P.tail P.tail E []

def witPairBody (P E _ _ : List Bool) : Bool := witFst E P || witSnd E P

/-- **The node of the witness entry `E` is an identifier or an endpoint of a listed pair.** -/
def witAny (E x : List Bool) : Bool := witId E x || atL 3 (anyE witPairBody) x E [] []

/-! ### Positions -/

def samePosBody (t b b' _ : List Bool) : Bool := isPosD (cutAt b t) && decide (cutAt b t <+: b')

/-- The two gadget entries have the same position. -/
def samePos (E E' : List Bool) : Bool := tailsE samePosBody (E.drop 13) (E.drop 13) (E'.drop 13) []

def succPosBody (t b b' _ : List Bool) : Bool :=
  isPosD (cutAt b t) && decide (([true, false] ++ cutAt b t) <+: b')

/-- The position of `E'` is the successor of the position of `E`. -/
def succPos (E E' : List Bool) : Bool := tailsE succPosBody (E.drop 13) (E.drop 13) (E'.drop 13) []

def lePosBody (t b b' _ : List Bool) : Bool :=
  isPosD (cutAt b t) && decide ((cutAt b t).take ((cutAt b t).length - 2) <+: b')

/-- The position of `E` is at most the position of `E'`. -/
def lePos (E E' : List Bool) : Bool := tailsE lePosBody (E.drop 13) (E.drop 13) (E'.drop 13) []

/-- The position of `E` is `0`. -/
def posZero (E : List Bool) : Bool := decide ([true, true] <+: E.drop 13)

def sameNodeBody (t b b' _ : List Bool) : Bool :=
  isPosD (cutAt b t) && decide (t <:+ b') && isPosD (cutAt b' t)

/-- The two witness entries have the same node. -/
def sameNode (E E' : List Bool) : Bool :=
  tailsE sameNodeBody (E.drop 13) (E.drop 13) (E'.drop 13) []

/-- The entry ends right after its position (the shape of `cur`, `len`, `nop`). -/
def posEnd (E : List Bool) : Bool :=
  isPosD ((E.drop 13).take ((E.drop 13).length - 1)) && decide ([false] <:+ E.drop 13)

/-! ### Labels -/

/-- The body of the first-label lookup with a doubled label. -/
def lblTestD (t y w DK : List Bool) : Bool :=
  entriesB (cutAt y t) && decide ((true :: (dbl w ++ DK ++ [false])) <+: t) &&
    !occB (cutAt y t ++ [false]) (true :: dbl w)

/-- **The first entry of the label list `y` with key `w` is `w` followed by the doubled `DK`.** -/
def firstLblD (y w DK : List Bool) : Bool := tailsE lblTestD y y w DK

/-- **The label of the identifier serialised as `w` is the task doubled as `DK`**, the default
label `inl 0` included. -/
def labelD (y w DK : List Bool) : Bool :=
  isDblD DK &&
    (firstLblD y w DK || (!occB y (true :: dbl w) && decide (DK = [true, false, true, false])))

/-- The position part of the witness entry `E'` of the identifier entry `I`. -/
def zOf (E' I : List Bool) : List Bool := cutAt (E'.drop 13) (dbl I.tail ++ ttf)

/-- The doubled label part of the label entry `E`, after a position part `Z`. -/
def dkOf (E Z : List Bool) : List Bool := cutAt ((E.drop 13).drop Z.length) ttf

/-- **`E` is the label entry for the position of the witness entry `E'` of the identifier entry
`I`**, the label list being `y`. -/
def labOk (E E' I y : List Bool) : Bool :=
  decide (E = kp tLab ++ zOf E' I ++ dkOf E (zOf E' I) ++ ttf) &&
    labelD y I.tail (dkOf E (zOf E' I))

def labOkBody (y E E' I : List Bool) : Bool := labOk E E' I y

/-- `labOk`, the label list read off the code `x`. -/
def labOkX (E E' I x : List Bool) : Bool := atL 4 labOkBody x E E' I

/-! ### The advice -/

def advOccBody (y M _ _ : List Bool) : Bool := occB y M

/-- The entry `M` occurs among the fact entries of the advice `a`. -/
def advOcc (a M : List Bool) : Bool := atL 1 advOccBody a M [] []

def unknownBody (t b a _ : List Bool) : Bool :=
  isPosD (cutAt b t) && decide ([true, false] <+: t) && !advOcc a (markA ++ t.drop 2)

/-- **The label entry `E'` carries a primitive task the domain does not mention.** -/
def unknownD (E' a : List Bool) : Bool := tailsE unknownBody (E'.drop 13) (E'.drop 13) a []

/-! ### The kinds of entries -/

def kInstBody (J E _ _ : List Bool) : Bool := decide (E = preEnt tagI3 J)

/-- A fact of the instance, tagged. -/
def kInst (E x : List Bool) : Bool := anyE kInstBody x E [] []

/-- The root task (announced by the first marker row). -/
def kRoot (E a : List Bool) : Bool := advOcc a (mkEnt tagPrec U0 E)

/-- The fact `cur 0`. -/
def kCur (E : List Bool) : Bool := decide (E = entCur0)

def kLabBody2 (I E' E x : List Bool) : Bool := witNode E' (dbl I.tail) && labOkX E E' I x

def kLabBody1 (E' E x _ : List Bool) : Bool := atL 2 (anyE kLabBody2) x E' E x

/-- A label entry, justified by a witness entry and the label list. -/
def kLab (E c x : List Bool) : Bool := decide (kp tLab <+: E) && anyE kLabBody1 c E x []

def kNopBody (E' E a _ : List Bool) : Bool :=
  decide (kp tLab <+: E') && samePos E E' && unknownD E' a

/-- A `nop` entry, justified by a label entry with an unknown primitive task. -/
def kNop (E c a : List Bool) : Bool :=
  decide (kp tNop <+: E) && posEnd E && anyE kNopBody c E a []

def kLenBody1 (E' E _ _ : List Bool) : Bool := !(decide (kp tLab <+: E') && samePos E E')

def kLenBody2 (E' E _ _ : List Bool) : Bool := decide (kp tLab <+: E') && succPos E' E

/-- A `len` entry, at the first position without a label entry. -/
def kLen (E c : List Bool) : Bool :=
  decide (kp tLen <+: E) && posEnd E && allE kLenBody1 c E [] [] &&
    (posZero E || anyE kLenBody2 c E [] [])

/-- **Every entry of the configuration is of one of the admitted kinds.** -/
def entryOk (E c x a : List Bool) : Bool :=
  kInst E x || kRoot E a || kCur E || witAny E x || kLab E c x || kNop E c a || kLen E c

/-! ### The presence conditions -/

def pInstBody (J c _ _ : List Bool) : Bool := occB c (preEnt tagI3 J)

def pInst (c x : List Bool) : Bool := allE pInstBody x c [] []

def pRootBody (E a _ _ : List Bool) : Bool := kRoot E a

def pRoot (c a : List Bool) : Bool := anyE pRootBody c a [] []

def pCur (c : List Bool) : Bool := occB c entCur0

def pTotalBody2 (E I _ _ : List Bool) : Bool := witNode E (dbl I.tail)

def pTotalBody1 (I c _ _ : List Bool) : Bool := anyE pTotalBody2 c I [] []

def pTotal (c x : List Bool) : Bool := atL 2 (allE pTotalBody1) x c [] []

def pEndpFst (E P _ _ : List Bool) : Bool := witFst E P

def pEndpSnd (E P _ _ : List Bool) : Bool := witSnd E P

def pEndpBody (P c _ _ : List Bool) : Bool := anyE pEndpFst c P [] [] && anyE pEndpSnd c P [] []

def pEndp (c x : List Bool) : Bool := atL 3 (allE pEndpBody) x c [] []

def pFuncBody2 (E' E _ _ : List Bool) : Bool :=
  !(decide (kp tWit <+: E) && decide (kp tWit <+: E') && sameNode E E') || decide (E = E')

def pFuncBody1 (E c _ _ : List Bool) : Bool := allE pFuncBody2 c E [] []

def pFunc (c : List Bool) : Bool := allE pFuncBody1 c c [] []

def pInjBody2 (E' E x _ : List Bool) : Bool :=
  !(witId E x && witId E' x && samePos E E') || decide (E = E')

def pInjBody1 (E c x _ : List Bool) : Bool := allE pInjBody2 c E x []

def pInj (c x : List Bool) : Bool := allE pInjBody1 c c x []

def pDownBody2 (E' E x _ : List Bool) : Bool := witId E' x && succPos E' E

def pDownBody1 (E c x _ : List Bool) : Bool :=
  !(witId E x) || posZero E || anyE pDownBody2 c E x []

def pDown (c x : List Bool) : Bool := allE pDownBody1 c c x []

def pMonoBody3 (E' E P _ : List Bool) : Bool := !(witFst E P && witSnd E' P) || lePos E E'

def pMonoBody2 (E P c _ : List Bool) : Bool := allE pMonoBody3 c E P []

def pMonoBody1 (P c _ _ : List Bool) : Bool := allE pMonoBody2 c P c []

def pMono (c x : List Bool) : Bool := atL 3 (allE pMonoBody1) x c [] []

def pLabBody2 (I E' c x : List Bool) : Bool :=
  !(witNode E' (dbl I.tail)) || anyE labOkX c E' I x

def pLabBody1 (E' c x _ : List Bool) : Bool := atL 2 (allE pLabBody2) x E' c x

def pLab (c x : List Bool) : Bool := allE pLabBody1 c c x []

def pNopBody2 (E E' _ _ : List Bool) : Bool :=
  decide (kp tNop <+: E) && posEnd E && samePos E' E

def pNopBody1 (E' c a _ : List Bool) : Bool :=
  !(decide (kp tLab <+: E') && unknownD E' a) || anyE pNopBody2 c E' [] []

def pNop (c a : List Bool) : Bool := allE pNopBody1 c c a []

def pLenBody (E _ _ _ : List Bool) : Bool := decide (kp tLen <+: E) && posEnd E

def pLen (c : List Bool) : Bool := anyE pLenBody c [] [] []

def pBndBody2 (E' E _ _ : List Bool) : Bool := !(decide (kp tLen <+: E')) || lePos E E'

def pBndBody1 (E c _ _ : List Bool) : Bool :=
  !(decide (kp tWit <+: E)) || allE pBndBody2 c E [] []

/-- Every witness position is at most the position of the `len` entry. -/
def pBnd (c : List Bool) : Bool := allE pBndBody1 c c [] []

def entryOkBody (E c x a : List Bool) : Bool := entryOk E c x a

/-- **The initial test of the gadget machine.** -/
def seqInitB (c x a : List Bool) : Bool :=
  allE entryOkBody c c x a && pInst c x && pRoot c a && pCur c && pTotal c x && pEndp c x &&
    pFunc c && pInj c x && pDown c x && pMono c x && pLab c x && pNop c a && pLen c && pBnd c

/-- **The accepting test of the gadget machine**: the flag bit of the advice is set, and the
configuration carries the goal facts of the instance (tagged), `fin` and the fact `0`. -/
def seqAccB (c x a : List Bool) : Bool :=
  (a.reverse.headD false) && atL 1 (allE pInstBody) x c [] [] && occB c entFin && occB c nilEnt

/-! ### The tests are predicates of Cobham's class -/

section Cobham

variable {a b c d : Fn}

local notation "p0" => cobham_p0
local notation "p1" => cobham_p1
local notation "p2" => cobham_p2
local notation "p3" => cobham_p3
local notation "cst" => cobham_const

theorem cobhamB_witNode (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => witNode (a args) (b args) :=
  (((cobhamB_isPrefix (cst (kp tWit)) ha).and
    (cobhamB_isSuffix (cobham_app hb (cst ttf)) ha)).and
    (cobhamB_isPosD (cobham_cutAt (cobham_dropK 13 ha) (cobham_app hb (cst ttf))))).of_eq
      fun _ => rfl

theorem cobhamB4_witIdBody : CobhamB4 witIdBody :=
  CobhamB4.of (cobhamB_witNode p1 (cobham_dbl (cobham_tl p0)))

theorem cobhamB_witId (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => witId (a args) (b args) :=
  (cobhamB4_atL 2 (cobhamB4_anyE cobhamB4_witIdBody)).app hb ha (cst []) (cst [])

theorem cobhamB4_witFstBody : CobhamB4 witFstBody :=
  CobhamB4.of ((cobhamB_isBD (cobham_cutAt p1 p0)).and (cobhamB_witNode p2 (cobham_cutAt p1 p0)))

theorem cobhamB_witFst (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => witFst (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_witFstBody).app (cobham_tl hb) (cobham_tl hb) ha (cst [])

theorem cobhamB4_witSndBody : CobhamB4 witSndBody :=
  CobhamB4.of ((((cobhamB_isBD (cobham_cutAt p1 p0)).and
    (cobhamB_isBD (cobham_dropLastK 1 p0))).and
    (cobhamB_isSuffix (cst [false]) p0)).and (cobhamB_witNode p2 (cobham_dropLastK 1 p0)))

theorem cobhamB_witSnd (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => witSnd (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_witSndBody).app (cobham_tl hb) (cobham_tl hb) ha (cst [])

theorem cobhamB4_witPairBody : CobhamB4 witPairBody :=
  CobhamB4.of ((cobhamB_witFst p1 p0).or (cobhamB_witSnd p1 p0))

theorem cobhamB_witAny (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => witAny (a args) (b args) :=
  (cobhamB_witId ha hb).or
    ((cobhamB4_atL 3 (cobhamB4_anyE cobhamB4_witPairBody)).app hb ha (cst []) (cst []))

theorem cobhamB4_samePosBody : CobhamB4 samePosBody :=
  CobhamB4.of ((cobhamB_isPosD (cobham_cutAt p1 p0)).and
    (cobhamB_isPrefix (cobham_cutAt p1 p0) p2))

theorem cobhamB_samePos (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => samePos (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_samePosBody).app (cobham_dropK 13 ha) (cobham_dropK 13 ha)
    (cobham_dropK 13 hb) (cst [])

theorem cobhamB4_succPosBody : CobhamB4 succPosBody :=
  CobhamB4.of ((cobhamB_isPosD (cobham_cutAt p1 p0)).and
    (cobhamB_isPrefix (cobham_app (cst [true, false]) (cobham_cutAt p1 p0)) p2))

theorem cobhamB_succPos (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => succPos (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_succPosBody).app (cobham_dropK 13 ha) (cobham_dropK 13 ha)
    (cobham_dropK 13 hb) (cst [])

theorem cobhamB4_lePosBody : CobhamB4 lePosBody :=
  CobhamB4.of ((cobhamB_isPosD (cobham_cutAt p1 p0)).and
    (cobhamB_isPrefix (cobham_dropLastK 2 (cobham_cutAt p1 p0)) p2))

theorem cobhamB_lePos (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => lePos (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_lePosBody).app (cobham_dropK 13 ha) (cobham_dropK 13 ha)
    (cobham_dropK 13 hb) (cst [])

theorem cobhamB_posZero (ha : Cobham a) : CobhamB fun args => posZero (a args) :=
  cobhamB_isPrefix (cst [true, true]) (cobham_dropK 13 ha)

theorem cobhamB4_sameNodeBody : CobhamB4 sameNodeBody :=
  CobhamB4.of (((cobhamB_isPosD (cobham_cutAt p1 p0)).and (cobhamB_isSuffix p0 p2)).and
    (cobhamB_isPosD (cobham_cutAt p2 p0)))

theorem cobhamB_sameNode (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => sameNode (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_sameNodeBody).app (cobham_dropK 13 ha) (cobham_dropK 13 ha)
    (cobham_dropK 13 hb) (cst [])

theorem cobhamB_posEnd (ha : Cobham a) : CobhamB fun args => posEnd (a args) :=
  (cobhamB_isPosD (cobham_dropLastK 1 (cobham_dropK 13 ha))).and
    (cobhamB_isSuffix (cst [false]) (cobham_dropK 13 ha))

theorem cobhamB4_lblTestD : CobhamB4 lblTestD :=
  CobhamB4.of (((cobhamB_entriesB (cobham_cutAt p1 p0)).and
    (cobhamB_isPrefix (cobham_consT (cobham_app (cobham_app (cobham_dbl p2) p3)
      (cst [false]))) p0)).and
    (cobhamB_occB (cobham_app (cobham_cutAt p1 p0) (cst [false]))
      (cobham_consT (cobham_dbl p2))).not)

theorem cobhamB_labelD (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => labelD (a args) (b args) (c args) :=
  (cobhamB_isDblD hc).and (((cobhamB4_tailsE cobhamB4_lblTestD).app ha ha hb hc).or
    ((cobhamB_occB ha (cobham_consT (cobham_dbl hb))).not.and
      (cobhamB_eqStr hc (cst [true, false, true, false]))))

theorem cobham_zOf (ha : Cobham a) (hb : Cobham b) : Cobham fun args => zOf (a args) (b args) :=
  cobham_cutAt (cobham_dropK 13 ha) (cobham_app (cobham_dbl (cobham_tl hb)) (cst ttf))

theorem cobham_dkOf (ha : Cobham a) (hb : Cobham b) : Cobham fun args => dkOf (a args) (b args) :=
  cobham_cutAt (cobham_drop hb (cobham_dropK 13 ha)) (cst ttf)

theorem cobhamB_labOk (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) (hd : Cobham d) :
    CobhamB fun args => labOk (a args) (b args) (c args) (d args) :=
  (cobhamB_eqStr ha (cobham_app (cobham_app (cobham_app (cst (kp tLab)) (cobham_zOf hb hc))
    (cobham_dkOf ha (cobham_zOf hb hc))) (cst ttf))).and
    (cobhamB_labelD hd (cobham_tl hc) (cobham_dkOf ha (cobham_zOf hb hc)))

theorem cobhamB4_labOkX : CobhamB4 labOkX :=
  CobhamB4.of ((cobhamB4_atL 4 (CobhamB4.of (P := labOkBody) (cobhamB_labOk p1 p2 p3 p0))).app
    p3 p0 p1 p2)

theorem cobhamB_advOcc (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => advOcc (a args) (b args) :=
  (cobhamB4_atL 1 (CobhamB4.of (P := advOccBody) (cobhamB_occB p0 p1))).app ha hb (cst []) (cst [])

theorem cobhamB4_unknownBody : CobhamB4 unknownBody :=
  CobhamB4.of (((cobhamB_isPosD (cobham_cutAt p1 p0)).and
    (cobhamB_isPrefix (cst [true, false]) p0)).and
    (cobhamB_advOcc p2 (cobham_app (cst markA) (cobham_dropK 2 p0))).not)

theorem cobhamB_unknownD (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => unknownD (a args) (b args) :=
  (cobhamB4_tailsE cobhamB4_unknownBody).app (cobham_dropK 13 ha) (cobham_dropK 13 ha) hb (cst [])

theorem cobhamB_kInst (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => kInst (a args) (b args) :=
  (cobhamB4_anyE (CobhamB4.of (P := kInstBody) (cobhamB_eqStr p1 (cobham_preEnt tagI3 p0)))).app
    hb ha (cst []) (cst [])

theorem cobhamB_kRoot (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => kRoot (a args) (b args) :=
  cobhamB_advOcc hb (cobham_mkEnt tagPrec (cst U0) ha)

theorem cobhamB_kCur (ha : Cobham a) : CobhamB fun args => kCur (a args) :=
  cobhamB_eqStr ha (cst entCur0)

theorem cobhamB4_kLabBody2 : CobhamB4 kLabBody2 :=
  CobhamB4.of ((cobhamB_witNode p1 (cobham_dbl (cobham_tl p0))).and
    (cobhamB4_labOkX.app p2 p1 p0 p3))

theorem cobhamB4_kLabBody1 : CobhamB4 kLabBody1 :=
  CobhamB4.of ((cobhamB4_atL 2 (cobhamB4_anyE cobhamB4_kLabBody2)).app p2 p0 p1 p2)

theorem cobhamB_kLab (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => kLab (a args) (b args) (c args) :=
  (cobhamB_isPrefix (cst (kp tLab)) ha).and ((cobhamB4_anyE cobhamB4_kLabBody1).app hb ha hc (cst []))

theorem cobhamB4_kNopBody : CobhamB4 kNopBody :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tLab)) p0).and (cobhamB_samePos p1 p0)).and
    (cobhamB_unknownD p0 p2))

theorem cobhamB_kNop (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => kNop (a args) (b args) (c args) :=
  ((cobhamB_isPrefix (cst (kp tNop)) ha).and (cobhamB_posEnd ha)).and
    ((cobhamB4_anyE cobhamB4_kNopBody).app hb ha hc (cst []))

theorem cobhamB4_kLenBody1 : CobhamB4 kLenBody1 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tLab)) p0).and (cobhamB_samePos p1 p0)).not

theorem cobhamB4_kLenBody2 : CobhamB4 kLenBody2 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tLab)) p0).and (cobhamB_succPos p0 p1))

theorem cobhamB_kLen (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => kLen (a args) (b args) :=
  (((cobhamB_isPrefix (cst (kp tLen)) ha).and (cobhamB_posEnd ha)).and
    ((cobhamB4_allE cobhamB4_kLenBody1).app hb ha (cst []) (cst []))).and
    ((cobhamB_posZero ha).or ((cobhamB4_anyE cobhamB4_kLenBody2).app hb ha (cst []) (cst [])))

theorem cobhamB4_entryOk : CobhamB4 entryOk :=
  CobhamB4.of (((((((cobhamB_kInst p0 p2).or (cobhamB_kRoot p0 p3)).or (cobhamB_kCur p0)).or
    (cobhamB_witAny p0 p2)).or (cobhamB_kLab p0 p1 p2)).or (cobhamB_kNop p0 p1 p3)).or
    (cobhamB_kLen p0 p1))

theorem cobhamB4_pInstBody : CobhamB4 pInstBody :=
  CobhamB4.of (cobhamB_occB p1 (cobham_preEnt tagI3 p0))

theorem cobhamB4_pRootBody : CobhamB4 pRootBody := CobhamB4.of (cobhamB_kRoot p0 p1)

theorem cobhamB4_pTotalBody1 : CobhamB4 pTotalBody1 :=
  CobhamB4.of ((cobhamB4_anyE (CobhamB4.of (P := pTotalBody2)
    (cobhamB_witNode p0 (cobham_dbl (cobham_tl p1))))).app p1 p0 (cst []) (cst []))

theorem cobhamB4_pEndpBody : CobhamB4 pEndpBody :=
  CobhamB4.of (((cobhamB4_anyE (CobhamB4.of (P := pEndpFst) (cobhamB_witFst p0 p1))).app p1 p0
    (cst []) (cst [])).and
    ((cobhamB4_anyE (CobhamB4.of (P := pEndpSnd) (cobhamB_witSnd p0 p1))).app p1 p0
      (cst []) (cst [])))

theorem cobhamB4_pFuncBody2 : CobhamB4 pFuncBody2 :=
  CobhamB4.of ((((cobhamB_isPrefix (cst (kp tWit)) p1).and
    (cobhamB_isPrefix (cst (kp tWit)) p0)).and (cobhamB_sameNode p1 p0)).not.or
    (cobhamB_eqStr p1 p0))

theorem cobhamB4_pFuncBody1 : CobhamB4 pFuncBody1 :=
  CobhamB4.of ((cobhamB4_allE cobhamB4_pFuncBody2).app p1 p0 (cst []) (cst []))

theorem cobhamB4_pInjBody2 : CobhamB4 pInjBody2 :=
  CobhamB4.of ((((cobhamB_witId p1 p2).and (cobhamB_witId p0 p2)).and
    (cobhamB_samePos p1 p0)).not.or (cobhamB_eqStr p1 p0))

theorem cobhamB4_pInjBody1 : CobhamB4 pInjBody1 :=
  CobhamB4.of ((cobhamB4_allE cobhamB4_pInjBody2).app p1 p0 p2 (cst []))

theorem cobhamB4_pDownBody2 : CobhamB4 pDownBody2 :=
  CobhamB4.of ((cobhamB_witId p0 p2).and (cobhamB_succPos p0 p1))

theorem cobhamB4_pDownBody1 : CobhamB4 pDownBody1 :=
  CobhamB4.of (((cobhamB_witId p0 p2).not.or (cobhamB_posZero p0)).or
    ((cobhamB4_anyE cobhamB4_pDownBody2).app p1 p0 p2 (cst [])))

theorem cobhamB4_pMonoBody3 : CobhamB4 pMonoBody3 :=
  CobhamB4.of (((cobhamB_witFst p1 p2).and (cobhamB_witSnd p0 p2)).not.or (cobhamB_lePos p1 p0))

theorem cobhamB4_pMonoBody2 : CobhamB4 pMonoBody2 :=
  CobhamB4.of ((cobhamB4_allE cobhamB4_pMonoBody3).app p2 p0 p1 (cst []))

theorem cobhamB4_pMonoBody1 : CobhamB4 pMonoBody1 :=
  CobhamB4.of ((cobhamB4_allE cobhamB4_pMonoBody2).app p1 p0 p1 (cst []))

theorem cobhamB4_pLabBody2 : CobhamB4 pLabBody2 :=
  CobhamB4.of ((cobhamB_witNode p1 (cobham_dbl (cobham_tl p0))).not.or
    ((cobhamB4_anyE cobhamB4_labOkX).app p2 p1 p0 p3))

theorem cobhamB4_pLabBody1 : CobhamB4 pLabBody1 :=
  CobhamB4.of ((cobhamB4_atL 2 (cobhamB4_allE cobhamB4_pLabBody2)).app p2 p0 p1 p2)

theorem cobhamB4_pNopBody2 : CobhamB4 pNopBody2 :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tNop)) p0).and (cobhamB_posEnd p0)).and
    (cobhamB_samePos p1 p0))

theorem cobhamB4_pNopBody1 : CobhamB4 pNopBody1 :=
  CobhamB4.of (((cobhamB_isPrefix (cst (kp tLab)) p0).and (cobhamB_unknownD p0 p2)).not.or
    ((cobhamB4_anyE cobhamB4_pNopBody2).app p1 p0 (cst []) (cst [])))

theorem cobhamB4_pLenBody : CobhamB4 pLenBody :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tLen)) p0).and (cobhamB_posEnd p0))

theorem cobhamB4_pBndBody2 : CobhamB4 pBndBody2 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tLen)) p0).not.or (cobhamB_lePos p1 p0))

theorem cobhamB4_pBndBody1 : CobhamB4 pBndBody1 :=
  CobhamB4.of ((cobhamB_isPrefix (cst (kp tWit)) p0).not.or
    ((cobhamB4_allE cobhamB4_pBndBody2).app p1 p0 (cst []) (cst [])))

/-- **The initial test is a predicate of Cobham's class.** -/
theorem cobhamB_seqInitB (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => seqInitB (a args) (b args) (c args) := by
  have h1 := (cobhamB4_allE (CobhamB4.of (P := entryOkBody)
    (cobhamB4_entryOk.app p0 p1 p2 p3))).app ha ha hb hc
  have h2 := (cobhamB4_allE cobhamB4_pInstBody).app hb ha (cst []) (cst [])
  have h3 := (cobhamB4_anyE cobhamB4_pRootBody).app ha hc (cst []) (cst [])
  have h4 := cobhamB_occB ha (cst entCur0)
  have h5 := (cobhamB4_atL 2 (cobhamB4_allE cobhamB4_pTotalBody1)).app hb ha (cst []) (cst [])
  have h6 := (cobhamB4_atL 3 (cobhamB4_allE cobhamB4_pEndpBody)).app hb ha (cst []) (cst [])
  have h7 := (cobhamB4_allE cobhamB4_pFuncBody1).app ha ha (cst []) (cst [])
  have h8 := (cobhamB4_allE cobhamB4_pInjBody1).app ha ha hb (cst [])
  have h9 := (cobhamB4_allE cobhamB4_pDownBody1).app ha ha hb (cst [])
  have h10 := (cobhamB4_atL 3 (cobhamB4_allE cobhamB4_pMonoBody1)).app hb ha (cst []) (cst [])
  have h11 := (cobhamB4_allE cobhamB4_pLabBody1).app ha ha hb (cst [])
  have h12 := (cobhamB4_allE cobhamB4_pNopBody1).app ha ha hc (cst [])
  have h13 := (cobhamB4_anyE cobhamB4_pLenBody).app ha (cst []) (cst []) (cst [])
  have h14 := (cobhamB4_allE cobhamB4_pBndBody1).app ha ha (cst []) (cst [])
  exact h1.and h2 |>.and h3 |>.and h4 |>.and h5 |>.and h6 |>.and h7 |>.and h8 |>.and h9
    |>.and h10 |>.and h11 |>.and h12 |>.and h13 |>.and h14

/-- **The accepting test is a predicate of Cobham's class.** -/
theorem cobhamB_seqAccB (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => seqAccB (a args) (b args) (c args) :=
  (((cobhamB_head (cobham_rev hc)).and
    ((cobhamB4_atL 1 (cobhamB4_allE cobhamB4_pInstBody)).app hb ha (cst []) (cst []))).and
    (cobhamB_occB ha (cst entFin))).and (cobhamB_occB ha (cst nilEnt))

end Cobham

end SeqM

end Space

end HTN
