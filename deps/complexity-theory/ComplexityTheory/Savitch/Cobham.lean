import ComplexityTheory.Savitch.Sel
import ComplexityTheory.Savitch.Reach
/-!
# The step of the search is a function of the polynomial-time class

`ComplexityTheory/Savitch/State.lean` writes the depth-first search of Savitch's recursion as a
function `HTN.Savitch.step` of the state, parametrised by the width `E` of a node, the height `KF`
at which the recursion bottoms out, and the one-step test.  To iterate it inside the
polynomial-space class of `ComplexityTheory/Collapse/Fun.lean` it has to be a function of
*bit-string arguments only*, and a function of Cobham's class.

This file writes that function, `HTN.Savitch.svStepFn`, on the argument list

    0  the state             1  a template of length `W`     2  a template of length `E`
    3  a template of length `frW E`                          4  a template of length `KF`
    5  the input `x`         6  the advice `a`

— the three numerical parameters are passed as *lengths* of template strings, which is how a
function of Cobham's class can depend on them.  `HTN.Savitch.svStepFn_apply` identifies it with
`HTN.Savitch.step` for the one-step test `HTN.Savitch.stpM` of
`ComplexityTheory/Savitch/Reach.lean`, and `HTN.Savitch.cobham_svStepFn` places it in Cobham's
class.
-/

namespace HTN

namespace Savitch

open PTime PSpace Space

/-! ### The pieces of the state -/

/-- The state itself. -/
def sS : Fn := fun args => args.getD 0 []

/-- The two return bits. -/
def sRet : Fn := fun args => (sS args).take 2

/-- The stack, below the return bits. -/
def sRest : Fn := fun args => (sS args).drop 2

/-- The top frame. -/
def sFr : Fn := fun args => (sRest args).take (args.getD 3 []).length

/-- The stack below the top frame. -/
def sSt : Fn := fun args => (sRest args).drop (args.getD 3 []).length

/-- The phase bits of the top frame. -/
def sPh : Fn := fun args => (sFr args).take 2

/-- The first endpoint of the top frame. -/
def sU : Fn := fun args => ((sFr args).drop 2).take (args.getD 2 []).length

/-- The second endpoint of the top frame. -/
def sV : Fn := fun args =>
  (((sFr args).drop 2).drop (args.getD 2 []).length).take (args.getD 2 []).length

/-- The midpoint of the top frame. -/
def sMid : Fn := fun args =>
  (((sFr args).drop 2).drop (args.getD 2 []).length).drop (args.getD 2 []).length

theorem cobham_sS : Cobham sS := Cobham.proj 0

theorem cobham_sRet : Cobham sRet := cobham_take (cobham_const [false, false]) cobham_sS

theorem cobham_sRest : Cobham sRest := cobham_drop (cobham_const [false, false]) cobham_sS

theorem cobham_sFr : Cobham sFr := cobham_take (Cobham.proj 3) cobham_sRest

theorem cobham_sSt : Cobham sSt := cobham_drop (Cobham.proj 3) cobham_sRest

theorem cobham_sPh : Cobham sPh := cobham_take (cobham_const [false, false]) cobham_sFr

theorem cobham_frDrop : Cobham (fun args => (sFr args).drop 2) :=
  cobham_drop (cobham_const [false, false]) cobham_sFr

theorem cobham_sU : Cobham sU := cobham_take (Cobham.proj 2) cobham_frDrop

theorem cobham_frDrop2 :
    Cobham (fun args => ((sFr args).drop 2).drop (args.getD 2 []).length) :=
  cobham_drop (Cobham.proj 2) cobham_frDrop

theorem cobham_sV : Cobham sV := cobham_take (Cobham.proj 2) cobham_frDrop2

theorem cobham_sMid : Cobham sMid := cobham_drop (Cobham.proj 2) cobham_frDrop2

/-! ### The one-step test -/

/-- Decoding a computed node, at the width recorded by the first template. -/
def sDec (b : Fn) : Fn := fun args => dec (args.getD 1 []).length (b args)

/-- **Decoding at a computed width** is a function of Cobham's class. -/
theorem cobham_decOf {w b : Fn} (hw : Cobham w) (hb : Cobham b) :
    Cobham (fun args => dec (w args).length (b args)) := by
  have h1 : Cobham (fun args : Args => (b args).drop (w args).length) := cobham_drop hw hb
  have h2 : Cobham (fun args : Args => (b args).take (w args).length) := cobham_take hw hb
  have h3 : Cobham (fun args : Args => onesPrefix ((b args).take (w args).length)) :=
    (cobham_c1 cobham_onesPrefixFn h2).of_eq' fun args => by
      simp [compFn, onesPrefixFn_apply]
  exact cobham_take h3 h1

theorem cobham_sDec {b : Fn} (hb : Cobham b) : Cobham (sDec b) :=
  cobham_decOf (Cobham.proj 1) hb

/-- The one-step test between the two endpoints of the top frame. -/
def sStp (M : NSpace) : Args → Bool := fun args =>
  stpM M (args.getD 5 []) (args.getD 6 []) (args.getD 1 []).length (sU args) (sV args)

theorem cobhamB_sStp (M : NSpace) : CobhamB (sStp M) := by
  have hu : Cobham (sDec sU) := cobham_sDec cobham_sU
  have hv : Cobham (sDec sV) := cobham_sDec cobham_sV
  exact (cobhamB_eqStr hu hv).or
    (M.cobham_stepB.comp4 hv hu (Cobham.proj 5) (Cobham.proj 6))

/-! ### The branches -/

/-- Popping the frame with a constant answer. -/
def svPop (b : Bool) : Fn := fun args => [true, b] ++ sSt args

/-- Popping the frame with the answer of the one-step test. -/
def svPopStp (M : NSpace) : Fn := fun args => [true, sStp M args] ++ sSt args

/-- Pushing the first child. -/
def svPush1 : Fn := fun args =>
  [false, false] ++ (fresh (args.getD 2 []).length (sU args) (sMid args) ++
    (frame [true, false] (sU args) (sV args) (sMid args) ++ sSt args))

/-- Pushing the second child. -/
def svPush2 : Fn := fun args =>
  [false, false] ++ (fresh (args.getD 2 []).length (sMid args) (sV args) ++
    (frame [false, true] (sU args) (sV args) (sMid args) ++ sSt args))

/-- Pushing the first child for the next midpoint. -/
def svPush3 : Fn := fun args =>
  [false, false] ++ (fresh (args.getD 2 []).length (sU args) (succB (sMid args)) ++
    (frame [true, false] (sU args) (sV args) (succB (sMid args)) ++ sSt args))

theorem cobham_svPop (b : Bool) : Cobham (svPop b) :=
  cobham_app2 (cobham_const [true, b]) cobham_sSt

theorem cobham_svPopStp (M : NSpace) : Cobham (svPopStp M) :=
  cobham_app2 ((cobham_c1 (Cobham.cons true) (cobhamB_sStp M)).of_eq' fun args => by
    simp [compFn, consFn]) cobham_sSt

theorem cobham_zerosE : Cobham (fun args : Args => zeros (args.getD 2 []).length) :=
  (cobham_c1 cobham_zerosFn (Cobham.proj 2)).of_eq' fun args => by
    simp [compFn, zerosFn_apply, proj]

theorem cobham_onesE : Cobham (fun args : Args => ones (args.getD 2 []).length) :=
  (cobham_c1 cobham_onesLenFn (Cobham.proj 2)).of_eq' fun args => by
    simp [compFn, onesLenFn_apply, proj]

theorem cobham_succMid : Cobham (fun args : Args => succB (sMid args)) :=
  (cobham_c1 cobham_succFn cobham_sMid).of_eq' fun args => by simp [compFn, succFn_apply]

theorem cobham_svPush1 : Cobham svPush1 :=
  cobham_app2 (cobham_const [false, false])
    (cobham_app2
      (cobham_app2 (cobham_app2 (cobham_app2 (cobham_const [false, false]) cobham_sU)
        cobham_sMid) cobham_zerosE)
      (cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2 (cobham_const [true, false]) cobham_sU)
        cobham_sV) cobham_sMid) cobham_sSt))

theorem cobham_svPush2 : Cobham svPush2 :=
  cobham_app2 (cobham_const [false, false])
    (cobham_app2
      (cobham_app2 (cobham_app2 (cobham_app2 (cobham_const [false, false]) cobham_sMid)
        cobham_sV) cobham_zerosE)
      (cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2 (cobham_const [false, true]) cobham_sU)
        cobham_sV) cobham_sMid) cobham_sSt))

theorem cobham_svPush3 : Cobham svPush3 :=
  cobham_app2 (cobham_const [false, false])
    (cobham_app2
      (cobham_app2 (cobham_app2 (cobham_app2 (cobham_const [false, false]) cobham_sU)
        cobham_succMid) cobham_zerosE)
      (cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2 (cobham_const [true, false]) cobham_sU)
        cobham_sV) cobham_succMid) cobham_sSt))

/-! ### The step -/

/-- The advance to the next midpoint. -/
def svAdv : Fn := fun args =>
  if sMid args = ones (args.getD 2 []).length then svPop false args
  else if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
      svPush3 args
    else svPop false args

/-- **The step of the search, as a function of bit strings only.** -/
def svStepFn (M : NSpace) : Fn := fun args =>
  if (sRest args).length < (args.getD 3 []).length then sS args
  else if (sRet args).headD false = false then
    (if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
        svPush1 args
      else svPopStp M args)
  else if sPh args = [true, false] then
    (if ((sRet args).drop 1).headD false = true then
        (if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
            svPush2 args
          else svPop false args)
      else svAdv args)
  else if sPh args = [false, true] then
    (if ((sRet args).drop 1).headD false = true then svPop true args else svAdv args)
  else sS args

/-- **The function is the step of the search**, once the templates have the intended lengths. -/
theorem svStepFn_apply (M : NSpace) (args : Args)
    (hF : (args.getD 3 []).length = frW (args.getD 2 []).length) :
    svStepFn M args = step (args.getD 2 []).length (args.getD 4 []).length
      (stpM M (args.getD 5 []) (args.getD 6 []) (args.getD 1 []).length) (args.getD 0 []) := by
  simp only [svStepFn, svAdv, svPop, svPopStp, svPush1, svPush2, svPush3, sStp, sS, sRet, sRest,
    sFr, sSt, sPh, sU, sV, sMid, step, hF]

/-! ### The step belongs to Cobham's class -/

theorem cobhamB_room :
    CobhamB (fun args : Args =>
      decide ((sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length)) :=
  (cobhamB_lenLE (cobham_app2 cobham_sSt (Cobham.proj 3)) (Cobham.proj 4)).of_eq fun args => by
    simp [proj]

theorem cobham_svAdv : Cobham svAdv := by
  refine cobham_ite (p := fun args => decide (sMid args = ones (args.getD 2 []).length))
    (cobhamB_eqStr cobham_sMid cobham_onesE) (cobham_svPop false) ?_ (fun args => by simp)
  exact cobham_ite cobhamB_room cobham_svPush3 (cobham_svPop false) (fun args => by simp)

theorem cobham_svStepFn (M : NSpace) : Cobham (svStepFn M) := by
  have hretbit : CobhamB (fun args : Args => ((sRet args).drop 1).headD false) :=
    cobhamB_head (cobham_drop (cobham_const [false]) cobham_sRet)
  have hinner1 : Cobham (fun args : Args =>
      if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
        svPush1 args else svPopStp M args) :=
    cobham_ite cobhamB_room cobham_svPush1 (cobham_svPopStp M) (fun args => by simp)
  have hinner2 : Cobham (fun args : Args =>
      if ((sRet args).drop 1).headD false = true then
        (if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
            svPush2 args else svPop false args)
      else svAdv args) :=
    cobham_ite hretbit
      (cobham_ite cobhamB_room cobham_svPush2 (cobham_svPop false) (fun args => by simp))
      cobham_svAdv (fun args => by simp)
  have hinner3 : Cobham (fun args : Args =>
      if ((sRet args).drop 1).headD false = true then svPop true args else svAdv args) :=
    cobham_ite hretbit (cobham_svPop true) cobham_svAdv (fun args => by simp)
  have htail : Cobham (fun args : Args =>
      if sPh args = [false, true] then
        (if ((sRet args).drop 1).headD false = true then svPop true args else svAdv args)
      else sS args) :=
    cobham_ite (cobhamB_eqStr cobham_sPh (cobham_const [false, true])) hinner3 cobham_sS
      (fun args => by simp)
  have hmid : Cobham (fun args : Args =>
      if sPh args = [true, false] then
        (if ((sRet args).drop 1).headD false = true then
            (if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
                svPush2 args else svPop false args)
          else svAdv args)
      else if sPh args = [false, true] then
        (if ((sRet args).drop 1).headD false = true then svPop true args else svAdv args)
      else sS args) :=
    cobham_ite (cobhamB_eqStr cobham_sPh (cobham_const [true, false])) hinner2 htail
      (fun args => by simp)
  have houter : Cobham (fun args : Args =>
      if (sRet args).headD false = false then
        (if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
            svPush1 args else svPopStp M args)
      else if sPh args = [true, false] then
        (if ((sRet args).drop 1).headD false = true then
            (if (sSt args).length + (args.getD 3 []).length ≤ (args.getD 4 []).length then
                svPush2 args else svPop false args)
          else svAdv args)
      else if sPh args = [false, true] then
        (if ((sRet args).drop 1).headD false = true then svPop true args else svAdv args)
      else sS args) :=
    cobham_ite (((cobhamB_head cobham_sRet)).not) hinner1 hmid (fun args => by simp)
  exact cobham_ite
    (p := fun args => !decide ((args.getD 3 []).length ≤ (sRest args).length))
    ((cobhamB_lenLE (Cobham.proj 3) cobham_sRest).not) cobham_sS houter
    (fun args => by simp)

end Savitch

end HTN
