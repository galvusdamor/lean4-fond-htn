import FondHtn.StrongOD.RegBlock
import FondHtn.StrongOD.Acyc
/-!
# The exponential-space search for regular problems

A configuration (`FOND.SOD.RCfg`) is a certificate `R` (a list of names, closed under the
methods, all of whose methods are regular, `FOND.SOD.regCertB`) and a core
`(ph, cur, S, B, nx, S', R, st)`:

* phase `0`: `cur` is the list of the names still to be decomposed (at most one) and `S` the
  current belief set (an explicit list of states);
* phase `1`: the block `B` (the primitive part of the chosen method) is being checked against the
  guessed next belief set `S'`: every state of the list `R` (initially `S`) must win the block
  game with leaves in `S'`; `st` is the stack of the nondeterministic depth-first evaluation
  (`HTN.Syn.PolyDom.dfsStep`) of the block game for the current state; `nx` are the names of the
  method's compound tasks.

Steps (`FOND.SOD.rstep`): *choose* a regular method of the current name and guess `S'`; *load*
the next state of `R` onto the stack; one *dfs* step; *finish* the block (`cur := nx`,
`S := S'`).  The search accepts in phase `0` with no names left.  All steps are polynomial time
in the configuration.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-- The core of a configuration: `(ph, cur, S, B, nx, S', R, st)`. -/
abbrev RCore : Type :=
  ℕ × List ℕ × List (List ℕ) × TnDesc × List ℕ × List (List ℕ) × List (List ℕ) × List (ℕ × GCfg)

/-- A configuration: a certificate and a core. -/
abbrev RCfg : Type := List ℕ × RCore

instance instDecEqRCore : DecidableEq RCore :=
  @instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _
      (inferInstanceAs (DecidableEq TnDesc)) (@instDecidableEqProd _ _ inferInstance
        (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance
          (@instDecidableEqList _ (@instDecidableEqProd _ _ inferInstance instDecEqGCfg))))))))

instance instDecEqRCfg : DecidableEq RCfg :=
  @instDecidableEqProd _ _ inferInstance instDecEqRCore

/-- The certificate check for `REG`: the names of `R` contain those of `tn_I` and are closed
under their methods, which are regular. -/
def regCertB (p : FProbDesc) (R : List ℕ) : Bool :=
  p.tnI.ids.all (fun x => !(lblOf p.tnI x).1 || decide ((lblOf p.tnI x).2 ∈ R)) &&
    p.methods.all (fun e => !decide (e.1 ∈ R) || (regB e.2 && e.2.ids.all fun z =>
      !(lblOf e.2 z).1 || decide ((lblOf e.2 z).2 ∈ R))) &&
    R.all (fun c => decide (c ∈ numsOf (skel p))) &&
    decide (R.length ≤ (numsOf (skel p)).length)

/-- Choose a method and guess the next belief set. -/
def chooseB (p : FProbDesc) (X Y : RCore) : Bool :=
  X.1 == 0 && p.methods.any fun e => decide ([e.1] = X.2.1) && regB e.2 &&
    decide (Y = (1, X.2.1, X.2.2.1, primD e.2, compL e.2, Y.2.2.2.2.2.1, X.2.2.1, []))

/-- Load the next state of `R`. -/
def loadB (X Y : RCore) : Bool :=
  X.1 == 1 && X.2.2.2.2.2.2.2.isEmpty && !X.2.2.2.2.2.2.1.isEmpty &&
    decide (Y = (1, X.2.1, X.2.2.1, X.2.2.2.1, X.2.2.2.2.1, X.2.2.2.2.2.1,
      X.2.2.2.2.2.2.1.tail, [(2 * X.2.2.2.1.ids.length,
        ((0 : ℕ), (0 : ℕ), X.2.2.2.2.2.2.1.headI.dedup, X.2.2.2.1))]))

/-- One step of the depth-first evaluation of the block game. -/
def dfsB (p : FProbDesc) (X Y : RCore) : Bool :=
  X.1 == 1 && !X.2.2.2.2.2.2.2.isEmpty &&
    dfsStep bacc buni bsuccs ((p, X.2.2.2.2.2.1), X.2.2.2.2.2.2.2, Y.2.2.2.2.2.2.2) &&
    decide (Y = (1, X.2.1, X.2.2.1, X.2.2.2.1, X.2.2.2.2.1, X.2.2.2.2.2.1, X.2.2.2.2.2.2.1,
      Y.2.2.2.2.2.2.2))

/-- Finish the block. -/
def finB (X Y : RCore) : Bool :=
  X.1 == 1 && X.2.2.2.2.2.2.2.isEmpty && X.2.2.2.2.2.2.1.isEmpty &&
    decide (Y = (0, X.2.2.2.2.1, X.2.2.2.2.2.1, X.2.2.2.1, X.2.2.2.2.1, X.2.2.2.2.2.1, [], []))

/-- **The step relation.** -/
def rstep (y : FProbDesc × RCfg × RCfg) : Bool :=
  decide (y.2.2.1 = y.2.1.1) && (chooseB y.1 y.2.1.2 y.2.2.2 || loadB y.2.1.2 y.2.2.2 ||
    dfsB y.1 y.2.1.2 y.2.2.2 || finB y.2.1.2 y.2.2.2)

/-- **The initial configurations**: the first block is the primitive part of `tn_I`. -/
def rinit (y : FProbDesc × RCfg) : Bool :=
  y.1.validB && regB y.1.tnI && regCertB y.1 y.2.1 &&
    decide (y.2.2 = (1, [], [], primD (d₀ y.1), compL (d₀ y.1), y.2.2.2.2.2.2.2.1,
      [y.1.init.dedup], []))

/-- **The accepting configurations.** -/
def racc (y : FProbDesc × RCfg) : Bool := y.2.2.1 == 0 && y.2.2.2.1.isEmpty

/-! ## Polynomial time -/

theorem pt_primB : PT fun z : TnDesc × ℕ => primB z.1 z.2 :=
  PT.not (PT.fst.comp (pt_lblOf PT.fst PT.snd))

theorem pt_primD : PT primD := by
  unfold primD
  exact PT.pair (PT.filter PT.fst (pt_primB.comp (PT.pair PT.fst PT.snd)))
    (PT.pair (PT.dedup (PT.filter (PT.fst.comp PT.snd) (PT.and
      (pt_primB.comp (PT.pair PT.fst (PT.fst.comp PT.snd)))
      (pt_primB.comp (PT.pair PT.fst (PT.snd.comp PT.snd))))))
      (PT.filter (PT.snd.comp PT.snd) (PT.not (PT.fst.comp (PT.snd.comp PT.snd)))))

theorem pt_compL : PT compL := by
  unfold compL
  exact PT.map (PT.filter PT.fst (PT.fst.comp (pt_lblOf PT.fst PT.snd)))
    (PT.snd.comp (pt_lblOf PT.fst PT.snd))

theorem pt_regCertB : PT fun z : FProbDesc × List ℕ => regCertB z.1 z.2 := by
  have ht : PT fun z : FProbDesc × List ℕ => z.1.tnI := PT.snd.comp (PT.snd.comp PT.fst)
  have hm : PT fun z : FProbDesc × List ℕ => z.1.methods := PT.snd.comp (PT.fst.comp PT.fst)
  have hN : PT fun z : FProbDesc × List ℕ => numsOf (skel z.1) :=
    pt_numsOf.comp (pt_skel.comp PT.fst)
  unfold regCertB
  refine PT.and (PT.and (PT.and ?_ ?_) (PT.all PT.snd (PT.elem (hN.comp PT.fst) PT.snd)))
    (PT.le (PT.length PT.snd) (PT.length hN))
  · have hl : PT fun z : (FProbDesc × List ℕ) × ℕ => lblOf z.1.1.tnI z.2 :=
      pt_lblOf (ht.comp PT.fst) PT.snd
    exact PT.all (PT.fst.comp ht) (PT.or (PT.not (PT.fst.comp hl))
      (PT.elem (PT.snd.comp (PT.fst)) (PT.snd.comp hl)))
  · have hl : PT fun z : ((FProbDesc × List ℕ) × MethodDesc) × ℕ => lblOf z.1.2.2 z.2 :=
      pt_lblOf (PT.snd.comp (PT.snd.comp PT.fst)) PT.snd
    exact PT.all hm (PT.or (PT.not (PT.elem (PT.snd.comp PT.fst) (PT.fst.comp PT.snd)))
      (PT.and (pt_regB.comp (PT.snd.comp PT.snd))
        (PT.all (PT.fst.comp (PT.snd.comp PT.snd)) (PT.or (PT.not (PT.fst.comp hl))
          (PT.elem (PT.snd.comp (PT.fst.comp PT.fst)) (PT.snd.comp hl))))))

section Fields

variable {α : Type} [BEnc α] {f : α → RCore}

theorem pt_ph (hf : PT f) : PT fun a => (f a).1 := PT.fst.comp hf
theorem pt_cur (hf : PT f) : PT fun a => (f a).2.1 := PT.fst.comp (PT.snd.comp hf)
theorem pt_S (hf : PT f) : PT fun a => (f a).2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp hf))
theorem pt_B (hf : PT f) : PT fun a => (f a).2.2.2.1 :=
  PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hf)))
theorem pt_nx (hf : PT f) : PT fun a => (f a).2.2.2.2.1 :=
  PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hf))))
theorem pt_S' (hf : PT f) : PT fun a => (f a).2.2.2.2.2.1 :=
  PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hf)))))
theorem pt_R (hf : PT f) : PT fun a => (f a).2.2.2.2.2.2.1 :=
  PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp
    (PT.snd.comp hf))))))
theorem pt_st (hf : PT f) : PT fun a => (f a).2.2.2.2.2.2.2 :=
  PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp
    (PT.snd.comp hf))))))

theorem pt_mk {g0 : α → ℕ} {g1 : α → List ℕ} {g2 : α → List (List ℕ)} {g3 : α → TnDesc}
    {g4 : α → List ℕ} {g5 g6 : α → List (List ℕ)} {g7 : α → List (ℕ × GCfg)}
    (h0 : PT g0) (h1 : PT g1) (h2 : PT g2) (h3 : PT g3) (h4 : PT g4) (h5 : PT g5) (h6 : PT g6)
    (h7 : PT g7) : PT fun a => ((g0 a, g1 a, g2 a, g3 a, g4 a, g5 a, g6 a, g7 a) : RCore) :=
  PT.pair h0 (PT.pair h1 (PT.pair h2 (PT.pair h3 (PT.pair h4 (PT.pair h5 (PT.pair h6 h7))))))

end Fields

theorem pt_rstep : PT rstep := by
  have hX : PT fun y : FProbDesc × RCfg × RCfg => y.2.1.2 := PT.snd.comp (PT.fst.comp PT.snd)
  have hY : PT fun y : FProbDesc × RCfg × RCfg => y.2.2.2 := PT.snd.comp (PT.snd.comp PT.snd)
  have hp : PT fun y : FProbDesc × RCfg × RCfg => y.1 := PT.fst
  have hch : PT fun y : FProbDesc × RCfg × RCfg => chooseB y.1 y.2.1.2 y.2.2.2 := by
    unfold chooseB
    refine PT.and (PT.beq (pt_ph hX) (PT.const 0)) (PT.any (PT.snd.comp (PT.fst.comp hp)) ?_)
    have hX' := hX.comp (PT.fst (β := MethodDesc))
    have hY' := hY.comp (PT.fst (β := MethodDesc))
    exact PT.and (PT.and (PT.eq (PT.single (PT.fst.comp PT.snd)) (pt_cur hX'))
      (pt_regB.comp (PT.snd.comp PT.snd)))
      (PT.eq hY' (pt_mk (PT.const 1) (pt_cur hX') (pt_S hX') (pt_primD.comp (PT.snd.comp PT.snd))
        (pt_compL.comp (PT.snd.comp PT.snd)) (pt_S' hY') (pt_S hX') (PT.const [])))
  have hld : PT fun y : FProbDesc × RCfg × RCfg => loadB y.2.1.2 y.2.2.2 := by
    unfold loadB
    exact PT.and (PT.and (PT.and (PT.beq (pt_ph hX) (PT.const 1)) (PT.isEmpty (pt_st hX)))
      (PT.not (PT.isEmpty (pt_R hX))))
      (PT.eq hY (pt_mk (PT.const 1) (pt_cur hX) (pt_S hX) (pt_B hX) (pt_nx hX) (pt_S' hX)
        (PT.tail (pt_R hX)) (PT.single (PT.pair (PT.affine 2 0 (PT.length (PT.fst.comp (pt_B hX))))
          (PT.pair (PT.const 0) (PT.pair (PT.const 0) (PT.pair (PT.dedup (PT.headI (pt_R hX)))
            (pt_B hX))))))))
  have hdf : PT fun y : FProbDesc × RCfg × RCfg => dfsB y.1 y.2.1.2 y.2.2.2 := by
    unfold dfsB
    exact PT.and (PT.and (PT.and (PT.beq (pt_ph hX) (PT.const 1)) (PT.not (PT.isEmpty (pt_st hX))))
      ((pt_dfsStep pt_bacc pt_buni pt_bsuccs).comp (PT.pair (PT.pair hp (pt_S' hX))
        (PT.pair (pt_st hX) (pt_st hY)))))
      (PT.eq hY (pt_mk (PT.const 1) (pt_cur hX) (pt_S hX) (pt_B hX) (pt_nx hX) (pt_S' hX)
        (pt_R hX) (pt_st hY)))
  have hfn : PT fun y : FProbDesc × RCfg × RCfg => finB y.2.1.2 y.2.2.2 := by
    unfold finB
    exact PT.and (PT.and (PT.and (PT.beq (pt_ph hX) (PT.const 1)) (PT.isEmpty (pt_st hX)))
      (PT.isEmpty (pt_R hX)))
      (PT.eq hY (pt_mk (PT.const 0) (pt_nx hX) (pt_S' hX) (pt_B hX) (pt_nx hX) (pt_S' hX)
        (PT.const []) (PT.const [])))
  unfold rstep
  exact PT.and (PT.eq (PT.fst.comp (PT.snd.comp PT.snd)) (PT.fst.comp (PT.fst.comp PT.snd)))
    (PT.or (PT.or (PT.or hch hld) hdf) hfn)

theorem pt_rinit : PT rinit := by
  have hX : PT fun y : FProbDesc × RCfg => y.2.2 := PT.snd.comp PT.snd
  unfold rinit
  exact PT.and (PT.and (PT.and (FProbDesc.pt_validB.comp PT.fst)
    (pt_regB.comp (PT.snd.comp (PT.snd.comp PT.fst))))
    (pt_regCertB.comp (PT.pair PT.fst (PT.fst.comp PT.snd))))
    (PT.eq hX (pt_mk (PT.const 1) (PT.const []) (PT.const []) (pt_primD.comp (pt_d₀.comp PT.fst))
      (pt_compL.comp (pt_d₀.comp PT.fst)) (pt_S' hX)
      (PT.single (PT.dedup (PT.fst.comp (PT.snd.comp PT.fst)))) (PT.const [])))

theorem pt_racc : PT racc :=
  PT.and (PT.beq (pt_ph (PT.snd.comp PT.snd)) (PT.const 0))
    (PT.isEmpty (pt_cur (PT.snd.comp PT.snd)))

end SOD

end FOND
