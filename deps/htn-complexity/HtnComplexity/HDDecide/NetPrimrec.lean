import HtnComplexity.HDDecide.NetMain
import HtnComplexity.Computable.AcDecideCell
import HtnComplexity.Computable.ToDecideCell
import HtnComplexity.Computable.RegDecideCell
/-!
# The Petri net of a one-hole-digging description is computable

The construction `(d, q) ↦ (hdNet d q, hdM0 q, hdM1)` is primitive recursive.
-/

namespace HTN

namespace HD

open Syn Syn.ToDec Petri Primrec

/-! ### Basic pieces -/

theorem net_eq_casesOn (d : DomDesc) (q : InstDesc) (k : ℕ) :
    net d q k = Nat.casesOn k q.tnI (fun j => (d.methods.getD j default).2) := by
  cases k <;> rfl

theorem primrec_net : Primrec fun w : (DomDesc × InstDesc) × ℕ => net w.1.1 w.1.2 w.2 := by
  have hg : Primrec₂ fun (w : (DomDesc × InstDesc) × ℕ) (j : ℕ) =>
      (w.1.1.methods.getD j default).2 :=
    Primrec₂.mk (Primrec.snd.comp ((Primrec.list_getD default).comp
      (primrec_methods.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd))
  exact (Primrec.nat_casesOn Primrec.snd (primrec_tnI.comp (Primrec.snd.comp Primrec.fst))
    hg).of_eq fun w => (net_eq_casesOn _ _ _).symm

theorem primrec_nrmF : Primrec fun w : (DomDesc × InstDesc) × List ℕ => nrmF w.1.1 w.1.2 w.2 :=
  primrec_filterB (primrec_allFacts.comp Primrec.fst)
    (Primrec₂.mk (primrec_memB.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem isEmpty_eq (l : List ℕ) : l.isEmpty = (l.length == 0) := by cases l <;> rfl

theorem primrec_tokOf : Primrec₂ tokOf := by
  refine Primrec₂.mk ?_
  have hc : Primrec fun w : ℕ × List ℕ => w.2.isEmpty :=
    (Primrec.beq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)).of_eq
      fun w => (isEmpty_eq w.2).symm
  exact (Primrec.cond hc (Primrec.const []) (Primrec.list_cons.comp Primrec.id
    (Primrec.const []))).of_eq fun w => rfl

theorem primrec_beq_list : Primrec₂ fun (a b : List ℕ) => a == b :=
  (Primrec.beq (α := List ℕ)).of_eq fun a b => by
    by_cases h : a = b <;> simp [h]

/-! ### The step rules -/

/-- The context of a step rule: description, states, item and identifier. -/
abbrev Ctx : Type := DomDesc × InstDesc × List ℕ × List ℕ × ℕ × List ℕ × ℕ

theorem pD : Primrec fun z : Ctx => z.1 := Primrec.fst
theorem pQ : Primrec fun z : Ctx => z.2.1 := Primrec.fst.comp Primrec.snd
theorem pLf : Primrec fun z : Ctx => z.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem pLb : Primrec fun z : Ctx => z.2.2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem pK : Primrec fun z : Ctx => z.2.2.2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem pL : Primrec fun z : Ctx => z.2.2.2.2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    Primrec.snd))))
theorem pX : Primrec fun z : Ctx => z.2.2.2.2.2.2 :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    Primrec.snd))))

theorem pNet : Primrec fun z : Ctx => net z.1 z.2.1 z.2.2.2.2.1 :=
  primrec_net.comp (Primrec.pair (Primrec.pair pD pQ) pK)

theorem pLp : Primrec fun z : Ctx => (net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2 :=
  primrec_lblPair.comp (Primrec.pair pNet pX)

theorem pRest : Primrec fun z : Ctx =>
    tokOf z.2.2.2.2.1 (z.2.2.2.2.2.1.filter (fun y => y != z.2.2.2.2.2.2)) :=
  primrec_tokOf.comp pK (primrec_filterB pL (Primrec₂.mk (Primrec.not.comp
    (Primrec.beq.comp Primrec.snd (pX.comp Primrec.fst)))))

theorem pCtl : Primrec fun z : Ctx => ((1 : ℕ), z.2.2.1, z.2.2.2.1) :=
  Primrec.pair (Primrec.const 1) (Primrec.pair pLf pLb)

theorem pItem : Primrec fun z : Ctx => (some (z.2.2.2.2.1, z.2.2.2.2.2.1) : Option Tok) :=
  Primrec.option_some.comp (Primrec.pair pK pL)

theorem primrec_progR : Primrec fun z : Ctx =>
    progR z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 := by
  have hc1 : Primrec fun z : Ctx => !((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).1 :=
    Primrec.not.comp (Primrec.fst.comp pLp)
  have hc2 : Primrec fun z : Ctx =>
      z.2.2.2.2.2.1.all (fun y => !TnDesc.ordB (net z.1 z.2.1 z.2.2.2.2.1) y z.2.2.2.2.2.2) :=
    primrec_allB pL (Primrec₂.mk (Primrec.not.comp (TnDesc.primrec_ordB.comp
      (Primrec.pair (pNet.comp Primrec.fst) (Primrec.pair Primrec.snd (pX.comp Primrec.fst))))))
  have ha : Primrec fun z : Ctx => ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).2 :=
    Primrec.snd.comp pLp
  have hc3 : Primrec fun z : Ctx =>
      applB z.1 z.2.2.1 ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).2 :=
    primrec_applB.comp (Primrec.pair pD pLf) ha
  have hpost : Primrec fun z : Ctx =>
      nrmF z.1 z.2.1 (stepL z.1 z.2.2.1 ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).2) :=
    primrec_nrmF.comp (Primrec.pair (Primrec.pair pD pQ)
      (primrec_stepL.comp (Primrec.pair pD pLf) ha))
  have hrule : Primrec fun z : Ctx => (((1 : ℕ), z.2.2.1, z.2.2.2.1),
      (some (z.2.2.2.2.1, z.2.2.2.2.2.1) : Option Tok),
      ((1 : ℕ), nrmF z.1 z.2.1 (stepL z.1 z.2.2.1
        ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).2), z.2.2.2.1),
      tokOf z.2.2.2.2.1 (z.2.2.2.2.2.1.filter (fun y => y != z.2.2.2.2.2.2))) :=
    Primrec.pair pCtl (Primrec.pair pItem (Primrec.pair
      (Primrec.pair (Primrec.const 1) (Primrec.pair hpost pLb)) pRest))
  exact (Primrec.cond (Primrec.and.comp (Primrec.and.comp hc1 hc2) hc3)
    (Primrec.list_cons.comp hrule (Primrec.const [])) (Primrec.const [])).of_eq fun _ => rfl

/-- The body of `regrR` for one guessed state `s`. -/
theorem primrec_regrBody : Primrec₂ fun (z : Ctx) (s : List ℕ) =>
    bif !((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).1 &&
        z.2.2.2.2.2.1.all (fun y => !TnDesc.ordB (net z.1 z.2.1 z.2.2.2.2.1) z.2.2.2.2.2.2 y) &&
        applB z.1 s ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).2 &&
        (nrmF z.1 z.2.1 (stepL z.1 s ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).2) ==
          z.2.2.2.1) then
      [(((1 : ℕ), z.2.2.1, z.2.2.2.1), (some (z.2.2.2.2.1, z.2.2.2.2.2.1) : Option Tok),
        ((1 : ℕ), z.2.2.1, nrmF z.1 z.2.1 s),
        tokOf z.2.2.2.2.1 (z.2.2.2.2.2.1.filter (fun y => y != z.2.2.2.2.2.2)))]
    else [] := by
  refine Primrec₂.mk ?_
  have qD : Primrec fun w : Ctx × List ℕ => w.1.1 := pD.comp Primrec.fst
  have qQ : Primrec fun w : Ctx × List ℕ => w.1.2.1 := pQ.comp Primrec.fst
  have qLf : Primrec fun w : Ctx × List ℕ => w.1.2.2.1 := pLf.comp Primrec.fst
  have qLb : Primrec fun w : Ctx × List ℕ => w.1.2.2.2.1 := pLb.comp Primrec.fst
  have qL : Primrec fun w : Ctx × List ℕ => w.1.2.2.2.2.2.1 := pL.comp Primrec.fst
  have qDQ : Primrec fun w : Ctx × List ℕ => (w.1.1, w.1.2.1) := Primrec.pair qD qQ
  have hS : Primrec fun w : Ctx × List ℕ => w.2 := Primrec.snd
  have hc1 : Primrec fun w : Ctx × List ℕ =>
      !((net w.1.1 w.1.2.1 w.1.2.2.2.2.1).lblPair w.1.2.2.2.2.2.2).1 :=
    (Primrec.not.comp (Primrec.fst.comp pLp)).comp Primrec.fst
  have hc2 : Primrec fun w : Ctx × List ℕ => w.1.2.2.2.2.2.1.all
      (fun y => !TnDesc.ordB (net w.1.1 w.1.2.1 w.1.2.2.2.2.1) w.1.2.2.2.2.2.2 y) :=
    primrec_allB qL (Primrec₂.mk (Primrec.not.comp (TnDesc.primrec_ordB.comp
      (Primrec.pair ((pNet.comp Primrec.fst).comp Primrec.fst) (Primrec.pair ((pX.comp Primrec.fst).comp Primrec.fst)
        Primrec.snd)))))
  have ha : Primrec fun w : Ctx × List ℕ =>
      ((net w.1.1 w.1.2.1 w.1.2.2.2.2.1).lblPair w.1.2.2.2.2.2.2).2 :=
    (Primrec.snd.comp pLp).comp Primrec.fst
  have hc3 : Primrec fun w : Ctx × List ℕ =>
      applB w.1.1 w.2 ((net w.1.1 w.1.2.1 w.1.2.2.2.2.1).lblPair w.1.2.2.2.2.2.2).2 :=
    primrec_applB.comp (Primrec.pair qD hS) ha
  have hc4 : Primrec fun w : Ctx × List ℕ =>
      (nrmF w.1.1 w.1.2.1 (stepL w.1.1 w.2 ((net w.1.1 w.1.2.1 w.1.2.2.2.2.1).lblPair
        w.1.2.2.2.2.2.2).2) == w.1.2.2.2.1) :=
    primrec_beq_list.comp (primrec_nrmF.comp (Primrec.pair (qDQ)
      (primrec_stepL.comp (Primrec.pair qD hS) ha))) qLb
  have hrule : Primrec fun w : Ctx × List ℕ =>
      (((1 : ℕ), w.1.2.2.1, w.1.2.2.2.1), (some (w.1.2.2.2.2.1, w.1.2.2.2.2.2.1) : Option Tok),
        ((1 : ℕ), w.1.2.2.1, nrmF w.1.1 w.1.2.1 w.2),
        tokOf w.1.2.2.2.2.1 (w.1.2.2.2.2.2.1.filter (fun y => y != w.1.2.2.2.2.2.2))) :=
    Primrec.pair (pCtl.comp Primrec.fst) (Primrec.pair (pItem.comp Primrec.fst) (Primrec.pair
      (Primrec.pair (Primrec.const 1) (Primrec.pair qLf
        (primrec_nrmF.comp (Primrec.pair (qDQ) hS)))) (pRest.comp Primrec.fst)))
  exact (Primrec.cond (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp hc1 hc2) hc3) hc4)
    (Primrec.list_cons.comp hrule (Primrec.const [])) (Primrec.const [])).of_eq fun _ => rfl

theorem primrec_regrR : Primrec fun z : Ctx =>
    regrR z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 :=
  (Primrec.list_flatMap (primrec_subsets.comp (primrec_allFacts.comp (Primrec.pair pD pQ)))
    primrec_regrBody).of_eq fun _ => rfl

/-- The body of `decR` for one method index `j`. -/
theorem primrec_decBody : Primrec₂ fun (z : Ctx) (j : ℕ) =>
    bif ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).1 &&
        z.2.2.2.2.2.1.all (fun y => !TnDesc.ordB (net z.1 z.2.1 z.2.2.2.2.1) y z.2.2.2.2.2.2 &&
          !TnDesc.ordB (net z.1 z.2.1 z.2.2.2.2.1) z.2.2.2.2.2.2 y) &&
        ((z.1.methods.getD j default).1 == ((net z.1 z.2.1 z.2.2.2.2.1).lblPair z.2.2.2.2.2.2).2)
      then
      [(((1 : ℕ), z.2.2.1, z.2.2.2.1), (some (z.2.2.2.2.1, z.2.2.2.2.2.1) : Option Tok),
        ((1 : ℕ), z.2.2.1, z.2.2.2.1),
        tokOf z.2.2.2.2.1 (z.2.2.2.2.2.1.filter (fun y => y != z.2.2.2.2.2.2)) ++
          tokOf (j + 1) (net z.1 z.2.1 (j + 1)).ids)]
    else [] := by
  refine Primrec₂.mk ?_
  have f1 {σ : Type} [Primcodable σ] {g : Ctx → σ} (h : Primrec g) :
      Primrec fun w : Ctx × ℕ => g w.1 := h.comp Primrec.fst
  have hJ : Primrec fun w : Ctx × ℕ => w.2 := Primrec.snd
  have hc1 := f1 (Primrec.fst.comp pLp)
  have hord {a b : Ctx × ℕ × ℕ → ℕ} (ha : Primrec a) (hb : Primrec b) :
      Primrec fun u : Ctx × ℕ × ℕ => !TnDesc.ordB (net u.1.1 u.1.2.1 u.1.2.2.2.2.1) (a u) (b u) :=
    Primrec.not.comp (TnDesc.primrec_ordB.comp
      (Primrec.pair (pNet.comp Primrec.fst) (Primrec.pair ha hb)))
  have hc2 : Primrec fun w : Ctx × ℕ => w.1.2.2.2.2.2.1.all
      (fun y => !TnDesc.ordB (net w.1.1 w.1.2.1 w.1.2.2.2.2.1) y w.1.2.2.2.2.2.2 &&
        !TnDesc.ordB (net w.1.1 w.1.2.1 w.1.2.2.2.2.1) w.1.2.2.2.2.2.2 y) := by
    have h0 : Primrec₂ fun (w : Ctx × ℕ) (y : ℕ) =>
        !TnDesc.ordB (net w.1.1 w.1.2.1 w.1.2.2.2.2.1) y w.1.2.2.2.2.2.2 &&
          !TnDesc.ordB (net w.1.1 w.1.2.1 w.1.2.2.2.2.1) w.1.2.2.2.2.2.2 y := by
      refine Primrec₂.mk ?_
      have e1 := hord (a := fun u => u.2.2) (b := fun u => u.2.1) (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)
      have e2 := hord (a := fun u => u.2.1) (b := fun u => u.2.2) (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)
      have hm : Primrec fun v : (Ctx × ℕ) × ℕ => (v.1.1, v.1.1.2.2.2.2.2.2, v.2) :=
        Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.pair
          ((pX.comp Primrec.fst).comp Primrec.fst) Primrec.snd)
      exact (Primrec.and.comp (e1.comp hm) (e2.comp hm)).of_eq fun v => rfl
    exact primrec_allB (f1 pL) h0
  have hc3 : Primrec fun w : Ctx × ℕ =>
      ((w.1.1.methods.getD w.2 default).1 ==
        ((net w.1.1 w.1.2.1 w.1.2.2.2.2.1).lblPair w.1.2.2.2.2.2.2).2) :=
    Primrec.beq.comp (Primrec.fst.comp ((Primrec.list_getD default).comp
      (primrec_methods.comp (f1 pD)) hJ)) (f1 (Primrec.snd.comp pLp))
  have hnew : Primrec fun w : Ctx × ℕ => tokOf (w.2 + 1) (net w.1.1 w.1.2.1 (w.2 + 1)).ids := by
    have hj1 : Primrec fun w : Ctx × ℕ => w.2 + 1 := Primrec.succ.comp hJ
    exact primrec_tokOf.comp hj1 (primrec_ids.comp (primrec_net.comp
      (Primrec.pair (Primrec.pair (f1 pD) (f1 pQ)) hj1)))
  have hrule : Primrec fun w : Ctx × ℕ =>
      (((1 : ℕ), w.1.2.2.1, w.1.2.2.2.1), (some (w.1.2.2.2.2.1, w.1.2.2.2.2.2.1) : Option Tok),
        ((1 : ℕ), w.1.2.2.1, w.1.2.2.2.1),
        tokOf w.1.2.2.2.2.1 (w.1.2.2.2.2.2.1.filter (fun y => y != w.1.2.2.2.2.2.2)) ++
          tokOf (w.2 + 1) (net w.1.1 w.1.2.1 (w.2 + 1)).ids) :=
    Primrec.pair (f1 pCtl) (Primrec.pair (f1 pItem) (Primrec.pair (f1 pCtl)
      (Primrec.list_append.comp (f1 pRest) hnew)))
  exact (Primrec.cond (Primrec.and.comp (Primrec.and.comp hc1 hc2) hc3)
    (Primrec.list_cons.comp hrule (Primrec.const [])) (Primrec.const [])).of_eq fun _ => rfl

theorem primrec_decR : Primrec fun z : Ctx =>
    decR z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 :=
  (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp
    (primrec_methods.comp pD))) primrec_decBody).of_eq fun _ => rfl

/-! ### All rules -/

theorem primrec_stepAt : Primrec fun z : Ctx =>
    progR z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 ++
      regrR z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 ++
      decR z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 :=
  Primrec.list_append.comp (Primrec.list_append.comp primrec_progR primrec_regrR) primrec_decR

theorem primrec_allToks : Primrec fun w : DomDesc × InstDesc => allToks w.1 w.2 := by
  have hpair : Primrec₂ fun (u : (DomDesc × InstDesc) × ℕ) (l : List ℕ) => ((u.2, l) : Tok) :=
    Primrec₂.mk (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hin : Primrec₂ fun (w : DomDesc × InstDesc) (k : ℕ) =>
      (subsets (net w.1 w.2 k).ids).map fun l => ((k, l) : Tok) :=
    Primrec₂.mk (Primrec.list_map (primrec_subsets.comp (primrec_ids.comp primrec_net)) hpair)
  have hr : Primrec fun w : DomDesc × InstDesc => List.range (w.1.methods.length + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp
      (primrec_methods.comp Primrec.fst)))
  exact (Primrec.list_flatMap hr hin).of_eq fun _ => rfl

/-- The type of the innermost context of `stepRules`. -/
abbrev SCtx : Type := (((DomDesc × InstDesc) × List ℕ) × List ℕ) × Tok

theorem primrec_stepRules : Primrec fun w : DomDesc × InstDesc => stepRules w.1 w.2 := by
  have hF : Primrec fun w : DomDesc × InstDesc => subsets (allFacts w.1 w.2) :=
    primrec_subsets.comp primrec_allFacts
  have hctx : Primrec fun v : SCtx × ℕ => ((v.1.1.1.1.1, v.1.1.1.1.2, v.1.1.1.2, v.1.1.2,
      v.1.2.1, v.1.2.2, v.2) : Ctx) := by
    have h1 : Primrec fun v : SCtx × ℕ => v.1 := Primrec.fst
    have h11 : Primrec fun v : SCtx × ℕ => v.1.1 := Primrec.fst.comp h1
    have h111 : Primrec fun v : SCtx × ℕ => v.1.1.1 := Primrec.fst.comp h11
    have h1111 : Primrec fun v : SCtx × ℕ => v.1.1.1.1 := Primrec.fst.comp h111
    exact Primrec.pair (Primrec.fst.comp h1111) (Primrec.pair (Primrec.snd.comp h1111)
      (Primrec.pair (Primrec.snd.comp h111) (Primrec.pair (Primrec.snd.comp h11)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp h1))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp h1)) Primrec.snd)))))
  have h4 : Primrec₂ fun (u : SCtx) (x : ℕ) =>
      progR u.1.1.1.1 u.1.1.1.2 u.1.1.2 u.1.2 u.2.1 u.2.2 x ++
        regrR u.1.1.1.1 u.1.1.1.2 u.1.1.2 u.1.2 u.2.1 u.2.2 x ++
        decR u.1.1.1.1 u.1.1.1.2 u.1.1.2 u.1.2 u.2.1 u.2.2 x := by
    have h := primrec_stepAt.comp hctx
    exact Primrec₂.mk (h.of_eq fun _ => rfl)
  have h3 : Primrec₂ fun (u : ((DomDesc × InstDesc) × List ℕ) × List ℕ) (p : Tok) =>
      p.2.flatMap fun x =>
        progR u.1.1.1 u.1.1.2 u.1.2 u.2 p.1 p.2 x ++ regrR u.1.1.1 u.1.1.2 u.1.2 u.2 p.1 p.2 x ++
          decR u.1.1.1 u.1.1.2 u.1.2 u.2 p.1 p.2 x :=
    Primrec₂.mk ((Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) h4).of_eq fun _ => rfl)
  have h2 : Primrec₂ fun (u : (DomDesc × InstDesc) × List ℕ) (lb : List ℕ) =>
      (allToks u.1.1 u.1.2).flatMap fun p => p.2.flatMap fun x =>
        progR u.1.1 u.1.2 u.2 lb p.1 p.2 x ++ regrR u.1.1 u.1.2 u.2 lb p.1 p.2 x ++
          decR u.1.1 u.1.2 u.2 lb p.1 p.2 x :=
    Primrec₂.mk ((Primrec.list_flatMap (primrec_allToks.comp (Primrec.fst.comp Primrec.fst))
      h3).of_eq fun _ => rfl)
  have h1 : Primrec₂ fun (w : DomDesc × InstDesc) (lf : List ℕ) =>
      (subsets (allFacts w.1 w.2)).flatMap fun lb =>
        (allToks w.1 w.2).flatMap fun p => p.2.flatMap fun x =>
          progR w.1 w.2 lf lb p.1 p.2 x ++ regrR w.1 w.2 lf lb p.1 p.2 x ++
            decR w.1 w.2 lf lb p.1 p.2 x :=
    Primrec₂.mk ((Primrec.list_flatMap (hF.comp Primrec.fst) h2).of_eq fun _ => rfl)
  exact (Primrec.list_flatMap hF h1).of_eq fun _ => rfl

theorem primrec_startRules : Primrec fun w : DomDesc × InstDesc => startRules w.1 w.2 := by
  have hF : Primrec fun w : DomDesc × InstDesc => subsets (allFacts w.1 w.2) :=
    primrec_subsets.comp primrec_allFacts
  have hc : Primrec₂ fun (w : DomDesc × InstDesc) (s : List ℕ) => w.2.goalList.all (memB s) :=
    Primrec₂.mk (primrec_allB (primrec_goalList.comp (Primrec.snd.comp Primrec.fst))
      (Primrec₂.mk (primrec_memB.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))
  have hnf : Primrec₂ fun (w : DomDesc × InstDesc) (s : List ℕ) => nrmF w.1 w.2 s :=
    Primrec₂.mk (primrec_nrmF.comp (Primrec.pair Primrec.fst Primrec.snd))
  have hni : Primrec fun w : DomDesc × InstDesc => nrmF w.1 w.2 w.2.initList :=
    primrec_nrmF.comp (Primrec.pair Primrec.id (primrec_initList.comp Primrec.snd))
  have hrule : Primrec₂ fun (w : DomDesc × InstDesc) (s : List ℕ) =>
      ((startC, (none : Option Tok), ((1 : ℕ), nrmF w.1 w.2 w.2.initList, nrmF w.1 w.2 s),
        ([] : List Tok)) : HRule) :=
    Primrec₂.mk (Primrec.pair (Primrec.const _) (Primrec.pair (Primrec.const _) (Primrec.pair
      (Primrec.pair (Primrec.const 1) (Primrec.pair (hni.comp Primrec.fst) hnf))
      (Primrec.const _))))
  have hb : Primrec₂ fun (w : DomDesc × InstDesc) (s : List ℕ) =>
      bif w.2.goalList.all (memB s) then
        [((startC, (none : Option Tok), ((1 : ℕ), nrmF w.1 w.2 w.2.initList, nrmF w.1 w.2 s),
          ([] : List Tok)) : HRule)]
      else [] :=
    Primrec₂.mk (Primrec.cond hc (Primrec.list_cons.comp hrule (Primrec.const []))
      (Primrec.const []))
  exact (Primrec.list_flatMap hF hb).of_eq fun _ => rfl

theorem primrec_endRules : Primrec fun w : DomDesc × InstDesc => endRules w.1 w.2 := by
  have hF : Primrec fun w : DomDesc × InstDesc => subsets (allFacts w.1 w.2) :=
    primrec_subsets.comp primrec_allFacts
  have hr : Primrec₂ fun (_ : DomDesc × InstDesc) (l : List ℕ) =>
      ((((1 : ℕ), l, l), (none : Option Tok), doneC, ([] : List Tok)) : HRule) :=
    Primrec₂.mk (Primrec.pair (Primrec.pair (Primrec.const 1) (Primrec.pair Primrec.snd
      Primrec.snd)) (Primrec.const _))
  exact (Primrec.list_map hF hr).of_eq fun _ => rfl

theorem primrec_hdRules : Primrec fun w : DomDesc × InstDesc => hdRules w.1 w.2 :=
  Primrec.list_append.comp (Primrec.list_append.comp primrec_startRules primrec_stepRules)
    primrec_endRules

/-! ### The net and the markings -/

theorem primrec_option_toList {α : Type} [Primcodable α] : Primrec (Option.toList : Option α → List α) :=
  (Primrec.option_casesOn (g := fun (_ : Option α) (a : α) => [a]) Primrec.id (Primrec.const [])
    (Primrec₂.mk (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))).of_eq
      fun o => by cases o <;> rfl

theorem primrec_ruleNet {C P : Type} [Primcodable C] [Primcodable P] [DecidableEq C]
    [DecidableEq P] : Primrec (ruleNet : List (Rule C P) → List (Trans (C ⊕ P))) := by
  have hinr : Primrec₂ fun (_ : Rule C P) (x : P) => (Sum.inr x : C ⊕ P) :=
    Primrec₂.mk (Primrec.sumInr.comp Primrec.snd)
  have ht : Primrec₂ fun (_ : List (Rule C P)) (r : Rule C P) =>
      ((Sum.inl r.1 :: r.2.1.toList.map Sum.inr, Sum.inl r.2.2.1 :: r.2.2.2.map Sum.inr) :
        Trans (C ⊕ P)) := by
    refine Primrec₂.mk ?_
    have hr : Primrec fun v : List (Rule C P) × Rule C P => v.2 := Primrec.snd
    exact Primrec.pair
      (Primrec.list_cons.comp (Primrec.sumInl.comp (Primrec.fst.comp hr))
        (Primrec.list_map (primrec_option_toList.comp (Primrec.fst.comp (Primrec.snd.comp hr)))
          (hinr.comp (hr.comp Primrec.fst) Primrec.snd)))
      (Primrec.list_cons.comp (Primrec.sumInl.comp (Primrec.fst.comp (Primrec.snd.comp
          (Primrec.snd.comp hr))))
        (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hr)))
          (hinr.comp (hr.comp Primrec.fst) Primrec.snd)))
  exact (Primrec.list_map Primrec.id ht).of_eq fun _ => rfl

theorem primrec_mapNet_encode {Q : Type} [Primcodable Q] [DecidableEq Q] :
    Primrec (mapNet (Encodable.encode : Q → ℕ)) := by
  have he : Primrec₂ fun (_ : Trans Q) (x : Q) => Encodable.encode x :=
    Primrec₂.mk (Primrec.encode.comp Primrec.snd)
  have ht : Primrec₂ fun (_ : List (Trans Q)) (t : Trans Q) =>
      ((t.1.map Encodable.encode, t.2.map Encodable.encode) : Trans ℕ) :=
    Primrec₂.mk (Primrec.pair (Primrec.list_map (Primrec.fst.comp Primrec.snd)
        (he.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (he.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))
  exact (Primrec.list_map Primrec.id ht).of_eq fun _ => rfl

theorem primrec_hdNet : Primrec fun w : DomDesc × InstDesc => hdNet w.1 w.2 :=
  (primrec_mapNet_encode.comp (primrec_ruleNet.comp primrec_hdRules)).of_eq fun _ => rfl

theorem primrec_hdM0 : Primrec hdM0 := by
  have he : Primrec₂ fun (_ : InstDesc) (t : Tok) => Encodable.encode (Sum.inr t : Ctl ⊕ Tok) :=
    Primrec₂.mk (Primrec.encode.comp (Primrec.sumInr.comp Primrec.snd))
  exact (Primrec.list_cons.comp (Primrec.const _) (Primrec.list_map
    (primrec_tokOf.comp (Primrec.const 0) (primrec_ids.comp primrec_tnI)) he)).of_eq fun _ => rfl

/-- **The reduction to Petri net reachability is primitive recursive.** -/
theorem primrec_hdInstance : Primrec fun w : DomDesc × InstDesc => (hdNet w.1 w.2, hdM0 w.2, hdM1) :=
  Primrec.pair primrec_hdNet (Primrec.pair (primrec_hdM0.comp Primrec.snd) (Primrec.const _))

end HD

end HTN
