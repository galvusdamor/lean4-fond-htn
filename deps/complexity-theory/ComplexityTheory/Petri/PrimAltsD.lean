import ComplexityTheory.Petri.CAltsD
import ComplexityTheory.Petri.PrimAlts
import ComplexityTheory.Petri.RE
/-!
# The concrete alternatives and certificate conditions of step (d) are primitive recursive
-/

namespace HTN

namespace Petri

namespace PR

variable {α β : Type*} [Primcodable α] [Primcodable β]

theorem forall_mem' {f : α → List β} {Q : α × β → Prop} (hf : Primrec f) (hq : PrimrecPred Q) :
    PrimrecPred fun a => ∀ b ∈ f a, Q (a, b) :=
  primrecPred_forall_mem (q := fun a b => Q (a, b)) hf hq

theorem exists_mem' {f : α → List β} {Q : α × β → Prop} (hf : Primrec f) (hq : PrimrecPred Q) :
    PrimrecPred fun a => ∃ b ∈ f a, Q (a, b) :=
  primrecPred_exists_mem (q := fun a b => Q (a, b)) hf hq

theorem imp {P Q : α → Prop} (hp : PrimrecPred P) (hq : PrimrecPred Q) :
    PrimrecPred fun a => P a → Q a :=
  (hp.not.or hq).of_eq fun _ => imp_iff_not_or.symm

theorem isSome {f : α → Option β} (hf : Primrec f) : PrimrecPred fun a => (f a).isSome = true :=
  Primrec.eq.comp (Primrec.option_isSome.comp hf) (Primrec.const true)

end PR

namespace KLM

open Primrec Classical

theorem pr_cCompat : PrimrecPred fun x : ℕ × CW × CW => cCompat x.1 x.2.1 x.2.2 :=
  (PR.forall_mem' (list_range.comp fst)
    (PR.imp (PR.isSome ((list_getD none).comp (fst.comp (snd.comp fst)) snd))
      (PR.imp (PR.isSome ((list_getD none).comp (snd.comp (snd.comp fst)) snd))
        (Primrec.eq.comp ((list_getD none).comp (fst.comp (snd.comp fst)) snd)
          ((list_getD none).comp (snd.comp (snd.comp fst)) snd))))).of_eq fun _ => Iff.rfl

theorem pr_cimpose : Primrec fun x : ℕ × CW × CW => cimpose x.1 x.2.1 x.2.2 :=
  (list_map (list_range.comp fst)
    (Primrec.ite (PR.isSome ((list_getD none).comp (snd.comp (snd.comp fst)) snd))
      ((list_getD none).comp (snd.comp (snd.comp fst)) snd)
      ((list_getD none).comp (fst.comp (snd.comp fst)) snd)).to₂).of_eq fun _ => rfl

theorem pr_cGEdge : PrimrecPred fun x : ℕ × CW × CV × CW => cGEdge x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hm : Primrec fun p : (ℕ × CW × CV × CW) × ℕ => p.1.2.1.getD p.2 none :=
    (list_getD none).comp (fst.comp (snd.comp fst)) snd
  have hm' : Primrec fun p : (ℕ × CW × CV × CW) × ℕ => p.1.2.2.2.getD p.2 none :=
    (list_getD none).comp (snd.comp (snd.comp (snd.comp fst))) snd
  have ha : Primrec fun p : (ℕ × CW × CV × CW) × ℕ => p.1.2.2.1.getD p.2 0 :=
    (list_getD 0).comp (fst.comp (snd.comp (snd.comp fst))) snd
  have hv : Primrec fun p : (ℕ × CW × CV × CW) × ℕ =>
      (((p.1.2.1.getD p.2 none).getD 0 : ℕ) : ℤ) + p.1.2.2.1.getD p.2 0 :=
    IntPR.add.comp (IntPR.natCast.comp (option_getD.comp hm (const 0))) ha
  exact (PrimrecPred.and
    (PR.forall_mem' (list_range.comp fst) (PR.imp (PR.isSome hm) (IntPR.le.comp (const 0) hv)))
    (PR.forall_mem' (list_range.comp fst) (PR.imp (PR.isSome hm')
      (PrimrecPred.and (PR.isSome hm)
        (Primrec.eq.comp (IntPR.natCast.comp (option_getD.comp hm' (const 0))) hv))))).of_eq
    fun _ => Iff.rfl

theorem pr_normV : Primrec₂ normV :=
  (list_map (list_range.comp fst) ((list_getD 0).comp (snd.comp fst) snd).to₂).of_eq fun _ => rfl

theorem pr_cnd : Primrec₂ cnd := ((list_getD (0, [])).comp fst snd).of_eq fun _ => rfl

theorem pr_cgP : PrimrecPred fun x : ℕ × List (ℕ × CW) × ℕ × ℕ × CE =>
    cgP x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hNs : Primrec fun x : ℕ × List (ℕ × CW) × ℕ × ℕ × CE => x.2.1 := fst.comp snd
  have hi := pr_cnd.comp hNs (fst.comp (snd.comp snd))
  have hi' := pr_cnd.comp hNs (fst.comp (snd.comp (snd.comp snd)))
  have he : Primrec fun x : ℕ × List (ℕ × CW) × ℕ × ℕ × CE => x.2.2.2.2 :=
    snd.comp (snd.comp (snd.comp snd))
  exact (PrimrecPred.and (Primrec.eq.comp (fst.comp hi) (fst.comp he))
    (PrimrecPred.and (Primrec.eq.comp (fst.comp hi') (snd.comp (snd.comp he)))
      (pr_cGEdge.comp (pair fst (pair (snd.comp hi) (pair (fst.comp (snd.comp he))
        (snd.comp hi'))))))).of_eq fun _ => Iff.rfl

theorem pr_cgRaw : Primrec fun x : ℕ × CC × List (ℕ × CW) => cgRaw x.1 x.2.1 x.2.2 := by
  have hf : Primrec fun r : (((ℕ × CC × List (ℕ × CW)) × ℕ) × ℕ) × CE =>
      decide (cgP r.1.1.1.1 r.1.1.1.2.2 r.1.1.2 r.1.2 r.2) :=
    (pr_cgP.comp (pair (fst.comp (fst.comp (fst.comp fst)))
      (pair (snd.comp (snd.comp (fst.comp (fst.comp fst))))
        (pair (snd.comp (fst.comp fst)) (pair (snd.comp fst) snd))))).decide
  have hm : Primrec fun r : (((ℕ × CC × List (ℕ × CW)) × ℕ) × ℕ) × CE =>
      (r.1.1.2, normV r.1.1.1.1 r.2.2.1, r.1.2) :=
    pair (snd.comp (fst.comp fst))
      (pair (pr_normV.comp (fst.comp (fst.comp (fst.comp fst))) (fst.comp (snd.comp snd)))
        (snd.comp fst))
  have hq : Primrec fun q : ((ℕ × CC × List (ℕ × CW)) × ℕ) × ℕ =>
      ((cEdges q.1.1.2.1).filter fun e => decide (cgP q.1.1.1 q.1.1.2.2 q.1.2 q.2 e)).map
        fun e => (q.1.2, normV q.1.1.1 e.2.1, q.2) :=
    list_map (PR.list_filter (pr_cEdges.comp (fst.comp (snd.comp (fst.comp fst)))) hf.to₂) hm.to₂
  have hi : Primrec fun p : (ℕ × CC × List (ℕ × CW)) × ℕ =>
      (List.range p.1.2.2.length).flatMap fun i' =>
        ((cEdges p.1.2.1).filter fun e => decide (cgP p.1.1 p.1.2.2 p.2 i' e)).map
          fun e => (p.2, normV p.1.1 e.2.1, i') :=
    list_flatMap (list_range.comp (list_length.comp (snd.comp (snd.comp fst)))) hq.to₂
  exact (list_flatMap (list_range.comp (list_length.comp (snd.comp snd))) hi.to₂).of_eq
    fun _ => rfl

theorem pr_cgEdges : Primrec fun x : ℕ × CC × List (ℕ × CW) => cgEdges x.1 x.2.1 x.2.2 :=
  (PR.list_dedup.comp pr_cgRaw).of_eq fun _ => rfl

theorem pr_cgComp : Primrec fun x : ℕ × CC × List (ℕ × CW) × ℕ × ℕ =>
    cgComp x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
  (pair (list_range.comp (list_length.comp (fst.comp (snd.comp snd))))
    (pair (list_map (fst.comp (snd.comp snd)) (snd.comp snd).to₂)
      (pair (pr_cgEdges.comp (pair fst (pair (fst.comp snd) (fst.comp (snd.comp snd)))))
        (snd.comp (snd.comp snd))))).of_eq fun _ => rfl

theorem pr_cdAlts : Primrec fun x : ℕ × CB × List (ℕ × CW) => cdAlts x.1 x.2.1 x.2.2 := by
  have hNs : Primrec fun q : (ℕ × CB × List (ℕ × CW)) × ℕ × ℕ => q.1.2.2 := snd.comp (snd.comp fst)
  have hb : Primrec fun q : (ℕ × CB × List (ℕ × CW)) × ℕ × ℕ => q.1.2.1 := fst.comp (snd.comp fst)
  have hd : Primrec fun q : (ℕ × CB × List (ℕ × CW)) × ℕ × ℕ => q.1.1 := fst.comp fst
  have h1 := pr_cnd.comp hNs (fst.comp snd)
  have h2 := pr_cnd.comp hNs (snd.comp snd)
  have hpairs : Primrec fun x : ℕ × CB × List (ℕ × CW) =>
      (List.range x.2.2.length).flatMap fun i₀ => (List.range x.2.2.length).map fun i₁ => (i₀, i₁) :=
    list_flatMap (list_range.comp (list_length.comp (snd.comp snd)))
      (list_map (list_range.comp (list_length.comp (snd.comp (snd.comp fst))))
        (pair (snd.comp fst) snd).to₂).to₂
  have hc : PrimrecPred fun q : (ℕ × CB × List (ℕ × CW)) × ℕ × ℕ =>
      (cnd q.1.2.2 q.2.1).1 = cEntry (cComp q.1.2.1) ∧ (cnd q.1.2.2 q.2.2).1 = cExit (cComp q.1.2.1) ∧
        cCompat q.1.1 (cInp q.1.2.1) (cnd q.1.2.2 q.2.1).2 ∧
          cCompat q.1.1 (cOut q.1.2.1) (cnd q.1.2.2 q.2.2).2 :=
    PrimrecPred.and (Primrec.eq.comp (fst.comp h1) (pr_cEntry.comp (pr_cComp.comp hb)))
      (PrimrecPred.and (Primrec.eq.comp (fst.comp h2) (pr_cExit.comp (pr_cComp.comp hb)))
        (PrimrecPred.and (pr_cCompat.comp (pair hd (pair (pr_cInp.comp hb) (snd.comp h1))))
          (pr_cCompat.comp (pair hd (pair (pr_cOut.comp hb) (snd.comp h2))))))
  exact (list_map (PR.list_filter hpairs hc.decide.to₂)
    (list_cons.comp (pair (pr_cPre.comp hb) (pair
      (pr_cimpose.comp (pair hd (pair (pr_cInp.comp hb) (snd.comp h1))))
      (pair (pr_cgComp.comp (pair hd (pair (pr_cComp.comp hb) (pair hNs snd))))
        (pr_cimpose.comp (pair hd (pair (pr_cOut.comp hb) (snd.comp h2)))))))
      (const [])).to₂).of_eq fun _ => rfl

theorem pr_crevC : Primrec crevC :=
  (pair pr_cNodes (pair pr_cLabs (pair (list_map pr_cEdges
      (pair (snd.comp (snd.comp snd)) (pair (list_map (fst.comp (snd.comp snd))
        (IntPR.neg.comp snd).to₂) (fst.comp snd))).to₂)
    (pair pr_cExit pr_cEntry)))).of_eq fun _ => rfl

theorem pr_crevB : Primrec crevB :=
  (pair (const []) (pair pr_cOut (pair (pr_crevC.comp pr_cComp) pr_cInp))).of_eq fun _ => rfl

theorem pr_cunrev : Primrec₂ cunrev :=
  (pair snd (pair (pr_cOut.comp fst) (pair (pr_crevC.comp (pr_cComp.comp fst))
    (pr_cInp.comp fst)))).of_eq fun _ => rfl

theorem pr_cdAltsB : Primrec fun x : ℕ × CB × List (ℕ × CW) => cdAltsB x.1 x.2.1 x.2.2 :=
  (list_map (pr_cdAlts.comp (pair fst (pair (pr_crevB.comp (fst.comp snd)) (snd.comp snd))))
    (list_map snd (pr_cunrev.comp snd (pr_cPre.comp (fst.comp (snd.comp (fst.comp fst))))).to₂).to₂).of_eq
    fun _ => rfl

theorem pr_clab : Primrec fun x : CC × ℕ × ℕ => clab x.1 x.2.1 x.2.2 :=
  ((list_getD none).comp ((list_getD []).comp (pr_cLabs.comp fst) (fst.comp snd))
    (snd.comp snd)).of_eq fun _ => rfl

/-! ### Certificate conditions -/

theorem pr_G1 : PrimrecPred fun y : ℕ × CW × CV => ∀ j ∈ List.range y.1,
    (y.2.1.getD j none).isSome → 0 ≤ (((y.2.1.getD j none).getD 0 : ℕ) : ℤ) + y.2.2.getD j 0 :=
  PR.forall_mem' (list_range.comp fst) (PR.imp (PR.isSome ((list_getD none).comp (fst.comp (snd.comp fst)) snd))
    (IntPR.le.comp (const 0) (IntPR.add.comp (IntPR.natCast.comp (option_getD.comp
      ((list_getD none).comp (fst.comp (snd.comp fst)) snd) (const 0)))
      ((list_getD 0).comp (snd.comp (snd.comp fst)) snd))))

theorem pr_G2 : PrimrecPred fun y : ℕ × CW × CV × CW => ∀ j ∈ List.range y.1,
    (y.2.2.2.getD j none).isSome → (y.2.1.getD j none).isSome ∧
      (((y.2.2.2.getD j none).getD 0 : ℕ) : ℤ) = (((y.2.1.getD j none).getD 0 : ℕ) : ℤ) + y.2.2.1.getD j 0 := by
  have hm : Primrec fun p : (ℕ × CW × CV × CW) × ℕ => p.1.2.1.getD p.2 none :=
    (list_getD none).comp (fst.comp (snd.comp fst)) snd
  have hm' : Primrec fun p : (ℕ × CW × CV × CW) × ℕ => p.1.2.2.2.getD p.2 none :=
    (list_getD none).comp (snd.comp (snd.comp (snd.comp fst))) snd
  have ha : Primrec fun p : (ℕ × CW × CV × CW) × ℕ => p.1.2.2.1.getD p.2 0 :=
    (list_getD 0).comp (fst.comp (snd.comp (snd.comp fst))) snd
  exact PR.forall_mem' (list_range.comp fst) (PR.imp (PR.isSome hm')
    (PrimrecPred.and (PR.isSome hm) (Primrec.eq.comp (IntPR.natCast.comp (option_getD.comp hm' (const 0)))
      (IntPR.add.comp (IntPR.natCast.comp (option_getD.comp hm (const 0))) ha))))

theorem pr_H1 : PrimrecPred fun y : ℕ × CC × (ℕ × CW) => ∀ j ∈ List.range y.1,
    (clab y.2.1 y.2.2.1 j).isSome → y.2.2.2.getD j none = clab y.2.1 y.2.2.1 j := by
  have hc : Primrec fun p : (ℕ × CC × (ℕ × CW)) × ℕ => clab p.1.2.1 p.1.2.2.1 p.2 :=
    pr_clab.comp (pair (fst.comp (snd.comp fst)) (pair (fst.comp (snd.comp (snd.comp fst))) snd))
  exact PR.forall_mem' (list_range.comp fst) (PR.imp (PR.isSome hc)
    (Primrec.eq.comp ((list_getD none).comp (snd.comp (snd.comp (snd.comp fst))) snd) hc))

theorem pr_H2 : PrimrecPred fun y : ℕ × CW × CW =>
    (∀ j ∈ List.range y.1, y.2.1.getD j none = none → y.2.2.getD j none = none) ∧
      ∀ j ∈ List.range y.1, (y.2.2.getD j none).isSome → y.2.2.getD j none = y.2.1.getD j none :=
  PrimrecPred.and
    (PR.forall_mem' (list_range.comp fst) (PR.imp
      (Primrec.eq.comp ((list_getD none).comp (fst.comp (snd.comp fst)) snd) (const none))
      (Primrec.eq.comp ((list_getD none).comp (snd.comp (snd.comp fst)) snd) (const none))))
    (PR.forall_mem' (list_range.comp fst) (PR.imp
      (PR.isSome ((list_getD none).comp (snd.comp (snd.comp fst)) snd))
      (Primrec.eq.comp ((list_getD none).comp (snd.comp (snd.comp fst)) snd)
        ((list_getD none).comp (fst.comp (snd.comp fst)) snd))))

theorem pr_cDCert : PrimrecPred fun x : ℕ × CB × List (ℕ × CW) => cDCert x.1 x.2.1 x.2.2 := by
  have p1 : PrimrecPred fun x : ℕ × CB × List (ℕ × CW) => ∀ p ∈ x.2.2,
      ∀ j ∈ List.range x.1, (clab (cComp x.2.1) p.1 j).isSome → p.2.getD j none = clab (cComp x.2.1) p.1 j :=
    PR.forall_mem' (snd.comp snd) (pr_H1.comp (pair (fst.comp fst) (pair (pr_cComp.comp (fst.comp (snd.comp fst))) snd)))
  have p2 : PrimrecPred fun x : ℕ × CB × List (ℕ × CW) => ∃ p ∈ x.2.2, p.1 = cEntry (cComp x.2.1) ∧
      ((∀ j ∈ List.range x.1, (cInp x.2.1).getD j none = none → p.2.getD j none = none) ∧
        ∀ j ∈ List.range x.1, (p.2.getD j none).isSome → p.2.getD j none = (cInp x.2.1).getD j none) :=
    PR.exists_mem' (snd.comp snd) (PrimrecPred.and
      (Primrec.eq.comp (fst.comp snd) (pr_cEntry.comp (pr_cComp.comp (fst.comp (snd.comp fst)))))
      (pr_H2.comp (pair (fst.comp fst) (pair (pr_cInp.comp (fst.comp (snd.comp fst))) (snd.comp snd)))))
  have p3 : PrimrecPred fun x : ℕ × CB × List (ℕ × CW) => ∀ p ∈ x.2.2, ∀ e ∈ cEdges (cComp x.2.1),
      e.1 = p.1 → (∀ j ∈ List.range x.1, (p.2.getD j none).isSome →
        0 ≤ (((p.2.getD j none).getD 0 : ℕ) : ℤ) + e.2.1.getD j 0) →
      ∃ p' ∈ x.2.2, p'.1 = e.2.2 ∧ ∀ j ∈ List.range x.1, (p'.2.getD j none).isSome →
        (p.2.getD j none).isSome ∧
          (((p'.2.getD j none).getD 0 : ℕ) : ℤ) = (((p.2.getD j none).getD 0 : ℕ) : ℤ) + e.2.1.getD j 0 := by
    have i3 : PrimrecPred fun r : ((((ℕ × CB × List (ℕ × CW)) × (ℕ × CW)) × CE) × (ℕ × CW)) =>
        r.2.1 = r.1.2.2.2 ∧ ∀ j ∈ List.range r.1.1.1.1, (r.2.2.getD j none).isSome →
          (r.1.1.2.2.getD j none).isSome ∧ (((r.2.2.getD j none).getD 0 : ℕ) : ℤ) =
            (((r.1.1.2.2.getD j none).getD 0 : ℕ) : ℤ) + r.1.2.2.1.getD j 0 :=
      PrimrecPred.and (Primrec.eq.comp (fst.comp snd) (snd.comp (snd.comp (snd.comp fst))))
        (pr_G2.comp (pair (fst.comp (fst.comp (fst.comp fst))) (pair (snd.comp (snd.comp (fst.comp fst)))
          (pair (fst.comp (snd.comp (snd.comp fst))) (snd.comp snd)))))
    have g1 : PrimrecPred fun q : ((ℕ × CB × List (ℕ × CW)) × (ℕ × CW)) × CE =>
        ∀ j ∈ List.range q.1.1.1, (q.1.2.2.getD j none).isSome →
          0 ≤ (((q.1.2.2.getD j none).getD 0 : ℕ) : ℤ) + q.2.2.1.getD j 0 :=
      pr_G1.comp (pair (fst.comp (fst.comp fst)) (pair (snd.comp (snd.comp fst)) (fst.comp (snd.comp snd))))
    have ex : PrimrecPred fun q : ((ℕ × CB × List (ℕ × CW)) × (ℕ × CW)) × CE =>
        ∃ p' ∈ q.1.1.2.2, p'.1 = q.2.2.2 ∧ ∀ j ∈ List.range q.1.1.1, (p'.2.getD j none).isSome →
          (q.1.2.2.getD j none).isSome ∧ (((p'.2.getD j none).getD 0 : ℕ) : ℤ) =
            (((q.1.2.2.getD j none).getD 0 : ℕ) : ℤ) + q.2.2.1.getD j 0 :=
      PR.exists_mem' (snd.comp (snd.comp (fst.comp fst))) i3
    have i2 : PrimrecPred fun q : ((ℕ × CB × List (ℕ × CW)) × (ℕ × CW)) × CE =>
        q.2.1 = q.1.2.1 → (∀ j ∈ List.range q.1.1.1, (q.1.2.2.getD j none).isSome →
          0 ≤ (((q.1.2.2.getD j none).getD 0 : ℕ) : ℤ) + q.2.2.1.getD j 0) →
        ∃ p' ∈ q.1.1.2.2, p'.1 = q.2.2.2 ∧ ∀ j ∈ List.range q.1.1.1, (p'.2.getD j none).isSome →
          (q.1.2.2.getD j none).isSome ∧ (((p'.2.getD j none).getD 0 : ℕ) : ℤ) =
            (((q.1.2.2.getD j none).getD 0 : ℕ) : ℤ) + q.2.2.1.getD j 0 :=
      PR.imp (Primrec.eq.comp (fst.comp snd) (fst.comp (snd.comp fst))) (PR.imp g1 ex)
    exact PR.forall_mem' (snd.comp snd)
      (PR.forall_mem' (pr_cEdges.comp (pr_cComp.comp (fst.comp (snd.comp fst)))) i2)
  exact (p1.and (p2.and p3)).of_eq fun _ => Iff.rfl

theorem pr_cEntryOK : PrimrecPred fun x : ℕ × CB => cEntryOK x.1 x.2 :=
  (pr_H1.comp (pair fst (pair (pr_cComp.comp snd) (pair (pr_cEntry.comp (pr_cComp.comp snd))
    (pr_cInp.comp snd))))).of_eq fun _ => Iff.rfl

theorem pr_cExitOK : PrimrecPred fun x : ℕ × CB => cExitOK x.1 x.2 :=
  (pr_H1.comp (pair fst (pair (pr_cComp.comp snd) (pair (pr_cExit.comp (pr_cComp.comp snd))
    (pr_cOut.comp snd))))).of_eq fun _ => Iff.rfl

end KLM

end Petri

end HTN
