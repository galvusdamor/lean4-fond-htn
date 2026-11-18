import ComplexityTheory.Petri.CertComplete
import ComplexityTheory.Petri.PrimAltsD
/-!
# The certificate checker is primitive recursive

`HTN.Petri.KLM.pr_accepts`: the predicate `Accepts d gp cert` is primitive recursive in
`(d, gp, cert)`.
-/

namespace HTN

namespace Petri

namespace KLM

open Primrec Classical

theorem pr_bndEq : Primrec fun x : ℕ × List CB × List (ℕ × ℤ) × ℕ =>
    bndEq x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (list_append.comp (pr_sysFrom.comp (pair fst (pair (const 0) (fst.comp snd))))
    (list_cons.comp (pair (list_append.comp (fst.comp (snd.comp snd))
        (list_cons.comp (pair (pr_totW.comp fst (fst.comp snd)) (const (-1 : ℤ))) (const [])))
      (IntPR.add.comp (IntPR.natCast.comp (snd.comp (snd.comp snd))) (const 1))) (const []))).of_eq
    fun _ => rfl

/-! ### Rule accessors -/

theorem pr_rTag : Primrec rTag := fst.of_eq fun _ => rfl
theorem pr_rPos : Primrec rPos := (fst.comp snd).of_eq fun _ => rfl
theorem pr_rR : Primrec rR := (fst.comp (snd.comp snd)).of_eq fun _ => rfl
theorem pr_rCe : Primrec rCe := (fst.comp (snd.comp (snd.comp snd))).of_eq fun _ => rfl
theorem pr_rJ : Primrec rJ := (fst.comp (snd.comp (snd.comp (snd.comp snd)))).of_eq fun _ => rfl
theorem pr_rB : Primrec rB :=
  (fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))).of_eq fun _ => rfl
theorem pr_rNs : Primrec rNs :=
  (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))).of_eq fun _ => rfl

theorem pr_rBlk : Primrec₂ rBlk := ((list_getD default).comp fst (pr_rPos.comp snd)).of_eq fun _ => rfl

/-! ### Alternatives and children -/

section

variable {X : Type*} [Primcodable X] {fd : X → ℕ} {fgp : X → List CB} {fr : X → CRule}

theorem pr_tagIs (hr : Primrec fr) (k : ℕ) : PrimrecPred fun x => rTag (fr x) = k :=
  Primrec.eq.comp (pr_rTag.comp hr) (const k)

end

theorem pr_ralts : Primrec fun x : ℕ × List CB × CRule => ralts x.1 x.2.1 x.2.2 := by
  have hd : Primrec fun x : ℕ × List CB × CRule => x.1 := fst
  have hr : Primrec fun x : ℕ × List CB × CRule => x.2.2 := snd.comp snd
  have hb : Primrec fun x : ℕ × List CB × CRule => rBlk x.2.1 x.2.2 := pr_rBlk.comp (fst.comp snd) hr
  have h1 := pr_cprune.comp hb (pr_rR.comp hr)
  have h2 := pr_csplit.comp hb (pr_rR.comp hr)
  have h3 := pr_cedgeAlts.comp (pair hd (pair hb (pair (pr_rCe.comp hr) (pr_rB.comp hr))))
  have h4 := pr_cinpAlts.comp (pair hd (pair hb (pair (pr_rJ.comp hr) (pr_rB.comp hr))))
  have h5 := pr_coutAlts.comp (pair hd (pair hb (pair (pr_rJ.comp hr) (pr_rB.comp hr))))
  have h6 := pr_cdAlts.comp (pair hd (pair hb (pr_rNs.comp hr)))
  have h7 := pr_cdAltsB.comp (pair hd (pair hb (pr_rNs.comp hr)))
  exact (Primrec.ite (pr_tagIs hr 1) h1 (Primrec.ite (pr_tagIs hr 2) h2
    (Primrec.ite (pr_tagIs hr 3) h3 (Primrec.ite (pr_tagIs hr 4) h4
    (Primrec.ite (pr_tagIs hr 5) h5 (Primrec.ite (pr_tagIs hr 6) h6
    (Primrec.ite (pr_tagIs hr 7) h7 (const [])))))))).of_eq fun _ => rfl

theorem pr_children : Primrec fun x : ℕ × List CB × CRule => children x.1 x.2.1 x.2.2 :=
  (list_map pr_ralts (list_append.comp (list_append.comp
    (PR.list_take.comp (fst.comp (snd.comp fst)) (pr_rPos.comp (snd.comp (snd.comp fst)))) snd)
    (PR.list_drop.comp (fst.comp (snd.comp fst)) (succ.comp (pr_rPos.comp (snd.comp (snd.comp fst)))))).to₂).of_eq
    fun _ => rfl

/-! ### Side conditions -/

theorem pr_localOK : PrimrecPred fun x : ℕ × List CB × CRule => localOK x.1 x.2.1 x.2.2 := by
  have hd : Primrec fun x : ℕ × List CB × CRule => x.1 := fst
  have hgp : Primrec fun x : ℕ × List CB × CRule => x.2.1 := fst.comp snd
  have hr : Primrec fun x : ℕ × List CB × CRule => x.2.2 := snd.comp snd
  have hb : Primrec fun x : ℕ × List CB × CRule => rBlk x.2.1 x.2.2 := pr_rBlk.comp hgp hr
  have hc : Primrec fun x : ℕ × List CB × CRule => cComp (rBlk x.2.1 x.2.2) := pr_cComp.comp hb
  have hfz : ∀ {f : ℕ × List CB × CRule → List TEq}, Primrec f →
      PrimrecPred fun x => feasB (f x) = false := fun hf =>
    Primrec.eq.comp (primrec_feasB.comp hf) (const false)
  have c0 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 0 ∧ feasB (sysFrom x.1 0 x.2.1) = false :=
    PrimrecPred.and (pr_tagIs hr 0) (hfz (pr_sysFrom.comp (pair hd (pair (const 0) hgp))))
  have c1 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 1 ∧ cEntry (cComp (rBlk x.2.1 x.2.2)) ∈ rR x.2.2 ∧
        ∀ e ∈ cEdges (cComp (rBlk x.2.1 x.2.2)), e.1 ∈ rR x.2.2 → e.2.2 ∈ rR x.2.2 :=
    PrimrecPred.and (pr_tagIs hr 1) (PrimrecPred.and
      (PR.list_mem.comp (pr_cEntry.comp hc) (pr_rR.comp hr))
      (PR.forall_mem' (pr_cEdges.comp hc) (PR.imp
        (PR.list_mem.comp (fst.comp snd) (pr_rR.comp (hr.comp fst)))
        (PR.list_mem.comp (snd.comp (snd.comp snd)) (pr_rR.comp (hr.comp fst))))))
  have c2 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 2 ∧ cEntry (cComp (rBlk x.2.1 x.2.2)) ∈ rR x.2.2 ∧
        ∀ e ∈ cEdges (cComp (rBlk x.2.1 x.2.2)), e.2.2 ∈ rR x.2.2 → e.1 ∈ rR x.2.2 :=
    PrimrecPred.and (pr_tagIs hr 2) (PrimrecPred.and
      (PR.list_mem.comp (pr_cEntry.comp hc) (pr_rR.comp hr))
      (PR.forall_mem' (pr_cEdges.comp hc) (PR.imp
        (PR.list_mem.comp (snd.comp (snd.comp snd)) (pr_rR.comp (hr.comp fst)))
        (PR.list_mem.comp (fst.comp snd) (pr_rR.comp (hr.comp fst))))))
  have c3 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 3 ∧ rCe x.2.2 ∈ cEdges (cComp (rBlk x.2.1 x.2.2)) ∧
        feasB (bndEq x.1 x.2.1 (edgeLin (d := x.1) x.2.1 (rPos x.2.2) (rCe x.2.2)) (rB x.2.2)) = false :=
    PrimrecPred.and (pr_tagIs hr 3) (PrimrecPred.and
      (PR.list_mem.comp (pr_rCe.comp hr) (pr_cEdges.comp hc))
      (hfz (pr_bndEq.comp (pair hd (pair hgp (pair
        (pr_edgeLin.comp (pair hd (pair hgp (pair (pr_rPos.comp hr) (pr_rCe.comp hr)))))
        (pr_rB.comp hr)))))))
  have c4 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 4 ∧ rJ x.2.2 < x.1 ∧ (cInp (rBlk x.2.1 x.2.2)).getD (rJ x.2.2) none = none ∧
        feasB (bndEq x.1 x.2.1 [(offs (d := x.1) x.2.1 (rPos x.2.2) + rJ x.2.2, 1)] (rB x.2.2)) = false :=
    PrimrecPred.and (pr_tagIs hr 4) (PrimrecPred.and (nat_lt.comp (pr_rJ.comp hr) hd)
      (PrimrecPred.and (Primrec.eq.comp ((list_getD none).comp (pr_cInp.comp hb) (pr_rJ.comp hr))
        (const none))
      (hfz (pr_bndEq.comp (pair hd (pair hgp (pair
        (list_cons.comp (pair (nat_add.comp (pr_offs.comp (pair hd (pair hgp (pr_rPos.comp hr))))
          (pr_rJ.comp hr)) (const (1 : ℤ))) (const []))
        (pr_rB.comp hr))))))))
  have c5 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 5 ∧ rJ x.2.2 < x.1 ∧ (cOut (rBlk x.2.1 x.2.2)).getD (rJ x.2.2) none = none ∧
        feasB (bndEq x.1 x.2.1 [(offs (d := x.1) x.2.1 (rPos x.2.2) + x.1 + rJ x.2.2, 1)]
          (rB x.2.2)) = false :=
    PrimrecPred.and (pr_tagIs hr 5) (PrimrecPred.and (nat_lt.comp (pr_rJ.comp hr) hd)
      (PrimrecPred.and (Primrec.eq.comp ((list_getD none).comp (pr_cOut.comp hb) (pr_rJ.comp hr))
        (const none))
      (hfz (pr_bndEq.comp (pair hd (pair hgp (pair
        (list_cons.comp (pair (nat_add.comp (nat_add.comp
            (pr_offs.comp (pair hd (pair hgp (pr_rPos.comp hr)))) hd)
          (pr_rJ.comp hr)) (const (1 : ℤ))) (const []))
        (pr_rB.comp hr))))))))
  have c6 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 6 ∧ cEntryOK x.1 (rBlk x.2.1 x.2.2) ∧ cDCert x.1 (rBlk x.2.1 x.2.2) (rNs x.2.2) :=
    PrimrecPred.and (pr_tagIs hr 6) (PrimrecPred.and (pr_cEntryOK.comp (pair hd hb))
      (pr_cDCert.comp (pair hd (pair hb (pr_rNs.comp hr)))))
  have c7 : PrimrecPred fun x : ℕ × List CB × CRule =>
      rTag x.2.2 = 7 ∧ cExitOK x.1 (rBlk x.2.1 x.2.2) ∧
        cDCert x.1 (crevB (rBlk x.2.1 x.2.2)) (rNs x.2.2) :=
    PrimrecPred.and (pr_tagIs hr 7) (PrimrecPred.and (pr_cExitOK.comp (pair hd hb))
      (pr_cDCert.comp (pair hd (pair (pr_crevB.comp hb) (pr_rNs.comp hr)))))
  exact (c0.or (PrimrecPred.and (nat_lt.comp (pr_rPos.comp hr) (list_length.comp hgp))
    (c1.or (c2.or (c3.or (c4.or (c5.or (c6.or c7)))))))).of_eq fun _ => Iff.rfl

/-! ### Certificates -/

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

theorem pr_nodeOK : PrimrecPred fun x : ℕ × List CNode × CNode => nodeOK x.1 x.2.1 x.2.2 :=
  (PrimrecPred.and (pr_localOK.comp (pair fst (pair (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd)))))
    (PR.forall_mem' (pr_children.comp (pair fst (pair (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd)))))
      (PR.exists_mem' (fst.comp (snd.comp fst))
        (Primrec.eq.comp (fst.comp snd) (snd.comp fst))))).of_eq fun _ => Iff.rfl

theorem pr_valid : PrimrecPred fun x : ℕ × List CNode => Valid x.1 x.2 :=
  (PR.forall_mem' (list_range.comp (list_length.comp snd))
    (pr_nodeOK.comp (pair (fst.comp fst) (pair (PR.list_take.comp (snd.comp fst) snd)
      ((list_getD default).comp (snd.comp fst) snd))))).of_eq fun _ => Iff.rfl

/-- **The certificate checker is primitive recursive.** -/
theorem pr_accepts : PrimrecPred fun x : ℕ × List CB × List CNode => Accepts x.1 x.2.1 x.2.2 :=
  (PrimrecPred.and (pr_valid.comp (pair fst (snd.comp snd)))
    (PR.exists_mem' (snd.comp snd) (Primrec.eq.comp (fst.comp snd) (fst.comp (snd.comp fst))))).of_eq
    fun _ => Iff.rfl

end KLM

end Petri

end HTN
