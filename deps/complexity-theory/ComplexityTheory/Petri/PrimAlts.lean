import ComplexityTheory.Petri.CAlts
import ComplexityTheory.Petri.PrimSys
/-!
# The concrete alternatives of steps (a), (b), (c) are primitive recursive
-/

namespace HTN

namespace Petri

namespace KLM

open Primrec Classical

theorem pr_crestrIn : Primrec fun x : CB × List ℕ × ℕ × ℕ =>
    crestr x.1 (fun n => decide (n ∈ x.2.1)) x.2.2.1 x.2.2.2 :=
  (pair (PR.list_filter (pr_cNodes.comp (pr_cComp.comp fst))
      (PR.list_mem.comp snd (fst.comp (snd.comp fst))).decide.to₂)
    (pair (pr_cLabs.comp (pr_cComp.comp fst))
      (pair (PR.list_filter (pr_cEdges.comp (pr_cComp.comp fst))
        (Primrec.and.comp (PR.list_mem.comp (fst.comp snd) (fst.comp (snd.comp fst))).decide
          (PR.list_mem.comp (snd.comp (snd.comp snd)) (fst.comp (snd.comp fst))).decide).to₂)
        (pair (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd)))))).of_eq fun _ => rfl

theorem pr_crestrNotIn : Primrec fun x : CB × List ℕ × ℕ × ℕ =>
    crestr x.1 (fun n => decide (n ∉ x.2.1)) x.2.2.1 x.2.2.2 :=
  (pair (PR.list_filter (pr_cNodes.comp (pr_cComp.comp fst))
      (PR.list_mem.comp snd (fst.comp (snd.comp fst))).not.decide.to₂)
    (pair (pr_cLabs.comp (pr_cComp.comp fst))
      (pair (PR.list_filter (pr_cEdges.comp (pr_cComp.comp fst))
        (Primrec.and.comp (PR.list_mem.comp (fst.comp snd) (fst.comp (snd.comp fst))).not.decide
          (PR.list_mem.comp (snd.comp (snd.comp snd)) (fst.comp (snd.comp fst))).not.decide).to₂)
        (pair (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd)))))).of_eq fun _ => rfl

theorem pr_cprune : Primrec₂ cprune :=
  (Primrec.ite (PR.list_mem.comp (pr_cExit.comp (pr_cComp.comp fst)) snd)
    (list_cons.comp (list_cons.comp (pair (pr_cPre.comp fst) (pair (pr_cInp.comp fst)
      (pair (pr_crestrIn.comp (pair fst (pair snd (pair (pr_cEntry.comp (pr_cComp.comp fst))
        (pr_cExit.comp (pr_cComp.comp fst)))))) (pr_cOut.comp fst)))) (const [])) (const []))
    (const [])).of_eq fun _ => rfl

theorem pr_csplit : Primrec₂ csplit :=
  (Primrec.ite (PR.list_mem.comp (pr_cExit.comp (pr_cComp.comp fst)) snd)
    (list_cons.comp (list_cons.comp (pair (pr_cPre.comp fst) (pair (pr_cInp.comp fst)
      (pair (pr_crestrIn.comp (pair fst (pair snd (pair (pr_cEntry.comp (pr_cComp.comp fst))
        (pr_cExit.comp (pr_cComp.comp fst)))))) (pr_cOut.comp fst)))) (const [])) (const []))
    (list_map (PR.list_filter (pr_cEdges.comp (pr_cComp.comp fst))
        (PrimrecPred.and (PR.list_mem.comp (fst.comp snd) (snd.comp fst))
          (PR.list_mem.comp (snd.comp (snd.comp snd)) (snd.comp fst)).not).decide.to₂)
      (list_cons.comp
        (pair (pr_cPre.comp (fst.comp fst)) (pair (pr_cInp.comp (fst.comp fst))
          (pair (pr_crestrIn.comp (pair (fst.comp fst) (pair (snd.comp fst)
            (pair (pr_cEntry.comp (pr_cComp.comp (fst.comp fst))) (fst.comp snd)))))
          ((list_getD []).comp (pr_cLabs.comp (pr_cComp.comp (fst.comp fst))) (fst.comp snd)))))
        (list_cons.comp
          (pair (fst.comp (snd.comp snd)) (pair
            ((list_getD []).comp (pr_cLabs.comp (pr_cComp.comp (fst.comp fst)))
              (snd.comp (snd.comp snd)))
            (pair (pr_crestrNotIn.comp (pair (fst.comp fst) (pair (snd.comp fst)
              (pair (snd.comp (snd.comp snd)) (pr_cExit.comp (pr_cComp.comp (fst.comp fst)))))))
            (pr_cOut.comp (fst.comp fst)))))
          (const []))).to₂)).of_eq fun _ => rfl

theorem pr_cminus : Primrec fun x : ℕ × CB × CE × ℕ × ℕ =>
    cminus x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
  (pair (PR.list_filter (pr_cNodes.comp (pr_cComp.comp (fst.comp snd))) (const true).to₂)
    (pair (pr_cLabs.comp (pr_cComp.comp (fst.comp snd)))
      (pair (PR.list_filter (pr_cEdges.comp (pr_cComp.comp (fst.comp snd)))
        (Primrec.not.comp (pr_ceqB.comp (pair (fst.comp fst) (pair snd
          (fst.comp (snd.comp (snd.comp fst))))))).to₂)
        (pair (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd))))))).of_eq
    fun _ => rfl

/-- The closed form of the chains. -/
theorem cchain_tail (d : ℕ) (b : CB) (ce : CE) : ∀ n,
    cchain d b ce ce.2.1 ((cLabs (cComp b)).getD ce.2.2 []) ce.2.2 n =
      List.replicate n (ce.2.1, (cLabs (cComp b)).getD ce.2.2 [], cminus d b ce ce.2.2 ce.1,
        (cLabs (cComp b)).getD ce.1 []) ++
      [(ce.2.1, (cLabs (cComp b)).getD ce.2.2 [], cminus d b ce ce.2.2 (cExit (cComp b)), cOut b)]
  | 0 => rfl
  | n + 1 => by rw [cchain, cchain_tail d b ce n]; rfl

theorem cchain_eq (d : ℕ) (b : CB) (ce : CE) (pre : CV) (inp : CW) (u : ℕ) (n : ℕ) :
    cchain d b ce pre inp u n = Nat.casesOn n [(pre, inp, cminus d b ce u (cExit (cComp b)), cOut b)]
      fun n => (pre, inp, cminus d b ce u ce.1, (cLabs (cComp b)).getD ce.1 []) ::
        (List.replicate n (ce.2.1, (cLabs (cComp b)).getD ce.2.2 [], cminus d b ce ce.2.2 ce.1,
          (cLabs (cComp b)).getD ce.1 []) ++
        [(ce.2.1, (cLabs (cComp b)).getD ce.2.2 [], cminus d b ce ce.2.2 (cExit (cComp b)),
          cOut b)]) := by
  cases n with
  | zero => rfl
  | succ n => rw [cchain, cchain_tail]

theorem pr_cedgeAlts : Primrec fun x : ℕ × CB × CE × ℕ => cedgeAlts x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  -- context `(x, k)`; `x = (d, b, ce, B)`
  have hd : Primrec fun p : (ℕ × CB × CE × ℕ) × ℕ => p.1.1 := fst.comp fst
  have hb : Primrec fun p : (ℕ × CB × CE × ℕ) × ℕ => p.1.2.1 := fst.comp (snd.comp fst)
  have hce : Primrec fun p : (ℕ × CB × CE × ℕ) × ℕ => p.1.2.2.1 :=
    fst.comp (snd.comp (snd.comp fst))
  have hlab : ∀ {u : (ℕ × CB × CE × ℕ) × ℕ → ℕ}, Primrec u →
      Primrec fun p => (cLabs (cComp p.1.2.1)).getD (u p) [] := fun hu =>
    (list_getD []).comp (pr_cLabs.comp (pr_cComp.comp hb)) hu
  have hmin : ∀ {u v : (ℕ × CB × CE × ℕ) × ℕ → ℕ}, Primrec u → Primrec v →
      Primrec fun p => cminus p.1.1 p.1.2.1 p.1.2.2.1 (u p) (v p) := fun hu hv =>
    pr_cminus.comp (pair hd (pair hb (pair hce (pair hu hv))))
  have hX : Primrec fun p : (ℕ × CB × CE × ℕ) × ℕ =>
      (p.1.2.2.1.2.1, (cLabs (cComp p.1.2.1)).getD p.1.2.2.1.2.2 [],
        cminus p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.1.2.2 p.1.2.2.1.1,
        (cLabs (cComp p.1.2.1)).getD p.1.2.2.1.1 []) :=
    pair (fst.comp (snd.comp hce)) (pair (hlab (snd.comp (snd.comp hce)))
      (pair (hmin (snd.comp (snd.comp hce)) (fst.comp hce)) (hlab (fst.comp hce))))
  have hY : Primrec fun p : (ℕ × CB × CE × ℕ) × ℕ =>
      (p.1.2.2.1.2.1, (cLabs (cComp p.1.2.1)).getD p.1.2.2.1.2.2 [],
        cminus p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.1.2.2 (cExit (cComp p.1.2.1)), cOut p.1.2.1) :=
    pair (fst.comp (snd.comp hce)) (pair (hlab (snd.comp (snd.comp hce)))
      (pair (hmin (snd.comp (snd.comp hce)) (pr_cExit.comp (pr_cComp.comp hb))) (pr_cOut.comp hb)))
  have hF : Primrec fun p : (ℕ × CB × CE × ℕ) × ℕ =>
      (cPre p.1.2.1, cInp p.1.2.1, cminus p.1.1 p.1.2.1 p.1.2.2.1 (cEntry (cComp p.1.2.1)) p.1.2.2.1.1,
        (cLabs (cComp p.1.2.1)).getD p.1.2.2.1.1 []) :=
    pair (pr_cPre.comp hb) (pair (pr_cInp.comp hb)
      (pair (hmin (pr_cEntry.comp (pr_cComp.comp hb)) (fst.comp hce)) (hlab (fst.comp hce))))
  have hk : Primrec fun p : (ℕ × CB × CE × ℕ) × ℕ =>
      cchain p.1.1 p.1.2.1 p.1.2.2.1 (cPre p.1.2.1) (cInp p.1.2.1) (cEntry (cComp p.1.2.1)) p.2 :=
    (nat_casesOn snd
      (list_cons.comp (pair (pr_cPre.comp hb) (pair (pr_cInp.comp hb)
        (pair (hmin (pr_cEntry.comp (pr_cComp.comp hb)) (pr_cExit.comp (pr_cComp.comp hb)))
          (pr_cOut.comp hb)))) (const []))
      (list_cons.comp (hF.comp fst)
        (list_append.comp (PR.list_replicate.comp snd (hX.comp fst))
          (list_cons.comp (hY.comp fst) (const [])))).to₂).of_eq fun p => (cchain_eq _ _ _ _ _ _ _).symm
  exact (list_map (list_range.comp (succ.comp (snd.comp (snd.comp snd)))) hk.to₂).of_eq fun _ => rfl

theorem pr_cupd : Primrec fun x : ℕ × CW × ℕ × ℕ => cupd x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (list_map (list_range.comp fst) (Primrec.ite (Primrec.eq.comp snd (fst.comp (snd.comp (snd.comp fst))))
    (option_some.comp (snd.comp (snd.comp (snd.comp fst))))
    ((list_getD none).comp (fst.comp (snd.comp fst)) snd)).to₂).of_eq fun _ => rfl

theorem pr_cinpAlts : Primrec fun x : ℕ × CB × ℕ × ℕ => cinpAlts x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (list_map (list_range.comp (succ.comp (snd.comp (snd.comp snd))))
    (list_cons.comp (pair (pr_cPre.comp (fst.comp (snd.comp fst)))
      (pair (pr_cupd.comp (pair (fst.comp fst) (pair (pr_cInp.comp (fst.comp (snd.comp fst)))
        (pair (fst.comp (snd.comp (snd.comp fst))) snd))))
      (pair (pr_cComp.comp (fst.comp (snd.comp fst))) (pr_cOut.comp (fst.comp (snd.comp fst))))))
      (const [])).to₂).of_eq fun _ => rfl

theorem pr_coutAlts : Primrec fun x : ℕ × CB × ℕ × ℕ => coutAlts x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (list_map (list_range.comp (succ.comp (snd.comp (snd.comp snd))))
    (list_cons.comp (pair (pr_cPre.comp (fst.comp (snd.comp fst)))
      (pair (pr_cInp.comp (fst.comp (snd.comp fst)))
      (pair (pr_cComp.comp (fst.comp (snd.comp fst)))
        (pr_cupd.comp (pair (fst.comp fst) (pair (pr_cOut.comp (fst.comp (snd.comp fst)))
          (pair (fst.comp (snd.comp (snd.comp fst))) snd)))))))
      (const [])).to₂).of_eq fun _ => rfl

end KLM

end Petri

end HTN
