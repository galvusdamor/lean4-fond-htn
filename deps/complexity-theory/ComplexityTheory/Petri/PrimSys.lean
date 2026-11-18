import ComplexityTheory.Petri.PrimFeas
/-!
# The characteristic system is primitive recursive

Primitive recursiveness of the accessors of concrete blocks and of `sysFrom` (via the closed form
`sysFrom_eq`), `totW`, `offs`, `edgeLin`, `bndEq`.
-/

namespace HTN

namespace Petri

namespace KLM

open Primrec

/-! ### Accessors -/

theorem pr_cPre : Primrec cPre := fst.of_eq fun _ => rfl
theorem pr_cInp : Primrec cInp := (fst.comp snd).of_eq fun _ => rfl
theorem pr_cComp : Primrec cComp := (fst.comp (snd.comp snd)).of_eq fun _ => rfl
theorem pr_cOut : Primrec cOut := (snd.comp (snd.comp snd)).of_eq fun _ => rfl
theorem pr_cNodes : Primrec cNodes := fst.of_eq fun _ => rfl
theorem pr_cLabs : Primrec cLabs := (fst.comp snd).of_eq fun _ => rfl
theorem pr_cEdges : Primrec cEdges := (fst.comp (snd.comp snd)).of_eq fun _ => rfl
theorem pr_cEntry : Primrec cEntry := (fst.comp (snd.comp (snd.comp snd))).of_eq fun _ => rfl
theorem pr_cExit : Primrec cExit := (snd.comp (snd.comp (snd.comp snd))).of_eq fun _ => rfl

theorem pr_nE : Primrec nE := (list_length.comp (pr_cEdges.comp pr_cComp)).of_eq fun _ => rfl

theorem pr_bw : Primrec₂ bw :=
  (nat_add.comp (nat_mul.comp (const 2) fst) (pr_nE.comp snd)).of_eq fun _ => rfl

theorem pr_cedge : Primrec₂ cedge :=
  ((list_getD (0, [], 0)).comp (pr_cEdges.comp (pr_cComp.comp fst)) snd).of_eq fun _ => rfl

/-! ### The equations of one block -/

theorem pr_inpEqs : Primrec fun x : ℕ × ℕ × CB => inpEqs x.1 x.2.1 x.2.2 :=
  (listFilterMap (list_range.comp fst)
    (option_map ((list_getD none).comp (pr_cInp.comp (snd.comp (snd.comp fst))) snd)
      (pair (list_cons.comp (pair (nat_add.comp (fst.comp (snd.comp (fst.comp fst))) (snd.comp fst))
        (const (1 : ℤ))) (const [])) (IntPR.natCast.comp snd)).to₂).to₂).of_eq fun _ => by
    simp only [inpEqs]; congr 1; funext j
    generalize List.getD _ j none = o; cases o <;> rfl

theorem pr_outEqs : Primrec fun x : ℕ × ℕ × CB => outEqs x.1 x.2.1 x.2.2 :=
  (listFilterMap (list_range.comp fst)
    (option_map ((list_getD none).comp (pr_cOut.comp (snd.comp (snd.comp fst))) snd)
      (pair (list_cons.comp (pair (nat_add.comp (nat_add.comp (fst.comp (snd.comp (fst.comp fst)))
          (fst.comp (fst.comp fst))) (snd.comp fst))
        (const (1 : ℤ))) (const [])) (IntPR.natCast.comp snd)).to₂).to₂).of_eq fun _ => by
    simp only [outEqs]; congr 1; funext j
    generalize List.getD _ j none = o; cases o <;> rfl

theorem pr_effEqs : Primrec fun x : ℕ × ℕ × CB => effEqs x.1 x.2.1 x.2.2 :=
  (list_map (list_range.comp fst)
    (pair (list_cons.comp
      (pair (nat_add.comp (nat_add.comp (fst.comp (snd.comp fst)) (fst.comp fst)) snd) (const (1 : ℤ)))
      (list_cons.comp (pair (nat_add.comp (fst.comp (snd.comp fst)) snd) (const (-1 : ℤ)))
        (list_map (list_range.comp (pr_nE.comp (snd.comp (snd.comp fst))))
          (pair (nat_add.comp (nat_add.comp (fst.comp (snd.comp (fst.comp fst)))
              (nat_mul.comp (const 2) (fst.comp (fst.comp fst)))) snd)
            (IntPR.neg.comp ((list_getD 0).comp
              (fst.comp (snd.comp (pr_cedge.comp (snd.comp (snd.comp (fst.comp fst))) snd)))
              (snd.comp fst)))).to₂)))
      (const (0 : ℤ))).to₂).of_eq fun _ => rfl

theorem pr_kirW : Primrec kirW :=
  (list_append.comp (list_append.comp
      (list_map (pr_cEdges.comp pr_cComp) (fst.comp snd).to₂)
      (list_map (pr_cEdges.comp pr_cComp) (snd.comp (snd.comp snd)).to₂))
    (list_cons.comp (pr_cEntry.comp pr_cComp)
      (list_cons.comp (pr_cExit.comp pr_cComp) (const [])))).of_eq fun _ => rfl

theorem pr_kv : Primrec fun x : CB × ℕ × ℕ => kv x.1 x.2.1 x.2.2 :=
  (IntPR.sub.comp
    (Primrec.ite (Primrec.eq.comp (fst.comp (pr_cedge.comp fst (snd.comp snd))) (fst.comp snd))
      (const (1 : ℤ)) (const 0))
    (Primrec.ite (Primrec.eq.comp (snd.comp (snd.comp (pr_cedge.comp fst (snd.comp snd))))
      (fst.comp snd)) (const (1 : ℤ)) (const 0))).of_eq fun _ => rfl

theorem pr_kirEqs : Primrec fun x : ℕ × ℕ × CB => kirEqs x.1 x.2.1 x.2.2 :=
  (list_map (pr_kirW.comp (snd.comp snd))
    (pair (list_map (list_range.comp (pr_nE.comp (snd.comp (snd.comp fst))))
        (pair (nat_add.comp (nat_add.comp (fst.comp (snd.comp (fst.comp fst)))
            (nat_mul.comp (const 2) (fst.comp (fst.comp fst)))) snd)
          (pr_kv.comp (pair (snd.comp (snd.comp (fst.comp fst))) (pair (snd.comp fst) snd)))).to₂)
      (IntPR.sub.comp
        (Primrec.ite (Primrec.eq.comp snd (pr_cEntry.comp (pr_cComp.comp (snd.comp (snd.comp fst)))))
          (const (1 : ℤ)) (const 0))
        (Primrec.ite (Primrec.eq.comp snd (pr_cExit.comp (pr_cComp.comp (snd.comp (snd.comp fst)))))
          (const (1 : ℤ)) (const 0)))).to₂).of_eq fun _ => rfl

theorem pr_blkEqs : Primrec fun x : ℕ × ℕ × CB => blkEqs x.1 x.2.1 x.2.2 :=
  (list_append.comp (list_append.comp (list_append.comp pr_inpEqs pr_outEqs) pr_effEqs)
    pr_kirEqs).of_eq fun _ => rfl

theorem pr_linkEqs : Primrec fun x : ℕ × ℕ × ℕ × CB => linkEqs x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (list_map (list_range.comp fst)
    (pair (list_cons.comp (pair (nat_add.comp (fst.comp (snd.comp (snd.comp fst))) snd)
          (const (1 : ℤ)))
        (list_cons.comp (pair (nat_add.comp (nat_add.comp (fst.comp (snd.comp fst)) (fst.comp fst))
          snd) (const (-1 : ℤ))) (const [])))
      ((list_getD 0).comp (pr_cPre.comp (snd.comp (snd.comp (snd.comp fst)))) snd)).to₂).of_eq
    fun _ => rfl

/-! ### The whole system -/

theorem totW_eq (d : ℕ) (bs : List CB) : totW (d := d) bs = (bs.map (bw d)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [totW, ih]

theorem pr_totW : Primrec₂ fun (d : ℕ) (bs : List CB) => totW (d := d) bs :=
  (PR.list_sumN.comp (list_map snd (pr_bw.comp (fst.comp fst) snd).to₂)).of_eq
    fun p => (totW_eq p.1 p.2).symm

theorem pr_offs : Primrec fun x : ℕ × List CB × ℕ => offs (d := x.1) x.2.1 x.2.2 :=
  (pr_totW.comp fst (PR.list_take.comp (fst.comp snd) (snd.comp snd))).of_eq fun _ => rfl

/-- The closed form of the characteristic system. -/
def sysCF (d o : ℕ) (bs : List CB) : List TEq :=
  (List.range bs.length).flatMap fun i =>
    blkEqs d (o + offs (d := d) bs i) (bs.getD i default) ++
      (if i + 1 < bs.length then
        linkEqs d (o + offs (d := d) bs i) (o + offs (d := d) bs (i + 1)) (bs.getD (i + 1) default)
      else [])

theorem offs_cons (d : ℕ) (b : CB) (bs : List CB) (i : ℕ) :
    offs (d := d) (b :: bs) (i + 1) = bw d b + offs (d := d) bs i := by
  simp [offs, totW]

theorem sysFrom_eq (d : ℕ) : ∀ (o : ℕ) (bs : List CB), sysFrom d o bs = sysCF d o bs
  | o, [] => rfl
  | o, [b] => by simp [sysFrom, sysCF, offs, totW]
  | o, b :: b' :: bs => by
    rw [sysFrom, sysFrom_eq d (o + bw d b) (b' :: bs)]
    unfold sysCF
    rw [List.length_cons (a := b), List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have h0 : offs (d := d) (b :: b' :: bs) 0 = 0 := rfl
    have h1 : offs (d := d) (b :: b' :: bs) 1 = bw d b := by simp [offs, totW]
    rw [h0, h1, if_pos (by simp), List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero,
      Nat.add_zero]
    simp only [List.append_assoc]
    congr 2
    refine List.flatMap_congr fun i _ => ?_
    simp only [offs_cons, List.getD_cons_succ, List.length_cons, add_assoc]
    congr 1
    split_ifs <;> first | rfl | omega

theorem pr_sysFrom : Primrec fun x : ℕ × ℕ × List CB => sysFrom x.1 x.2.1 x.2.2 :=
  (list_flatMap (list_range.comp (list_length.comp (snd.comp snd)))
    (list_append.comp
      (pr_blkEqs.comp (pair (fst.comp fst) (pair
        (nat_add.comp (fst.comp (snd.comp fst))
          (pr_offs.comp (pair (fst.comp fst) (pair (snd.comp (snd.comp fst)) snd))))
        ((list_getD default).comp (snd.comp (snd.comp fst)) snd))))
      (Primrec.ite (nat_lt.comp (succ.comp snd) (list_length.comp (snd.comp (snd.comp fst))))
        (pr_linkEqs.comp (pair (fst.comp fst) (pair
          (nat_add.comp (fst.comp (snd.comp fst))
            (pr_offs.comp (pair (fst.comp fst) (pair (snd.comp (snd.comp fst)) snd))))
          (pair (nat_add.comp (fst.comp (snd.comp fst))
            (pr_offs.comp (pair (fst.comp fst) (pair (snd.comp (snd.comp fst)) (succ.comp snd)))))
            ((list_getD default).comp (snd.comp (snd.comp fst)) (succ.comp snd))))))
        (const []))).to₂).of_eq fun x => (sysFrom_eq x.1 x.2.1 x.2.2).symm

/-! ### Bound tests -/

theorem pr_ceqB : Primrec fun x : ℕ × CE × CE => ceqB x.1 x.2.1 x.2.2 :=
  (Primrec.and.comp (Primrec.and.comp
      (Primrec.beq.comp (fst.comp (fst.comp snd)) (fst.comp (snd.comp snd)))
      (Primrec.beq.comp (snd.comp (snd.comp (fst.comp snd))) (snd.comp (snd.comp (snd.comp snd)))))
    (PR.list_all (list_range.comp fst)
      (Primrec.beq.comp ((list_getD 0).comp (fst.comp (snd.comp (fst.comp (snd.comp fst)))) snd)
        ((list_getD 0).comp (fst.comp (snd.comp (snd.comp (snd.comp fst)))) snd)).to₂)).of_eq
    fun _ => rfl

theorem pr_edgeLin : Primrec fun x : ℕ × List CB × ℕ × CE => edgeLin (d := x.1) x.2.1 x.2.2.1 x.2.2.2 :=
  (list_map (list_range.comp (pr_nE.comp ((list_getD default).comp (fst.comp snd) (fst.comp (snd.comp snd)))))
    (pair (nat_add.comp (nat_add.comp
        (pr_offs.comp (pair (fst.comp fst) (pair (fst.comp (snd.comp fst))
          (fst.comp (snd.comp (snd.comp fst))))))
        (nat_mul.comp (const 2) (fst.comp fst))) snd)
      (Primrec.ite (Primrec.eq.comp (pr_ceqB.comp (pair (fst.comp fst) (pair
          (pr_cedge.comp ((list_getD default).comp (fst.comp (snd.comp fst))
            (fst.comp (snd.comp (snd.comp fst)))) snd)
          (snd.comp (snd.comp (snd.comp fst)))))) (const true))
        (const (1 : ℤ)) (const 0))).to₂).of_eq fun _ => rfl

end KLM

end Petri

end HTN
