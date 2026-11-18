import HtnComplexity.AcVerify.Verifier
/-!
# The verifier of path witnesses is a predicate of Cobham's class

`HTN.Syn.AcVer.cobhamB_acV`: the verifier `acV` of `HtnComplexity/AcVerify/Verifier.lean`
runs in polynomial time in the length of its arguments.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space

/-! ### Small closure properties -/

theorem cobham_consF {a : Fn} (ha : Cobham a) : Cobham fun args => false :: a args :=
  (cobham_consB (cobhamB_const false) ha).of_eq' fun _ => rfl

theorem cobhamB_eq {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => decide (a args = b args) := cobhamB_eqStr ha hb

theorem cobhamB_hasNext {a : Fn} (ha : Cobham a) : CobhamB fun args => hasNext (a args) :=
  cobhamB_head ha

theorem cobhamB_isLast {a : Fn} (ha : Cobham a) : CobhamB fun args => isLast (a args) :=
  ((cobhamB_null ha).not.and (cobhamB_head ha).not).of_eq fun args => by
    rcases a args with _ | ⟨b, l⟩ <;> simp [isLast]

theorem cobhamB_lblB' {K x s : Fn} (hK : Cobham K) (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => lblB (K args) (x args) (s args) :=
  cobhamB_firstLabelS hK (cobham_yE hx) (cobham_nvAt hs)

theorem cobham_p3Of {c : Fn} (hc : Cobham c) : Cobham fun args => p3Of (c args) := by
  have hst := cobham_dropBL hc
  have hpr := cobham_dropBL hst
  have hf := cobham_dropBL (cobham_dropBL (cobham_dropBL hpr))
  exact (cobham_cut hpr hf).of_eq' fun _ => rfl

theorem cobham_stOf {c : Fn} (hc : Cobham c) : Cobham fun args => stOf (c args) := cobham_dropBL hc
theorem cobham_prOf {c : Fn} (hc : Cobham c) : Cobham fun args => prOf (c args) :=
  cobham_dropBL (cobham_stOf hc)
theorem cobham_adOf {c : Fn} (hc : Cobham c) : Cobham fun args => adOf (c args) :=
  cobham_dropBL (cobham_prOf hc)
theorem cobham_deOf {c : Fn} (hc : Cobham c) : Cobham fun args => deOf (c args) :=
  cobham_dropBL (cobham_adOf hc)
theorem cobham_fOf {c : Fn} (hc : Cobham c) : Cobham fun args => fOf (c args) :=
  cobham_dropBL (cobham_deOf hc)
theorem cobhamB_flagOf {c : Fn} (hc : Cobham c) : CobhamB fun args => flagOf (c args) :=
  cobhamB_head (cobham_fOf hc)
theorem cobham_tD {a : Fn} (ha : Cobham a) : Cobham fun args => tD (a args) := cobham_dropBL ha
theorem cobham_tH {a : Fn} (ha : Cobham a) : Cobham fun args => tH (a args) :=
  cobham_dropBL (cobham_tD ha)
theorem cobham_tO {a : Fn} (ha : Cobham a) : Cobham fun args => tO (a args) :=
  cobham_dropBL (cobham_tH ha)
theorem cobham_tA {a : Fn} (ha : Cobham a) : Cobham fun args => tA (a args) :=
  cobham_dropBL (cobham_tO ha)

theorem cobhamB_parseB {c : Fn} (hc : Cobham c) : CobhamB fun args => parseB (c args) :=
  (((((cobhamB_blOK hc).and (cobhamB_blOK (cobham_stOf hc))).and
    (cobhamB_blOK (cobham_prOf hc))).and (cobhamB_blOK (cobham_adOf hc))).and
    (cobhamB_blOK (cobham_deOf hc))).and
    ((cobhamB_null (cobham_fOf hc)).not.and (cobhamB_null (cobham_tl (cobham_fOf hc))) |>.of_eq
      fun args => by rcases fOf (c args) with _ | ⟨b, _ | ⟨b', l⟩⟩ <;> simp) |>.of_eq fun _ => rfl

/-! ### The tests -/

theorem cobhamB_rootRecB {x R : Fn} (hx : Cobham x) (hR : Cobham R) :
    CobhamB fun args => rootRecB (x args) (R args) := by
  unfold rootRecB
  refine cobhamB_anyTailsF (P := fun args s => idPos (x args) s &&
    decide (R args = true :: (key 0 ++ (dbl (nvAt s) ++ (kat 2 (R args) ++
      (kat 3 (R args) ++ [false]))))) &&
    isBDs (kat 3 (R args)) &&
    ((decide (kat 2 (R args) = key 0) &&
        (lblB (false :: undbl (kat 3 (R args))) (x args) s ||
          (decide (kat 3 (R args) = key 0) && !lblB [] (x args) s))) ||
      (decide (kat 2 (R args) = key 1) && lblB (true :: undbl (kat 3 (R args))) (x args) s)))
    ?_ hx
  have hx' := cobham_tailArgs hx
  have hR' := cobham_tailArgs hR
  have hs := cobham_var0
  have k2 := cobham_kat 2 hR'
  have k3 := cobham_kat 3 hR'
  refine (((cobhamB_idPos hx' hs).and (cobhamB_eq hR' (cobham_consT (cobham_app
    (cobham_const _) (cobham_app (cobham_dbl (cobham_nvAt hs)) (cobham_app k2
      (cobham_app k3 (cobham_const _)))))))).and (cobhamB_isBDs k3)).and ?_
  refine ((cobhamB_eq k2 (cobham_const _)).and ((cobhamB_lblB' (cobham_consF (cobham_undbl k3))
    hx' hs).or ((cobhamB_eq k3 (cobham_const _)).and
      (cobhamB_lblB' (cobham_const []) hx' hs).not))).or
    ((cobhamB_eq k2 (cobham_const _)).and (cobhamB_lblB' (cobham_consT (cobham_undbl k3)) hx' hs))

theorem cobhamB_linkB {a Rx Ry : Fn} (ha : Cobham a) (hx : Cobham Rx) (hy : Cobham Ry) :
    CobhamB fun args => linkB (a args) (Rx args) (Ry args) :=
  (cobhamB_eq (cobham_kat 2 hx) (cobham_const _)).and (cobhamB_occB (cobham_tH ha)
    (cobham_consT (cobham_app (cobham_kat 0 hy) (cobham_app (cobham_kat 3 hx)
      (cobham_const _)))))

theorem cobhamB_lastB {a c p R : Fn} (ha : Cobham a) (hc : Cobham c) (hp : Cobham p)
    (hR : Cobham R) : CobhamB fun args => lastB (a args) (c args) (p args) (R args) :=
  ((cobhamB_flagOf hc).or (cobhamB_eq (cobham_kat 2 hR) (cobham_const _))).and
    ((cobhamB_flagOf hc).not.or ((cobhamB_null hp).not.and (cobhamB_occB (cobham_tD ha) hR)))

theorem cobhamB_recsB {x a c : Fn} (hx : Cobham x) (ha : Cobham a) (hc : Cobham c) :
    CobhamB fun args => recsB (x args) (a args) (c args) := by
  unfold recsB
  refine ((cobhamB_head hc).and (cobhamB_rootRecB hx (cobham_nextEnt hc))).and ?_
  refine cobhamB_entAll (P := fun args pre R rest =>
      (decide (pre = []) || occB (a args) R || (isLast rest && flagOf (c args) &&
        occB (tD (a args)) R)) &&
        (!hasNext rest || linkB (a args) R (nextEnt rest)) &&
        (!isLast rest || lastB (a args) (c args) pre R)) ?_ hc
  have ha' := cobham_dropArgs ha 3
  have hc' := cobham_dropArgs hc 3
  have h0 : Cobham fun z : Args => z.getD 0 [] := Cobham.proj 0
  have h1 : Cobham fun z : Args => z.getD 1 [] := Cobham.proj 1
  have h2 : Cobham fun z : Args => z.getD 2 [] := Cobham.proj 2
  exact ((((cobhamB_null h0).or (cobhamB_occB ha' h1)).or
    (((cobhamB_isLast h2).and (cobhamB_flagOf hc')).and (cobhamB_occB (cobham_tD ha') h1))).and
    ((cobhamB_hasNext h2).not.or (cobhamB_linkB ha' h1 (cobham_nextEnt h2)))).and
    ((cobhamB_isLast h2).not.or (cobhamB_lastB ha' hc' h0 h1))

theorem cobhamB_childB {a w c : Fn} (ha : Cobham a) (hw : Cobham w) (hc : Cobham c) :
    CobhamB fun args => childB (a args) (w args) (c args) := by
  unfold childB
  refine cobhamB_entAll (P := fun args pre R _ => decide (pre = []) ||
    entAll (a args) fun _ M _ => !decide (kat 0 M = kat 0 R) ||
      occB (w args) (true :: dbl (pre ++ (true :: (kat 0 M ++ kat 1 M))))) ?_ hc
  have ha' := cobham_dropArgs ha 3
  have hw' := cobham_dropArgs hw 3
  refine (cobhamB_null (Cobham.proj 0)).or ?_
  refine cobhamB_entAll (P := fun z _ M _ => !decide (kat 0 M = kat 0 (z.getD 1 [])) ||
      occB (w (z.drop 3)) (true :: dbl (z.getD 0 [] ++ (true :: (kat 0 M ++ kat 1 M))))) ?_ ha'
  have hw'' := cobham_dropArgs hw' 3
  have hR := cobham_dropArgs (Cobham.proj 1) 3
  have hpre := cobham_dropArgs (Cobham.proj 0) 3
  have hM : Cobham fun z : Args => z.getD 1 [] := Cobham.proj 1
  refine ((cobhamB_eq (cobham_kat 0 hM) (cobham_kat 0 hR)).not.or
    (cobhamB_occB hw'' (cobham_consT (cobham_dbl (cobham_app hpre (cobham_consT
      (cobham_app (cobham_kat 0 hM) (cobham_kat 1 hM)))))))).of_eq fun z => ?_
  simp [proj, List.getD_eq_getElem?_getD, List.getElem?_drop, List.drop_drop]

theorem cobhamB_rootsB {x w : Fn} (hx : Cobham x) (hw : Cobham w) :
    CobhamB fun args => rootsB (x args) (w args) := by
  unfold rootsB
  refine cobhamB_allTailsF (P := fun args s => !idPos (x args) s ||
    occB (w args) (true :: dbl (true :: (key 0 ++ dbl (nvAt s))))) ?_ hx
  exact (cobhamB_idPos (cobham_tailArgs hx) cobham_var0).not.or
    (cobhamB_occB (cobham_tailArgs hw) (cobham_consT (cobham_dbl (cobham_consT
      (cobham_app (cobham_const _) (cobham_dbl (cobham_nvAt cobham_var0)))))))

theorem cobhamB_ordB {x a k j j' : Fn} (hx : Cobham x) (ha : Cobham a) (hk : Cobham k)
    (hj : Cobham j) (hj' : Cobham j') :
    CobhamB fun args => ordB (x args) (a args) (k args) (j args) (j' args) :=
  ((cobhamB_eq hk (cobham_const _)).and ((cobhamB_preOrdB hj hj' hx).and
    (cobhamB_preOrdB hj' hj hx).not)).or ((cobhamB_eq hk (cobham_const _)).not.and
    (cobhamB_occB (cobham_tO ha) (cobham_consT (cobham_app hk (cobham_app hj
      (cobham_app hj' (cobham_const _)))))))

theorem cobhamB_pairB {x a u v : Fn} (hx : Cobham x) (ha : Cobham a) (hu : Cobham u)
    (hv : Cobham v) : CobhamB fun args => pairB (x args) (a args) (u args) (v args) := by
  unfold pairB
  refine cobhamB_entAny (P := fun args pre R _ =>
    decide (pre <+: v args) && hasNext ((v args).drop pre.length) &&
      decide (kat 0 R = kat 0 (nextEnt ((v args).drop pre.length))) &&
      !decide (kat 1 R = kat 1 (nextEnt ((v args).drop pre.length))) &&
      (flagOf (u args) || flagOf (v args) ||
        !ordB (x args) (a args) (kat 0 R) (kat 1 (nextEnt ((v args).drop pre.length)))
          (kat 1 R))) ?_ hu
  have hx' := cobham_dropArgs hx 3
  have ha' := cobham_dropArgs ha 3
  have hu' := cobham_dropArgs hu 3
  have hv' := cobham_dropArgs hv 3
  have h0 : Cobham fun z : Args => z.getD 0 [] := Cobham.proj 0
  have h1 : Cobham fun z : Args => z.getD 1 [] := Cobham.proj 1
  have ht := cobham_drop h0 hv'
  have hn := cobham_nextEnt ht
  exact ((((cobhamB_isPrefix h0 hv').and (cobhamB_hasNext ht)).and
    (cobhamB_eq (cobham_kat 0 h1) (cobham_kat 0 hn))).and
    (cobhamB_eq (cobham_kat 1 h1) (cobham_kat 1 hn)).not).and
    (((cobhamB_flagOf hu').or (cobhamB_flagOf hv')).or
      (cobhamB_ordB hx' ha' (cobham_kat 0 h1) (cobham_kat 1 hn) (cobham_kat 1 h1)).not)

theorem cobhamB_pairsB {x a w : Fn} (hx : Cobham x) (ha : Cobham a) (hw : Cobham w) :
    CobhamB fun args => pairsB (x args) (a args) (w args) := by
  unfold pairsB
  refine cobhamB_entAll (P := fun args _ E rest =>
    entAll rest fun _ E' _ => pairB (x args) (a args) (cont E) (cont E')) ?_ hw
  refine cobhamB_entAll (P := fun z _ E' _ => pairB (x (z.drop 3)) (a (z.drop 3))
    (cont (z.getD 1 [])) (cont E')) ?_ (Cobham.proj 2)
  refine (cobhamB_pairB (cobham_dropArgs (cobham_dropArgs hx 3) 3)
    (cobham_dropArgs (cobham_dropArgs ha 3) 3)
    (cobham_cont (cobham_dropArgs (Cobham.proj 1) 3))
    (cobham_cont (Cobham.proj 1))).of_eq fun z => ?_
  simp [proj]

theorem cobhamB_actB {a K P : Fn} (ha : Cobham a) (hK : Cobham K) (hP : Cobham P) :
    CobhamB fun args => actB (a args) (K args) (P args) := by
  unfold actB
  refine (cobhamB_occB (cobham_tA ha) (cobham_consT (cobham_app hK (cobham_app (cobham_dbl hP)
    (cobham_const _))))).or (CobhamB.and ?_ (cobhamB_eq hP (cobham_const _)))
  refine (cobhamB_entAny (P := fun args _ E _ => decide (kat 0 E = K args)) ?_
    (cobham_tA ha)).not
  exact cobhamB_eq (cobham_kat 0 (Cobham.proj 1)) (cobham_dropArgs hK 3)

theorem cobhamB_rowB {a c : Fn} (ha : Cobham a) (hc : Cobham c) :
    CobhamB fun args => rowB (a args) (c args) := by
  unfold rowB
  refine ((cobhamB_flagOf hc).and (cobhamB_eq (cobham_p3Of hc) (cobham_const _))).or
    ((cobhamB_flagOf hc).not.and ?_)
  refine cobhamB_entAll (P := fun args _ R rest => !isLast rest ||
    actB (a args) (kat 3 R) (p3Of (c args))) ?_ hc
  exact (cobhamB_isLast (Cobham.proj 2)).not.or (cobhamB_actB (cobham_dropArgs ha 3)
    (cobham_kat 3 (Cobham.proj 1)) (cobham_p3Of (cobham_dropArgs hc 3)))

theorem cobhamB_transB {a S c : Fn} (ha : Cobham a) (hS : Cobham S) (hc : Cobham c) :
    CobhamB fun args => transB (a args) (S args) (c args) :=
  ((((cobhamB_subEntB (cobham_prOf hc) hS).and
    (cobhamB_subEntB (cobham_adOf hc) (cobham_stOf hc))).and
    (cobhamB_keepB hS (cobham_deOf hc) (cobham_stOf hc))).and
    (cobhamB_postB (cobham_stOf hc) (cobham_adOf hc) hS (cobham_deOf hc))).and
    (cobhamB_rowB ha hc)

theorem cobhamB_execB {x a w : Fn} (hx : Cobham x) (ha : Cobham a) (hw : Cobham w) :
    CobhamB fun args => execB (x args) (a args) (w args) := by
  unfold execB
  refine (((cobhamB_hasNext hw).not.or (cobhamB_transB ha hx (cobham_cont (cobham_nextEnt hw)))).and
    ((cobhamB_hasNext hw).or (cobhamB_subEntB (cobham_yB hx) hx))).and ?_
  refine cobhamB_entAll (P := fun args _ E rest =>
    (!hasNext rest || transB (a args) (stOf (cont E)) (cont (nextEnt rest))) &&
      (!isLast rest || subEntB (yB (x args)) (stOf (cont E)))) ?_ hw
  have hx' := cobham_dropArgs hx 3
  have ha' := cobham_dropArgs ha 3
  have hE : Cobham fun z : Args => z.getD 1 [] := Cobham.proj 1
  have hr : Cobham fun z : Args => z.getD 2 [] := Cobham.proj 2
  exact ((cobhamB_hasNext hr).not.or (cobhamB_transB ha' (cobham_stOf (cobham_cont hE))
    (cobham_cont (cobham_nextEnt hr)))).and ((cobhamB_isLast hr).not.or
      (cobhamB_subEntB (cobham_yB hx') (cobham_stOf (cobham_cont hE))))

/-- **The verifier is a predicate of Cobham's class.** -/
theorem cobhamB_acV : CobhamB acV := by
  have hx : Cobham fun args : Args => args.getD 0 [] := Cobham.proj 0
  have ha : Cobham fun args : Args => args.getD 1 [] := Cobham.proj 1
  have hw : Cobham fun args : Args => args.getD 2 [] := Cobham.proj 2
  unfold acV
  refine ((((cobhamB_blistB hw).and ?_).and (cobhamB_rootsB hx hw)).and
    (cobhamB_pairsB hx ha hw)).and (cobhamB_execB hx ha hw)
  refine cobhamB_entAll (P := fun args _ E _ => parseB (cont E) &&
      recsB (args.getD 0 []) (args.getD 1 []) (cont E) &&
      childB (args.getD 1 []) (args.getD 2 []) (cont E)) ?_ hw
  have hE := cobham_cont (Cobham.proj 1)
  have hx' := cobham_dropArgs hx 3
  have ha' := cobham_dropArgs ha 3
  have hw' := cobham_dropArgs hw 3
  exact ((cobhamB_parseB hE).and (cobhamB_recsB hx' ha' hE)).and (cobhamB_childB ha' hw' hE)

end AcVer

end Syn

end HTN
