import HtnComplexity.Computable.RegDecide
import HtnComplexity.Computable.AcDecideCell
/-!
# The decision procedure for `HTN-REG` is primitive recursive

`HtnComplexity/Computable/RegDecide.lean` proves that `HTN.Syn.regSolvableB` decides plan
existence for a regular domain description.  This file proves that it is **primitive
recursive** — the number of rounds `HTN.Syn.cfgBound` is an arithmetic expression in the lengths of the
description, and the search itself is the primitive recursive `HTN.Syn.bfs` of
`HtnComplexity/Computable/AcDecideCell.lean` — and concludes

    HTN.Syn.decider_HTN_REG : HTN.Syn.SynClass.HTN_REG.Decider,

which discharges the decidability hypothesis of the cells (`HTN`, `HTN-REG`) of the
compilability table for the **unrestricted** class: an arbitrary partially ordered initial task
network, and a hierarchy that may well be cyclic.
-/

namespace HTN

namespace Syn

open Primrec

/-! ### The two vocabularies and the bound -/

theorem primrec_allFacts : Primrec fun w : DomDesc × InstDesc => allFacts w.1 w.2 := by
  have hinit : Primrec fun w : DomDesc × InstDesc => w.2.initList :=
    Primrec.fst.comp Primrec.snd
  have hacts : Primrec fun w : DomDesc × InstDesc => w.1.actions :=
    Primrec.fst.comp Primrec.fst
  have hfm : Primrec fun w : DomDesc × InstDesc =>
      w.1.actions.flatMap (fun e => e.2.2.1) := by
    refine Primrec.list_flatMap hacts (Primrec₂.mk ?_)
    exact (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.list_append.comp hinit hfm

theorem primrec_allLbls : Primrec fun w : DomDesc × InstDesc => allLbls w.1 w.2 := by
  have htn : Primrec fun w : DomDesc × InstDesc => w.2.tnI.lbl :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hmap : Primrec fun w : DomDesc × InstDesc => w.2.tnI.lbl.map (fun p => p.2) :=
    Primrec.list_map htn (Primrec₂.mk (Primrec.snd.comp Primrec.snd))
  have hmeth : Primrec fun w : DomDesc × InstDesc => w.1.methods :=
    Primrec.snd.comp Primrec.fst
  have hfm : Primrec fun w : DomDesc × InstDesc =>
      w.1.methods.flatMap (fun e => e.2.lbl.map (fun p => p.2)) := by
    refine Primrec.list_flatMap hmeth (Primrec₂.mk ?_)
    refine Primrec.list_map ?_ (Primrec₂.mk (Primrec.snd.comp Primrec.snd))
    exact Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_cons.comp (Primrec.const ((false, 0) : Bool × ℕ))
    (Primrec.list_append.comp hmap hfm)

theorem primrec_slotCount : Primrec slotCount :=
  Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

theorem primrec_slotSize : Primrec slotSize :=
  (Primrec.nat_max.comp primrec_maxBody (Primrec.const 1)).of_eq fun _ => rfl

theorem primrec_bnd : Primrec fun w : DomDesc × InstDesc => bnd w.1 w.2 :=
  Primrec.nat_mul.comp (primrec_slotSize.comp Primrec.fst) (primrec_slotCount.comp Primrec.snd)

/-- The number of search rounds is primitive recursive in the description and the bound. -/
theorem primrec_cfgBound :
    Primrec fun w : (DomDesc × InstDesc) × ℕ => cfgBound w.1.1 w.1.2 w.2 := by
  have hF : Primrec fun w : (DomDesc × InstDesc) × ℕ => (allFacts w.1.1 w.1.2).length :=
    Primrec.list_length.comp (primrec_allFacts.comp Primrec.fst)
  have hL : Primrec fun w : (DomDesc × InstDesc) × ℕ => (allLbls w.1.1 w.1.2).length :=
    Primrec.list_length.comp (primrec_allLbls.comp Primrec.fst)
  have hB : Primrec fun w : (DomDesc × InstDesc) × ℕ => w.2 := Primrec.snd
  have h2 : Primrec fun w : (DomDesc × InstDesc) × ℕ => 2 ^ (allFacts w.1.1 w.1.2).length :=
    primrec_pow.comp (Primrec.const 2) hF
  have hpow : Primrec fun w : (DomDesc × InstDesc) × ℕ => (w.2 + 1) ^ w.2 :=
    primrec_pow.comp (Primrec.nat_add.comp hB (Primrec.const 1)) hB
  have hbase : Primrec fun w : (DomDesc × InstDesc) × ℕ =>
      w.2 * ((allLbls w.1.1 w.1.2).length * (w.2 + 1) ^ w.2) + 1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hB (Primrec.nat_mul.comp hL hpow))
      (Primrec.const 1)
  exact (Primrec.nat_mul.comp h2 (primrec_pow.comp hbase hB)).of_eq fun _ => rfl

/-! ### The procedure -/

/-- The bounded search is primitive recursive in the description and the bound. -/
theorem primrec_solvableB :
    Primrec fun w : (DomDesc × InstDesc) × ℕ => solvableB w.1.1 w.1.2 w.2 := by
  have hinit : Primrec fun w : (DomDesc × InstDesc) × ℕ => initConfig w.1.2 :=
    primrec_initConfig.comp (Primrec.snd.comp Primrec.fst)
  have hbfs : Primrec fun w : (DomDesc × InstDesc) × ℕ =>
      bfs w.1.1 (initConfig w.1.2) (cfgBound w.1.1 w.1.2 w.2) :=
    primrec_bfs.comp (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst) hinit)
      primrec_cfgBound)
  have hgoal : Primrec₂ fun (w : (DomDesc × InstDesc) × ℕ) (c : PConfig) => isGoalB w.1.2 c :=
    Primrec₂.mk (primrec_isGoalB.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
  exact primrec_anyB hbfs hgoal

set_option maxHeartbeats 2000000 in
theorem primrec_regSolvableB : Primrec₂ regSolvableB :=
  Primrec₂.mk ((primrec_solvableB.comp (Primrec.pair Primrec.id primrec_bnd)).of_eq
    fun _ => rfl)

/-! ### The decider -/

/-- **Plan existence is decidable for the class `HTN-REG`** — for an arbitrary *partially
ordered* initial task network, and for a hierarchy that may be cyclic.  The decision procedure
is the progression search of `Computable/PoSearch.lean`, run for the number of rounds
`HTN.Syn.cfgBound` that `Computable/RegDecide.lean` proves sufficient, and it is primitive
recursive. -/
theorem decider_HTN_REG : SynClass.HTN_REG.Decider :=
  ⟨regSolvableB, primrec_regSolvableB.to_comp, fun _ _ hd _ => regSolvableB_iff hd⟩

end Syn

end HTN
