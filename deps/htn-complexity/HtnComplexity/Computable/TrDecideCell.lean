import HtnComplexity.Computable.TrInv
import HtnComplexity.Computable.RegDecideCell
/-!
# Plan existence is decidable for `HTN-TR`, primitive recursively

`HtnComplexity/Computable/RegDecide.lean` runs the progression search of
`HtnComplexity/Computable/PoSearch.lean` for as many rounds as there are normal forms of
configurations with at most `B` open tasks, and proves it complete for **every** bound `B` the
reachable configurations obey (`HTN.Syn.solvableB_iff`).  For a *tail-recursive* description
`HtnComplexity/Computable/TrInv.lean` supplies such a bound, so all that is left here is
to instantiate the generic machinery and to check that the bound is primitive recursive:

    HTN.Syn.trSolvableB d q = HTN.Syn.solvableB d q (HTN.Syn.trBnd d q)
    HTN.Syn.trSolvableB_iff : d.IsTailRec → (trSolvableB d q = true ↔ Solvable d q)
    HTN.Syn.decider_HTN_TR : HTN.Syn.SynClass.HTN_TR.Decider

and the two cells of the row `HTN` for the column `HTN-TR`.  The initial task network may be
partially ordered and the hierarchy may be recursive; only the tail-recursion of the hierarchy
is used.
-/

namespace HTN

namespace Syn

open Primrec

/-! ### The decision procedure -/

/-- **The decision procedure for tail-recursive domain descriptions.** -/
def trSolvableB (d : DomDesc) (q : InstDesc) : Bool := solvableB d q (trBnd d q)

/-- **The decision procedure is correct.** -/
theorem trSolvableB_iff {d : DomDesc} {q : InstDesc} (hd : d.IsTailRec) :
    trSolvableB d q = true ↔ Solvable d q := by
  refine solvableB_iff (P := TrInv d q) (fun h => h.toCfgInv) (trInv_initConfig d q) ?_
  intro c c' hc hstep
  exact hc.step hd hstep

/-! ### It is primitive recursive -/

theorem primrec_trK : Primrec fun w : DomDesc × InstDesc => trK w.1 w.2 :=
  Primrec.nat_max.comp (primrec_slotSize.comp Primrec.fst) (primrec_slotCount.comp Primrec.snd)

theorem primrec_trR : Primrec fun w : DomDesc × InstDesc => trR w.1 w.2 :=
  Primrec.succ.comp (Primrec.list_length.comp primrec_allLbls)

theorem primrec_trBnd : Primrec fun w : DomDesc × InstDesc => trBnd w.1 w.2 :=
  Primrec.nat_mul.comp (primrec_slotSize.comp Primrec.fst)
    (primrec_pow.comp (Primrec.nat_add.comp primrec_trK (Primrec.const 1)) primrec_trR)

set_option maxHeartbeats 2000000 in
theorem primrec_trSolvableB : Primrec₂ trSolvableB :=
  Primrec₂.mk ((primrec_solvableB.comp (Primrec.pair Primrec.id primrec_trBnd)).of_eq
    fun _ => rfl)

/-! ### The decider -/

/-- **Plan existence is decidable for the class `HTN-TR`** — for an arbitrary *partially
ordered* initial task network and for a hierarchy that may be recursive, as long as it is tail
recursive.  The decision procedure is the progression search of `Computable/PoSearch.lean`, run
for the number of rounds that `Computable/RegDecide.lean` proves sufficient once the number of
open tasks is bounded, and it is primitive recursive. -/
theorem decider_HTN_TR : SynClass.HTN_TR.Decider :=
  ⟨trSolvableB, primrec_trSolvableB.to_comp, fun _ _ hd _ => trSolvableB_iff hd⟩

end Syn

end HTN
