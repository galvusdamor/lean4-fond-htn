import HtnComplexity.Computable.GridDesc
/-!
# Described grids are primitive recursive

Split out of `HTN.Computable.AcPrimrec`.
-/

namespace HTN

namespace Syn

namespace Ac

open Primrec

/-! ### The described grids -/

theorem primrec_gridRow : Primrec₂ gridRow := Primrec.list_getD _

theorem primrec_gridDesc : Primrec gridDesc := by
  have hrng : Primrec fun ls : List (List (Bool × ℕ)) => List.range ls.length :=
    Primrec.list_range.comp Primrec.list_length
  have hrow : Primrec fun y : List (List (Bool × ℕ)) × ℕ => gridRow y.1 y.2 :=
    primrec_gridRow.comp Primrec.fst Primrec.snd
  have hrowlen : Primrec fun y : List (List (Bool × ℕ)) × ℕ => (gridRow y.1 y.2).length :=
    Primrec.list_length.comp hrow
  have hids : Primrec cellIds := by
    refine Primrec.list_flatMap hrng ?_
    refine Primrec.list_map (Primrec.list_range.comp hrowlen) ?_
    exact Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hord : Primrec cellOrd := by
    refine Primrec.list_flatMap hrng ?_
    refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_sub.comp hrowlen (Primrec.const 1))) ?_
    exact Primrec.pair
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))
  have hlbl : Primrec cellLbl := by
    refine Primrec.list_flatMap hrng ?_
    refine Primrec.list_map (Primrec.list_range.comp hrowlen) ?_
    refine Primrec.pair
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) ?_
    exact (Primrec.list_getD ((false, 0) : Bool × ℕ)).comp
      (hrow.comp Primrec.fst) Primrec.snd
  exact Primrec.pair hids (Primrec.pair hord hlbl)

end Ac

end Syn

end HTN
