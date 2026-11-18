import ComplexityTheory.Petri.CharDec
import ComplexityTheory.Petri.PrimLib
/-!
# The bounded feasibility test is primitive recursive

`HTN.Petri.KLM.primrec_feasB`: the bounded-search test `feasB` for linear systems over `ℕ` (given
as lists of terms) is primitive recursive.
-/

namespace HTN

namespace Petri

namespace KLM

open Primrec

theorem primrec_tval : Primrec₂ fun (v : List ℕ) (ts : List (ℕ × ℤ)) =>
    tval ts (fun i => v.getD i 0) :=
  (PR.list_sumZ.comp (list_map snd (IntPR.mul.comp (snd.comp snd)
    (IntPR.natCast.comp ((list_getD 0).comp (fst.comp fst) (fst.comp snd)))).to₂)).of_eq
    fun _ => rfl

theorem primrec_eqHoldsB : Primrec₂ eqHoldsB :=
  (Primrec.eq.comp (primrec_tval.comp fst (fst.comp snd)) (snd.comp snd)).decide.of_eq
    fun _ => rfl

theorem primrec_tcoef : Primrec₂ tcoef :=
  (PR.list_sumZ.comp (list_map (PR.list_filter fst (Primrec.eq.comp (fst.comp snd)
    (snd.comp fst)).decide.to₂) (snd.comp snd).to₂)).of_eq fun _ => rfl

theorem primrec_tlen : Primrec tlen :=
  (PR.list_maxN.comp (list_map Primrec.id (succ.comp (fst.comp snd)).to₂)).of_eq fun _ => rfl

theorem primrec_dense : Primrec dense :=
  (Primrec.pair (list_map (list_range.comp (primrec_tlen.comp fst))
    (primrec_tcoef.comp (fst.comp fst) snd).to₂) snd).of_eq fun _ => rfl

theorem primrec_nVar : Primrec ILP.nVar :=
  (PR.list_maxN.comp (list_map Primrec.id (list_length.comp (fst.comp snd)).to₂)).of_eq fun _ => rfl

theorem primrec_natAbs : Primrec Int.natAbs :=
  (nat_add.comp IntPR.toNat IntPR.negToNat).of_eq fun z => by omega

theorem primrec_amax : Primrec ILP.amax :=
  (PR.list_sumN.comp (list_map Primrec.id (nat_add.comp (primrec_natAbs.comp (snd.comp snd))
    (PR.list_sumN.comp (list_map (fst.comp snd) (primrec_natAbs.comp snd).to₂))).to₂)).of_eq
    fun _ => rfl

theorem primrec_zsP : Primrec₂ Steinitz.zsP :=
  (PR.nat_pow.comp (succ.comp (nat_mul.comp (nat_mul.comp (const 2) fst) snd)) fst).of_eq
    fun _ => rfl

theorem primrec_solBnd : Primrec ILP.solBnd :=
  (primrec_zsP.comp list_length primrec_amax).of_eq fun _ => rfl

theorem boxes_eq (n B : ℕ) : boxes n B =
    Nat.rec [[]] (fun _ acc => acc.flatMap fun v => (List.range (B + 1)).map fun a => a :: v) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [boxes, ih]

theorem primrec_boxes : Primrec₂ boxes :=
  (nat_rec' fst (const [[]]) (list_flatMap (snd.comp snd)
    (list_map (list_range.comp (succ.comp (snd.comp (fst.comp fst))))
      (list_cons.comp snd (snd.comp fst)).to₂).to₂).to₂).of_eq fun p => (boxes_eq p.1 p.2).symm

theorem primrec_feasB : Primrec feasB :=
  (PR.list_any (primrec_boxes.comp (primrec_nVar.comp (list_map Primrec.id (primrec_dense.comp snd).to₂))
    (primrec_solBnd.comp (list_map Primrec.id (primrec_dense.comp snd).to₂)))
    (PR.list_all fst (primrec_eqHoldsB.comp (snd.comp fst) snd).to₂).to₂).of_eq fun _ => rfl

end KLM

end Petri

end HTN
