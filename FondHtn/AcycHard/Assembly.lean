import FondHtn.AcycHard.Chains
import FondHtn.AcycHard.Supply
/-!
# Assembly: from belief solvability of the decomposed network to the queue game

**`FOND.AcycHard.beliefSolvable_iff_qi`**: let the actions of a FOND HTN problem be the control
instructions and pool actions of a cell specification `X` (`δ = Sum.elim δC δP`), and let a
primitive task network `tn` be the disjoint union of

* the control chain `preW (tri S) · expandQ prog · refill^R`, and
* the pool chains: `S` blank cells `b` and a rich supply `U` of fresh cells and options.

Then `tn` is strongly solvable from the data state `d` (`BeliefSolvable`, i.e. strong OD) iff
the supply-free queue game `QI prog b^S d` is won.  What remains for the EXPSPACE lower bounds
(`doc/notes_acyc_expspace.md` §6): the hierarchy generating `tn` (L1c), the single-method
collapse for method-based policies (L1b), the program/automaton for the Savitch game (L3) and
the polynomial-time layer (L1d).
-/

namespace FOND

namespace AcycHard

open HTN

theorem beliefSolvable_iff_qi {Sym O D Pl C I : Type} [DecidableEq Sym] [DecidableEq O]
    [DecidableEq Pl] [DecidableEq I]
    (X : FSpec Sym O D Pl) (aS : Sym → Prop) (aO : O → Prop)
    (Pb : Problem (Tok Gate D) (CI Gate Pl ⊕ PA Sym O) C I)
    (hδ : Pb.δ = Sum.elim X.sys.δC X.sys.δP)
    (hne : ∀ p, (X.peffs p).Nonempty) {U : Multiset (List (PA Sym O))}
    (prog : List (Option Pl)) (hU : X.Rich aS aO U (FSpec.steps prog))
    (hst : X.S ≤ FSpec.steps prog) (b : Sym) (d : Set D) (R : ℕ)
    (hR : WSys.size (FSpec.liveR (Multiset.replicate X.S (b, X.S)) + U) ≤ R)
    {tn : TaskNetwork I (CI Gate Pl ⊕ PA Sym O) C} {ctl : List I} {pool : Multiset (List I)}
    {ℓ : I → CI Gate Pl ⊕ PA Sym O} (hch : IsChains tn ctl pool ℓ)
    (hctl : ctl.map ℓ = (WSys.expand (FSpec.preW (FSpec.tri X.S) ++ X.expandQ prog) ++
      List.replicate R (CI.refill : CI Gate Pl)).map Sum.inl)
    (hpool : pool.map (List.map ℓ) =
      (FSpec.liveR (Multiset.replicate X.S (b, X.S)) + U).map (List.map Sum.inr)) :
    Pb.BeliefSolvable tn (WSys.idle d) ↔ X.QI aS aO prog (List.replicate X.S b) d := by
  rw [beliefSolvable_iff_cwin Pb hch, hctl, hpool, hδ, cwin_sum_iff]
  exact X.cwin_iff_qi hne prog hU hst b d R hR

end AcycHard

end FOND
