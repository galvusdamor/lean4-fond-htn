import HtnComplexity.Undec.Correct
import HtnComplexity.Computable.GridPrimrec
import HtnComplexity.Computable.Decider
/-!
# Undecidability of HTN plan existence at a fixed domain description

The reduction of `HtnComplexity/Undec/Correct.lean` is *uniform in the instance*: the
domain description `tsmDom M` depends only on the machine, and the instance description
`tsmInst M s₁ s₂` — which is primitive recursive in the two initial stacks
(`HTN.Undec.primrec_tsmInst`) — carries the input.  Hence

> `HTN.Undec.not_deciderAt_tsmDom` — if the halting problem of the two-stack machine `M` is
> undecidable, then plan existence for the described HTN domain `tsmDom M` is undecidable, the
> initial state, the goal and the initial task network varying;

which is exactly the hypothesis `¬ HTN.Syn.SynClass.HTN.DeciderAt d₀` that every cell of the row
`HTN` of the computable compilability table rests on
(`HtnCompilability/Computable/Cells.lean`).

Two stacks over a finite control are Turing complete, so such a machine exists; that statement
is a fact of computability theory and is not proved here — it enters as the hypothesis `hM`.
-/

namespace HTN

namespace Undec

open Syn

/-! ### The instance map is primitive recursive -/

/-- The described instance, with the grid spelled out. -/
theorem tsmInst_eq (M : TSM) (s1 s2 : List ℕ) :
    tsmInst M s1 s2 =
      ([M.start], [M.acc], gridDesc [s1.map fun a => (true, tskName false a),
        s2.map fun a => (true, tskName true a)]) := by
  simp [tsmInst, gridDescOf, stackChain, encLabel, List.map_map, Function.comp_def]

theorem primrec_tskName (b : Bool) : Primrec (tskName b) :=
  Primrec₂.natPair.comp (Primrec.const _) Primrec.id

/-- **The instance map of the reduction is primitive recursive.** -/
theorem primrec_tsmInst (M : TSM) : Primrec fun p : List ℕ × List ℕ => tsmInst M p.1 p.2 := by
  have hrow : ∀ b : Bool, Primrec fun l : List ℕ => l.map fun a => ((true : Bool), tskName b a) :=
    fun b => Primrec.list_map Primrec.id
      ((Primrec.pair (Primrec.const true) ((primrec_tskName b).comp Primrec.snd)))
  have hrows : Primrec fun p : List ℕ × List ℕ =>
      [p.1.map fun a => ((true : Bool), tskName false a),
        p.2.map fun a => ((true : Bool), tskName true a)] :=
    Primrec.list_cons.comp ((hrow false).comp Primrec.fst)
      (Primrec.list_cons.comp ((hrow true).comp Primrec.snd) (Primrec.const []))
  have h := (Primrec.pair (Primrec.const [M.start])
    (Primrec.pair (Primrec.const [M.acc]) (Ac.primrec_gridDesc.comp hrows)))
  exact (h.of_eq fun p => (tsmInst_eq M p.1 p.2).symm)

/-! ### Undecidability -/

/-- **Plan existence for the fixed domain description `tsmDom M` is undecidable**, provided the
halting problem of the two-stack machine `M` is. -/
theorem not_deciderAt_tsmDom (M : TSM)
    (hM : ¬ ComputablePred fun p : List ℕ × List ℕ => M.Halts p.1 p.2) :
    ¬ SynClass.HTN.DeciderAt (tsmDom M) := by
  rintro ⟨g, hg, hcorr⟩
  refine hM ?_
  have hcomp : Computable fun p : List ℕ × List ℕ => g (tsmInst M p.1 p.2) :=
    hg.comp (primrec_tsmInst M).to_comp
  refine ComputablePred.computable_iff.2 ⟨_, hcomp, ?_⟩
  funext p
  have h1 : g (tsmInst M p.1 p.2) = true ↔ Solvable (tsmDom M) (tsmInst M p.1 p.2) :=
    hcorr _ trivial
  have h2 := solvable_tsm_iff M p.1 p.2
  simp only [eq_iff_iff]
  exact (h1.trans h2).symm

/-- **Plan existence for the class `HTN` of descriptions is undecidable**, provided some
two-stack machine has an undecidable halting problem. -/
theorem not_decider_HTN (M : TSM)
    (hM : ¬ ComputablePred fun p : List ℕ × List ℕ => M.Halts p.1 p.2) :
    ¬ SynClass.HTN.Decider :=
  SynClass.not_decider_of_not_deciderAt trivial (not_deciderAt_tsmDom M hM)

end Undec

end HTN
