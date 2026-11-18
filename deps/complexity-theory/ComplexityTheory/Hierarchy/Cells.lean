import ComplexityTheory.Hierarchy.KarpLipton
/-!
# What a cell of the compilability table would gain from a Karp–Lipton collapse upstairs

Cells 3–5 of Table 3 carry a hypothesis of the form "the target class does **not** decide the
hard language with polynomial advice", for target classes whose advice inclusion is
`NEXPTIME ⊆ EXPTIME/poly`.  A collapse theorem at the exponential scale would replace it by a
*separation*, which is the form the literature prefers.  This file states that replacement, in
the abstract setting of `Scale.lean`, so that it is visible exactly what has to be supplied.

Two remarks the statement makes precise.

* The advice budget of the cells is **polynomial**, while the faithful lift of `P/poly` under
  padding is exponential advice (`Transfer.inAdvice_iff`).  That direction is harmless:
  `HTN.Hier.inAdvice_mono` turns the smaller budget into the larger one, so a collapse theorem
  stated for the faithful lift is enough for the cells.  `HTN.Hier.Scale.withAdvice` is the scale
  with the smaller advice budget and the same quantifier structure.
* What a collapse would give is `EXPH = Σ₂^EXP`, not `NEXPTIME = EXPTIME`: even classically,
  `NP ⊆ P/poly` is not known to imply `P = NP`.  So the hypothesis a cell would end up carrying is
  "the exponential hierarchy does not collapse to its second level", not "`NEXPTIME ≠ EXPTIME`".
  `HTN.Hier.not_adviceHyp_of_not_collapseAt` is that implication.

The input `kl` of the theorem below — the Karp–Lipton implication *at the exponential scale* — is
now available: `HTN.Hier.karpLipton_of_adviceParams` (`WeakCells.lean`) supplies it from the
collapse theorem of `Collapse.lean` and the parameterisation `HTN.Hier.AdviceParams`.  See §46 of
`NOTES.md`, which also corrects the earlier reading of §44.5.
-/

namespace HTN

namespace Hier

/-- The same scale with a smaller advice budget: same base class, same quantifier budget.  At the
exponential scale, `EXPTIME/poly` instead of `EXPTIME/2^poly`. -/
def Scale.withAdvice (s : Scale) (A' : ℕ → Word → Prop) (h : ∀ n, A' n []) : Scale :=
  { s with A := A', A_nil := h }

@[simp] theorem sigmaLevel_withAdvice (s : Scale) (A' : ℕ → Word → Prop) (h : ∀ n, A' n [])
    (k : ℕ) (L : Lang) : SigmaLevel (s.withAdvice A' h) k L ↔ SigmaLevel s k L :=
  sigmaLevel_congr_scale (s₁ := s.withAdvice A' h) (s₂ := s) (fun _ => Iff.rfl)
    (fun _ _ => Iff.rfl) k L

/-- **The form a cell of the table would take.**  If the hierarchy of the scale does not collapse
to level `2`, and the Karp–Lipton implication holds at that scale, then not every `Σ₁` language of
the scale has advice — in the *smaller* advice budget `A'` as well, since small advice is a
special case of large advice.

Read at the exponential scale: if the exponential hierarchy does not collapse to `Σ₂^EXP`, then
`NEXPTIME ⊄ EXPTIME/poly`, which is exactly the hypothesis cells 3–5 of Table 3 carry.  The
missing input is `kl`. -/
theorem not_adviceHyp_of_not_collapseAt {s : Scale} {A' : ℕ → Word → Prop} {h : ∀ n, A' n []}
    (hle : ∀ n c, A' n c → s.A n c)
    (kl : (∀ L, SigmaLevel s 1 L → InAdvice s L) → CollapseAt s 2)
    (hsep : ¬ CollapseAt s 2) :
    ¬ ∀ L, SigmaLevel s 1 L → InAdvice (s.withAdvice A' h) L := by
  intro hAdv
  refine hsep (kl fun L hL => ?_)
  exact inAdvice_mono (s := s.withAdvice A' h) (t := s) (fun _ hR => hR) hle (hAdv L hL)

end Hier

end HTN
