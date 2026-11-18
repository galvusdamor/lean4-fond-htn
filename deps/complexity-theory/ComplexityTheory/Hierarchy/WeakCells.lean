import ComplexityTheory.Hierarchy.Collapse
import ComplexityTheory.Hierarchy.Cells
/-!
# What the collapse theorem gives the cells of Table 3

`Cells.lean` states what cells 3–5 of Table 3 would gain from a Karp–Lipton collapse *at the
exponential scale*: their hypothesis "the target class does not decide the hard language with
polynomial advice" could be traded for the separation `EXPH ≠ Σ₂^EXP`.  The input it needed was

    kl : (∀ L, SigmaLevel s 1 L → InAdvice s L) → CollapseAt s 2,

the Karp–Lipton implication one exponential up.  `Collapse.lean` now proves the implication from
the *relational* advice hypothesis `HTN.Hier.DecisionAdviceP` — the advice answers the existential
question with the strings quantified so far as parameters.  This file records the one remaining
step between the two forms and assembles the cell-facing statements.

## The step that is left, and why it is stated rather than proved

`InAdvice s L` speaks of a *language*: one input, no parameters.  `DecisionAdviceP s R` speaks of
a *relation*: the parameters are the exponentially long strings already quantified.  Turning the
first into the second is the familiar "the parameters are part of the input" move, which at the
polynomial scale is carried out with a complete problem and polynomial-time reductions.  At the
exponential scale it is a statement about the scale, not about quantifier structure, so this
development names it — `HTN.Hier.AdviceParams` — rather than pretending to prove it.

## Main results

* `HTN.Hier.karpLipton_of_adviceParams` — **the Karp–Lipton implication of the weak exponential
  hierarchy**, in the shape `Cells.lean` asks for: with the closure properties of the scale and
  the parameterisation of the advice hypothesis, `NEXPTIME ⊆ EXPTIME/poly ⟹ EXPH = Σ₂^EXP`;
* `HTN.Hier.not_decisionAdviceP_of_not_collapseAt` — its contrapositive in relational form: if
  the hierarchy does not collapse to its second level, some base relation's existential question
  has no advice;
* `HTN.Hier.not_inAdvice_of_not_collapseAt` — the cell-facing form: if the hierarchy does not
  collapse to its second level, some `Σ₁` language of the scale has no advice.
-/

namespace HTN

namespace Hier

variable {s : Scale}

/-- **The parameterisation of the advice hypothesis**: advice for every `Σ₁` *language* of the
scale gives advice for the existential question attached to every base *relation*, the strings
quantified so far being parameters.

At the polynomial scale this is the standard step through a complete problem; at the exponential
scale it is a property of the scale, and this development carries it as a named hypothesis. -/
def AdviceParams (s : Scale) : Prop :=
  (∀ L, SigmaLevel s 1 L → InAdvice s L) → ∀ R, s.base R → DecisionAdviceP s R

/-- **The Karp–Lipton implication of the weak exponential hierarchy.**  With the closure
properties of the scale (`HTN.Hier.Closure`, `HTN.Hier.SearchClosure`) and the parameterisation
of the advice hypothesis, advice for every `Σ₁` language collapses the hierarchy to its second
level: `NEXPTIME ⊆ EXPTIME/poly ⟹ EXPH = Σ₂^EXP`.

This is the input `kl` that `HTN.Hier.not_adviceHyp_of_not_collapseAt` was missing. -/
theorem karpLipton_of_adviceParams (c : Closure s) (sr : SearchClosure s) (hp : AdviceParams s) :
    (∀ L, SigmaLevel s 1 L → InAdvice s L) → CollapseAt s 2 :=
  fun h => collapseAt_two_of_decisionAdvice c sr (hp h)

/-- **Non-collapse gives non-advice, in relational form.**  If the hierarchy of the scale does not
collapse to its second level, then the existential question of some base relation is not decided
with advice inside the base class.  Read at the weak exponential scale: `EXPH ≠ Σ₂^EXP` implies
`NEXPTIME ⊄ EXPTIME/poly`. -/
theorem not_decisionAdviceP_of_not_collapseAt (c : Closure s) (sr : SearchClosure s)
    (hsep : ¬ CollapseAt s 2) : ¬ ∀ R, s.base R → DecisionAdviceP s R :=
  fun hadv => hsep (collapseAt_two_of_decisionAdvice c sr hadv)

/-- **Non-collapse gives non-advice, in the form the cells use**: if the hierarchy of the scale
does not collapse to its second level, some `Σ₁` language of the scale is not decided by the base
class with admissible advice.  Read at the weak exponential scale: `EXPH ≠ Σ₂^EXP` implies
`NEXPTIME ⊄ EXPTIME/poly`, the advice budget being the one of the scale. -/
theorem not_inAdvice_of_not_collapseAt (c : Closure s) (sr : SearchClosure s)
    (hp : AdviceParams s) (hsep : ¬ CollapseAt s 2) :
    ¬ ∀ L, SigmaLevel s 1 L → InAdvice s L :=
  fun h => hsep (karpLipton_of_adviceParams c sr hp h)

/-- The same, for the smaller advice budget `A'` of the cells (`EXPTIME/poly` in place of
`EXPTIME/2^poly`): small advice is a special case of large advice, so the conclusion is at least
as strong. -/
theorem not_inAdvice_withAdvice_of_not_collapseAt (c : Closure s) (sr : SearchClosure s)
    (hp : AdviceParams s) {A' : ℕ → Word → Prop} {hA' : ∀ n, A' n []}
    (hle : ∀ n c, A' n c → s.A n c) (hsep : ¬ CollapseAt s 2) :
    ¬ ∀ L, SigmaLevel s 1 L → InAdvice (s.withAdvice A' hA') L :=
  not_adviceHyp_of_not_collapseAt hle (karpLipton_of_adviceParams c sr hp) hsep

end Hier

end HTN
