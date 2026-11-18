import ComplexityTheory.Hierarchy.Transfer
/-!
# The Karp–Lipton step at an arbitrary scale, and the one ingredient that does not scale

`Transfer.lean` shows that everything about the *shape* of the two hierarchies scales: levels,
advice classes and collapses all travel upwards under padding.  This file isolates what the
Karp–Lipton *proof* needs beyond that shape, and it is a single thing: from advice that answers
the existential question one must be able to **produce a witness**, because the swapped
quantifier prefix has to *check* the guessed advice, and the only check available is to exhibit a
witness and verify it.

The abstract step is `HTN.Hier.sigmaLevel_two_of_extractor`:

> if `L x ↔ ∀ y ∃ z. R x [y, z]` with `R` in the base class, and there is an advice family
> together with an extractor that turns the advice into a witness `z`, and the base class can
> run the extractor, then `L` is at level `2` of the *existential* side.

The proof is the Karp–Lipton quantifier swap and nothing else.  Soundness of the swap is free:
a guessed advice string is only believed when the witness it produces passes the test.

`HTN.Hier.sigmaLevel_two_of_decisionAdvice` states the same conclusion from the two hypotheses in
the form the literature uses: `HTN.Hier.DecisionAdvice` (the advice *decides* the existential
question — this is `NP ⊆ P/poly`, or `NEXPTIME ⊆ EXPTIME/poly`, at the relevant scale) and
`HTN.Hier.WitnessFromDecision` (search reduces to decision).

## Where the asymmetry is — and where it is not

At the polynomial scale `WitnessFromDecision` is the downward self-reducibility of `SAT`: the
witness has polynomially many bits, and each is obtained from one further query, of polynomial
length, to the same advised decision procedure.

One might expect this to fail one exponential up, on the grounds that a `NEXPTIME` witness has
exponentially many bits, so that the self-reduction would ask the advised machine about
exponentially long *inputs*, whose advice — the advice for length `2^{poly}` — the `Σ₂` prefix at
the exponential scale cannot guess.  **That is the shape of the strong exponential hierarchy, not
of the weak one** (`Strong.lean`), and the weak hierarchy is what this development uses.  In a
level of the weak hierarchy the quantified strings are arguments of one base-class predicate
measured against the original input `x`, so the self-reduction never changes `x`, never needs
advice for a new length, and makes `2^{poly}` queries to a `2^{poly}`-time predicate.

`Search.lean` and `Swap.lean` carry that out: the extractor is built there and its correctness is
proved (`HTN.Hier.greedy_sound`), so at a scale with the closure properties of
`HTN.Hier.SearchClosure` the hypothesis `HTN.Hier.WitnessFromDecision` of this file is no longer
needed — `HTN.Hier.SearchClosure.swapParams` performs the swap from the advice hypothesis alone,
and `Collapse.lean` turns it into the collapse of the whole hierarchy.  The definitions and the
single-language step of this file are kept because they state the argument in its most economical
form, with the extractor as an explicit input.
-/

namespace HTN

namespace Hier

variable {s : Scale}

/-- The relation the Karp–Lipton swap uses: on the pair `[c, y]` of a guessed advice string `c`
and a universally quantified string `y`, it says that the extractor applied to `c` produces an
admissible witness for `y`. -/
def extRel (s : Scale) (R : Rel) (ext : Word → Word → Word → Word) : Rel :=
  fun x ys => match ys with
    | [c, y] => s.Q x.length (ext c x y) ∧ R x [y, ext c x y]
    | _ => False

/-- **The Karp–Lipton step**, at an arbitrary scale.

`L` is given in `∀∃` form over a base relation `R`; `adv` is an advice family whose strings are
short enough to be guessed by an existential quantifier of the scale (`hAQ`); `ext` turns advice
into witnesses (`hext_sound`) and can be run inside the base class (`hext_base`).  Then `L` is at
the existential level `2`.

Both halves of the equivalence are in the proof below: completeness uses the correct advice, and
soundness uses only that a guessed advice string is believed only when the witness it yields is
verified. -/
theorem sigmaLevel_two_of_extractor {L : Lang} {R : Rel} {adv : ℕ → Word}
    {ext : Word → Word → Word → Word}
    (hL : ∀ x, L x ↔ ∀ y, s.Q x.length y → ∃ z, s.Q x.length z ∧ R x [y, z])
    (hadv : ∀ n, s.A n (adv n)) (hAQ : ∀ n c, s.A n c → s.Q n c)
    (hext_base : s.base (extRel s R ext))
    (hext_sound : ∀ x y, s.Q x.length y → (∃ z, s.Q x.length z ∧ R x [y, z]) →
      s.Q x.length (ext (adv x.length) x y) ∧ R x [y, ext (adv x.length) x y]) :
    SigmaLevel s 2 L := by
  refine (sigmaLevel_two s L).2 ⟨extRel s R ext, hext_base, fun x => ?_⟩
  constructor
  · intro hx
    refine ⟨adv x.length, hAQ _ _ (hadv _), fun y hy => ?_⟩
    exact hext_sound x y hy ((hL x).1 hx y hy)
  · rintro ⟨c, -, hc⟩
    refine (hL x).2 fun y hy => ?_
    obtain ⟨hQ, hR⟩ := hc y hy
    exact ⟨ext c x y, hQ, hR⟩

/-- **The advice hypothesis**, for the existential question attached to `R`: an advice family and
a base-class relation that, given the advice, decide whether a witness `z` exists.  At the
polynomial scale this is `NP ⊆ P/poly`; at the exponential scale, `NEXPTIME ⊆ EXPTIME/poly`
(or `/2^poly`, depending on the advice budget of the scale). -/
def DecisionAdvice (s : Scale) (R : Rel) : Prop :=
  ∃ a : ℕ → Word, (∀ n, s.A n (a n)) ∧ ∃ D : Rel, s.base D ∧
    ∀ x y, s.Q x.length y → ((∃ z, s.Q x.length z ∧ R x [y, z]) ↔ D x [a x.length, y])

/-- **Search reduces to decision, with advice**: from any advised decision procedure for the
existential question attached to `R` one can extract witnesses, inside the base class.

At the polynomial scale this is the downward self-reducibility of `SAT`.  At the exponential
scale it is precisely the ingredient that the padding of `Transfer.lean` does not carry upwards;
see the discussion at the head of this file. -/
def WitnessFromDecision (s : Scale) (R : Rel) : Prop :=
  ∀ (a : ℕ → Word) (D : Rel), s.base D →
    (∀ x y, s.Q x.length y → ((∃ z, s.Q x.length z ∧ R x [y, z]) ↔ D x [a x.length, y])) →
    ∃ ext : Word → Word → Word → Word, s.base (extRel s R ext) ∧
      ∀ x y, s.Q x.length y → (∃ z, s.Q x.length z ∧ R x [y, z]) →
        s.Q x.length (ext (a x.length) x y) ∧ R x [y, ext (a x.length) x y]

/-- **The Karp–Lipton step in the form the literature uses**: the advice hypothesis plus
search-to-decision collapse a `∀∃` language to the existential level `2`.  The scale is
arbitrary, so this is the polynomial argument and the exponential argument at once — the
difference between the two levels is entirely in the availability of `WitnessFromDecision`. -/
theorem sigmaLevel_two_of_decisionAdvice {L : Lang} {R : Rel}
    (hL : ∀ x, L x ↔ ∀ y, s.Q x.length y → ∃ z, s.Q x.length z ∧ R x [y, z])
    (hAQ : ∀ n c, s.A n c → s.Q n c)
    (hDA : DecisionAdvice s R) (hW : WitnessFromDecision s R) :
    SigmaLevel s 2 L := by
  obtain ⟨a, ha, D, hD, hDec⟩ := hDA
  obtain ⟨ext, hext_base, hext_sound⟩ := hW a D hD hDec
  exact sigmaLevel_two_of_extractor hL ha hAQ hext_base hext_sound

end Hier

end HTN
