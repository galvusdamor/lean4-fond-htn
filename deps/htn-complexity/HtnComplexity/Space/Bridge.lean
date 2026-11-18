import ComplexityTheory.Space.Model
import HtnComplexity.Hypotheses.Families
/-!
# The target side of the Karp–Lipton cells: from a polynomial-space planner to `NPSPACE/poly`

`TABLE3-PLAN.md` splits the eight open cells of Table 3 into four ingredients.  Ingredient 2 —
"a polynomial-size compilation turns a hardness family in the source into polynomial advice in
the target" — is `HTN.Syn.Coded.inPolyAdvice_of_compilation`.  This file supplies the *generic
half* of ingredient 3: the step from

    InPolyAdvice c T L      ("`T`-plan existence decides `L` with polynomial advice")

to the complexity-theoretic statement

    InNSpacePoly L          ("`L ∈ NPSPACE/poly`")

for a target class `T` whose plan-existence problem can be solved in nondeterministic polynomial
space **with the domain description supplied as advice**.  That last notion is

* `HTN.Syn.SpaceDecidableAdv c T` — for every polynomially bounded family `D` of `T`-domain
  descriptions, and every polynomial `rq`, there are a machine of
  `ComplexityTheory/Space/Model.lean` and a polynomially long advice family `A` such that, for
  every `T`-instance description `q` **whose code has length at most `rq n`**, the machine
  accepts the code of `q` with advice `A n` exactly when `(D n, q)` is solvable.

Three remarks on the shape of the definition, all deliberate.

* The restriction to instances with a **short code** is not a convenience, it is forced.  The
  size measure of the compilability table, `HTN.Syn.DomDesc.size`, counts *symbols*, and a
  description of few symbols may mention numerals of astronomical magnitude, whose code is
  correspondingly long.  A domain family of polynomial symbol size can therefore not always be
  written into polynomially many advice bits, and whether a huge fact of the domain is the same
  as a huge fact of the instance is information no short advice can carry: without the
  restriction the statement would be **false**.  With it, the domain's oversized numerals are
  facts no admissible instance can mention, and the advice may carry the domain with them
  renamed away.  The bridge below supplies the restriction from the polynomial-time instance
  translation, whose outputs have codes of polynomial length — so nothing is lost for the cells.

* The domain is **advice, not input**.  This is what makes the notion usable without assuming
  that any domain translation runs in polynomial time: the advice string may be an arbitrary
  polynomially long function of the domain description — for instance a compiled `STRIPS`
  domain, however expensive to compute.  Only the *instance* is read in polynomial time.
* The machine is nondeterministic.  `NPSPACE = PSPACE` (Savitch) is not formalised here; the
  hypotheses below are therefore hypotheses about `NPSPACE/poly`, which is the class the
  literature writes `PSPACE/poly`.

## Results

* `HTN.Syn.inNSpacePoly_of_inPolyAdvice` — the bridge;
* `HTN.Syn.not_inPolyAdvice_of_not_inNSpacePoly` — its contrapositive, the form the cells use;
* `HTN.Syn.Coded.noAdvice_TO_HTN_of_spaceDecidableAdv` and the two cell theorems
  `HTN.Syn.cell_TO_HTN_to_HTN_REG_root_of_space`,
  `HTN.Syn.cell_TO_HTN_root_to_HTN_REG_root_of_space` — cell 2 of `TABLE3-PLAN.md` reduced to
  exactly two hypotheses: the target-side algorithm `SpaceDecidableAdv codingSer HTN-REG` and the
  complexity-theoretic separation `¬ InNSpacePoly (UniRecMem.L F)`, i.e. "the language of a
  uniform family of recursive alternating machines with a polynomial memory — an arbitrary
  language of alternating polynomial space — is not in `PSPACE/poly`".  In the notation of the
  literature the second hypothesis is `EXPTIME ⊄ PSPACE/poly`.
-/

namespace HTN

namespace Syn

open PTime Table Space

variable {ℰ : Family} {T : SynClass ℰ} {L : List Bool → Prop} {c : BitCoding InstDesc}

/-- **Plan existence for `T` is decidable in nondeterministic polynomial space, the domain
description being supplied as advice.**  The quantification over *families* of domains, rather
than over single domains, is what fixes the length of the advice against the length of the
input: the advice for the inputs of length `n` is computed from `D n`. -/
def SpaceDecidableAdv (c : BitCoding InstDesc) (T : SynClass ℰ) : Prop :=
  ∀ (D : ℕ → DomDesc) (r rq : Polynomial ℕ), (∀ n, T.domOk (D n)) →
    (∀ n, (D n).size ≤ r.eval n) →
    ∃ (M : NSpace) (A : ℕ → List Bool) (s : Polynomial ℕ),
      (∀ n, (A n).length ≤ s.eval n) ∧
        ∀ (n : ℕ) (q : InstDesc), T.instOk q → (c.code q).length ≤ rq.eval n →
          (Solvable (D n) q ↔ M.Accepts (c.code q) (A n))

/-- A polynomial-space planner for a class is one for every smaller class. -/
theorem SpaceDecidableAdv.mono {ℱ : Family} {T' : SynClass ℱ} (h : SpaceDecidableAdv c T)
    (hsub : SynSub T' T) : SpaceDecidableAdv c T' := by
  intro D r rq hdom hsize
  obtain ⟨M, A, s, hA, hM⟩ := h D r rq (fun n => hsub.dom _ (hdom n)) hsize
  exact ⟨M, A, s, hA, fun n q hq hlen => hM n q (hsub.inst _ hq) hlen⟩

/-- **The bridge**: a class whose plan-existence problem is solvable in nondeterministic
polynomial space with the domain as advice decides, with polynomial advice, only languages of
`NPSPACE/poly`. -/
theorem inNSpacePoly_of_inPolyAdvice (hT : SpaceDecidableAdv c T)
    (h : Coded.InPolyAdvice c T L) : InNSpacePoly L := by
  obtain ⟨E, D, r, hE, hDsize, -, hDok, hEok, hcorr⟩ := h
  obtain ⟨F, hF, hFE⟩ := hE
  obtain ⟨rq, hrq⟩ := hF.poly_length
  obtain ⟨M, A, s, hA, hM⟩ := hT D r rq hDok hDsize
  refine inNSpacePoly_of_precomp M (F := F) hF A s hA fun w => ?_
  have hlen : (c.code (E w)).length ≤ rq.eval w.length := by
    rw [← hFE w]; exact hrq w
  rw [hFE w, ← hM w.length (E w) (hEok w) hlen]
  exact (hcorr w).symm

/-- The form the cells use. -/
theorem not_inPolyAdvice_of_not_inNSpacePoly (hT : SpaceDecidableAdv c T)
    (hL : ¬ InNSpacePoly L) : ¬ Coded.InPolyAdvice c T L :=
  fun h => hL (inNSpacePoly_of_inPolyAdvice hT h)

end Syn

end HTN
