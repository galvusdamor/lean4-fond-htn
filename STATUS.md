# Status of the complexity results

Specification: `doc/results_catalogue.md` (all results of [CB21], [CB22], [DB25] and the ideas file,
with proof routes and the gaps found in the published proofs).  Deviations: `modifications/main.tex`.

Statements are about plan-existence languages over bit-encoded descriptions, as in `HtnComplexity`:
`FOND.PlanExFM c Y` (fixed methods, `c ∈ {weakLD, strongLD, weakOD, strongOD}`) and
`FOND.PlanExMP c Y` (method-based policies, `c ∈ {weak, strongCyclic, strong}`), `Y` a class
(`FOND.FClass`: `PRIM`, `ACYC`, `REG` (Bercher et al.), `REGtn` (CB21/Erol: with `tn_I`), `TR`,
`TO`, `TOtn`, `TOM`, `UNRES`).

Legend: ✅ formal · ⬜ to do · ⚠ published proof wrong/incomplete (catalogue §7) · ❓ open problem /
conjecture (proof idea only).

## Infrastructure

| item | status | Lean |
| --- | --- | --- |
| descriptions, validity in P, languages | ✅ | `FondHtn/Lang/Desc.lean` |
| deterministic problems collapse all criteria (except strong cyclic) | ✅ | `FondHtn/Transfer/Deterministic.lean` |
| goal elimination, `detDesc` (poly time, exact denotation) | ✅ | `FondHtn/Transfer/DetFond.lean`, `DetDesc.lean` |
| class preservation | ✅ | `FondHtn/Transfer/Classes.lean` |
| reductions `PlanEx Y ≤ₚ PlanExFM c Y'`, `≤ₚ PlanExMP c Y'` | ✅ | `FondHtn/Hardness/FromDet.lean` |
| closure of complexity classes under `≤ₚ` (for memberships via compilation) | ⬜ | — |
| weak compilation FOND → FOD [CB21 Lem 4.3] | ⬜ | — |
| strong LD compilation [CB21 Lem 4.6] | ⬜ | — |
| negative preconditions compiled away | ⬜ (needed only if a source uses positive-only actions) | — |

## Lower bounds

Inherited from deterministic HTN (✅ for all four FM criteria and for MP weak and strong; **not**
for MP strong cyclic, which does not collapse on recursive deterministic problems):

| class | bound | Lean |
| --- | --- | --- |
| PRIM | NP | `hard_PRIM_fm`, `hard_PRIM_mp` |
| REG ∩ ACYC ∩ TO | NP | `hard_REG_ACYC_TO_fm/_mp` |
| REG ∩ TO, TR ∩ TO, ACYC ∩ TO | PSPACE | `hard_REG_TO_*`, `hard_TR_TO_*`, `hard_ACYC_TO_*` |
| TO | EXPTIME | `hard_TO_*` |
| ACYC (∩ TOtn) | NEXPTIME | `hard_ACYC_*` |
| TR (∩ TOtn) | EXPSPACE | `hard_TR_*` |
| UNRES | undecidable | `undecidable_fm`, `undecidable_mp` |

FOND-specific lower bounds:

| result | status |
| --- | --- |
| CB21 Thm 4.1: PRIM ∩ TO weak NP-hard (SAT) | ⬜ |
| CB21 Thm 5.1: PRIM (PO) strong OD PSPACE-hard | ⚠ published reduction wrong (catalogue G9); re-prove from TQBF ⬜ |
| CB22 Thm 1: ACYC ∩ TO MP strong EXPTIME-hard | ⚠ incomplete (no acceptance check) ⬜ |
| CB22 Thm 2: ACYC MP strong EXPSPACE-hard | ⚠ sketch only ⬜ |
| CB22 Thm 3: REG MP strong EXPTIME-hard (from FOND planning) | ⬜ (needs FOND STRIPS EXPTIME-hardness) |
| CB22 Thm 4: TR ∩ TO MP strong EXPTIME-hard | ⬜ |
| CB22 Thm 5: TR MP strong 2-EXPTIME-hard | ⚠ sketch only; class 2-EXPTIME not yet defined ⬜ |
| DB25 Thm 1: chosen-length games EXPSPACE-complete | ⬜ (large; STRIPS gadgets unspecified) |
| DB25 Thm 4/5: REG FM strong OD EXPSPACE-hard | ⬜ |
| ideas: PCP, TR FM strong OD undecidable | ❓ |
| ideas: counters, ACYC EXPSPACE-hard / TR 2-EXPTIME-hard | ❓ |
| ideas: TO MP strong 2-EXPTIME-hard | ❓ |

## Upper bounds

| result | status |
| --- | --- |
| CB21 Cor 4.2 / CB22 Prop 2: PRIM weak ∈ NP | ⬜ |
| CB21 Thm 4.4 / Cor 4.5: weak ∈ FOD class (via Lem 4.3) | ⬜ |
| CB21 Thm 4.7: strong LD ∈ FOD class (via Lem 4.6) | ⬜ |
| CB21 Cor 4.8: TO strong OD | ⬜ (Prop 2.15 ✅ + Thm 4.7) |
| CB21 Thm 5.1: PRIM strong OD ∈ PSPACE | ⬜ |
| CB21 Thm 5.2 / 5.3: ACYC / REG strong OD ∈ EXPSPACE | ⬜ |
| CB21 Thm 3.1: semi-decidability | ⬜ |
| CB22 Thms 1–5: MP strong ∈ EXPTIME / EXPSPACE / 2-EXPTIME | ⬜ (alternating search; 2-EXPTIME not yet defined) |
| ideas: TO MP strong ∈ 2-EXPTIME | ❓ (rank argument missing) |
