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
| closure of complexity classes under `≤ₚ` (P, NP, PSPACE, EXPTIME, NEXPTIME, EXPSPACE) | ✅ | `FondHtn/Cx/Closure.lean`, `Closure2.lean` |
| weak compilation FOND → FOD [CB21 Lem 4.3] (preserves ACYC, TR, TO; not REG) | ✅ | `FondHtn/Weak/*.lean` |
| strong LD compilation [CB21 Lem 4.6], repaired for negative preconditions (∩/∪ tracking) | ✅ | `FondHtn/Upper/StrongCompile.lean`, `StrongDesc.lean` |
| negative preconditions compiled away | not needed (strong compilation handles them directly) | — |
| AND-OR games over polynomial configurations ∈ EXPTIME | ✅ | `FondHtn/Alt/ExpTime.lean` |
| bounded-depth AND-OR games ∈ PSPACE / EXPSPACE | ⏳ (in progress) | `FondHtn/Alt/Depth.lean` |
| CB22 Prop 2: MP weak = FM weak (repetition-free path, G18) | ✅ | `FondHtn/MP/Weak.lean` |
| strong cyclic: literal def. ≠ plan existence on deterministic problems; strong ⇒ fair; fair collapses | ✅ | `FondHtn/MP/StrongCyclic.lean`, `Fair.lean` |
| delaying decompositions (G8), MP strong progression game | ⏳ (in progress) | `FondHtn/MPStrong/` |

## Lower bounds

Inherited from deterministic HTN (✅ for all four FM criteria, for MP weak and strong, and for MP
strong cyclic in the *fair* reading (`hardFair_*`, `FondHtn/MP/Fair.lean`); **not** for the literal
strong cyclic definition of CB22, which does not collapse on recursive deterministic problems,
`LoopEx.literal_not_planExistence`):

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
| CB21 Thm 4.1: PRIM ∩ TO weak NP-hard (SAT) | ✅ `weakLD_PRIM_TO_complete` (`FondHtn/Prim/WeakHard.lean`) |
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
| CB21 Cor 4.2: PRIM weak ∈ NP (NP-complete) | ✅ `weakLD_PRIM_complete`, `weakOD_PRIM_complete` |
| CB21 Thm 4.4: weak LD/OD for ACYC, ACYC∩TO, TR, TR∩TO, TO complete | ✅ `FondHtn/Weak/Mem.lean` |
| CB21 Cor 4.5: REG (∩TO) weak LD/OD PSPACE-complete (via TR of height 2, new proof) | ✅ `FondHtn/Weak/Reg.lean` |
| CB21 Thm 4.7: strong LD for PRIM, ACYC(∩TO), REG(∩TO), TR(∩TO), TO, REG∩ACYC∩TO complete | ✅ `FondHtn/Upper/StrongMem.lean` |
| CB21 Cor 4.8: TO strong OD complete; PRIM∩TO strong LD/OD ∈ P | ✅ `StrongMem.lean`, `FondHtn/Prim/StrongP.lean` |
| CB22 Prop 2 consequences: MP weak for PRIM(∩TO), ACYC(∩TO), REG(∩TO), TR(∩TO), TO complete | ✅ `FondHtn/MP/WeakComplexity.lean`, `WeakReg.lean` |
| CB21 Thm 5.1: PRIM strong OD ∈ PSPACE | ⬜ |
| CB21 Thm 5.2 / 5.3: ACYC / REG strong OD ∈ EXPSPACE | ⬜ |
| CB21 Thm 3.1: semi-decidability | ⬜ |
| CB22 Thms 1–5: MP strong ∈ EXPTIME / EXPSPACE / 2-EXPTIME | ⬜ (alternating search; 2-EXPTIME not yet defined) |
| ideas: TO MP strong ∈ 2-EXPTIME | ❓ (rank argument missing) |
