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
| bounded-depth AND-OR games ∈ PSPACE / EXPSPACE | ✅ | `FondHtn/Alt/Depth.lean` |
| 2-EXPTIME (padding) and AND-OR games over exponential configurations ∈ 2-EXPTIME | ✅ | `FondHtn/Cx/Exp2.lean` |
| CB22 Prop 2: MP weak = FM weak (repetition-free path, G18) | ✅ | `FondHtn/MP/Weak.lean` |
| strong cyclic: literal def. ≠ plan existence on deterministic problems; strong ⇒ fair; fair collapses | ✅ | `FondHtn/MP/StrongCyclic.lean`, `Fair.lean` |
| delaying decompositions (G8), MP strong progression game | ✅ | `FondHtn/MPStrong/Prog.lean`, `Game.lean` |

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
| REGtn (∩ TO) (CB21 regular: tn_I regular too) | PSPACE, all FM criteria, MP weak/strong, fair | `FondHtn/RegTn/Hard.lean` (direct STRIPS reduction, goal checked by a terminal method); PSPACE-complete for weak LD/OD, strong LD, MP weak |

FOND-specific lower bounds:

| result | status |
| --- | --- |
| CB21 Thm 4.1: PRIM ∩ TO weak NP-hard (SAT) | ✅ `weakLD_PRIM_TO_complete` (`FondHtn/Prim/WeakHard.lean`) |
| CB21 Thm 5.1: PRIM (PO) strong OD PSPACE-hard | ✅ repaired via TQBF (TQBF PSPACE-hard from STRIPS by Savitch), `FondHtn/QBF/`; complete: `strongOD_PRIM_complete` |
| CB22 Thm 1: ACYC ∩ TO MP strong EXPTIME-hard | ✅ new reduction from TO HTN (path game on the DP table), `FondHtn/HardMP/`; EXPTIME-complete `strongMP_ACYC_TO_complete` (also fair) |
| CB22 Thm 2: ACYC MP strong EXPSPACE-hard | ⚠ sketch only ⬜ (attempt and obstacles: `doc/notes_cb22_thm2.md`) |
| CB22 Thms 1, 3, 4 for fair strong cyclic: EXPTIME-complete (ACYC∩TO, TR∩TO, REG, REG∩TO) | ✅ `FondHtn/HardMP/Fair*.lean` (REG needs a round counter: without it a fair policy can cycle — counterexample in `FairC.lean` doc) |
| CB22 Thm 3: REG (∩TO) MP strong EXPTIME-hard | ✅ from TO HTN (not FOND planning); complete `strongMP_REG_complete`, `strongMP_REG_TO_complete` |
| CB22 Thm 4: TR ∩ TO MP strong EXPTIME-hard | ✅ complete `strongMP_TR_TO_complete` |
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
| CB21 Thm 5.1: PRIM strong OD ∈ PSPACE | ✅ `FondHtn/StrongOD/Prim.lean` |
| CB21 Thm 5.2: ACYC strong OD ∈ EXPSPACE | ✅ `FondHtn/StrongOD/Acyc.lean` |
| CB21 Thm 5.3: REGtn strong OD ∈ EXPSPACE | ✅ `FondHtn/StrongOD/Reg.lean` (sequential composition `bsw_comp`, belief-set chains); Bercher REG (tn_I arbitrary) ⬜ (parallel chains) |
| CB21 Thm 3.1: semi-decidability (weak LD/OD, strong LD, MP weak) | ✅ `FondHtn/Upper/SemiDec.lean`; strong OD ⬜ |
| CB22 Thms 1, 3, 4: MP strong ∈ EXPTIME (ACYC∩TO, REG(∩TO), TR∩TO) | ✅ `FondHtn/MPStrong/Mem.lean` (hardness ⏳) |
| CB22 Thms 1–5 for **fair** strong cyclic: ACYC∩TO, REG(∩TO), TR∩TO ∈ EXPTIME, ACYC ∈ EXPSPACE (fair = strong on ACYC), TR ∈ 2-EXPTIME; G8 holds for the fair reading | ✅ `FondHtn/MPStrong/Cyclic*.lean`, `FondHtn/Alt/Buchi.lean` (hardness ⬜) |
| CB22 Thms 2, 5: MP strong ACYC ∈ EXPSPACE, TR ∈ 2-EXPTIME | ✅ `FondHtn/MPStrong/Acyc.lean`, `TR.lean` (hardness ⬜) |
| ideas: TO MP strong ∈ 2-EXPTIME | ✅ `strongMP_TO_mem` (`FondHtn/MPStrong/TOGame.lean`, `TODesc.lean`; rank argument = sequential composition) |
| ideas: TO MP fair strong cyclic ∈ 2-EXPTIME | ❓ table fails (counterexamples, `doc/notes_to_fair.md`); needs pushdown-Büchi summaries |
