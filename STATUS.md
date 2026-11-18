# Status of the complexity results

Open work and next steps: `TODO.md`.

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
| alternating sources: EXPSPACE = Savitch game (`expspace_savWin`), 2-EXPTIME = CKS tableau game (`exptime2_tabWin`) | ✅ | `FondHtn/ATM/`, `doc/notes_atm.md` |
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
| DB25 Thm 1: chosen-length games EXPSPACE-complete | ⬜ not formalised (not needed: Thm 4/5 proved directly from NTMs) |
| DB25 Thm 4/5: REG(tn) FM strong OD EXPSPACE-hard | ✅ `FondHtn/DB25/Hard.lean` (direct reduction from exp-space NTMs, positive preconditions only); REGtn EXPSPACE-complete `strongOD_REGtn_complete` |
| ideas: PCP, TR/Bercher-REG FM strong OD undecidable | ❓ sketch does not work with STRIPS-style FOND actions (inactive mode's checks cannot be freed); no PCP in library — `doc/notes_pcp_strongOD.md`; needs the author's input |
| ideas: counters, ACYC EXPSPACE-hard / TR 2-EXPTIME-hard | ❓ construction and missing pieces (ATM source EXPSPACE ⊆ AEXPTIME, parallel-chain semantics) in `doc/notes_acyc_strongOD.md` |
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
| CB21 Thm 3.1: semi-decidable and undecidable for all four FM criteria (and MP weak) | ✅ `FondHtn/Upper/SemiDec.lean`, `FondHtn/StrongOD/SemiDec.lean` (`thm_3_1_all`) |
| CB22 Thms 1, 3, 4: MP strong ∈ EXPTIME (ACYC∩TO, REG(∩TO), TR∩TO) | ✅ `FondHtn/MPStrong/Mem.lean` (hardness ⏳) |
| CB22 Thms 1–5 for **fair** strong cyclic: ACYC∩TO, REG(∩TO), TR∩TO ∈ EXPTIME, ACYC ∈ EXPSPACE (fair = strong on ACYC), TR ∈ 2-EXPTIME; G8 holds for the fair reading | ✅ `FondHtn/MPStrong/Cyclic*.lean`, `FondHtn/Alt/Buchi.lean` (hardness ⬜) |
| CB22 Thms 2, 5: MP strong ACYC ∈ EXPSPACE, TR ∈ 2-EXPTIME | ✅ `FondHtn/MPStrong/Acyc.lean`, `TR.lean` (hardness ⬜) |
| CB22 arbitrary PO: MP weak and strong semi-decidable and undecidable | ✅ `FondHtn/MPSemi/Strong.lean` (`mp_weak_strong_semi_undec`); fair: open, `doc/notes_fair_semidec.md` |
| ideas: TO MP strong ∈ 2-EXPTIME | ✅ `strongMP_TO_mem` (`FondHtn/MPStrong/TOGame.lean`, `TODesc.lean`; rank argument = sequential composition) |
| ideas: TO MP fair strong cyclic ∈ 2-EXPTIME | ✅ `fairMP_TO_mem` via summary game with exit sets/targets (`FondHtn/MPStrong/TOFair2*.lean`, `FondHtn/Alt/Buchi2.lean`, `doc/notes_to_fair_3.md`); the ideas-file table itself is wrong for the fair reading (`doc/notes_to_fair.md`) |

## Ideas file (`doc/ideas_for_pascal_spring_2025.md`) at a glance

| idea | status |
| --- | --- |
| Total order, membership (strong / fair) | ✅ `strongMP_TO_mem`, `fairMP_TO_mem` (fair needs a corrected summary game) |
| Total order, 2-EXPTIME hardness | construction completed on paper (`doc/notes_to_hard.md`), formalisation partial (`FondHtn/TOHard2/`) |
| Counters, ACYC EXPSPACE-hard | core proved (`FondHtn/AcycHard/`), remaining layers in `doc/notes_acyc_expspace.md` |
| Counters, TR 2-EXPTIME-hard | source + round lemma proved (`FondHtn/HardTR/`), encoding open |
| PCP | plan: repaired by gated cheat tasks (`doc/notes_pcp_strongOD.md`); formalisation and PCP undecidability open |
