# Formalising Bercher et al., *Propositional HTN Planning: Problem Classes and Complexity Results*

Status file for the formalisation of the article (`HTN-Complextiy--mainfile.pdf`, draft version) in
the repositories `htn-planning` (model, classes) and `htn-complexity` (complexity results).

## Ground rules (decided 2026-10-24)

* **Model.** The article's own model (negative preconditions, negative goals, "all linearisations
  executable" with ordering insertion, TIHTN) lives in `HtnPlanning/Article/`.  Bridge lemmas
  connect it to the existing model (`HTN.Problem`: positive preconditions, one executable
  linearisation).  Existing proofs stay on the existing model; the *article versions* of the
  theorems are derived through the bridges.
* **Statements.** Literal plan-existence languages `PlanEx` over bit-encoded problems
  (domain + instance), as in Def. 4.1.  This needs polynomial-time recognition of codes and of
  the classes.
* **Proof routes.** The article's route is tried first.  If it is wrong, this is reported here and
  repaired if possible; otherwise an existing alternative route is used and documented.  Existing
  proofs that take other routes are kept.

## Errors and gaps found in the article

| place | problem | handling |
| --- | --- | --- |
| §2, def. of γ | "defined iff `s ⊆ prec⁺`" — should be `prec⁺ ⊆ s` | formalised as `prec⁺ ⊆ s` |
| Def. 2.5 | ordering insertion of `(t,t')` with `t' ≺* t` (or `t = t'`) does not give a strict partial order, contrary to the remark after the definition | the insertion step requires the result to be a strict partial order |
| draft | TIHTN solutions, the acyclic-TIHTN lemma and Prop. 2.1.1 references are `??` | defined following Geier & Bercher (2011) / Alford et al. (2015) |
| Thm 4.1.1 | assumes Chomsky normal form ("w.l.o.g.") | not needed: the encoding works for arbitrary rules incl. ε; the grammars of the reduction have right-hand sides of length ≤ 2, which is what Cor. 4.1.2 needs |
| Thm 4.3.8 | the formal `tn_I` mislabels ids (`t_{2i+1} ↦ φ↦⊤` for all `i`; `t₂` gets two labels) | the intended network (each of the `2n+1` actions once) |
| Thm 4.3.8/4.3.12 | variables numbered `x₁…xₙ` | variables are arbitrary numbers in the code of a formula; the encodings number the *distinct* variables (otherwise not polynomial) |
| Thm 4.3.12 | breaks for formulas without variables (no initial task `x₁`) | a dummy variable is added |
| Thm 4.1.1 | cites undecidability of CFG intersection | proved: from two-stack machines (`ComplexityTheory/CFG/`), via the classical triple construction |
| Lem 4.2.4 | bound `k · m^(h-1) ≤ r^h` on the number of decompositions is wrong: a tree of height `h` and width `m` has up to `1 + m + … + m^(h-1)` inner nodes. Counterexample `tn_I = {A, A}`, `A → {B, B}`, `B → {a}` (`h = k = m = r = 2`): 6 decompositions `> 4` | corrected bound `k · (1 + m + … + m^(h-1)) < (r+1)^h` (`lem_4_2_4`); Thms 4.2.5/4.2.6, Cor 4.2.8 unaffected |
| Def 4.3 | progression bound quantifies over `(s_I, tn_I) →* (s_I, tn)` (initial state only) | all reachable states |
| Lem 4.2.21 | bound `k · m · h` fails for `h = 0` (noHTN: bound `0`) and `m = 0` | corrected `k · (1 + (m-1) · h)`, which is `≤ k · m · h` for `m, h ≥ 1` (`lem_4_2_21_article`) |
| Lem 4.2.15 | `k · m^h` fails for `m = 0` (`h ≥ 1`) | assumes `m ≥ 1` (any upper bound on method sizes can be taken `≥ 1`) |
| Lem 4.2.15 proof | "tasks in the same stratum have the same progression bound" and `c_max` are not made precise (TODO in the draft) | proof via the splitting lemma, induction on the rank with an inner induction on the number of steps |
| Lem 4.2.2 | only strata of size ≥ 2 are collapsed; a singleton stratum `{c}` with a method `(c, [c])` (allowed by Def. 3.7) stays cyclic | all methods that become self-loops are dropped (`HTN.Method.IsLoop`) |
| Cor 4.2.3 | `Sol(P) = Sol(P')` holds only up to task ids (decomposition creates fresh ids) | proved up to isomorphism, for HTN and TIHTN solutions |
| Cor 4.3.3 | "`h` a fixed constant": for `h = 0` the class `TAIL-REC_0` has no compound tasks (noHTN, in NP), so PSPACE-hardness needs `h ≥ 1` | stated for `h ≥ 1` |
| Thm 4.3.4 | the bound `2^#V` (`#V` the number of state variables) | `#V` read as the number of facts of the initial state and the positive effects — the only facts a reachable state contains (`StripsDesc.facts`) |
| Lem 4.2.11 proof | "regular ⇒ height 1 (Thm. 3.0.1), so Cor. 4.2.8 applies": Thm. 3.0.1 is about `≤_r`-stratifications; a `≤₀`-stratification is a total order of the reachable names, so its height is their number (the chain `A₁ → a A₂ → … → a Aₙ` is acyclic and regular of height `n`) | claim proved differently: regular trees are caterpillars of polynomial size (`size_le_of_reg`) |
| Thm 4.2.5 proof | sizes via Lem. 4.2.4, whose bound is wrong | the certificate is bounded directly: a tree rooted at rank `r` has `≤ (B+1)^(r+1)` nodes (`size_le_of_acycCert`) |
| Cor 4.2.23 proof | for `UNRES ∩ TO-M` the progression bounds of Lems. 4.2.15–4.2.21 do not apply (no stratification); "restrict to the acyclic variant" is not made precise | new lemma `tihtn_bound_TOM`: acyclic progression is abstract progression of the problem *unfolded by ancestor sets*, which is acyclic (rank `2(N-|S|) + [c ∈ S]`); bound `k·(1 + (m-1)(2N+2))` |
| Def 4.2 | acyclic progression gives inserted tasks the ancestors `a(t) ∪ {α(t)}` (not their own names), so a name may repeat once in a row (`c → d → d`) | harmless; formalised literally |
| Thm 4.2.12 | second bullet reads `Sol(P)` for the TIHTN solutions | TIHTN solutions |
| Thm 4.3.7 (TR) | extends the acyclic encoding by recursion; not formalised | the tail-recursive encoding of `HtnComplexity/SpaceEnc/` (two alternating loops, one round per machine step, cells stored in the tails of words, addresses checked by binary counters), already proved correct, is used instead |
| Thm 4.3.7 (ACYC) | the printed construction is unsound (head counter one unit ahead of the tape; `heads` count `K+2`) | the repaired construction `TMEnc.problemFix` with the homing machine (`NOTES.md`), already proved correct |
| Thm 4.3.6 | reduces the game G6 and cites its EXPTIME-hardness (Stockmeyer–Chandra), which is not formalised | same technique (methods with inverse actions restore the state, so a sequence of tasks is a universal branching, the choice of a method an existential one), applied to the tableau check of Chandra–Kozen–Stockmeyer: a deterministic machine for the padded language decides it in exponential time, and `chk a` checks the tableau entry `(t, i)` with counters of `B` bits (`HTN.Article.TabData.solvable_iff`) |
| Thm 4.2.10 proof | iterates "over all tasks in tn_I" in their order, but the input lists the order as a relation; recognising codes of well-formed problems of the class in logarithmic space is not discussed | the task of rank `k` (number of predecessors) is found by counting; codes are parsed by positions (a value nested in `d` self-delimiting strings sits in the input at stride `2^d`); the check runs per occurrence of a fact in a precondition or the goal rather than per state variable (same idea, one bit of state) |

## Results — status

Legend: ✅ formal (article version) · 🟡 formal on the existing model / non-uniform form only ·
⬜ not yet.

| result | statement | status | Lean |
| --- | --- | --- | --- |
| Defs 2.1–2.7 | model, Sol(P), TIHTN | ✅ | `HtnPlanning/Article/Model.lean`; bridges `Article/Bridge.lean`, `Article/DualU.lean` (`solvable_ofPos_iff`, `sol_dual`, `solvable_iff_toPos(U)`) |
| Prop 2.1.1 | single initial task | ✅ (plan existence; `Sol` equal only up to ids) | `HTN.Article.prop_2_1_1` |
| Defs 2.8–2.10, Prop 2.2.1 | decomposition trees | ✅ (yields as action sequences; trees indexed by the method's task ids, so `β`/isomorphisms are implicit) | `HtnPlanning/Article/DTree.lean`: `netYield_iff_trees`, `Problem.solvable_iff_trees` |
| (TIHTN) | TIHTN plan existence; cyclic decompositions avoidable (the `??` lemma) | ✅ | `HtnPlanning/Article/TIHTN.lean`: `solvableTI_iff_decomp`, `solvableTI_iff_trees`, `solvableTI_iff_acyc_trees` |
| Defs 3.1–3.11 | classes, heights, `ACYC_h`, `TAIL-REC_h` | ✅ | `HtnPlanning/Article/Classes.lean` |
| Thm 3.0.1 | REG = TAIL-REC₁ | ✅ | `HTN.Article.Problem.thm_3_0_1` |
| Def 4.1 | PlanEx languages | ✅ | `HtnComplexity/Article/PlanEx.lean` (`PlanEx`, `PlanExTI`; descriptions `HtnPlanning/Article/Desc.lean`) |
| Thm 4.1.1 | UNRES undecidable (CFG ∩) | ✅ article route | `HTN.Article.thm_4_1_1`; CFG ∩ undecidable `ComplexityTheory/CFG/Undec.lean`; old route kept in `HtnComplexity/Undec/` |
| Cor 4.1.2, 4.1.3 | restricted undecidability | ✅ | `HTN.Article.cor_4_1_2`, `HTN.Article.cor_4_1_3` |
| Thm 4.1.4 | semi-decidable | ✅ | `HTN.Article.thm_4_1_4` (search on the dual-rail translation `HtnPlanning/Article/ToSyn.lean`) |
| Thm 4.2.1 | TO in EXPTIME | ✅ article route (Alg. 1, dynamic program over all states) | `HTN.Article.thm_4_2_1` (`Article/TOExp.lean`; DP `Article/TODP.lean`, `Article/TODPPT.lean`; refinement semantics `Article/TOSem.lean`; `EXPTIME` = `P` on exponentially padded inputs, `ComplexityTheory/Lang/ExpTime.lean`, `PT/ExpTime.lean`); old route `Space/AltPlanner.lean` |
| Lem 4.2.2, Cor 4.2.3 | MOSTLY-ACYC → ACYC | ✅ semantic (corrected: self-loops) + poly-time computation (`HTN.Article.lem_4_2_2_pt`, `Article/MostlyAcycPT.lean`) | `HTN.Article.Problem.lem_4_2_2`, `cor_4_2_3` (`HtnPlanning/Article/MostlyAcyc.lean`) |
| Lem 4.2.4 | decomposition bound | ✅ corrected (article's bound is false) | `HTN.Article.Problem.lem_4_2_4` (`HtnPlanning/Article/DecompBound.lean`); other bound in `AcVerify/Bound*.lean` |
| Thm 4.2.5 | ACYC (htn) ∈ NEXPTIME | ✅ article route (guess trees + plan; exponential certificate) | `HTN.Article.thm_4_2_5` (`Article/AcycNExp.lean`: acyclicity certificate `Article/AcycCert.lean`, tree certificates `Article/TreeCert*.lean`, execution check `Article/RunCheck.lean`); old route `AcVerify/NExp.lean` |
| Thm 4.2.6, Cor 4.2.7 | ACYC/UNRES (tihtn) ∈ NEXPTIME | ✅ article route (path-acyclic trees + gap lemma) | `HTN.Article.thm_4_2_6`, `cor_4_2_7` (`Article/TINExp.lean`; gap lemma `exists_short_gaps` in `Article/ShortRun.lean`) |
| Cor 4.2.9 | noHTN ∈ NP | ✅ | `HTN.Article.cor_4_2_9`; with Thm 4.3.8: `HTN.Article.noHTN_npComplete` (NP-complete) |
| Cor 4.2.8, Lem 4.2.11 | ACYC_h, ACYC∩REG(∩TO) ∈ NP | ✅ (4.2.11 by a different argument, see errors) | `HTN.Article.cor_4_2_8` (`Article/AcycNP.lean`), `lem_4_2_11`, `lem_4_2_11_TO` (`Article/AcycRegNP.lean`) |
| Thm 4.2.10 | noHTN∩TO ∈ L | ✅ article route (the plan is the initial task network in its order; checked fact by fact with logarithmic counters) | `HTN.Article.thm_4_2_10` (`Article/NoHTNTOL.lean`: the unique linearisation by ranks `Article/NoHTNTORank.lean`, execution fact by fact `Article/NoHTNTOExec.lean`, the checks as terms `Article/NoHTNTOFmt.lean`, `NoHTNTOValid.lean`, `NoHTNTOSteps.lean`, `NoHTNTOExecT.lean`; reading codes in logarithmic space `Logspace/`; `L` and the fold language `ComplexityTheory/Lang/Logspace.lean`, `LogDSL.lean`, `LogCalc.lean`) |
| Def 4.2, Thm 4.2.12, Cor 4.2.13 | progression, acyclic progression | ✅ | HTN: `thm_4_2_12_htn`, `cor_4_2_13_htn` (`Article/Progression.lean`); TIHTN: `thm_4_2_12_tihtn`, `cor_4_2_13_tihtn` (`Article/AcycProgression.lean`, via trees) |
| Def 4.3, Prop 4.2.14, Lem 4.2.15/19/21 | progression bounds | ✅ (4.2.21 corrected) | `HtnPlanning/Article/ProgBoundArticle.lean`: `IsProgBound`, `prop_4_2_14`, `lem_4_2_15`, `lem_4_2_19`, `lem_4_2_21`(`_article`); proofs `Article/AbsProgression.lean` (splitting lemma), `Article/ProgBound.lean` |
| Cor 4.2.16–4.2.22 | TAIL-REC ∈ EXPSPACE; TAIL-REC_h, REG(∩TO), TAIL-REC/ACYC ∩ TO(-M) ∈ PSPACE | ✅ article route (progression search, uniform Savitch) | `HTN.Article.cor_4_2_16`, `cor_4_2_17`, `cor_4_2_18`(`_TO`), `cor_4_2_20`(`_acyc`), `cor_4_2_22`(`_acyc`) (`Article/ProgCors.lean`; search on descriptions `Article/ProgDesc*.lean`, `Article/ProgSpace.lean`; class certificates `Article/TRCert.lean`; `PT/Search.lean`; Savitch without advice `ComplexityTheory/Savitch/Uniform.lean`); old routes `Space/TrSpace.lean`, … |
| Cor 4.2.23–4.2.25 | TIHTN PSPACE memberships | ✅ (4.2.23 for UNRES via a new bound, see errors) | `HTN.Article.cor_4_2_23_tr`, `cor_4_2_23_acyc`, `cor_4_2_24`(`_TO`, `_TOM`, `_regAcyc`, `_regAcyc_TO`, `_regAcyc_TOM`), `cor_4_2_25`(`_TO`) (`Article/TICors.lean`); `cor_4_2_23_unres` (`Article/TIUnres.lean`, bound `HTN.Article.Problem.tihtn_bound_TOM` in `HtnPlanning/Article/Unfold.lean`); acyclic progression on descriptions `Article/AProgDesc.lean`, `Article/AProgSpace.lean` |
| Thm 4.3.1, Cors 4.3.2/4.3.3 | REG/TR PSPACE-hard | ✅ article route (from STRIPS) | `HTN.Article.thm_4_3_1`, `cor_4_3_2`, `cor_4_3_3` (`HtnComplexity/Article/StripsReg.lean`); old encoding `HtnPlanning/Core/Strips.lean` |
| Thm 4.3.4 | ACYC∩TO PSPACE-hard | ✅ article route (doubling encoding + short plans) | `HTN.Article.thm_4_3_4` (`Article/StripsAcyc.lean`, `Article/StripsShort.lean`); old encoding `ToHtnAc/StripsToAc.lean` |
| Thm 4.3.5 | TIHTN PSPACE-hard | ✅ article route | `HTN.Article.thm_4_3_5` (`Article/StripsTI.lean`) |
| Thm 4.3.6 | TO EXPTIME-hard (G6) | ✅ article technique, different source (see errors) | `HTN.Article.thm_4_3_6` (`Article/TOHard.lean`; tableau check `Article/TOHardDesc.lean`, `TOHardAct.lean`, `TOHardSound.lean`, `TOHardComplete.lean`, `TOHardPT.lean`; counters `Article/BinCount.lean`; induction over refinements `Article/TOInd.lean`; deterministic machines for `P` `ComplexityTheory/Machine/Det.lean`, `Machine/PTime.lean`; tableau of a run `ComplexityTheory/TM/Tableau.lean`); old alternation families `Complexity/RecMemUniform.lean` |
| Thm 4.3.7 | ACYC NEXPTIME-hard, TR EXPSPACE-hard | ✅ ACYC: article route; TR: existing alternative route (see errors) | `HTN.Article.thm_4_3_7_acyc` (`Article/NExpHard.lean`: the repaired encoding `TMEnc.problemFix` of the homing machine rendered with an explicit polynomial method list `Article/NExpRend.lean`, `NExpRendU.lean`, computed in polynomial time `Article/NExpPT.lean`, halving closures `Article/HalvingL.lean`); `HTN.Article.thm_4_3_7_tr` (`Article/ExpSpaceHard.lean`: the tail-recursive encoding of `SpaceEnc/` with explicit numberings `Article/ExpSpaceNum.lean`, `Article/ExpSpacePT.lean`); normal form of positive descriptions `Article/SynBridge.lean`, `Article/NBody.lean`; old non-uniform families `Space/NexpFamily.lean`, `SpaceEnc/Family.lean` |
| (cited) | STRIPS PSPACE-hard (Bylander) | ✅ proved | `HTN.Article.strips_pspaceHard` (`Article/StripsTM.lean`: Bylander's encoding of space-bounded machines, `Article/StripsHard.lean`; uses `HTN.Mach.exists_tm_of_inPSpace`) |
| (cited) | SAT NP-hard (Cook) | ✅ | `HTN.Article.sat_npHard` (Cook–Levin of `NPHard/` + polynomial-time conversion) |
| Thm 4.3.8 | noHTN NP-hard (SAT) | ✅ article route | `HTN.Article.thm_4_3_8` |
| Cor 4.3.9 | noHTN without prec⁻ NP-hard | ✅ | `HTN.Article.cor_4_3_9` |
| Cor 4.3.10 | ACYC_h NP-hard | ✅ | `HTN.Article.cor_4_3_10` |
| Cor 4.3.11 | REG∩ACYC NP-hard | ✅ | `HTN.Article.cor_4_3_11` |
| Thm 4.3.12 | REG∩ACYC∩TO(-M) NP-hard (SAT) | ✅ article route | `HTN.Article.thm_4_3_12_TO`, `thm_4_3_12_TOM` |

## Infrastructure added

* `ComplexityTheory/Machine/` (repo `complexity-theory`) — **machine simulations**, the basis of
  all uniform upper bounds and hardness proofs:
  * `NSM.lean` — nondeterministic stack machines (flat code with `guess`/`choose`/`accept`);
    compiled stack programs (`Prog`, the realizers of Cobham's class) run on them;
  * `Seg.lean` — run segments (deterministic stretches give soundness of simulations for free),
    space-bounded runs, restriction of a machine to finitely many states;
  * `SimDef/SimRun/SimStep/SimPre/SimMain.lean` — **a single-tape Turing machine over
    `Option Bool` with `Fin k` states simulating any stack machine** (`HTN.Mach.exists_tm`):
    sound, and complete with explicit time and space bounds;
  * `Logic.lean`, `Kit.lean` — deterministic runs, acceptance, the guessing loop, realizers;
  * `NExp.lean` — **guess and check**: a polynomial-time verifier with certificates of length
    `≤ 2^p(|x|)` gives membership in `NEXPTIME` (`HTN.Mach.inNExp_of_verifier`);
  * `ExpSpace.lean` — **search**: reachability along a polynomial-time transition relation on
    configurations of length `≤ 2^p(|x|)` gives membership in `EXPSPACE`
    (`HTN.Mach.inExpSpace_of_search`);
  * `EvalH.lean`, `SRealize.lean`, `SDec.lean`, `SLoop.lean`, `PSpace.lean` — **the polynomial-space
    function algebra is machine space**: every function of `PSpaceF` is computed by a stack program
    with polynomially bounded stacks (binary counters for the exponential iteration), hence every
    language of `PSPACE` is accepted by a single-tape Turing machine in polynomial space
    (`HTN.Mach.exists_tm_of_inPSpace`) — the identification the development had left open.
* `HtnComplexity/Article/Strips*.lean` — STRIPS problems (`StripsDesc`, `PlanExSTRIPS`), Bylander's
  encoding of space-bounded machines (PSPACE-hardness of STRIPS), short plans, and the article's
  three encodings of STRIPS into REG/TO, ACYC/TO and TIHTN problems.

* `ComplexityTheory/Lang/Basic.lean` — languages, (semi-)decidability, polynomial-time many-one
  reductions, hardness, completeness, names for P, NP, PSPACE, NEXPTIME, EXPSPACE.
* `ComplexityTheory/Lang/Logspace.lean`, `LogDSL.lean`, `LogCalc.lean` — `L` (register programs),
  the fold language with its compilation to register programs, and derived constructs
  (quantifiers, counting, first index).
* `HtnComplexity/Logspace/` — reading codes in logarithmic space: values of nested
  self-delimiting codes sit in the input at a stride `2^d` (`Located.lean`); a parser for the
  formats of codes by positions with its correctness (`Parse.lean`) and as a term (`ParseT.lean`);
  navigation (pairs, list entries, lengths, equality of numbers; `Nav.lean`) and checks on
  located lists (`Check.lean`).
* `HtnComplexity/PT/` — the typed polynomial-time calculus (moved from `htn-compilability`),
  now with polynomial-time *decoders* (`PT/Decode.lean`) and the passage to languages of raw bit
  strings (`PT/Lang.lean`: `inP_codeLang`, `redP_codeLang`).
* `HtnComplexity/PT/NP.lean` — `inNP_codeLang`: languages of codes with polynomial-time
  checkable, polynomially bounded certificates are in NP.
* `HtnComplexity/Article/Valid.lean` — well-formedness of descriptions is decidable in
  polynomial time (`pt_validB`).
* `HtnPlanning/Article/ToSyn.lean` — the dual-rail translation of article descriptions to
  descriptions of `HTN.Syn`, with `solvable_toSyn_iff` (every decision procedure/upper bound for
  `HTN.Syn.Solvable` applies).

## Definitions of the complexity classes

* **P, NP, PSPACE** — Cobham-style function classes, identified with Turing machines
  (`ComplexityTheory/Machine/`).
* **EXPTIME** — `P` on exponentially padded inputs (`HTN.Cx.EXPTIME`, the classical padding
  characterisation).
* **L** — the languages decided by a deterministic **register program** whose registers stay
  polynomially bounded in the input length (`HTN.Cx.L`, `ComplexityTheory/Lang/Logspace.lean`): a
  while program over a fixed finite set of natural-number registers that reads the input only
  through its length and single bits.  A register bounded by `q(n)` holds `O(log n)` bits, so this
  is the classical characterisation of deterministic logarithmic space by machines with a
  constant number of logarithmic-size registers (equivalently, multi-head two-way automata).
  Programs are written as terms of a fold language (`HTN.Cx.LTerm`, `Lang/LogDSL.lean`) and
  compiled to register programs (`HTN.Cx.inL_of_term`).

## Status

All results of the article are formal (article versions, axioms `propext`, `Classical.choice`,
`Quot.sound` only).  Where the article's route was wrong or rests on unformalised literature,
the table of errors above says what was done instead.  Remaining caveats:

* Prop. 2.1.1 and Cor. 4.2.3 hold for solution sets only up to task ids (decomposition creates
  fresh ids); plan existence is preserved exactly.

## Plan (as decided 2026-10-24; carried out)

1. **Article model** (`HtnPlanning/Article/`): Defs 2.1–2.7, TIHTN, classes with stratification
   height, bridges to `HTN.Problem` (negative preconditions compiled away by dual-rail facts;
   ordering insertion ↔ one executable linearisation).
2. **Article descriptions and codes**: finite descriptions with negative preconditions/goals, a
   bit code of whole problems, polynomial-time decoding, polynomial-time class recognition.
3. **Complexity framework** (`complexity-theory`): languages, L, P, NP, PSPACE, EXPTIME, NEXPTIME,
   EXPSPACE; polynomial-time (and logspace) many-one reductions; hardness, completeness;
   (semi-)decidability of languages.
4. **Results**, in the order: undecidability / semi-decidability; NP results (SAT); PSPACE
   results (STRIPS, progression bounds); NEXPTIME; EXPTIME; EXPSPACE; L.
