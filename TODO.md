# TODO

Open work on the formalisation of FOND HTN complexity (CB21, CB22, DB25, and the ideas file
`doc/ideas_for_pascal_spring_2025.md`). What is done is in `STATUS.md`; the deviations from the
papers are in `modifications/main.tex`. Every `doc/notes_*.md` file referenced below has the
detailed construction or obstruction for its item.

Legend: **[WIP]** partial Lean files exist · **[PLAN]** construction on paper, no Lean yet ·
**[BLOCKED]** needs a decision or new idea · **[OPEN]** not attempted.

---

## 1. Ideas file (`doc/ideas_for_pascal_spring_2025.md`)

### 1.1 Total order — membership ✅ done
- Strong: `strongMP_TO_mem` (2-EXPTIME). Fair strong cyclic: `fairMP_TO_mem` (2-EXPTIME,
  corrected summary game; the proposed table is wrong for the fair reading,
  `doc/notes_to_fair.md`, `notes_to_fair_2.md`, `notes_to_fair_3.md`).

### 1.2 Total order — hardness (2-EXPTIME-hard, strong MP) **[WIP]**
- Construction completed on paper: `doc/notes_to_hard.md` (deviates from the ideas file: CKS
  tableau claims, three-way L/C/R challenge, enforced chain length).
- Partial Lean: `FondHtn/TOHard2/` (Auto, Bits, Chain, Desc, Game, Shape, Sound, State, Transfer),
  compile and are sorry-free (intermediate lemmas).
- Next:
  1. Soundness of a claim task `K` (the agent stopped right after `Transfer`).
  2. Completeness of `K`.
  3. `padExp2` copies of `good_dOf` / `solvable_dOf_iff`.
  4. Validity, class TO, PT layer, final theorem; then `Cx.Complete` with `strongMP_TO_mem`.
  5. Fair version (`hardFair_TO` is only EXPTIME).

### 1.3 Counters — ACYC EXPSPACE-hard (FM strong OD and MP strong = CB22 Thm 2) **[WIP]**
- Core proved: `FondHtn/AcycHard/` (chain game, FIFO cell queue, supply, `beliefSolvable_iff_qi`).
- Plan: `doc/notes_acyc_expspace.md` §6. Source: `FOND.ATM.expspace_savWin`.
- Next:
  1. L3: queue game → Savitch game (`QI` as an automaton queue game, sweep lemma, list
     version of `SavWin`, check automaton for `x ⊢ y`), ≈1000–1500 lines.
  2. L1b/L1c: the acyclic hierarchy (doubling, binary counts), every reachable primitive network
     is `IsChains`; for MP: `MPAndOr tn s ↔ CWin(expansions)` on partially decomposed networks.
  3. L1d: descriptions, validity, ACYC, PT layer.
  4. Assembly: `Cx.Hard Cx.EXPSPACE (PlanExFM .strongOD FClass.ACYC)` and
     `(PlanExMP .strong FClass.ACYC)`; completeness with `strongOD_ACYC_mem`, `strongMP_ACYC_mem`;
     fair via `planExMPFair_eq_strong`.

### 1.4 Counters — TR 2-EXPTIME-hard (MP strong and fair = CB22 Thm 5) **[WIP]**
- Proved: `FondHtn/HardTR/{Source,WGame,Round}.lean` (source game with all-ones counters,
  word game layer, abstract round lemma `round_sound`, `boot_sound`).
- Partial: `FondHtn/HardTR/{Lang,Row,SrcTab,Tab}.lean` (compile, sorry-free; intermediate).
- Plan: `doc/notes_cb22_thm5_progress2.md`.
- Next: P3a (tableau transducer as `Mach`, induction on `t`), P1/P2 (refinements accepted by the
  automaton, encoding, descriptions, PT, TR certificate), P4 (completeness on real networks),
  P5/P6 (assembly, completeness with `strongMP_TR_mem` / `fairMP_TR_mem`).

### 1.5 PCP — TR / Bercher-REG FM strong OD undecidable **[PLAN]**
- The original sketch fails (inactive mode's checks block); repaired by gated cheat tasks
  (author's suggestion, see the end of `doc/notes_pcp_strongOD.md`). Next: formalise the
  construction; instances are Bercher-REG ∩ TR (two compound tasks in tn_I).
- Also needs a PCP undecidability proof (none in the library; from `undecTSM` or a TM
  simulation).

---

## 2. CB21

- **Thm 5.3 for Bercher-style REG** (tn_I arbitrary): membership open; parallel chains
  interleave with unbounded lag (`doc/notes_reg_strongOD.md`). EXPSPACE-hardness is proved
  (`strongOD_REG_expspaceHard`). Possibly undecidable (cf. 1.5). **[OPEN]**
- Everything else of CB21 is done (see `STATUS.md`).

## 3. CB22

- Thm 2 lower bound: see 1.3. Thm 5 lower bound: see 1.4.
- **Literal strong cyclic** (Def. 7 as written): only the separation from plan existence is
  proved (`LoopEx.literal_not_planExistence`). Upper/lower bounds for the literal reading are
  not done; we treat the fair reading as the intended one. **[OPEN — decide whether wanted]**
- **Fair strong cyclic, unrestricted problems**: semi-decidability open; conjectured not RE
  (`doc/notes_fair_semidec.md`). **[OPEN]**

## 4. DB25

- Thm 4/5 (regular strong OD EXPSPACE-hard) ✅ via a direct NTM reduction.
- **Thm 1 and Lemmas 1–3 (chosen-length games EXPSPACE-complete)** **[WIP]**: partial files in
  `FondHtn/DB25Games/` (Build, Game, HardDesc, Main, Sem, Tab); agent stopped at the usage limit
  without a report. Next: check what compiles, finish game semantics, lemmas, membership,
  hardness; write `doc/notes_db25_games.md`.

## 5. Housekeeping

- `deps/` is read-only (vendored libraries, `deps/README.md`); missing library lemmas go into
  `FondHtn/`.

- Resume the three agents stopped by the usage limit (TOHard2, HardTR, DB25Games) or restart from
  the notes.
- Update `doc/results_catalogue.md` §7 gaps with the repairs (G6/G7/G8/G9/G11/G13/G17/G18 are
  addressed; see `modifications/main.tex`).
- Linter warnings in `FondHtn/DB25/` (unused variables/simp args).
- Fix `doc/results_catalogue.md` statements now superseded by results (e.g. CB21 Thm 5.1 is
  repaired via TQBF).

## Compile status of partial files

All partial modules from the agents stopped by the usage limit compile without errors and without
`sorry` (checked with `lake build` per module) and are imported in `FondHtn.lean`:
`FondHtn/TOHard2/*` (9 modules), `FondHtn/HardTR/{Lang,Row,SrcTab,Tab}`,
`FondHtn/DB25Games/*` (6 modules). They contain intermediate lemmas only; none of the target
theorems of 1.2, 1.4 or 4 is proved yet.
