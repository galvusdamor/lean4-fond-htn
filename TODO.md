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

### 1.2 Total order — hardness (2-EXPTIME-hard, strong MP) **[DONE]**
- Proved: `FOND.TOHard2.hard_TO_mpStrong`, with membership `FOND.TOHard2.complete_TO_mpStrong`
  (2-EXPTIME-complete), `FondHtn/TOHard2/` (construction `doc/notes_to_hard.md`; soundness
  `SoundK.lean`, completeness `CompleteK.lean`, machine link `Red.lean`, PT `PT.lean`).
- Open follow-up: the fair strong cyclic version (`hardFair_TO` is only EXPTIME).

### 1.3 Counters — ACYC EXPSPACE-hard (FM strong OD and MP strong = CB22 Thm 2) **[DONE]**
- Proved: `FOND.AcycHard.hard_ACYC_strongOD`, `hard_ACYC_mpStrong`, `hard_ACYC_mpFair` and the
  EXPSPACE-completeness versions (`FondHtn/AcycHard/Main.lean`); construction
  `doc/notes_acyc_expspace.md` (chain game, FIFO cell queue, supply, Savitch program `SavProg`,
  single-method hierarchy `Hier*`, transfer to coded names, instance `Inst*`, PT `InstPT`).

### 1.4 Counters — TR 2-EXPTIME-hard (MP strong and fair = CB22 Thm 5) **[DONE]**
- Proved: `FOND.HardTR.complete_TR_mpStrong` and `FOND.HardTR.complete_TR_mpFair`
  (2-EXPTIME-complete), `FondHtn/HardTR/` (plan `doc/notes_cb22_thm5_progress2.md`):
  source game `Source.lean`/`SrcTab.lean`, tableau transducer `Tab.lean`, round lemma `Round.lean`,
  encoding `Enc*.lean`, description `TDesc*.lean`, soundness `TSound.lean` (word game `WTrans.lean`,
  language `TLang.lean`), completeness `TPlay.lean` (tagged chain game `TChains.lean`/`TGame.lean`,
  canonical run `TComp.lean`), TR certificate `TClass.lean`, instance `TInst.lean`, PT `TPT.lean`,
  assembly `TMain.lean`; fair: `WSafe.lean`, `TFair.lean`.
- Fair: the transducer game `Mach.Win` is the *safety-closed* configuration game (`SWin`); the
  round lemma never needed induction on the game, termination comes from the tableau time. A fair
  policy gives the progression fair game (`mpStrongCyclicFairSolvable_iff_prog`) and from it the
  safe word game (`lsafe_of_fairWin`), pulled back to records and configurations.

### 1.5 PCP — TR / Bercher-REG FM strong OD undecidable **[DONE]**
- Proved: `FOND.PCP.undecidable_strongOD_REG_TR` (`FondHtn/PCP/Reduction.lean`). It reduces
  directly from the halting problem of `undecTSM` (no PCP needed); construction and check:
  `doc/notes_pcp_check.md`.
- No follow-ups: the analogous undecidability cannot hold for the other criteria. On REG
  (Bercher) and on TR, every other criterion is already proved decidable: weak LD/OD
  (`weakOD_REG_complete` PSPACE, `weakOD_TR_complete` EXPSPACE), strong LD
  (`FondHtn/Upper/StrongMem.lean`), MP weak (`FondHtn/MP/WeakComplexity.lean`, `WeakReg.lean`),
  MP strong (`strongMP_REG_complete` EXPTIME, `strongMP_TR_mem` 2-EXPTIME) and MP fair
  (`fairMP_REG_complete`, `fairMP_TR_mem`). The undecidability is specific to strong OD (one
  decomposition fixed in advance against all outcomes). For `REGtn` strong OD is EXPSPACE-complete
  (`strongOD_REGtn_complete`); the PCP instances are not in `REGtn` (tn_I has four unordered roots).

---

## 2. CB21

- **Thm 5.3 for Bercher-style REG** (tn_I arbitrary): membership open; parallel chains
  interleave with unbounded lag (`doc/notes_reg_strongOD.md`). EXPSPACE-hardness is proved
  (`strongOD_REG_expspaceHard`). **Settled**: undecidable, since `REG ∩ TR ⊆ REG`
  (`FOND.PCP.undecidable_strongOD_REG_TR`), so no EXPSPACE membership.
- Everything else of CB21 is done (see `STATUS.md`).

## 3. CB22

- Thm 2 lower bound: see 1.3. Thm 5 lower bound: see 1.4 (MP strong and fair done).
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
