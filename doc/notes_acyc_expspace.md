# EXPSPACE lower bounds for acyclic partially ordered FOND HTN problems

Targets:
1. CB22 Thm 2: `Cx.Hard Cx.EXPSPACE (PlanExMP .strong FClass.ACYC)` (also fair, via
   `planExMPFair_eq_strong`);
2. CB21 Thm 5.2 lower bound (ideas file "counters"): `Cx.Hard Cx.EXPSPACE (PlanExFM .strongOD
   FClass.ACYC)`.

Membership is proved for both (`strongMP_ACYC_mem`, `strongOD_ACYC_mem`).

Status: **one construction serves both targets**. What is **formalised** in
`FondHtn/AcycHard/` (no sorry, standard axioms only), §3:
* the combinatorial core, the FIFO queue of counter cells (the "hard combinatorial core" of
  `notes_acyc_strongOD.md` §3.2);
* the bridge from belief solvability of a union-of-chains network;
* the supply argument.

Together: `beliefSolvable_iff_qi`. The remaining layers are listed in §6 with their proof
obligations.

## 1. Decisions and why they avoid the known obstacles

**Single methods.** Every compound task name of the construction has exactly one method. The
hierarchy only serves to *generate* an exponentially large primitive network. It is acyclic:
its compound tasks are doubling clocks.

Consequences:
* **FM.** Fixed methods: there is exactly one achievable primitive network up to isomorphism.
  Strong OD solvability is belief solvability of that network.
* **MP.** Method-based policies: a decomposition choice does not exist, so the commitment
  obstacle of `notes_cb22_thm2.md` §4 disappears. Delaying a decomposition only delays the
  *generation* of tasks, not a choice.
  * Lemma (§6, L1b): for single-method acyclic problems, `MPAndOr tn s` holds iff
    `BeliefSolvable (full decomposition of tn) s`.
  * So `MPStrongSolvable ↔ StrongODSolvable` on the constructed problems, and
    `planExMPFair_eq_strong` covers the fair reading.

**Where the alternation lives.**
* Existential: the *order* in which the player executes pool tasks. Executed tasks are gone,
  so this order is irrevocable, which provides commitment for free.
* Universal: nature's outcome of one control action per round.
* As argued in `notes_acyc_strongOD.md` §1, a fixed network cannot hold the existential
  choices. The policy's execution order supplies them.

**Source: the Savitch game** `FOND.ATM.expspace_savWin`, or directly `AcceptsInSpace` with the
`≤ 2^K` run bound.
* Positions are pairs of configurations with `S = 2^p(|w|)` cells.
* A round runs as follows:
  1. the player writes a midpoint configuration `d` cell by cell (her choice of the symbol of
     each new cell);
  2. nature picks a half;
  3. the next round reads the chosen pair.
* There are `K = k + p + 2·2^p` rounds; the hierarchy counts them, so no counter is needed in
  the state.
* The base case `x = y ∨ x ⊢ y` is checked by a finite automaton sweeping over the cells.
* Nothing needs an ATM, a head counter or a transition gadget. The tape head is a marker inside
  the cell symbols, and the machine `N` is fixed by the language, so all alphabets and
  automata are constant-size, apart from the `|w| + 1` input states of §4.

**Memory: a FIFO of counter cells.** This is the "counters" idea, simplified. The tape is not
updated in place. Each round *rewrites* the whole sequence of `S` cells. The queue delivers
the cell written `S` steps earlier, so every round reads the previous round's cells in order.

## 2. The network (after decomposition): one control chain plus pools

All tasks are primitive after decomposition. The network is the disjoint union of:
* the **control chain**, totally ordered;
* **pool chains**, each totally ordered, pairwise unordered and unordered with the control.

Facts: tokens `op g`, `dn g` for the gates `g ∈ {T, R, F, I, U}`, plus data facts.

| pool task | gate | data pre | data effect |
|---|---|---|---|
| `init τ` | I | – | add `wr τ` |
| `tick` | T | – | – |
| `res` | R | – | – |
| `fin τ` | F | – | add `rd τ` |
| `opt o` | U | `opre o` | add `oadd o`, del `odel o` |

Every pool task with gate `g` has precondition `op g`, deletes `op g` and adds `dn g`.

| control task | pre | effect |
|---|---|---|
| `opn g` | – | add `op g` |
| `cls g` | `dn g` | del `dn g` |
| `plain p` | data pre | data effects, possibly several (nature) |
| `refill` | – | add **all** facts |

**Window.** `opn g · cls g`: between them the player must execute exactly one pool task of gate
`g` and nothing else (formalised: `WSys.cwin_iff_wwin`).

**Cells.** A cell is the chain `init τ · (tick · res)^S · fin τ`. The initial *blank* cells are
`(tick · res)^S · fin b` (no `init`). The pools are:
* `S` blank cells;
* for every symbol `τ`, `N` fresh cells;
* for every option `o`, `N` copies of `[opt o]`.

Here `N ≥` the number of steps.

**Control chain:**

    preW(tri S) · expandQ(prog) · refill^R

* `preW m = (opn T cls T opn R cls R)^m`, with `tri S = S(S-1)/2`.
* A **step** is the window program `T^S R^S F I U`.
* `prog` is a list of steps and plain actions, described in §4.
* `R ≥` the total number of pool tasks.

**Why the queue works** (formalised, `FSpec.wwin_step`, `wwin_Tphase`, `wwin_Rphase`):
* A cell that has ticked must resume before it ticks again.
* So `S` windows `T` with `S` live cells tick *every* live cell exactly once, and the `S`
  windows `R` resume them all.
* The unique cell with no unit left then finishes in window `F`. It reports its symbol `rd σ`.
* In window `I` the player starts a fresh cell `τ` of her choice, reported as `wr τ`.
* In window `U` she executes an option whose precondition holds. This is how the data state,
  i.e. the automaton, is updated, and how illegal choices of `τ` are punished: no option
  applies, so she is stuck.

**Initial staggering without a staircase.**
* The blank cells start with `S` units each.
* `preW(tri S)` gives `tri S` single-unit advances, distributed by the player.
* Unless the units end up as exactly `{1, …, S}`, some value `v ∈ [1, S]` is missing. Each
  step moves the gap one unit down, and when it reaches `1`, window `F` is stuck
  (`FSpec.not_wwin_bad`).
* So any program with at least `S` steps forces perfect staggering.
* This replaces the varying-length warm-up phases, which a polynomial acyclic hierarchy cannot
  generate.

**Trash.** After the program, `refill^R` lets the player empty the remaining pools: unused
fresh cells, unused options and the last `S` live cells. `refill` adds every fact, so every
pool task is applicable (`WSys.cwin_refill`). Acceptance is checked by a plain action
*before* the trash.

## 3. Formalised (no sorry, standard axioms only)

`FondHtn/AcycHard/ChainGame.lean`:
* `CWin δC δP ctl M s`: the chain game, i.e. the control chain plus a multiset of pool chains,
  with the belief-solvability rules.
* `WSys`: gates and data effects; `δP`, `δC`: the token encoding; `expand`.
* `WSys.WWin`: the window game.
* `WSys.cwin_refill`: trash.
* **`WSys.cwin_iff_wwin`**: `CWin δC δP (expand ws ++ replicate R refill) M (idle d) ↔ WWin
  ws M d`, for `size M ≤ R`.

`FondHtn/AcycHard/Fifo.lean`:
* `FSpec` (with `S`, `rd`, `wr`, options, plain actions), `PA`, `Gate`, `cellR`, `newCell`,
  `liveR`/`liveP` (resumed/paused cells as multisets of `(symbol, units left)`), `UOk`.
* Window lemmas `wwin_T/R/F/I/U`, phase lemmas `wwin_Tphase`, `wwin_Rphase`, the step lemma
  `wwin_step`.
* `enc q i`: the cells of a queue. The queue game `QWin prog q U d`: a step on `σ :: q` lets
  the player append `τ` and execute an option `o` with `opre o ⊆ d ∪ {rd σ, wr τ}`. Plain
  actions are universal over their outcomes.
* `wwin_good_iff`: on a well-staggered queue, the window game equals the queue game.
* `not_wwin_bad`: bad staggering loses.
* `PreReach`, `PreReach.stagger`, `wwin_preW`: the pre-warm phase.
* **`FSpec.wwin_fifo_iff`** and **`FSpec.cwin_fifo_iff`**:

      CWin δC δP (expand (preW (tri S) ++ expandQ prog) ++ replicate R refill)
          (liveR (replicate S (b, S)) + U) (idle d)
        ↔ QWin prog (replicate S b) U d

  Hypotheses:
  * plain actions have ≥ 1 outcome;
  * `U` consists of fresh cells, options and `[]`;
  * `prog` has ≥ `S` steps;
  * `R ≥` pool size.

`FondHtn/AcycHard/Supply.lean` (L3a):
* `FSpec.QI aS aO prog q d`: the **supply-free queue game**, with allowed symbols `aS` and
  options `aO`.
* `FSpec.Rich U n`: the pool has `≥ n` fresh cells per allowed symbol, `≥ n` copies per
  allowed option, and nothing else besides `[]`.
* **`qwin_iff_qi`** and **`cwin_iff_qi`**: the chain game of the construction is `QI prog
  b^S d`.

`FondHtn/AcycHard/Chains.lean` (L1a):
* `IsChains tn ctl pool ℓ`: `tn` is the disjoint union of id chains, ordered within chains,
  with primitive labels `ℓ`.
* **`beliefSolvable_iff_cwin`**: `P.BeliefSolvable tn s ↔ CWin P.δ P.δ (ctl.map ℓ)
  (pool.map (map ℓ)) s`.
* **`cwin_sum_iff`**: relabelling to the action type `CI ⊕ PA` with `δ = Sum.elim δC δP`.

`FondHtn/AcycHard/Assembly.lean`:
* **`beliefSolvable_iff_qi`**: for a problem with `δ = Sum.elim δC δP` and a network `tn` that
  is (`IsChains`) the control chain `preW (tri S) · expandQ prog · refill^R` together with the
  `S` blank cells and a rich supply,

      Pb.BeliefSolvable tn (idle d) ↔ QI aS aO prog (b^S) d

  This is the whole HTN-independent core: from strong OD solvability of the decomposed
  network down to the supply-free queue game.

## 4. The program and the automaton (paper level; obligations L3b–L3d in §6)

Cell symbols: `Sym = Option (X × X × X)`, with `none` the blank `b` and `X = Γ × Option Q`
(tape symbol, and the state if the head is there). A configuration `c` with `c.head < S` is
encoded as `encC c = [(c.tape i, if i = c.head then some c.state else none) | i < S]`.

Data facts: `st a` for automaton states `a`, plus the transient `rd σ`, `wr τ`. **Between
steps the data state is always a singleton `{st a}`**; there are no mode facts and no input
facts.
* Options are the transitions `(a, σ, τ, a') ∈ Δ` of one NFA: `opre = odel = {st a, rd σ,
  wr τ}`, `oadd = {st a'}`.
* From `{st a}`, a step reading `σ` is therefore: the player picks `τ` and `a'` with
  `(a, σ, τ, a') ∈ Δ`, and the new state is `{st a'}`.
* The automaton's states are partitioned by mode, and `Δ` preserves the mode. So options of
  other modes never apply, and mode switches happen only by plain actions, at statically
  known positions of the control.

`prog`, in order:
1. **Input sweep** (`S` steps). States `In i` for `i ≤ |w|`, input-dependent: there are
   `|w| + 1` of them, `In |w|` meaning "beyond the input".
   * Transition `(In i, b, (x_i, e, e), In (min(i+1, |w|)))`, where `x_i = encC(c₀)_i` (the
     input symbol or blank, with the marker `q₀` at `i = 0`).
   * `e` is arbitrary, except that a marker in `e` must carry an accepting state.
   * The queue becomes `(c₀, e, e)`, with `e` the claimed accepting configuration.
   * Then the plain action `toRd`: delete all `st (In i)`, add `st (Rd L)`.
2. **K rounds**, each consisting of `S` steps in mode `Rd h`, then a plain action:
   * the transition is `(Rd h, (a, m, b'), (x, d, y), Rd h)` iff `(x, y) = proj_h (a, m, b')`,
     where `proj_L = (a, m)` and `proj_R = (m, b')`; `d` is arbitrary;
   * after rounds `1 … K−1`, the plain action `half` deletes `st (Rd L), st (Rd R)` and has
     the two outcomes add `st (Rd L)` / add `st (Rd R)`;
   * after round `K`, the plain action `halfChk` has the same deletes and the outcomes add
     `st (Chk L c₀)` / add `st (Chk R c₀)`. The control knows statically which round is last.
3. **Check sweep** (`S` steps), mode `Chk h`. The NFA reads `proj_h` of the read triples and
   checks:
   * both components are valid encodings (exactly one marker);
   * `x = y`, or `x ⊢ y`:
     * it guesses `tr = (q, a, q', b, mv) ∈ N.step`, applied at the marker of `x`;
     * the marker of `y` is at `mv.apply i`; left at 0 stays, as in `Move.apply`;
     * right at `S − 1` leaves no marker in `y`, so the check fails, matching `head < S`;
   * window: the previous cell pair, for left moves.

   The NFA guesses the last cell and moves to the unique state `ChkOK`, which has no
   outgoing transitions. Written symbols are arbitrary.

   Then the plain action `acc` with precondition `{st ChkOK}`.

Steps: `S·(K + 2) ≥ S`. Plain actions have ≥ 1 outcome. Supply: `n = S·(K + 2)` per allowed
symbol and per transition.

**Shape invariant (part of L3b).** Every plain action deletes all states of its mode, and is
reached only in that mode. Hence the data state stays a singleton `{st a}` with `a` in the
mode of the program position, for **every** play, adversarial ones included. `QI` on such
states is the **automaton queue game**:

    AQ (plain p :: r) q a = (a satisfies pre p) ∧ ∀ a' ∈ out p, AQ r q a'
    AQ (step :: r) (σ :: q) a = ∃ τ a', (a, σ, τ, a') ∈ Δ ∧ AQ r (q ++ [τ]) a'

## 5. Correctness argument (paper)

`QWin prog (b^S) U {st In}` holds iff:

    ∃ e accepting, ListWin K (encC c₀) e

where:

    ListWin 0 x y := Chk x y
    ListWin (k+1) x y := ∃ m, ∀ h, ListWin k (proj_h (x, m, y))

* **L3a (supply).** Done: `qwin_iff_qi`.
* **L3b (shape invariant and sweep lemma).** First, `QI` on singleton states equals `AQ`.
  Then the sweep lemma: `S` steps in a fixed mode from queue `q` (length `S`) and state
  `{st a}` reach queue `t` and state `{st a'}` iff `t` is chosen symbol by symbol and there is
  an automaton run `a → a'` on `zip q t`. The queue after `j` steps is
  `drop j q ++ take j t`. Induction on `j`.
* **L3c (rounds).** Round `k` with the queue holding triples whose `proj_h` is `(x, y)`:
  * the player's writes are exactly triples `(x_i, m_i, y_i)`, i.e. the choice of
    `m ∈ X^S`;
  * `half` gives nature's `h'`;
  * so the K rounds are `ListWin K` on lists (`QWin` quantifies `∀` over the outcomes of
    `half`, `∃` over the writes).
* **L3d (lists vs machine).**
  * `ListWin k x y` implies `x` and `y` are valid (induction; leaves check validity), so every
    midpoint is `encC d` for a configuration `d` (tape outside `[0, S)` copied from `c₀`).
  * `Chk (encC c) (encC c') ↔ (c = c' ∨ N.Step c c') ∧ heads < S`, for configurations that
    agree with `c₀` outside `[0, S)`.
  * Hence `ListWin K (encC c₀) (encC c) ↔ SavWin N S K c₀ c` (via `savWin_iff`: both are
    `∃ n ≤ 2^K` runs within space `S`; `tape_of_reachesSpace` keeps the outside fixed).
  * Then `expspace_savWin` gives `L w ↔ QWin …`.

## 6. Remaining proof obligations

**L3 (queue game → Savitch game).** **Done** (`FondHtn/AcycHard/SavGame.lean`, `SavChk.lean`,
`SavProg.lean`): `qi_prog_iff`. Deviations from §4: the check automaton has states
`start/eqp/eqd/pre/pl q/pr q/dn` (equality branch, before the head, pending left/right move,
done) with correctness `acc_iff`/`acc_zip_iff` (accepted lists encode equal or successive
configurations; validity by counting markers); plain actions delete only the states of their
mode (`toRd` the `inp` states, `half`/`halfChk` the two `rd` states), so no shape invariant is
needed; `prog S K` has `K + 1` rounds.

**L1 design (in progress).** Generic *hierarchy* module: every compound name has one body,
either a sequence (seq-kind) or a set (set-kind, unordered); seq bodies contain only primitives
and seq-kind compounds; a rank makes the hierarchy acyclic. Invariant on partially decomposed
networks: a control chain and a multiset of pool chains of *items* (primitive or seq-kind
compound tasks), plus singleton pool chains of set-kind compounds; the expansion of the items
is invariant under decomposition. Consequences: every achievable primitive network is
`IsChains` with the expanded label lists (FM), and `MPAndOr tn s ↔ CWin (expansions) s` (MP).
Then a CWin renaming lemma (facts and action names as numbers) connects the described problem
to `X.cwin_iff_qi`.

**L1 status.** Done: `FondHtn/AcycHard/Hier.lean` (chains `UC`, `step_seq`, `step_set`),
`HierInv.lean` (`HSpec`, expansions `exI`/`exMI`/`exC`, `HInv`, `HInv.step`, `HInv.isChains`,
`exists_primitive`), `HierGame.lean` (`strongOD_iff_hier`, `mpAndOr_iff_hier`).

**Remaining plan for the instance.**
1. Transfer lemma: `CWin` with control `u ++ refill^R` (`u` refill-free) is invariant under an
   injective fact encoding and action naming, provided the encoded actions are the images
   except `refill`, which only has to make all remaining pool actions applicable (the abstract
   `refill` adds `Set.univ`, which a finite description cannot).
2. Description: facts `Tok Gate (Fct (AS Q) (Sym Q Γ))` coded as numbers; actions: `opn/cls g`,
   plain `toRd/half/halfChk/acc`, `refill` (adds the codes of all needed facts), pool `init τ`,
   `tick`, `res`, `fin τ`, `opt o` for the (finitely many) options of `Sav.Δ`.
3. Hierarchy: control = `preC ++ sweepC ++ [toRd] ++ (sweepC ++ [half])^K ++ sweepC ++ [halfChk]
   ++ sweepC ++ [acc] ++ refill^R` with `sweepC = stepC^S`, `stepC = (W T)^S (W R)^S W F W I W U`,
   powers by binary doubling (seq-kind); pool root (set-kind) = `S` blank cells + `n` fresh cells
   per symbol + `n` copies per option, multiplicities by set-kind doubling.
4. `HInv` of `tn_I` (two unordered roots), `Fit`, method existence, validity, ACYC (rank),
   PT, final theorems (FM via `strongOD_iff_hier`, MP via `mpAndOr_iff_hier`).
* The NFA `Chk` is the only machine-specific part.
* `X`, `Q`, `Γ` are finite and fixed (`Fin k`, `Space.TapeSym`); only the `In` states depend
  on `w`.

**L1a (networks of chains).** **Done**: `beliefSolvable_iff_cwin`, `cwin_sum_iff`, and the
assembled `beliefSolvable_iff_qi`.

**L1b (single-method collapse).** If every compound name has at most one method and the
problem is acyclic:
* `MPAndOr tn s → ∀ tn' primitive, tn →* tn' → BeliefSolvable tn' s`;
* conversely `BeliefSolvable` of a full decomposition `→ MPAndOr` (decompose first, then
  `MPAndOr.prim`; this direction holds without the single-method hypothesis).

The first needs:
* decomposition commutes with progression: if `t` is primitive and unconstrained in `tn`, and
  `tn →* tn'`, then `tn.progress t →* tn'.progress t`;
* confluence up to isomorphism of the unique full decomposition;
* isomorphism invariance of `BeliefSolvable` (as `MPAndOrH.iff_of_isoVia`).

With L1b, target (1) follows from target (2) on these instances, and the fair reading
follows by `planExMPFair_eq_strong`.

*Alternative to L1b that avoids isomorphisms.* Generalise `IsChains` to partially decomposed
networks:
* a chain may contain compound tasks, and its *expansion* replaces each compound task by its
  (unique, statically known) label list;
* prove `MPAndOr tn s ↔ CWin (expansions)` directly, by induction:
  * a decomposition step does not change the expansions;
  * executing a head primitive task removes the first label;
  * a compound head can always be expanded first, so the "∃ head" of `CWin` is matched.

The same generalised invariant also gives L1c for FM: every achievable primitive network
satisfies `IsChains` with the prescribed label lists. This is the recommended route, because
`IsChains` speaks about the concrete ids and needs no isomorphism.

**L1c (the hierarchy).** Compound names, all with a single method:

| name | method |
|---|---|
| `Dbl_j(x)` | `[Dbl_{j-1}(x), Dbl_{j-1}(x)]`, ordered or unordered according to `x` |

* **Control.** A totally ordered chain of blocks `preW(tri S)` (`tri S` written in binary:
  ordered doublings of the 4-task block), then the input sweep, then `K` rounds (binary `K`;
  round = `Step^S · half`, `Step` = `T^S R^S F I U` with `T^S` an ordered doubling), then the
  check sweep, then `acc`, then `refill^R`.
* **Pools.**
  * `S` blank cells: an *unordered* doubling of the chain `(tick res)^S fin b`, itself an
    ordered doubling.
  * `N` fresh cells per symbol: unordered doubling.
  * `N` options per type.
* All counts are numbers with polynomially many bits, so the descriptions are polynomial.
* Acyclic: the index `j` decreases.
* Proof obligation, in the form needed by `beliefSolvable_iff_qi`: **every** primitive `tn`
  with `tnI →* tn` satisfies `IsChains tn ctl pool ℓ` with
  `ctl.map ℓ = (control).map inl` and `pool.map (map ℓ) = (cells + supply).map (map inr)`.
  No isomorphism is needed. By induction on `j`, `Dbl_j` decomposes to `2^j` copies; the library's `HardMP`
  clocks do this for totally ordered networks only, so an unordered (parallel) variant is
  needed.

**L1d (PT layer).** The description `w ↦ FProbDesc` is polynomial-time computable, as in
`FondHtn/HardMP/PT.lean`, with validity and `ACYC` membership of the described problem.

Assembly of `Cx.Hard Cx.EXPSPACE (PlanExFM .strongOD FClass.ACYC)`:
1. `expspace_savWin` gives the language as a Savitch game;
2. L1d gives the polynomial-time description;
3. `strongOD_iff_beliefSolvable` turns solvability into belief solvability;
4. L1c gives the unique full decomposition, which is `IsChains` of the right shape;
5. `beliefSolvable_iff_qi` (done) reduces to the queue game;
6. L3 connects the queue game to the Savitch game.

MP strong and fair follow by L1b and `planExMPFair_eq_strong`.

The initial state of the problem is `idle {st (In 0)}`, i.e. the data fact `st (In 0)` only.

## 7. Notes on alternatives that were rejected

* **Warm-up with fillers.** Fillers are pooled free ticks used in a warm-up whose step `j` has
  `j` live cells. This works by global counting, but the deviation analysis is harder than
  the pre-warm staggering, and it needs a gating fact `warm`.
* **Warm-up with varying tick counts.** `j` windows in step `j` would need a staircase chain
  `Σ_j T^j`. A polynomial acyclic hierarchy cannot generate it: the extension sets would be
  exponentially many names.
* **Choice gadgets with disposal.** "Exactly one of k applicable tasks, dispose of the others"
  is unnecessary. Pooled options plus final trash suffice, because pool tasks of the same name
  are interchangeable.
* **Universal challenge of a committed tableau** (`notes_cb22_thm2.md` §2). Under full
  observability the player sees the challenge before writing the challenged cells. Only
  memory with a *fixed delay* (the FIFO) makes the past readable without a challenge.
* **Direct ATM simulation.** It needs a head counter, transition gadgets and an AEXPTIME
  source. The Savitch game needs none of these, because the head is a marker in the cell
  symbols.
