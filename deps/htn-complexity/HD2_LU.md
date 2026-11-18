# `PLANEX(H₂ ∩ L)`: decidability of two-hole-digging, loop-unrolling problems

Status file, branch `two-hole-digging`, started 2026-10-29.

## 1. The question

Dekker & Behnke, *Barely Decidable Fragments of Planning*, Sect. 6: `H₂` (at most two compound
tasks in `t₀`, at most one per method) is undecidable (Höller, Lin, Erol, Bercher, IPC 2023); is
`PLANEX(H₂ ∩ L)` decidable?  `L` (loop-unrolling): `|C| ≤ 1` and `|M| ≤ 2`.

Lean (`htn-planning`):

* `HTN.Problem.IsHD2`, `HTN.Problem.IsLU`, `HTN.Classes.HD2_LU_HTN` (`Classes/HD2.lean`,
  `Classes/LU.lean`);
* `HTN.Examples.Classes.HD1_LU_HTN_ssubset_HD2_LU_HTN` (`Core/HD2Examples.lean`).

## 2. Shape of the problem

Let `c` be the compound task name.  The degenerate cases are:

* `t₀` has no compound task: a single primitive network;
* `t₀` has one compound task: `H₁ ∩ L`, `ACKERMANN`-complete (Thm. 9);
* no primitive method: unsolvable (if `t₀` has a compound task); only primitive methods: finitely
  many primitive networks.

**Core shape.** `t₀` contains two compound tasks `c₁, c₂`.  The methods are `cont = (c, t)`, with
exactly one compound task `h`, and a primitive method `stop = (c, S)`.  Decompositions of different
tasks commute, so the reachable primitive networks are exactly `N(n₁, n₂)`: hole `i` is unrolled
`n_i` times by `cont` and closed by `stop`.

**Structure of `N(n₁, n₂)`.** Split the primitive tasks of `cont` by their relation to `h`:
`B = {t ≺ h}`, `A = {h ≺ t}`, `U = {t ∥ h}` (by transitivity a `U`-task has predecessors only in
`B ∪ U` and successors only in `A ∪ U`).  Each hole consists of levels `1 … n` (copies of `B ∪ U ∪
A`) and a bottom copy `S`.  For `x` in level `j` and `y` deeper (or in `S`): `x ≺ y` iff `x ∈ B`,
`y ≺ x` iff `x ∈ A`, otherwise unordered.  So along a hole

    B₁ ≺ B₂ ≺ … ≺ Bₙ ≺ S ≺ Aₙ ≺ … ≺ A₁,

while `U_k` *floats*: it lies after `B_{k−1}` (and its predecessors in `B_k ∪ U_k`) and before
`A_{k−1}` (and its successors in `A_k ∪ U_k`).  The two holes inherit the relations of `c₁` and `c₂`
in `t₀`.

## 3. Decidable sub-cases

1. **`c₁` and `c₂` ordered in `t₀`** (say `c₁ ≺ c₂`): all of hole 1 precedes all of hole 2.  Guess
   the state between the two holes and which free tasks of `t₀` run in which part; each part is an
   `H₁ ∩ L` reachability question with a fixed final state (problem (2) in the proof of Prop. 7).
   Decidable, in `ACKERMANN`.
2. **`Π ∈ I ∪ F`.**  Prop. 7 needs no hole bound for `I ∪ F`, and `C ∩ H₁ ∩ L ∩ B ⊆ H₂ ∩ L ∩ (I ∪
   F)`.  By Thm. 9, `PLANEX(H₂ ∩ L ∩ (I ∪ F))` is `ACKERMANN`-complete.  This covers `B = ∅` and
   `A = ∅` (when `t₀` complies as well).
3. **`U = ∅`.**  A hole yields the words `Lin(B)ⁿ Lin(S) Lin(A)ⁿ`.  The shuffle of two of them,
   with the constraints of `t₀` and the finite state space, is accepted by a finite automaton with
   two counters, each making one reversal.  Emptiness of reversal-bounded counter machines is
   decidable (Ibarra 1978).  Decidable; the complexity has not been worked out.

**Open core:** `c₁ ∥ c₂`, `U ≠ ∅`, and `Π ∉ I ∪ F`.

## 4. Lemma 6 (and with it Prop. 7) fails for `H₂ ∩ L`

The repository formalises the `H₁` procedure in `HtnComplexity/HDDecide/`:

* the bidirectional search on pieces `HTN.HD.HStep`;
* `HTN.HD.solvable_of_piecesSolvable` (soundness, no hypothesis);
* `HTN.HD.piecesSolvable_of_solvable` (completeness = Lemma 6; needs `MethodsHD1`, `IsHD1`);
* `HTN.HD.piecesSolvable_iff_reach` (Petri net, no hypothesis);
* decidability of Petri net reachability (`HTN.Petri.petriReachDecidable`).

So **completeness for `H₂ ∩ L` would have given decidability almost for free.  It is false.**

**Formal result** (`HtnComplexity/HDDecide/HD2LUCex.lean`):

* `HTN.HD.Cex.exists_hd2LU_solvable_not_piecesSolvable`: there are a description `d` and an
  instance `q` with `MethodsHD1 d`, `IsHD2 q`, `(problem d q).IsLU`, `Solvable d q` and
  `¬ PiecesSolvable d q`;
* `HTN.HD.Cex.not_solvable_iff_reach`: the Petri net of Prop. 7 (`hdNet`) does not characterise
  solvability on `2-HD-HTN ∩ L`.

Both use only the standard axioms (no `native_decide`).  Solvability is certified by an explicit
13-step path of the progression search on descriptions (`HTN.Syn.solvable_of_pReach`), which the
kernel checks with `decide`.

**The instance.**

* `cont = {b ≺ h ≺ a}` and `stop = {t}`, so `B = {b}`, `A = {a}` and `U = ∅`.
* `t₀ = {c₁, c₂} ∪ {p₁ ≺ p₂ ≺ p₃}`; the chain is unordered with `c₁` and `c₂`, so `t₀` is
  symmetric in the two holes.
* The chain splits a plan into phases `0 | 1 | 2 | 3`.  Fluents allow `b` in phases `0, 1`, `a` in
  `2, 3` and `t` in `0, 3`.  `p₂` needs a `b` in phase `1` and `p₃` needs an `a` in phase `2`.
* Solution: `b t p₁ b p₂ a p₃ t a`.  One hole runs `b ≺ t ≺ a` in phases `0, 0, 2`, the other in
  phases `1, 3, 3`, so the two holes cross.

**Why the search on pieces fails.**  In a `cont` piece `b ≺ h ≺ a`, so the search can only
*progress* `b` and only *regress* `a`, and it decomposes `h` only once both are gone.  Let `i` be
the forward phase and `j` the backward phase (`i ≤ j`; `i` grows, `j` shrinks).

* `p₃` cannot be progressed, since no `a` is ever progressed.  So some `a` is regressed in phase
  `2` while its hole is present.  Some hole is closed (decomposed by `stop`) afterwards, when
  `j ≤ 2`.  Its `t` must run in phase `0`, so that closing happens with `i = 0`.
* `p₂` needs some `b` progressed in phase `1` while its hole is present.  Some hole is closed
  afterwards, when `i ≥ 1`.  Its `t` must run in phase `3`, so that closing happens with `j = 3`.
* The two closings are incompatible, whichever comes first.

The Lean proof is an invariant of `HStep`: the ghost phases `i`, `j`, the four events as ghost
propositions, the number of compound tasks, and a monotone dead-end predicate `Bad`.
`scripts/hd2lu_pieces_cex.py` confirms the same by brute force (with a control).

**Consequences.**

* Prop. 7's Petri net does not decide `2-HD-HTN ∩ L`; a decision procedure needs something else.
* **Correction to the first version of this file:** floating tasks are *not* needed to break
  Lemma 6.  The instance has `U = ∅`, a sub-case that *is* decidable by §3.3 (reversal-bounded
  counters).  So the failure of Lemma 6 says nothing about the open core.  What the instance does
  show is that `H₂ ∩ L` can force the windows of its two holes to cross, even with a symmetric
  `t₀`.  The first version used a larger instance with a floating `u` and phase sub-divisions;
  that `u` is unnecessary.

## 5. Toward undecidability

**One hole can store a word over a finite alphabet** (a 1-turn stack).  Give each level `U = {u_α,
u_β}` with `u_σ ≺ a`, and use flags so that exactly one `U`-task runs per descent step and exactly
one per ascent step.  Backward induction over the ascent shows that every descent step executes a
task of its own level:

* the deepest level must keep exactly one `u`, since its ascent step pops only one;
* the same then holds for the level above, and so on.

So the ascent step of level `k` pops exactly the task that level `k` kept.  On its own this stays
inside `H₁` (bidirectional search absorbs one stack).

**Two distinguishable 1-turn stacks** with all pushes before all pops give PCP, i.e.
undecidability: the linear grammars `S → u_i S i | #` and `S → v_i S i | #`.  This is essentially
Höller et al.'s argument restricted to linear grammars.

**The obstacle is anonymity.**  In `L` both holes unroll the same method.

* *Steps are anonymous*: both holes execute the same `B`- and `A`-tasks.  An unverified idea: keep
  the holes at different positions of a cycle `b⁰ ≺ b¹ ≺ …` inside `B`, so that the action name
  determines the hole.  Tracking identities then needs conditional effects, which floating helper
  tasks with trashing (as in Prop. 8) might emulate.
* *Pending `U`-tasks are exchangeable*: while both are enabled, a step may execute the other hole's
  copy.  Example: `X` means to push `α` (runs its `u_β`) and `Y` means to push `β` (runs its
  `u_α`).  If `X`'s step runs `Y`'s `u_β` and `Y`'s step runs `X`'s `u_α`, the counts and
  deadlines are unchanged but the contents are swapped.  A floating task cannot have a `B`-successor
  (that would make it a `B`-task), so its window always spans the whole subtree below it.  The
  naive PCP encoding therefore fails.
* *Phases* (finitely many, via `t₀` tasks as in §4) separate the holes only boundedly often.  The
  sequential pattern "push `X`; push `Y`; pop `X`; pop `Y`" that §4 forces composes finite-state
  transductions, which is decidable.  PCP needs unboundedly many correlated concurrent pushes.

### 5.1 When can two holes exchange stored symbols? (hand analysis, 2026-10-29)

Setting: the stack gadget above.  Each level `ℓ` has tokens `u_α, u_β` with `b ≺ u ≺ a`, so a
token of `ℓ` can run anywhere in the window `W_ℓ = [b_ℓ, a_ℓ]`.  Each descent step executes
exactly one token (`desc_ℓ`) and each ascent step exactly one (`pop_ℓ`).  Assume steps are
*atomic* (the protocol lets no other task run inside a step), so `desc_ℓ ≈ b_ℓ` and
`pop_ℓ ≈ a_ℓ`.  Attributing token executions to levels is a matching problem, one label at a
time: every token is matched to one execution inside its window.

* **One hole: no exchange.**  The windows of one hole are nested.  `W_ℓ` contains exactly the
  `2(n−ℓ+1)` executions of levels `≥ ℓ`, which is exactly the number of their tokens.  By induction
  from the bottom, `desc_ℓ` and `pop_ℓ` must serve level `ℓ`: the attribution is forced.
* **Two holes: exchange iff the windows cross.**  Take `ℓ` in one hole and `m` in the other, with
  `ℓ` storing `β` (`desc_ℓ = α`) and `m` storing `α` (`desc_m = β`).
  * The cheat: `pop_ℓ` uses `m`'s `α`-token and `desc_m` uses `ℓ`'s `β`-token.  This needs
    `a_ℓ ∈ W_m` and `b_m ∈ W_ℓ`, i.e. `b_ℓ < b_m < a_ℓ < a_m`: the windows cross.
  * The result: `ℓ` pops `α` and `m` pops `β`, so **the two levels have swapped their stored
    symbols**, with all counts and deadlines respected.
  * Nested or disjoint windows admit no such matching.
* **Lockstep collapses to one stack.**  In the natural PCP pattern the descent is `X₁ Y₁ X₂ Y₂ …`
  and the ascent `…X₂ Y₂ X₁ Y₁`.  There `X_k` crosses exactly `Y_k`, and `X_{k+1} ⊂ Y_k`,
  `Y_{k+1} ⊂ X_k` are nested.  Exchanges happen only inside the pairs `(X_k, Y_k)`.  The two
  stacks therefore behave like **one stack of unordered pairs**: pushdown power, decidable.

**Consequence for undecidability encodings.**  Concurrent pushes need crossing windows, and
crossing windows allow exchanges.  So a PCP-style encoding needs a non-lockstep crossing pattern,
in which one level crosses several levels of the other hole, and its correctness has to survive
the exchanges along all crossing pairs.  Plausibly such patterns allow *more* exchanges, not
fewer; this would explain why swap-robust structures have been so hard to find.

**Speculation (superseded by §6).**  The first version of this paragraph called pushdown-VASS
reachability open.  That is outdated: it is decidable (§6).

## 6. Comparison with pushdown VASS (2026-10-29)

### 6.1 Literature (checked 2026-10-29)

* **PVASS reachability is decidable** in full generality: Guttenberg, Keskin, Meyer, *PVASS
  Reachability Is Decidable*, LICS 2026, LIPIcs 380, 53:1–53:25 (arXiv 2504.05015).  The
  procedure is Hyper-Ackermann, conjectured optimal.  Before it: one-dimensional PVASS by
  Bizière and Czerwiński (arXiv 2411.02386, preprint); coverability in dimension one by Leroux,
  Sutre, Totzke (2015).
* **VASS with nested zero tests** (a test of counter `j` also tests every counter `i ≤ j`):
  decidable (Reinhardt; Bonnet), Ackermannian upper bound (Guttenberg, Czerwiński, Lasota, arXiv
  2502.07660).  Atig and Ganty reduce reachability of VASS controlled by *finite-index grammars*
  to it.
* **Consequence for us.**  A reduction `PLANEX(H₂ ∩ L) ≤ PVASS reachability` would settle the
  question positively, citing a peer-reviewed theorem and no hypothesis.  The upper bound is the
  direction that matters.

### 6.2 What the structure of `L` gives

* **Pending blocks are counters.**  Take a forward progression search that decomposes a hole only
  when the next task lies below it.  The `A`-blocks of the open levels above the current level are
  untouched until the hole is closed, and in `L` they are copies of the same block.  So per hole
  they form a counter, not a stack (backward search: the same for `B`-blocks).  With `U = ∅`
  nothing else is unbounded, which re-proves §3.3 (finite control and two counters).
* **The `U`-pieces carry position.**  A `U`-task of level `ℓ` can only run after `B_{ℓ−1}` and
  its in-level `B`-predecessors, and must finish before `A_{ℓ−1}` and its in-level
  `A`-successors.  Two pieces in the same state but created at different levels are not
  interchangeable.  Moving a piece to a deeper level can violate its predecessors; Hall's
  condition then forces the honest last-in-first-out assignment (this is the stack gadget of §5).
  Worse, pieces of buried levels keep changing while buried, since any open level's `U`-tasks may
  run at any time.  A forward-only search therefore needs *a stack whose buried cells can be
  updated* (monotonically), one per hole.  That is not a pushdown.
* **One hole.**  Dekker and Behnke's bidirectional search removes this stack: processed from both
  ends, a hole is a set of pieces, i.e. a VASS (Lemma 6).
* **Two holes.**  §4 shows that bidirectional search with isolated decompositions is incomplete.
  Allowing a hole to be decomposed early, while some of its `B`- or `A`-tasks are still
  unprocessed, makes the pending blocks of that hole a run of identical blocks — again a counter.
  The `U`-pieces below the pending run are then *locked* (for regression, or for progression),
  and they are released from the shallow end in creation order, i.e. **first in, first out**.
  Choosing the released piece from counts is unsound for the same positional reason as above.
  This queue is the precise obstacle to a VASS or PVASS simulation along these lines.

### 6.3 Lower bound: can `H₂ ∩ L` simulate PVASS?

Unlikely by a direct simulation.  Each hole is a *one-turn* storage: levels are opened during its
descent and closed during its ascent.  Finitely many holes give boundedly many turns, while a
PVASS stack turns unboundedly often; Petri tokens do not obviously make up for this.  The known
lower bound stays `ACKERMANN` (from `H₁ ∩ L`).

### 6.4 Upper bound: the open sub-questions

1. **FIFO release.**  Can the locked `U`-pieces of §6.2 be canonicalised so that their release
   order no longer matters?  For instance, show that a solution exists in which every locked piece
   is either untouched or complete when released.  If so, early-decomposition bidirectional
   search is a VASS and `PLANEX(H₂ ∩ L) ∈ ACKERMANN`.
2. **One stack for the crossing.**  Otherwise: keep one hole as pieces and put only the other
   hole's crossing part on a PVASS stack.  The difficulty is that the crossing part is touched at
   both ends.
3. **Exchange closure** (§5.1).  The set of valid observable runs contains both the honest
   two-stack runs (e.g. the FIFO pattern `push X, push Y, pop X, pop Y` with own contents) and the
   merged one-stack runs (the exchanged reading of the same pattern).  So exchange alone does not
   collapse two holes to one stack; it widens the set of runs.  A reduction must keep the honest
   runs.

### 6.5 Test of §6.4.1: counting the locked pieces is unsound (2026-10-29)

Tools are in `scripts/hd2lu_search/`:

* `abs_search.py`: an exact solver over `N(n₁, n₂)`, and an *early-decomposition* bidirectional
  search.  Such a search may decompose a hole before its `h` is isolated, keeping that level's
  `B`- or `A`-block pending.  Pending blocks are counted.  The locked `U`-pieces of the pending
  run are kept as a multiset, and the piece released at the shallow end or taken at the deep end
  is chosen freely (the counting abstraction).
* `pos_search.py`: the same search with the locked pieces kept *in order*.  The shallow end
  releases the oldest piece and the deep end takes the newest, so this search is exact.
* `hand_instances.py`: the two instances below.

Findings:

* **The early-decomposition search handles crossing.**  It finds the formalised counterexample of
  §4 at the right depths, where the search on pieces fails.
* **Counting is unsound, already for one hole (`1-HD ∩ L`).**  The instance:
  * `cont = b ≺ u ≺ a` (`u` floats w.r.t. `h`), `stop = ∅`;
  * phases `0a 0b 1a 1b 1c 1d 2`, given by a chain `p₁ ≺ … ≺ p₆`;
  * at least two `b`s in phase 1 (sub-phases `1a`, `1b`), at least two `a`s in phase 1 (`1c`,
    `1d`), and at most one `u` in phase 1 (in `1b`).
* **No plan at any depth.**  In one hole, the levels with `b` in phase 1 and those with `a` in
  phase 1 are both deep suffixes of the level chain.  So at least two levels have their whole
  window inside phase 1, and each needs a `u` there; only one fits.  The exact solver agrees for
  depths `≤ 5`.
* **The fake.**  The counting search finds a "plan" of depth 4: `b u | b u | b | b u | a | a | u a a`.
  * When the deep end moves up from level 4, it takes the *complete* locked piece (in reality
    level 2's) for level 3.
  * Level 3's `u` is still pending in reality and cannot run in phase 1.
  * The positional search correctly finds nothing.
* **Consequence for §6.4.1.**  The fake's locked pieces are untouched or complete, which is the
  canonical form proposed there.  So that canonical form does not help: what matters is *where*
  the complete and untouched pieces sit, not only how many there are.  A VASS abstraction along
  these lines is not available; the order must be kept.
* **Pending runs cannot simply be bounded.**  Phases as in §4 can force one hole's whole descent
  into a pending run, and the depth can be forced to be large.  We have no computable bound on the
  needed run length, and expect none.

**What is left for a PVASS reduction.**  The ordered locked pieces are:

* released oldest-first by the backward search, and taken newest-first at the deep end by the
  forward search: a *deque*;
* updated anywhere, since `U`-tasks of buried pieces can be progressed.

A forward-only treatment of a hole removes the releases (a stack) but keeps the buried updates.
For a single anchored `U`-task, an earliest-deadline-first choice makes every update hit the
topmost *incomplete* piece, which can be buried under complete ones.  Representing that on a
PVASS stack needs an *exact* transfer of a counter onto the stack, and a PVASS cannot test a
counter for zero:

* inexact transfers are sound when they make a piece's deadline earlier (an early consumption);
* they are unsound when a new level is pushed, because complete levels then move above it.

For one hole, Dekker and Behnke's isolation (Lemma 6) avoids all of this.  The open question is
whether two holes admit a search that isolates enough to need at most one stack.

### 6.6 One hole can always be isolated (formalised 2026-10-30)

**Statement (formal).**  `HTN.HD.isolation` (`HtnComplexity/HDDecide/Isolation.lean`): assume
every method has at most one compound task and the described problem is solvable.  For every task
`x₀` of the initial network there is a network `tn₁` with these properties:

* `tn₁` is reachable from the initial network;
* `x₀` is still in `tn₁` with its label, and it is `tn₁`'s only compound task;
* the instance `q₁` that describes `tn₁` (same initial state and goal) is one-hole-digging and is
  **solved by the search on pieces**, i.e. `x₀`'s hole needs only decompositions of isolated
  tasks.

The semantic core is `HTN.DecomposesToN.unroll_except` and `HTN.Problem.exists_unroll_except`
(`HtnPlanning/Core/Unroll.lean`).  Decompositions of different tasks commute (`pull_out`), so
every compound task other than `x₀` can be decomposed first, down to primitive tasks.  The pieces
part is the existing Lemma 6 (`piecesSolvable_of_solvable`), applied to a description of `tn₁`
(`HTN.HD.descOf`).  Standard axioms only.  No assumption on the number of holes is needed.

**How weak this is.**  An earlier version of this section stated it as "Lemma 6'": with the
meeting point in `X`'s bottom region, `X` is decomposed only when isolated and `Y` lazily.  That
is the same statement, because the lazy hole may as well be unrolled eagerly before the search
starts.  So it does not localise the difficulty in a usable way.  The other hole is not tracked
at all; it becomes a primitive network of unbounded size, with all its ordering.  The earlier
"consequences" (a queue part and a stack part of `Y`) describe one particular lazy schedule and
are not needed for anything that follows.

### 6.6a Searches used for testing

`scripts/hd2lu_search/iso_search.py` restricts the positional search of §6.5: hole `X` may only
decompose isolated tasks, hole `Y` freely.  It agrees with the exact solver on the counterexample
of §4 and on the random instances tried.

### 6.7 Several cut points (idea, 2026-10-29)

Split the plan at finitely many cut points and run a bidirectional search in each segment, with
only *isolated* decompositions.

* **It is still a VASS.**  Each frontier has a finite state, and each piece records which
  segments processed which of its tasks (finite).  This record is needed to keep the order
  consistent across segments.
* **It handles the §4 counterexample.**  One cut in each hole's bottom region makes both holes
  isolated.
* **For general `H₂` no bound on the number of cuts can exist,** since a bound would make `H₂`
  decidable.  Each lead/lag inversion between the two holes' descents can force a further cut:
  * the forward frontier of a segment waits for `X`'s next level, which needs an `A`-task
    regressed in a later segment;
  * that regression needs a `Y` level whose `B`-task lies behind the waiting point.

**Conjecture (bounded cuts for `L`).**  For `H₂ ∩ L` a number of cuts computable from the instance
suffices: blocks of the two holes are interchangeable in `L`, so inversions can be undone by
reassigning blocks, as long as the `U`-pieces and the bottoms allow it (exchanges, §5.1).  If this
holds, `PLANEX(H₂ ∩ L)` is decidable via plain VASS reachability (`ACKERMANN`), with no PVASS
needed.

### 6.8 Multi-cut search: first experiment (2026-10-30)

`scripts/hd2lu_search/cut_search.py` implements the search of §6.7.

* **How it works.**  `K` cuts split the plan into `K+1` segments, each searched from both ends.
  States at the cuts are guessed.  Processed tasks carry a class (`F_0 < B_0 < F_1 < …`), and a
  child piece inherits class bounds from its parent's `B`- and `A`-tasks.
* **On the counterexample of §4** (`cut_test.py`): `K = 0` (the search on pieces) finds nothing,
  in line with `HD2LUCex.lean`; `K = 1` finds exactly the solvable depths.
* **Too slow for broad experiments.**  `K = 1` takes about ten minutes on this tiny instance,
  because it explores all interleavings of four frontiers.

**What forces a cut** (hand analysis, not checked).  By the argument of §4, a successful run of
the search on pieces has the following property.  Take decompositions `D` (creating level `ℓ+1`
of hole `H`) and `D'` (creating level `j+1` of hole `G`), with `D` before `D'`.  Then `G`'s tasks
at depth `≥ j+1` lie inside the window of `H`'s level `ℓ`.  A cut is needed when, for some pair,
neither containment holds.  Typically:

* `H`'s level `ℓ+1` starts before `G`'s level `j` (the `B`-task enabling it comes later);
* yet `H`'s level `ℓ` ends before `G`'s level `j` ends.

Call this an *inversion*.

* **A single cut between all descents and all ascents does not remove inversions.**  The forward
  frontier of the descent segment waits for `H`'s level `ℓ+1`.  The backward frontier of the
  ascent segment must first pass `G`'s level `j`, whose creation needs a `B`-task the waiting
  forward frontier has not reached.
* **A cut separating the two starts, or the two ends, of an inverted pair removes it.**
* **So the number of cuts needed is governed by how many inversions cannot be removed by
  reassigning blocks between the holes.**  In general `H₂`, inversions are pinned by the methods
  and can be unbounded (PCP).  In `L`, only the `U`-pieces and the bottoms pin them.

**Next tool.**  For a fixed plan and assignment of its tasks to holes and levels, the frontiers'
orders are fixed, and decompositions only ever enable further moves.  So a greedy simulation
decides whether a given set of cuts works, and cut positions can be enumerated.  With the exact
solver enumerating plans of small depth, this gives the minimal number of cuts per instance
cheaply.

### 6.9 What the cuts measure, and where the encodings break (2026-10-30, hand analysis)

**Lemma 6 already fails for two sequential holes.**  Take the plan `b s u a | b s u a` (two holes
of depth 1, one after the other, `cont = b ≺ u ≺ a`).  If the action state forces this order, the
search on pieces deadlocks:

* the forward frontier waits for the first hole to be decomposed, which needs its `a`;
* the backward frontier waits for the second hole, which needs its `b`.

One cut between the holes fixes it.  So the formalised counterexample of §4 is a refined version
of a very simple phenomenon.  (`scripts/hd2lu_search/forcing.py` computes a lower bound on the
cuts needed by any interpretation of an event sequence.)

**Decidability is equivalent to a computable bound on cuts.**  Assume the K-cut isolated search
of §6.7 is sound for every fixed K (believed, not proven).  It is complete for each solution with
K = plan length.  Hence:

* if the minimal number of cuts of some solution is bounded by a computable function of the
  instance, the K-cut VASS decides the problem;
* conversely, if the problem is decidable, the minimal number of cuts is computable: decide
  "solvable with ≤ K cuts" for K = 0, 1, …

So cut experiments can only produce evidence, not the answer.

**Cuts are needed at inversions.**  By §6.8, in a fixed plan a cut is needed where two consecutive
levels of one hole both start before and end before two consecutive levels of the other (the
pattern `2143` in the pairing of descents with ascents).  A zig-zag of `k` such inversions needs
`k` cuts in disjoint intervals.  Small random plans rarely need more than one cut (`cuts_needed.py`:
at most 2 cuts for up to 5 levels).  Random `u`-placements on a zig-zag skeleton did not force
two cuts (`zigzag_search.py`).  A two-block `u`-cluster design (`bbuubbssaauuaa`) provably forces
one inversion.

**Why the two-stack encodings break.**  The stack gadget stores one symbol per level.  A wrong
symbol can be popped *without violating anything* by routing it through a level `M` of the other
hole:

* `M` consumes the stored task of level `L₂` at `M`'s own step;
* `M`'s own copy of that task is consumed by the faked pop of level `L₁`.

This needs `M` to start inside `L₂` and end after `L₁` (`L₂ ⊂ L₁`): an inversion.  It is
available because every level must execute *every* task of the single method, so every level of
the other hole carries every label.

* Tags (depth mod `p` in the labels) block fakes spanning fewer than `p` levels.  The other hole
  still carries all tags, though, so a fake over `p` levels remains possible.
* A PCP encoding needs inversions of unbounded span, the overhang between the two words.  (PCP
  with bounded overhang is decidable.)  So no fixed tag scheme blocks all fakes.
* A swap-robust encoding would therefore need a mechanism other than labels to keep stored
  symbols apart.

**Status.**  Neither direction is proven.

* *For undecidability*: a gadget that forces inversions of unbounded span *and* blocks fakes across
  them.
* *For decidability*: a computable bound on the cuts.  Plausibly via a normal form: re-route
  symbols through the other hole (fakes are exactly the reinterpretations available) to shorten
  inversions.

### 6.10 Rolling cuts, plan shapes, and one stack (2026-10-30)

**Rolling cuts.**  The K-cut search fixes its cuts in advance.  A *rolling* search instead places
a cut only when a segment is stuck, inside that segment's unprocessed part (guessing the state
there), and drops a segment once its frontiers meet.  For a fixed bound W on the number of
segments open at the same time ("width") it is still a VASS: the frontier classes are renumbered
when a segment is split or dropped.  It is a restriction of the K-cut search to particular
schedules, so it is sound whenever that search is.  `scripts/hd2lu_search/width.py` computes the
least width for a fixed plan and interpretation, and a lower bound over all valid interpretations
(u's free, as in `forcing.py`).

**Plans as loops in the grid.**  Read left to right, a plan moves (depth of X, depth of Y) through
the grid: openings step up, closings step down, and each coordinate rises once and falls once.
`scripts/hd2lu_search/loops.py` builds plans from such paths.  Computed widths:

| shape | width |
|---|---|
| L-shaped bubble `a×b` (path `Xᵃ Yᵇ`, return `Yᵇ Xᵃ`), any size; any number in a row | 2 |
| band: two parallel staircases at distance `d` with `k` diagonal steps between them | 2, 3, 4 for `k = 0, 1, 2` (`d ≥ 3`) |
| triangle `bⁿ s (b a)ⁿ s aⁿ`: X down, then X up while Y goes down, then Y up | `n + 1` |

So rolling cuts handle any number of crossings in a row, but not thick crossings.

**The triangle is forced, and one stack handles it.**  With the u's placed as
`bⁿ uᵏ s (b u a)ⁿ s uⁿ⁻ᵏ aⁿ`, the interpretation is unique already by counting (all a's between
the two bottoms belong to the hole that bottoms first).  Its width lower bound is `n + 1` (computed
for `n ≤ 5`).  Under a fixed control regime such a family needs unbounded width.  But the meeting
point can be placed at the second bottom:

* X then lies entirely on the forward side and can be processed left to right with a stack;
* Y spans the meeting point and is handled in lockstep as in Lemma 6.

**Phases.**  Let X bottom first.  Then the plan splits at the two bottoms:

1. **before `s_X`:** only `B`-tasks.  Which hole each block belongs to is free, up to counts.
2. **between `s_X` and `s_Y`:** `A`-blocks of X and `B`-blocks of Y.  This attribution is forced
   when the labels of `B` and `A` differ.
3. **after `s_Y`:** only `A`-blocks.  Again free up to counts.

Take the meeting point at `s_Y` and the forward frontier's stack for the X levels that close in
phase 2.  What remains in lockstep is the X levels that close in phase 3 and all Y levels.  The
only obstacle left is a *bubble*: the order in which these open in phase 1 differs from the order
in which they close in phase 3.  Thin bubbles are harmless, sequences of bubbles cost width 2, and
thick bubbles (bands) cost unbounded width.  The triangle has no phase-3 X levels and so no
bubble.

**Bands were not forced in the simplest class.**  For `cont = b ≺ u ≺ a` (one floating task,
anchored on both sides), with both bottoms adjacent:

* random u-placements gave width ≤ 2 (6 and 8 levels, 400 each);
* hill climbing gave width ≤ 2 (6 levels);
* placements biased towards the edges of a band's own windows gave width ≤ 2 (`d = 3`, `k ≤ 2`).

Every such placement had many valid interpretations, and some interpretation was nearly
lockstep.

**Why a crossing reads back only multisets.**  This is a hand argument, a Hall-type counting.
Consider a stack gadget:

* `U = {u₁, u₂}`, each `uᵢ ≺ a`, unordered with `b` and `h`;
* pushing symbol `γ` executes `u_{3−γ}` before the level's `b`;
* popping executes `u_r` just before its `a`.

Call a set `S` of levels *closed* if no other level's execution is usable by a level of `S`.
Every level needs one `u₁` and one `u₂`, so for closed `S` the executions of `S` contain exactly
`|S|` of each type.  If `S ⊂ S'` are closed and differ in one level, that level pops what it
pushed.

* In one hole every `{levels ≥ k}` is closed, so the stack is faithful.
* For two holes, `X_{≥i} ∪ Y_{≥j}` is closed only if `X_{i−1}` and `Y_{j−1}` push before both
  windows open and pop after both deadlines.
* A chain of closed sets with single-level steps forces the windows to be laminar (nested or
  disjoint), i.e. one stack.
* Across crossing windows the steps contain several levels, and only the multiset of their
  symbols is forced.

A PCP-style encoding with two faithful stacks needs both stacks pushed together and popped
together, at different rates.  These are the crossings of phases 1 and 3, where in addition the
attribution to holes is free.  The forced transfer of phase 2 alone has a decidable information
flow: a rational relation between what X keeps and what Y receives.

**Caveat on "a stack for one hole".**  Processing a hole left to right is not a plain pushdown
automaton.  Its floating tasks may be executed while deeper levels are on top.  For floating
tasks anchored singly (no order among them), a pool of credits works:

* executions in a descent are pushed as markers;
* they are released into per-type counters when the levels above them are popped;
* each closing level takes its tasks from the counters.

This gives one stack plus counters, i.e. a PVASS.  For ordered floating tasks (chains such as
`u₁ ≺ u₂` within a level, as in the FAKE instance of §6.5), the pool must remember order.  It is
not known whether a PVASS still suffices.

**Status.**  Still open.  The working conjecture for decidability is a reduction to PVASS: one
stack for the hole parts that are entirely on one side, lockstep plus rolling cuts for the rest.
Its open points:

1. thick bubbles in phases 1/3 (bands), which the simplest class does not seem to force;
2. the pool for ordered floating tasks.

An undecidability proof would have to force bands *and* keep per-level information across them.
The closed-set argument says the latter fails at least for gadgets of the kind above.

### 6.11 Thick bubbles, the L-theorem, and one stack plus counters per hole (2026-10-30)

This section takes up the two open points of §6.10.

**1. What could force a thick bubble.**  In phases 1 and 3 the attribution of blocks to holes is
free up to counts.  Three tools could fix it.

* **The action state cannot.**  STRIPS actions are idempotent: if `x` is applicable after
  itself, `x x` and `x` lead to the same state.  So the state cannot tell two overlapping blocks
  with the same labels from one block.  With only `B`-tasks between them, the run that places the
  blocks one after the other reaches the same states.
  * A first design (`B = {p ≺ q}` with phase pattern `p p q q`, to force pairs of simultaneous
    openings) fails for this reason.
  * The state can forbid overlap, never force it.
* **Pins of the initial network** (`t ≺ c₂`, `c₁ ≺ t`, …) are finitely many.  They force an L at
  the ends, never an unbounded alternation.
* **Floating tasks** are what remains.  Each must lie in a window of a level of the right hole,
  and different attributions give different windows.

**Size matters.**  With adjacent bottoms, a pairing of `N` levels needs width ≥ 3 only from
`N = 7` on (4 of 3,432 pairings at `N = 7`, 62 of 12,870 at `N = 8`).  The 3+3 searches of the
first round could not show a thick bubble at all; only the 8-level searches below are evidence.

**Experiments at 8 levels, adjacent bottoms, starting from thick pairings.**  Floating tasks were
placed tightly inside the windows of a thick pairing.  Then the least width over *all* pairings
valid for that plan was computed exactly.

* *Unordered floating types* (`famsearch.py`).  Each type has one of four windows: after its own
  or its parent's `b`, and before its own or its parent's `a`.
  * For one unordered type, earliest-deadline-first is exact.
  * 250 placements each for `op`, `po`, `pp`, `op+po`, `oo+pp` and all four together gave least
    width 2 in every case.
  * The same holds for `oo` with 1–3 types (150 each).
* *Ordered floating types* (`ordsearch.py`, exact backtracking).  Six orders, including
  three-element orders with mixed anchors.  `u ≺ v` (both unanchored) completed 300 placements;
  the others completed between 10 and 50 placements in 40 minutes.  The least width was ≤ 2
  throughout.

These random placements never forced a thick bubble.  A targeted search does force one; see
§6.12.

**Theorem (simplest class).**  Assume:

* the bottoms are adjacent, i.e. all `B`-blocks precede both bottoms and all `A`-blocks follow
  them;
* there are no pins;
* every floating type is unordered and anchored at its level's own `b` and own `a`.

Then whenever some interpretation of a plan is valid, an L interpretation is valid.  An L is
handled with one cut.

*Proof.*  Number the openings `1…N` and the closings `1…N` in time order.  An interpretation is
given by two words `lo, lc ∈ {X, Y}^N` with the same number `p` of `X`s; the hole structure
(LIFO pairing) is then determined.  For a type, a window lies inside
`[opening N−k+1, closing m]` iff its level opens among the last `k` and closes among the first
`m`.  These intervals are the only ones that matter.  Their window count is

    φ(k, m) = min(f, g) + min(k − f, m − g),

where `f = f(k)` counts the `X`s among the last `k` openings and `g = g(m)` those among the
first `m` closings.  By Glover's condition (Hall's theorem for points and intervals), a type can
be matched iff `φ(k, m) ≤ U(k, m)` for all `k, m`, where `U(k, m)` is the number of its tasks in
that interval.  So it suffices to find `n` with `φ_n ≤ φ` pointwise, `φ_n` belonging to the L
pairing `lo = lc = Xⁿ Y^{N−n}`.  For the L pairing:

* `φ_n = 0` for `k ≤ N−n, m ≤ n`;
* `φ_n = k + m − N ≤ φ` for `k > N−n, m > n`;
* `φ_n = min(k, m − n)` on `k ≤ N−n, m > n`;
* `φ_n = min(k − N + n, m)` on `k > N−n, m ≤ n`.

Let `A(n)` say `φ ≥ min(k, m − n)` on the third region and `B(n)` say
`φ ≥ min(k − N + n, m)` on the fourth.  `A` is upward closed in `n` with `A(N)`, and `B` is
downward closed with `B(0)`.  Suppose no `n` satisfies both.  Then for some `n ≥ 1`, `A(n−1)` and
`B(n)` fail:

* `φ(k₁, m₁) < min(k₁, m₁ − n + 1)` with `k₁ ≤ N − n + 1`, `m₁ ≥ n`;
* `φ(k₂, m₂) < min(k₂ − N + n, m₂)` with `k₂ ≥ N − n + 1`, `m₂ ≤ n`.

So `k₁ ≤ k₂` and `m₂ ≤ m₁`.  Write `φ = min(k, m, f + (m − g), g + (k − f))`.  Both values are
below `min(k, m)`, so each is attained by one of the last two terms.  Each of the four
combinations is contradictory (`ȳ` counts `Y`s):

1. `f₁ + (m₁−g₁) < k₁` and `g₂ + (k₂−f₂) < m₂` give
   `ȳ_open(k₁) ≤ ȳ_open(k₂) < ȳ_close(m₂) ≤ ȳ_close(m₁) < ȳ_open(k₁)`.
2. `g₁ + (k₁−f₁) < m₁` and `f₂ + (m₂−g₂) < m₂` give
   `f(k₁) ≤ f(k₂) < g(m₂) ≤ g(m₁) < f(k₁)`.
3. `f₁ + (m₁−g₁) < m₁ − n + 1` and `f₂ + (m₂−g₂) < k₂ − N + n` give `g(m₁) ≥ n`, and
   `ȳ_open(k₂) > N − n`, i.e. `p < n`; contradiction.
4. `g₁ + (k₁−f₁) < m₁ − n + 1` and `g₂ + (k₂−f₂) < k₂ − N + n` give `ȳ_close(m₁) ≥ n`, i.e.
   `p ≤ N − n`, and `f(k₂) > N − n`; contradiction.

Hence some `n` (in fact an interval of them) works.  Since the domination is pointwise, the same
L serves every type at once. ∎

(`lshape.py dominate` confirms it for all 17,560 pairings with `N ≤ 8`.)

For the other three windows no L (and no nested shape) dominates in general.  Many pairings
already at `N = 6` are not dominated.  Yet the searches above always found *some* thin valid
interpretation.  One ordered example has no valid L but 96 valid interpretations of width 1.  So
the normal form to aim for is "no thick bubble", not "L".

**2. One hole read left to right: one stack and counters** (`pool.py`).  The parts of a hole
that lie entirely on one side of the meeting point are processed with a stack.  Their floating
tasks may run while deeper levels are on top.  The stack is never touched below its top:

* **Descent:** push a marker for every level and every floating task.
* **Closing a level:**
  * pop its marker;
  * release the floating-task markers above it into a *pool* (they are earlier than everything in
    the pool, so they are prepended);
  * also release the markers down to the parent's marker, which only types not ordered after
    their own `b` may use for this level.
* **Ascent:** floating tasks executed on the way up are appended to the pool.
* **The pool** is a multiset of *partial embeddings* `S ⊆ U`, each reserved for one future level:
  * a prepended `x` may join `S` if nothing in `S` is ordered before `x`;
  * an appended `x` may join `S` if nothing in `S` is ordered after `x`.
* **Claims:** a closing level takes a down-closed `S` containing every type ordered before an
  `A`-task.  The rest is its *leftover*, completed by appended markers before the parent closes.
  Only one leftover is pending at any time, so it fits in the finite control.

This is one stack plus counters, i.e. a PVASS component.  An exhaustive search of its
configurations agreed with the exact semantics on all 4,000 random single-hole plans tested: 10
orders on up to three floating types, mixing all anchorings; tasks were placed anywhere, so many
plans were invalid.  No proof yet.

**3. The resulting procedure** (conjectured to be complete).

1. Guess which hole `F` bottoms first, and meet at the other bottom `s_G`.
2. `F`'s levels that close between the bottoms: left to right with the stack and the pool.
   The outermost of them may leave a bounded leftover beyond `s_G`, handed to the backward
   frontier as a guess.
3. The lockstep box (`F`'s outer levels and all of `G`): pieces in lockstep as in Lemma 6.
4. Rolling cuts, each placed among the closings of phase 3, so the stack is never split.  The
   width needed is ≤ 2 under the normal form below.

This is a pushdown VASS, so reachability is decidable (Guttenberg, Keskin, Meyer, LICS 2026).

**Status.**  `PLANEX(H₂ ∩ L)` is decidable *if*:

* **(N) normal form:** every solvable instance has a solution whose lockstep box has width ≤ 2;
* **(P) pool:** the pool method is exact;
* **(S) soundness and completeness** of the combined search for such solutions.

(P) and (S) are supported by experiments; neither is proven.  §6.12 shows that (N) is false for
single plans but survives the STRIPS restriction in the cases tested.  It is open for
instances.

### 6.12 A forced thick bubble on a plan, and the STRIPS restriction (2026-10-30)

**The plan-level normal form is false.**  `forcethick.py` searches, from a thick pairing, for
placements of floating tasks on which every thin interpretation is invalid.  It works with Hall
counts (exact for unordered types).  At 7 levels it found the plan

    bbuuwbuwwzbvwwzbvzzbubwssaaauuavvavzauvwzzav

Its floating types are unordered, one per anchoring:

| type | window |
|---|---|
| `u` | own `b` to own `a` |
| `v` | own `b` to parent's `a` |
| `w` | parent's `b` to own `a` |
| `z` | parent's `b` to parent's `a` |

* **Unique interpretation.**  Up to renaming the holes and swapping the bottoms, the plan has
  exactly one valid interpretation: opening order and closing order are both `XXXYXYY`.  Its
  width is 3.  This is confirmed independently with the exact enumerator of `rich.py`
  (`width_lb = 3`, 4 valid interpretations = 1 up to symmetry).
* **All four anchorings are needed.**  Each family is, for some thin pairings, the only reason
  that pairing is invalid.
* **Larger plans.**
  * Width 3 was not forced at 8 levels (30 restarts × 500 steps; best: 2 thin pairings left).
  * Width 4 needs at least 10 levels (6 of 184,756 pairings).  It was not forced there either
    (12 restarts × 800 steps; the best placement still left 56 valid pairings of width ≤ 3).

So for plans, thick bubbles can be forced, and the procedure of §6.11 with width 2 would miss
this plan.

**But STRIPS cannot pin a plan down.**  A STRIPS state is determined, fact by fact, by the last
action that touched the fact.  The formalisation's `transition a s = (s \ del a) ∪ add a` makes
this immediate.  So the state after a sequence depends only on its *last-occurrence order*: the
image in the free right regular band, where `xx = x` and `xyx = yx`.  Applicability of the next
action depends only on that order.

* In particular the state cannot count.  A run of one action has length exactly 1 (if the
  action destroys its own precondition), or any length.
* Interleavings of identical blocks are invisible.

`rrb.py` builds the most restrictive constraint of this kind containing a given plan:

* the steps (prefix order, next action) that occur in it;
* goal: the plan's final order.

It then enumerates that constraint's valid plans (bounded depth and length) with their least
width.

| forced plan | valid plans in the closure | least widths |
|---|---|---|
| the plan above | 769 (depth ≤ 7, length ≤ 50) | 141 of width 1, 484 of width 2, 144 of width 3 |
| `bwbuwwubuwwbwbvzvzbuzbzssaazzawuavvvavuauvaz` | 130 | 2 and 3 |
| `bwbvwwzbwvbuwwbubbzvssauauauwazzzzuuzavavavv` | 18 | 1, 2 and 3 |

(`forcedmany.py` generates forced plans and runs the closure.)  A real STRIPS encoding allows
at least these plans, so every such instance also has thin solutions.

**Consequence.**  The normal form has to be stated for instances:

> **(N)** every solvable instance has a solution whose lockstep box has width ≤ 2 (or at most a
> bound computable from the instance).

The forced plans needed exact run lengths and exact interleavings, which STRIPS cannot express.
The algebraic restriction (STRIPS transition monoids are right regular bands) is the new tool for
a proof.  It is also new for the undecidability side: an encoding may only use constraints
that depend on last-occurrence orders.

### 6.13 How much width can floating tasks force? (2026-10-30)

**Unordered floating tasks: width 3, apparently never 4.**  For unordered floating types,
validity depends only on the Hall count functions of the four anchorings (§6.12).  Several
tasks of one type per level only scale a count function.  Counts are monotone: if a pairing `Q`
has counts ≤ those of `P` in every family, no placement of unordered tasks makes `P` valid and
`Q` invalid.  `domwidth.py` checks domination exhaustively.

| levels | pairings | of width > W | not dominated by width ≤ W |
|---|---|---|---|
| 8, W = 2 | 12,870 | 62 | 46 (width 3 can be forced, cf. §6.12) |
| 10, W = 3 | 184,756 | 6 | **0** |
| 11, W = 3 | 705,432 | 136 | **0** |

So on up to 11 levels, unordered floating tasks with any anchorings and multiplicities cannot
force width 4.  Each width-4 pairing at 10 levels is a band and is dominated after a single
adjacent transposition: `YX → XY` among the openings, or `XY → YX` among the closings.  This
squares off one step of the staircase.  At 11 levels, 4 of the 136 need more than one
transposition (`transpose.py`).

> **Conjecture.**  Unordered floating tasks never force width > 3 (adjacent bottoms, no pins).

**Ordered floating tasks** are not determined by counts.  Two searches look for placements
that force width `W + 1`; both filter with each type's counts and then check exactly.

* `chainforce.py` places all floating types at once.
* `chainstage2.py` adds an ordered pair `c ≺ d` to a fixed unordered placement.  More tasks can
  only remove valid pairings, so this is sound.

The exact check uses `cvalid.py`.  Unordered types are matched by earliest-deadline-first, each
component of ordered types by the C matcher `cmatch.c`.  It agreed with `rich.valid` on 2,972 +
1,101 checks.

* *7 levels, W = 2, chains alone* (25 restarts × 150 steps each).  The orders tested were
  `u ≺ v` with windows own `b` → parent `a` and parent `b` → own `a` (both orders), `u ≺ v`
  both anchored on both sides, `u ≺ v` unanchored, and a three-element chain.  At least 6 thin
  pairings always stayed valid.  Chains alone did not force width 3, which four unordered
  anchorings do.
* *10 levels, W = 3, four unordered types plus one chain* (`chainstage2.py`, 10 restarts ×
  150 steps).  Stage 1 was the best unordered placement, leaving 56 thin pairings valid.  An
  added chain reduced them:
  * to 22 (both tasks own `b` → parent `a`, or both parent `b` → parent `a`);
  * to 48 (`po ≺ op`, `po ≺ po`);
  * not at all (`oo ≺ oo`, `op ≺ po`).

  So chains add forcing power, but width 4 was not forced.

**(P) is provable: proof sketch.**  This covers one hole processed left to right with the pool
of §6.11, with single-task blocks; longer blocks only add bookkeeping.

* *Soundness.*  When level `ℓ` closes, every marker in the pool was executed after `ℓ`'s `b`
  and before its `a`.
  * Markers above `ℓ`'s stack marker were pushed after its `b`; ascent markers came later still.
  * The region between the parent's marker and `ℓ`'s may extend `ℓ`'s partial only for types
    whose window starts at the parent's `b`.
  * Leftovers are completed by markers appended after `ℓ`'s `a` and before the parent closes.

  So every claimed task lies in its window.  The in-level order holds because a prepended marker
  is earlier, and an appended one later, than all markers already in its partial, and the
  extension rules check exactly the order relations with those.
* *Completeness.*  Given a valid assignment, let the run put each marker into the partial of the
  level it is assigned to.
  * The extension rules hold, since the assignment respects the order.
  * At `ℓ`'s closing, its partial consists of its tasks executed so far.  It is down-closed and
    contains every type ordered before an `A`-task.
  * Its remaining tasks lie after its `a` and before the parent's `a`, so they are appended in
    time.

  Tasks of `ℓ` executed while deeper levels were on top sit above those levels' markers.  They
  are released, earlier than everything in the pool, when those levels close, and wait in `ℓ`'s
  partial.

**Status.**  If the width that floating tasks can force is bounded by a constant `c(cont)`,
the procedure of §6.11 with width `c(cont)` is complete, and `PLANEX(H₂ ∩ L)` is decidable
modulo (P) and (S).  The STRIPS restriction of §6.12 can only lower the width needed.

### 6.14 Why width 3 suffices for unordered floating tasks: paths, counts, descent (2026-10-30)

Setting: adjacent bottoms, no pins, unordered floating types (any anchorings and
multiplicities).  Read the openings outside-in as a lattice path `F` from `(0,0)` to
`(n_X, n_Y)`, with `X` a step right and `Y` a step up.  Read the closings from the end, also
outside-in, as a path `B` between the same points.  The lockstep case is `F = B`.

**Hall counts in path form (proved).**  Let `F(i)` be the point of `F` after `i` steps and
`B(j)` that of `B`.  The interval from the opening after `F(i)` to the closing before `B(j)`
contains the windows of

    N − |F(i) ∨ B(j)|

levels for anchoring `oo` (own `b`, own `a`); `∨` is the componentwise maximum and `|·|` the
coordinate sum.  For a parent anchor replace `F(i)` (opening side) or `B(j)` (closing side) by
the point shifted by `(1, 1)`, capped at `(n_X, n_Y)`.  This follows directly from
`min(k_X, m_X) + min(k_Y, m_Y)` with `k_X = n_X − F(i).x` and so on.  So smaller counts
(easier to satisfy) mean that `F` and `B` are farther apart.  The L pairing, `F` right then up
and `B` up then right, is as far apart as possible.

**Width in path form (checked).**  At any time the processed openings are the first `a` X- and
the first `b` Y-openings, and similarly `a', b'` for the closings.  `a` may grow only while
`a ≤ a'`, and `a'` only while `a' ≤ a`; likewise for `b`.  The open segments number

    runs(F; a, b) + runs(B; a', b') − 1,

counting the runs of unprocessed positions.  The width is the least maximum of this along a
schedule.  `widthformula.py` agrees with `width.min_width` on all pairings with 4, 6 and 8
levels.

**One move and its margins (proved).**  Take an inward corner of `F`: `F` goes up from `(x, y)`
to `(x, y+1)` and then right.  Pushing it out to `(x+1, y)` (a transposition `YX → XY` among
the openings) changes only `F(i)`.  For a point `v` of `B` the join changes by
`[v.x ≤ x] − [v.y ≤ y]`.  With the shifted variants, no count increases iff `B` avoids

    {x' ≥ x+1, y' ≤ y}  ∪  {x' ≥ x, y' ≤ y−1}  ∪  {x' ≥ x+2, y' ≤ y+1},

and then some count strictly decreases.  The three regions come from the families `oo`/`pp`,
`op` and `po`.  The other three moves (the other corner type of `F`, and both corner types of
`B`) are mirror images.  So a corner of one path that points towards the other path can always
be pushed out unless the other path comes within about one cell of it.

**Descent (proved) and local minima (checked).**  Moves that lower some count and raise none
terminate.  They end in a *locally minimal* pairing whose counts are ≤ the original's, so it is
valid whenever the original is.  `localmin.py` computes all locally minimal pairings:

| levels | pairings | locally minimal | their widths |
|---|---|---|---|
| 9 | 48,620 | 4,462 | 1: 3,102 · 2: 1,316 · 3: 44 |
| 10 | 184,756 | 12,140 | 1: 8,150 · 2: 3,856 · 3: 134 |
| 11 | 705,432 | 33,012 | 1: 21,456 · 2: 11,168 · 3: 388 |

None has width 4.

**Theorem U.**  Assume:

* bottoms adjacent, no pins, single-task `B`- and `A`-blocks;
* all floating tasks unordered, with any anchorings and multiplicities.

If a plan has a valid interpretation, it has one of width ≤ 5.  Computationally the bound is 3
up to 11 levels.

*Proof.*

1. **Validity depends only on counts.**  For one unordered type, a matching exists iff for
   every interval the number of windows inside is ≤ the number of tasks of that type inside
   (Glover's condition, i.e. Hall's theorem for points and intervals).  The relevant intervals
   run from a hole start or opening to a closing or hole end.  Their task counts depend on the
   plan, not on the interpretation.  So an interpretation whose counts are pointwise ≤ those
   of a valid one is valid.  The counts are joins, as above.  For parent anchors the shifted
   points are capped at `(n_X, n_Y)`, and the boundary intervals add the point `(0, 0)` to the
   shifted sets.
2. **Moves of `B`.**  Take a corner of `B` where `B` goes right to `c = (cx, cy)` and then up,
   and push it to `(cx − 1, cy + 1)`.  This swaps two adjacent closings.  Only `B(j)` and its
   shift change, so no count increases unless one of the following holds:
   * `F` meets
     `A₁ = {x ≤ cx−1, y ≥ cy+1}`, `A₂ = {x ≤ cx−2, y ≥ cy}` or `A₃ = {x ≤ cx, y ≥ cy+2}`;
   * `cy = n_Y − 1`, where capping always blocks.

   The four combinations of shifts give exactly these regions, and capping adds only the last
   case.  The mirror move (right/up exchanged) is symmetric.
3. **Descent.**  If `F` is weakly below-right of the corner, the move adds one cell between
   the paths.  So repeatedly applying such count-non-increasing outward moves of `B`
   terminates, and the result is valid by step 1.  At the end, every corner of `B` that points
   towards `F` is blocked as in step 2.
4. **Schedule.**  Process the openings in the order of `F`, the closings one step behind at the
   same point.  This respects the creation constraints.  When `F` is at `p`, the openings form
   one run and the closings `runs(B; p)` runs.  So the number of open segments is
   `runs(B; p') ≤ runs(B; p) + 1`, where `p'` is the point before `p`.  Let `B` pass
   above-left of `p` (the other case is symmetric; if `B` passes through `p` there is one run).
   Then `runs(B; p) = 1 + μ`, where `μ` is the number of up-runs of `B` between its first point
   at height `p.y` and its first point at column `p.x`.  Every up-run but the first starts at a
   right-then-up corner `c` with `cy ≥ p.y` and `cx ≤ p.x`.
5. **Each such corner is blocked, so it lies on row `p.y`, on column `p.x`, or on row
   `n_Y − 1`.**  `F` is weakly below-right of `c`, so the corner points towards `F`; by step 3
   it is blocked.  `F` passes through `p`, so its points before `p` have `y ≤ p.y`, and those
   after have `x ≥ p.x`.  Check where `F` can meet each region:
   * `A₁` and `A₃` can be met only after `p`, by a point with `x = cx = p.x`;
   * `A₂` can be met only before `p`, at height `cy = p.y`.

   Otherwise `cy = n_Y − 1`.
6. **Counting.**  A monotone path has at most one such corner per row and per column.  So
   `μ ≤ 1 + 3`, `runs(B; p) ≤ 5`, and the number of open segments is ≤ 5 throughout. ∎

`followF.py` confirms that the schedule of step 4 costs ≤ 3 at every locally minimal pairing up to
9 levels.

**Not covered.**

* Ordered floating tasks: counts no longer decide validity.  A transposition keeps every task
  assignment valid except for tasks lying between the two swapped openings (or closings) that
  belong to the shrunk level or its child.  The fat-region argument needs a re-matching lemma
  for such tasks.
* Pins.
* Separated bottoms (phase 2).

## 7. Next steps

1. ~~Formalise §4~~ — done (`HtnComplexity/HDDecide/HD2LUCex.lean`, 2026-10-29).
2. **Decidability side:** a reduction to PVASS along §6.10–6.11.  Open:
   * (N): a width bounded by `c(cont)` always suffices.
     * **Proved (Theorem U, §6.14)** for unordered floating tasks with adjacent bottoms, no pins
       and single-task blocks: width ≤ 5 (≤ 3 computationally).
     * The proof should extend with `O(1)` extra blocked corners to pins (checked at 10 levels)
       and separated bottoms (one extra level's windows).  Multi-task blocks need the count
       model with intra-block anchors.
     * **Open: ordered floating tasks.**  Validity is no longer decided by counts.  A corner
       move is still valid when the gap between the two swapped openings or closings holds no
       floating task.  Otherwise a re-matching argument is needed: packet exchange fails at
       one end of the window.  Searches found no forcing beyond width 3.
     * For instances, STRIPS transitions form a right regular band (§6.12), which can only
       help.
   * (P): exactness of the pool (proof sketch in §6.13).
   * (S): correctness of the combined search.
   A proof of (N) needs a replacement for the L of the theorem: for parent-anchored windows no
   single L dominates.
3. **Undecidability side:** an encoding that survives swaps of pending floating tasks between the
   holes, or a reduction from a problem that is invariant under such swaps.  §5.1 narrows this
   down: exchanges happen exactly along crossing windows, and lockstep crossing gives only one
   stack.
4. **Classification:** see §6.  PVASS reachability is decidable (LICS 2026), so an upper bound
   `H₂ ∩ L ≤ PVASS` would settle decidability.  The naive VASS route of §6.4.1 is refuted
   (§6.5): the locked pieces must be kept in order.  Open: a search for two holes whose ordered
   data fit into one stack.
