# Fair strong cyclic, total order: the summary game (third note)

Continues `notes_to_fair.md` and `notes_to_fair_2.md`.  This note fixes the summary construction
and checks it on paper against the three test cases.  Formalisation status is at the end.

## 0. Setting

The problem is totally ordered.  A node of the real game is a pair `(w, s)`: `w` is the remaining
network, a word of tasks of unbounded length, and `s` is the state.  Moves act on the first task
of `w`.  By `CyclicGame.lean` and `TOFair.lean`, fair solvability is `FairWinT univ tn_I s_I`:
there is a positional, iso-closed set `X` of nodes, every node of which lies in the attractor
`FAttrT G X`.  The attractor uses progression moves; a primitive task needs *all* outcomes in `X`
and *some* outcome of lower rank.

Composition is proved (`fairWinT_seqNet_iff`):

    FairWinT G (u;v) s ⟺ ∃ S', FairWinT S' u s ∧ ∀ s' ∈ S', FairWinT G v s'.

What is missing is a finite description of `FairWinT S' [c] s`.  The summary table satisfies
`T = F(T)` but is neither the least nor the greatest fixpoint (`notes_to_fair_2.md`, §2).

## 1. Two progress modes

A call frame must satisfy two different progress requirements.

* **mode `any`** (local fairness): every reachable position of the frame can reach *some* exit
  of the frame, i.e. a state of the frame's exit set `E`.
* **mode `tgt e`** (target reachability): the frame start can reach the *specific* exit `e ∈ E`.
  The parent needs this to make progress through one chosen continuation.

Both are reachability (μ) properties.  They must hold for the *same* strategy, and the strategy
must be safe: all outcomes stay in `X`.  Safety is the coinductive (ν) part.  Mode `tgt e` must
be tracked separately from mode `any`.  Reaching some exit does not imply reaching `e`, and the
parent's progress can only use one continuation.

## 2. The summary game

The game is finite: all components are bounded by the description.

Nodes:

* `Pos(w, s, E, μ)`: `w` is a suffix of `tn_I` or of a method network; `s` a state; `E` an exit
  set (an explicit list of states, or `⊤` at the root); `μ ∈ {any} ∪ {tgt e | e ∈ E}`.
* `Split(c', s, E', e', w, E, μ)`: the sub-call `c'` from `s` with exit set `E'` and progress
  target `e' ∈ E'`; afterwards the frame continues with `w`.
* `Call(c, s, E, e)` and `CallM(c, s, E, e, m)`: a call of `c` and its chosen method `m`.

Each node has two successor relations: `succX` (the successors that must be safe) and `succZ`
(the successors used for progress).  Kinds:

| node | kind | `succX` | `succZ` | accepting |
| --- | --- | --- | --- | --- |
| `Pos([], s, E, any)` | — | — | — | `s ∈ E` |
| `Pos([], s, E, tgt e)` | — | — | — | `s = e` |
| `Pos(a::w, s, E, μ)`, `a` applicable | **fair** | `Pos(w, o, E, any)` for all outcomes `o` | `Pos(w, o, E, μ)` for all outcomes `o` | — |
| `Pos(c'::w, s, E, μ)` | **existential** over `E' ≠ ∅` and `e' ∈ E'` | `Split(c', s, E', e', w, E, μ)` | same | — |
| `Split(c', s, E', e', w, E, μ)` | **conjunctive** | `Call(c', s, E', e')` and `Pos(w, x, E, any)` for all `x ∈ E'` | `Call(c', s, E', e')` and `Pos(w, e', E, μ)` | — |
| `Call(c, s, E, e)` | **existential** over methods `m` of `c` | `CallM(c, s, E, e, m)` | same | — |
| `CallM(c, s, E, e, m)` | **conjunctive** | `Pos(body m, s, E, any)` | `Pos(body m, s, E, tgt e)` | — |

`Pos(a::w, …)` with `a` inapplicable has no successors and loses.

Semantics: `Win := νX. μZ. Attr(X, Z)`, i.e. some `X` contains the root and satisfies `X ⊆ Z(X)`,
where `Z(X)` is the least set with

* `acc n → n ∈ Z`;
* existential `n`: some `m ∈ succX(n)` with `m ∈ X ∧ m ∈ Z`;
* fair `n`: all of `succX(n)` in `X`, some of `succZ(n)` in `Z`;
* conjunctive `n`: all of `succX(n)` in `X`, all of `succZ(n)` in `Z`.

The root is `Pos(tn_I, s_I, ⊤, any)`.

Nodes reached only through `succZ`, i.e. those in mode `tgt`, need not lie in `X`; they only need
`Z`.  This is why the two relations are separate.  If `succZ` successors also had to be in `X`,
every `tgt e` position would have to reach `e` from *every* reachable position.  That fails in
the retry loop: the position "exited in `s₀`" is reachable but is not the target.

## 3. Checks

**(1) `c → [c]` only; root `[c]`.**  `Pos([c], s, ⊤, any)` needs a `Split` with
`Call(c, s, E', e') ∈ Z`.  That needs `CallM` with `Pos([c], s, E', tgt e') ∈ Z`, which needs a
`Split` with `Call(c, s, E'', e'') ∈ Z` at a lower rank, and so on.  There are finitely many
nodes, so some call node would need to sit strictly below itself in rank.  No finite rank exists.
**Rejected**, correctly: the decomposition never ends.

**(2) Retry loop**: `c → [c₂, c] | []`, `c₂ → [a]`, `a` from `s₀` with outcomes `{s₀, s₁}`; the
root is `[c, g]`, where `g` needs `s₁`.

* `Call(c₂, s₀, {s₀,s₁}, s₁)` has rank 3: `[a]`'s outcome `s₁` reaches the target exit.
* `Call(c, s₁, {s₁}, s₁)` uses `[]` and is immediately accepting.
* `Pos([c₂, c], s₀, {s₁}, tgt s₁)` goes to `Split(c₂, s₀, {s₀,s₁}, s₁, [c], …)`.  Its `succZ`
  successors are `Call(c₂, …)`, which has finite rank, and `Pos([c], s₁, {s₁}, tgt s₁)`, which has
  finite rank via `Call(c, s₁, …)`.  Its `succX` successors are `Call(c₂, …)`,
  `Pos([c], s₀, {s₁}, any)` and `Pos([c], s₁, {s₁}, any)`.
* Hence `Call(c, s₀, {s₁}, s₁) ∈ Z` with finite rank, through `CallM([c₂, c])`.
* `Pos([c], s₀, {s₁}, any)`: its `Split(c, s₀, {s₁}, s₁, [], {s₁}, any)` needs
  `Call(c, s₀, {s₁}, s₁) ∈ X` (coinductive) and `∈ Z` (finite rank, from the previous step).
* `X` is the set of all these nodes.  **Accepted**, correctly.

**(3) Unbounded stack**: `c → [a, c, b] | []`, `a` as in (2), `b` a no-op; the root is `[c, g]`,
where `g` needs `s₁`.  Choose `Call(c, s₀, {s₁}, s₁)` with method `[a, c, b]`.

* The tgt-path takes outcome `s₁`, then `Split(c, s₁, {s₁}, s₁, [b])`: `[]`, then `b`, then exit
  `s₁`.  Finite rank.
* The `X`-obligations include `Pos([c, b], s₀, {s₁}, any)`.  It is justified by
  `Split(c, s₀, {s₁}, s₁, [b])`, which needs `Call(c, s₀, {s₁}, s₁)` in `X` (coinductive) and in
  `Z` (finite rank, previous item).
* **Accepted**, correctly.  The summary is finite even though real plays grow the stack without
  bound.

**(4) Over-approximated exit set** (the unsound row 3 of `notes_to_fair_2.md`): `c₂ → [a]` with
`a` deterministic to `s₀`, and the parent claims `E' = {s₀, s₁}` with target `e' = s₁`.
`Call(c₂, s₀, E', s₁)` needs `Pos([a], s₀, E', tgt s₁) ∈ Z`, whose only `Z`-successor is
`Pos([], s₀, E', tgt s₁)`.  That node is not accepting since `s₀ ≠ s₁`.  **Rejected**, correctly.

## 4. Proof plan (against `FairWinT`)

**Soundness** (game → fair).  Real nodes are stacks of frames.  `X_sem` is the set of networks
that are isomorphic to a concatenation of frames such that:

* the top position lies in `X`;
* every lower frame's continuation from every exit of the frame above lies in `X`;
* the bottom exit set is the target.

Two facts are needed.

* **(S1) Closure:** every non-goal node of `X_sem` has a move all of whose successors are in
  `X_sem`.  This uses the `succX` rules; the frame annotation is existential, so no single
  positional choice per network is needed.
* **(S2) Reachability:** every node of `X_sem` has a finite `X_sem`-respecting path to the goal.
  * First a lemma by induction on the `Z`-rank: a frame in mode `tgt e` reaches exit `e`.  A
    `Split` pushes the sub-call in mode `tgt e'`; by induction on the sub-call's smaller rank it
    returns in `e'`; then the continuation follows, again at a smaller rank.
  * Then induction on the stack depth: in mode `any` the top frame reaches some exit; the frame
    below continues from an `X` position.

Then `FAttrT` follows by induction on the path length.

**Completeness** (fair → game).  Semantic predicates:

* `SA(w, s, E) := FairWinT E (net w) s`;
* `ST(w, s, E, e)`: there is a solution `X_s` of `SA` whose attractor towards `{e}` contains
  `(net w, s)`.  The *same* `X_s` is required.

`X_g` is the set of game nodes whose predicate holds.  `Z`-membership is proved by strong
induction on semantic attractor ranks.  This needs a **path-splitting lemma**: if `u;v` is won
with rank `n`, then the attractor path completes `u` at some exit `e` with a rank `≤ n` in `u`,
and continues in `v` from `e` with a smaller rank.  This is a ranked refinement of `compL`.
Exit sets are restricted to states over the facts of the description, as in `TODesc`.

**Complexity.** Nodes have exponential size, since `E` is a list of up to `2^|F|` states.  So
there are doubly exponentially many nodes.  The fixpoint is computed as in `FondHtn/Alt/Buchi.lean`,
with one extra node kind (conjunctive) and separate `succX` / `succZ` relations.  This gives
`2-EXPTIME`; together with the inherited `hardFair_TO` (EXPTIME-hard), the bounds would be
EXPTIME-hard and in 2-EXPTIME.

## 5. Formalisation status: done

Everything in §2–§4 is formalised, with no `sorry` and only the standard axioms.

* `FondHtn/Alt/Buchi2.lean`: the game tool.  It has three node kinds (existential, fair,
  conjunctive), separate `stepX` / `stepZ` successor relations and the νX.μZ winning region
  `B2Win`.  `inExpTime_codeLang_of_buchi2` and `inExp2Time_codeLang_of_buchi2` decide it.
* `FondHtn/MPStrong/TOFair2Sem.lean`: projection (`projSet`, `projSet_attr`) and **path
  splitting** (`FAttrT.split`).
* `FondHtn/MPStrong/TOFair2Desc.lean`: the summary game of §2 on descriptions.
  * Soundness (§4): frame stacks `Stk`, the semantic set `XS`, the motive
    `PosStmt`/`CallStmt`/`Mot`, `sound`, `stk_attr`, `fairWin_of_b2Win`.
  * Completeness: `SemP`/`SemCall`/`SemC`, `cpos` by induction on the rank using path
    splitting, `xc_attr`, `b2Win_of_fairWin`.
  * Polynomial time and the main results:
    * **`fairMP_TO_mem : Cx.EXPTIME2 (PlanExMPFair FClass.TO)`**;
    * `fairMP_TO_bounds` (with the inherited EXPTIME-hardness `hardFair_TO`);
    * `strongMP_TO_bounds`.

One detail differs from §2: positions in mode `tgt e` are separate configurations.  Their
`stepX` successors are mode-`any` positions and their `stepZ` successors are mode-`tgt`
positions, exactly as in the table.
