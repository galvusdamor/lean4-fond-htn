# CB22 Thm 5: TR MP strong is 2-EXPTIME-hard — design and status

Target: `Cx.Hard Cx.EXPTIME2 (PlanExMP .strong FClass.TR)`. Membership `strongMP_TR_mem` exists,
so this would give `Cx.Complete Cx.EXPTIME2 (PlanExMP .strong FClass.TR)`.

Status: **not formalised.** The source is formalised:
`FOND.ATM.exptime2_tabWin` (`FondHtn/ATM/Tableau.lean`), the CKS tableau game of a fixed
deterministic machine `M` on the doubly exponentially padded input. Below are the design of the
encoding, a check of the G8 issue, and the work packages with size estimates. The work is a
merge of two large existing developments:
- the MP strong path-game reductions of `FondHtn/HardMP/` (≈ 4700 lines; EXPTIME, polynomial
  counters in the state);
- the tail-recursive tape encoding of `HtnComplexity/SpaceEnc/` (26 files; deterministic plan
  existence, exponential tape in the network).

Neither can be reused as a black box.

## 1. The game to encode

For a given `x`, with `B := c · 2^q(|x|)` the counter width (`T x < 2^B`):

* a position is `(t, i, σ)`, where
  - `t` and `i` are `B`-bit counters,
  - `σ = (state option, symbol)` is constant size;
* at `t = 0`, the position is won iff `σ = row0 i`, where
  `row0 i = (i = 0 ? q₀ : none, (padExp2 q x).getD i)`. Cell `i` of the padded word is decided
  by comparing `i` with `2|x|`, `2|x| + 2` and `2|x| + 2 + 2^2^q`, and for `i < 2|x|` by reading
  bit `⌊i/2⌋` of `x`. That only needs the low `log |x|` bits plus "all high bits zero";
* at `t + 1`:
  1. ∃ names `l, c, r` with `F l c r = σ` (the local rule `M.F`, a finite table);
  2. ∀ picks `d ∈ {−1, 0, +1}`, with `d = −1` impossible at `i = 0`;
  3. the new position is `(t, i + d, (l, c, r)[d])`;
* the initial claim: ∃ picks `i ≤ T` and an accepting entry; the start is `(T x, i, σ)`.

## 2. Encoding sketch (MP strong, tail-recursive)

* **State (polynomial).**
  - the claimed entry `σ` and the three named entries `l, c, r`;
  - nature's direction `d`;
  - carry/borrow bits and phase flags for the counter passes.
* **Network (exponential).**
  - The counters `t` and `i` are stored as `2·B` pending primitive bit tasks
    `bit_t(j, b)` and `bit_i(j, b)`.
  - `B` copies are produced per round by a doubling clock inside the tail-recursive round
    method. This is the mechanism of SpaceEnc, which stores a `2^m`-cell tape in the tails of
    the words of two alternating loops.
* **One round** is one iteration of a tail-recursive loop `round → [claim, nature, pass_t,
  pass_i, round]`:
  1. `claim`: the policy's method choice puts `l, c, r` with `F l c r = σ` into the state. This
     is an action with precondition `σ` and effect `l, c, r`, one action per table row. The
     choice is **existential**.
  2. `nature`: a nondeterministic action sets `d` and moves `σ := (l, c, r)[d]`. This is
     **universal**.
  3. `pass_t`: execute the old `t` bits from least to most significant with a borrow in the
     state. Each old bit task is paired with one new bit task, chosen by the policy as a
     decomposition, whose precondition checks `new = old ⊖ borrow`. If the policy chooses
     wrongly, it is stuck, so a strong policy chooses correctly.
  4. `pass_i`: the same for `i ± d`. The `i = 0`, `d = −1` case is blocked by a "borrow out"
     dead end.
  5. When the old `t` is zero, a `final` branch replaces the loop. It checks the `t = 0`
     condition by a pass over the `i` bits.

## 3. G8 (delaying decompositions) and commitment

* **The claims `l, c, r`** are written to the state by the `claim` action, which is executed
  before the `nature` action (`claim ≺ nature` inside the round). The policy may delay
  *decompositions*, but not past an ordering constraint on primitive executions. So `l, c, r`
  are fixed before nature moves. **No commitment problem.**
* **The counter bits** are chosen by the policy, possibly after it has seen `d`. That is
  harmless: the correct new value is a function of the old value and `d`, and every bit is
  checked locally against the old bit and the carry. Any delay only lets the policy see `d`
  before choosing, and there is nothing to gain from it.
* **What must be proved** is the converse soundness: in every outcome branch the network after
  a round again holds exactly the counters `t − 1` and `i + d`. This is SpaceEnc's tape-copy
  invariant (old and new words consumed in lockstep), now under a policy instead of a fixed
  plan, and with nature's `d` read from the state during the copy.

## 4. The fair reading

For `PlanExMPFair FClass.TR`, a fair policy may cycle. A cycle here would repeat a position
`(t, i, σ)`, but `t` strictly decreases every round, so no reachable node repeats as long as `t`
is in the network: `t` is itself the round counter that the HardMP agent had to add for the
EXPTIME case. The fair and strong readings should therefore coincide on this family, as in
`fair_iff_strong_ACYC`, via a well-founded measure on reachable nodes: the value of `t`, then
the position within the round. The same encoding would give
`Cx.Hard Cx.EXPTIME2 (PlanExMPFair FClass.TR)`, and with `fairMP_TR_mem`, completeness.

## 5. Work packages (estimated sizes, by analogy)

| package | content | estimate |
| --- | --- | --- |
| P1 | descriptions: actions/methods of the round loop, doubling clock, counter bits; PT construction; TR certificate | 1500 lines (cf. `HardMP/Desc*`, `Article/ExpSpaceNum`, `ExpSpacePT`) |
| P2 | the network invariant per round: every refinement of the round is `claim · nature · pass_t · pass_i`, counters in canonical form | 1500 lines (cf. `SpaceEnc/Yield`, `BlockYield`, `Sound*`) |
| P3 | soundness: a strong policy induces a winning ∃-strategy of `TabWin` (by induction on `t`) | 800 lines (cf. `HardMP/Sem`, `Rounds`) |
| P4 | completeness: from `TabWin` (true claims, `tabWin_iff`), build the policy and prove strongness | 800 lines (cf. `HardMP/Bridge`, `SpaceEnc/Comp*`) |
| P5 | assembly with `exptime2_tabWin`, padding sizes (`B = c·2^q`), `Cx.Hard` | 300 lines |
| P6 | fair reading via the measure `t` | 300 lines |

Recommended order: P5's arithmetic first, i.e. fix `B` and the counter conventions. Then P1, then
P2 before P3/P4; P2 is where the SpaceEnc ideas must be re-proved under policies.
