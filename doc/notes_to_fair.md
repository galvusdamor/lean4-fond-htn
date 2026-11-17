# Total order, fair strong cyclic: why the ideas-file table fails

(Recorded from the formalisation attempt; strong case proved as `strongMP_TO_mem`,
`FondHtn/MPStrong/TODesc.lean`.)

`c` compound, `a` nondeterministic with outcomes `s₁` (success) and `s₀` (retry).

1. **Greatest-fixpoint table is unsound for the fair reading.** Single method `c → [c]`: every
   triple `(c, s, S')` survives the greatest fixpoint, yet decomposition never ends, so no goal is
   reachable: no fair solution. (It *is* a literal CB22 strong cyclic solution — the greatest
   fixpoint "ends in S' or never finishes" is the safety/literal reading.)
2. **Least-fixpoint table is incomplete for the fair reading.** `c → [c₂, c] | []`, `c₂ → [a]`:
   the fair policy uses `[c₂, c]` in `s₀` and `[]` in `s₁`. The play cycles `(c, s₀) → … →
   (c, s₀)`, fair because progress happens via outcome `s₁`; in the table `(c, s₀, S')` depends on
   itself through the tail call, so the least fixpoint never adds it.
3. Treating split nodes as fair-universal (all successors safe, *some* in the attractor) is
   unsound (example 1); requiring *all* in the attractor is incomplete (example 2).

**Obstruction.** Fair TO planning is a Büchi-like game on a pushdown system (the network is the
stack; e.g. `c → [a, c, b]` gives infinitely many reachable nodes, each with a reachable goal).
A correct algorithm needs per-call summaries `(c, s, S_safe, S_good)` (all exits in `S_safe`;
from every reachable node of the call some exit in `S_good` reachable), composed (checked on
paper), and computed by a nested νμ fixpoint over summary nodes — saturation for pushdown Büchi
games. Open.
