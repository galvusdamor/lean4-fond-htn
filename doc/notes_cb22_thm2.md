# CB22 Thm 2 (ACYC, partially ordered, MP strong): notes on the EXPSPACE lower bound

Status: **open.** No formal proof. This note records what was tried after the EXPTIME
reductions in `FondHtn/HardMP/` were finished, and why they do not extend. Target:

    Cx.Hard Cx.EXPSPACE (PlanExMP .strong FClass.ACYC)

The inherited bound is NEXPTIME (`hard_ACYC_mp`). Membership in EXPSPACE is in
`FondHtn/MPStrong/`. CB22's proof ("extend ABA15 Thm 6.1 to ATMs") is only a sketch (catalogue
G12).

## 1. Why the path game of `FondHtn/HardMP/` stops at EXPTIME

The Thm 1/3/4 reductions play a path game down a derivation tree. Each node of the tree is
stored in the FOND state as a polynomial-size triple `(c, s, s')`. The policy states the
children: a method and the intermediate states. Nature then chooses one child.

Every position of this game is a polynomial-size configuration plus a clock. So the game is an
alternating polynomial-space computation, which is EXPTIME (= APSPACE). Making the clock longer
does not help.

EXPSPACE = AEXPTIME needs alternating runs whose configurations are **exponentially large**. In
MP strong ACYC the only place for exponential information is the **task network**:
- reachable networks have size at most `m^(k+1)` (ABA15 Cor 3.2);
- the policy sees the whole network, since the policy is a function of `(tn, s)`.

## 2. Ingredients that do work

* **Doubling clocks** (`clk j → [clk (j-1), clk (j-1)]`) give `2^N` copies of a gadget in an
  acyclic, polynomial-size hierarchy. This works for totally ordered and partially ordered
  networks alike.
* **Counters in the state** (as in `FondHtn/HardMP/DescC.lean`) give the position of the
  current gadget within a totally ordered chain of `2^N` gadgets: one increment per gadget.
* **Honest recording of nature's choices.** Let a nondeterministic action add fact `u_b`.
  Order directly after it a compound task whose methods are `[chk_b, hold_b]`, where `chk_b`
  has precondition `u_b`. The policy must decompose it according to the outcome. If `hold_b`
  is left pending, the network keeps the choice.
* **Universal challenge plus local verification**, as in the tableau proof of Thm 4.3.6:
  1. Nature picks a cell index `(t, i)` (2N bits, by N nondeterministic actions).
  2. One totally ordered pass over the committed cells uses a counter to copy the symbols at
     `(t-1, i-1..i+1)` and `(t, i)` into registers.
  3. A final check tests the transition relation.

  For a strong solution every challenge must succeed. So the committed tableau is locally
  consistent everywhere, i.e. it is a computation.

## 3. Intended construction

Reduce from an alternating machine `M` with time and space `2^n`, so from AEXPTIME:
1. Rows `t = 0 … 2^n - 1`; each row is `2^n` cells, produced by a clock.
2. **Commit** row `t + 1`: the policy picks the symbol of each cell (existential choices) by
   decomposing cell tasks `cell → [mark_σ, hold_σ]`.
3. If the state of row `t` is universal, nature picks the branch, which is recorded honestly as
   in §2.
4. After the last row, nature challenges one cell and the `hold_σ` tasks are checked in a final
   pass, as in §2.
5. Acceptance: the last row holds an accepting state. This is checked as one more challenge
   type.

Correctness would follow, as in `FondHtn/HardMP/Rounds.lean`, from these facts:
- a strong solution is a strategy that commits rows as a function of the recorded universal
  choices;
- local consistency under every challenge forces genuine computation branches;
- conversely, an accepting computation tree yields such a strategy.

## 4. The obstacle: commitment before the challenge

MP policies may **delay decompositions**: decomposing any compound task at any time is allowed,
and delaying is never worse (`MPAndOrH.delay`, gap G8). So "the policy chooses σ when it
decomposes `cell`" commits nothing. The policy can wait until nature has fixed the challenge
`(t, i)` and then choose every σ to suit that one challenge. Some mechanism must force each
decomposition to happen *before* the challenge, while a trace of the choice survives *after* it.

Variants considered:

1. **Order `mark_σ` before the challenge and leave `hold_σ` pending.** This needs `mark ≺
   challenge ≺ hold` for every cell. Decomposition copies the ordering constraints of `cell` to
   all its subtasks. So if cells form a chain `cell₁ ≺ cell₂ ≺ …`, then `hold₁ ≺ mark₂`, and all
   holds must run before the challenge, which loses the information. If `cell` is unordered
   with respect to the challenge, the challenge can no longer be forced after the marks.
2. **Force "all marks done" by a counter precondition on the challenge**, with the cells
   mutually unordered so that the holds survive. The cells then carry no position: their names
   are polynomial and cannot hold an exponential index. The policy fixes the execution order,
   so the holds form an unordered multiset of symbols, and the final pass cannot locate cell
   `(t, i)`.
3. **Two chains, A for marks and B for holds, built by separate decompositions.** Chain B is
   decomposed only after the challenge, so the policy can choose B's symbols adaptively. A
   consistency check between A and B at the challenged index would require A to be read after
   the challenge, which is variant 1 again.

All three fail for the same reason. In a partially ordered acyclic network, information
persists only as pending tasks, and their positions are protected only by ordering constraints
that copy over to every subtask. This is the coupling that ABA15's NEXPTIME proof solves with
three synchronised totally ordered chains:
- tape symbols,
- copy-check,
- head and transition.

These chains interleave by shared facts. Commitment is forced because each chain's next
primitive can only run when the other chains have produced the matching fact. CB22's sketch
assumes this synchronisation still holds when the policy chooses decompositions adaptively and
nature branches.

## 5. Most promising route and what remains

* **Route A (CB22 / ABA15).** Formalise ABA15 Thm 6.1:
  - the three chains, each produced by doubling clocks;
  - synchronisation facts that force lockstep execution.

  Then add nondeterministic `step∀` actions to the head chain. The lockstep is what forces
  commitment: the tape chain must have *executed* the cell of row `t` before the head chain
  can read it, so nothing is left to choose adaptively.

  Remaining work:
  1. Prove that lockstep is forced even though the policy chooses the interleaving and
     decomposes lazily. ABA15 argues this for a fixed linearisation.
  2. Handle universal transitions that move the head in different directions (CB22 assumes
     they all move the same way).
  3. Build a large PT layer.

  The pieces of `FondHtn/HardMP/` that should carry over:
  - the list game (`Bridge.lean`), but only for totally ordered parts, so it needs
    generalising to interleavings of chains;
  - the `ASpec`/program compilation (`Encoding.lean`, `Desc.lean`);
  - the clock.
* **Route B.** Reduce from a known EXPSPACE-hard deterministic class
  (`thm_4_3_7_tr`: TR ∩ TOtn) by unrolling tail recursion into acyclic doubling with clocks
  `clk_j(q, q')`. This cannot work: deterministic ACYC is in NEXPTIME. The unrolling fails
  because TR runs may need doubly exponential length when chains interleave, since networks
  grow exponentially. Alternation would have to supply the missing power, which leads back to
  route A.
