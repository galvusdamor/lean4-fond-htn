# Is fair strong cyclic method-based plan existence semi-decidable (unrestricted problems)?

Status: **open; not formalised.** For comparison, what is formalised:

* `FOND.strongMP_semiDecidable` (`FondHtn/MPSemi/Strong.lean`): strong method-based plan
  existence, `PlanExMP .strong FClass.UNRES`, is semi-decidable. It is also undecidable
  (`FOND.strongMP_semi_undec`).
* The fair reading `PlanExMPFair` is decidable for ACYC, REG, TR, TR∩TO and REG∩TO
  (`FondHtn/MPStrong/CyclicDesc.lean`, `CyclicAcyc.lean`).
* Fair plan existence is undecidable for UNRES. The reductions `redP_planExMPFair` from
  deterministic plan existence give RE-hardness.

## Why the strong proof does not carry over

The strong case has a **finite certificate**. Strong solvability is the *least* fixpoint
`MPProg`, so every winning strategy has a finite height `n` (`MPProg.toH`). The description game
truncated at depth `2n` is a finite AND-OR tree, and an accepting run of its depth-first
evaluation is a finite object that a polynomial-time check verifies.

Fair solvability is the *nested* fixpoint `νW. μZ. goal ∨ (∃ move. all successors in W ∧ some
successor in Z)` (`FOND.Problem.FairWin`, `mpStrongCyclicFairSolvable_iff_prog`). A witness is a
post-fixpoint `X`: a set of nodes, closed under isomorphism, every node of which lies in the
attractor of `X`.

* For the decidable classes above, the nodes reachable from `(tn_I, s_I)` lie in a finite set
  up to isomorphism, because progression bounds the network size. `X` is then a finite set of
  description-level nodes, and the attractor computation is a finite fixpoint iteration.
* For UNRES the reachable networks can grow without bound *along cycles of the policy*.
  Example: a recursive task `c → [a, c] | []`, where `a` has a "fail" outcome that leads back
  to an earlier state. Each retry decomposes `c` again, so the retry loop visits infinitely many
  non-isomorphic networks. A fair policy may need such unbounded loops: retrying is the point
  of strong cyclic plans. Then `X` is infinite, and no finite object certifies the greatest
  fixpoint.
* The least-fixpoint (attractor) part is RE for a given *finite* `X`. In the unrestricted case
  one would have to certify `∀ x ∈ X, x ∈ μZ…` for an infinite, isomorphism-closed `X`. That is
  a `Π`-type condition over an infinite object, and the natural upper bound is not `Σ⁰₁`.

## Expected answer and a route to a proof

**Conjecture:** not semi-decidable. That would mean fair strong cyclic MP plan existence is
**co-RE-hard** for UNRES, in addition to the known RE-hardness, so it is neither RE nor co-RE.
Proof idea: reduce non-halting of a two-counter (or two-stack) machine `M` to fair solvability.

* A recursive decomposition simulates `M` step by step. The policy chooses the simulation by
  method choices. The environment decides, through an outcome of a "checkpoint" action after
  every step, between "audit" and "continue".
* "audit" verifies the last step locally. A correct step leads to a goal; a wrong step leads to
  a dead end.
* "continue" proceeds with the simulation.
* Reaching the halting state leads to a dead end, a node from which no goal is reachable.
* If `M` never halts, the correct simulation policy is fair: from every reachable node the next
  checkpoint's "audit" outcome reaches a goal. If `M` halts, every policy either simulates
  incorrectly (an audit reaches a dead end) or reaches the halting dead end. Either way some
  reachable node cannot reach a goal.

The delicate part is the local audit. The checkpoint must compare the counter or stack contents
before and after a step using only STRIPS facts and the hierarchy. This is the same difficulty
discussed for the PCP construction in `doc/notes_pcp_strongOD.md`, but here unrestricted
recursion is available, so the existing CFG / two-stack machinery of
`ComplexityTheory/CFG/TSMGram.lean` is a natural starting point.

Until this is done, the CB22 table entry "semi-decidable" should be read as **proved for weak and
strong**, and **open for strong cyclic** (in both the literal and the fair reading).
