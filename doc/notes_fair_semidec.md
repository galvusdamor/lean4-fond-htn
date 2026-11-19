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


## Update (brief study): a simpler reduction, no grammars

The local audit above is not needed. The existing HTN encoding of two-stack machines
(`HtnComplexity/Undec/Encoding.lean`: each stack is a chain of compound tasks, one per stack
symbol; the two chains are unordered; a transition is a method of the top symbol whose body is
the transition's action followed by the pushed symbols) already enforces faithful simulation by
preconditions on the control state. Three changes make it a reduction from "the machine runs
forever" to fair solvability:

1. **Ticks.** Every transition action gets a second outcome that sets a fact `STOP`.
2. **Drain.** Every symbol task gets a second method `[drain]`, where `drain` requires `STOP`;
   a bottom marker at the end of each chain is also only drainable under `STOP`. So the goal
   (empty network) is reachable only after a `STOP` outcome.
3. **No acceptance.** The accepting state gets no transitions (it is a dead end like any stuck
   configuration).

Claim: fair solvable ⟺ the machine has an infinite run from the initial configuration.

* (⇐) Follow the infinite run. Every reachable node is either on the run (the next transition's
  `STOP` outcome reaches the goal by draining) or in `STOP` mode (drain everything).
* (⇒) Fair ⇒ progression fair game ⇒ the *safe word game* on the yields of `tn_I`
  (`FOND.HardTR.lsafe_of_fairWin`, already proved for TR and fully generic). Because of the
  bottom markers, `[] ∉ L` without a drain, and drains are inapplicable without `STOP`. Choosing
  the non-`STOP` outcome at every move gives an infinite sequence of applicable transition
  actions, each extending a prefix of a yield. A prefix lemma for the stack encoding ("prefixes
  of yields of the two chains, executed in continue mode, are run prefixes") turns it into an
  infinite run.

Source of non-semi-decidability: the machine `undecTSM` simulates a deterministic TM0
(`ComplexityTheory/Undec/Sim/`). Needed: *infinite run from `start(n)` ⟺ `¬ (univFun n).Dom`*.
* ⇐ (divergence gives an infinite run): the forward simulation (`Sim/Forward.lean`) simulates
  each TM0 step by finitely many machine steps; iterating gives the infinite run.
* ⇒ (no infinite run if TM0 halts): needs a forward legitimacy invariant (every step from a
  legitimate state stays legitimate and makes progress toward the next TM0 step). The backward
  argument of `Sim/Backward.lean` (`step_dest`) contains most of the case analysis; the deps note
  that determinism itself is not proved there.

Then: if fair plan existence were semi-decidable, `{n | ¬ (univFun n).Dom}` would be RE; with the
RE-ness of `Dom` this contradicts `ComputablePred.halting_problem`. (The reduction only needs to
be computable.)

**Assessment.** Feasible and conceptually clean; it would settle the cell as
**neither RE nor co-RE** (RE-hardness is known). Rough size: HTN side (encoding changes, both
directions, prefix lemma) 1–1.5k lines; machine side (forward invariant for `simTSM`, infinite runs
⟺ divergence) 0.8–1.5k lines; computability glue ~0.2k. Main risks: the forward invariant of the
two-stack simulation, and the prefix lemma for the PO stack encoding.
