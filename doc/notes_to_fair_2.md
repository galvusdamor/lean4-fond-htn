# Fair strong cyclic, total order: second attempt (summaries)

Follow-up to `notes_to_fair.md`.  Status: **membership `Cx.EXPTIME2 (PlanExMPFair FClass.TO)` not
proved.**  What is proved, what fails, and what is left.

## 1. Proved (Lean, `FondHtn/MPStrong/TOFair.lean`)

* `FAttrT G X n tn s`, `FairWinT G tn s` — the progression fair game (νX.μZ, positional sets `X`
  closed under isomorphism) with a **target**: the empty network is a goal only in a state of `G`.
  `fairWinT_univ_iff : FairWinT univ tn s ↔ FairWin true tn s`, so with
  `mpStrongCyclicFairSolvable_iff_prog` (CyclicGame.lean) fair solvability is
  `FairWinT univ tn_I s_I`.
* **Fair sequential composition** (`fairWinT_seqNet_iff`, from `FairWinT.compL` / `compR`): for
  well-formed `u`, `v` with disjoint ids,

      FairWinT G (u ; v) s  ↔  ∃ S', FairWinT S' u s ∧ ∀ s' ∈ S', FairWinT G v s'.

  `⇒`: `S' := {s' | FairWinT G v s'}`, and the positional set of `u ; v` is projected to `u`.
  `⇐`: union of the lifted set of `u` and the sets of `v`.  Unions work because the attractor is
  existential: a node needs only *some* witness move.

So composition is **not** the obstruction.  The fair rank argument holds exactly as in the strong
case (`MPProgTH.compL/compR`).

## 2. Why the strong table does not carry over

Set `T(c, s, S') := FairWinT S' [c] s`, where `[c]` is a one-task network.  With the composition
lemma, plus the unfolding of a single compound task and of a single primitive task (routine, not
formalised), `T` satisfies the **same equation** `T = F(T)` as the strong table:

    T(c, s, S') ⟺ ∃ method m of c: the body of m, scanned left to right, is admissible, where
                   a primitive a needs all outcomes in the next state set, and a compound c'
                   needs some S'' with T(c', ·, S'') and the rest admissible from every state of S''.

For the strong reading `T` is the **least** fixpoint of `F`; that is TODesc.lean.  For the fair
reading `T` is a fixpoint of `F` but **neither the least nor the greatest**:

* **Not the greatest.**  Take `c → [c]` only.  The greatest fixpoint contains `(c, s, S')` for every
  `S'`, yet the decomposition never terminates and no goal is reachable.  The greatest fixpoint
  is the literal CB22 reading ("ends in S' or never finishes"): the ideas-file variant decides
  literal strong cyclic, not fair strong cyclic.
* **Not the least.**  Take `c → [c₂, c] | []`, `c₂ → [a]`, and `a` with outcomes `s₀` (retry) and
  `s₁` (success).  The policy "`[c₂, c]` in `s₀`, `[]` in `s₁`" is a fair solution, so
  `T(c, s₀, {s₁})` holds.  But `(c, s₀, {s₁})` depends on itself through the tail call, so the
  least fixpoint never contains it.

`F` loses exactly the information fairness needs: *which* exits of a sub-call are actually
reachable, and that a cycle through recursive calls is left with positive "probability".

## 3. Summary games tried (single global νμ over summary positions)

Positions: `Call(c, s, …)`, `Body(w, s, …)` (the remaining method body `w`), and
`Split(c', s, E, w)` (a sub-call `c'` with exit set `E`, continuation `w` from each `s' ∈ E`).
Exits of a call are `Body([], s)`.  The split's safety condition is clear: the call node and
all continuations must be in `X`.  The problem is the split's **progress** (`Z`) rule; none of
the obvious choices is right:

| `Z`-rule at `Split` | verdict | witness |
| --- | --- | --- |
| all continuations in `Z` (conjunctive) | incomplete | retry example: the tail call `Body([c], s₀)` gets no finite rank |
| call in `X` and some continuation in `Z` | unsound | `c → [c]`: progress through the trivial continuation |
| call in `Z` and some continuation in `Z` | unsound | the call may never exit into the chosen continuation (exits only over-approximated by `E`) |
| call in `Z` and all continuations in `Z` | incomplete | retry example again |
| summaries `(c, s, S_safe, S_good)` with "every reachable node reaches an exit in `S_good`" | wrong spec | inside `c₂ = [a]` the node "exited in `s₀`" is reachable but cannot reach `s₁`; the right per-call property is "the *call start* reaches `S_good`", which does not compose positionally |

## 4. What a correct construction needs (not formalised)

The real game is a **fair game on a pushdown system** (stack = the totally ordered network).
Plays can grow the stack without bound and still be fair, e.g. `c → [a, c, b]`.  A sound and
complete summary must separate:

1. **Safety (coinductive):** the exit set `E` of a call is an over-approximation, all
   continuations from `E` are safe, and sub-call safety may be assumed recursively, as in a
   greatest fixpoint (this is what makes the retry loop work).
2. **Reachability (inductive across recursion levels):** for each exit `e` that is used for
   progress, `e` is *reachable* from the call start.  This must be a least fixpoint even through
   recursive calls, with ranks decreasing from caller to callee (this is what rules out `c → [c]`).
   Call configurations therefore need a target: `Reach(c, s, E, e)`.
3. **Local fairness:** every reachable position of a call body reaches *some* exit of that call.
   Inside sub-calls this follows from (1) and (2) of the sub-call; across the continuation it
   follows from the continuation being safe.

These are three objectives of different fixpoint type over configurations
`(c, s, E[, e], position)`.  Each configuration has exponential size, so there are doubly
exponentially many, which fits 2-EXPTIME.  The Büchi tool (`FondHtn/Alt/Buchi.lean`) only has
existential and *fair-universal* nodes (all successors in `X`, some in `Z`).  The construction also
needs:

* **conjunctive nodes** (all successors in `X` **and** all in `Z`), for "all of these
  reachability obligations";
* **target-indexed attractors** in one νμ, i.e. a Z-rank per obligation `(c, s, E, e)`.

Both are routine to add to the tool: the fixpoint computation is the same, with one more node
kind in `attrStep`.  The open part is the **proof** that the three-part characterisation is
sound and complete for `FairWin` on totally ordered problems:

* soundness: building a positional policy for the infinite pushdown graph from the finite
  summary solution;
* completeness: reading summaries off a positional fair policy; exact exit sets come from the
  reachable exits of each call.

I estimate this to be considerably larger than the strong TO membership (TOGame + TODesc), and
the precise summary definitions should first be checked on paper against the three examples
above (`c → [c]`, the retry loop, `c → [a, c, b]`).
