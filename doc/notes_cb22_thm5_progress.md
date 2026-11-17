# CB22 Thm 5 (TR, MP strong, 2-EXPTIME-hard): progress and plan for P1/P2

Status:
* P5 is done (`FondHtn/HardTR/Source.lean`):
  - `exptime2_tabWin_pow`: the tableau game started at the time `2^B − 1`, with `B = 2^e(|x|)`;
  - the bit-list counter passes `decB`, `incB` and `isZeroB`, with their numeric meaning.
* P1 to P4 and P6 are **not started**. This note fixes the design and the proof plan so that a
  later session can start directly. The context of the session that wrote it was exhausted.

## 1. Design: "transducer SpaceEnc"

We keep the architecture of `HtnComplexity/SpaceEnc`:
- two alternating tail-recursive loops, A (`p = true`) and B (`p = false`);
- one *block* per round;
- each block holds `W = 2^m` address-checked **chain words** and one round-end word.

The tape has `W = 2·B` cells, with `B = 2^e(|x|)`. Cell `2j` holds bit `j` of `t` and cell
`2j+1` holds bit `j` of `i`. A chain word of parity `p`:

    ws p · wb p (m-1) x … wb p 0 x · op p γ γ' · (inc p k | wrap p) · rv p γ' · rb p (m-1) x … rb p 0 x

Its parts:
* `wb … x` checks the address `x` against the round counter `cb` (state) when the word is
  written.
* `op p γ γ'` is the **transducer action**. Its precondition is `sym γ` (the bit read from the
  other loop's tail) together with the transducer state in the FOND state. Its effect sets the
  new transducer state and requires `γ' = out(state, γ)`, with one action per row of the
  transducer table.
* `rv p γ' · rb …` is the tail. It is read in the next round by the other loop and puts `sym γ'`
  into the state, with the address checked again.

The transducer is finite and fixed by `M.F` and the round phase:
- its state is `(σ, l, c, r, d, borrow_t, carry_i, zero_t, zero_i, …)`;
- on a `t` cell it applies `decB` with the borrow and updates `zero_t`;
- on an `i` cell it applies `incB` or `decB` according to `d`;
- in the final round it evaluates `row0 i` with the address bits as position.

The round-end word, in place of SpaceEnc's head move, is

    claim p (l, c, r) · nature p · …

* `claim p (l, c, r)`: one action per triple with `M.F l c r = σ`. Its precondition is `σ` and
  its effect sets `l, c, r`. The policy chooses it, so this move is **existential**.
* `nature p`: a **nondeterministic** action with three outcomes `d ∈ {−1, 0, +1}`. It sets
  `σ := (l, c, r)[d]` and `d`, so this move is **universal**.
* G8 is not a problem: `claim ≺ nature` inside one word, so `claim` is executed before nature
  moves.

The start and the end:
* **Round 0** writes `t = 1^B` and the existential choice of `i` (one `wb`/`op` per cell, with
  the bit chosen by the policy) and an accepting entry `σ`.
* **Termination**: when `zero_t` holds at the end of a round, the last block's words run the
  `row0` check, and `fin` accepts if it succeeds.

## 2. The abstract round lemma (the core of P2)

We work on the progression game `MPProg` on descriptions (`FondHtn/MPStrong/Game.lean`, with the
fresh-id convention `decDesc`, `progDesc`), since `mpStrongSolvable_iff_mpProg` reduces
strong MP solvability to it.

* **Canonical round-start node** `K(ρ, w)`:
  - the round parity `ρ`;
  - the tape content `w : Fin W → Bool`, stored as the pending tails `rv · rb…` of the previous
    block of the other loop;
  - the recursive loop task of the writing loop, not yet decomposed;
  - the recursive task of the other loop, pending after its tails;
  - the FOND state: counter `cb = 0`, the transducer start state, and `σ`.
* **Round lemma (soundness).** If `MPProg K(ρ, w)` holds, then:
  - either `zero_t(w)` holds and `row0(i(w)) = σ`;
  - or there are `l, c, r` with `F l c r = σ` such that for every `d`,
    `MPProg K(¬ρ, upd(w, d))` holds with the new `σ`.

  Proof plan:
  1. Progression from `K` can only decompose the writing loop task into a block. Before
     the round-end word, every executed primitive is a `wb`/`op`/`inc`/`rv`/`rb` action of the
     two blocks.
  2. Lockstep invariant (SpaceEnc's `SoundInv`, but for one round and for every play prefix):
     - the counter `cb` equals the number of completed positions;
     - the next executable `rv`/`rb` are exactly those of address `cb`;
     - the next `wb` must carry address `cb`.

     This is a statement about **all** play prefixes, not about one refinement, so it is
     proved by induction along `MPProg` derivations with a `SoundInv`-style invariant on
     (network, state).
  3. At the end of the sweep the new block's tails are pending with `upd(w, d)` and the
     network is `K(¬ρ, …)` **up to isomorphism**, using `MPProg.isoVia`.
* **Round lemma (completeness).** Conversely, from `K(ρ, w)`:
  - the canonical strategy decomposes the words with the correct addresses and transducer
    outputs, chooses the `claim` given by a winning `TabWin` claim, and continues;
  - for each nature outcome it reaches `K(¬ρ, upd(w, d))`.

  This is proved by building the play explicitly, as in SpaceEnc's `CompPlan`/`CompStep*`, as
  an `MPProg` derivation segment.

Abstract layer (description-independent, proposed file `HardTR/Round.lean`):
- state the lemmas for an abstract "two-loop block system" given by
  1. a word language,
  2. the address check,
  3. the transducer;
- then instantiate them with descriptions in `HardTR/Desc.lean` (P1).

The lockstep argument needs only these facts:
- words are totally ordered sequences;
- blocks are unordered sets of words, followed by the loop's recursive task;
- the counter and address checks force one word per address per round.

## 3. Assembly (P3/P4)

* **P3 (soundness).** By induction on `t` (the counter, decreasing), with the round lemma: a
  strong policy from `K(…, t, i, σ)` gives `TabWin t i σ`.
* **P4 (completeness).** From `tabWin_iff`, the true claims give `TabWin`; then the round lemma
  (completeness) is iterated `2^B − 1` times.
* **P6 (fair reading).** The measure "value of `t`, then position in round" decreases strictly
  along every play, so fair = strong on this family, as in `fair_iff_strong_ACYC`.

## 4. Estimates

| package | lines |
| --- | --- |
| P1 (descriptions, PT, TR certificate) | ≈ 1500 |
| P2 (abstract round lemma + instantiation) | ≈ 2500 |
| P3, P4 together | ≈ 1200 |
| P6 | ≈ 300 |

The SpaceEnc files to mirror are `Defs`, `Words`, `BlockYield`, `SoundInv`, `SoundCore`,
`CompStep*` and `RenderTR`.
