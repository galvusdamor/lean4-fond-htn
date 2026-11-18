# PCP with gated cheats — check and the construction that is formalised

Target: strong OD plan existence (fixed methods) is undecidable for problems that are
Bercher-regular and tail-recursive (`FClass.inter FClass.REG FClass.TR`).

## Verdict on the repair

The gated-cheat repair works, with three refinements found while checking it:

1. **Cheats must live in separate supply chains**, not inside the chains `A`, `B`. A regular
   method puts its primitive tasks before its compound task, so every cheat of a block of `A`
   must be executed before the next block of `A`. The cheats of the *active* mode are disabled
   until `fin` (otherwise the policy could fake the active check), so a cheat inside `A` would
   block `A`. Two supply chains `S₁`, `S₂` (methods `s → [cheat_m, s] | []`), unordered with
   everything, fix this; their length is chosen with the decomposition, before the mode is known.
   One cheat action per mode suffices: `cheat_m` adds *all* facts of mode `m`.
2. **`A` and `B` must be separate chains**: between the two modes the alignment of the two
   streams drifts by a whole configuration, which a lockstep (block-by-block) structure cannot
   absorb with finitely many facts.
3. **No PCP is needed.** The two modes check two equalities of morphic images,
   `π₁(A) = π₁(B)` and `π₂(A) = π₂(B)`, which encodes runs of a two-stack machine directly
   (the library's `undecTSM`, `HTN.Undec.not_computablePred_undecTSM`). This avoids proving PCP
   undecidable.

## Construction

Two-stack machine `M`, initial stacks `(s₁, s₂)`. A configuration `(q, s₁, s₂)` is written
`rev s₁ · Q q · s₂`. A step on stack 1 by transition `t` rewrites `pop · Q src` into
`rev push · Q tgt`; on stack 2, `Q src · pop` into `Q tgt · push`.

Letters carry one optional character per mode, `(o₁, o₂)`.
- `A = [(·,c) | c ∈ enc(init)#] ++ [(c,c) | c ∈ mid] ++ [(c,·) | c ∈ enc(final)#]`, `mid` arbitrary.
- `B` = one or more blocks `u · R(t) · v · #`, `u, v` stack symbols as `(c,c)`, `R(t)` = the
  letters `(r,·)` of the right-hand side followed by `(·,l)` of the left-hand side.

Then `π₂(A) = π₂(B) ∧ π₁(A) = π₁(B)` holds for some `mid`, `B` iff `M` reaches the final
configuration from the initial one in at least one step (split both sides at `#`).

FOND problem: facts `free_m`, `pend_m(c)`, `cheatOK_m` for modes `m = 1, 2`.
- `init`: two outcomes, mode 1 adds `{free₁, cheatOK₂}`, mode 2 adds `{free₂, cheatOK₁}`.
- A letter of `A` with `o_m = c`: precondition `free_m`, adds `pend_m(c)`, deletes `free_m`.
- A letter of `B` with `o_m = c`: precondition `pend_m(c)`, adds `free_m`, deletes `pend_m(c)`.
- `cheat_m`: precondition `cheatOK_m`, adds all facts of mode `m`.
- `fin`: precondition `{free₁, free₂}`, adds `{cheatOK₁, cheatOK₂}`.
- `tn_I = {init, A, B, S₁, S₂, fin}`, `init ≺ A, B ≺ fin`. Chains are automata: methods
  `(k, q) → [x, (k, q')]` and `(k, q) → []` for final `q`. All methods are regular (one compound
  task, last); one stratum gives tail recursion.

Correctness. The only applicable first task is `init`. Afterwards all actions are deterministic.
In the active mode `m`, the facts of mode `m` change only through the letters of `A` and `B`
before `fin` (its cheats need `cheatOK_m`, which only `fin` adds), so executing all letters and
then `fin` (precondition `free_m`) is possible iff the `m`-streams of `A` and `B` are equal. The
facts of the other mode are restored by a `cheat` before every letter. After `fin` the remaining
cheats are enabled. The trivial case (initial = final configuration, zero steps) is mapped to a
fixed solvable instance.
