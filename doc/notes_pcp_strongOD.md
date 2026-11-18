# "PCP" idea: FM strong OD undecidable for Bercher-regular / tail-recursive problems — notes

Status: **not formalised.** The sketched construction (ideas file, section "PCP") does not work
as sketched with STRIPS actions (FOND actions without conditional effects). Below: why, what is
available in the library, and possible repairs.

Target: `¬ Cx.Decidable (PlanExFM .strongOD (FClass.inter FClass.REG FClass.TR))`.

Scope check. `FClass.REG` is Bercher's class: `tn_I` is unrestricted. If regularity also
covered `tn_I` (CB21 Def. 3.3 / DB25), the problem would be decidable, since regular FM strong
OD is in EXPSPACE (CB21 Thm 5.3, DB25 Thm 2). So any undecidability proof must use the two
unordered compound tasks in `tn_I`, as the sketch does.

## 1. Library sources

* `HTN.Article.thm_4_1_1` and the corollaries in `Article/Undecidability.lean` reduce from
  **intersection of context-free grammars** (`HTN.CFG.not_computablePred_inter_fixed`,
  `ComplexityTheory/CFG/Undec.lean`).
* That result is proved from the halting problem of a two-stack machine (`HTN.Undec.undecTSM`)
  via the "stack grammars" of `CFG/TSMGram.lean`.
* **There is no PCP in the library.** The stack grammars use rules
  `I p i q → N p s[i] r · I r (i+1) q` with nested nonterminals. They are not tail-recursive,
  so the CFG route gives only the known `undecidable_fm` (UNRES), not TR or REG.
* A PCP-based proof therefore needs a new undecidability proof for PCP, from
  `undecTSM` or a TM simulation. That is large but standard.

## 2. The sketched construction and where it breaks

Sketch:
- `tn_I = init ≺ {A, B}`;
- `A → [i, u_i, A] | [i, u_i]`, and `B` likewise with `v_i`, where index and character tasks
  are primitive;
- `init` has two outcomes, "char mode" and "word mode";
- after the fixed decomposition, the OD policy interleaves A and B.

In char mode the policy should check that the character sequences agree, ignoring index tasks.
In word mode it should check that the index sequences agree, ignoring character tasks.

**The problem is "ignoring".** Every task is one action with mode-independent preconditions and
effects. Only `init` behaves differently per mode, and only through the state it produces.

Take the character check in char mode. A one-place channel needs some fact `f` that a B-char
task requires and that some task makes false. An example:
- `emit_a`: precondition `¬busy`, adds `busy, let_a`;
- `take_b`: needs `busy, let_b`, deletes both.

The same tasks run in word mode with the same effects. In word mode the interleaving is fixed
by index alignment. Within one word block the lag between A's and B's characters is arbitrary,
and across blocks it is unbounded, since PCP solutions need not align. So the character tasks
block in word mode.

The same argument applies to index tasks in char mode, and to any finite channel. A channel
that is "free" in one mode must keep its preconditions satisfied under every interleaving of
the mode-independent effects that the other mode's alignment imposes. A fact that is never
falsified cannot block in the other mode either. A fact that is falsified must be restored by
a matching task with bounded delay, and that is exactly what fails.

Splitting each element into a char part and a word part acting on disjoint facts (`[c, w]`)
does not help either. The free part's preconditions still have to survive the forced (lagged)
interleaving of the other mode.

So the sketch needs **conditional effects**, or **mode-dependent applicability**, i.e.
disjunctive preconditions such as "word mode ∨ letter matches". Neither is available.

## 3. Possible repairs (not done)

1. **Disjunctive preconditions via nondeterministic outcomes.** These do not work. Outcomes
   are adversarial in strong OD, so they cannot be used to select the free behaviour.
2. **More chains and consistency modes.** Use chains `A, A', B, B'` and three modes:
   char (A vs B), word (A' vs B'), consistency (A vs A', B vs B'). Every chain still takes
   part in two modes and must be free in the third, so this is the same obstacle.
3. **Method-based policies (MP) instead of FM.** Each element is compound, with methods
   `[check]` or `[skip]`, and `skip` requires the mode fact. In MP the policy decomposes after
   seeing the mode, but it can then also choose different words per mode, since decompositions
   can be delayed (gap G8). So the words are not committed. This is the same commitment
   obstacle as in `doc/notes_cb22_thm2.md` §4.
4. **A different undecidable source that needs only bounded-lag checks per mode.** For
   example, encode a 2-counter machine computation:
   - word = sequence of configurations with counters in unary;
   - A emits configurations `c₀ c₁ c₂ …`, B emits the claimed successors `c₁' c₂' …`;
   - mode 1 checks `cₖ₊₁ = cₖ'` (letter equality with a shift of one configuration), and
     mode 2 checks that each pair `(cₖ, cₖ')` is a step.

   Both checks compare *unboundedly long* configurations with lag one configuration, so the
   lag is unbounded again. The difficulty is generic. Any correspondence-type check between
   two independent regular chains needs unbounded buffering in at least one mode, and a mode
   that does not check must still execute everything.
5. **Use the partial order inside methods.** Allow TR (non-last compound subtasks of lower
   strata) to place the "free" parts of the inactive mode in a separate unordered branch. For
   example, `A → [i, u_i, A]` ∥ `skipA` where `skipA` collects the inactive-mode tasks.
   Separating them requires the inactive tasks to be produced by the *same* decomposition
   choice, i.e. a method `A → {[i, u_i-check, A], [i, u_i-free]}` with two compound subtasks.
   That is allowed in TR if the second is of a lower stratum, but then each copy recurses
   independently, so the two decomposition sequences are again not tied together.

**Recommendation.** Before formalising, ask the author of the idea what mechanism makes the
inactive mode's tasks free. As stated, the construction does not go through with STRIPS FOND
actions. The undecidability of FM strong OD for TR (and Bercher-REG) stays open (❓). The
inherited result `undecidable_fm` (UNRES) is unaffected.

## Repair (suggested by the author, 2026-11-18): gated cheat tasks

Add cheat tasks "add f" / "del f" for every fact f of the *other* mode, a constant number inside
every method (so the supply grows with the chains; methods stay regular: primitives, then the
compound task last). Gating: cheats for word-mode facts require `cheatW`, which `init`'s
char-mode outcome adds; in word mode `cheatW` is only added by the final task `fin` (after the
genuine word checks), so the active mode's own cheats are idle until the end and then execute
harmlessly; symmetrically `cheatC`. `fin` requires both "chars matched" and "indices matched";
the inactive one is produced by cheats. The active check uses conjunctive preconditions with
lag 1 (`free`/`pending_x` handshake). Soundness: fixed methods commit both words before `init`
reveals the mode. This defeats the obstruction above (identical effects in both modes): the
cheats give the policy arbitrary control over the inactive mode's facts only.
Remaining: formalise; PCP undecidability (not in the library; from the two-stack machine).
