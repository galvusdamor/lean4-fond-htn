# TO MP strong is 2-EXPTIME-hard: construction (ideas file "Total order — Hardness", reworked)

Target: `Cx.Hard Cx.EXPTIME2 (PlanExMP .strong FClass.TO)`.
- Membership: `strongMP_TO_mem`.
- `HTN.Cx.EXPTIME2` is P on doubly exponentially padded inputs (`FondHtn/Cx/Exp2.lean`).

Status: the construction is fully specified here. Proof plan and formalisation status are in
§6–7.

## 0. Source and abstraction

As in `HTN.Article.thm_4_3_6` (`Article/TOHard.lean`), but one exponential higher:
- `L ∈ EXPTIME2` gives `padLang2 q L ∈ P`, hence a deterministic single-tape machine `M`
  (`Mach.exists_dtm_of_inP`).
- `M` decides `padLang2 q L` in polynomial time `r`.
- On the padded word `w = padExp2 q x`, of length `c₂ ≈ 2|x| + 2 + 2^(2^q(|x|))`, it runs for
  at most `r(c₂) < 2^D` steps, where `D = 2^b` and `b` is polynomial in `|x|`.

The run is abstracted exactly as in TOHard by **`HTN.Article.TabData.Good d tabC`**:
- a tableau `tabC t i` with `t, i < 2^(d.B)`;
- a first row given by `c₁, c₂, baseU, codeTrue, codeNone`;
- local rules `mid` (interior), `lft` (cell 0), `rgt` (cell `mx = 2^B − 1`);
- accepting codes `acc`.

`Good` is a property of the table only, so it can be instantiated with **`d.B := D = 2^b`**. The
proof of `TOHard.good_dOf` uses the padding only through `N = 2^(q(|x|))`. Copying it with
`N = 2^(2^q)` (the padded word `pairStr x (replicate N true)` = `padExp2 q x`) gives
`Good (dOf M Bl x N) (tab of M on padExp2 q x)` with `Bl.length = D`.

**What is new.** Coordinates are `D`-digit numbers with `D = 2^b`. A digit index has `b` bits
and fits in the state. The numbers themselves never do.

## 1. State

Fields of a configuration, encoded as in `FondHtn/HardMP/Encoding.lean`:

| field | meaning |
| --- | --- |
| `CHECK_r`, `r < b` | the challenged digit `Check`, set by nature exactly once per run, at the bottom of the recursion |
| `CTR_r`, `r < b` | the digit counter `d` of the verification chain currently running |
| `EQ` | `d = Check`, recomputed for every digit |
| `TB`, `IB` | digit `Check` of the time `t` and of the cell `i` of the current claim |
| `SYM_a` | the symbol claimed (one-hot) |
| `MODE_L / MODE_C / MODE_R` | nature's challenge (which predecessor cell) |
| `PH_*` | phase bits of the digit automata (§3) |

## 2. Claims

The compound task **`K`** ("claim") is executed from a *clean* configuration: `CHECK`,
`CTR`, `PH` all false. Its intended meaning is:

> **Claim(t, i, a):** the policy can execute `K` such that every leaf has `SYM = a`,
> `TB = t[Check]` and `IB = i[Check]`, and `tabC t i = a`.

The numbers are not chosen anywhere explicitly. They are *defined* by the requirements of the
enclosing level, and the universal choice of `Check` forces consistency across all digits.

## 3. Verification chains: deterministic programs over all digits

A **digit type** is a tuple of local relations, one per tracked number. All relations needed
are built from the following, where `z` is the input bit (from the inner claim), `o` the output
bit and `K[d]` a constant digit:

| relation | types (low → high) | automaton (regular, checked by `PH`) |
| --- | --- | --- |
| `o = z + 1` (Inc) | `lo` (z=1, o=0), `at` (z=0, o=1), `hi` (o=z) | `lo* at hi*` |
| `o = z − 1` (Dec) | `lo` (z=0, o=1), `at` (z=1, o=0), `hi` (o=z) | `lo* at hi*` |
| `o = z` (Copy) | `cp` | `cp*` |
| `o ≥ K` (constant) | `fr` (free), `wt` (o=1, K=0), `eq` (o=K) | `fr* wt eq* \| eq*` |
| `o < K` | `fr`, `wt'` (o=0, K=1), `eq` | `fr* wt' eq*` |
| `o = K` | `eq` | `eq*` |

The verification chain of one level, for committed types `τ₀ … τ_{D−1}`, is the program
`∏_{d < D} [phase(τ_d); cmp_0 … cmp_{b−1}; act(τ_d); inc]` followed by
`[final: CTR all ones, accepting phases; reset CTR, PH]`:
- `cmp_r` is deterministic: four single-action alternatives keyed on `CTR_r`/`CHECK_r`. It
  clears `EQ` on a mismatch (`EQ` is set before `cmp_0`).
- `act(τ)` has alternatives `¬EQ` (no-op) or `EQ ∧ (the relation of τ at this digit)`. Its
  effects transform `TB`/`IB` (the input is the current value, the output is written in
  place).
- Constant digits `K[d]`: `K` has few set digits (`c₁` small; `c₂` has
  `ones(|prefW| + 1) ∪ {2^q}`). So "`K[Check] = 1`" is an alternative per set digit `e`
  (precondition `CHECK = e`, a conjunction). "`K[Check] = 0`" is a chain of disequality
  witnesses, one per `e`.

Every instruction is a list of single-action alternatives. The chain is therefore a *program*
in the sense of `FondHtn/HardMP/Encoding.lean` (`wpP`).

**Key lemma (chain).** For clean `CTR`/`PH` and `c = Check`: `config ∈ wpP(chain τ) Ψ` iff
1. `τ` is accepted by the automata (independent of `Check`); and
2. for the relation of `τ_c`, the input bits at `c` satisfy its precondition; and
3. the configuration with `TB`, `IB` transformed by `τ_c` (and `CTR`, `PH`, `EQ` reset) lies
   in `Ψ`.

The proof is an induction over `d` with invariant "`CTR = d`, `PH` = automaton state after
`τ_{<d}`, `EQ` recomputed".

**Arithmetic lemmas.** For `τ ∈ lo* at hi*` (Inc) with `p` the position of `at`, and digit
functions `z, o : Fin D → Bool`: `∀ c, o c = Inc_τ(c, z c) ∧ pre` iff `o = z + 1` as `D`-digit
numbers, with no overflow; similarly for Dec and the comparisons.

## 4. The methods (all networks totally ordered)

**Commitment by left recursion.** For each kind of level, `Λ → [Λ, G(τ)] | [Body, G(τ)]`,
with one method per type `τ`:
- `G(τ)` is a compound with the single method `G(τ) → chain instructions for one digit`.
- In the leftmost (progression) game, which is equivalent to MP strong (`Bridge.lean`), the
  policy must expand `Λ` completely before anything in `Body` executes.
- So the whole type sequence is **committed before** nature chooses the mode and `Check`. This
  is the commitment mechanism of the ideas file (`<preserve>`/`<transition>` recursion), and
  it is sound because delaying is impossible: the inner claim is generated by the last
  expansion.

Methods of `K`:

* **Step, interior rule `q = (a, l, c, r) ∈ mid`:** `K → [Λ_q]` with
  `Body_q = [pickMode(L/C/R), Sub_q]`, and
  `Sub_q → [assert MODE_L, K, assert SYM_l] | [MODE_C, K, SYM_c] | [MODE_R, K, SYM_r]`.

  The types are triples `(time: Inc, index: Inc under MODE_L / Copy under MODE_C / Dec under
  MODE_R)`. The index act is guarded by the mode bit, so all three relations are committed at
  once. The final instruction after the chain sets `SYM := a`.
  - The inner claim for `L` is `(t − 1, i − 1)`, i.e. `t = t' + 1`, `i = i' + 1`.
  - For `R` it is `(t − 1, i + 1)`, i.e. `i = i' − 1`.
  - `0 < i < mx` is enforced automatically: Inc has no accepting run on the all-ones input,
    and Dec none on the all-zeros input.
* **Step, rule `q ∈ lft` (cell 0):** modes `C`, `R` only. The final instruction asserts
  `¬IB`, so `i[Check] = 0` for all `Check`.
* **Step, rule `q ∈ rgt` (cell `mx`):** modes `L`, `C`. The final instruction asserts `IB`.
* **Base, `t = 0`, prefix cell `c < c₁`:** `K → [pickCheck_0 … pickCheck_{b−1}, set ¬TB,
  set SYM_{baseU c}, IBconst(c)]`. `pickCheck_r` is nondeterministic (add `CHECK_r` / nothing).
  `IBconst(c)` sets `IB := c[Check]` (an alternative per set bit of `c`, or witnesses of
  `Check ∉ ones(c)`).
* **Base, `c₁ ≤ i < c₂`:** `K → [Λ_tru]` with `Body = [pickCheck…, set ¬TB, SYM_codeTrue,
  guessIB]`.
  - `guessIB` is a free choice of the bit.
  - The types are pairs `(o ≥ c₁, o < c₂)` acting on `IB` (checks only).
* **Base, `i ≥ c₂`:** the same with `(o ≥ c₂)` and `SYM_codeNone`.
* **Root** (`tn_I = [Root]`): `Root → [Λ_root]` with
  `Body = [K, assert TB, assert SYM_a]` for `a ∈ acc`.
  - The types are `(o = guessed bit)`, i.e. the root commits the digits of `i` (`eqK` with a
    per-digit committed bit).
  - `TB = 1` for all `Check` means `t = mx`.

**Deviations from the ideas file.**
1. The tableau abstraction `TabData` replaces the separate **Tape**/**Machine** claims and
   `<preserve>`/`<transition>`. Every cell, including the head, is one entry of the CKS
   tableau, so one kind of claim suffices.
2. Three-way challenge (`L/C/R`) instead of `TAPEMODE/MACHMODE`.
3. Deterministic `EQ` recomputation instead of `<addmaybe>/<delmaybe>` with policy-chosen
   disequality witnesses. Same effect, but programs become straight-line and fit `wpP`.
4. The input enters through the first-row rules of `TabData`, with comparisons against
   doubly exponential constants with few set digits. The ideas file assumes an empty tape.
5. Exact length `D` of each chain is enforced by the counter: `final` requires `CTR` all ones.

## 5. Correctness (proof plan)

**Soundness.** By induction on the height of `LRunH n [K] (enc c₀) Φ`, for clean `c₀`. If
every configuration in `Φ` lies in `Pin(t, i, a)` = {`Check` set, `TB = t[Check]`,
`IB = i[Check]`, `SYM = a`}, then `tabC t i = a`.
- *Step.* Unfold `K → Λ`. The left-recursion lemma gives a type sequence `τ` with
  `LRunH (Body ++ G(τ…) ++ final)`. `pickMode` is followed by the inner `K` with
  postcondition `Ψ_k = wpP(chain τ ++ final) Φ`.
  - By the chain lemma, every configuration in `Ψ_k` has `TB_in = Inc_τ^{-1}(t[Check])` and
    `IB_in = …`. Define `t' := t − 1` and `i' := i ∓ 1` digitwise via the arithmetic lemmas;
    acceptance of `τ` gives the exact numeric relation.
  - So `Ψ_k ⊆ Pin(t', i', SYM_k)`. The induction hypothesis gives the three predecessor
    entries, and `Good.mid_s` (`lft_s`, `rgt_s`) gives `tabC t i = a`.
- *Base.* The program semantics is exact. Since `Check` ranges over all `b`-bit values by
  `pickCheck` (all outcomes), `Pin` forces `t[c] = 0` for all `c`, i.e. `t = 0`, and the
  comparisons force `i` into the right region. `Good.base/tru/non` finish.
- *Root.* `Pin` with `t = mx`, the committed `i`, `a ∈ acc`.

**Completeness.** By induction on `t`. For every `t, i < 2^D` and every requirement
postcondition `Φ ⊇ Pin(t, i, tabC t i)`, `LRun [K] (enc c₀) Φ` holds for clean `c₀`.
- Choose the method by `Good.mid_c` (`lft_c`, `rgt_c`) or by the first-row region.
- Choose `τ` from the actual carry positions of `t − 1 → t` and `i ± 1 → i`.

Then MP strong solvability of the description ⇔ `∃ i < 2^D, tabC mx i ∈ acc` ⇔ (copy of
`solvable_dOf_iff`) `M` accepts `padExp2 q x`. The class is TO: all networks are sequences
(`seqTn`).

**PT.** All names are polynomial:
- digit types are finite tuples;
- constants are `b`-bit numbers (set digits of `c₁, c₂`);
- `D = 2^b` never appears explicitly, only `b` (the counter width).

So the description is PT in `x` as in `TOHardPT.lean`/`FondHtn/HardMP/PT.lean`, with `b` given
in unary as a list length (`exists_pt_polyLen`).

## 6. Formalisation plan (reusing `FondHtn/HardMP/`)

1. `Encoding.lean` (`Cfg`, `ASpec`, `toFAct`, `wpP`, block lemmas) is reused unchanged. Each
   instruction becomes a compound task with one single-action method per alternative, as in
   `Desc.lean` (`cN r pc`). The chain/list lemmas of `Sem.lean` carry over with compound
   names for instructions instead of program states.
2. New: the digit-chain program and its key lemma (§3); arithmetic of digit functions; the
   left-recursion lemma for `Λ` in the list game (`LRunH (Λ :: xs) ↔ ∃ τ ≠ [], LRunH (Body ++
   G τ ++ xs)`).
3. Soundness and completeness of `K` (§5); root; machine link (copy of `good_dOf` and
   `solvable_dOf_iff` for `padExp2`).
4. Validity, the class TO, PT, and `thm`: `HTN.Cx.EXPTIME2`-hardness via `RedP` from
   `padLang2`.

   This needs a version of the TOHard argument with `Cx.padExp2`: `L ∈ EXPTIME2` gives
   `padLang2 q L ∈ P`, hence a DTM. The reduction `x ↦ desc(x)` is PT, and correctness is
   `L x ↔ solvable`.

## 7. Status

Not formalised; this note is the deliverable of the time-boxed attempt. The construction above
has been checked by hand at the level of §5. The riskiest parts are:
- the chain lemma's invariant, in particular the interaction of the phase automaton for
  several relations at once with the guarded index relations;
- the exact-length enforcement.

Both are finite-state arguments over `d` and look routine. The estimated size is of the order
of `FondHtn/HardMP/` times two to three, about 5–8k lines including PT.
