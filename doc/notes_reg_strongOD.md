# FM strong OD for Bercher-regular problems (`FClass.REG`): why the EXPSPACE argument does not extend

Status: **no membership claim.** What is formalised is CB21 Thm 5.3 for `FClass.REGtn`, where
`tn_I` is regular too: `FOND.strongOD_REGtn_mem : Cx.EXPSPACE (PlanExFM .strongOD FClass.REGtn)`
(`FondHtn/StrongOD/Reg.lean`). For Bercher's `FClass.REG`, where `tn_I` is arbitrary, the
expectation is **undecidability**: see `doc/notes_pcp_strongOD.md` and the PCP formalisation in
progress under `FondHtn/PCP/` (instances `tn_I = [init] ≺ {A, B}` with two unordered regular
chains).

## What the REGtn proof uses

1. Every achievable primitive network is a *sequence* of blocks `B₀ ≺ B₁ ≺ … ≺ B_ℓ`. Each block
   is the primitive part of `tn_I` or of a method, and every task of a block precedes every task
   of the next one (`FOND.SOD.prefix_decDesc`).
2. Sequential composition (`FOND.SOD.bsw_comp`): solvability of `X ; Y` from `s` is the same as
   solvability of `X` from `s` with every leaf in `{s' | Y solvable from s'}`.
3. Therefore a single *cut* between consecutive blocks carries everything the future needs: the
   set `S_i` of states in which execution can be when block `i` starts. The method chain is fixed
   in advance (fixed methods), and the belief sets are guessed forward
   (`FOND.SOD.strongOD_iff_nw`). The search configuration is (current name, belief set): finite,
   of exponential size.

## Where `FClass.REG` breaks this

With `tn_I = init ≺ {c₁, c₂}`, `c₁` and `c₂` unordered, the achievable primitive networks have the
shape

    init ≺ ( B¹₁ ; B¹₂ ; … ; B¹_ℓ₁ )  ∥  ( B²₁ ; B²₂ ; … ; B²_ℓ₂ )

The two chains are sequences of blocks, but nothing orders a block of chain 1 against a block of
chain 2.

* There is **no global cut.** An OD policy chooses the interleaving per branch. After some
  outcomes it may have run three blocks of chain 1 and none of chain 2, after others one block of
  each. Step 2 needs every task of the prefix to precede every task of the rest, and no "frontier"
  of the two chains has that property. A sound decomposition must quantify over all down-closed
  frontiers `(i, j)` (block `i` of chain 1, block `j` of chain 2) at once.
* **Product search over tuples.** The natural generalisation is one current name per chain and a
  joint belief object.
  * The method choices of the chains are fixed in advance (fixed methods), but the policy's
    position in the chains varies per branch.
  * The joint belief object must therefore record, for each pair of positions `(i, j)` that some
    branch can occupy, the states possible there. Positions are unbounded, since chains are
    recursive.
  * The difference `i − j` (the "lag") is unbounded, so no finite family of joint belief sets
    indexed by a bounded window of positions suffices.
  * This is exactly the freedom the PCP construction uses: two chains generate the two words, and
    the policy must align them, against the interleaving forced by the other mode. Bounding the
    lag would decide PCP.
* Consequently the product search over (name₁, name₂, joint belief set), with steps that
  decompose one chain, is **not sound**: it implicitly assumes both chains cross block boundaries
  at the same time in every branch.

## Summary

| class | status |
| --- | --- |
| `REGtn` (CB21 Def. 3.3, DB25) | ∈ EXPSPACE, formalised (`strongOD_REGtn_mem`) |
| `REG` (Bercher, `tn_I` arbitrary) | expected undecidable (PCP; `FondHtn/PCP/`, `doc/notes_pcp_strongOD.md`); no membership |

If the PCP reduction does not work out, the next candidate argument is the following.
Restricted to `tn_I` with *one* compound task plus arbitrary primitive tasks (unordered with
respect to the chain), the same cut argument applies once the primitive part of `tn_I` has been
merged into the first block. In that case the frontier is still a single position in a single
chain, interleaved with a bounded set of primitive tasks. With two or more compound tasks in
`tn_I` it fails as described above.
