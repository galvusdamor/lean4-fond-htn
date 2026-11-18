# htn-complexity — Complexity results for HTN and STRIPS planning in Lean 4

Encodings of Turing machines and other machine models into planning problems, hardness families (non-uniform reductions to plan existence), bit codings of descriptions and polynomial time on them, verifiers for plan existence, decision procedures and bounds.

This repository is one of four that together formalise the compilability of HTN planning:

1. `complexity-theory` (`ComplexityTheory`) — complexity theory, independent of planning;
2. `htn-planning` (`HtnPlanning`) — definitions of STRIPS and HTN planning and basic lemmas;
3. `htn-complexity` (`HtnComplexity`) — complexity results for HTN and STRIPS planning;
4. `htn-compilability` (`HtnCompilability`) — compilability theory and proofs.

Each repository depends only on the ones before it (and on Mathlib).

## Dependencies

* [`complexity-theory`](../complexity-theory) (`ComplexityTheory`)
* [`htn-planning`](../htn-planning) (`HtnPlanning`)

The Lean toolchain is pinned in `lean-toolchain`; Mathlib is pinned to `v4.28.0`.

## Building

```
lake exe cache get   # Mathlib oleans
lake build
```

`lakefile.toml` refers to the repository below this one by a relative path (all four repositories
checked out side by side); a commented block shows the `git` form for use with GitHub.

The module `HtnComplexity` imports all modules of the repository.  It contains 476 modules.
