# htn-planning — Definitions of STRIPS and HTN planning in Lean 4, with basic lemmas

Classical (STRIPS) planning and planning with conditional effects; HTN planning: task networks, methods, decomposition, problems and solutions, the structural problem classes (totally ordered, regular, tail-recursive, acyclic, unordered, one-hole-digging, two-hole-digging, loop-unrolling, ...); finite descriptions of domains and instances and their classes; normal forms, progression search, interleavings and the basic lemmas about decomposition.

This repository is one of four that together formalise the compilability of HTN planning:

1. `complexity-theory` (`ComplexityTheory`) — complexity theory, independent of planning;
2. `htn-planning` (`HtnPlanning`) — definitions of STRIPS and HTN planning and basic lemmas;
3. `htn-complexity` (`HtnComplexity`) — complexity results for HTN and STRIPS planning;
4. `htn-compilability` (`HtnCompilability`) — compilability theory and proofs.

Each repository depends only on the ones before it (and on Mathlib).

## Dependencies

* [`complexity-theory`](../complexity-theory) (`ComplexityTheory`)

The Lean toolchain is pinned in `lean-toolchain`; Mathlib is pinned to `v4.28.0`.

## Building

```
lake exe cache get   # Mathlib oleans
lake build
```

`lakefile.toml` refers to the repository below this one by a relative path (all four repositories
checked out side by side); a commented block shows the `git` form for use with GitHub.

The module `HtnPlanning` imports all modules of the repository.  It contains 85 modules.
