# complexity-theory — Complexity theory in Lean 4, independent of planning

Machine models (nondeterministic Turing machines, two-stack machines, counter machines, alternating machines with a polynomial memory), complexity classes (`P`, `NP`, the polynomial hierarchy, `PSPACE`, `APSPACE = EXPTIME`, `NEXPTIME`, `EXPSPACE`, with advice), Cobham's class and its equivalence with polynomial-time Turing machines, Savitch's theorem, collapse results, a primitive recursive diagonal language, Petri nets and vector addition systems, and the standard complexity-theoretic hypotheses.

This repository is one of four that together formalise the compilability of HTN planning:

1. `complexity-theory` (`ComplexityTheory`) — complexity theory, independent of planning;
2. `htn-planning` (`HtnPlanning`) — definitions of STRIPS and HTN planning and basic lemmas;
3. `htn-complexity` (`HtnComplexity`) — complexity results for HTN and STRIPS planning;
4. `htn-compilability` (`HtnCompilability`) — compilability theory and proofs.

Each repository depends only on the ones before it (and on Mathlib).

## Dependencies

* Mathlib only.

The Lean toolchain is pinned in `lean-toolchain`; Mathlib is pinned to `v4.28.0`.

## Building

```
lake exe cache get   # Mathlib oleans
lake build
```

`lakefile.toml` refers to the repository below this one by a relative path (all four repositories
checked out side by side); a commented block shows the `git` form for use with GitHub.

The module `ComplexityTheory` imports all modules of the repository.  It contains 174 modules.
