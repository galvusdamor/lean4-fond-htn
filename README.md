# lean-fond-htn — FOND HTN planning in Lean 4

Formalisation of fully observable nondeterministic (FOND) HTN planning, following

* [CB21] Chen & Bercher, ICAPS 2021 — *fixed methods* (`FONDFM`): weak/strong × linearisation-/outcome-dependent;
* [CB22] Chen & Bercher, ICAPS 2022 — *method-based policies* (`FONDMP`): weak / strong cyclic / strong;
* [DB25] Dekker & Behnke, ICAPS 2025 — solvable belief states (strong fixed-method solutions).

The papers are in `doc/`.

## Dependencies

Builds on the local `HtnPlanning` library (`../htn-split/htn-planning`, which pulls in
`ComplexityTheory`), reusing its task networks, methods, isomorphism, decomposition and problem classes.
Lean / Mathlib `v4.28.0`.

## Modules

| module | content |
| --- | --- |
| `FondHtn.Basic` | nondeterministic actions, domains, problems, well-formedness, problem classes (via the deterministic skeleton) |
| `FondHtn.FixedMethods` | [CB21] LD and OD solutions, [DB25] solvable belief states |
| `FondHtn.FixedMethodsLemmas` | strong OD solutions [CB21] ⇔ solvable belief states [DB25] |
| `FondHtn.MethodPolicies` | [CB22] method-based policies, execution structure up to isomorphism, weak / strong cyclic / strong solutions |

Deviations from the literal paper definitions (and why) are documented in the module docstrings.

## Building

```
lake build
```
