# lean-fond-htn — FOND HTN planning in Lean 4

Formalisation of fully observable nondeterministic (FOND) HTN planning, following

* [CB21] Chen & Bercher, ICAPS 2021 — *fixed methods* (`FONDFM`): weak/strong × linearisation-/outcome-dependent;
* [CB22] Chen & Bercher, ICAPS 2022 — *method-based policies* (`FONDMP`): weak / strong cyclic / strong;
* [DB25] Dekker & Behnke, ICAPS 2025 — solvable belief states (strong fixed-method solutions).

The papers are in `doc/`.

## Dependencies

Builds on the HTN formalisation libraries `HtnComplexity`, `HtnPlanning` and `ComplexityTheory`,
reusing their task networks, methods, isomorphism, decomposition, problem classes and complexity
theory. They are **vendored, read-only, in `deps/`** (see `deps/README.md`): do not modify them;
new material goes into `FondHtn/`. Lean / Mathlib `v4.28.0`.

Build: `lake exe cache get` (Mathlib) then `lake build`. Status: `STATUS.md`; open work: `TODO.md`.

## Modules

| module | content |
| --- | --- |
| `FondHtn.Basic` | nondeterministic actions, domains, problems, well-formedness, problem classes (via the deterministic skeleton) |
| `FondHtn.FixedMethods` | [CB21] LD and OD solutions, [DB25] solvable belief states |
| `FondHtn.FixedMethodsLemmas` | strong OD solutions [CB21] ⇔ solvable belief states [DB25] |
| `FondHtn.FixedMethodsRelations` | [CB21] Props. 2.12, 2.13 (⇒), 2.15 |
| `FondHtn.MethodPolicies` | [CB22] method-based policies, execution structure up to isomorphism, weak / strong cyclic / strong solutions |
| `FondHtn.IsoLemmas` | explicit isomorphisms, transport of progression/decomposition, simulation of policy steps |
| `FondHtn.MethodPoliciesStrong` | strong method-based solutions ⇔ AND/OR game |
| `FondHtn.Examples` | counterexample of [CB21] Prop. 2.13 (⇍), [CB22] Fig. 1 |

Deviations from the literal paper definitions (and why) are documented in the module docstrings and
in the report `modifications/main.tex` (JAIR template; build with `latexmk -pdf main.tex`).

## Building

```
lake build
```
