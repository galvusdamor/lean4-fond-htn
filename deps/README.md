# Vendored dependencies — DO NOT MODIFY

This directory contains verbatim copies of the HTN formalisation libraries this project builds on.
They are vendored so that the repository builds on its own.

| directory | Lean library | source commit |
| --- | --- | --- |
| `complexity-theory/` | `ComplexityTheory` | `dc376f2586c76583e2f4b66ca716891ddb36f54b` |
| `htn-planning/` | `HtnPlanning` | `7a0c3edd3d7d5542c4c8b88dce35f83599027989` |
| `htn-complexity/` | `HtnComplexity` | `9f081f15fdca2f4a3c6ea3cb9906cd86817409e5` |

Copied (sources only, without `.git` and build outputs) from the upstream repositories
(local checkout `htn-split/`), on 2026-11-18.

**Rules**

* **Do not edit anything under `deps/`.** This project is not allowed to change these libraries.
  Everything new goes into `FondHtn/` — if a lemma about a library definition is missing, prove it
  in `FondHtn/` (that is what e.g. `FondHtn/Cx/Closure.lean` does for closure under reductions).
* To update a dependency, replace the whole directory by a fresh copy of the upstream repository
  and record the new commit in the table above; never patch files in place.
* The three libraries reference each other by relative paths (`../htn-planning`,
  `../complexity-theory`), which is why they sit side by side here. The root `lakefile.toml`
  requires `deps/htn-complexity`, which pulls in the other two.
