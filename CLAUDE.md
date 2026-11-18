# Instructions for agents working in this repository

* **Never modify files under `deps/`** (vendored copies of ComplexityTheory, HtnPlanning,
  HtnComplexity; see `deps/README.md`). Put all new definitions and lemmas into `FondHtn/`.
* Status of the formalisation: `STATUS.md`; open work: `TODO.md`; deviations from the papers:
  `modifications/main.tex`; proof plans and obstructions: `doc/notes_*.md`.
* Build single modules with `lake build FondHtn.<Module>` or `lake env lean <file>`.
* No `sorry`, no new axioms.
