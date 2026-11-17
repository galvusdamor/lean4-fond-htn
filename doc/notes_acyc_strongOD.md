# CB21 Thm 5.2 lower bound: FM strong OD, acyclic, partial order — EXPSPACE-hardness (notes)

Status: **not formalised.** The time box was not enough. This note gives the construction I
consider viable and lists what a formalisation needs.

Target: `Cx.Hard Cx.EXPSPACE (PlanExFM .strongOD FClass.ACYC)`.
- Membership is proved: `strongOD_ACYC_mem`.
- The inherited lower bound is NEXPTIME.

## 1. Why fixed methods remove the commitment problem, and why that is not enough

- With fixed methods the planner picks one achievable primitive network, then an OD policy
  plays against nature. A committed decomposition cannot adapt to later outcomes. This is the
  obstacle of `doc/notes_cb22_thm2.md`, and here it disappears.
- **But it is too strong a commitment for Savitch- or challenge-style verification.**
  - The existential choices of an alternating exponential-time machine depend on earlier
    universal choices.
  - A committed network would have to contain the answers for every universal history. That is
    a tree of exponential depth, so doubly exponential size.
  - Acyclic networks have at most exponential size (ABA15 Cor 3.2).
  - The same objection rules out the planner committing to "midpoint configurations" of a
    2^(2^n)-step EXPSPACE computation: the midpoints depend on nature's choices of half.
- **Consequence.** After the decomposition, the existential power must lie in the **OD
  policy**, i.e. in the choice of which task to execute next. The universal power lies in
  nature's outcomes.
  - With **one method per compound name** (no decomposition choice at all) FM, MP strong and
    MP strong cyclic coincide. The ideas file makes this observation.
  - This is the "counters" construction of the ideas file, which extends ABA15 Thm 6.1 to
    alternation.

## 2. The construction: counters, made alternating

Source: an alternating Turing machine `M` with tape 2^n and time 2^n, i.e. AEXPTIME =
EXPSPACE. Encoding the alternation:
- existential states: the policy's choice;
- universal states: an action of the control chain with one outcome per transition.

The library has no ATMs. The available sources are `Space.InExpSpace` and EXPSPACE NTMs. So the
first step is a padding/alternation lemma, AEXPTIME ⊇ EXPSPACE: the Chandra–Kozen–Stockmeyer
simulation, formalised over the library's `TM.NTM`.

The network (`tn_I`) is a parallel composition of three kinds of components. Every compound
name has exactly one method. Doubling clocks `clk_j → [clk_{j-1}, clk_{j-1}]` produce the
exponential repetitions, so the hierarchy is acyclic and of polynomial size.

1. **Cells.** A σ-cell, for σ ∈ Γ, is a totally ordered chain
   `init_σ · (tick · resume)^(2^n - 1) · final_σ`.
   - Its clock is implicit: it is the position in the chain.
   - There are 2^(2n) cells of each symbol: 2^n atomic steps times 2^n global steps.
   - Each task's preconditions refer to global phase facts of the control:
     - `init_σ` needs `phase_init ∧ want_σ`;
     - `tick` needs `phase_inc` and adds `ticked`;
     - `resume` needs `phase_resume`;
     - `final_σ` needs `phase_final` and adds `read_σ`.
2. **Control.** One totally ordered chain for 2^n global steps × 2^n atomic steps. Per atomic
   step it runs:
   1. *finalize*: set `phase_final`; the policy must execute exactly one `final_σ` of some cell,
      which leaves `read_σ`;
   2. *compute*: from `read_σ`, the state facts `q` and the head-position counter, either copy
      the symbol (`want_σ`) or, at the head, apply a transition;
   3. *initialize*: set `phase_init`; the policy must execute one `init` of the requested
      symbol;
   4. *increment*: 2^n − 1 sub-steps; each sets `phase_inc`, and exactly one `tick` must happen
      (checked by `ticked`);
   5. *resume*: 2^n − 1 sub-steps of `phase_resume`.

   How the transition step (2) is chosen:
   - Existential states: the control step is a set of parallel alternatives guarded by `q`,
     and the policy picks one. Equivalently, the policy may execute any of several `apply_t`
     actions.
   - Universal states: the control action is nondeterministic, one outcome per transition, so
     nature picks.
3. **Cheat/trash.** Once an accepting state is reached, a flag `acc` enables "cheat" versions
   of every remaining task (unused cells, remaining control), so the network can be emptied.
   This is the "backup and trash" mechanism of the ideas file and DB25.

**Invariant (the heart of ABA15 Thm 6.1).** At the start of each atomic step, the live cells
(initialised and not yet finalised) are exactly 2^n − 1 cells with pairwise distinct clock
values 0 … 2^n − 2, plus none at 2^n − 1. Why it holds:
- In the increment loop each live cell ticks exactly once. A cell that has ticked is "paused":
  its next task is `resume`, which is blocked until the resume loop. There are exactly
  2^n − 1 increments and 2^n − 1 live cells.
- So after the loop the oldest cell sits at clock 2^n − 1 and is the only one whose next task
  is `final`. "Find the cell whose clock is 2^n − 1" is therefore forced. Its symbol is the
  tape cell under the rotating read position, so the tape is a FIFO queue of length 2^n.

A strong OD solution thus corresponds to an ATM strategy that accepts on every universal
branch, and vice versa.

## 3. What a formalisation needs (why it did not fit the time box)

1. **ATM source.** EXPSPACE ⊆ AEXPTIME (CKS), over `TM.NTM`/`Space.InExpSpace`, with a PT
   encoding. Alternatively, use DB25's chosen-length planning games (EXPSPACE-complete) if
   `FondHtn/DB25/` provides them. A game "Éloise vs Abélard for r = 2^n·poly moves on a STRIPS
   state" is too weak because its state is polynomial. Chosen-length games do not encode
   exponential tapes directly either, so the counter cells are still needed.
2. **Semantics of strong OD on a PO network with exponentially many parallel chains.** The
   library has `FOND.Problem.strongOD_iff_beliefSolvable`, a least fixpoint over
   (remaining network, state).
   - An abstraction is needed from (remaining network, state) to a *configuration*: the
     multiset of live cells by (symbol, clock), unused cells by symbol, control position,
     state facts.
   - The invariant of §2 must be proved for every policy, including adversarial interleavings.
     This is the hard combinatorial core; ABA15 only argues it informally.
3. **Doubling clocks for PO networks.** The clocks of `FondHtn/HardMP/` are totally ordered.
   Here we need `2^(2n)` parallel cell chains and chains of length 2^n, i.e. a parallel
   doubling `par_j → {par_{j-1}, par_{j-1}}`, together with a sequence-network-style
   description of PO networks. The list game of `Bridge.lean` handles only sequences; it needs
   a multiset-of-sequences version.
4. **PT layer** in the style of `FondHtn/HardMP/PT.lean`.

## 4. Cheaper partial targets

* The ATM-free half: a deterministic version gives NEXPTIME-hardness, which is already
  inherited, so it has no value by itself. It would be a useful milestone for the invariant
  proof.
* A semantic lemma independent of the machine: "in the cell/control network with
  `phase_*` facts, every strongly winning policy realises the FIFO queue". This could be
  stated and proved first on an abstract model (multisets of clock values) before the HTN
  layer.
