import HtnComplexity.Space.RegTable
import HtnComplexity.Space.Bridge
/-!
# Classes that reduce to an action table

`HtnComplexity/Space/StripsSystem.lean` recasts plan existence for `STRIPS` as reachability
in an action table, and `HtnComplexity/Space/RegTable.lean` carries a regular HTN problem
into that form.  This file names the *interface* the two produce, because it is the interface
every `PSPACE` target of Table 3 will be approached through:

    HTN.Space.TblReduction T :
      a table `tbl d` computed from the domain description alone,
      an initial state `init q` and a goal `goal q` computed from the instance description alone,
      a flag `live d` depending on the domain alone,
      with   Solvable d q ↔ live d ∧ SolvableTbl (tbl d) (init q) (goal q).

The split is the point.  In the machine of `ComplexityTheory/Space/Model.lean` the table and
the flag are read off the **advice** — the advice may therefore be an arbitrary polynomially long
function of the domain description, and no assumption on the cost of the domain compilation is
made anywhere — while the initial state and the goal are read off the **input**, the code of the
instance description, which is what a polynomial-time reading of the input has to manage.

`HTN.Space.regReduction` is the reduction for regular HTN with a rooted instance
(the target class of cells 2 and 7 of `TABLE3-PLAN.md`); its initial state and goal are
`q.initList.map (12 * ·) ++ [8 * rootName q + 1]` and `q.goalList.map (12 * ·) ++ [2]`, that is,
a fixed renaming of the facts of the instance plus two bookkeeping facts.

What is *not* here, and is the remaining work on the target side, is the machine itself: a
polynomial-time (Cobham) implementation of

1. "the configuration lists exactly the facts of `init q`", read off the code of `q`;
2. "some row of the table of the advice carries the configuration `c` to the configuration `c'`";
3. "the configuration contains every fact of `goal q`", again read off the code of `q`,

together with the encoding of the table into polynomially many advice bits.  The bound on the
configurations that the model requires is already available in the mathematics:
`HTN.Space.solvableTbl_iff_small` restricts the runs to duplicate-free states made of facts of
the initial state and of the add lists of the table, and `HTN.Space.length_le_of_nodup_subset`
bounds their length.
-/

namespace HTN

namespace Space

open Syn Table

/-- **A reduction of a class to an action table**: the table and the flag depend on the domain
description only, the initial state and the goal on the instance description only. -/
structure TblReduction {ℰ : Family} (T : SynClass ℰ) where
  /-- The action table of a domain description. -/
  tbl : DomDesc → List Row
  /-- A condition on the domain description alone, without which nothing is solvable. -/
  live : DomDesc → Prop
  /-- The initial state of an instance description. -/
  init : InstDesc → List ℕ
  /-- The goal of an instance description. -/
  goal : InstDesc → List ℕ
  /-- Plan existence is reachability in the table. -/
  correct : ∀ d q, T.domOk d → T.instOk q →
    (Solvable d q ↔ live d ∧ SolvableTbl (tbl d) (init q) (goal q))

/-- **Regular HTN with a rooted instance reduces to an action table** — the table is the action
table of the `STRIPS` domain Alford's translation produces, and the initial state and the goal
are a renaming of the initial state and the goal of the instance. -/
def regReduction : TblReduction SynClass.HTN_REG_root where
  tbl := regTable
  live := fun d => (regDom d).HasEmptyMethod
  init := regInit
  goal := regGoal
  correct := fun _ _ hd hq => solvable_reg_iff_solvableTbl hd hq

@[simp] theorem regReduction_tbl (d : DomDesc) : regReduction.tbl d = regTable d := rfl

@[simp] theorem regReduction_init (q : InstDesc) : regReduction.init q = regInit q := rfl

@[simp] theorem regReduction_goal (q : InstDesc) : regReduction.goal q = regGoal q := rfl

end Space

end HTN
