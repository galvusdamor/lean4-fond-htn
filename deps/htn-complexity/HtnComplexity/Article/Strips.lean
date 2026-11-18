import HtnComplexity.Article.PlanEx
import HtnComplexity.PT.Lang
/-!
# STRIPS planning problems

The hardness results of Section 4.3 start from classical (STRIPS) planning.  A STRIPS problem
`(D, s_I, g)` with `D = (V, N_P, δ)` is described by its actions (`HTN.Article.ActDesc`, with
`prec⁺`, `prec⁻`, `eff⁺`, `eff⁻`), the initial state and the goal `(g⁺, g⁻)`
(`HTN.Article.StripsDesc`).  A plan is a sequence of declared action names that is executable
from the initial state and ends in a goal state (`HTN.Article.StripsDesc.Solvable`); the language
`HTN.Article.PlanExSTRIPS` collects the codes of the well-formed (distinct action names) solvable
problems.

The semantics is that of the article's model: a STRIPS problem is read as the problem
`HTN.Article.StripsDesc.toProbDesc` with no methods and an empty initial task network, so that
the actions, the state transition and the goal test are literally those of Section 2.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-- **A STRIPS problem description**: actions, initial state, `g⁺`, `g⁻`. -/
abbrev StripsDesc : Type := List ActDesc × List ℕ × List ℕ × List ℕ

namespace StripsDesc

/-- The actions. -/
def actions (d : StripsDesc) : List ActDesc := d.1
/-- The initial state. -/
def init (d : StripsDesc) : List ℕ := d.2.1
/-- The positive goal. -/
def goalPos (d : StripsDesc) : List ℕ := d.2.2.1
/-- The negative goal. -/
def goalNeg (d : StripsDesc) : List ℕ := d.2.2.2

/-- The empty task network. -/
def emptyTn : TnDesc := ([], [], [])

/-- The STRIPS problem as a problem of the article's model without methods. -/
def toProbDesc (d : StripsDesc) : ProbDesc := ((d.actions, []), (d.init, emptyTn, d.goalPos, d.goalNeg))

/-- **Plan existence**: a sequence of declared actions leads from the initial state to a goal
state. -/
def Solvable (d : StripsDesc) : Prop :=
  ∃ π : List ℕ, (∀ a ∈ π, d.toProbDesc.Declared a) ∧
    ∃ s, d.toProbDesc.toProblem.Run π {f | f ∈ d.init} s ∧ d.toProbDesc.toProblem.GoalState s

end StripsDesc

/-- A STRIPS description is well formed iff its action names are distinct. -/
def StripsDesc.Valid (d : StripsDesc) : Prop := (d.actions.map ActDesc.name).Nodup

/-- **The plan-existence language of STRIPS**: the codes of well-formed, solvable problems. -/
def PlanExSTRIPS : Cx.Language := codeLang StripsDesc fun d => d.Valid ∧ d.Solvable

end Article

end HTN
