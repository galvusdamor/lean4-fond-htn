import HtnComplexity.Guard.TaskGuard
/-!
# The hypotheses of the method-guard theorem are satisfiable

`HTN.GuardTask.solvable_guardTasks_iff` carries a list of hypotheses — the two method sets
correspond, the guard ids are fresh, the guard actions are no-ops whose preconditions are facts
that hold initially and that no action deletes.  This file instantiates all of them, so that the
theorem is not a statement about an empty situation.

The example is the smallest one that shows the construction at work: one compound task, one
method whose body is a single action, and one guard task in front of it.
-/

namespace HTN

namespace GuardTask

namespace Ex

/-- The body of the only method: the single primitive task `0`, labelled by the action `1`. -/
def body : TaskNetwork ℕ ℕ ℕ where
  T := {0}
  ord := fun _ _ => False
  α := fun _ => Sum.inl 1

/-- The only method: it decomposes the compound task `0` into `body`. -/
def meth : Method ℕ ℕ ℕ where
  abstractTask := 0
  subtasks := body

/-- The guard id of the method: an id outside its body. -/
def gid : Method ℕ ℕ ℕ → ℕ := fun _ => 1

/-- The guard action of the method: the action `0`, whose precondition is the fact `0`. -/
def gact : Method ℕ ℕ ℕ → ℕ := fun _ => 0

/-- The action model: the guard action `0` asks for the fact `0` and does nothing, the action
`1` adds the fact `1`. -/
def model : ActionModel ℕ ℕ where
  prec a := if a = 0 then {0} else ∅
  add a := if a = 1 then {1} else ∅
  del _ := ∅

/-- The original domain. -/
def dom : Domain ℕ ℕ ℕ ℕ where
  toActionModel := model
  methods := {meth}

/-- The guarded domain: the same actions, the method with its guard task. -/
def domG : Domain ℕ ℕ ℕ ℕ where
  toActionModel := model
  methods := {guardMethod gid gact meth}

/-- The instance: the fact `0` holds, the goal is the fact `1`, the initial network is the
compound task `0`. -/
def inst : Instance ℕ ℕ ℕ ℕ where
  init := {0}
  goal := {1}
  tnI := { T := {0}, ord := fun _ _ => False, α := fun _ => Sum.inr 0 }

lemma body_wf : body.WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma tnI_wf : inst.tnI.WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

/-- **The hypotheses of the method-guard theorem are jointly satisfiable.** -/
theorem solvable_guardTasks_iff_ex :
    (domG.mkProblem inst).Solvable ↔ (dom.mkProblem inst).Solvable := by
  refine solvable_guardTasks_iff (G := {0}) (gid := gid) (gact := gact) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    tnI_wf
  · rintro m hm
    have : m = meth := hm
    subst this
    exact rfl
  · rintro mg hmg
    have : mg = guardMethod gid gact meth := hmg
    exact ⟨meth, rfl, this⟩
  · rintro m hm
    have : m = meth := hm
    subst this
    exact body_wf
  · rintro m hm
    have : m = meth := hm
    subst this
    simp [gid, meth, body]
  · rintro m hm
    have : m = meth := hm
    subst this
    refine ⟨?_, rfl, rfl⟩
    simp [gact, dom, model]
  · intro a f hf
    simp [dom, model]
  · simp [inst]

end Ex

end GuardTask

end HTN
