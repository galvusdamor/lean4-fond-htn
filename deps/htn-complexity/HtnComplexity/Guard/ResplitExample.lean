import HtnComplexity.Guard.MethodGuard
/-!
# The hypotheses of the method-guard re-split are satisfiable

`HTN.GuardTask.solvable_methodGuard_resplit_iff` moves the choice of a *method* out of the domain
and into the instance.  This file instantiates all of its hypotheses on the smallest example that
shows the construction at work — one compound task, two methods (one per letter of a two-letter
alphabet), and an instance whose initial state admits the first of them — so that the theorem is
not a statement about an empty situation.
-/

namespace HTN

namespace GuardTask

namespace Ex2

/-- The body that writes the letter `a`: the single primitive task `0`, labelled `a`. -/
def body (a : ℕ) : TaskNetwork ℕ ℕ ℕ where
  T := {0}
  ord := fun _ _ => False
  α := fun _ => Sum.inl a

/-- The method that writes the letter `a` for the compound task `0`. -/
def meth (a : ℕ) : Method ℕ ℕ ℕ where
  abstractTask := 0
  subtasks := body a

/-- The guard id of a method: an id outside its body. -/
def gid : Method ℕ ℕ ℕ → ℕ := fun _ => 1

/-- The guard action of a method: `10` for the method writing `0`, `11` for the other one. -/
def gact : Method ℕ ℕ ℕ → ℕ := fun m => if m.subtasks.α 0 = Sum.inl 0 then 10 else 11

/-- The action model: the guard actions `10` and `11` ask for their own fact and do nothing, the
letter actions `0` and `1` record the letter they wrote. -/
def model : ActionModel ℕ ℕ where
  prec a := if a = 10 then {10} else if a = 11 then {11} else ∅
  add a := if a = 0 then {0} else if a = 1 then {1} else ∅
  del _ := ∅

/-- The family domain before guarding: one method per letter. -/
def dall : Domain ℕ ℕ ℕ ℕ where
  toActionModel := model
  methods := {meth 0, meth 1}

/-- The domain of the word `0`: only the method writing `0`. -/
def dspec : Domain ℕ ℕ ℕ ℕ where
  toActionModel := model
  methods := {meth 0}

/-- The guarded family domain. -/
def dfam : Domain ℕ ℕ ℕ ℕ where
  toActionModel := model
  methods := (fun m => guardMethod gid gact m) '' {meth 0, meth 1}

/-- The instance: nothing holds initially, the goal is "the letter `0` was written". -/
def inst : Instance ℕ ℕ ℕ ℕ where
  init := ∅
  goal := {0}
  tnI := { T := {0}, ord := fun _ _ => False, α := fun _ => Sum.inr 0 }

lemma body_wf (a : ℕ) : (body a).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma tnI_wf : inst.tnI.WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma meth_ne : meth 1 ≠ meth 0 := by
  intro hcon
  have hb : body 1 = body 0 := congrArg Method.subtasks hcon
  have : (body 1).α 0 = (body 0).α 0 := by rw [hb]
  simp [body] at this

lemma gact_zero : gact (meth 0) = 10 := by simp [gact, meth, body]

lemma gact_one : gact (meth 1) = 11 := by simp [gact, meth, body]

/-- **The hypotheses of the method-guard re-split are satisfiable.** -/
theorem solvable_methodGuard_resplit_iff_ex :
    (dfam.mkProblem ⟨inst.init ∪ {10}, inst.goal, inst.tnI⟩).Solvable ↔
      (dspec.mkProblem inst).Solvable := by
  refine solvable_methodGuard_resplit_iff (Dall := dall) (G := {10, 11}) (Gw := {10})
    (gid := gid) (gact := gact) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ tnI_wf
  · -- the word's methods are among the family's
    rintro m hm
    have hm0 : m = meth 0 := hm
    subst hm0
    exact Or.inl rfl
  · -- every family method is guarded in `dfam`
    intro m hm
    exact ⟨m, hm, rfl⟩
  · -- every method of `dfam` is a guarded family method
    rintro mg ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · -- the bodies are well formed
    rintro m (rfl | rfl) <;> exact body_wf _
  · -- the guard ids are fresh
    rintro m (rfl | rfl) <;> simp [gid, meth, body]
  · -- the guard actions are no-ops asking for a guard fact
    rintro m (rfl | rfl)
    · refine ⟨?_, ?_, ?_⟩ <;> simp [gact_zero, dall, model]
    · refine ⟨?_, ?_, ?_⟩ <;> simp [gact_one, dall, model]
  · -- the instance admits exactly the methods of the word
    rintro m (rfl | rfl)
    · simp only [gact_zero]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      simp [dall, model]
    · simp only [gact_one]
      constructor
      · intro hm
        exact absurd (hm : meth 1 = meth 0) meth_ne
      · intro hcon
        have h11 : (11 : ℕ) ∈ ({10} : Set ℕ) := by
          refine hcon ?_
          simp [dall, model]
        simp at h11
  · -- the word's facts are guard facts
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    simp [hf]
  · -- no action adds a guard fact
    intro a f hf
    by_cases h0 : a = 0
    · subst h0
      simp only [dall, model] at hf
      simp at hf
      simp [hf]
    · by_cases h1 : a = 1
      · subst h1
        simp only [dall, model] at hf
        simp at hf
        simp [hf]
      · simp [dall, model, h0, h1] at hf
  · -- no action deletes a fact at all
    intro a f hf
    simp [dall, model] at hf
  · -- the actions the word's problem can use do not mention guard facts
    rintro a (⟨t, ht, hta⟩ | ⟨m, hm, t, ht, hta⟩) f hf
    · exact absurd (hta : (Sum.inr 0 : ℕ ⊕ ℕ) = Sum.inl a) Sum.inr_ne_inl
    · have hm0 : m = meth 0 := hm
      subst hm0
      have ha : a = 0 := by simpa [meth, body] using hta.symm
      subst ha
      simp [dall, model] at hf
  · -- the initial state has no guard fact
    intro f hf
    simp [inst] at hf
  · -- the goal has no guard fact
    intro f hf
    have hf0 : f = 0 := by simpa [inst] using hf
    simp [hf0]

end Ex2

end GuardTask

end HTN
