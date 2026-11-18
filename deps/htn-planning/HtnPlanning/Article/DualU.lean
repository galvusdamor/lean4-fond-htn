import HtnPlanning.Article.Bridge
/-!
# The dual-rail translation relative to a finite set of facts

The dual-rail translation `HTN.Article.Problem.dual` of `HtnPlanning/Article/Bridge.lean` encodes
a state `s` by the facts `inl f` for `f ∈ s` and `inr f` for `f ∉ s` — for *every* `f`, so the
initial state of the translation is infinite whenever the type of facts is.  For descriptions only
the facts mentioned by the problem matter.  This file relativises the translation to a set `U` of
facts that contains every fact mentioned by an action or by the goal:

* `HTN.Article.encStateU U s` — `inl f` for `f ∈ s ∩ U`, `inr f` for `f ∈ U \ s`;
* `HTN.Article.Problem.dualU U P`, `HTN.Article.Problem.toPosU U P`;
* **`HTN.Article.Problem.sol_dualU`** — the translation has the same HTN solutions (and
  `solTI_dualU` the same TIHTN solutions);
* **`HTN.Article.Problem.solvable_iff_toPosU`** — plan existence is plan existence of the
  translation as a problem of `HTN.Problem`.
-/

namespace HTN

namespace Article

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- The dual-rail encoding of a state relative to `U`. -/
def encStateU (U s : Set F) : Set (F ⊕ F) := Sum.inl '' (s ∩ U) ∪ Sum.inr '' (U \ s)

@[simp] theorem inl_mem_encStateU {U s : Set F} {f : F} :
    Sum.inl f ∈ encStateU U s ↔ f ∈ s ∧ f ∈ U := by
  simp [encStateU]

@[simp] theorem inr_mem_encStateU {U s : Set F} {f : F} :
    Sum.inr f ∈ encStateU U s ↔ f ∈ U ∧ f ∉ s := by
  simp [encStateU]

/-- An action mentions only facts of `U`. -/
def Action.Within (U : Set F) (a : Action F) : Prop :=
  a.pre ⊆ U ∧ a.preNeg ⊆ U ∧ a.add ⊆ U ∧ a.del ⊆ U

theorem Action.applicable_dual_iffU {U : Set F} {a : Action F} (ha : a.Within U) (s : Set F) :
    a.dual.Applicable (encStateU U s) ↔ a.Applicable s := by
  simp only [Action.Applicable, Action.dual, Set.union_subset_iff, Set.image_subset_iff,
    Set.empty_disjoint, and_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => (by simpa using h1 hf : f ∈ s ∧ f ∈ U).1,
      Set.disjoint_left.2 fun f hf hs => ?_⟩
    exact (by simpa using h2 hf : f ∈ U ∧ f ∉ s).2 hs
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by simpa using ⟨h1 hf, ha.1 hf⟩,
      fun f hf => by simpa using ⟨ha.2.1 hf, Set.disjoint_left.1 h2 hf⟩⟩

theorem Action.apply_dualU {U : Set F} {a : Action F} (ha : a.Within U) (s : Set F) :
    a.dual.apply (encStateU U s) = encStateU U (a.apply s) := by
  ext x
  rcases x with f | f
  · by_cases h1 : f ∈ a.add <;> by_cases h2 : f ∈ a.del <;> by_cases h3 : f ∈ s <;>
      by_cases h4 : f ∈ U <;>
      simp_all [Action.apply, Action.dual, encStateU] <;>
      first | exact h4 (ha.2.2.1 h1) | exact h4 (ha.2.2.2 h2) | skip
  · by_cases h1 : f ∈ a.add <;> by_cases h2 : f ∈ a.del <;> by_cases h3 : f ∈ s <;>
      by_cases h4 : f ∈ U <;>
      simp_all [Action.apply, Action.dual, encStateU] <;>
      first | exact h4 (ha.2.2.1 h1) | exact h4 (ha.2.2.2 h2) | skip

namespace Problem

/-- All actions and the goal mention only facts of `U`. -/
def Within (U : Set F) (P : Problem F A C I) : Prop :=
  (∀ a, (P.δ a).Within U) ∧ P.goalPos ⊆ U ∧ P.goalNeg ⊆ U

/-- **The dual-rail translation relative to `U`.** -/
def dualU (U : Set F) (P : Problem F A C I) : Problem (F ⊕ F) A C I where
  δ a := (P.δ a).dual
  methods := P.methods
  init := encStateU U P.init
  tnI := P.tnI
  goalPos := Sum.inl '' P.goalPos ∪ Sum.inr '' P.goalNeg
  goalNeg := ∅

variable {U : Set F} {P : Problem F A C I}

theorem run_dualU_iff (hP : P.Within U) (as : List A) (s : Set F) (t : Set (F ⊕ F)) :
    (P.dualU U).Run as (encStateU U s) t ↔ ∃ s', t = encStateU U s' ∧ P.Run as s s' := by
  induction as generalizing s with
  | nil =>
    simp only [Run]
    constructor
    · rintro rfl; exact ⟨s, rfl, rfl⟩
    · rintro ⟨s', rfl, rfl⟩; rfl
  | cons a as ih =>
    simp only [Run, dualU]
    rw [Action.applicable_dual_iffU (hP.1 a), Action.apply_dualU (hP.1 a)]
    have := ih ((P.δ a).apply s)
    simp only [dualU] at this
    rw [this]
    constructor
    · rintro ⟨h, s', rfl, hr⟩; exact ⟨s', rfl, h, hr⟩
    · rintro ⟨s', rfl, h, hr⟩; exact ⟨h, s', rfl, hr⟩

theorem goalState_dualU_iff (hP : P.Within U) (s : Set F) :
    (P.dualU U).GoalState (encStateU U s) ↔ P.GoalState s := by
  simp only [GoalState, dualU, Set.union_subset_iff, Set.image_subset_iff, Set.empty_disjoint,
    and_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => (by simpa using h1 hf : f ∈ s ∧ f ∈ U).1,
      Set.disjoint_left.2 fun f hf hs => ?_⟩
    exact (by simpa using h2 hf : f ∈ U ∧ f ∉ s).2 hs
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by simpa using ⟨h1 hf, hP.2.1 hf⟩,
      fun f hf => by simpa using ⟨hP.2.2 hf, Set.disjoint_left.1 h2 hf⟩⟩

theorem executableIn_dualU_iff (hP : P.Within U) (tn : TaskNetwork I A C) (s : Set F) :
    (P.dualU U).ExecutableIn tn (encStateU U s) ↔ P.ExecutableIn tn s := by
  unfold ExecutableIn
  refine and_congr Iff.rfl (forall_congr' fun l => forall_congr' fun as =>
    imp_congr Iff.rfl (imp_congr Iff.rfl ?_))
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨s', -, h⟩ := (run_dualU_iff hP as s t).1 ht
    exact ⟨s', h⟩
  · rintro ⟨s', h⟩
    exact ⟨_, (run_dualU_iff hP as s _).2 ⟨s', rfl, h⟩⟩

theorem generates_dualU_iff (hP : P.Within U) (tn : TaskNetwork I A C) (s : Set F)
    (t : Set (F ⊕ F)) :
    (P.dualU U).Generates tn (encStateU U s) t ↔ ∃ s', t = encStateU U s' ∧ P.Generates tn s s' := by
  unfold Generates
  simp only [run_dualU_iff hP]
  constructor
  · rintro ⟨l, as, hl, has, s', rfl, h⟩; exact ⟨s', rfl, l, as, hl, has, h⟩
  · rintro ⟨s', rfl, l, as, hl, has, h⟩; exact ⟨l, as, hl, has, s', rfl, h⟩

theorem goal_congrU (hP : P.Within U) (tn : TaskNetwork I A C) :
    (∀ t, (P.dualU U).Generates tn (encStateU U P.init) t → (P.dualU U).GoalState t) ↔
      (∀ s, P.Generates tn P.init s → P.GoalState s) := by
  constructor
  · intro h s hs
    exact (goalState_dualU_iff hP s).1 (h _ ((generates_dualU_iff hP tn _ _).2 ⟨s, rfl, hs⟩))
  · intro h t ht
    obtain ⟨s', rfl, hs'⟩ := (generates_dualU_iff hP tn _ _).1 ht
    exact (goalState_dualU_iff hP s').2 (h s' hs')

/-- **The relative dual-rail translation has exactly the same HTN solutions.** -/
theorem sol_dualU [DecidableEq I] (hP : P.Within U) : (P.dualU U).Sol = P.Sol := by
  ext tn
  simp only [Sol, Set.mem_setOf_eq, IsSol]
  have hinit : (P.dualU U).init = encStateU U P.init := rfl
  rw [hinit, executableIn_dualU_iff hP]
  exact and_congr Iff.rfl (and_congr (goal_congrU hP tn) Iff.rfl)

/-- **The relative dual-rail translation has exactly the same TIHTN solutions.** -/
theorem solTI_dualU [DecidableEq I] (hP : P.Within U) : (P.dualU U).SolTI = P.SolTI := by
  ext tn
  simp only [SolTI, Set.mem_setOf_eq, IsSolTI]
  have hinit : (P.dualU U).init = encStateU U P.init := rfl
  rw [hinit, executableIn_dualU_iff hP]
  exact and_congr Iff.rfl (and_congr (goal_congrU hP tn) Iff.rfl)

/-- The relative dual-rail translation as a problem of `HTN.Problem`. -/
def toPosU (U : Set F) (P : Problem F A C I) : HTN.Problem (F ⊕ F) A C I where
  prec a := (P.δ a).dual.pre
  add a := (P.δ a).dual.add
  del a := (P.δ a).dual.del
  methods := P.methods
  init := encStateU U P.init
  goal := Sum.inl '' P.goalPos ∪ Sum.inr '' P.goalNeg
  tnI := P.tnI

theorem ofPos_toPosU (U : Set F) (P : Problem F A C I) : ofPos (P.toPosU U) = P.dualU U := rfl

/-- **Plan existence through the relative dual-rail translation.** -/
theorem solvable_iff_toPosU [DecidableEq I] (hP : P.Within U) (hwf : P.WF) :
    P.Solvable ↔ (P.toPosU U).Solvable := by
  rw [← solvable_ofPos_iff _ ⟨hwf.tnI, hwf.methods⟩, ofPos_toPosU, Solvable, Solvable,
    sol_dualU hP]

end Problem

end Article

end HTN
