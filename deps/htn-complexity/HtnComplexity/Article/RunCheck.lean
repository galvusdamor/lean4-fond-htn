import HtnComplexity.Article.NoHTNNP
/-!
# Executing a plan of a problem description

`HTN.Article.runB p π` executes the action sequence `π` from the initial state of the description
`p` — positive and negative preconditions, delete-then-add effects, as in Def. 2.4 — and checks the
goal `(g⁺, g⁻)` in the final state.

* `HTN.Article.runB_iff` — `runB p π` holds iff `π` runs from `s_I` into a goal state of the
  described problem;
* `HTN.Article.pt_runB` — it is polynomial time.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime NoHTN

/-- The description of the action named `a`: the first one listed under the name. -/
def actDescOf (p : ProbDesc) (a : ℕ) : ActDesc := (p.actions.filter fun x => x.1 == a).headI

theorem δ_eq_actDescOf (p : ProbDesc) (a : ℕ) : p.δ a = (actDescOf p a).toAction := by
  unfold ProbDesc.δ actDescOf
  induction p.actions with
  | nil =>
    simp only [List.find?_nil, List.filter_nil, List.headI_nil]
    simp only [ActDesc.toAction, Action.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext f <;>
      simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff] <;> exact List.not_mem_nil
  | cons x l ih =>
    by_cases h : x.1 = a
    · simp [List.find?, List.filter, ActDesc.name, h]
    · have h' : (x.1 == a) = false := by simpa using h
      simp only [List.find?, ActDesc.name, h', List.filter_cons, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- One step of the execution: applicability so far, and the successor state. -/
def runStep (p : ProbDesc) (s : Bool × List ℕ) (a : ℕ) : Bool × List ℕ :=
  (s.1 && (actDescOf p a).2.1.all (fun f => decide (f ∈ s.2)) &&
      (actDescOf p a).2.2.1.all (fun f => !decide (f ∈ s.2)),
    s.2.filter (fun f => !decide (f ∈ (actDescOf p a).2.2.2.2)) ++ (actDescOf p a).2.2.2.1)

/-- **The execution check.** -/
def runB (p : ProbDesc) (π : List ℕ) : Bool :=
  let r := π.foldl (runStep p) (true, p.init)
  r.1 && p.goalPos.all (fun f => decide (f ∈ r.2)) && p.goalNeg.all (fun f => !decide (f ∈ r.2))

theorem runStep_state (p : ProbDesc) (b : Bool) (s : List ℕ) (a : ℕ) :
    {f | f ∈ (runStep p (b, s) a).2} = (p.toProblem.δ a).apply {f | f ∈ s} := by
  ext f
  change _ ↔ f ∈ (p.δ a).apply _
  rw [δ_eq_actDescOf]
  simp [runStep, Action.apply, ActDesc.toAction]

theorem runStep_flag (p : ProbDesc) (b : Bool) (s : List ℕ) (a : ℕ) :
    (runStep p (b, s) a).1 = true ↔ b = true ∧ (p.toProblem.δ a).Applicable {f | f ∈ s} := by
  change _ ↔ _ ∧ (p.δ a).Applicable _
  rw [δ_eq_actDescOf]
  simp only [runStep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, Action.Applicable, ActDesc.toAction, Set.subset_def, Set.mem_setOf_eq,
    Set.disjoint_left, and_assoc]

theorem foldl_runStep (p : ProbDesc) : ∀ (π : List ℕ) (b : Bool) (s : List ℕ),
    ((π.foldl (runStep p) (b, s)).1 = true ↔ b = true ∧ ∃ s', p.toProblem.Run π {f | f ∈ s} s') ∧
      ∀ s', p.toProblem.Run π {f | f ∈ s} s' → s' = {f | f ∈ (π.foldl (runStep p) (b, s)).2} := by
  intro π
  induction π with
  | nil =>
    intro b s
    exact ⟨by simp [Problem.Run], fun s' h => h⟩
  | cons a π ih =>
    intro b s
    simp only [List.foldl_cons]
    have e : (runStep p (b, s) a) = ((runStep p (b, s) a).1, (runStep p (b, s) a).2) := rfl
    rw [e]
    obtain ⟨h1, h2⟩ := ih (runStep p (b, s) a).1 (runStep p (b, s) a).2
    rw [runStep_state] at h1 h2
    refine ⟨?_, fun s' hs' => h2 s' hs'.2⟩
    rw [h1, runStep_flag]
    constructor
    · rintro ⟨⟨hb, ha⟩, s', hs'⟩
      exact ⟨hb, s', ha, hs'⟩
    · rintro ⟨hb, s', ha, hs'⟩
      exact ⟨⟨hb, ha⟩, s', hs'⟩

/-- **The execution check is correct.** -/
theorem runB_iff (p : ProbDesc) (π : List ℕ) :
    runB p π = true ↔ ∃ s, p.toProblem.Run π p.toProblem.init s ∧ p.toProblem.GoalState s := by
  obtain ⟨h1, h2⟩ := foldl_runStep p π true p.init
  unfold runB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  rw [h1]
  constructor
  · rintro ⟨⟨⟨-, s', hs'⟩, hpos⟩, hneg⟩
    refine ⟨s', hs', ?_, ?_⟩
    · intro f hf; rw [h2 s' hs']; exact hpos f hf
    · rw [Set.disjoint_left]; intro f hf; rw [h2 s' hs']; exact hneg f hf
  · rintro ⟨s', hs', hpos, hneg⟩
    refine ⟨⟨⟨rfl, s', hs'⟩, fun f hf => ?_⟩, fun f hf => ?_⟩
    · have := hpos hf; rw [h2 s' hs'] at this; exact this
    · intro hf'
      exact Set.disjoint_left.1 hneg hf (by rw [h2 s' hs']; exact hf')

/-! ### Polynomial time -/

theorem pt_actDescOf : PT fun x : ProbDesc × ℕ => actDescOf x.1 x.2 :=
  PT.headI (PT.filter (p := fun (x : ProbDesc × ℕ) (y : ActDesc) => y.1 == x.2)
    (PT.fst.comp (PT.fst.comp PT.fst)) (PT.beq (PT.fst.comp PT.snd) (PT.snd.comp PT.fst)))

theorem sz_actDescOf_le (p : ProbDesc) (a : ℕ) : sz (actDescOf p a) ≤ sz p + sz (default : ActDesc) := by
  unfold actDescOf
  have h1 := sz_headI_le (p.actions.filter fun x => x.1 == a)
  have h2 := sz_filter_le p.actions (fun x => x.1 == a)
  have h3 : sz p.actions ≤ sz p := (sz_fst_le p.1).trans (sz_fst_le p)
  omega

theorem pt_runStep : PT fun x : (ProbDesc × List ℕ) × (Bool × List ℕ) × ℕ =>
    runStep x.1.1 x.2.1 x.2.2 := by
  unfold runStep
  have hL : PT fun x : (ProbDesc × List ℕ) × (Bool × List ℕ) × ℕ => actDescOf x.1.1 x.2.2 :=
    pt_actDescOf.comp (PT.pair (PT.fst.comp PT.fst) (PT.snd.comp PT.snd))
  have hs : PT fun x : (ProbDesc × List ℕ) × (Bool × List ℕ) × ℕ => x.2.1.2 :=
    PT.snd.comp (PT.fst.comp PT.snd)
  refine PT.pair (PT.and (PT.and (PT.fst.comp (PT.fst.comp PT.snd))
    (PT.all (PT.fst.comp (PT.snd.comp hL)) (PT.elem (hs.comp PT.fst) PT.snd)))
    (PT.all (PT.fst.comp (PT.snd.comp (PT.snd.comp hL))) (PT.not (PT.elem (hs.comp PT.fst) PT.snd))))
    (PT.append ?_ (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hL)))))
  exact PT.filter hs (PT.not (PT.elem
    (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (hL.comp PT.fst))))) PT.snd))

theorem sz_runStep_le (p : ProbDesc) (s : Bool × List ℕ) (a : ℕ) :
    sz (runStep p s a) ≤ sz s + sz p + sz (default : ActDesc) := by
  have h1 := sz_actDescOf_le p a
  have h2 : sz (actDescOf p a).2.2.2.1 ≤ sz (actDescOf p a) :=
    (sz_fst_le _).trans ((sz_snd_le _).trans ((sz_snd_le _).trans (sz_snd_le _)))
  unfold runStep
  rw [sz_prod, sz_prod]
  have h3 := sz_filter_le s.2 (fun f => !decide (f ∈ (actDescOf p a).2.2.2.2))
  have h4 := sz_append_le (s.2.filter fun f => !decide (f ∈ (actDescOf p a).2.2.2.2))
    (actDescOf p a).2.2.2.1
  have h5 : sz (s.1 && (actDescOf p a).2.1.all (fun f => decide (f ∈ s.2)) &&
      (actDescOf p a).2.2.1.all (fun f => !decide (f ∈ s.2))) = sz s.1 := rfl
  omega

theorem pt_runB : PT fun x : ProbDesc × List ℕ => runB x.1 x.2 := by
  unfold runB
  have hf : PT fun x : ProbDesc × List ℕ => x.2.foldl (runStep x.1) (true, x.1.init) :=
    PT.foldl (α := ProbDesc × List ℕ) (β := ℕ) (σ := Bool × List ℕ)
      (g := fun x s a => runStep x.1 s a) PT.snd
      (PT.pair (PT.const true) (PT.fst.comp (PT.snd.comp PT.fst))) pt_runStep (c := 1)
      (d := 1 + sz (default : ActDesc)) fun x s a _ => by
        have h := sz_runStep_le x.1 s a
        have : sz x.1 ≤ sz x := sz_fst_le x
        nlinarith
  exact PT.and (PT.and (PT.fst.comp hf)
    (PT.all (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.fst))))
      (PT.elem (PT.snd.comp (hf.comp PT.fst)) PT.snd)))
    (PT.all (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.fst))))
      (PT.not (PT.elem (PT.snd.comp (hf.comp PT.fst)) PT.snd)))

end Article

end HTN
