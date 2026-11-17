import FondHtn.Transfer.Deterministic
import FondHtn.Basic
import HtnPlanning.Core.ReachableLabels
import HtnPlanning.Article.DTree
/-!
# Deterministic HTN problems with goals as FOND problems

A problem `Q` of the deterministic article model has a state goal `(g⁺, g⁻)`; FOND HTN problems
have none.  `FOND.detFond Q i g` is the FOND problem with the same methods and initial state, the
actions of `Q` (each with its single effect), and the initial task network of `Q` followed by a
new task `i ↦ g` whose action checks the goal.  For a fresh id `i` and an action name `g` not
used by `Q`, every criterion considered here holds iff `Q` is solvable
(`FOND.detFond_solvable_iff`).
-/

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- **The FOND version of a deterministic problem**, with the goal checked by a last task. -/
def detFond [DecidableEq A] [DecidableEq I] (Q : HTN.Article.Problem F A C I) (i : I) (g : A) :
    Problem F A C I where
  δ := fun a => if a = g then ⟨Q.goalPos, Q.goalNeg, {(∅, ∅)}⟩ else Action.ofDet (Q.δ a)
  methods := Q.methods
  init := Q.init
  tnI := Q.tnI.appendLast i g

/-- `g` is not used as a task name by `Q`. -/
def FreshName (Q : HTN.Article.Problem F A C I) (g : A) : Prop :=
  (∀ t ∈ Q.tnI.T, Q.tnI.α t ≠ Sum.inl g) ∧
    ∀ m ∈ Q.methods, ∀ t ∈ m.subtasks.T, m.subtasks.α t ≠ Sum.inl g

variable [DecidableEq A] [DecidableEq I] {Q : HTN.Article.Problem F A C I} {i : I} {g : A}

theorem detFond_isDeterministic : (detFond Q i g).IsDeterministic := by
  intro a
  by_cases ha : a = g
  · exact ⟨(∅, ∅), by simp [detFond, ha]⟩
  · exact ⟨((Q.δ a).add, (Q.δ a).del), by simp [detFond, ha, Action.ofDet]⟩

theorem detFond_wf (hQ : Q.WF) : (detFond Q i g).WF where
  tnI := show (Q.tnI.appendLast i g).WF from appendLast_wf hQ.tnI
  methods := hQ.methods
  actions := by
    intro a
    by_cases ha : a = g
    · simp only [detFond, ha, if_true]
      exact ⟨⟨_, rfl⟩, Set.finite_singleton _⟩
    · simp only [detFond, ha, if_false]
      exact Action.ofDet_wf _

/-- Runs of `Q` followed by the goal check are the weakly executable sequences. -/
theorem weakExec_detFond_iff :
    ∀ (as : List A) (s : Set F), g ∉ as →
      ((detFond Q i g).WeakExec (as ++ [g]) s ↔ ∃ s', Q.Run as s s' ∧ Q.GoalState s') := by
  intro as
  induction as with
  | nil =>
    intro s _
    simp only [List.nil_append, Problem.WeakExec, HTN.Article.Problem.Run, exists_eq_left]
    simp [detFond, Action.Applicable, Action.outcomes, HTN.Article.Problem.GoalState]
  | cons a as ih =>
    intro s hg
    have hag : a ≠ g := fun e => hg (e ▸ List.mem_cons_self)
    have hg' : g ∉ as := fun h => hg (List.mem_cons_of_mem _ h)
    have hδ : (detFond Q i g).δ a = Action.ofDet (Q.δ a) := by simp [detFond, hag]
    show (((detFond Q i g).δ a).Applicable s ∧ ∃ s' ∈ ((detFond Q i g).δ a).outcomes s,
      (detFond Q i g).WeakExec (as ++ [g]) s') ↔ _
    rw [hδ, Action.ofDet_applicable, Action.ofDet_outcomes]
    simp only [Set.mem_singleton_iff, exists_eq_left, ih _ hg', HTN.Article.Problem.Run]
    constructor
    · rintro ⟨happ, s', hrun, hgoal⟩; exact ⟨s', ⟨happ, hrun⟩, hgoal⟩
    · rintro ⟨s', ⟨happ, hrun⟩, hgoal⟩; exact ⟨happ, s', hrun, hgoal⟩

omit [DecidableEq A] in
/-- Task networks reachable from `tn_I` never use the name `g`. -/
theorem labels_ne_of_decomposesTo (hg : FreshName Q g) {tn : TaskNetwork I A C}
    (h : HTN.DecomposesTo Q.methods Q.tnI tn) : ∀ t ∈ tn.T, tn.α t ≠ Sum.inl g := by
  have := HTN.DecomposesTo.labels_mem (L := {x | x ≠ Sum.inl g}) h hg.1 hg.2
  exact fun t ht => this t ht

omit [DecidableEq A] in
theorem not_mem_actions (hg : FreshName Q g) {tn : TaskNetwork I A C}
    (h : HTN.DecomposesTo Q.methods Q.tnI tn) {l : List I} {as : List A}
    (hl : tn.IsLinearization l) (has : tn.IsActionSeq l as) : g ∉ as := by
  intro hgas
  have : Sum.inl g ∈ l.map tn.α := by
    rw [has]; exact List.mem_map.2 ⟨g, hgas, rfl⟩
  obtain ⟨t, ht, hte⟩ := List.mem_map.1 this
  exact labels_ne_of_decomposesTo hg h t ((hl.2.1 t).1 ht) hte

/-- **Weak LD solvability of `detFond Q i g` is solvability of `Q`.** -/
theorem detFond_weakLD_iff [Infinite I] (hQ : Q.WF) (hi : i ∉ Q.tnI.T) (hg : FreshName Q g) :
    (detFond Q i g).WeakLDSolvable ↔ Q.Solvable := by
  rw [HTN.Article.Problem.solvable_iff_decomp Q hQ]
  constructor
  · rintro ⟨X, l', ⟨hX, hprimX⟩, hl', bs, hbs, hex⟩
    obtain ⟨tn, rfl, hd, hwf, hitn⟩ := decomposesTo_of_appendLast hX hQ.tnI hi
    obtain ⟨l, rfl, hl⟩ := (isLinearization_appendLast_iff hitn).1 hl'
    obtain ⟨as, rfl, has⟩ := (isActionSeq_appendLast_iff hl hitn).1 hbs
    have hprim : tn.IsPrimitive := by
      intro t ht
      have hti : t ≠ i := fun e => hitn (e ▸ ht)
      obtain ⟨b, hb⟩ := hprimX t (Finset.mem_insert_of_mem ht)
      exact ⟨b, by simpa [appendLast, hti] using hb⟩
    obtain ⟨s, hrun, hgoal⟩ := (weakExec_detFond_iff as _ (not_mem_actions hg hd hl has)).1 hex
    exact ⟨tn, hd, hprim, l, as, s, hl, has, hrun, hgoal⟩
  · rintro ⟨tn, hd, hprim, l, as, s, hl, has, hrun, hgoal⟩
    obtain ⟨tn', σ, hav, hσ, hwf', hi'⟩ := decomposesTo_avoid hd hQ.tnI {i}
      (Finset.disjoint_singleton_left.2 hi)
    have hit : i ∉ tn'.T := Finset.disjoint_singleton_left.1 hi'
    obtain ⟨hX, -, -⟩ := decomposesTo_appendLast (a := g) hav hQ.tnI hi
    obtain ⟨hl', has'⟩ := TaskNetwork.Iso.map_isLinearization hσ.1 hσ.2.1 hσ.2.2 hl
    refine ⟨tn'.appendLast i g, l.map σ ++ [i], ⟨hX, ?_⟩,
      isLinearization_appendLast hl' hit, as ++ [g],
      (isActionSeq_appendLast_iff hl' hit).2 ⟨as, rfl, has' as has⟩,
      (weakExec_detFond_iff as _ (not_mem_actions hg hd hl has)).2 ⟨s, hrun, hgoal⟩⟩
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact ⟨g, by simp [appendLast]⟩
    · have hti : t ≠ i := fun e => hit (e ▸ ht)
      obtain ⟨t₀, ht₀, rfl⟩ := hσ.surj ht
      obtain ⟨b, hb⟩ := hprim t₀ ht₀
      exact ⟨b, by simp [appendLast, hti, hσ.α_eq ht₀, hb]⟩

/-- **Every criterion except strong cyclic agrees with solvability of `Q`.** -/
theorem detFond_solvable_iff [Infinite I] (hQ : Q.WF) (hi : i ∉ Q.tnI.T) (hg : FreshName Q g) :
    ((detFond Q i g).WeakLDSolvable ↔ Q.Solvable) ∧
    ((detFond Q i g).StrongLDSolvable ↔ Q.Solvable) ∧
    ((detFond Q i g).WeakODSolvable ↔ Q.Solvable) ∧
    ((detFond Q i g).StrongODSolvable ↔ Q.Solvable) ∧
    ((detFond Q i g).MPWeakSolvable ↔ Q.Solvable) ∧
    ((detFond Q i g).MPStrongSolvable ↔ Q.Solvable) := by
  have hdet := detFond_isDeterministic (Q := Q) (i := i) (g := g)
  have hwf := detFond_wf (i := i) (g := g) hQ
  have h0 := detFond_weakLD_iff hQ hi hg
  obtain ⟨h1, h2, h3⟩ := Problem.det_fm_iff hdet hwf.tnI
  exact ⟨h0, h1.trans h0, h2.trans h0, h3.trans h0,
    (Problem.det_mpWeak_iff hdet hwf).trans h0, (Problem.det_mpStrong_iff hdet hwf).trans h0⟩

end FOND
