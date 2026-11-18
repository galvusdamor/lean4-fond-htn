import HtnPlanning.Article.DualU
import HtnPlanning.Progression.ProgressionSound
import HtnPlanning.Progression.ProgressionComplete
import HtnPlanning.Classes.Basic
/-!
# Progression (Def. 4.2, Thm. 4.2.12, Cor. 4.2.13 — the HTN part)

**Definition 4.2 (progression).** A pair of a state and a task network is progressed either by
decomposing a compound task without predecessors, or by applying a primitive task without
predecessors that is applicable in the state (and removing it).  Here the search node also records
the actions applied so far (`HTN.Article.PNode`).

* `HTN.Article.Problem.ProgStep`, `ProgReach`, `GoalNode`;
* **`HTN.Article.Problem.thm_4_2_12_htn`** — `Sol(P) ≠ ∅` iff some progression from
  `(s_I, tn_I)` reaches an empty task network in a goal state;
* **`HTN.Article.Problem.cor_4_2_13_htn`** — the action sequences found by progression are exactly
  the (action sequences of the) totally ordered solutions.

Both are transferred from the progression search of `HtnPlanning/Progression/` (Höller et al.)
through the dual-rail translation, which turns the article's actions with negative preconditions
into actions of `HTN.Problem` step by step.
-/

namespace HTN

namespace Article

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- A node of progression: the state, the remaining task network and the actions applied. -/
structure PNode (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The state. -/
  state : Set F
  /-- The remaining task network. -/
  net : TaskNetwork I A C
  /-- The actions applied so far. -/
  plan : List A

namespace Problem

variable [DecidableEq I] (P : Problem F A C I)

/-- **Definition 4.2 (progression).** -/
inductive ProgStep : PNode F A C I → PNode F A C I → Prop
  /-- A primitive task without predecessors, applicable in the state, is applied. -/
  | prog {s : Set F} {tn : TaskNetwork I A C} {π : List A} {t : I} {a : A}
      (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s) :
      ProgStep ⟨s, tn, π⟩ ⟨(P.δ a).apply s, tn.progress t, π ++ [a]⟩
  /-- A compound task without predecessors is decomposed. -/
  | decomp {s : Set F} {tn tn' : TaskNetwork I A C} {π : List A} {t : I} {m : Method I A C}
      (hu : tn.Unconstrained t) (hstep : DecompStep P.methods tn t m tn') :
      ProgStep ⟨s, tn, π⟩ ⟨s, tn', π⟩

/-- The initial node `(s_I, tn_I)`. -/
def initPNode : PNode F A C I := ⟨P.init, P.tnI, []⟩

/-- `(s_I, tn_I) →*_P n`. -/
def ProgReach (n : PNode F A C I) : Prop := Relation.ReflTransGen P.ProgStep P.initPNode n

/-- A goal node: the empty task network in a goal state. -/
def GoalNode (n : PNode F A C I) : Prop := n.net.T = ∅ ∧ P.GoalState n.state

/-! ### Simulation by the dual-rail translation -/

/-- The dual-rail image of a node. -/
def encNode (n : PNode F A C I) : SearchNode (F ⊕ F) A C I :=
  ⟨encStateU Set.univ n.state, n.net, n.plan⟩

variable {P}

theorem within_univ : P.Within Set.univ :=
  ⟨fun _ => ⟨Set.subset_univ _, Set.subset_univ _, Set.subset_univ _, Set.subset_univ _⟩,
    Set.subset_univ _, Set.subset_univ _⟩

theorem toPosU_applicable_iff (U : Set F) (a : A) (s : Set (F ⊕ F)) :
    (P.toPosU U).Applicable a s ↔ (P.δ a).dual.Applicable s := by
  simp [ActionModel.Applicable, Action.Applicable, toPosU, Action.dual]

theorem step_encNode_iff {n : PNode F A C I} {m : SearchNode (F ⊕ F) A C I} :
    (P.toPosU Set.univ).Step (encNode n) m ↔ ∃ n', m = encNode n' ∧ P.ProgStep n n' := by
  have hw := within_univ (P := P)
  constructor
  · intro h
    cases h with
    | prog hu hα happ =>
      rename_i t a
      have happ' : (P.δ a).Applicable n.state :=
        (Action.applicable_dual_iffU (hw.1 a) _).1 ((toPosU_applicable_iff _ _ _).1 happ)
      refine ⟨⟨(P.δ a).apply n.state, n.net.progress t, n.plan ++ [a]⟩, ?_, ProgStep.prog hu hα happ'⟩
      simp only [encNode]
      congr 1
      exact Action.apply_dualU (hw.1 a) _
    | decomp hu hstep =>
      exact ⟨⟨n.state, _, n.plan⟩, rfl, ProgStep.decomp hu hstep⟩
  · rintro ⟨n', rfl, h⟩
    cases h with
    | prog hu hα happ =>
      rename_i s tn π t a
      have := HTN.Problem.Step.prog (P := P.toPosU Set.univ) (s := encStateU Set.univ s)
        (π := π) hu hα ((toPosU_applicable_iff _ _ _).2 ((Action.applicable_dual_iffU (hw.1 a) _).2 happ))
      simp only [encNode]
      convert this using 2
      exact (Action.apply_dualU (hw.1 a) _).symm
    | decomp hu hstep => exact HTN.Problem.Step.decomp hu hstep

theorem reachableNode_iff {m : SearchNode (F ⊕ F) A C I} :
    (P.toPosU Set.univ).ReachableNode m ↔ ∃ n, m = encNode n ∧ P.ProgReach n := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨P.initPNode, rfl, Relation.ReflTransGen.refl⟩
    | tail _ hs ih =>
      obtain ⟨n, rfl, hn⟩ := ih
      obtain ⟨n', rfl, hs'⟩ := step_encNode_iff.1 hs
      exact ⟨n', rfl, hn.tail hs'⟩
  · rintro ⟨n, rfl, h⟩
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.tail (step_encNode_iff.2 ⟨_, rfl, hs⟩)

theorem goalNode_encNode_iff (n : PNode F A C I) :
    (P.toPosU Set.univ).IsGoalNode (encNode n) ↔ P.GoalNode n := by
  refine and_congr Iff.rfl (Iff.trans ?_ (goalState_dualU_iff (within_univ (P := P)) n.state))
  simp [HTN.Problem.GoalState, GoalState, dualU, toPosU, encNode]

/-- **Theorem 4.2.12 (HTN part).** `Sol(P) ≠ ∅` iff some progression of `(s_I, tn_I)` reaches the
empty task network in a state satisfying the goal. -/
theorem thm_4_2_12_htn [Infinite I] (hP : P.WF) : P.Solvable ↔ ∃ n, P.ProgReach n ∧ P.GoalNode n := by
  rw [solvable_iff_toPosU (within_univ (P := P)) hP,
    HTN.Problem.solvable_iff_exists_goalNode ⟨hP.tnI, hP.methods⟩]
  constructor
  · rintro ⟨m, hm, hg⟩
    obtain ⟨n, rfl, hn⟩ := reachableNode_iff.1 hm
    exact ⟨n, hn, (goalNode_encNode_iff n).1 hg⟩
  · rintro ⟨n, hn, hg⟩
    exact ⟨_, reachableNode_iff.2 ⟨n, rfl, hn⟩, (goalNode_encNode_iff n).2 hg⟩

/-! ### Corollary 4.2.13 -/

theorem run_toPosU_iff (as : List A) (s s' : Set F) :
    (P.dualU (Set.univ : Set F)).Run as (encStateU Set.univ s) (encStateU Set.univ s') ↔
      P.Run as s s' := by
  rw [run_dualU_iff (within_univ (P := P))]
  constructor
  · rintro ⟨s'', h, hr⟩
    have : s' = s'' := by
      ext f
      have := congrArg (fun t => Sum.inl f ∈ t) h
      simpa using this
    rwa [this]
  · intro h; exact ⟨s', rfl, h⟩

/-- **Corollary 4.2.13 (HTN part).** The action sequences of goal nodes reached by progression
are exactly the action sequences of the totally ordered solutions. -/
theorem cor_4_2_13_htn [Infinite I] (hP : P.WF) (π : List A) :
    (∃ n, P.ProgReach n ∧ P.GoalNode n ∧ n.plan = π) ↔
      ∃ tn ∈ P.Sol, tn.IsTotallyOrdered ∧ ∃ l, tn.IsLinearization l ∧ tn.IsActionSeq l π := by
  set Q := P.toPosU Set.univ
  have hQ : Q.WF := ⟨hP.tnI, hP.methods⟩
  have h1 : (∃ n, P.ProgReach n ∧ P.GoalNode n ∧ n.plan = π) ↔ Q.IsSolutionPlan π := by
    constructor
    · rintro ⟨n, hn, hg, rfl⟩
      exact HTN.Problem.isSolutionPlan_of_goalNode hQ (reachableNode_iff.2 ⟨n, rfl, hn⟩)
        ((goalNode_encNode_iff n).2 hg)
    · intro h
      obtain ⟨m, hm, hg, hpl⟩ := HTN.Problem.exists_goalNode_of_isSolutionPlan hQ h
      obtain ⟨n, rfl, hn⟩ := reachableNode_iff.1 hm
      exact ⟨n, hn, (goalNode_encNode_iff n).1 hg, hpl⟩
  rw [h1, ← sol_dualU (within_univ (P := P)), ← ofPos_toPosU]
  constructor
  · rintro ⟨tn₀, l, hreach, hprim, hl, has, happ, hgoal⟩
    have hwf : tn₀.WF := HTN.DecomposesTo.wf hreach hQ.tnI
    classical
    have hirr : ∀ a, ¬ (ordExt tn₀ (chain l)).ord a a := fun a h =>
      lt_irrefl _ (idxOf_lt_of_ordExt_chain hwf hl h)
    have hps : ∀ p ∈ chain l, p.1 ∈ tn₀.T ∧ p.2 ∈ tn₀.T ∧ tn₀.IsPrimitiveId p.1 ∧
        tn₀.IsPrimitiveId p.2 := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := idxOf_lt_of_mem_chain hl.1 hp
      have h1' := (hl.2.1 _).1 h1
      have h2' := (hl.2.1 _).1 h2
      exact ⟨h1', h2', hprim _ h1', hprim _ h2'⟩
    set tn' := ordExt tn₀ (chain l)
    have hoi : OIReach tn₀ tn' := oiReach_ordExt hwf _ hps hirr
    have hwf' : tn'.WF := ordExt_wf hwf (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1⟩) hirr
    have hl' : tn'.IsLinearization l := by
      refine ⟨hl.1, hl.2.1, ?_⟩
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij hc
      have := idxOf_lt_of_ordExt_chain hwf hl hc
      rw [List.idxOf_getElem hl.1, List.idxOf_getElem hl.1] at this
      omega
    refine ⟨tn', ⟨⟨fun t ht => hprim t ht, fun l' as' hl'' has'' => ?_⟩, fun s ⟨l', as', hl'', has'', hrun⟩ => ?_,
      tn₀, hreach, hoi⟩, ?_, l, hl', has⟩
    · obtain ⟨tn'', htn'', -, -, -, -, huniq⟩ := exists_oiReach_unique_lin hwf hprim hl
      obtain rfl := huniq l' (htn'' ▸ hl'')
      obtain rfl := TaskNetwork.isActionSeq_unique has'' has
      exact ⟨_, (run_ofPos_iff _ _ _ _).2 ⟨happ, rfl⟩⟩
    · obtain ⟨tn'', htn'', -, -, -, -, huniq⟩ := exists_oiReach_unique_lin hwf hprim hl
      obtain rfl := huniq l' (htn'' ▸ hl'')
      obtain rfl := TaskNetwork.isActionSeq_unique has'' has
      rw [run_ofPos_iff] at hrun
      rw [goalState_ofPos_iff, hrun.2]
      exact hgoal
    · intro a ha b hb hab
      have ha' := (hl.2.1 a).2 ha
      have hb' := (hl.2.1 b).2 hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha'
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
      have hij : i ≠ j := fun h => hab (by subst h; rfl)
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact Or.inl (Relation.TransGen.mono (fun x y hxy => Or.inr hxy) (transGen_chain hi hj h))
      · exact Or.inr (Relation.TransGen.mono (fun x y hxy => Or.inr hxy) (transGen_chain hj hi h))
  · rintro ⟨tn, ⟨hex, hgoal, tn₀, hdec, hoi⟩, -, l, hl, has⟩
    have hl₀ := hoi.isLinearization hl
    obtain ⟨s', hrun⟩ := hex.2 l π hl has
    have hg := hgoal s' ⟨l, π, hl, has, hrun⟩
    rw [run_ofPos_iff] at hrun
    rw [goalState_ofPos_iff] at hg
    refine ⟨tn₀, l, hdec, ?_, hl₀, ?_, hrun.1, hrun.2 ▸ hg⟩
    · intro t ht
      obtain ⟨a, ha⟩ := hex.1 t (by rw [hoi.T]; exact ht)
      exact ⟨a, by rw [← hoi.α]; exact ha⟩
    · unfold TaskNetwork.IsActionSeq at has ⊢; rw [← hoi.α]; exact has

end Problem

end Article

end HTN
