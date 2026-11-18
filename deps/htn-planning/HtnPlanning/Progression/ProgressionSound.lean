import HtnPlanning.Progression.ProgressionSplit
import HtnPlanning.Progression.ProgressionComplete
import HtnPlanning.Core.SolutionIso
/-!
# Soundness of progression search

This file proves the soundness half of Theorem 1 of

  D. Höller, P. Bercher, G. Behnke, S. Biundo,
  *HTN Planning as Heuristic Progression Search*, JAIR 67 (2020):

whatever progression search returns is a solution — the plan of a reachable goal node is a
solution plan of the problem (`HTN.Problem.isSolutionPlan_of_goalNode`).

The proof is an invariant of the search space (`HTN.Problem.Repr`): for every reachable search
node `(s, tn, π)` there are

* a task network `tn₀` reachable from `tn_I` by decomposition,
* a list `lP` of the tasks of `tn₀` that have already been progressed, and
* a copy `tnBar` of the node's task network

such that `tn₀` splits into `lP` followed by `tnBar` (`HTN.TaskNetwork.Split`), `lP` induces the
plan prefix `π`, that prefix is applicable in `s₀` and leads to `s`.  A decomposition step of the
search is mirrored by a decomposition of `tn₀` — with a fresh copy that avoids *all* of `tn₀`,
which is why the node's network is only tracked up to isomorphism — and a progression step moves
one task from `tnBar` to the end of `lP`.

At a goal node the remaining network is empty, so `lP` is a linearization of `tn₀` inducing
exactly the plan of the node: the three solution criteria hold.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable [DecidableEq I] [Infinite I] {P : Problem F A C I}

open TaskNetwork

/-- **The invariant of progression search**: the node has progressed the prefix `lP` of a task
network `tn₀` reachable from `tn_I`, and its own task network is (a copy of) the remainder. -/
def Repr (P : Problem F A C I) (n : SearchNode F A C I) : Prop :=
  ∃ (tn₀ tnBar : TaskNetwork I A C) (lP : List I),
    P.Reachable tn₀ ∧ tnBar.WF ∧ Split tn₀ lP tnBar ∧ tnBar.Iso n.net ∧
      tn₀.IsActionSeq lP n.plan ∧ P.SeqApplicable n.plan P.init ∧
      n.state = P.transitionSeq n.plan P.init

omit [Infinite I] in
/-- The initial node satisfies the invariant. -/
lemma repr_initNode (hP : P.WF) : P.Repr P.initNode := by
  refine ⟨P.tnI, P.tnI, [], Relation.ReflTransGen.refl, hP.tnI, ?_, TaskNetwork.Iso.refl _,
    rfl, trivial, rfl⟩
  exact
    { nodup := List.nodup_nil
      mem := by intro x; simp
      disj := by intro x hx; simp at hx
      pairwise := List.Pairwise.nil
      front := by intro x _ y hy; simp at hy
      ord_iff := by intro x _ y _; rfl
      alpha := by intro x _; rfl }

omit [Infinite I] in
/-- The invariant is preserved by a progression step. -/
lemma repr_prog {s : Set F} {tn : TaskNetwork I A C} {π : List A} {t : I} {a : A}
    (hrepr : P.Repr ⟨s, tn, π⟩) (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a)
    (happ : P.Applicable a s) :
    P.Repr ⟨P.transition a s, tn.progress t, π ++ [a]⟩ := by
  obtain ⟨tn₀, tnBar, lP, hreach, hwfBar, hsplit, hiso, hact, hsapp, hstate⟩ := hrepr
  obtain ⟨σ, hbij, hord, hαiso⟩ := hiso
  obtain ⟨tb, htb, htbσ⟩ : ∃ x ∈ tnBar.T, σ x = t := by
    obtain ⟨x, hx, hxt⟩ := hbij.surjOn (by simpa using hu.1)
    exact ⟨x, by simpa using hx, hxt⟩
  have hmaps : ∀ x ∈ tnBar.T, σ x ∈ tn.T := fun x hx => by
    simpa using hbij.mapsTo (by simpa using hx)
  -- `tb` is unconstrained in `tnBar`
  have htbunc : ∀ x ∈ tnBar.T, ¬ tnBar.ord x tb := by
    intro x hx hcon
    have : tn.ord (σ x) (σ tb) := (hord x hx tb htb).1 hcon
    rw [htbσ] at this
    exact hu.2 (σ x) (hmaps x hx) this
  have htbnotin : tb ∉ lP := fun hc => hsplit.disj tb hc htb
  have hαtb : tn₀.α tb = Sum.inl a := by
    rw [hsplit.alpha tb htb, hαiso tb htb, htbσ]
    exact hα
  refine ⟨tn₀, tnBar.progress tb, lP ++ [tb], hreach, TaskNetwork.progress_wf hwfBar ⟨htb,
    htbunc⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- the split for the extended prefix
    refine
      { nodup := ?_
        mem := ?_
        disj := ?_
        pairwise := ?_
        front := ?_
        ord_iff := ?_
        alpha := ?_ }
    · exact List.Nodup.append hsplit.nodup (List.nodup_singleton tb)
        (by intro x hx hx'; simp at hx'; subst hx'; exact htbnotin hx)
    · intro x
      rw [hsplit.mem x]
      simp only [List.mem_append, List.mem_singleton, mem_progress_T]
      constructor
      · rintro (hx | hx)
        · exact Or.inl (Or.inl hx)
        · by_cases hxt : x = tb
          · exact Or.inl (Or.inr hxt)
          · exact Or.inr ⟨hxt, hx⟩
      · rintro ((hx | rfl) | ⟨-, hx⟩)
        · exact Or.inl hx
        · exact Or.inr htb
        · exact Or.inr hx
    · intro x hx
      rw [mem_progress_T]
      rintro ⟨hxt, hxT⟩
      rcases List.mem_append.1 hx with hx' | hx'
      · exact hsplit.disj x hx' hxT
      · simp at hx'
        exact hxt hx'
    · refine List.pairwise_append.2 ⟨hsplit.pairwise, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact hsplit.front y htb x hx
    · intro x hx y hy
      rw [mem_progress_T] at hx
      rcases List.mem_append.1 hy with hy' | hy'
      · exact hsplit.front x hx.2 y hy'
      · simp only [List.mem_singleton] at hy'
        subst hy'
        intro hcon
        exact htbunc x hx.2 ((hsplit.ord_iff x hx.2 y htb).1 hcon)
    · intro x hx y hy
      rw [mem_progress_T] at hx hy
      simp only [progress_ord]
      rw [hsplit.ord_iff x hx.2 y hy.2]
      exact ⟨fun h => ⟨h, hx.1⟩, fun h => h.1⟩
    · intro x hx
      rw [mem_progress_T] at hx
      simpa using hsplit.alpha x hx.2
  · have := TaskNetwork.iso_progress hbij hord hαiso htb
    rwa [htbσ] at this
  · simp only [IsActionSeq, List.map_append, List.map_cons, List.map_nil] at hact ⊢
    rw [hact, hαtb]
  · refine (P.seqApplicable_append π [a] P.init).2 ⟨hsapp, ?_⟩
    rw [← hstate]
    exact ⟨happ, trivial⟩
  · rw [P.transitionSeq_append π [a] P.init, ← hstate]
    rfl

/-- The invariant is preserved by a decomposition step. -/
lemma repr_decomp (hP : P.WF) {s : Set F} {tn tn' : TaskNetwork I A C} {π : List A} {t : I}
    {m : Method I A C} (hwftn : tn.WF) (hrepr : P.Repr ⟨s, tn, π⟩)
    (hstep : DecompStep P.methods tn t m tn') :
    P.Repr ⟨s, tn', π⟩ := by
  obtain ⟨tn₀, tnBar, lP, hreach, hwfBar, hsplit, hiso, hact, hsapp, hstate⟩ := hrepr
  obtain ⟨hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hstep
  obtain ⟨σ, hbij, hord, hαiso⟩ := hiso
  have hwf₀ : tn₀.WF := HTN.DecomposesTo.wf hreach hP.tnI
  obtain ⟨tb, htb, htbσ⟩ : ∃ x ∈ tnBar.T, σ x = t := by
    obtain ⟨x, hx, hxt⟩ := hbij.surjOn (by simpa using htT)
    exact ⟨x, by simpa using hx, hxt⟩
  -- a copy of the method's subtask network avoiding all of `tn₀`
  obtain ⟨v, hv, hviso, hdisj₀⟩ := TaskNetwork.exists_fresh_iso_copy u hu tn₀.T
  have hsub : ∀ x ∈ tnBar.T, x ∈ tn₀.T := fun x hx => hsplit.mem_of_mem_rest hx
  have hdisjBar : Disjoint tnBar.T v.T := by
    rw [Finset.disjoint_left]
    intro x hx
    exact Finset.disjoint_left.1 hdisj₀ (hsub x hx)
  have hvnot : ∀ x ∈ tn₀.T, x ∉ v.T := fun x hx => Finset.disjoint_left.1 hdisj₀ hx
  have htb₀ : tb ∈ tn₀.T := hsub tb htb
  have hαtb : tn₀.α tb = Sum.inr m.abstractTask := by
    rw [hsplit.alpha tb htb, hαiso tb htb, htbσ]
    exact hαt
  refine ⟨decomposeWith tn₀ tb v, decomposeWith tnBar tb v, lP,
    Relation.ReflTransGen.tail hreach ⟨tb, m, hmM, htb₀, hαtb, v, hv, hviso.trans huiso,
      hdisj₀, rfl⟩, decomposeWith_wf hwfBar hv hdisjBar, ?_, ?_, ?_, hsapp, hstate⟩
  · -- the split survives the decomposition
    have hlPne : ∀ x ∈ lP, x ≠ tb := by
      intro x hx
      rintro rfl
      exact hsplit.disj x hx htb
    have hlP₀ : ∀ x ∈ lP, x ∈ tn₀.T := fun x hx => hsplit.mem_of_mem_prefix hx
    refine
      { nodup := hsplit.nodup
        mem := ?_
        disj := ?_
        pairwise := ?_
        front := ?_
        ord_iff := ?_
        alpha := ?_ }
    · intro x
      rw [mem_decomposeWith_T, mem_decomposeWith_T]
      constructor
      · rintro (⟨hx, hxt⟩ | hx)
        · rcases (hsplit.mem x).1 hx with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨h, hxt⟩)
        · exact Or.inr (Or.inr hx)
      · rintro (hx | ⟨hx, hxt⟩ | hx)
        · exact Or.inl ⟨hlP₀ x hx, hlPne x hx⟩
        · exact Or.inl ⟨hsplit.mem_of_mem_rest hx, hxt⟩
        · exact Or.inr hx
    · intro x hx
      rw [mem_decomposeWith_T]
      rintro (⟨hxT, -⟩ | hxv)
      · exact hsplit.disj x hx hxT
      · exact hvnot x (hlP₀ x hx) hxv
    · refine hsplit.pairwise.imp_of_mem ?_
      intro a b ha hb hab hcon
      refine hab ?_
      exact (decomposeWith_ord_old_old hv hdisj₀ (hlP₀ b hb) (hlPne b hb) (hlP₀ a ha)
        (hlPne a ha)).1 hcon
    · intro x hx y hy
      rw [mem_decomposeWith_T] at hx
      rcases hx with ⟨hxT, hxt⟩ | hxv
      · rw [decomposeWith_ord_old_old hv hdisj₀ (hsub x hxT) hxt (hlP₀ y hy) (hlPne y hy)]
        exact hsplit.front x hxT y hy
      · rw [decomposeWith_ord_new_old hwf₀ hv hdisj₀ hxv (hlP₀ y hy)]
        exact hsplit.front tb htb y hy
    · intro x hx y hy
      rw [mem_decomposeWith_T] at hx hy
      rcases hx with ⟨hxT, hxt⟩ | hxv
      · rcases hy with ⟨hyT, hyt⟩ | hyv
        · rw [decomposeWith_ord_old_old hv hdisj₀ (hsub x hxT) hxt (hsub y hyT) hyt,
            decomposeWith_ord_old_old hv hdisjBar hxT hxt hyT hyt]
          exact hsplit.ord_iff x hxT y hyT
        · rw [decomposeWith_ord_old_new hwf₀ hv hdisj₀ (hsub x hxT) hyv,
            decomposeWith_ord_old_new hwfBar hv hdisjBar hxT hyv]
          exact hsplit.ord_iff x hxT tb htb
      · rcases hy with ⟨hyT, hyt⟩ | hyv
        · rw [decomposeWith_ord_new_old hwf₀ hv hdisj₀ hxv (hsub y hyT),
            decomposeWith_ord_new_old hwfBar hv hdisjBar hxv hyT]
          exact hsplit.ord_iff tb htb y hyT
        · rw [decomposeWith_ord_new_new hwf₀ hdisj₀ hxv hyv,
            decomposeWith_ord_new_new hwfBar hdisjBar hxv hyv]
    · intro x hx
      rw [mem_decomposeWith_T] at hx
      rcases hx with ⟨hxT, -⟩ | hxv
      · simp only [decomposeWith_α, if_neg (hvnot x (hsub x hxT))]
        exact hsplit.alpha x hxT
      · simp only [decomposeWith_α, if_pos hxv]
  · obtain ⟨ρ, hρbij, hρord, hρα⟩ := hviso
    have := decomposeWith_iso_congr hwfBar hwftn hv hu hdisjBar hdisj htb hbij hord hαiso
      hρbij hρord hρα
    rwa [htbσ] at this
  · -- the progressed prefix keeps its labels
    have hmap : lP.map (decomposeWith tn₀ tb v).α = lP.map tn₀.α := by
      refine List.map_congr_left ?_
      intro x hx
      have hx₀ : x ∈ tn₀.T := hsplit.mem_of_mem_prefix hx
      simp only [decomposeWith_α, if_neg (hvnot x hx₀)]
    simp only [IsActionSeq] at hact ⊢
    rw [hmap, hact]

/-- **Every reachable search node satisfies the invariant.** -/
theorem repr_of_reachableNode (hP : P.WF) {n : SearchNode F A C I} (h : P.ReachableNode n) :
    P.Repr n := by
  induction h with
  | refl => exact repr_initNode hP
  | @tail b c _ hstep ih =>
    have hwfb : b.net.WF := Problem.ReachableNode.wf hP (by assumption)
    cases hstep with
    | prog hu hα happ => exact repr_prog ih hu hα happ
    | decomp _ hstep => exact repr_decomp hP hwfb ih hstep

/-- **The plan of a reachable node is an executable prefix.**  At every point of the search the
actions progressed so far are applicable in the initial state, and the node's state is the state
they lead to. -/
theorem seqApplicable_plan_of_reachableNode (hP : P.WF) {n : SearchNode F A C I}
    (h : P.ReachableNode n) :
    P.SeqApplicable n.plan P.init ∧ n.state = P.transitionSeq n.plan P.init := by
  obtain ⟨-, -, -, -, -, -, -, -, hsapp, hstate⟩ := repr_of_reachableNode hP h
  exact ⟨hsapp, hstate⟩

/-- **Soundness of progression search** (Theorem 1 of the paper): the plan of a reachable goal
node is a solution plan of the problem. -/
theorem isSolutionPlan_of_goalNode (hP : P.WF) {n : SearchNode F A C I}
    (hreach : P.ReachableNode n) (hgoal : P.IsGoalNode n) : P.IsSolutionPlan n.plan := by
  obtain ⟨tn₀, tnBar, lP, hr, hwfBar, hsplit, hiso, hact, hsapp, hstate⟩ :=
    repr_of_reachableNode hP hreach
  -- the remaining network is empty
  have hBarempty : tnBar.T = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨σ, hbij, -, -⟩ := hiso
    have : σ x ∈ n.net.T := by simpa using hbij.mapsTo (by simpa using hx)
    rw [hgoal.1] at this
    simp at this
  -- so `lP` is a linearization of `tn₀`
  have hlin : tn₀.IsLinearization lP := by
    have hempty : (∅ : Finset I) = tnBar.T := hBarempty.symm
    have h := hsplit.isLinearization (l := []) ⟨List.nodup_nil, by
      intro x; constructor
      · intro hx; simp at hx
      · intro hx; rw [hBarempty] at hx; simp at hx, List.Pairwise.nil⟩
    simpa using h
  refine ⟨tn₀, lP, hr, ?_, hlin, hact, hsapp, ?_⟩
  · intro x hx
    exact TaskNetwork.isPrimitiveId_of_isActionSeq hact x ((hlin.2.1 x).2 hx)
  · rw [← hstate]
    exact hgoal.2

/-- **Soundness of the optimized progression search** (Theorem 1 for Algorithms 2 and 3): the
restricted search space is part of the full one, so its goal nodes carry solution plans too. -/
theorem isSolutionPlan_of_goalNodeSel (hP : P.WF) {sel : TaskNetwork I A C → I}
    {n : SearchNode F A C I}
    (hreach : Relation.ReflTransGen (P.StepSel sel) P.initNode n) (hgoal : P.IsGoalNode n) :
    P.IsSolutionPlan n.plan :=
  isSolutionPlan_of_goalNode hP
    (Relation.ReflTransGen.mono (fun _ _ hs => Problem.StepSel.step P hs) hreach) hgoal

/-- **The optimized progression search decides solvability**: restricting the search so that it
decomposes the selected task whenever an unconstrained abstract task exists, and progresses only
otherwise, still finds a goal node exactly for the solvable problems. -/
theorem solvable_iff_exists_goalNodeSel (hP : P.WF) {sel : TaskNetwork I A C → I}
    (hsel : ∀ tn : TaskNetwork I A C, tn.HasUncAbstract →
      tn.Unconstrained (sel tn) ∧ tn.IsAbstractId (sel tn)) :
    P.Solvable ↔ ∃ n : SearchNode F A C I,
      Relation.ReflTransGen (P.StepSel sel) P.initNode n ∧ P.IsGoalNode n := by
  constructor
  · intro h
    obtain ⟨as, has⟩ := Problem.solvable_iff_exists_solutionPlan.1 h
    obtain ⟨n, hr, hg, -⟩ := exists_goalNodeSel_of_isSolutionPlan hP hsel has
    exact ⟨n, hr, hg⟩
  · rintro ⟨n, hr, hg⟩
    exact Problem.solvable_iff_exists_solutionPlan.2
      ⟨n.plan, isSolutionPlan_of_goalNodeSel hP hr hg⟩

/-- **Progression search is sound and complete**: the problem is solvable exactly when the
search space contains a goal node. -/
theorem solvable_iff_exists_goalNode (hP : P.WF) :
    P.Solvable ↔ ∃ n : SearchNode F A C I, P.ReachableNode n ∧ P.IsGoalNode n := by
  constructor
  · intro h
    obtain ⟨as, has⟩ := Problem.solvable_iff_exists_solutionPlan.1 h
    obtain ⟨n, hr, hg, -⟩ := exists_goalNode_of_isSolutionPlan hP has
    exact ⟨n, hr, hg⟩
  · rintro ⟨n, hr, hg⟩
    exact Problem.solvable_iff_exists_solutionPlan.2 ⟨n.plan, isSolutionPlan_of_goalNode hP hr hg⟩

end Problem

end HTN
