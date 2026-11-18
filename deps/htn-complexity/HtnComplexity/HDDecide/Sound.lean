import HtnComplexity.HDDecide.Rep
/-!
# Soundness of the search on pieces

A run of the search on pieces (`HTN.HD.HStep`) is replayed by the progression search of the
semantics (`HTN.Problem.Step`): progressions and decompositions are replayed as they are, while
*regressed* tasks are kept in the task network, in a list `D` of deferred tasks, and executed at
the very end, in the reverse order of their regression.  The invariant `HTN.HD.SimS` relates a
configuration of the search on pieces to a search node and the list of deferred tasks:

* the remaining tasks of the node are the represented tasks (`HTN.HD.Rep`) and the deferred ones;
* no deferred task precedes a represented one, and the deferred tasks are listed in an order in
  line with the ordering;
* executing the deferred tasks, in the order of the list, from the backward state is possible and
  reaches a goal state.

Hence `HTN.HD.solvable_of_piecesSolvable`: the pieces criterion implies solvability (for every
described problem, one-hole-digging or not).
-/

namespace HTN

namespace HD

open Syn

variable {d : DomDesc} {q : InstDesc}

/-- The simulation invariant of the soundness proof. -/
structure SimS (d : DomDesc) (q : InstDesc) (c : HCfg) (n : SearchNode ℕ ℕ ℕ ℕ) (D : List ℕ)
    (Tp : Finset ℕ) : Prop where
  reach : (problem d q).ReachableNode n
  state : n.state = {f | f ∈ c.1}
  wf : n.net.WF
  disj : Disjoint Tp D.toFinset
  T_eq : n.net.T = Tp ∪ D.toFinset
  rep : Rep d q n.net Tp c.2.2
  nodup : D.Nodup
  notBefore : ∀ v ∈ D, ∀ y ∈ Tp, ¬ n.net.ord v y
  pairwise : D.Pairwise (fun a b => ¬ n.net.ord b a)
  back : ∃ as : List ℕ, D.map n.net.α = as.map Sum.inl ∧
    (problem d q).SeqApplicable as {f | f ∈ c.2.1} ∧
    (problem d q).GoalState ((problem d q).transitionSeq as {f | f ∈ c.2.1})

theorem simS_init {sω : Finset ℕ} (hsω : ∀ f ∈ q.goalList, f ∈ sω) :
    SimS d q (q.initList.toFinset, sω, initPieces q) (problem d q).initNode []
      q.tnI.ids.toFinset where
  reach := Relation.ReflTransGen.refl
  state := by ext f; simp [Problem.initNode]
  wf := (problem_wf d q).tnI
  disj := by simp
  T_eq := by simp [Problem.initNode]
  rep := ⟨_, _, _, _, repW_init⟩
  nodup := List.nodup_nil
  notBefore := by simp
  pairwise := List.Pairwise.nil
  back := ⟨[], rfl, trivial, fun f hf => hsω f hf⟩

/-- Executing the deferred tasks at the end of the run. -/
theorem goal_of_deferred : ∀ (D : List ℕ) (n : SearchNode ℕ ℕ ℕ ℕ) (as : List ℕ),
    (problem d q).ReachableNode n → n.net.WF → n.net.T = D.toFinset → D.Nodup →
    D.Pairwise (fun a b => ¬ n.net.ord b a) → D.map n.net.α = as.map Sum.inl →
    (problem d q).SeqApplicable as n.state →
    (problem d q).GoalState ((problem d q).transitionSeq as n.state) →
    ∃ n', (problem d q).ReachableNode n' ∧ (problem d q).IsGoalNode n' := by
  intro D
  induction D with
  | nil =>
    intro n as hr _ hT _ _ hα _ hg
    have : as = [] := by simpa using hα.symm
    subst this
    exact ⟨n, hr, by simpa using hT, hg⟩
  | cons v D ih =>
    intro n as hr hwf hT hnd hpw hα happ hg
    obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
      cases as with
      | nil => simp at hα
      | cons a as' => exact ⟨a, as', rfl⟩
    simp only [List.map_cons, List.cons.injEq] at hα
    obtain ⟨hva, hα'⟩ := hα
    obtain ⟨happa, happ'⟩ := happ
    have hvT : v ∈ n.net.T := by rw [hT]; simp
    have hunc : n.net.Unconstrained v := by
      refine ⟨hvT, fun t' ht' ho => ?_⟩
      rw [hT] at ht'
      rcases List.mem_cons.1 (List.mem_toFinset.1 ht') with rfl | ht'
      · exact hwf.irrefl _ ho
      · exact (List.rel_of_pairwise_cons hpw ht') ho
    have hstep : (problem d q).Step n ⟨(problem d q).transition a n.state, n.net.progress v,
        n.plan ++ [a]⟩ := Problem.Step.prog hunc hva happa
    have hnd' := (List.nodup_cons.1 hnd)
    refine ih _ as' (hr.tail hstep) (TaskNetwork.progress_wf hwf hunc) ?_ hnd'.2 ?_ ?_ happ' hg
    · show n.net.T.erase v = _
      rw [hT]
      ext y
      simp only [Finset.mem_erase, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro ⟨hne, rfl | hy⟩
        · exact absurd rfl hne
        · exact hy
      · intro hy
        exact ⟨fun he => hnd'.1 (he ▸ hy), Or.inr hy⟩
    · exact (List.pairwise_cons.1 hpw).2.imp fun h ho => h ho.1
    · simpa using hα'

/-- The end of a run: no pieces left, and the two states agree. -/
theorem goal_of_simS {s : Finset ℕ} {n : SearchNode ℕ ℕ ℕ ℕ} {D : List ℕ} {Tp : Finset ℕ}
    (h : SimS d q (s, s, 0) n D Tp) :
    ∃ n', (problem d q).ReachableNode n' ∧ (problem d q).IsGoalNode n' := by
  obtain ⟨U, inst, loc, kind, hw⟩ := h.rep
  have hTp : Tp = ∅ := hw.eq_zero_iff.1 rfl
  obtain ⟨as, hα, happ, hg⟩ := h.back
  refine goal_of_deferred D n as h.reach h.wf (by rw [h.T_eq, hTp]; simp) h.nodup h.pairwise hα
    ?_ ?_
  · rw [h.state]; exact happ
  · rw [h.state]; exact hg

/-- **One step of the search on pieces is replayed** by at most one step of the semantic
progression search. -/
theorem simS_step {c c' : HCfg} (hs : HStep d q c c') {n : SearchNode ℕ ℕ ℕ ℕ} {D : List ℕ}
    {Tp : Finset ℕ} (h : SimS d q c n D Tp) :
    ∃ n' D' Tp', SimS d q c' n' D' Tp' := by
  obtain ⟨U, inst, loc, kind, hw⟩ := h.rep
  -- the task of the piece
  have task : ∀ {k S x}, (k, S) ∈ c.2.2 → x ∈ S →
      ∃ t ∈ Tp, kind (inst t) = k ∧ Sof Tp inst loc (inst t) = S ∧ loc t = x :=
    fun hm hx => hw.exists_of_mem hm hx
  have hTpT : Tp ⊆ n.net.T := by rw [h.T_eq]; exact Finset.subset_union_left
  have hDT : ∀ v ∈ D, v ∈ n.net.T := by
    intro v hv; rw [h.T_eq]; exact Finset.mem_union_right _ (List.mem_toFinset.2 hv)
  have hnotD : ∀ t ∈ Tp, t ∉ D := fun t ht hD =>
    Finset.disjoint_left.1 h.disj ht (List.mem_toFinset.2 hD)
  -- a task without predecessors in its piece is unconstrained
  have unc : ∀ {t}, t ∈ Tp → (∀ t' ∈ Tp, ¬ n.net.ord t' t) → n.net.Unconstrained t := by
    intro t ht hno
    refine ⟨hTpT ht, fun t' ht' ho => ?_⟩
    rw [h.T_eq] at ht'
    rcases Finset.mem_union.1 ht' with ht' | ht'
    · exact hno t' ht' ho
    · exact h.notBefore t' (List.mem_toFinset.1 ht') t ht ho
  cases hs with
  | prog sf sb M k S x a hm hx hmin hlab happ =>
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := task hm hx
    have hno := hw.not_ord_of_min ht hmin
    have hu := unc ht hno
    have hα : n.net.α t = Sum.inl a := (hw.lbl t ht).trans hlab
    have happ' : (problem d q).Applicable a n.state := by
      rw [h.state]; exact (appF_iff d sf a).1 happ
    have hstep := Problem.Step.prog (P := problem d q) (π := n.plan) hu hα happ'
    refine ⟨⟨(problem d q).transition a n.state, n.net.progress t, n.plan ++ [a]⟩, D,
      Tp.erase t, ?_⟩
    obtain ⟨as, hαD, hbapp, hbg⟩ := h.back
    exact {
      reach := h.reach.tail hstep
      state := by
        show (problem d q).transition a n.state = _
        rw [h.state]; exact (coe_nxtF d sf a).symm
      wf := TaskNetwork.progress_wf h.wf hu
      disj := Finset.disjoint_of_subset_left (Finset.erase_subset _ _) h.disj
      T_eq := by
        show n.net.T.erase t = _
        rw [h.T_eq, Finset.erase_union_distrib, Finset.erase_eq_of_notMem
          (fun hD => hnotD t ht (List.mem_toFinset.1 hD))]
      rep := ⟨U, inst, loc, kind, (hw.erase ht).transfer (fun _ _ => rfl)
        (fun a ha b _ => by
          simp only [TaskNetwork.progress_ord]
          exact ⟨fun h => h.1, fun h => ⟨h, Finset.ne_of_mem_erase ha⟩⟩)⟩
      nodup := h.nodup
      notBefore := fun v hv y hy ho => h.notBefore v hv y (Finset.mem_of_mem_erase hy) ho.1
      pairwise := h.pairwise.imp fun h ho => h ho.1
      back := ⟨as, hαD, hbapp, hbg⟩ }
  | regr sf sb s M k S x a hm hx hmax hlab _ happ hnxt =>
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := task hm hx
    have hno := hw.not_ord_of_max ht hmax
    refine ⟨n, t :: D, Tp.erase t, ?_⟩
    obtain ⟨as, hαD, hbapp, hbg⟩ := h.back
    exact {
      reach := h.reach
      state := h.state
      wf := h.wf
      disj := by
        rw [Finset.disjoint_left]
        intro y hy hyD
        rcases List.mem_cons.1 (List.mem_toFinset.1 hyD) with rfl | hyD
        · exact Finset.notMem_erase y Tp hy
        · exact hnotD y (Finset.mem_of_mem_erase hy) hyD
      T_eq := by
        rw [h.T_eq]
        ext y
        simp only [Finset.mem_union, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
        constructor
        · rintro (hy | hy)
          · by_cases hyt : y = t
            · exact Or.inr (Or.inl hyt)
            · exact Or.inl ⟨hyt, hy⟩
          · exact Or.inr (Or.inr hy)
        · rintro (⟨-, hy⟩ | rfl | hy)
          · exact Or.inl hy
          · exact Or.inl ht
          · exact Or.inr hy
      rep := ⟨U, inst, loc, kind, hw.erase ht⟩
      nodup := List.nodup_cons.2 ⟨hnotD t ht, h.nodup⟩
      notBefore := by
        intro v hv y hy
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hno y (Finset.mem_of_mem_erase hy)
        · exact h.notBefore v hv y (Finset.mem_of_mem_erase hy)
      pairwise := List.Pairwise.cons (fun b hb ho => h.notBefore b hb t ht ho) h.pairwise
      back := by
        refine ⟨a :: as, ?_, ⟨(appF_iff d s a).1 happ, ?_⟩, ?_⟩
        · simp only [List.map_cons, hαD]
          rw [(hw.lbl t ht).trans hlab]
        · show (problem d q).SeqApplicable as ((problem d q).transition a _)
          have : (problem d q).transition a {f | f ∈ s} = {f | f ∈ sb} := by
            rw [← hnxt]; exact (coe_nxtF d s a).symm
          rw [this]; exact hbapp
        · show (problem d q).GoalState ((problem d q).transitionSeq as
            ((problem d q).transition a _))
          have : (problem d q).transition a {f | f ∈ s} = {f | f ∈ sb} := by
            rw [← hnxt]; exact (coe_nxtF d s a).symm
          rw [this]; exact hbg }
  | dec sf sb M k S x c j hm hx hiso hlab hj hname =>
    obtain ⟨t, ht, rfl, rfl, rfl⟩ := task hm hx
    have hno := hw.not_ord_of_min ht (fun y hy => (hiso y hy).1)
    have hno' := hw.not_ord_of_max ht (fun y hy => (hiso y hy).2)
    have hu := unc ht hno
    -- a fresh copy of the method's network
    obtain ⟨u, huwf, huiso, hdisj⟩ :=
      TaskNetwork.exists_fresh_iso_copy (net d q (j + 1)).toTaskNetwork
        (net d q (j + 1)).toTaskNetwork_wf n.net.T
    obtain ⟨σ, hbij, hord, hσα⟩ := huiso
    obtain ⟨i', hi'⟩ := Infinite.exists_notMem_finset U
    have hmeth : (d.methods.getD j default) ∈ d.methods := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have hstepD : DecompStep (problem d q).methods n.net t (d.methods.getD j default).toMethod
        (decomposeWith n.net t u) := by
      refine ⟨⟨_, hmeth, rfl⟩, hTpT ht, ?_, u, huwf, ⟨σ, hbij, hord, hσα⟩, hdisj, rfl⟩
      rw [hw.lbl t ht, hlab, ← hname]
      rfl
    have hstep := Problem.Step.decomp (P := problem d q) (s := n.state) (π := n.plan) hu hstepD
    have hw' := hw.decompose h.wf hTpT ht (fun y hy => ⟨hno y hy, hno' y hy⟩) huwf hbij
      hord hσα hdisj hi'
    have hDu : ∀ v ∈ D, v ∉ u.T := fun v hv => Finset.disjoint_left.1 hdisj (hDT v hv)
    have hnt : ∀ {x y : ℕ}, x ∉ n.net.T → ¬ n.net.ord x y := fun hx ho => hx (h.wf.mem_left ho)
    have hnt' : ∀ {x y : ℕ}, y ∉ n.net.T → ¬ n.net.ord x y :=
      fun hy ho => hy (h.wf.mem_right ho)
    have hnu : ∀ {x y : ℕ}, x ∉ u.T → ¬ u.ord x y := fun hx ho => hx (huwf.mem_left ho)
    -- the deferred tasks are ordered as before
    have hordD : ∀ v ∈ D, ∀ y, (decomposeWith n.net t u).ord v y →
        (n.net.ord v t ∧ y ∈ u.T) ∨ (n.net.ord v y ∧ y ≠ t) := by
      intro v hv y ho
      rcases ho with ho | ⟨ho, hy⟩ | ⟨-, hvu⟩ | ⟨ho, -, hyt⟩
      · exact absurd ho (hnu (hDu v hv))
      · exact Or.inl ⟨ho, hy⟩
      · exact absurd hvu (hDu v hv)
      · exact Or.inr ⟨ho, hyt⟩
    obtain ⟨as, hαD, hbapp, hbg⟩ := h.back
    refine ⟨⟨n.state, decomposeWith n.net t u, n.plan⟩, D, Tp.erase t ∪ u.T, ?_⟩
    exact {
      reach := h.reach.tail hstep
      state := h.state
      wf := decomposeWith_wf h.wf huwf hdisj
      disj := by
        rw [Finset.disjoint_left]
        intro y hy hyD
        rcases Finset.mem_union.1 hy with hy | hy
        · exact hnotD y (Finset.mem_of_mem_erase hy) (List.mem_toFinset.1 hyD)
        · exact hDu y (List.mem_toFinset.1 hyD) hy
      T_eq := by
        show n.net.T.erase t ∪ u.T = _
        rw [h.T_eq, Finset.erase_union_distrib, Finset.erase_eq_of_notMem
          (fun hD => hnotD t ht (List.mem_toFinset.1 hD))]
        ext y
        simp only [Finset.mem_union]
        tauto
      rep := ⟨_, _, _, _, hw'⟩
      nodup := h.nodup
      notBefore := by
        intro v hv y hy ho
        rcases hordD v hv y ho with ⟨ho, -⟩ | ⟨ho, hyt⟩
        · exact h.notBefore v hv t ht ho
        · rcases Finset.mem_union.1 hy with hy | hy
          · exact h.notBefore v hv y (Finset.mem_of_mem_erase hy) ho
          · exact hnt' (fun hyT => Finset.disjoint_left.1 hdisj hyT hy) ho
      pairwise := by
        refine h.pairwise.imp_of_mem fun {a b} ha hb hn ho => ?_
        rcases hordD b hb a ho with ⟨-, hau⟩ | ⟨ho, -⟩
        · exact hDu a ha hau
        · exact hn ho
      back := ⟨as, by
          rw [← hαD]
          refine List.map_congr_left fun v hv => ?_
          simp [decomposeWith_α, hDu v hv], hbapp, hbg⟩ }

/-- Runs of the search on pieces are replayed. -/
theorem simS_reach {c c' : HCfg} (hr : HReach d q c c') :
    ∀ {n D Tp}, SimS d q c n D Tp → ∃ n' D' Tp', SimS d q c' n' D' Tp' := by
  induction hr with
  | refl => exact fun h => ⟨_, _, _, h⟩
  | tail _ hs ih =>
    intro n D Tp h
    obtain ⟨n', D', Tp', h'⟩ := ih h
    exact simS_step hs h'

/-- **Soundness of the pieces criterion.** -/
theorem solvable_of_piecesSolvable (h : PiecesSolvable d q) : Solvable d q := by
  obtain ⟨sω, s, -, hsω, hr⟩ := h
  obtain ⟨n, D, Tp, hn⟩ := simS_reach hr (simS_init (d := d) hsω)
  obtain ⟨n', hr', hg⟩ := goal_of_simS hn
  exact (Problem.solvable_iff_exists_goalNode (problem_wf d q)).2 ⟨n', hr', hg⟩

end HD

end HTN
