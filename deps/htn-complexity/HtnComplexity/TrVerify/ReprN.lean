import HtnPlanning.Progression.ProgressionSound
/-!
# Progression soundness with a count of the decomposition steps

`HtnPlanning/Progression/ProgressionSound.lean` proves that the plan of a reachable goal
node of progression search is a solution plan, through the invariant `HTN.Problem.Repr`, which
records a task network `tn₀` *reachable by decomposition* from the initial task network.  The
upper bound for tail-recursive problems (`HtnComplexity/TrVerify/`) needs to know **how
many** decomposition steps lead to `tn₀`: at most the number of steps of the search run.

This file generalises the invariant to an arbitrary predicate `R` on `tn₀`
(`HTN.Problem.ReprG`); `HTN.Problem.Repr` is the instance `R = P.Reachable`.  The invariant is
preserved by progression with the same `R`, and by decomposition from `R` to any `R'` that
contains the one-step decompositions of `R` (`HTN.Problem.reprG_decomp`).  The counted version
`HTN.Problem.DecompN` (decomposition in exactly `k` steps) then gives
`HTN.Problem.isSolution_decompN_of_run`: a search run of length `k` that ends in a goal node
yields a solution task network reached by decomposition in at most `k` steps.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable [DecidableEq I] [Infinite I] {P : Problem F A C I}

open TaskNetwork

/-- **The invariant of progression search, for a predicate `R` on the decomposed network.**
As `HTN.Problem.Repr`, with `P.Reachable tn₀` replaced by `R tn₀`. -/
def ReprG (P : Problem F A C I) (R : TaskNetwork I A C → Prop) (n : SearchNode F A C I) : Prop :=
  ∃ (tn₀ tnBar : TaskNetwork I A C) (lP : List I),
    R tn₀ ∧ tnBar.WF ∧ Split tn₀ lP tnBar ∧ tnBar.Iso n.net ∧
      tn₀.IsActionSeq lP n.plan ∧ P.SeqApplicable n.plan P.init ∧
      n.state = P.transitionSeq n.plan P.init

omit [DecidableEq I] [Infinite I] in
/-- The initial node satisfies the invariant for every `R` holding at the initial network. -/
lemma reprG_initNode (hP : P.WF) {R : TaskNetwork I A C → Prop} (hR : R P.tnI) :
    P.ReprG R P.initNode := by
  refine ⟨P.tnI, P.tnI, [], hR, hP.tnI, ?_, TaskNetwork.Iso.refl _, rfl, trivial, rfl⟩
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
lemma reprG_prog {R : TaskNetwork I A C → Prop} {s : Set F} {tn : TaskNetwork I A C} {π : List A} {t : I} {a : A}
    (hrepr : P.ReprG R ⟨s, tn, π⟩) (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a)
    (happ : P.Applicable a s) :
    P.ReprG R ⟨P.transition a s, tn.progress t, π ++ [a]⟩ := by
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
lemma reprG_decomp {R R' : TaskNetwork I A C → Prop} {s : Set F} {tn tn' : TaskNetwork I A C} {π : List A} {t : I}
    {m : Method I A C} (hwftn : tn.WF) (hrepr : P.ReprG R ⟨s, tn, π⟩)
    (hstep : DecompStep P.methods tn t m tn')
    (hRwf : ∀ tn₀, R tn₀ → tn₀.WF)
    (hR : ∀ tn₀ tn₁, R tn₀ → DecompStep' P.methods tn₀ tn₁ → R' tn₁) :
    P.ReprG R' ⟨s, tn', π⟩ := by
  obtain ⟨tn₀, tnBar, lP, hreach, hwfBar, hsplit, hiso, hact, hsapp, hstate⟩ := hrepr
  obtain ⟨hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hstep
  obtain ⟨σ, hbij, hord, hαiso⟩ := hiso
  have hwf₀ : tn₀.WF := hRwf _ hreach
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
    hR _ _ hreach ⟨tb, m, hmM, htb₀, hαtb, v, hv, hviso.trans huiso,
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


/-! ### Counting the decomposition steps -/

/-- `DecompN M k tn tn'`: `tn` decomposes into `tn'` in exactly `k` steps. -/
def DecompN (M : Set (Method I A C)) : ℕ → TaskNetwork I A C → TaskNetwork I A C → Prop
  | 0, a, b => a = b
  | k + 1, a, c => ∃ b, DecompN M k a b ∧ DecompStep' M b c

omit [Infinite I] in
theorem DecompN.decomposesTo {M : Set (Method I A C)} :
    ∀ {k : ℕ} {a b : TaskNetwork I A C}, DecompN M k a b → HTN.DecomposesTo M a b
  | 0, _, _, h => h ▸ Relation.ReflTransGen.refl
  | _ + 1, _, _, ⟨_, h, hs⟩ => (DecompN.decomposesTo h).tail hs

/-- The networks reached from the initial task network in at most `k` decomposition steps. -/
def RN (P : Problem F A C I) (k : ℕ) (tn : TaskNetwork I A C) : Prop :=
  ∃ j ≤ k, DecompN P.methods j P.tnI tn

omit [Infinite I] in
theorem RN.wf (hP : P.WF) {k : ℕ} {tn : TaskNetwork I A C} (h : P.RN k tn) : tn.WF := by
  obtain ⟨j, -, hj⟩ := h
  exact HTN.DecomposesTo.wf hj.decomposesTo hP.tnI

omit [Infinite I] in
theorem RN.mono {k k' : ℕ} (hk : k ≤ k') {tn : TaskNetwork I A C} (h : P.RN k tn) :
    P.RN k' tn := by
  obtain ⟨j, hj, h⟩ := h
  exact ⟨j, hj.trans hk, h⟩

omit [DecidableEq I] [Infinite I] in
theorem ReprG.mono {R R' : TaskNetwork I A C → Prop} (hRR : ∀ tn, R tn → R' tn)
    {n : SearchNode F A C I} (h : P.ReprG R n) : P.ReprG R' n := by
  obtain ⟨tn₀, tnBar, lP, hR, rest⟩ := h
  exact ⟨tn₀, tnBar, lP, hRR _ hR, rest⟩

/-- `StepN P k n n'`: a run of the progression search of exactly `k` steps. -/
def StepN (P : Problem F A C I) : ℕ → SearchNode F A C I → SearchNode F A C I → Prop
  | 0, a, b => a = b
  | k + 1, a, c => ∃ b, StepN P k a b ∧ P.Step b c

omit [Infinite I] in
theorem StepN.reachableNode : ∀ {k : ℕ} {n : SearchNode F A C I},
    P.StepN k P.initNode n → P.ReachableNode n
  | 0, _, h => h ▸ ReachableNode.refl P
  | _ + 1, _, ⟨_, h, hs⟩ => (StepN.reachableNode h).tail hs

/-- **A run of `k` search steps keeps the invariant with at most `k` decomposition steps.** -/
theorem reprG_RN_of_stepN (hP : P.WF) :
    ∀ {k : ℕ} {n : SearchNode F A C I}, P.StepN k P.initNode n → P.ReprG (P.RN k) n
  | 0, _, h => h ▸ reprG_initNode hP ⟨0, le_rfl, rfl⟩
  | k + 1, n, ⟨b, hb, hs⟩ => by
    have ih := reprG_RN_of_stepN hP hb
    have hwfb : b.net.WF := ReachableNode.wf hP hb.reachableNode
    cases hs with
    | prog hu hα happ =>
      exact (reprG_prog ih hu hα happ).mono fun _ h => h.mono (Nat.le_succ k)
    | decomp _ hstep =>
      refine reprG_decomp hwfb ih hstep (fun _ h => h.wf hP) ?_
      rintro tn₀ tn₁ ⟨j, hj, h⟩ hs
      exact ⟨j + 1, by omega, tn₀, h, hs⟩

/-- **Counted soundness of progression search**: a run of `k` steps from the initial node to a
goal node yields a solution task network reached by at most `k` decomposition steps. -/
theorem exists_solution_RN_of_stepN (hP : P.WF) {k : ℕ} {n : SearchNode F A C I}
    (hrun : P.StepN k P.initNode n) (hgoal : P.IsGoalNode n) :
    ∃ tn₀, P.RN k tn₀ ∧ tn₀.IsPrimitive ∧ P.Executable tn₀ := by
  obtain ⟨tn₀, tnBar, lP, hr, hwfBar, hsplit, hiso, hact, hsapp, hstate⟩ :=
    reprG_RN_of_stepN hP hrun
  have hBarempty : tnBar.T = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨σ, hbij, -, -⟩ := hiso
    have : σ x ∈ n.net.T := by simpa using hbij.mapsTo (by simpa using hx)
    rw [hgoal.1] at this
    simp at this
  have hlin : tn₀.IsLinearization lP := by
    have h := hsplit.isLinearization (l := []) ⟨List.nodup_nil, by
      intro x; constructor
      · intro hx; simp at hx
      · intro hx; rw [hBarempty] at hx; simp at hx, List.Pairwise.nil⟩
    simpa using h
  refine ⟨tn₀, hr, ?_, lP, n.plan, hlin, hact, hsapp, ?_⟩
  · intro x hx
    exact TaskNetwork.isPrimitiveId_of_isActionSeq hact x ((hlin.2.1 x).2 hx)
  · rw [← hstate]
    exact hgoal.2

end Problem

end HTN
