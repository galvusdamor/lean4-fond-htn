import HtnPlanning.Core.DecompCommute
/-!
# What decomposition does to the tasks that are already there

Decomposition only ever replaces one abstract task by a fresh network.  Consequently the tasks
that are *not* decomposed keep their name and their mutual ordering, primitive tasks survive
any decomposition sequence, and — the key fact for the completeness of progression search — a
task that is unconstrained after a decomposition sequence was already unconstrained before it,
*provided* that the network had no unconstrained abstract task to begin with
(`HTN.DecomposesTo.unconstrained_of_not_hasUA`).

The last statement is what makes progression search complete: while an unconstrained abstract
task exists the search decomposes it (and `HTN.DecomposesToN.pull_out` lets the solution's
decomposition sequence be reordered accordingly); when none exists, the task that the solution
executes next is already present and unconstrained, so the search can progress it.
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

namespace TaskNetwork

variable [DecidableEq I]

omit [DecidableEq I] in
/-- A nonempty well-formed task network has an unconstrained task. -/
lemma exists_unconstrained {tn : TaskNetwork I A C} (hwf : tn.WF) (hne : tn.T.Nonempty) :
    ∃ t, tn.Unconstrained t := by
  obtain ⟨t, ht, hmin⟩ :=
    TaskNetwork.exists_minimal_of_finset (r := tn.ord) hwf.irrefl hwf.trans tn.T hne
  exact ⟨t, ht, hmin⟩

omit [DecidableEq I] in
/-- A task with a predecessor has a *minimal* predecessor, and a minimal predecessor is
unconstrained. -/
lemma exists_unconstrained_pred {tn : TaskNetwork I A C} (hwf : tn.WF) {t z : I}
    (hz : tn.ord z t) : ∃ y, tn.Unconstrained y ∧ tn.ord y t := by
  classical
  set S : Finset I := tn.T.filter (fun y => tn.ord y t) with hS
  have hSne : S.Nonempty := ⟨z, Finset.mem_filter.2 ⟨hwf.mem_left hz, hz⟩⟩
  obtain ⟨y, hyS, hmin⟩ :=
    TaskNetwork.exists_minimal_of_finset (r := tn.ord) hwf.irrefl hwf.trans S hSne
  obtain ⟨hyT, hyt⟩ := Finset.mem_filter.1 hyS
  refine ⟨y, ⟨hyT, ?_⟩, hyt⟩
  intro z' hz' hcon
  exact hmin z' (Finset.mem_filter.2 ⟨hz', hwf.trans hcon hyt⟩) hcon

end TaskNetwork

section Step

variable [DecidableEq I] {M : Set (Method I A C)} {tn tna : TaskNetwork I A C}

/-- Well-formedness is preserved by a decomposition step. -/
lemma DecompStep'.wf (h : DecompStep' M tn tna) (hwf : tn.WF) : tna.WF := by
  obtain ⟨t, m, hs⟩ := h
  exact hs.wf hwf

/-- Tasks that survive a decomposition step keep their name. -/
lemma DecompStep'.α_eq (hstep : DecompStep' M tn tna) {x : I} (hx : x ∈ tn.T) :
    tna.α x = tn.α x := by
  obtain ⟨-, -, -, -, -, u, -, -, hdisj, rfl⟩ := hstep
  have : x ∉ u.T := Finset.disjoint_left.1 hdisj hx
  simp [decomposeWith_α, this]

/-- Primitive tasks are never decomposed, so they survive a decomposition step. -/
lemma DecompStep'.mem_of_isPrimitiveId (hstep : DecompStep' M tn tna) {x : I} (hx : x ∈ tn.T)
    (hprim : tn.IsPrimitiveId x) : x ∈ tna.T := by
  obtain ⟨t, m, -, -, hα, u, -, -, -, rfl⟩ := hstep
  refine mem_decomposeWith_T.2 (Or.inl ⟨hx, ?_⟩)
  rintro rfl
  obtain ⟨a, ha⟩ := hprim
  rw [ha] at hα
  exact Sum.inl_ne_inr hα

/-- Tasks that survive a decomposition step keep their mutual ordering. -/
lemma DecompStep'.ord_iff (hstep : DecompStep' M tn tna) {x y : I}
    (hx : x ∈ tn.T) (hy : y ∈ tn.T) (hx' : x ∈ tna.T) (hy' : y ∈ tna.T) :
    tna.ord x y ↔ tn.ord x y := by
  obtain ⟨t, m, -, -, -, u, hu, -, hdisj, rfl⟩ := hstep
  have hxu : x ∉ u.T := Finset.disjoint_left.1 hdisj hx
  have hyu : y ∉ u.T := Finset.disjoint_left.1 hdisj hy
  have hxt : x ≠ t := by
    rcases mem_decomposeWith_T.1 hx' with ⟨-, h⟩ | h
    · exact h
    · exact absurd h hxu
  have hyt : y ≠ t := by
    rcases mem_decomposeWith_T.1 hy' with ⟨-, h⟩ | h
    · exact h
    · exact absurd h hyu
  exact decomposeWith_ord_old_old hu hdisj hx hxt hy hyt

/-- **A task that is unconstrained after a decomposition step was unconstrained before it**,
provided the network had no unconstrained abstract task. -/
lemma DecompStep'.unconstrained_of_not_hasUncAbstract (hstep : DecompStep' M tn tna)
    (hwf : tn.WF) (hno : ¬ tn.HasUncAbstract) {v : I} (hv : tna.Unconstrained v) :
    tn.Unconstrained v := by
  obtain ⟨t, m, -, htT, hαt, u, hu, -, hdisj, rfl⟩ := hstep
  -- `t` is abstract, hence constrained; a minimal predecessor `y₀` of `t` is unconstrained
  have habs : tn.IsAbstractId t := ⟨m.abstractTask, hαt⟩
  have hcon : ¬ tn.Unconstrained t := fun h => hno ⟨t, h, habs⟩
  obtain ⟨z, hzT, hz⟩ : ∃ z ∈ tn.T, tn.ord z t := by
    by_contra hcon'
    exact hcon ⟨htT, fun z hz hcz => hcon' ⟨z, hz, hcz⟩⟩
  obtain ⟨y, hyunc, hyt⟩ := TaskNetwork.exists_unconstrained_pred hwf hz
  have hyT : y ∈ tn.T := hyunc.1
  have hynet : y ≠ t := by rintro rfl; exact hwf.irrefl y hyt
  have hyna : y ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inl ⟨hyT, hynet⟩)
  -- `v` cannot be one of the new tasks
  have hvold : v ∈ tn.T ∧ v ≠ t := by
    rcases mem_decomposeWith_T.1 hv.1 with h | hnew
    · exact h
    · exfalso
      have : (decomposeWith tn t u).ord y v :=
        (decomposeWith_ord_old_new hwf hu hdisj hyT hnew).2 hyt
      exact hv.2 y hyna this
  refine ⟨hvold.1, ?_⟩
  intro z' hz'T hz'v
  by_cases hz't : z' = t
  · subst hz't
    -- `y ≺ t ≺ v`, and both `y` and `v` survive the step
    have hyv : tn.ord y v := hwf.trans hyt hz'v
    have : (decomposeWith tn z' u).ord y v :=
      (decomposeWith_ord_old_old hu hdisj hyT hynet hvold.1 hvold.2).2 hyv
    exact hv.2 y hyna this
  · have hz'na : z' ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inl ⟨hz'T, hz't⟩)
    have : (decomposeWith tn t u).ord z' v :=
      (decomposeWith_ord_old_old hu hdisj hz'T hz't hvold.1 hvold.2).2 hz'v
    exact hv.2 z' hz'na this

/-- If a network has no unconstrained abstract task, neither has any of its decompositions. -/
lemma DecompStep'.not_hasUncAbstract (hstep : DecompStep' M tn tna) (hwf : tn.WF)
    (hno : ¬ tn.HasUncAbstract) : ¬ tna.HasUncAbstract := by
  rintro ⟨v, hv, c, hc⟩
  have hvold : tn.Unconstrained v := hstep.unconstrained_of_not_hasUncAbstract hwf hno hv
  refine hno ⟨v, hvold, c, ?_⟩
  rw [← hstep.α_eq hvold.1]
  exact hc

end Step

section Seq

variable [DecidableEq I] {M : Set (Method I A C)} {tn tnStar : TaskNetwork I A C}

/-- **Primitive tasks survive any decomposition sequence**, with their name. -/
lemma DecomposesTo.mem_of_isPrimitiveId (h : DecomposesTo M tn tnStar) {x : I} :
    x ∈ tn.T → tn.IsPrimitiveId x → x ∈ tnStar.T ∧ tnStar.IsPrimitiveId x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hx hprim => ⟨hx, hprim⟩
  | @head a b hstep _ ih =>
    intro hx hprim
    have hxb : x ∈ b.T := hstep.mem_of_isPrimitiveId hx hprim
    have hprimb : b.IsPrimitiveId x := by
      obtain ⟨n, hn⟩ := hprim
      exact ⟨n, by rw [hstep.α_eq hx]; exact hn⟩
    exact ih hxb hprimb

/-- **A task that is unconstrained after a decomposition sequence was unconstrained before
it**, and has the same name, provided the network had no unconstrained abstract task. -/
lemma DecomposesTo.unconstrained_of_not_hasUncAbstract (h : DecomposesTo M tn tnStar)
    {v : I} (hv : tnStar.Unconstrained v) :
    tn.WF → ¬ tn.HasUncAbstract → tn.Unconstrained v ∧ tnStar.α v = tn.α v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ _ => ⟨hv, rfl⟩
  | @head a b hstep _ ih =>
    intro hwfa hnoa
    have hwfb : b.WF := hstep.wf hwfa
    have hnob : ¬ b.HasUncAbstract := hstep.not_hasUncAbstract hwfa hnoa
    obtain ⟨hvb, hαb⟩ := ih hwfb hnob
    have hva : a.Unconstrained v := hstep.unconstrained_of_not_hasUncAbstract hwfa hnoa hvb
    exact ⟨hva, by rw [hαb, hstep.α_eq hva.1]⟩

/-- **Progression commutes with a decomposition sequence.** -/
lemma DecomposesToN.progress {n : ℕ} {t₁ : I} (h : DecomposesToN M n tn tnStar) :
    t₁ ∈ tn.T → tn.IsPrimitiveId t₁ →
      DecomposesToN M n (tn.progress t₁) (tnStar.progress t₁) := by
  induction h with
  | refl tn => exact fun _ _ => DecomposesToN.refl _
  | @head a b c n hstep _ ih =>
    intro ht₁ hprim
    obtain ⟨t, m, hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hstep
    have hstep' : DecompStep' M a (decomposeWith a t u) :=
      ⟨t, m, hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩
    have hne : t₁ ≠ t := by
      rintro rfl
      obtain ⟨x, hx⟩ := hprim
      rw [hx] at hαt
      exact Sum.inl_ne_inr hαt
    have ht₁u : t₁ ∉ u.T := Finset.disjoint_left.1 hdisj ht₁
    have ht₁b : t₁ ∈ (decomposeWith a t u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht₁, hne⟩)
    have hprimb : (decomposeWith a t u).IsPrimitiveId t₁ := by
      obtain ⟨x, hx⟩ := hprim
      exact ⟨x, by rw [hstep'.α_eq ht₁]; exact hx⟩
    have hstepP : DecompStep' M (a.progress t₁) (decomposeWith (a.progress t₁) t u) := by
      refine ⟨t, m, hmM, ?_, ?_, u, hu, huiso, ?_, rfl⟩
      · exact TaskNetwork.mem_progress_T.2 ⟨fun h => hne h.symm, htT⟩
      · exact hαt
      · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
    refine DecomposesToN.head hstepP ?_
    have hcomm : (decomposeWith a t u).progress t₁ = decomposeWith (a.progress t₁) t u :=
      progress_decomposeWith_comm hu hne ht₁u
    rw [← hcomm]
    exact ih ht₁b hprimb

end Seq

end HTN
