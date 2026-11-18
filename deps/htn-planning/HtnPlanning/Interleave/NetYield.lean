import HtnPlanning.Interleave.ParallelDecomp
import HtnPlanning.Core.Size
import HtnPlanning.Core.SolutionIso
/-!
# Refinement of an arbitrary task network into an action sequence

`HtnPlanning/Core/TONormalForm.lean` describes the refinements of a *totally ordered* task
network by the relation `HTN.Domain.YieldSeq` on task sequences.  Networks that are not totally
ordered — such as the initial task network of the HTN-AC compilation, a parallel composition of
exponentially many memory cells and proof steps — need a relation that admits arbitrary
*interleavings* of the parts.  This file introduces it:

`HTN.Domain.NetYieldN D n tn as` — the task network `tn` can be decomposed in `n` steps into a
primitive network one of whose linearizations induces the action sequence `as`;
`HTN.Domain.NetYield D tn as` — the same with the number of steps forgotten.

This is exactly the notion appearing in the solution criteria: `HTN.Problem.isSolutionPlan_iff`
states that the solution plans of a planning problem are the refinements of its initial task
network that are executable in the initial state and reach the goal.

The results of this file are the structural rules of the new relation:

* `HTN.Domain.NetYieldN.iso` — it only depends on the task network up to renaming of identifiers;
* `HTN.Domain.netYieldN_isPar_iff` — a **parallel** composition is refined exactly by the
  interleavings of refinements of its parts, the numbers of steps adding up;
* `HTN.Domain.netYieldN_isSeries_iff` — a **sequential** composition is refined exactly by the
  concatenations of refinements of its parts;
* `HTN.Domain.netYieldN_single_prim` and `HTN.Domain.netYieldN_single_comp` — a network with a
  single task is refined by that action, resp. by the refinements of the subtask networks of the
  methods for that compound task, one step being spent on the method application.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Domain

variable [DecidableEq I] (D : Domain F A C I)

/-- `D.NetYieldN n tn as`: the task network `tn` can be decomposed in exactly `n` steps into a
primitive task network having a linearization whose action sequence is `as`. -/
def NetYieldN (n : ℕ) (tn : TaskNetwork I A C) (as : List A) : Prop :=
  ∃ tn' : TaskNetwork I A C, StepsN D.methods n tn tn' ∧ tn'.IsPrimitive ∧
    ∃ l : List I, tn'.IsLinearization l ∧ tn'.IsActionSeq l as

/-- `D.NetYield tn as`: the task network `tn` can be refined into the action sequence `as`. -/
def NetYield (tn : TaskNetwork I A C) (as : List A) : Prop := ∃ n, D.NetYieldN n tn as

variable {D}

lemma NetYieldN.netYield {n : ℕ} {tn : TaskNetwork I A C} {as : List A}
    (h : D.NetYieldN n tn as) : D.NetYield tn as := ⟨n, h⟩

/-- The refinement relation in terms of the decomposition relation `→*`. -/
lemma netYield_iff {tn : TaskNetwork I A C} {as : List A} :
    D.NetYield tn as ↔ ∃ tn' : TaskNetwork I A C, DecomposesTo D.methods tn tn' ∧
      tn'.IsPrimitive ∧ ∃ l : List I, tn'.IsLinearization l ∧ tn'.IsActionSeq l as := by
  constructor
  · rintro ⟨n, tn', hsteps, hprim, l, hlin, has⟩
    exact ⟨tn', hsteps.decomposesTo, hprim, l, hlin, has⟩
  · rintro ⟨tn', hd, hprim, l, hlin, has⟩
    obtain ⟨n, hn⟩ := exists_stepsN hd
    exact ⟨n, tn', hn, hprim, l, hlin, has⟩

/-- **Refinement is invariant under renaming of the task identifiers.** -/
lemma NetYieldN.iso [Infinite I] {n : ℕ} {tn tn' : TaskNetwork I A C} {as : List A}
    (h : D.NetYieldN n tn as) (hwf : tn.WF) (hwf' : tn'.WF) (hiso : tn.Iso tn') :
    D.NetYieldN n tn' as := by
  obtain ⟨sol, hsteps, hprim, l, hlin, has⟩ := h
  obtain ⟨sol', hsteps', hsoliso⟩ := hsteps.iso_avoiding tn' hwf hwf' hiso ∅
  obtain ⟨l', hlin', has'⟩ := (hsoliso.exists_linearization_actionSeq_iff as).1 ⟨l, hlin, has⟩
  exact ⟨sol', hsteps'.stepsN, TaskNetwork.Iso.isPrimitive hsoliso hprim, l', hlin', has'⟩

end Domain

namespace Problem

variable [DecidableEq I] {P : Problem F A C I}

/-- **The solution plans of a planning problem are the refinements of its initial task network
that are executable in the initial state and reach the goal.** -/
theorem isSolutionPlan_iff {as : List A} :
    P.IsSolutionPlan as ↔ P.domain.NetYield P.tnI as ∧ P.SeqApplicable as P.init ∧
      P.GoalState (P.transitionSeq as P.init) := by
  constructor
  · rintro ⟨tn, l, hreach, hprim, hlin, has, happ, hgoal⟩
    exact ⟨Domain.netYield_iff.2 ⟨tn, hreach, hprim, l, hlin, has⟩, happ, hgoal⟩
  · rintro ⟨hy, happ, hgoal⟩
    obtain ⟨tn, hreach, hprim, l, hlin, has⟩ := Domain.netYield_iff.1 hy
    exact ⟨tn, l, hreach, hprim, hlin, has, happ, hgoal⟩

/-- **A planning problem is solvable exactly when its initial task network can be refined into
an executable action sequence reaching the goal.** -/
theorem solvable_iff_netYield :
    P.Solvable ↔ ∃ as : List A, P.domain.NetYield P.tnI as ∧ P.SeqApplicable as P.init ∧
      P.GoalState (P.transitionSeq as P.init) := by
  rw [solvable_iff_exists_solutionPlan]
  exact exists_congr fun _ => isSolutionPlan_iff

end Problem

namespace Domain

variable [DecidableEq I] {D : Domain F A C I}

open TaskNetwork

/-! ### Refinements of a parallel composition -/

/-- **Refinements of a parallel composition are the interleavings of refinements of the two
parts.** -/
theorem netYieldN_isPar_iff [Infinite I] {n : ℕ} {tn tn₁ tn₂ : TaskNetwork I A C} {as : List A}
    (h : IsPar tn tn₁ tn₂) (hw₁ : tn₁.WF) (hw₂ : tn₂.WF) :
    D.NetYieldN n tn as ↔ ∃ (n₁ n₂ : ℕ) (as₁ as₂ : List A), n = n₁ + n₂ ∧
      Interleave as₁ as₂ as ∧ D.NetYieldN n₁ tn₁ as₁ ∧ D.NetYieldN n₂ tn₂ as₂ := by
  classical
  constructor
  · rintro ⟨sol, hsteps, hprim, l, hlin, has⟩
    obtain ⟨n₁, n₂, a, b, rfl, ha, hb, hpar⟩ := h.stepsN_split hw₁ hw₂ hsteps
    obtain ⟨hpa, hpb⟩ := hpar.isPrimitive_iff.1 hprim
    obtain ⟨l₁, l₂, hint, hlin₁, hlin₂⟩ := hpar.exists_interleave_of_isLinearization hlin
    obtain ⟨as₁, as₂, hintas, has₁, has₂⟩ :=
      exists_interleave_actionSeq hint (fun t ht => hpar.α₁ t ((hlin₁.2.1 t).1 ht))
        (fun t ht => hpar.α₂ t ((hlin₂.2.1 t).1 ht)) has
    exact ⟨n₁, n₂, as₁, as₂, rfl, hintas, ⟨a, ha, hpa, l₁, hlin₁, has₁⟩,
      ⟨b, hb, hpb, l₂, hlin₂, has₂⟩⟩
  · rintro ⟨n₁, n₂, as₁, as₂, rfl, hint, ⟨a, ha, hpa, l₁, hlin₁, has₁⟩,
      ⟨b, hb, hpb, l₂, hlin₂, has₂⟩⟩
    -- run the derivation of the left part inside the composition, avoiding the right part
    obtain ⟨a', ha', haiso⟩ := ha.iso_avoiding tn₁ hw₁ hw₁ (Iso.refl _) tn₂.T
    obtain ⟨tnA, hstepsA, hparA⟩ := h.stepsN_lift_left hw₂ ha'
    have hawf : a.WF := ha.wf hw₁
    have ha'wf : a'.WF := ha'.stepsN.wf hw₁
    -- now the derivation of the right part, avoiding the (already decomposed) left part
    obtain ⟨b', hb', hbiso⟩ := hb.iso_avoiding tn₂ hw₂ hw₂ (Iso.refl _) a'.T
    obtain ⟨tnB, hstepsB, hparB⟩ := hparA.stepsN_lift_right ha'wf hb'
    obtain ⟨l₁', hlin₁', has₁'⟩ := (haiso.exists_linearization_actionSeq_iff as₁).1
      ⟨l₁, hlin₁, has₁⟩
    obtain ⟨l₂', hlin₂', has₂'⟩ := (hbiso.exists_linearization_actionSeq_iff as₂).1
      ⟨l₂, hlin₂, has₂⟩
    have hb'wf : b'.WF := hb'.stepsN.wf hw₂
    refine ⟨tnB, hstepsA.trans hstepsB, hparB.isPrimitive_iff.2
      ⟨TaskNetwork.Iso.isPrimitive haiso hpa, TaskNetwork.Iso.isPrimitive hbiso hpb⟩, ?_⟩
    obtain ⟨lint, hintl, hasint⟩ := exists_interleave_ids hint
      (fun t ht => hparB.α₁ t ((hlin₁'.2.1 t).1 ht))
      (fun t ht => hparB.α₂ t ((hlin₂'.2.1 t).1 ht)) has₁' has₂'
    exact ⟨lint, hparB.isLinearization_of_interleave ha'wf hb'wf hintl hlin₁' hlin₂', hasint⟩

/-! ### Refinements of a sequential composition -/

/-- **Refinements of a sequential composition are the concatenations of refinements of the two
parts.** -/
theorem netYieldN_isSeries_iff [Infinite I] {n : ℕ} {tn tn₁ tn₂ : TaskNetwork I A C}
    {as : List A} (h : IsSeries tn tn₁ tn₂) (hw₁ : tn₁.WF) (hw₂ : tn₂.WF) :
    D.NetYieldN n tn as ↔ ∃ (n₁ n₂ : ℕ) (as₁ as₂ : List A), n = n₁ + n₂ ∧ as = as₁ ++ as₂ ∧
      D.NetYieldN n₁ tn₁ as₁ ∧ D.NetYieldN n₂ tn₂ as₂ := by
  classical
  constructor
  · rintro ⟨sol, hsteps, hprim, l, hlin, has⟩
    obtain ⟨n₁, n₂, a, b, rfl, ha, hb, hser⟩ := h.stepsN_split hw₁ hw₂ hsteps
    obtain ⟨hpa, hpb⟩ := hser.isPrimitive_iff.1 hprim
    obtain ⟨l₁, l₂, rfl, hlin₁, hlin₂⟩ := hser.exists_append_of_isLinearization hlin
    obtain ⟨as₁, as₂, rfl, has₁, has₂⟩ :=
      exists_append_actionSeq (fun t ht => hser.α₁ t ((hlin₁.2.1 t).1 ht))
        (fun t ht => hser.α₂ t ((hlin₂.2.1 t).1 ht)) has
    exact ⟨n₁, n₂, as₁, as₂, rfl, rfl, ⟨a, ha, hpa, l₁, hlin₁, has₁⟩, ⟨b, hb, hpb, l₂, hlin₂,
      has₂⟩⟩
  · rintro ⟨n₁, n₂, as₁, as₂, rfl, rfl, ⟨a, ha, hpa, l₁, hlin₁, has₁⟩,
      ⟨b, hb, hpb, l₂, hlin₂, has₂⟩⟩
    obtain ⟨a', ha', haiso⟩ := ha.iso_avoiding tn₁ hw₁ hw₁ (Iso.refl _) tn₂.T
    obtain ⟨tnA, hstepsA, hserA⟩ := h.stepsN_lift_left hw₂ ha'
    have ha'wf : a'.WF := ha'.stepsN.wf hw₁
    obtain ⟨b', hb', hbiso⟩ := hb.iso_avoiding tn₂ hw₂ hw₂ (Iso.refl _) a'.T
    obtain ⟨tnB, hstepsB, hserB⟩ := hserA.stepsN_lift_right ha'wf hb'
    have hb'wf : b'.WF := hb'.stepsN.wf hw₂
    obtain ⟨l₁', hlin₁', has₁'⟩ := (haiso.exists_linearization_actionSeq_iff as₁).1
      ⟨l₁, hlin₁, has₁⟩
    obtain ⟨l₂', hlin₂', has₂'⟩ := (hbiso.exists_linearization_actionSeq_iff as₂).1
      ⟨l₂, hlin₂, has₂⟩
    refine ⟨tnB, hstepsA.trans hstepsB, hserB.isPrimitive_iff.2
      ⟨TaskNetwork.Iso.isPrimitive haiso hpa, TaskNetwork.Iso.isPrimitive hbiso hpb⟩,
      l₁' ++ l₂', hserB.isLinearization_append ha'wf hb'wf hlin₁' hlin₂', ?_⟩
    exact append_actionSeq (fun t ht => hserB.α₁ t ((hlin₁'.2.1 t).1 ht))
      (fun t ht => hserB.α₂ t ((hlin₂'.2.1 t).1 ht)) has₁' has₂'

/-! ### Refinements of a network with a single task -/

/-- Decomposing the only task of a one-task network leaves exactly the inserted copy. -/
lemma _root_.HTN.TaskNetwork.IsSingle.decomposeWith_iso {tn u : TaskNetwork I A C} {t : I}
    (h : IsSingle tn t) (hdisj : Disjoint tn.T u.T) : (decomposeWith tn t u).Iso u := by
  classical
  have herase : tn.T.erase t = ∅ := by
    ext x
    simp only [Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
    intro hxt hx
    exact hxt ((h.memT x).1 hx)
  have hT : (decomposeWith tn t u).T = u.T := by
    simp [decomposeWith_T, herase]
  refine ⟨id, ?_, ?_, ?_⟩
  · rw [hT]; exact Set.bijOn_id _
  · intro x hx y hy
    rw [hT] at hx hy
    simpa using decomposeWith_ord_new_new (t := t) h.wf hdisj hx hy
  · intro x hx
    rw [hT] at hx
    simp [decomposeWith_α, hx]

/-- **A one-task network labelled by an action is refined only by that action**, in no steps. -/
theorem netYieldN_single_prim {n : ℕ} {tn : TaskNetwork I A C} {t : I} {a : A} {as : List A}
    (h : IsSingle tn t) (hα : tn.α t = Sum.inl a) :
    D.NetYieldN n tn as ↔ n = 0 ∧ as = [a] := by
  constructor
  · rintro ⟨sol, hsteps, hprim, l, hlin, has⟩
    have hn : n = 0 := by
      by_contra hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨tn₂, ⟨t', m, -, ht', hα', -⟩, -⟩ := hsteps.exists_head
      have : t' = t := (h.memT t').1 ht'
      subst this
      rw [hα] at hα'
      exact Sum.inl_ne_inr hα'
    subst hn
    cases hsteps with
    | refl =>
        rw [h.isLinearization_iff] at hlin
        subst hlin
        have : [tn.α t] = as.map Sum.inl := has
        rw [hα] at this
        cases as with
        | nil => simp at this
        | cons b bs =>
            simp only [List.map_cons, List.cons.injEq] at this
            obtain ⟨hb, hbs⟩ := this
            have hba : a = b := Sum.inl_injective hb
            have hbs' : bs = [] := by simpa using hbs.symm
            simp [hba, hbs']
  · rintro ⟨rfl, rfl⟩
    refine ⟨tn, StepsN.refl _, ?_, [t], h.isLinearization_iff.2 rfl, ?_⟩
    · intro x hx
      rw [(h.memT x).1 hx]
      exact ⟨a, hα⟩
    · show [tn.α t] = [Sum.inl a]
      rw [hα]

/-- **A one-task network labelled by a compound task is refined by the refinements of the
subtask networks of its methods**, one step being spent on the method application. -/
theorem netYieldN_single_comp [Infinite I] {n : ℕ} {tn : TaskNetwork I A C} {t : I} {c : C}
    {as : List A} (h : IsSingle tn t) (hα : tn.α t = Sum.inr c)
    (hmwf : ∀ m ∈ D.methods, m.subtasks.WF) :
    D.NetYieldN n tn as ↔ ∃ (k : ℕ) (m : Method I A C), n = k + 1 ∧ m ∈ D.methods ∧
      m.abstractTask = c ∧ D.NetYieldN k m.subtasks as := by
  classical
  constructor
  · rintro ⟨sol, hsteps, hprim, l, hlin, has⟩
    have hn : n ≠ 0 := by
      rintro rfl
      cases hsteps with
      | refl =>
          obtain ⟨b, hb⟩ := hprim t h.mem
          rw [hα] at hb
          exact Sum.inr_ne_inl hb
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨tn₂, ⟨t', m, hm, ht', hα', u, hu, huiso, hdisj, rfl⟩, hrest⟩ := hsteps.exists_head
    have htt : t' = t := (h.memT t').1 ht'
    subst htt
    rw [hα] at hα'
    have hmc : m.abstractTask = c := (Sum.inr_injective hα').symm
    refine ⟨k, m, rfl, hm, hmc, ?_⟩
    have hiso : (decomposeWith tn t' u).Iso m.subtasks :=
      (h.decomposeWith_iso hdisj).trans huiso
    have hwf₂ : (decomposeWith tn t' u).WF := decomposeWith_wf h.wf hu hdisj
    exact Domain.NetYieldN.iso ⟨sol, hrest, hprim, l, hlin, has⟩ hwf₂ (hmwf m hm) hiso
  · rintro ⟨k, m, rfl, hm, rfl, hy⟩
    obtain ⟨u, hu, huiso, hdisj⟩ :=
      TaskNetwork.exists_fresh_iso_copy m.subtasks (hmwf m hm) tn.T
    have hdisj' : Disjoint tn.T u.T := hdisj
    have hstep : DecompStep' D.methods tn (decomposeWith tn t u) :=
      ⟨t, m, hm, h.mem, hα, u, hu, huiso, hdisj', rfl⟩
    have hiso : (decomposeWith tn t u).Iso m.subtasks :=
      (h.decomposeWith_iso hdisj').trans huiso
    have hwf₂ : (decomposeWith tn t u).WF := decomposeWith_wf h.wf hu hdisj'
    obtain ⟨sol, hsteps, hprim, l, hlin, has⟩ :=
      Domain.NetYieldN.iso hy (hmwf m hm) hwf₂ hiso.symm
    exact ⟨sol, StepsN.head hstep hsteps, hprim, l, hlin, has⟩

end Domain

end HTN
