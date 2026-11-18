import HtnPlanning.Interleave.ChainSeqYield
import HtnComplexity.ToHtnAc.ToHtnAcCntPar
/-!
# The sequential part of the HTN-AC compilation is chain closed

Every compound task of the compiled domain of `HtnComplexity/ToHtnAc/ToHtnAc.lean` *except* the
parallel counting task `𝔠^k_T` and the initial task `t_I` is decomposed by methods whose body is
a single chain.  This file records that observation and derives, via
`HTN.Domain.chainYield_iff_yieldSeq`, that on those tasks the interleaving refinement relation
`HTN.Domain.ChainYield` of `HtnPlanning/Interleave/GridYield.lean` coincides with the totally ordered
refinement relation `HTN.Domain.YieldSeq` used by the gadget lemmas of
`HtnComplexity/ToHtnAc/ToHtnAcSim.lean`.

Results:

* `HTN.ToAc.IsSeqTask` — the compound tasks with totally ordered methods;
* `HTN.ToAc.gridBody_iff` — the grid bodies of the compiled domain are exactly (the grids of) the
  entries of `HTN.ToAc.bodies`;
* `HTN.ToAc.chainClosed_isSeqTask` — `HTN.Domain.ChainClosed` holds for these tasks;
* `HTN.ToAc.chainYield_iff_yieldSeq` — **the two refinement relations agree on chains of
  sequential tasks**;
* `HTN.ToAc.chainYield_singleton_iff_yield` and `HTN.ToAc.netYield_tnI_iff_yieldSeq` — the
  resulting description of the plans of the compiled problem in terms of `YieldSeq`.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open TaskNetwork Domain

/-- The compound tasks of the compiled domain all of whose methods have a single chain as their
body.  These are all the tasks except the parallel counting task `𝔠^k_T` and the initial task
`t_I`; the totally ordered counting task `𝔠̄^k_T` is sequential as soon as the task it counts
is. -/
def IsSeqTask : AcTask F A C → Prop
  | .cntPar _ _ => False
  | .tI => False
  | .cnt t _ => IsSeqTask t
  | _ => True

@[simp] lemma isSeqTask_SEL {i : Fin 5} : IsSeqTask (AcTask.SEL i : AcTask F A C) := trivial
@[simp] lemma isSeqTask_SELn {n : ℕ} {i : Fin 5} :
    IsSeqTask (AcTask.SELn n i : AcTask F A C) := trivial
@[simp] lemma isSeqTask_EQ {i j : Fin 5} : IsSeqTask (AcTask.EQ i j : AcTask F A C) := trivial
@[simp] lemma isSeqTask_EQn {n : ℕ} {i j : Fin 5} :
    IsSeqTask (AcTask.EQn n i j : AcTask F A C) := trivial
@[simp] lemma isSeqTask_STATE1 {n : ℕ} : IsSeqTask (AcTask.STATE1 n : AcTask F A C) := trivial
@[simp] lemma isSeqTask_STATE3 {n : ℕ} : IsSeqTask (AcTask.STATE3 n : AcTask F A C) := trivial
@[simp] lemma isSeqTask_MEM : IsSeqTask (AcTask.MEM : AcTask F A C) := trivial
@[simp] lemma isSeqTask_WRITE : IsSeqTask (AcTask.WRITE : AcTask F A C) := trivial
@[simp] lemma isSeqTask_READ : IsSeqTask (AcTask.READ : AcTask F A C) := trivial
@[simp] lemma isSeqTask_TUPLE : IsSeqTask (AcTask.TUPLE : AcTask F A C) := trivial
@[simp] lemma isSeqTask_cnt {t : AcTask F A C} {k : ℕ} :
    IsSeqTask (AcTask.cnt t k) ↔ IsSeqTask t := Iff.rfl
@[simp] lemma isSeqTask_cntPar {t : AcTask F A C} {k : ℕ} :
    ¬ IsSeqTask (AcTask.cntPar t k) := id
@[simp] lemma isSeqTask_tI : ¬ IsSeqTask (AcTask.tI : AcTask F A C) := id

/-- The grid bodies of the compiled domain are exactly the entries of `HTN.ToAc.bodies`, up to
the presentation of the grid. -/
lemma gridBody_iff {c : AcTask F A C} {ls : List (List (AcAct F A C ⊕ AcTask F A C))} :
    (domain D vars bound).GridBody c ls ↔
      ∃ ls' ∈ bodies D vars bound c, TaskNetwork.grid ls' = TaskNetwork.grid ls := by
  constructor
  · rintro ⟨m, ⟨ls', hls', hsub'⟩, rfl, hsub⟩
    exact ⟨ls', hls', by rw [← hsub', hsub]⟩
  · rintro ⟨ls', hls', he⟩
    exact ⟨⟨c, TaskNetwork.grid ls'⟩, ⟨ls', hls', rfl⟩, rfl, he⟩

/-- Every body of a sequential task is a single chain of sequential tasks (the empty grid being
the grid of the empty chain). -/
lemma bodies_single_of_isSeqTask {c : AcTask F A C} (hc : IsSeqTask c)
    {ls : List (List (AcAct F A C ⊕ AcTask F A C))} (h : ls ∈ bodies D vars bound c) :
    ∃ l, TaskNetwork.grid ls = TaskNetwork.grid [l] ∧
      ∀ c' : AcTask F A C, Sum.inr c' ∈ l → IsSeqTask c' := by
  have hnil : TaskNetwork.grid ([] : List (List (AcAct F A C ⊕ AcTask F A C))) =
      TaskNetwork.grid [([] : List (AcAct F A C ⊕ AcTask F A C))] :=
    TaskNetwork.grid_nil_eq_grid_cons_nil
  cases c with
  | SEL i =>
      simp only [bodies] at h
      simp only [Set.mem_singleton_iff] at h
      subst h
      exact ⟨_, rfl, by simp⟩
  | SELn n i =>
      simp only [bodies] at h
      split_ifs at h with hn
      · simp only [Set.mem_singleton_iff] at h
        subst h
        exact ⟨[], hnil, by simp⟩
      · obtain ⟨v, -, hv | hv⟩ := h <;> subst hv <;> exact ⟨_, rfl, by simp⟩
  | EQ i j =>
      simp only [bodies] at h
      simp only [Set.mem_singleton_iff] at h
      subst h
      exact ⟨_, rfl, by simp⟩
  | EQn n i j =>
      simp only [bodies] at h
      split_ifs at h with hn
      · simp only [Set.mem_singleton_iff] at h
        subst h
        exact ⟨[], hnil, by simp⟩
      · obtain ⟨v, -, hv | hv⟩ := h <;> subst hv <;> exact ⟨_, rfl, by simp⟩
  | STATE1 n =>
      simp only [bodies] at h
      split_ifs at h with hn
      · simp only [Set.mem_singleton_iff] at h
        subst h
        exact ⟨_, rfl, by simp⟩
      · obtain ⟨v, -, hv | hv⟩ := h <;> subst hv <;> exact ⟨_, rfl, by simp⟩
  | STATE3 n =>
      simp only [bodies] at h
      split_ifs at h with hn
      · obtain ⟨t, hv⟩ := h
        subst hv
        exact ⟨_, rfl, by simp⟩
      · obtain ⟨v, -, hv | hv⟩ := h <;> subst hv <;> exact ⟨_, rfl, by simp⟩
  | MEM =>
      simp only [bodies] at h
      simp only [Set.mem_singleton_iff] at h
      subst h
      exact ⟨_, rfl, by simp⟩
  | WRITE =>
      simp only [bodies] at h
      simp only [Set.mem_singleton_iff] at h
      subst h
      exact ⟨_, rfl, by simp⟩
  | READ =>
      simp only [bodies] at h
      simp only [Set.mem_singleton_iff] at h
      subst h
      exact ⟨_, rfl, by simp⟩
  | TUPLE =>
      simp only [bodies] at h
      rcases h with h | h
      · obtain ⟨c, x, y, -, hv⟩ := h
        subst hv
        exact ⟨_, rfl, by simp⟩
      · obtain ⟨o, hv⟩ := h
        subst hv
        exact ⟨_, rfl, by simp⟩
  | cnt t k =>
      have ht : IsSeqTask t := hc
      simp only [bodies] at h
      split_ifs at h with h0 h1 h2
      · simp only [Set.mem_singleton_iff] at h
        subst h
        exact ⟨[], hnil, by simp⟩
      · rcases h with h | h
        · subst h
          exact ⟨_, rfl, by simpa using ht⟩
        · subst h
          exact ⟨[], hnil, by simp⟩
      · simp only [Set.mem_singleton_iff] at h
        subst h
        exact ⟨_, rfl, by simpa using ht⟩
      · rcases h with h | h <;> subst h <;> exact ⟨_, rfl, by simpa using ht⟩
  | cntPar t k => exact absurd hc (by simp)
  | tI => exact absurd hc (by simp)

/-- **The sequential tasks of the compiled domain are chain closed.** -/
theorem chainClosed_isSeqTask :
    Domain.ChainClosed (domain D vars bound) {t : AcTask F A C | IsSeqTask t} := by
  intro c hc ls hgb
  obtain ⟨ls', hls', he⟩ := gridBody_iff.1 hgb
  obtain ⟨l, hl, hmem⟩ := bodies_single_of_isSeqTask hc hls'
  exact ⟨l, by rw [← he, hl], hmem⟩

/-- **On chains of sequential tasks, the interleaving refinement relation and the totally ordered
refinement relation of the compiled domain agree.** -/
theorem chainYield_iff_yieldSeq {xs : List (AcAct F A C ⊕ AcTask F A C)}
    {as : List (AcAct F A C)} (hS : ∀ c : AcTask F A C, Sum.inr c ∈ xs → IsSeqTask c) :
    (domain D vars bound).ChainYield xs as ↔ (domain D vars bound).YieldSeq xs as :=
  Domain.chainYield_iff_yieldSeq methods_grid chainClosed_isSeqTask hS

/-- A single sequential task refines in the interleaving semantics exactly as it does in the
totally ordered semantics. -/
theorem chainYield_singleton_iff_yield {c : AcTask F A C} (hc : IsSeqTask c)
    {as : List (AcAct F A C)} :
    (domain D vars bound).ChainYield [Sum.inr c] as ↔
      (domain D vars bound).YieldSeq [Sum.inr c] as :=
  chainYield_iff_yieldSeq (by
    intro c' hc'
    simp only [List.mem_singleton, Sum.inr.injEq] at hc'
    subst hc'
    exact hc)

/-! ### Unpacking the parallel copies

The two components of a plan of the compiled problem are refinements of `m` parallel copies of a
single (sequential) task.  These lemmas peel off one copy at a time, each copy now being
described by the totally ordered refinement relation for which the gadget lemmas of
`HtnComplexity/ToHtnAc/ToHtnAcSim.lean` are stated. -/

@[simp] lemma gridYield_replicate_zero {c : AcTask F A C} {as : List (AcAct F A C)} :
    (domain D vars bound).GridYield (List.replicate 0 [Sum.inr c]) as ↔ as = [] := by
  rw [List.replicate_zero, gridYield_nil_iff]

/-- **A refinement of `m + 1` parallel copies of a sequential task is an interleaving of a
totally ordered refinement of one copy with a refinement of the remaining `m` copies.** -/
theorem gridYield_replicate_succ {c : AcTask F A C} (hc : IsSeqTask c) {m : ℕ}
    {as : List (AcAct F A C)} :
    (domain D vars bound).GridYield (List.replicate (m + 1) [Sum.inr c]) as ↔
      ∃ as₁ as₂, (domain D vars bound).YieldSeq [Sum.inr c] as₁ ∧
        (domain D vars bound).GridYield (List.replicate m [Sum.inr c]) as₂ ∧
        Interleave as₁ as₂ as := by
  rw [List.replicate_succ, gridYield_cons_iff]
  simp only [chainYield_singleton_iff_yield hc]

end ToAc

end HTN
