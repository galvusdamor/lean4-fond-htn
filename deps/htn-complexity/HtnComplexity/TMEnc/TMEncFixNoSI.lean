import HtnComplexity.TMEnc.TMEncFixInitGrid
/-!
# The fresh initial task is used exactly once

The repaired domain `HTN.TMEnc.domainFix` has one method more than the domain of the grid
bodies `HTN.TMEnc.domainBod`: the single method of the fresh initial task `sI`, whose subtask
network `HTN.TMEnc.initNetFix` is *not* a grid (it is a grid followed by the task `done`).  All the
syntactic analysis of refinements — `HTN.Domain.netYield_grid_iff`,
`HTN.Domain.netYield_gridTail_iff`, `HTN.TMEnc.chainYield_singleton_bod_iff` — is available for
`domainBod` only, so the *analysis* direction of the simulation argument needs to know that,
below the initial task network, the extra method is never applicable again.

That is what this file proves:

* `HTN.TMEnc.NoSI` — a compound task that does not mention `sI` (note that `sI` could hide
  inside a counting task `C^k_t`, so this is a recursive predicate, not just `c ≠ sI`);
* `HTN.TMEnc.noSI_of_mem_bodiesFix` — no body of a task without `sI` mentions `sI`;
* `HTN.TMEnc.netYield_bod_of_fix` — **a refinement of a network without `sI` in the repaired
  domain is a refinement in the domain of the grid bodies**;
* `HTN.TMEnc.netYield_tnIFix_iff` — **the refinements of the initial task network are exactly
  the refinements of the three chains of `HTN.TMEnc.initChainsFix` followed by one of `done`**.
  This is the analysis counterpart of `HTN.TMEnc.netYield_tnIFix_of_gridYield`, i.e. the first
  step of the soundness half of the simulation argument.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Tasks that do not mention the fresh initial task -/

/-- A compound task that does not mention the fresh initial task `sI`, not even inside a
counting task. -/
def NoSI : TMTask Q Γ → Prop
  | .cSeq t _ => NoSI t
  | .cPar t _ => NoSI t
  | .sI => False
  | _ => True

@[simp] lemma noSI_sI : ¬ NoSI (TMTask.sI : TMTask Q Γ) := id

/-- Reduce a membership in a body of `HTN.TMEnc.bodies` and the resulting membership in its
flattening to the finitely many possibilities, and close the goal `NoSI c`. -/
local macro "nosi_tac" h:ident hy:ident : tactic =>
  `(tactic| (try simp only [bodies, Set.mem_singleton_iff, Set.mem_insert_iff,
        Set.mem_setOf_eq] at $h:ident) <;>
      (try casesm* _ ∧ _, _ ∨ _, Exists _) <;> subst_vars <;>
      (try simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.mem_append, List.not_mem_nil, List.mem_replicate,
        or_false, false_or, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at $hy:ident) <;>
      (try casesm* _ ∧ _, _ ∨ _) <;> subst_vars <;> first | trivial | assumption)

/-- No body of a task without `sI` mentions `sI`. -/
lemma noSI_of_mem_bodies {t : TMTask Q Γ} (ht : NoSI t)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodies N w K t)
    {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) : NoSI c := by
  cases t with
  | acquire x => nosi_tac hls hc
  | release x => nosi_tac hls hc
  | produce => nosi_tac hls hc
  | produceSym d => nosi_tac hls hc
  | tapeProduce => nosi_tac hls hc
  | waitCell => nosi_tac hls hc
  | waitN i => nosi_tac hls hc
  | chk => nosi_tac hls hc
  | headCell => nosi_tac hls hc
  | noHeadCell => nosi_tac hls hc
  | heads => nosi_tac hls hc
  | transition => nosi_tac hls hc
  | transitionAndCheck => nosi_tac hls hc
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> nosi_tac hls hc
  | produceInit => nosi_tac hls hc
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> nosi_tac hls hc
  | done => nosi_tac hls hc
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls <;> nosi_tac hls hc
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls <;> nosi_tac hls hc
  | sI => simp [bodies] at hls

/-- **No body of the repaired construction mentions `sI`.** -/
lemma noSI_of_mem_bodiesFix {t : TMTask Q Γ} (ht : NoSI t)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodiesFix N w K t)
    {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) : NoSI c := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp only [checkerBodyFix, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
    rcases hc with rfl | rfl | rfl <;> trivial
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact noSI_of_mem_bodies ht hls hc

/-! ### Networks that do not mention the fresh initial task -/

/-- All compound tasks of the network avoid `sI`. -/
def NetNoSI (tn : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)) : Prop :=
  ∀ t ∈ tn.T, ∀ c : TMTask Q Γ, tn.α t = Sum.inr c → NoSI c

lemma netNoSI_grid {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (h : ∀ c : TMTask Q Γ, Sum.inr c ∈ ls.flatten → NoSI c) : NetNoSI (TaskNetwork.grid ls) := by
  intro t ht c hc
  have hmem := TaskNetwork.grid_α_mem_flatten (ls := ls) ht
  rw [hc] at hmem
  exact h c hmem

/-- **The initial task network of the repaired construction mentions no `sI`.** -/
lemma netNoSI_initNetFix : NetNoSI (initNetFix (Q := Q) (Γ := Γ) K) := by
  intro t ht c hc
  have hmem := TaskNetwork.gridTail_α_mem_flatten (ls := initChainsFix (Q := Q) (Γ := Γ) K)
    (tl := [Sum.inr (TMTask.done : TMTask Q Γ)]) ht
  rw [show (TaskNetwork.gridTail (initChainsFix (Q := Q) (Γ := Γ) K)
    [Sum.inr (TMTask.done : TMTask Q Γ)]).α t = Sum.inr c from hc] at hmem
  simp only [initChainsFix, headChainFix, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    Sum.inr.injEq] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

/-- A decomposition step of the repaired domain applied to a network without `sI` uses a method
of the domain of the grid bodies, and its result has no `sI` either. -/
lemma decompStep_bod_of_fix {tn₁ tn₂ : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    {t : ℕ × ℕ} {m : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    (h : DecompStep (domainFix N w K).methods tn₁ t m tn₂) (hn : NetNoSI tn₁) :
    DecompStep (domainBod N w K).methods tn₁ t m tn₂ ∧ NetNoSI tn₂ := by
  obtain ⟨hm, htT, hαt, tn', hwf', ⟨σ, hbij, hord, hα⟩, hdisj, rfl⟩ := h
  have hnoSI : NoSI m.abstractTask := hn t htT _ hαt
  have hmbod : m ∈ (domainBod N w K).methods := by
    rcases hm with hm | hm
    · exact hm
    · simp only [Set.mem_singleton_iff] at hm
      subst hm
      exact absurd hnoSI (by simp)
  obtain ⟨ls, hls, hsub⟩ := id hmbod
  refine ⟨⟨hmbod, htT, hαt, tn', hwf', ⟨σ, hbij, hord, hα⟩, hdisj, rfl⟩, ?_⟩
  intro x hx c hc
  by_cases hx' : x ∈ tn'.T
  · have hxσ : σ x ∈ m.subtasks.T := by simpa using hbij.mapsTo (by simpa using hx')
    have hασ : m.subtasks.α (σ x) = Sum.inr c := by
      rw [← hα x hx']
      simpa [hx'] using hc
    rw [hsub] at hxσ hασ
    have hmem := TaskNetwork.grid_α_mem_flatten (ls := ls) hxσ
    rw [hασ] at hmem
    exact noSI_of_mem_bodiesFix hnoSI hls hmem
  · have hx₁ : x ∈ tn₁.T := by
      rcases mem_decomposeWith_T.1 hx with ⟨h, -⟩ | h
      · exact h
      · exact absurd h hx'
    exact hn x hx₁ c (by simpa [hx'] using hc)

/-- **A derivation of the repaired domain that starts at a network without `sI` is a derivation
of the domain of the grid bodies.** -/
lemma stepsN_bod_of_fix {n : ℕ} {tn tn' : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    (h : StepsN (domainFix N w K).methods n tn tn') (hn : NetNoSI tn) :
    StepsN (domainBod N w K).methods n tn tn' ∧ NetNoSI tn' := by
  induction h with
  | refl tn => exact ⟨StepsN.refl tn, hn⟩
  | tail hsteps hstep ih =>
      obtain ⟨hbod, hno⟩ := ih hn
      obtain ⟨t, m, hs⟩ := hstep
      obtain ⟨hs', hno'⟩ := decompStep_bod_of_fix hs hno
      exact ⟨StepsN.tail hbod ⟨t, m, hs'⟩, hno'⟩

/-- **Every refinement of a network without `sI` in the repaired domain is one of the domain of
the grid bodies.** -/
theorem netYield_bod_of_fix {tn : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    {as : List (TMAct Q Γ)} (hn : NetNoSI tn) (h : (domainFix N w K).NetYield tn as) :
    (domainBod N w K).NetYield tn as := by
  obtain ⟨n, sol, hsteps, hprim, l, hlin, has⟩ := h
  exact ⟨n, sol, (stepsN_bod_of_fix hsteps hn).1, hprim, l, hlin, has⟩

/-! ### The refinements of the initial task network -/

/-- **The refinements of the initial task network of the repaired problem are exactly the
refinements of the three chains of `HTN.TMEnc.initChainsFix`, followed by a refinement of the task
`done`.**

The direction from right to left is `HTN.TMEnc.netYield_tnIFix_of_gridYield`; the direction from
left to right is the first step of the analysis of a solution plan. -/
theorem netYield_tnIFix_iff {as : List (TMAct Q Γ)} :
    (domainFix N w K).NetYield (instance_ N).tnI as ↔
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧
        (domainBod N w K).GridYield (initChainsFix (Q := Q) (Γ := Γ) K) as₁ ∧
        (domainBod N w K).ChainYield [Sum.inr TMTask.done] as₂ := by
  constructor
  · rintro ⟨n, hn⟩
    have hsingle : TaskNetwork.IsSingle (instance_ N).tnI (0, 0) :=
      TaskNetwork.isSingle_seq_singleton _
    have hα : (instance_ N).tnI.α (0, 0) = Sum.inr (TMTask.sI : TMTask Q Γ) :=
      TaskNetwork.seq_singleton_α _
    obtain ⟨k, m, rfl, hm, hmc, hy⟩ :=
      (netYieldN_single_comp (D := domainFix N w K) hsingle hα methodsFix_wf).1 hn
    have hmeq : m = ⟨TMTask.sI, initNetFix (Q := Q) (Γ := Γ) K⟩ := by
      rcases hm with ⟨ls, hls, hsub⟩ | hm
      · rw [hmc] at hls
        simp [bodiesFix, bodies] at hls
      · simpa [Set.mem_singleton_iff] using hm
    subst hmeq
    have hbod : (domainBod N w K).NetYield (initNetFix (Q := Q) (Γ := Γ) K) as :=
      netYield_bod_of_fix netNoSI_initNetFix ⟨k, hy⟩
    exact (netYield_gridTail_iff methods_grid_bod).1 hbod
  · rintro ⟨as₁, as₂, rfl, h₁, h₂⟩
    exact netYield_tnIFix_of_gridYield h₁ h₂

/-- **The solution plans of the repaired problem**: an executable refinement of the three chains
followed by one of `done`.  This is the entry point of the analysis of a solution plan. -/
theorem isSolutionPlanFix_iff {as : List (TMAct Q Γ)} :
    (problemFix N w K).IsSolutionPlan as ↔
      (∃ as₁ as₂, as = as₁ ++ as₂ ∧
        (domainBod N w K).GridYield (initChainsFix (Q := Q) (Γ := Γ) K) as₁ ∧
        (domainBod N w K).ChainYield [Sum.inr TMTask.done] as₂) ∧
      (problemFix N w K).SeqApplicable as (problemFix N w K).init := by
  rw [Problem.isSolutionPlan_iff]
  constructor
  · rintro ⟨hy, happ, -⟩
    exact ⟨netYield_tnIFix_iff.1 hy, happ⟩
  · rintro ⟨hy, happ⟩
    refine ⟨netYield_tnIFix_iff.2 hy, happ, ?_⟩
    simp [Problem.GoalState, problemFix, Domain.mkProblem, instance_]

/-- **The three chains of the initial task network, split apart.**  A refinement of the initial
grid is an interleaving of a refinement of the head-counter chain, one of the chain of the cell
counters and one of the tape chain. -/
theorem gridYield_initChains_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).GridYield (initChainsFix (Q := Q) (Γ := Γ) K) as ↔
      ∃ ah ac at' bs,
        (domainBod N w K).ChainYield (headChainFix (Q := Q) (Γ := Γ) K) ah ∧
        (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers (K + 1))] ac ∧
        (domainBod N w K).ChainYield
          [Sum.inr TMTask.produceInit, Sum.inr (TMTask.cSeq TMTask.tapeProduce K)] at' ∧
        Interleave ac at' bs ∧ Interleave ah bs as := by
  unfold initChainsFix
  rw [gridYield_cons_iff]
  constructor
  · rintro ⟨ah, bs, hh, hrest, hint⟩
    rw [gridYield_cons_iff] at hrest
    obtain ⟨ac, at', hc, hrest', hint'⟩ := hrest
    rw [gridYield_singleton_iff] at hrest'
    exact ⟨ah, ac, at', bs, hh, hc, hrest', hint', hint⟩
  · rintro ⟨ah, ac, at', bs, hh, hc, ht, hint', hint⟩
    exact ⟨ah, bs, hh, (gridYield_cons_iff).2 ⟨ac, at', hc, gridYield_singleton_iff.2 ht, hint'⟩,
      hint⟩

end TMEnc

end HTN
