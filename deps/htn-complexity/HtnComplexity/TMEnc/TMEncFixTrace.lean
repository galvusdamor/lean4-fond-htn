import HtnComplexity.TMEnc.TMEncFixSim
import HtnComplexity.TMEnc.TMEncTrace
/-!
# The machine states along a plan of the repaired encoding

The state-level half of the simulation argument — a solution plan of the encoded problem
witnesses a run of the machine from its initial state to an accepting one — holds for the
repaired construction of `HtnComplexity/TMEnc/TMEncFix.lean` exactly as it does for the printed
one: the repaired body of `checkers¹` contains no primitive action at all, so it neither adds an
illegal action nor an accepting test.

* `HTN.TMEnc.legal_of_mem_netYieldFix` — every action of every plan is legal;
* `HTN.TMEnc.countP_acceptCheck_eq_oneFix` — every plan performs exactly one accepting test;
* `HTN.TMEnc.exists_accepting_run_of_isSolutionPlanFix` — a solution plan of the repaired
  problem witnesses an accepting run of the machine.

For the printed construction the last statement is vacuous, because that problem has no solution
plan at all (`HTN.TMEnc.not_solvable`); for the repaired one it is not refuted by any of the
counting arguments of this development.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Legal actions -/

lemma legalAct_of_mem_bodiesFix {t : TMTask Q Γ}
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodiesFix N w K t)
    {a : TMAct Q Γ} (ha : Sum.inl a ∈ ls.flatten) : LegalAct N a := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix] at ha
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact legalAct_of_mem_bodies hls ha

/-- **Every action of every plan of the repaired problem is legal.** -/
theorem legal_of_mem_netYieldFix {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) : ∀ a ∈ as, LegalAct N a := by
  refine forall_mem_of_netYield (P := LegalAct N) ?_ ?_ h
  · rintro ⟨c, tn⟩ hm t ht a hα
    rcases hm with ⟨ls, hls, hsub⟩ | hm
    · simp only at hls hsub
      subst hsub
      have hmem := TaskNetwork.grid_α_mem_flatten (ls := ls) ht
      rw [show (TaskNetwork.grid ls).α t = Sum.inl a from hα] at hmem
      exact legalAct_of_mem_bodiesFix hls hmem
    · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have hmem := TaskNetwork.gridTail_α_mem_flatten (ls := initChainsFix K)
        (tl := [Sum.inr (TMTask.done : TMTask Q Γ)]) ht
      rw [show (TaskNetwork.gridTail (initChainsFix K)
        [Sum.inr (TMTask.done : TMTask Q Γ)]).α t = Sum.inl a from hα] at hmem
      simp [initChainsFix, headChainFix] at hmem
  · intro t ht a hα
    have hmem := TaskNetwork.grid_α_mem_flatten (ls := [[Sum.inr (TMTask.sI : TMTask Q Γ)]])
      (show t ∈ (TaskNetwork.grid [[Sum.inr (TMTask.sI : TMTask Q Γ)]]).T from ht)
    rw [show (TaskNetwork.grid [[Sum.inr (TMTask.sI : TMTask Q Γ)]]).α t = Sum.inl a from hα]
      at hmem
    simp at hmem

/-! ### The accepting test -/

open scoped Classical in
lemma sum_wDone_bodiesFix {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wDone N)).sum = wDone N (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix, wDone, doneCount]
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact sum_wDone_bodies hls

open scoped Classical in
lemma balanced_wDoneFix : Balanced (methodsFix N w K) (wDone N) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wDone_bodiesFix hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    simp [initChainsFix, headChainFix, wDone, doneCount]

open scoped Classical in
/-- **Every plan of the repaired problem performs exactly one accepting test.** -/
theorem countP_acceptCheck_eq_oneFix {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isAcceptCheck N) = 1 := by
  have hw := weight_of_netYield (balanced_wDoneFix (N := N) (w := w) (K := K)) h
  rw [sum_map_wDone, weight_tnIFix] at hw
  simp only [wDone, doneCount, Nat.cast_one] at hw
  exact_mod_cast hw

/-! ### The machine accepts -/

lemma stateIs_initFix : StateIs N.init ((problemFix N w K).init : Set (TMFact Q Γ)) := by
  intro p
  show (TMFact.st p : TMFact Q Γ) ∈ ({TMFact.st N.init} : Set (TMFact Q Γ)) ↔ p = N.init
  simp

open scoped Classical in
/-- **The soundness of the repaired encoding at the level of the machine states.**  If the
repaired problem has a solution plan, then the machine `N` can go from its initial state to an
accepting state, each step being a transition of `N`. -/
theorem exists_accepting_run_of_isSolutionPlanFix {as : List (TMAct Q Γ)}
    (h : (problemFix N w K).IsSolutionPlan as) :
    ∃ f ∈ N.accept, Relation.ReflTransGen (StateStep N) N.init f := by
  obtain ⟨hy, happ, -⟩ := Problem.isSolutionPlan_iff.1 h
  have hlegal := legal_of_mem_netYieldFix hy
  have hcount := countP_acceptCheck_eq_oneFix hy
  have hex : ∃ a ∈ as, isAcceptCheck N a = true := by
    by_contra hcon
    push_neg at hcon
    have : as.countP (isAcceptCheck N) = 0 :=
      List.countP_eq_zero.2 fun a ha => by simpa using hcon a ha
    omega
  obtain ⟨a, hmem, hacc⟩ := hex
  obtain ⟨pre, post, rfl⟩ : ∃ pre post, as = pre ++ a :: post := by
    obtain ⟨pre, post, h⟩ := List.append_of_mem hmem
    exact ⟨pre, post, h⟩
  rw [ActionModel.seqApplicable_append] at happ
  obtain ⟨happre, happost⟩ := happ
  obtain ⟨ha, -⟩ := happost
  obtain ⟨q, hq, hreach⟩ :=
    exists_stateIs_of_seqApplicable (N := N) pre ((problemFix N w K).init) N.init
      (fun b hb => hlegal b (by simp [hb])) happre stateIs_initFix
  match a, hacc with
  | .check (.st f), hacc =>
      have hf : f ∈ N.accept := by simpa [isAcceptCheck] using hacc
      have hst : (TMFact.st f : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).transitionSeq pre ((problemFix N w K).init) :=
        ha (show (TMFact.st f : TMFact Q Γ) ∈ ({TMFact.st f} : Set (TMFact Q Γ)) from rfl)
      have hfq : f = q := (hq f).1 hst
      subst hfq
      exact ⟨f, hf, hreach⟩

end TMEnc

end HTN
