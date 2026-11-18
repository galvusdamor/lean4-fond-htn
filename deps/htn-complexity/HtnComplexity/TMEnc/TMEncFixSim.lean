import HtnComplexity.TMEnc.TMEncFixCount
import HtnComplexity.TMEnc.TMEncHead
/-!
# The plan counters of the repaired encoding

The necessary conditions that `HtnComplexity/TMEnc/TMEncSim.lean` and
`HtnComplexity/TMEnc/TMEncHead.lean` prove for the printed construction hold for the repaired
construction of `HtnComplexity/TMEnc/TMEncFix.lean` as well.  All of them are weight arguments,
and the repaired body of `checkers¹` — `(release_check, C^K_{transitionAndCheck}, release_sync)`
— has, for each of these weights, exactly the weight the printed body has: it drops one `check`
task, which writes no symbol, places no head, gives no answer of the head counter and examines
no cell.

* `HTN.TMEnc.countP_assert_eq_sqFix` — every plan writes exactly `(K+1)²` tape symbols;
* `HTN.TMEnc.countP_assertHead_eqFix` — every plan places the head exactly `K + 1` times;
* `HTN.TMEnc.countP_examine_eqFix` — every plan performs exactly `K(K+1)` cell examinations;
* `HTN.TMEnc.countP_startHead_eqFix`, `HTN.TMEnc.countP_extra_acquireHeadFix` — the budget of
  the head counter;
* `HTN.TMEnc.symUnique_of_seqApplicableFix`, `HTN.TMEnc.headUnique_of_planFix` — at every point
  of a plan at most one tape symbol holds and the head flag is consistent (these depend on the
  action model and the initial state only, which the repair does not touch).
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The number of tape symbols -/

lemma sum_wAssert_bodiesFix {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wAssert w K)).sum = wAssert w K (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix, wAssert, assertCount]
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact sum_wAssert_bodies hls

lemma balanced_wAssertFix : Balanced (methodsFix N w K) (wAssert (Q := Q) w K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wAssert_bodiesFix hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    simp [initChainsFix, headChainFix, wAssert, assertCount]

/-- **Every plan of the repaired problem writes exactly
`1 + max |w| 1 + (K - |w|) + K(K+1)` tape symbols.** -/
theorem countP_assert_eqFix {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP isAssert = (1 + max w.length 1 + (K - w.length)) + K * (1 + K) := by
  have hw := weight_of_netYield (balanced_wAssertFix (N := N) (w := w) (K := K)) h
  rw [sum_map_wAssert, weight_tnIFix] at hw
  simp only [wAssert, assertCount] at hw
  exact_mod_cast hw

/-- **The witness of the repaired problem has `(K+1)²` cells.** -/
theorem countP_assert_eq_sqFix (hw0 : w ≠ []) (hwK : w.length ≤ K) {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP isAssert = (K + 1) ^ 2 := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw0
  rw [countP_assert_eqFix h]
  have hmax : max w.length 1 = w.length := by omega
  rw [hmax]
  ring_nf
  omega

/-! ### The head placements -/

lemma sum_wHead_bodiesFix {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wHead K)).sum = wHead K (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix, wHead, headCount]
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact sum_wHead_bodies hls

lemma balanced_wHeadFix : Balanced (methodsFix N w K) (wHead (Q := Q) (Γ := Γ) K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wHead_bodiesFix hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    simp [initChainsFix, headChainFix, wHead, headCount]
    ring

/-- **Every plan of the repaired problem places the head exactly `K + 1` times.** -/
theorem countP_assertHead_eqFix {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP isAssertHead = K + 1 := by
  have hw := weight_of_netYield (balanced_wHeadFix (N := N) (w := w) (K := K)) h
  rw [sum_map_wHead, weight_tnIFix] at hw
  simp only [wHead, headCount] at hw
  have hw' : as.countP isAssertHead = 1 + K := by exact_mod_cast hw
  omega

/-! ### The cell examinations -/

lemma sum_wExamine_bodiesFix {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wExamine K)).sum = wExamine K (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix, wExamine, examineCount]
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact sum_wExamine_bodies hls

lemma balanced_wExamineFix : Balanced (methodsFix N w K) (wExamine (Q := Q) (Γ := Γ) K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wExamine_bodiesFix hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    simp [initChainsFix, headChainFix, wExamine, examineCount]

/-- **Every plan of the repaired problem examines the cells exactly `K(K+1)` times.** -/
theorem countP_examine_eqFix {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP isStepOrNoHead = (K + 1) * K := by
  have hw := weight_of_netYield (balanced_wExamineFix (N := N) (w := w) (K := K)) h
  rw [sum_map_wExamine, weight_tnIFix] at hw
  simp only [wExamine, examineCount] at hw
  exact_mod_cast hw

/-! ### The budget of the head counter -/

/-- How many `start head` actions the full expansion of a compound task performs, for the
**repaired** construction.  It differs from `HTN.TMEnc.startHeadCount` only at the initial task
`sI`, whose repaired head chain `HTN.TMEnc.headChainFix` runs `K (K+2) + 2 + (K-1)` units — the
`K² + 3K + 1` of the printed one for `K ≥ 1`, but now one per request, none of them free. -/
def startHeadCountFix (K : ℕ) : TMTask Q Γ → ℕ
  | .release x => if x = SyncKind.head then 1 else 0
  | .headCell => 1
  | .noHeadCell => 1
  | .heads => K + 2
  | .cSeq t k => k * startHeadCountFix K t
  | .cPar t k => k * startHeadCountFix K t
  | .sI => K * (K + 2) + 2 + (K - 1)
  | _ => 0

/-- The weight counting the answers of the repaired head counter. -/
def wStartHeadFix (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isStart SyncKind.head a then 1 else 0
  | Sum.inr t => (startHeadCountFix K t : ℤ)

lemma sum_wStartHeadFix_bodiesPrinted {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map (wStartHeadFix K)).sum = wStartHeadFix K (Sum.inr t) := by
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix, isStart]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      cases y <;> simp [wStartHeadFix, startHeadCountFix, isStart]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wStartHeadFix, startHeadCountFix, isStart]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix, isStart]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix]
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wStartHeadFix, startHeadCountFix, isStart]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix, isStart]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix, isStart]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wStartHeadFix, startHeadCountFix, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_one]
      push_cast
      ring
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wStartHeadFix, startHeadCountFix, isStart, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wStartHeadFix, startHeadCountFix, isStart]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wStartHeadFix, startHeadCountFix]
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHeadFix, startHeadCountFix]
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wStartHeadFix, startHeadCountFix]
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wStartHeadFix, startHeadCountFix, isStart]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHeadFix, startHeadCountFix]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHeadFix, startHeadCountFix]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * startHeadCountFix K u + k / 2 * startHeadCountFix K u =
            k * startHeadCountFix K u := by
          have hrw : k / 2 * startHeadCountFix K u + k / 2 * startHeadCountFix K u =
              (2 * (k / 2)) * startHeadCountFix K u := by ring
          rw [hrw, hk2]
        simp only [wStartHeadFix, startHeadCountFix, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : startHeadCountFix K u + (k - 1) * startHeadCountFix K u = k * startHeadCountFix K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wStartHeadFix, startHeadCountFix, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHeadFix, startHeadCountFix]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHeadFix, startHeadCountFix]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * startHeadCountFix K u + k / 2 * startHeadCountFix K u =
            k * startHeadCountFix K u := by
          have hrw : k / 2 * startHeadCountFix K u + k / 2 * startHeadCountFix K u =
              (2 * (k / 2)) * startHeadCountFix K u := by ring
          rw [hrw, hk2]
        simp only [wStartHeadFix, startHeadCountFix, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : startHeadCountFix K u + (k - 1) * startHeadCountFix K u = k * startHeadCountFix K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wStartHeadFix, startHeadCountFix, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The head budget of the repaired construction.**  The body of `checkers¹` consists of
compound tasks only, so the count transfers from the printed development. -/
lemma sum_wStartHeadFix_bodiesFix {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wStartHeadFix K)).sum = wStartHeadFix K (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix, wStartHeadFix, startHeadCountFix]
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact sum_wStartHeadFix_bodiesPrinted hls

lemma balanced_wStartHeadFix :
    Balanced (methodsFix N w K) (wStartHeadFix (Q := Q) (Γ := Γ) K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wStartHeadFix_bodiesFix hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    simp [initChainsFix, headChainFix, wStartHeadFix, startHeadCountFix]
    ring

lemma sum_map_wStartHeadFix (as : List (TMAct Q Γ)) :
    (as.map fun a => wStartHeadFix (Q := Q) (Γ := Γ) K (Sum.inl a)).sum =
      (as.countP (isStart SyncKind.head) : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isStart SyncKind.head a = true
      · simp [wStartHeadFix, h]; ring
      · simp [wStartHeadFix, h]

/-- **The repaired head counter of the repaired problem runs exactly `K² + 3K + 1` units.**  Each
of them consumes one request, and none of them answers for free. -/
theorem countP_startHead_eqFix (hK : 1 ≤ K) {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isStart SyncKind.head) = 1 + K + K * (K + 2) := by
  have hw := weight_of_netYield (balanced_wStartHeadFix (N := N) (w := w) (K := K)) h
  rw [sum_map_wStartHeadFix, weight_tnIFix] at hw
  simp only [wStartHeadFix, startHeadCountFix] at hw
  have hw' : as.countP (isStart SyncKind.head) = K * (K + 2) + 2 + (K - 1) := by exact_mod_cast hw
  omega

/-- **The head counter of a solution plan of the repaired problem is exhausted exactly.**  The
tape and the transitions together issue exactly one request per unit of the counter — for the
printed construction the count is off by the one free answer of the prologue. -/
theorem countP_callHead_eq_of_isSolutionPlanFix (hK : 1 ≤ K) {as : List (TMAct Q Γ)}
    (h : (problemFix N w K).IsSolutionPlan as) :
    as.countP (isCall SyncKind.head) = 1 + K + K * (K + 2) := by
  obtain ⟨hy, -, -⟩ := Problem.isSolutionPlan_iff.1 h
  obtain ⟨-, -, h₃, h₄⟩ := countP_sync_eq_of_isSolutionPlan_fix SyncKind.head h
  rw [countP_startHead_eqFix hK hy] at h₃ h₄
  omega

/-- **The transitions of a solution plan of the repaired problem eat up exactly `K` steps of the
head counter.** -/
theorem countP_extra_acquireHeadFix {as : List (TMAct Q Γ)} (hw0 : w ≠ []) (hwK : w.length ≤ K)
    (h : (problemFix N w K).IsSolutionPlan as) :
    as.countP (isCall SyncKind.head) = as.countP isAssert + K := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw0
  have hK : 1 ≤ K := by omega
  obtain ⟨hy, -, -⟩ := Problem.isSolutionPlan_iff.1 h
  have h₁ := countP_callHead_eq_of_isSolutionPlanFix hK h
  rw [countP_assert_eq_sqFix hw0 hwK hy, h₁]
  ring_nf

/-! ### The state invariants

The initial state and the action model of the repaired problem are those of the printed one, so
the two state invariants of `HtnComplexity/TMEnc/TMEncSim.lean` hold verbatim. -/

/-- **At every point of a plan of the repaired problem at most one tape symbol holds.** -/
theorem symUnique_of_seqApplicableFix {as : List (TMAct Q Γ)}
    (h : (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as ((problemFix N w K).init)) :
    SymUnique ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as ((problemFix N w K).init)) :=
  symUnique_transitionSeq as _ h (symUnique_init (N := N) (w := w) (K := K))

/-- **At every point of a plan of the repaired problem the head flag is consistent.** -/
theorem headUnique_of_planFix (as : List (TMAct Q Γ)) :
    HeadUnique ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as ((problemFix N w K).init)) :=
  headUnique_transitionSeq as _ (headUnique_init (N := N) (w := w) (K := K))

end TMEnc

end HTN
