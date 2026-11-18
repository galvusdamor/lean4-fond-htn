import HtnComplexity.TMEnc.TMEncFix
/-!
# The handshake counting theorem for the repaired encoding

`HtnComplexity/TMEnc/TMEncCount.lean` proves, for the construction as printed, that in every
solution plan the four synchronisation actions of a channel occur equally often (up to the one
answer of the prologue of the head counter).  The repaired construction of
`HtnComplexity/TMEnc/TMEncFix.lean` differs from the printed one at the single body of
`checkers¹`, and that body contains no synchronisation *action* at all — it consists of three
compound tasks.  All of the counting therefore transfers verbatim, through the generic body
lemma `HTN.TMEnc.sum_weight_bodies` of the printed development.

* `HTN.TMEnc.countP_call_eq_countP_wait_fix`, `HTN.TMEnc.countP_respond_eq_countP_start_fix` —
  the hierarchy half;
* `HTN.TMEnc.countP_sync_eq_of_isSolutionPlan_fix` and
  `HTN.TMEnc.countP_sync_eq_of_isSolutionPlan_fix'` — the lock-step theorem for the repaired
  problem.

Together with `HTN.TMEnc.countP_start_eq_countP_call_fix` this says that the repaired
construction *passes* the test that refutes the printed one: the number of answers the `K + 1`
cell counters give on a cell channel is exactly the number of requests the `(K+1)²` cells of
the witness issue, namely `(K+1)³`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **The transfer lemma.**  A weight that vanishes on all actions except the four of a channel,
is balanced on the two pairs `call`/`wait` and `start`/`respond` and charges a compound task
with `-d` per occurrence of `sI`, weighs every body of the *repaired* construction exactly as
much as the task it decomposes.  The repaired body of `checkers¹` consists of compound tasks
only, so it is weighed by the `sI`-count alone. -/
lemma sum_weight_bodiesFix (d : ℤ) (ω : TMAct Q Γ ⊕ TMTask Q Γ → ℤ)
    (hcomp : ∀ t : TMTask Q Γ, ω (Sum.inr t) = -(sICount t : ℤ) * d)
    (hacq : ∀ y : SyncKind,
      ω (Sum.inl (TMAct.call y)) + ω (Sum.inl (TMAct.wait y)) = 0)
    (hrel : ∀ y : SyncKind,
      ω (Sum.inl (TMAct.start y)) + ω (Sum.inl (TMAct.respond y)) = 0)
    (hother : (∀ (c : Option Γ), ω (Sum.inl (TMAct.assert c)) = 0) ∧
      (∀ f : TMFact Q Γ, ω (Sum.inl (TMAct.check f)) = 0) ∧
      ω (Sum.inl (TMAct.assertHead : TMAct Q Γ)) = 0 ∧
      ω (Sum.inl (TMAct.retractHead : TMAct Q Γ)) = 0 ∧
      ∀ (q : Q) (c : Option Γ) (q' : Q) (c' : Option Γ),
        ω (Sum.inl (TMAct.step q c q' c')) = 0)
    {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map ω).sum = ω (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix, hcomp, sICount]
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact sum_weight_bodies d ω hcomp hacq hrel hother hls

/-- **The weight of the initial method of the repaired construction.**  Its three chains consist
of compound tasks only — the repaired head counter of `HTN.TMEnc.headChainFix` has no bare
prologue — and none of them expands into `sI`, so the initial method weighs nothing. -/
lemma sum_weight_initChainsFix (d : ℤ) (ω : TMAct Q Γ ⊕ TMTask Q Γ → ℤ)
    (hcomp : ∀ t : TMTask Q Γ, ω (Sum.inr t) = -(sICount t : ℤ) * d) :
    (((initChainsFix K : List (List (TMAct Q Γ ⊕ TMTask Q Γ))) ++
      [[Sum.inr (TMTask.done : TMTask Q Γ)]]).flatten.map ω).sum = 0 := by
  simp [initChainsFix, headChainFix, hcomp, sICount]

/-- The weight counting the actions of a task answering a step of the channel `x`, for the
**repaired** construction: `+1` for `start x`, `-1` for `respond x`, and `0` on every compound
task.  The printed construction needs the correction `-1` per occurrence of `sI` on the channel
`head` (`HTN.TMEnc.wReleaseOn`), because its head counter answers the first request for free;
the repaired counter does not. -/
def wRelease0 (x : SyncKind) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => (if isStart x a = true then 1 else 0) - (if isRespond x a = true then 1 else 0)
  | Sum.inr _ => 0

lemma sum_map_wRelease0 (x : SyncKind) (as : List (TMAct Q Γ)) :
    (as.map fun a => wRelease0 (Q := Q) (Γ := Γ) x (Sum.inl a)).sum =
      (as.countP (isStart x) : ℤ) - as.countP (isRespond x) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.countP_cons]
      by_cases hc : isStart x a = true <;> by_cases hw : isRespond x a = true <;>
        simp [wRelease0, hc, hw] <;> ring

/-- **The asking weight is balanced for the repaired domain.** -/
lemma balanced_wAcquireFix (x : SyncKind) :
    Balanced (methodsFix N w K) (wAcquire (Q := Q) (Γ := Γ) x) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    refine sum_weight_bodiesFix 0 _ (fun t => by simp [wAcquire]) (fun y => ?_) (fun y => ?_)
      ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ _ _ => rfl⟩ hls
    · by_cases hy : y = x
      · simp [wAcquire, isCall, isWait, hy]
      · simp [wAcquire, isCall, isWait, hy]
    · simp [wAcquire, isCall, isWait]
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail,
      sum_weight_initChainsFix 0 _ (fun t => by simp [wAcquire])]
    simp [wAcquire]

/-- **The answering weight is balanced for the repaired domain.** -/
lemma balanced_wRelease0Fix (x : SyncKind) :
    Balanced (methodsFix N w K) (wRelease0 (Q := Q) (Γ := Γ) x) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    refine sum_weight_bodiesFix 0 _ (fun t => by simp [wRelease0])
      (fun y => by simp [wRelease0, isStart, isRespond]) (fun y => ?_)
      ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ _ _ => rfl⟩ hls
    by_cases hy : y = x
    · simp [wRelease0, isStart, isRespond, hy]
    · simp [wRelease0, isStart, isRespond, hy]
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail,
      sum_weight_initChainsFix 0 _ (fun t => by simp [wRelease0])]
    simp [wRelease0]

/-- **Every refinement of the initial task network of the repaired problem asks for as many
steps as it waits for them.** -/
theorem countP_call_eq_countP_wait_fix (x : SyncKind) {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isCall x) = as.countP (isWait x) := by
  have hw := weight_of_netYield (balanced_wAcquireFix (N := N) (w := w) (K := K) x) h
  rw [sum_map_wAcquire, weight_tnIFix] at hw
  simp only [wAcquire] at hw
  omega

/-- **Every refinement of the initial task network of the repaired problem answers exactly as
many steps as it starts**, on every channel — the repaired head counter of
`HTN.TMEnc.headChainFix` answers no request for free. -/
theorem countP_respond_eq_countP_start_fix (x : SyncKind) {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isRespond x) = as.countP (isStart x) := by
  have hw := weight_of_netYield (balanced_wRelease0Fix (N := N) (w := w) (K := K) x) h
  rw [sum_map_wRelease0, weight_tnIFix] at hw
  simp only [wRelease0] at hw
  omega

/-- The initial state of the repaired problem contains no semaphore facts. -/
lemma stepF_not_mem_initFix (x : SyncKind) :
    (TMFact.stepF x : TMFact Q Γ) ∉ (problemFix N w K).init := by
  show (TMFact.stepF x : TMFact Q Γ) ∉ ({TMFact.st N.init} : Set (TMFact Q Γ))
  simp

lemma steppedF_not_mem_initFix (x : SyncKind) :
    (TMFact.steppedF x : TMFact Q Γ) ∉ (problemFix N w K).init := by
  show (TMFact.steppedF x : TMFact Q Γ) ∉ ({TMFact.st N.init} : Set (TMFact Q Γ))
  simp

/-- **The handshake counting theorem for the repaired encoding.**  In every solution plan of the
repaired problem the four synchronisation actions of each channel occur equally often, up to the
single answer of the prologue on the channel `head`. -/
theorem countP_sync_eq_of_isSolutionPlan_fix (x : SyncKind) {as : List (TMAct Q Γ)}
    (h : (problemFix N w K).IsSolutionPlan as) :
    as.countP (isCall x) = as.countP (isWait x) ∧
      as.countP (isRespond x) = as.countP (isStart x) ∧
      as.countP (isStart x) ≤ as.countP (isCall x) ∧
      as.countP (isCall x) ≤ as.countP (isStart x) := by
  obtain ⟨hy, happ, -⟩ := Problem.isSolutionPlan_iff.1 h
  have h₁ : as.countP (isCall x) = as.countP (isWait x) := countP_call_eq_countP_wait_fix x hy
  have h₂ : as.countP (isRespond x) = as.countP (isStart x) :=
    countP_respond_eq_countP_start_fix x hy
  have h₃ : as.countP (isStart x) ≤ as.countP (isCall x) :=
    countP_start_le_countP_call x (stepF_not_mem_initFix x) happ
  have h₄ : as.countP (isWait x) ≤ as.countP (isRespond x) :=
    countP_wait_le_countP_respond x (steppedF_not_mem_initFix x) happ
  exact ⟨h₁, h₂, h₃, by omega⟩

/-- **The handshake counting theorem for the two cell channels of the repaired encoding.** -/
theorem countP_sync_eq_of_isSolutionPlan_fix' (x : SyncKind) {as : List (TMAct Q Γ)}
    (h : (problemFix N w K).IsSolutionPlan as) :
    as.countP (isCall x) = as.countP (isWait x) ∧
      as.countP (isWait x) = as.countP (isRespond x) ∧
      as.countP (isRespond x) = as.countP (isStart x) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := countP_sync_eq_of_isSolutionPlan_fix x h
  exact ⟨h₁, by omega, by omega⟩

/-- **The repaired construction passes the test that refutes the printed one.**  For a cell
channel the balance required of a solution plan — as many `start` as `call` actions — is
satisfied by *every* refinement of the initial task network of the repaired problem, whereas for
the printed construction the two counts differ by `checkersCount K (K+1) − (K+1)³ ≥ K + 1`,
which is why the printed problem is unsolvable (`HTN.TMEnc.not_solvable`). -/
theorem countP_sync_consistent_fix (x : SyncKind) (hx : x ≠ SyncKind.head) (hw0 : w ≠ [])
    (hwK : w.length ≤ K) {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isCall x) = as.countP (isWait x) ∧
      as.countP (isWait x) = as.countP (isRespond x) ∧
      as.countP (isRespond x) = as.countP (isStart x) := by
  have hxx : x = SyncKind.check ∨ x = SyncKind.sync := by
    cases x with
    | head => exact absurd rfl hx
    | check => exact Or.inl rfl
    | sync => exact Or.inr rfl
  have h₁ : as.countP (isCall x) = as.countP (isWait x) := countP_call_eq_countP_wait_fix x h
  have h₂ : as.countP (isRespond x) = as.countP (isStart x) :=
    countP_respond_eq_countP_start_fix x h
  have h₃ : as.countP (isStart x) = as.countP (isCall x) :=
    countP_start_eq_countP_call_fix x hxx hw0 hwK h
  exact ⟨h₁, by omega, h₂⟩

end TMEnc

end HTN
