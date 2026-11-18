import HtnPlanning.Interleave.Semaphore
import HtnComplexity.TMEnc.TMEncFixCount
/-!
# The channels of the encoding alternate

`HtnComplexity/TMEnc/TMEncSem.lean` proves the two *global* semaphore inequalities of a channel;
`HtnComplexity/TMEnc/TMEncCount.lean` turns them, together with the hierarchy, into the equalities
`#call x = #wait x = #respond x = #start x` of a solution plan.  This file adds the
corresponding **prefix** statement, which is what a simulation argument needs: at every point of
a solution plan the number of requests issued on a cell channel is the number answered so far
plus the value of the semaphore, so a second request is never issued before the previous one has
been answered.

* `HTN.TMEnc.semaphore_stepF`, `HTN.TMEnc.semaphore_steppedF` — the two facts of a channel are
  boolean semaphores of the action model in the sense of
  `HTN.ActionModel.Semaphore` (this depends on the action model only, hence holds for the
  printed and for the repaired construction alike);
* `HTN.TMEnc.countP_prefix_call_eq_start_add_ind_fix`,
  `HTN.TMEnc.countP_prefix_respond_eq_wait_add_ind_fix` — the exact prefix count for a solution
  plan of the repaired problem;
* `HTN.TMEnc.countP_prefix_alternates_fix` — the resulting alternation bounds.
-/

namespace HTN

namespace TMEnc

open TM ActionModel

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The two facts of a channel are boolean semaphores -/

/-- The fact `x_step` is a boolean semaphore: `call x` raises it and `start x`, which requires
it, lowers it. -/
theorem semaphore_stepF (x : SyncKind) :
    (actionModel (Q := Q) (Γ := Γ)).Semaphore (TMFact.stepF x) (isCall x) (isStart x) where
  con_prec := by
    intro a ha
    cases a with
    | start y =>
        have hy : y = x := by simpa [isStart] using ha
        subst hy
        simp [actionModel, TMEnc.prec]
    | _ => simp [isStart] at ha
  con_del := by
    intro a ha
    cases a with
    | start y =>
        have hy : y = x := by simpa [isStart] using ha
        subst hy
        simp [actionModel, TMEnc.del]
    | _ => simp [isStart] at ha
  con_not_add := by
    intro a ha
    cases a with
    | start y =>
        have hy : y = x := by simpa [isStart] using ha
        subst hy
        simp [actionModel, TMEnc.add]
    | _ => simp [isStart] at ha
  add_sig := by
    intro a ha
    cases a <;>
      simp_all [actionModel, TMEnc.add, isCall, eq_comm]
  del_con := by
    intro a ha
    cases a <;>
      simp_all [actionModel, TMEnc.del, isStart, eq_comm]

/-- The fact `x_stepped` is a boolean semaphore: `respond x` raises it and `wait x`, which
requires it, lowers it. -/
theorem semaphore_steppedF (x : SyncKind) :
    (actionModel (Q := Q) (Γ := Γ)).Semaphore (TMFact.steppedF x) (isRespond x) (isWait x) where
  con_prec := by
    intro a ha
    cases a with
    | wait y =>
        have hy : y = x := by simpa [isWait] using ha
        subst hy
        simp [actionModel, TMEnc.prec]
    | _ => simp [isWait] at ha
  con_del := by
    intro a ha
    cases a with
    | wait y =>
        have hy : y = x := by simpa [isWait] using ha
        subst hy
        simp [actionModel, TMEnc.del]
    | _ => simp [isWait] at ha
  con_not_add := by
    intro a ha
    cases a with
    | wait y =>
        have hy : y = x := by simpa [isWait] using ha
        subst hy
        simp [actionModel, TMEnc.add]
    | _ => simp [isWait] at ha
  add_sig := by
    intro a ha
    cases a <;>
      simp_all [actionModel, TMEnc.add, isRespond, eq_comm]
  del_con := by
    intro a ha
    cases a <;>
      simp_all [actionModel, TMEnc.del, isWait, eq_comm]

/-! ### The exact prefix counts of a solution plan of the repaired problem -/

/-- **At every point of a solution plan, the requests on a cell channel are the answers plus the
value of the semaphore.**  Since the semaphore is boolean, at most one request is outstanding. -/
theorem countP_prefix_call_eq_start_add_ind_fix (x : SyncKind)
    {as : List (TMAct Q Γ)} (h : (problemFix N w K).IsSolutionPlan as)
    {p q : List (TMAct Q Γ)} (hpq : as = p ++ q) :
    p.countP (isCall x) =
      p.countP (isStart x) +
        ind (TMFact.stepF x) ((actionModel (Q := Q) (Γ := Γ)).transitionSeq p
          ((problemFix N w K).init)) := by
  obtain ⟨-, happ, -⟩ := Problem.isSolutionPlan_iff.1 h
  obtain ⟨h₁, h₂, h₃⟩ := countP_sync_eq_of_isSolutionPlan_fix' x h
  exact (semaphore_stepF x).countP_prefix_add_ind happ (stepF_not_mem_initFix x)
    (by omega) hpq

/-- The same statement for the second semaphore of a cell channel. -/
theorem countP_prefix_respond_eq_wait_add_ind_fix (x : SyncKind)
    {as : List (TMAct Q Γ)} (h : (problemFix N w K).IsSolutionPlan as)
    {p q : List (TMAct Q Γ)} (hpq : as = p ++ q) :
    p.countP (isRespond x) =
      p.countP (isWait x) +
        ind (TMFact.steppedF x) ((actionModel (Q := Q) (Γ := Γ)).transitionSeq p
          ((problemFix N w K).init)) := by
  obtain ⟨-, happ, -⟩ := Problem.isSolutionPlan_iff.1 h
  obtain ⟨h₁, h₂, h₃⟩ := countP_sync_eq_of_isSolutionPlan_fix' x h
  exact (semaphore_steppedF x).countP_prefix_add_ind happ (steppedF_not_mem_initFix x)
    (by omega) hpq

/-- **The channels of the repaired construction alternate.**  At every point of a solution plan
the number of requests issued on a cell channel is the number of answers given, or one more; and
likewise for the second half of the handshake.  In particular no process of the construction can
run a whole cell ahead of another one. -/
theorem countP_prefix_alternates_fix (x : SyncKind)
    {as : List (TMAct Q Γ)} (h : (problemFix N w K).IsSolutionPlan as)
    {p q : List (TMAct Q Γ)} (hpq : as = p ++ q) :
    p.countP (isStart x) ≤ p.countP (isCall x) ∧
      p.countP (isCall x) ≤ p.countP (isStart x) + 1 ∧
      p.countP (isWait x) ≤ p.countP (isRespond x) ∧
      p.countP (isRespond x) ≤ p.countP (isWait x) + 1 := by
  have h₁ := countP_prefix_call_eq_start_add_ind_fix x h hpq
  have h₂ := countP_prefix_respond_eq_wait_add_ind_fix x h hpq
  have hi₁ := ind_le_one (TMFact.stepF x)
    ((actionModel (Q := Q) (Γ := Γ)).transitionSeq p ((problemFix N w K).init))
  have hi₂ := ind_le_one (TMFact.steppedF x)
    ((actionModel (Q := Q) (Γ := Γ)).transitionSeq p ((problemFix N w K).init))
  exact ⟨by omega, by omega, by omega, by omega⟩

end TMEnc

end HTN
