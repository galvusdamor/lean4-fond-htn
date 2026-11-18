import HtnComplexity.ToHtnAc.ToHtnAcStepSeg
import HtnComplexity.ToHtnAc.ToHtnAcComplete
import HtnComplexity.ToHtnAc.ToHtnAcLockstep
/-!
# Quiescent points of a plan: no semaphore is up

The soundness half of the correctness of the TO-HTN ⟶ HTN-AC compilation needs to know that, at
a point of a plan at which no handshake is open, the only component that can move is the proof
step holding the lock: every other component would have to begin with `lock`, `accept_X` or
`wait_X`, and each of those actions needs a semaphore that is down.

That the semaphores really are down is proved here, directly from the semaphore invariant of
`HtnPlanning/Interleave/Semaphore.lean` (no global counting is needed):

* `HTN.ToAc.key1_notMem_of_countP_eq` — as many `accept_X` as `ask_X` executed ⟹ `key₁^X` is
  down, so no `accept_X` is applicable: no memory cell can enter a phase;
* `HTN.ToAc.key2_notMem_of_countP_eq` — as many `wait_X` as `done_X` executed ⟹ `key₂^X` is
  down, so no `wait_X` is applicable: no proof step can consume an answer;
* `HTN.ToAc.key0_notMem_of_lock_held` — one more `lock` than `unlock` executed ⟹ `key₀` is
  down, so no `lock` is applicable: no further proof step can start.

`HTN.ToAc.Quiescent` packages the three counting conditions, and
`HTN.ToAc.not_applicable_of_quiescent` states the conclusion: at a quiescent point of a plan the
actions `lock`, `accept_R`, `accept_W`, `wait_R` and `wait_W` are all inapplicable.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {Q : Instance F A C I} {vars : List F}
  {bound : ℕ} {tI0 : C} {p : List (AcAct F A C)}

open Domain ActionModel

/-! ### The value of a semaphore at a point of a plan -/

/-- A semaphore that is initially down and has been consumed as often as it has been signalled
is down. -/
lemma notMem_of_semaphore_countP_eq {f : AcFact F A C} {sig con : AcAct F A C → Bool}
    (hsem : (actionModel D.toActionModel :
      ActionModel (AcFact F A C) (AcAct F A C)).Semaphore f sig con)
    (hinit : f ∉ (problem D Q vars bound tI0).init)
    (happ : (problem D Q vars bound tI0).SeqApplicable p (problem D Q vars bound tI0).init)
    (h : p.countP sig ≤ p.countP con) :
    f ∉ (problem D Q vars bound tI0).transitionSeq p (problem D Q vars bound tI0).init := by
  have hle := hsem.countP_add_ind_le p (problem D Q vars bound tI0).init happ
  rw [ind_eq_zero hinit] at hle
  intro hmem
  have h1 : ind f ((actionModel D.toActionModel).transitionSeq p
      (problem D Q vars bound tI0).init) = 1 := ind_eq_one hmem
  rw [h1] at hle
  omega

/-- **A memory cell can only start a phase after a request.**  If at a point of a plan as many
`accept_X` as `ask_X` actions have been executed, then `key₁^X` is down. -/
theorem key1_notMem_of_countP_eq (x : RW)
    (happ : (problem D Q vars bound tI0).SeqApplicable p (problem D Q vars bound tI0).init)
    (h : p.countP (isAsk x) ≤ p.countP (isAccept x)) :
    (AcFact.key1 x : AcFact F A C) ∉
      (problem D Q vars bound tI0).transitionSeq p (problem D Q vars bound tI0).init :=
  notMem_of_semaphore_countP_eq
    (semaphore_key1 (D := D.toActionModel) (F := F) (A := A) (C := C) x)
    (key1_notMem_init (Q := Q) (tI0 := tI0) x) happ h

/-- **A proof step can only consume an answer that has been given.**  If at a point of a plan as
many `wait_X` as `done_X` actions have been executed, then `key₂^X` is down. -/
theorem key2_notMem_of_countP_eq (x : RW)
    (happ : (problem D Q vars bound tI0).SeqApplicable p (problem D Q vars bound tI0).init)
    (h : p.countP (isDone x) ≤ p.countP (isWait x)) :
    (AcFact.key2 x : AcFact F A C) ∉
      (problem D Q vars bound tI0).transitionSeq p (problem D Q vars bound tI0).init :=
  notMem_of_semaphore_countP_eq
    (semaphore_key2 (D := D.toActionModel) (F := F) (A := A) (C := C) x)
    (key2_notMem_init (Q := Q) (tI0 := tI0) x) happ h

/-- **While a proof step holds the lock no other step can start.**  If at a point of a plan one
more `lock` than `unlock` action has been executed, then `key₀` is down. -/
theorem key0_notMem_of_lock_held
    (happ : (problem D Q vars bound tI0).SeqApplicable p (problem D Q vars bound tI0).init)
    (h : p.countP isUnlock < p.countP isLock) :
    (AcFact.key0 : AcFact F A C) ∉
      (problem D Q vars bound tI0).transitionSeq p (problem D Q vars bound tI0).init := by
  have hle := (semaphore_key0 (D := D.toActionModel) (F := F) (A := A) (C := C)).countP_add_ind_le
    p (problem D Q vars bound tI0).init happ
  have h0 : ind (AcFact.key0 : AcFact F A C) (problem D Q vars bound tI0).init = 1 :=
    ind_eq_one (key0_mem_init (Q := Q) (tI0 := tI0))
  rw [h0] at hle
  intro hmem
  have h1 : ind (AcFact.key0 : AcFact F A C) ((actionModel D.toActionModel).transitionSeq p
      (problem D Q vars bound tI0).init) = 1 := ind_eq_one hmem
  rw [h1] at hle
  omega

/-! ### Quiescent points -/

/-- A point of a plan is *quiescent* if a proof step holds the lock and no handshake is in
progress at all: every request has been accepted, every acceptance has been answered and every
answer has been consumed. -/
def Quiescent (p : List (AcAct F A C)) : Prop :=
  p.countP isUnlock < p.countP isLock ∧
    ∀ x : RW, p.countP (isAsk x) = p.countP (isAccept x) ∧
      p.countP (isAccept x) = p.countP (isDone x) ∧
      p.countP (isDone x) = p.countP (isWait x)

/-- **A point at which the lock is held and no request is open is quiescent.**  By the lock-step
theorem the four counters of a handshake channel are then all equal, so no memory cell is inside
a phase either. -/
theorem quiescent_of_no_open_request (hnd : vars.Nodup)
    {γs σs : List (List (AcAct F A C))} {as as₁ as₂ q : List (AcAct F A C)}
    (hγ : ∀ γ ∈ γs, (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] γ)
    (hσ : ∀ σ ∈ σs, (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] σ)
    (hcells : InterleaveList γs as₁) (hsteps : InterleaveList σs as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hpq : as = p ++ q)
    (hlock : p.countP isUnlock < p.countP isLock)
    (hopen : ∀ x : RW, p.countP (isAsk x) = p.countP (isWait x)) :
    Quiescent p := by
  refine ⟨hlock, fun x => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    handshake_lockstep' (Q := Q) (tI0 := tI0) hnd x hγ hσ hcells hsteps hint happ hpq
  have := hopen x
  exact ⟨by omega, by omega, by omega⟩

/-- A predicate implied by `isSync` counts nothing in a sequence without synchronisation
actions. -/
lemma countP_eq_zero_of_countP_isSync {v : List (AcAct F A C)} (hv : v.countP isSync = 0)
    {q : AcAct F A C → Bool} (hq : ∀ a : AcAct F A C, q a → isSync a) : v.countP q = 0 := by
  refine List.countP_eq_zero.2 fun a ha => ?_
  intro hqa
  exact (List.countP_eq_zero.1 hv) a ha (hq a hqa)

/-- **Executing actions that do not synchronise preserves quiescence.**  This is what makes the
exclusion lemma iterable: the active proof step keeps the lock and opens no request while it
guesses and compares. -/
lemma Quiescent.append_nonSync {v : List (AcAct F A C)} (h : Quiescent p)
    (hv : v.countP isSync = 0) : Quiescent (p ++ v) := by
  have hL : v.countP isLock = 0 :=
    countP_eq_zero_of_countP_isSync hv (by intro a; cases a <;> simp [isLock, isSync])
  have hU : v.countP isUnlock = 0 :=
    countP_eq_zero_of_countP_isSync hv (by intro a; cases a <;> simp [isUnlock, isSync])
  have hA : ∀ x : RW, v.countP (isAsk x) = 0 := fun x =>
    countP_eq_zero_of_countP_isSync hv (by intro a; cases a <;> simp [isAsk, isSync])
  have hC : ∀ x : RW, v.countP (isAccept x) = 0 := fun x =>
    countP_eq_zero_of_countP_isSync hv (by intro a; cases a <;> simp [isAccept, isSync])
  have hD : ∀ x : RW, v.countP (isDone x) = 0 := fun x =>
    countP_eq_zero_of_countP_isSync hv (by intro a; cases a <;> simp [isDone, isSync])
  have hW : ∀ x : RW, v.countP (isWait x) = 0 := fun x =>
    countP_eq_zero_of_countP_isSync hv (by intro a; cases a <;> simp [isWait, isSync])
  obtain ⟨hlock, hhs⟩ := h
  refine ⟨by rw [List.countP_append, List.countP_append, hL, hU]; omega, fun x => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hhs x
  have e := hA x; have e' := hC x; have e'' := hD x; have e''' := hW x
  refine ⟨?_, ?_, ?_⟩ <;> simp only [List.countP_append, e, e', e'', e'''] <;> omega

/-- **At a quiescent point only the proof step holding the lock can move.**  None of the
actions that a memory cell or another proof step would have to perform next — `accept_X` to
enter a phase, `lock` to start, `wait_X` to consume an answer — is applicable. -/
theorem not_applicable_of_quiescent (hq : Quiescent p)
    (happ : (problem D Q vars bound tI0).SeqApplicable p (problem D Q vars bound tI0).init) :
    ¬ (domain D vars bound).Applicable (AcAct.lock : AcAct F A C)
        ((problem D Q vars bound tI0).transitionSeq p (problem D Q vars bound tI0).init) ∧
      ∀ x : RW,
        ¬ (domain D vars bound).Applicable (AcAct.accept x)
            ((problem D Q vars bound tI0).transitionSeq p
              (problem D Q vars bound tI0).init) ∧
          ¬ (domain D vars bound).Applicable (AcAct.waitA x)
            ((problem D Q vars bound tI0).transitionSeq p
              (problem D Q vars bound tI0).init) := by
  obtain ⟨hlock, hhs⟩ := hq
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · rw [applicable_lock_iff]
    exact key0_notMem_of_lock_held happ hlock
  · rw [applicable_accept_iff]
    exact key1_notMem_of_countP_eq x happ (le_of_eq (hhs x).1)
  · rw [applicable_waitA_iff]
    exact key2_notMem_of_countP_eq x happ (le_of_eq (hhs x).2.2)

end ToAc

end HTN
