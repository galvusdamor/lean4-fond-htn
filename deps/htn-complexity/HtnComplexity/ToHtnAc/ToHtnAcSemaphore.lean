import HtnPlanning.Interleave.Semaphore
import HtnComplexity.ToHtnAc.ToHtnAc
/-!
# The semaphores of the TO-HTN ⟶ HTN-AC compilation

The compilation of `HtnComplexity/ToHtnAc/ToHtnAc.lean` synchronises the parallel `MEM`, `READ`,
`WRITE` and `TUPLE` tasks through three families of facts:

* `key₁^X` is raised by `ask_X` and lowered by `accept_X`,
* `key₂^X` is raised by `done_X` and lowered by `wait_X`,
* `key₀` is raised by `unlock` and lowered by `lock`, and holds initially.

Each of them is a boolean semaphore in the sense of `HtnPlanning/Interleave/Semaphore.lean`, so the
counting invariant proved there applies.  The consequences recorded here are the *handshake
bounds*: in every executable plan of the compiled problem — indeed in every applicable prefix of
one — there are at most as many `accept_X` as `ask_X` actions and at most as many `wait_X` as
`done_X` actions, and at most one more `lock` than `unlock` action.

Since each `MEM` task contributes exactly one `accept_W` and one `done_R`, each `WRITE` task one
`ask_W` and one `wait_W`, each `READ` task one `ask_R` and one `wait_R`, and the innermost body
of `STATE_0^3` one `done_W` and one `accept_R`, these bounds are what forces every use of a
memory cell to be paired with a `READ`/`WRITE` occurrence inside a `TUPLE` body.
-/

namespace HTN

namespace ToAc

variable {F A C : Type}

/-! ### Recognising the synchronisation actions -/

/-- Is the action `ask_X`? -/
def isAsk (x : RW) : AcAct F A C → Bool
  | .ask y => y == x
  | _ => false

/-- Is the action `accept_X`? -/
def isAccept (x : RW) : AcAct F A C → Bool
  | .accept y => y == x
  | _ => false

/-- Is the action `done_X`? -/
def isDone (x : RW) : AcAct F A C → Bool
  | .doneA y => y == x
  | _ => false

/-- Is the action `wait_X`? -/
def isWait (x : RW) : AcAct F A C → Bool
  | .waitA y => y == x
  | _ => false

/-- Is the action `lock`? -/
def isLock : AcAct F A C → Bool
  | .lock => true
  | _ => false

/-- Is the action `unlock`? -/
def isUnlock : AcAct F A C → Bool
  | .unlock => true
  | _ => false

/-! ### The three semaphores -/

variable {D : ActionModel F A}

/-- `key₁^X` is a boolean semaphore raised by `ask_X` and lowered by `accept_X`. -/
theorem semaphore_key1 (x : RW) :
    (actionModel D : ActionModel (AcFact F A C) (AcAct F A C)).Semaphore
      (AcFact.key1 x) (isAsk x) (isAccept x) where
  con_prec := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | y | _ | _ | _) h <;>
      simp_all [isAccept, actionModel, prec]
  con_del := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | y | _ | _ | _) h <;>
      simp_all [isAccept, actionModel, del]
  con_not_add := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | y | _ | _ | _) h <;>
      simp_all [isAccept, actionModel, add]
  add_sig := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | y | _ | _ | _ | _) h <;>
      simp_all [isAsk, actionModel, add]
  del_con := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | y | _ | _ | _) h <;>
      simp_all [isAccept, actionModel, del]

/-- `key₂^X` is a boolean semaphore raised by `done_X` and lowered by `wait_X`. -/
theorem semaphore_key2 (x : RW) :
    (actionModel D : ActionModel (AcFact F A C) (AcAct F A C)).Semaphore
      (AcFact.key2 x) (isDone x) (isWait x) where
  con_prec := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | y | _) h <;>
      simp_all [isWait, actionModel, prec]
  con_del := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | y | _) h <;>
      simp_all [isWait, actionModel, del]
  con_not_add := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | y | _) h <;>
      simp_all [isWait, actionModel, add]
  add_sig := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | y | _ | _) h <;>
      simp_all [isDone, actionModel, add]
  del_con := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | y | _) h <;>
      simp_all [isWait, actionModel, del]

/-- `key₀` is a boolean semaphore raised by `unlock` and lowered by `lock`. -/
theorem semaphore_key0 :
    (actionModel D : ActionModel (AcFact F A C) (AcAct F A C)).Semaphore
      AcFact.key0 isUnlock isLock where
  con_prec := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) h <;>
      simp_all [isLock, actionModel, prec]
  con_del := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) h <;>
      simp_all [isLock, actionModel, del]
  con_not_add := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) h <;>
      simp_all [isLock, actionModel, add]
  add_sig := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) h <;>
      simp_all [isUnlock, actionModel, add]
  del_con := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) h <;>
      simp_all [isLock, actionModel, del]

/-! ### The initial state -/

section Instance

variable {I : Type} {Q : Instance F A C I} {tI0 : C}

lemma key1_notMem_init (x : RW) : AcFact.key1 x ∉ (instance_ Q tI0).init := by
  rintro (h | ⟨v, i, h⟩) <;> simp_all

lemma key2_notMem_init (x : RW) : AcFact.key2 x ∉ (instance_ Q tI0).init := by
  rintro (h | ⟨v, i, h⟩) <;> simp_all

lemma key0_mem_init : (AcFact.key0 : AcFact F A C) ∈ (instance_ Q tI0).init :=
  Or.inl rfl

/-! ### The handshake bounds -/

variable {D' : Domain F A C I} {vars : List F} {bound : ℕ} {as : List (AcAct F A C)}

/-- **Every `accept_X` in an executable plan of the compiled problem is matched by an earlier
`ask_X`.**  Stated as a counting bound; applying it to the prefixes of a plan (which are
applicable as well) gives the prefix property. -/
theorem countP_accept_le_countP_ask (x : RW)
    (happ : (problem D' Q vars bound tI0).SeqApplicable as (problem D' Q vars bound tI0).init) :
    as.countP (isAccept x) ≤ as.countP (isAsk x) :=
  (semaphore_key1 (D := D'.toActionModel) (F := F) (A := A) (C := C) x).countP_con_le happ
    (key1_notMem_init (Q := Q) (tI0 := tI0) x)

/-- **Every `wait_X` in an executable plan of the compiled problem is matched by an earlier
`done_X`.** -/
theorem countP_wait_le_countP_done (x : RW)
    (happ : (problem D' Q vars bound tI0).SeqApplicable as (problem D' Q vars bound tI0).init) :
    as.countP (isWait x) ≤ as.countP (isDone x) :=
  (semaphore_key2 (D := D'.toActionModel) (F := F) (A := A) (C := C) x).countP_con_le happ
    (key2_notMem_init (Q := Q) (tI0 := tI0) x)

/-- **The `TUPLE` bodies of an executable plan of the compiled problem do not overlap:** every
`lock` but the first is matched by an earlier `unlock`. -/
theorem countP_lock_le_countP_unlock_succ
    (happ : (problem D' Q vars bound tI0).SeqApplicable as (problem D' Q vars bound tI0).init) :
    as.countP isLock ≤ as.countP isUnlock + 1 :=
  (semaphore_key0 (D := D'.toActionModel) (F := F) (A := A) (C := C)).countP_con_le_succ happ

/-- The same bounds for a solution plan of the compiled problem. -/
theorem IsSolutionPlan.countP_accept_le_countP_ask (x : RW)
    (h : (problem D' Q vars bound tI0).IsSolutionPlan as) :
    as.countP (isAccept x) ≤ as.countP (isAsk x) :=
  ToAc.countP_accept_le_countP_ask (Q := Q) (tI0 := tI0) (vars := vars) (bound := bound)
    x h.classical.1

/-- The same bounds for a solution plan of the compiled problem. -/
theorem IsSolutionPlan.countP_wait_le_countP_done (x : RW)
    (h : (problem D' Q vars bound tI0).IsSolutionPlan as) :
    as.countP (isWait x) ≤ as.countP (isDone x) :=
  ToAc.countP_wait_le_countP_done (Q := Q) (tI0 := tI0) (vars := vars) (bound := bound)
    x h.classical.1

/-- The same bounds for a solution plan of the compiled problem. -/
theorem IsSolutionPlan.countP_lock_le_countP_unlock_succ
    (h : (problem D' Q vars bound tI0).IsSolutionPlan as) :
    as.countP isLock ≤ as.countP isUnlock + 1 :=
  ToAc.countP_lock_le_countP_unlock_succ (Q := Q) (tI0 := tI0) (vars := vars)
    (bound := bound) h.classical.1

end Instance

end ToAc

end HTN
