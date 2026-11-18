import HtnPlanning.Core.PrefixSum
import HtnComplexity.ToHtnAc.ToHtnAcCellPhase
import HtnComplexity.ToHtnAc.ToHtnAcMutex
/-!
# The handshakes of a plan of the HTN-AC compilation run in lock-step

A plan of the compiled problem of `HtnComplexity/ToHtnAc/ToHtnAc.lean` interleaves the runs of the
parallel memory cells with the runs of the parallel proof steps, and the two families
communicate through the handshakes `ask_X`, `accept_X`, `done_X`, `wait_X`: a proof step *asks*
for a memory cell and *waits* for the answer, a memory cell *accepts* the request and signals
that it is *done*.

The semaphore invariants of `HtnComplexity/ToHtnAc/ToHtnAcSemaphore.lean` say that in an executable
plan there are never more `accept_X` than `ask_X` and never more `wait_X` than `done_X`, and the
counting theorem `HTN.ToAc.countP_handshake_eq_card_mem` says that in a plan the four numbers are
*equal*: no request goes unanswered and no answer is lost.  Together with the shape of the two
kinds of run this pins the behaviour completely:

`HTN.ToAc.handshake_lockstep` — at **every point** of a plan,

```
#wait_X  ≤  #done_X  ≤  #accept_X  ≤  #ask_X  ≤  #wait_X + 1 ,
```

so the four counters never differ by more than one and the four actions of a handshake occur in
the cyclic order `ask_X`, `accept_X`, `done_X`, `wait_X`.  In particular, whenever an answer is
pending (`#done_X = #wait_X + 1`), *all four counters are equal to `#wait_X + 1`*
(`HTN.ToAc.handshake_all_eq_of_done_pending`): no request is open and no memory cell is between
its `accept_X` and its `done_X`, i.e. the memory cell that answered the pending request is the
only one that has moved and it has finished its phase.

This is the missing matching statement of the soundness half of the correctness proof: it is
what turns the latch specification `HTN.ToAc.mem_isLatch` into the statement that the triple a
proof step reads is the triple some earlier proof step wrote.

The proof is by *prefix sums of integer weights* (`HtnPlanning/Core/PrefixSum.lean`):

* `HTN.ToAc.psumNonneg_cellW` — in a memory cell run, `#done_X` never overtakes `#accept_X`;
* `HTN.ToAc.psumNonneg_stepW` — in a proof-step run, `#ask_X` never overtakes `#wait_X` by more
  than the number of locks currently held;

both are additive along an interleaving, and the remaining two inequalities come from the
semaphore alternation lemma `HTN.ActionModel.Semaphore.countP_prefix_add_ind`.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### The synchronisation actions and the weights -/

/-- Is the action one of the synchronisation actions (`lock`, `unlock` or a handshake)? -/
def isSync : AcAct F A C → Bool
  | .lock => true
  | .unlock => true
  | .ask _ => true
  | .accept _ => true
  | .doneA _ => true
  | .waitA _ => true
  | _ => false

lemma handshakePred_isSync : HandshakePred (isSync : AcAct F A C → Bool) := by
  constructor <;> intros <;> simp [isSync]

/-- The weight measuring how many memory cells are between their `accept_X` and their
`done_X`. -/
def cellW (x : RW) : AcAct F A C → ℤ := fun a =>
  (if isAccept x a then (1 : ℤ) else 0) - (if isDone x a then (1 : ℤ) else 0)

/-- The weight measuring the number of locks held minus the number of open requests. -/
def stepW (x : RW) : AcAct F A C → ℤ := fun a =>
  ((if isLock a then (1 : ℤ) else 0) - (if isUnlock a then (1 : ℤ) else 0)) +
    ((if isWait x a then (1 : ℤ) else 0) - (if isAsk x a then (1 : ℤ) else 0))

lemma wsum_cellW (x : RW) (l : List (AcAct F A C)) :
    wsum (cellW x) l = (l.countP (isAccept x) : ℤ) - (l.countP (isDone x) : ℤ) :=
  sum_map_eq_countP_sub (fun _ => rfl) l

lemma wsum_stepW (x : RW) (l : List (AcAct F A C)) :
    wsum (stepW x) l =
      ((l.countP isLock : ℤ) - (l.countP isUnlock : ℤ)) +
        ((l.countP (isWait x) : ℤ) - (l.countP (isAsk x) : ℤ)) := by
  rw [show (stepW x : AcAct F A C → ℤ) =
      fun a => ((if isLock a then (1 : ℤ) else 0) - (if isUnlock a then (1 : ℤ) else 0)) +
        ((if isWait x a then (1 : ℤ) else 0) - (if isAsk x a then (1 : ℤ) else 0)) from rfl,
    wsum_add, sum_map_eq_countP_sub (fun _ => rfl) l, sum_map_eq_countP_sub (fun _ => rfl) l]

lemma cellW_eq_zero_of_not_isSync {x : RW} {a : AcAct F A C} (h : ¬ isSync a) : cellW x a = 0 := by
  cases a <;> simp_all [isSync, cellW, isAccept, isDone]

lemma stepW_eq_zero_of_not_isSync {x : RW} {a : AcAct F A C} (h : ¬ isSync a) : stepW x a = 0 := by
  cases a <;> simp_all [isSync, stepW, isLock, isUnlock, isAsk, isWait]

/-- An action sequence without synchronisation actions has weight `0` everywhere. -/
lemma weights_zero_of_countP_isSync {w : AcAct F A C → ℤ}
    (hw : ∀ a : AcAct F A C, ¬ isSync a → w a = 0) {l : List (AcAct F A C)}
    (h : l.countP isSync = 0) : ∀ a ∈ l, w a = 0 := by
  intro a ha
  exact hw a (by simpa using (List.countP_eq_zero.1 h) a ha)

/-! ### A memory cell: `done_X` never overtakes `accept_X` -/

lemma testsOf_isSync_false {i : Fin 5} {S : Set F} {vs : List F} {a : AcAct F A C}
    (ha : a ∈ testsOf (A := A) (C := C) i S vs) : ¬ isSync a := by
  classical
  simp only [testsOf, List.mem_reverse, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  unfold testAct
  split <;> simp [isSync]

lemma writesOf_isSync_false {j : Fin 5} {S : Set F} {vs : List F} {a : AcAct F A C}
    (ha : a ∈ writesOf (A := A) (C := C) j S vs) : ¬ isSync a := by
  classical
  simp only [writesOf, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  unfold writeAct
  split <;> simp [isSync]

/-- In the write phase of a memory cell, `done_W` does not overtake `accept_W`, and the phase
contains no read handshake at all. -/
lemma psumGe_cellW_memWrite (x : RW) (S S' : Set F) (t : A ⊕ C) :
    PSumNonneg (cellW x) (memWrite (A := A) (C := C) S S' t vars) := by
  classical
  rcases x with _ | _
  · -- the read channel: the write phase contains no read handshake
    refine psumNonneg_of_weights_zero (fun a ha => ?_)
    simp only [memWrite, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha
    · simp [cellW, isAccept, isDone]
    rcases ha with ha | ha
    · rcases ha with ha | ha
      · exact cellW_eq_zero_of_not_isSync (testsOf_isSync_false ha)
      · exact cellW_eq_zero_of_not_isSync (testsOf_isSync_false ha)
    · rcases ha with rfl | ha
      · simp [cellW, isAccept, isDone]
      · rcases ha with rfl | ha
        · simp [cellW, isAccept, isDone]
        · simp at ha
  · -- the write channel: `accept_W` first, `done_W` last
    refine PSumGe.cons le_rfl ?_
    have hacc : cellW RW.write (AcAct.accept RW.write : AcAct F A C) = 1 := by
      simp [cellW, isAccept, isDone]
    rw [hacc]
    refine PSumGe.append_zero (l₁ := testsOf 0 S vars ++ testsOf 2 S' vars) (fun a ha => ?_) ?_
    · rcases List.mem_append.1 ha with ha | ha
      · exact cellW_eq_zero_of_not_isSync (testsOf_isSync_false ha)
      · exact cellW_eq_zero_of_not_isSync (testsOf_isSync_false ha)
    · refine PSumGe.cons (by norm_num) ?_
      have hpre : cellW RW.write (AcAct.preC t : AcAct F A C) = 0 := by
        simp [cellW, isAccept, isDone]
      rw [hpre]
      refine PSumGe.cons (by norm_num) ?_
      have hdone : cellW RW.write (AcAct.doneA RW.write : AcAct F A C) = -1 := by
        simp [cellW, isAccept, isDone]
      rw [hdone]
      exact PSumGe.nil (by norm_num)

/-- In the read phase of a memory cell, `done_R` does not overtake `accept_R`, and the phase
contains no write handshake at all. -/
lemma psumGe_cellW_memRead (x : RW) (S S' : Set F) (t : A ⊕ C) :
    PSumNonneg (cellW x) (memRead (A := A) (C := C) S S' t vars) := by
  classical
  rcases x with _ | _
  · -- the read channel: `accept_R` first, `done_R` last
    refine PSumGe.cons le_rfl ?_
    have hacc : cellW RW.read (AcAct.accept RW.read : AcAct F A C) = 1 := by
      simp [cellW, isAccept, isDone]
    rw [hacc]
    refine PSumGe.cons (by norm_num) ?_
    have hsetC : cellW RW.read (AcAct.setC t : AcAct F A C) = 0 := by
      simp [cellW, isAccept, isDone]
    rw [hsetC]
    refine PSumGe.append_zero (l₁ := writesOf 4 S' vars ++ writesOf 3 S vars) (fun a ha => ?_) ?_
    · rcases List.mem_append.1 ha with ha | ha
      · exact cellW_eq_zero_of_not_isSync (writesOf_isSync_false ha)
      · exact cellW_eq_zero_of_not_isSync (writesOf_isSync_false ha)
    · refine PSumGe.cons (by norm_num) ?_
      have hdone : cellW RW.read (AcAct.doneA RW.read : AcAct F A C) = -1 := by
        simp [cellW, isAccept, isDone]
      rw [hdone]
      exact PSumGe.nil (by norm_num)
  · -- the write channel: the read phase contains no write handshake
    refine psumNonneg_of_weights_zero (fun a ha => ?_)
    simp only [memRead, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha
    · simp [cellW, isAccept, isDone]
    rcases ha with rfl | ha
    · simp [cellW, isAccept, isDone]
    rcases ha with ha | ha
    · rcases ha with ha | ha
      · exact cellW_eq_zero_of_not_isSync (writesOf_isSync_false ha)
      · exact cellW_eq_zero_of_not_isSync (writesOf_isSync_false ha)
    · rcases ha with rfl | ha
      · simp [cellW, isAccept, isDone]
      · simp at ha

/-- **In a memory cell, `done_X` never overtakes `accept_X`.** -/
theorem psumNonneg_cellW (hnd : vars.Nodup) (x : RW) {γ : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] γ) :
    PSumNonneg (cellW x) γ := by
  obtain ⟨S, S', t, rfl⟩ := yieldSeq_MEM_phases (D := D) (bound := bound) hnd h
  exact PSumNonneg.append (psumGe_cellW_memWrite x S S' t) (psumGe_cellW_memRead x S S' t)

/-! ### A proof step: an open request means a held lock -/

/-- The refinements of the guessing and comparing gadgets contain no synchronisation action. -/
lemma weights_zero_of_yieldSeq_SEL {w : AcAct F A C → ℤ}
    (hw : ∀ a : AcAct F A C, ¬ isSync a → w a = 0) {i : Fin 5} {l : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL i)] l) : ∀ a ∈ l, w a = 0 :=
  weights_zero_of_countP_isSync hw (countP_yieldSeq_SEL handshakePred_isSync h)

/-- The refinements of the guessing and comparing gadgets contain no synchronisation action. -/
lemma weights_zero_of_yieldSeq_EQ {w : AcAct F A C → ℤ}
    (hw : ∀ a : AcAct F A C, ¬ isSync a → w a = 0) {i j : Fin 5} {l : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ i j)] l) : ∀ a ∈ l, w a = 0 :=
  weights_zero_of_countP_isSync hw (countP_yieldSeq_EQ handshakePred_isSync h)

/-- The write requests of a proof step: each of them is closed immediately. -/
lemma psumGe_stepW_writes (x : RW) :
    ∀ w : ℕ, PSumGe (stepW x) (-1)
      (List.flatten
        (List.replicate w ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C)))) := by
  intro w
  induction w with
  | zero => exact PSumGe.nil (by norm_num)
  | succ w ih =>
      rw [List.replicate_succ, List.flatten_cons]
      simp only [List.cons_append, List.nil_append]
      refine PSumGe.cons (by norm_num) ?_
      rcases x with _ | _
      · have h1 : stepW RW.read (AcAct.ask RW.write : AcAct F A C) = 0 := by
          simp [stepW, isLock, isUnlock, isAsk, isWait]
        rw [h1]
        refine PSumGe.cons (by norm_num) ?_
        have h2 : stepW RW.read (AcAct.waitA RW.write : AcAct F A C) = 0 := by
          simp [stepW, isLock, isUnlock, isAsk, isWait]
        rw [h2]
        exact ih.mono (by norm_num)
      · have h1 : stepW RW.write (AcAct.ask RW.write : AcAct F A C) = -1 := by
          simp [stepW, isLock, isUnlock, isAsk, isWait]
        rw [h1]
        refine PSumGe.cons (by norm_num) ?_
        have h2 : stepW RW.write (AcAct.waitA RW.write : AcAct F A C) = 1 := by
          simp [stepW, isLock, isUnlock, isAsk, isWait]
        rw [h2]
        exact ih.mono (by norm_num)

/-- A proof step's write requests do not change the balance. -/
lemma wsum_stepW_writes (x : RW) :
    ∀ w : ℕ, wsum (stepW x)
      (List.flatten
        (List.replicate w ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))))
      = 0 := by
  intro w
  induction w with
  | zero => simp
  | succ w ih =>
      rw [List.replicate_succ, List.flatten_cons]
      simp only [List.cons_append, List.nil_append, wsum_cons, ih]
      rcases x with _ | _ <;> simp [stepW, isLock, isUnlock, isAsk, isWait]

/-- A handshake pair `ask_Y ; wait_Y` inside a proof step keeps the balance. -/
lemma psumGe_stepW_pair (x y : RW) {c : ℤ} {l : List (AcAct F A C)} (hc : c ≤ -1)
    (h : PSumGe (stepW x) c l) :
    PSumGe (stepW x) c (AcAct.ask y :: AcAct.waitA y :: l) := by
  have hge : -1 ≤ stepW x (AcAct.ask y : AcAct F A C) := by
    rcases x with _ | _ <;> rcases y with _ | _ <;>
      simp [stepW, isLock, isUnlock, isAsk, isWait]
  have hsum : stepW x (AcAct.ask y : AcAct F A C) + stepW x (AcAct.waitA y : AcAct F A C) = 0 := by
    rcases x with _ | _ <;> rcases y with _ | _ <;>
      simp [stepW, isLock, isUnlock, isAsk, isWait]
  refine PSumGe.cons (by omega) ?_
  refine PSumGe.cons (by omega) ?_
  have hc' : c - stepW x (AcAct.ask y : AcAct F A C) - stepW x (AcAct.waitA y : AcAct F A C)
      = c := by omega
  rw [hc']
  exact h

/-- **In a proof step, an open request means that the lock is held.**  Every prefix of a proof
step satisfies `#ask_X - #wait_X ≤ #lock - #unlock`. -/
theorem psumNonneg_stepW (x : RW) {σ : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] σ) :
    PSumNonneg (stepW x) σ := by
  have hz : ∀ a : AcAct F A C, ¬ isSync a → stepW x a = 0 :=
    fun a ha => stepW_eq_zero_of_not_isSync ha
  have hlock : stepW x (AcAct.lock : AcAct F A C) = 1 := by
    rcases x with _ | _ <;> simp [stepW, isLock, isUnlock, isAsk, isWait]
  have hunlock : stepW x (AcAct.unlock : AcAct F A C) = -1 := by
    rcases x with _ | _ <;> simp [stepW, isLock, isUnlock, isAsk, isWait]
  have hpreC : ∀ t : A ⊕ C, stepW x (AcAct.preC t : AcAct F A C) = 0 :=
    fun t => hz _ (by simp [isSync])
  have hsetC : ∀ t : A ⊕ C, stepW x (AcAct.setC t : AcAct F A C) = 0 :=
    fun t => hz _ (by simp [isSync])
  have hop2 : ∀ o : A, stepW x (AcAct.op2 o : AcAct F A C) = 0 :=
    fun o => hz _ (by simp [isSync])
  have htail' : ∀ w : ℕ, PSumGe (stepW x) (-1)
      (List.flatten
          (List.replicate w ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C)))
        ++ [AcAct.unlock]) := by
    intro w
    refine PSumGe.append (psumGe_stepW_writes x w) ?_
    rw [wsum_stepW_writes x w]
    refine PSumGe.cons (by norm_num) ?_
    rw [hunlock]
    exact PSumGe.nil (by norm_num)
  rcases yieldSeq_TUPLE_shape h with
    ⟨c, u, v, g₁, g₂, g₃, e₁, e₂, e₃, e₄, w, -, -, hg₁, hg₂, hg₃, he₁, he₂, he₃, he₄, rfl⟩ |
    ⟨o, g₁, g₂, g₃, e₁, e₂, w, -, hg₁, hg₂, hg₃, he₁, he₂, rfl⟩
  · simp only [tupleCompoundSeq, List.append_assoc, List.cons_append, List.nil_append]
    refine PSumGe.cons le_rfl ?_
    rw [hlock]
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_SEL hz hg₁) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_SEL hz hg₂) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_SEL hz hg₃) ?_
    refine psumGe_stepW_pair x RW.read (by norm_num) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_EQ hz he₁) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_EQ hz he₂) ?_
    refine PSumGe.cons (by norm_num) ?_
    rw [hpreC]
    refine psumGe_stepW_pair x RW.read (by norm_num) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_EQ hz he₃) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_EQ hz he₄) ?_
    refine PSumGe.cons (by norm_num) ?_
    rw [hpreC]
    refine PSumGe.cons (by norm_num) ?_
    rw [hsetC]
    exact (htail' w).mono (by norm_num)
  · simp only [tuplePrimitiveSeq, List.append_assoc, List.cons_append, List.nil_append]
    refine PSumGe.cons le_rfl ?_
    rw [hlock]
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_SEL hz hg₁) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_SEL hz hg₂) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_SEL hz hg₃) ?_
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_EQ hz he₁) ?_
    refine PSumGe.cons (by norm_num) ?_
    rw [hop2]
    refine PSumGe.append_zero (weights_zero_of_yieldSeq_EQ hz he₂) ?_
    refine PSumGe.cons (by norm_num) ?_
    rw [hsetC]
    exact (htail' w).mono (by norm_num)

/-! ### The two families of runs do not see each other's weights -/

/-- An action sequence without `accept_X` and `done_X` has `cellW`-weight `0` everywhere. -/
lemma cellW_zero_of_countP {x : RW} {l : List (AcAct F A C)}
    (h₁ : l.countP (isAccept x) = 0) (h₂ : l.countP (isDone x) = 0) :
    ∀ a ∈ l, cellW x a = 0 := by
  intro a ha
  have ha₁ : ¬ isAccept x a := by simpa using (List.countP_eq_zero.1 h₁) a ha
  have ha₂ : ¬ isDone x a := by simpa using (List.countP_eq_zero.1 h₂) a ha
  simp [cellW, ha₁, ha₂]

/-- An action sequence without `lock`, `unlock`, `ask_X` and `wait_X` has `stepW`-weight `0`
everywhere. -/
lemma stepW_zero_of_countP {x : RW} {l : List (AcAct F A C)}
    (h₁ : l.countP isLock = 0) (h₂ : l.countP isUnlock = 0)
    (h₃ : l.countP (isAsk x) = 0) (h₄ : l.countP (isWait x) = 0) :
    ∀ a ∈ l, stepW x a = 0 := by
  intro a ha
  have ha₁ : ¬ isLock a := by simpa using (List.countP_eq_zero.1 h₁) a ha
  have ha₂ : ¬ isUnlock a := by simpa using (List.countP_eq_zero.1 h₂) a ha
  have ha₃ : ¬ isAsk x a := by simpa using (List.countP_eq_zero.1 h₃) a ha
  have ha₄ : ¬ isWait x a := by simpa using (List.countP_eq_zero.1 h₄) a ha
  simp [stepW, ha₁, ha₂, ha₃, ha₄]

/-- A proof step contains no `accept_X` and no `done_X`. -/
lemma psumNonneg_cellW_TUPLE (x : RW) {σ : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] σ) :
    PSumNonneg (cellW x) σ := by
  obtain ⟨r, w, -, -, -, e⟩ := countP_yieldSeq_TUPLE h
  refine psumNonneg_of_weights_zero (cellW_zero_of_countP ?_ ?_)
  · rw [e _ (handshakePred_isAccept x)]; rcases x with _ | _ <;> simp [isAccept]
  · rw [e _ (handshakePred_isDone x)]; rcases x with _ | _ <;> simp [isDone]

/-- A memory cell contains no `lock`, `unlock`, `ask_X` or `wait_X`. -/
lemma psumNonneg_stepW_MEM (x : RW) {γ : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] γ) :
    PSumNonneg (stepW x) γ := by
  refine psumNonneg_of_weights_zero (stepW_zero_of_countP ?_ ?_ ?_ ?_)
  · rw [countP_yieldSeq_MEM handshakePred_isLock h]; simp [isLock]
  · rw [countP_yieldSeq_MEM handshakePred_isUnlock h]; simp [isUnlock]
  · rw [countP_yieldSeq_MEM (handshakePred_isAsk x) h]; rcases x with _ | _ <;> simp [isAsk]
  · rw [countP_yieldSeq_MEM (handshakePred_isWait x) h]; rcases x with _ | _ <;> simp [isWait]

/-! ### The lock-step theorem -/

section Instance

variable {Q : Instance F A C I} {tI0 : C}

/-- **The four actions of a handshake run in lock-step**, for a plan given as an interleaving of
a list of memory-cell runs with a list of proof-step runs. -/
theorem handshake_lockstep' (hnd : vars.Nodup) (x : RW)
    {γs σs : List (List (AcAct F A C))} {as as₁ as₂ p q : List (AcAct F A C)}
    (hγ : ∀ γ ∈ γs, (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] γ)
    (hσ : ∀ σ ∈ σs, (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] σ)
    (hcells : InterleaveList γs as₁) (hsteps : InterleaveList σs as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hpq : as = p ++ q) :
    p.countP (isWait x) ≤ p.countP (isDone x) ∧
      p.countP (isDone x) ≤ p.countP (isAccept x) ∧
      p.countP (isAccept x) ≤ p.countP (isAsk x) ∧
      p.countP (isAsk x) ≤ p.countP (isWait x) + 1 := by
  subst hpq
  have happp : (problem D Q vars bound tI0).SeqApplicable p (problem D Q vars bound tI0).init :=
    ((ActionModel.seqApplicable_append _ p q _).1 happ).1
  have hprefix : p <+: p ++ q := ⟨q, rfl⟩
  -- the two semaphore bounds
  have hsem₂ : p.countP (isWait x) ≤ p.countP (isDone x) :=
    countP_wait_le_countP_done (D' := D) (Q := Q) (tI0 := tI0) x happp
  have hsem₁ : p.countP (isAccept x) ≤ p.countP (isAsk x) :=
    countP_accept_le_countP_ask (D' := D) (Q := Q) (tI0 := tI0) x happp
  have hlock : p.countP isLock ≤ p.countP isUnlock + 1 :=
    countP_lock_le_countP_unlock_succ (D' := D) (Q := Q) (tI0 := tI0) happp
  -- `done_X` never overtakes `accept_X`
  have hcell : PSumNonneg (cellW x) (p ++ q) :=
    hint.psumNonneg (hcells.psumNonneg fun l hl => psumNonneg_cellW hnd x (hγ l hl))
      (hsteps.psumNonneg fun l hl => psumNonneg_cellW_TUPLE x (hσ l hl))
  -- an open request means a held lock
  have hstep : PSumNonneg (stepW x) (p ++ q) :=
    hint.psumNonneg (hcells.psumNonneg fun l hl => psumNonneg_stepW_MEM x (hγ l hl))
      (hsteps.psumNonneg fun l hl => psumNonneg_stepW x (hσ l hl))
  have hc := hcell p hprefix
  have hs := hstep p hprefix
  rw [wsum_cellW] at hc
  rw [wsum_stepW] at hs
  refine ⟨hsem₂, ?_, hsem₁, ?_⟩ <;> omega

/-- **The four actions of a handshake run in lock-step.**  At every point of an executable plan
of the compiled problem,
`#wait_X ≤ #done_X ≤ #accept_X ≤ #ask_X ≤ #wait_X + 1`. -/
theorem handshake_lockstep (hnd : vars.Nodup) (x : RW) {m₁ m₂ : ℕ}
    {as as₁ as₂ p q : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁)
    (htup : (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hpq : as = p ++ q) :
    p.countP (isWait x) ≤ p.countP (isDone x) ∧
      p.countP (isDone x) ≤ p.countP (isAccept x) ∧
      p.countP (isAccept x) ≤ p.countP (isAsk x) ∧
      p.countP (isAsk x) ≤ p.countP (isWait x) + 1 := by
  obtain ⟨γs, -, hallγ, hILγ⟩ :=
    exists_interleaveList_of_gridYield_replicate (D := D) isSeqTask_MEM m₁ hmem
  obtain ⟨σs, -, hallσ, hILσ⟩ :=
    exists_interleaveList_of_gridYield_replicate (D := D) isSeqTask_TUPLE m₂ htup
  exact handshake_lockstep' (Q := Q) (tI0 := tI0) hnd x hallγ hallσ hILγ hILσ hint happ hpq

/-- **When an answer is pending, all four handshake counters agree.**  If at some point of an
executable plan a memory cell has signalled `done_X` that has not been consumed by a `wait_X`,
then at that point there is no open request and no memory cell is between its `accept_X` and its
`done_X`: the cell that answered is the only one that moved, and it has finished its phase. -/
theorem handshake_all_eq_of_done_pending (hnd : vars.Nodup) (x : RW) {m₁ m₂ : ℕ}
    {as as₁ as₂ p q : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁)
    (htup : (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hpq : as = p ++ q)
    (hpending : p.countP (isDone x) = p.countP (isWait x) + 1) :
    p.countP (isAsk x) = p.countP (isWait x) + 1 ∧
      p.countP (isAccept x) = p.countP (isWait x) + 1 ∧
      p.countP (isDone x) = p.countP (isWait x) + 1 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    handshake_lockstep (Q := Q) (tI0 := tI0) hnd x hmem htup hint happ hpq
  exact ⟨by omega, by omega, hpending⟩

/-- **At most one memory cell is in a phase at a time.**  Let a plan be an interleaving of the
runs `γs` of its memory cells with the runs `σs` of its proof steps, and let `p` be a point of
its execution.  Then `p` decomposes into prefixes `ps` of the cell runs and prefixes of the
proof steps, and at most one of the cells has accepted the handshake `X` without having
signalled `done_X` yet: the phases of the memory cells do not overlap.  (Together with
`HTN.ToAc.at_most_one_tuple_in_progress` this says that a plan is a strictly serial execution:
one proof step at a time and, inside it, one memory-cell phase at a time.) -/
theorem at_most_one_cell_in_phase (hnd : vars.Nodup) (x : RW)
    {γs σs : List (List (AcAct F A C))} {as as₁ as₂ p : List (AcAct F A C)}
    (hγ : ∀ γ ∈ γs, (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] γ)
    (hσ : ∀ σ ∈ σs, (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] σ)
    (hcells : InterleaveList γs as₁) (hsteps : InterleaveList σs as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hp : p <+: as) :
    ∃ (ps qs : List (List (AcAct F A C))) (p₁ p₂ : List (AcAct F A C)),
      Interleave p₁ p₂ p ∧ InterleaveList ps p₁ ∧ InterleaveList qs p₂ ∧
      List.Forall₂ (· <+: ·) ps γs ∧ List.Forall₂ (· <+: ·) qs σs ∧
      (ps.filter (fun r => decide (r.countP (isDone x) < r.countP (isAccept x)))).length ≤ 1 := by
  classical
  obtain ⟨p₁, p₂, hp₁, hp₂, hintp⟩ := hint.exists_prefix hp
  obtain ⟨ps, hps, hallp⟩ := hcells.exists_prefix hp₁
  obtain ⟨qs, hqs, hallq⟩ := hsteps.exists_prefix hp₂
  refine ⟨ps, qs, p₁, p₂, hintp, hps, hqs, hallp, hallq, ?_⟩
  obtain ⟨r, hr⟩ := hp
  -- the lock-step bound at the point `p`
  obtain ⟨hwait, hdone, haccept, hask⟩ :=
    handshake_lockstep' (Q := Q) (tI0 := tI0) hnd x hγ hσ hcells hsteps hint happ hr.symm
  have hbal : p.countP (isAccept x) ≤ p.countP (isDone x) + 1 := by omega
  -- in every cell, `done_X` never overtakes `accept_X`
  have hmono : ∀ t ∈ ps, t.countP (isDone x) ≤ t.countP (isAccept x) := by
    refine forall_mem_of_forall₂_prefix hallp (fun l hl t ht => ?_)
    have h0 := ((psumNonneg_cellW hnd x (hγ l hl)).of_prefix ht).total
    rw [wsum_cellW] at h0
    omega
  have hkey : (ps.filter (fun t => decide (t.countP (isDone x) < t.countP (isAccept x)))).length +
      (ps.map (fun l => l.countP (isDone x))).sum ≤
      (ps.map (fun l => l.countP (isAccept x))).sum :=
    length_filter_add_sum_le (fun t : List (AcAct F A C) => t.countP (isAccept x))
      (fun t : List (AcAct F A C) => t.countP (isDone x)) ps hmono
  -- the proof steps contribute no `accept_X` and no `done_X`
  have hstep0 : ∀ t ∈ qs, t.countP (isAccept x) = 0 ∧ t.countP (isDone x) = 0 := by
    refine forall_mem_of_forall₂_prefix hallq (fun l hl t ht => ?_)
    obtain ⟨r₀, w₀, -, -, -, e⟩ := countP_yieldSeq_TUPLE (hσ l hl)
    have h₁ : l.countP (isAccept x) = 0 := by
      rw [e _ (handshakePred_isAccept x)]; rcases x with _ | _ <;> simp [isAccept]
    have h₂ : l.countP (isDone x) = 0 := by
      rw [e _ (handshakePred_isDone x)]; rcases x with _ | _ <;> simp [isDone]
    have c₁ : t.countP (isAccept x) ≤ l.countP (isAccept x) := (ht.sublist).countP_le
    have c₂ : t.countP (isDone x) ≤ l.countP (isDone x) := (ht.sublist).countP_le
    omega
  have hsum₁ : (qs.map (fun l => l.countP (isAccept x))).sum = 0 :=
    List.sum_eq_zero (by
      intro n hn
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hn
      exact (hstep0 l hl).1)
  have hsum₂ : (qs.map (fun l => l.countP (isDone x))).sum = 0 :=
    List.sum_eq_zero (by
      intro n hn
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hn
      exact (hstep0 l hl).2)
  have hacc : p.countP (isAccept x) = (ps.map (fun l => l.countP (isAccept x))).sum := by
    rw [hintp.countP, hps.countP, hqs.countP, hsum₁, Nat.add_zero]
  have hdn : p.countP (isDone x) = (ps.map (fun l => l.countP (isDone x))).sum := by
    rw [hintp.countP, hps.countP, hqs.countP, hsum₂, Nat.add_zero]
  omega

/-! ### Where the memory cells stand when an answer is pending -/

/-- A pointwise bound gives a bound on the sums. -/
lemma sum_map_le_sum_map {β : Type*} (f g : β → ℕ) :
    ∀ l : List β, (∀ y ∈ l, g y ≤ f y) → (l.map g).sum ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons y l ih =>
      intro h
      have h₁ := h y (by simp)
      have h₂ := ih (fun u hu => h u (by simp [hu]))
      simp only [List.map_cons, List.sum_cons]
      omega

/-- If a sum is bounded by a pointwise smaller sum, the two are equal pointwise. -/
lemma eq_of_sum_le_sum {β : Type*} (f g : β → ℕ) :
    ∀ l : List β, (∀ y ∈ l, g y ≤ f y) → (l.map f).sum ≤ (l.map g).sum →
      ∀ y ∈ l, f y = g y := by
  intro l
  induction l with
  | nil => intro _ _ y hy; simp at hy
  | cons y l ih =>
      intro hle hsum z hz
      have hrest : (l.map g).sum ≤ (l.map f).sum :=
        sum_map_le_sum_map f g l (fun u hu => hle u (by simp [hu]))
      have hy := hle y (by simp)
      simp only [List.map_cons, List.sum_cons] at hsum
      rcases List.mem_cons.1 hz with rfl | hz
      · omega
      · exact ih (fun u hu => hle u (by simp [hu])) (by omega) z hz

/-- **When an answer is pending, no memory cell is in the middle of a phase.**  At a point of an
executable plan at which a memory cell has signalled `done_R` that the asking proof step has not
yet consumed, every memory cell has either not yet accepted the read handshake — so it has at
most latched its triple — or has finished its whole run. -/
theorem cells_settled_of_done_read_pending (hnd : vars.Nodup)
    {γs σs : List (List (AcAct F A C))} {as as₁ as₂ p : List (AcAct F A C)}
    (hγ : ∀ γ ∈ γs, (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] γ)
    (hσ : ∀ σ ∈ σs, (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] σ)
    (hcells : InterleaveList γs as₁) (hsteps : InterleaveList σs as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hp : p <+: as)
    (hpending : p.countP (isDone RW.read) = p.countP (isWait RW.read) + 1) :
    ∃ (ps qs : List (List (AcAct F A C))) (p₁ p₂ : List (AcAct F A C)),
      Interleave p₁ p₂ p ∧ InterleaveList ps p₁ ∧ InterleaveList qs p₂ ∧
      List.Forall₂ (· <+: ·) qs σs ∧
      List.Forall₂ (fun u γ => ∃ (S S' : Set F) (t : A ⊕ C),
        γ = memWrite S S' t vars ++ memRead S S' t vars ∧
          (u <+: memWrite S S' t vars ∨ u = γ)) ps γs := by
  classical
  obtain ⟨p₁, p₂, hp₁, hp₂, hintp⟩ := hint.exists_prefix hp
  obtain ⟨ps, hps, hallp⟩ := hcells.exists_prefix hp₁
  obtain ⟨qs, hqs, hallq⟩ := hsteps.exists_prefix hp₂
  refine ⟨ps, qs, p₁, p₂, hintp, hps, hqs, hallq, ?_⟩
  obtain ⟨rest, hrest⟩ := hp
  -- at this point the numbers of `accept_R` and of `done_R` agree
  obtain ⟨-, hacc, -⟩ :=
    (by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := handshake_lockstep' (Q := Q) (tI0 := tI0) hnd RW.read hγ hσ
        hcells hsteps hint happ hrest.symm
      exact ⟨by omega, by omega, hpending⟩ :
      p.countP (isAsk RW.read) = p.countP (isWait RW.read) + 1 ∧
        p.countP (isAccept RW.read) = p.countP (isWait RW.read) + 1 ∧
        p.countP (isDone RW.read) = p.countP (isWait RW.read) + 1)
  have hpeq : p.countP (isAccept RW.read) = p.countP (isDone RW.read) := by omega
  -- the proof steps contribute no `accept_R` and no `done_R`
  have hstep0 : ∀ u ∈ qs, u.countP (isAccept RW.read) = 0 ∧ u.countP (isDone RW.read) = 0 := by
    refine forall_mem_of_forall₂_prefix hallq (fun l hl u hu => ?_)
    obtain ⟨r₀, w₀, -, -, -, e⟩ := countP_yieldSeq_TUPLE (hσ l hl)
    have h₁ : l.countP (isAccept RW.read) = 0 := by
      rw [e _ (handshakePred_isAccept RW.read)]; simp [isAccept]
    have h₂ : l.countP (isDone RW.read) = 0 := by
      rw [e _ (handshakePred_isDone RW.read)]; simp [isDone]
    have c₁ : u.countP (isAccept RW.read) ≤ l.countP (isAccept RW.read) := (hu.sublist).countP_le
    have c₂ : u.countP (isDone RW.read) ≤ l.countP (isDone RW.read) := (hu.sublist).countP_le
    omega
  have hsum₁ : (qs.map (fun l => l.countP (isAccept RW.read))).sum = 0 :=
    List.sum_eq_zero (by
      intro n hn
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hn
      exact (hstep0 l hl).1)
  have hsum₂ : (qs.map (fun l => l.countP (isDone RW.read))).sum = 0 :=
    List.sum_eq_zero (by
      intro n hn
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hn
      exact (hstep0 l hl).2)
  have hacc' : p.countP (isAccept RW.read) = (ps.map (fun l => l.countP (isAccept RW.read))).sum := by
    rw [hintp.countP, hps.countP, hqs.countP, hsum₁, Nat.add_zero]
  have hdn' : p.countP (isDone RW.read) = (ps.map (fun l => l.countP (isDone RW.read))).sum := by
    rw [hintp.countP, hps.countP, hqs.countP, hsum₂, Nat.add_zero]
  -- in every cell, `done_R` never overtakes `accept_R`; with equal sums the two agree cellwise
  have hmono : ∀ u ∈ ps, u.countP (isDone RW.read) ≤ u.countP (isAccept RW.read) := by
    refine forall_mem_of_forall₂_prefix hallp (fun l hl u hu => ?_)
    have h0 := ((psumNonneg_cellW hnd RW.read (hγ l hl)).of_prefix hu).total
    rw [wsum_cellW] at h0
    omega
  have hcellwise : ∀ u ∈ ps, u.countP (isAccept RW.read) = u.countP (isDone RW.read) :=
    eq_of_sum_le_sum (fun u : List (AcAct F A C) => u.countP (isAccept RW.read))
      (fun u : List (AcAct F A C) => u.countP (isDone RW.read)) ps hmono (by omega)
  -- and then the classification of the cell prefixes applies
  have hfinal : ∀ {us gs : List (List (AcAct F A C))}, List.Forall₂ (· <+: ·) us gs →
      (∀ γ ∈ gs, (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] γ) →
      (∀ u ∈ us, u.countP (isAccept RW.read) = u.countP (isDone RW.read)) →
      List.Forall₂ (fun u γ => ∃ (S S' : Set F) (t : A ⊕ C),
        γ = memWrite S S' t vars ++ memRead S S' t vars ∧
          (u <+: memWrite S S' t vars ∨ u = γ)) us gs := by
    intro us gs h
    induction h with
    | nil => intro _ _; exact List.Forall₂.nil
    | @cons u γ us' gs' hu hall ih =>
        intro hmem hcnt
        have hγ₀ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] γ :=
          hmem γ (by simp)
        obtain ⟨S, S', t, hsplit⟩ := yieldSeq_MEM_phases (D := D) (bound := bound) hnd hγ₀
        subst hsplit
        refine List.Forall₂.cons ⟨S, S', t, rfl, ?_⟩
          (ih (fun γ' hγ' => hmem γ' (by simp [hγ'])) (fun v hv => hcnt v (by simp [hv])))
        have heq := hcnt u (by simp)
        by_cases hz : u.countP (isAccept RW.read) = 0
        · exact Or.inl (cell_prefix_memWrite_of_countP_accept_read hu hz)
        · exact Or.inr (cell_eq_run_of_countP_done_read hu (by omega))
  exact hfinal hallp hγ hcellwise

/-- The lock-step property of a solution plan of the compiled problem. -/
theorem handshake_lockstep_of_isSolutionPlan (hnd : vars.Nodup) (x : RW)
    {as p q : List (AcAct F A C)} (hsol : (problem D Q vars bound tI0).IsSolutionPlan as)
    (hpq : as = p ++ q) :
    p.countP (isWait x) ≤ p.countP (isDone x) ∧
      p.countP (isDone x) ≤ p.countP (isAccept x) ∧
      p.countP (isAccept x) ≤ p.countP (isAsk x) ∧
      p.countP (isAsk x) ≤ p.countP (isWait x) + 1 := by
  obtain ⟨hnet, happ, -⟩ := Problem.isSolutionPlan_iff.1 hsol
  obtain ⟨m₁, m₂, as₁, as₂, -, -, hmem, htup, hint⟩ :=
    (netYield_tnI_iff (Q := Q) (tI0 := tI0)).1 hnet
  exact handshake_lockstep (Q := Q) (tI0 := tI0) hnd x hmem htup hint happ hpq

end Instance

end ToAc

end HTN
