import HtnPlanning.Interleave.SchedPeel
import HtnComplexity.ToHtnAc.ToHtnAcCompoundStep
import HtnComplexity.ToHtnAc.ToHtnAcMutex
import HtnComplexity.ToHtnAc.ToHtnAcLockstep
/-!
# Reading a plan of the compiled problem off its components

This file is the technical core of the **soundness** half of the correctness of the
TO-HTN ⟶ HTN-AC compilation: given a plan of the compiled problem — by
`HTN.ToAc.netYield_tnI_iff` an interleaving of the runs of the memory cells (`MEM`) with the
runs of the proof steps (`TUPLE`) — it shows that the plan has no freedom at all: it is a
concatenation of *blocks*, one per proof step, with the phases of the memory cells the step
talks to spliced into its handshakes.

The argument is entirely local, in terms of the three semaphores:

* `HTN.ToAc.KeysDown` — all semaphores are down.  Then no component can begin an action: a
  memory cell would need `key₁^X` to accept a request, an unstarted proof step would need
  `key₀`, and a proof step waiting for an answer would need `key₂^X`
  (`HTN.ToAc.compInv_stuck`, `HTN.ToAc.stuck_waitA`).
* consequently, while the active component performs actions that raise no semaphore
  (`HTN.ToAc.keySilent`) the plan must follow it action by action
  (`HTN.ToAc.peel_silent_run`, an instance of `HTN.Sched.peel_run`);
* at a handshake the plan must continue with a full phase of one memory cell
  (`HTN.ToAc.peel_readHandshake`, `HTN.ToAc.peel_writeHandshake`).

The state of every component is described by `HTN.ToAc.CompInv`: a memory cell is either
untouched, or has latched a triple — and then, and this is what the whole analysis is for, the
triple it latched is *derivable in the proof-tuple calculus* — or is finished; a proof step is
either untouched or finished.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### Semaphores that are down -/

/-- All three semaphores are down: no component can move except the one that already holds the
lock and is not waiting for an answer. -/
def KeysDown (s : Set (AcFact F A C)) : Prop :=
  AcFact.key0 ∉ s ∧ ∀ x : RW, AcFact.key1 x ∉ s ∧ AcFact.key2 x ∉ s

/-- The lock is taken and no request is open: no memory cell and no unstarted proof step can
move. -/
def NoLockNoAsk (s : Set (AcFact F A C)) : Prop :=
  AcFact.key0 ∉ s ∧ ∀ x : RW, AcFact.key1 x ∉ s

lemma KeysDown.toNoLockNoAsk {s : Set (AcFact F A C)} (h : KeysDown s) : NoLockNoAsk s :=
  ⟨h.1, fun x => (h.2 x).1⟩

/-- An action that raises no semaphore. -/
def keySilent : AcAct F A C → Prop
  | AcAct.unlock => False
  | AcAct.ask _ => False
  | AcAct.doneA _ => False
  | _ => True

lemma keySilent_of_not_isSync {a : AcAct F A C} (h : ¬ isSync a) : keySilent a := by
  cases a <;> simp_all [isSync, keySilent]

lemma keySilent_of_countP_isSync {u : List (AcAct F A C)} (h : u.countP isSync = 0) :
    ∀ a ∈ u, keySilent a := fun a ha =>
  keySilent_of_not_isSync (by simpa using (List.countP_eq_zero.1 h) a ha)

lemma keysDown_transition {a : AcAct F A C} (ha : keySilent a) {s : Set (AcFact F A C)}
    (h : KeysDown s) : KeysDown ((domain D vars bound).transition a s) := by
  obtain ⟨h0, h12⟩ := h
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩ <;>
    · cases a <;>
        simp_all [keySilent, ActionModel.transition, domain, actionModel, ToAc.add, ToAc.del]

lemma noLockNoAsk_transition {a : AcAct F A C} (ha : keySilent a) {s : Set (AcFact F A C)}
    (h : NoLockNoAsk s) : NoLockNoAsk ((domain D vars bound).transition a s) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, fun x => ?_⟩ <;>
    · cases a <;>
        simp_all [keySilent, ActionModel.transition, domain, actionModel, ToAc.add, ToAc.del]

/-- `doneA` raises only `key₂`, so it does not unblock a memory cell or an unstarted step. -/
lemma noLockNoAsk_transition_doneA {x : RW} {s : Set (AcFact F A C)} (h : NoLockNoAsk s) :
    NoLockNoAsk ((domain D vars bound).transition (AcAct.doneA x) s) := by
  obtain ⟨h0, h1⟩ := h
  exact ⟨by simpa using h0, fun y => by simpa using h1 y⟩

/-! ### The state of a component -/

/-- The possible states of a memory cell during a plan: untouched, or *latched* — having read a
triple that, as the analysis shows, is derivable in the proof-tuple calculus. -/
def CellInv (D : Domain F A C I) (vars : List F) (l : List (AcAct F A C)) : Prop :=
  (∃ (S S' : Set F) (t : A ⊕ C), l = memWrite S S' t vars ++ memRead S S' t vars) ∨
    ∃ (S S' : Set F) (t : A ⊕ C), l = memRead S S' t vars ∧ D.Provable S t S'

/-- The possible states of a component of a plan that is not currently running: a memory cell,
an unstarted proof step, or an exhausted component. -/
def CompInv (D : Domain F A C I) (vars : List F) (bound : ℕ) (l : List (AcAct F A C)) : Prop :=
  CellInv D vars l ∨ (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] l ∨ l = []

lemma compInv_nil : CompInv D vars bound ([] : List (AcAct F A C)) := Or.inr (Or.inr rfl)

lemma memWrite_cons (S S' : Set F) (t : A ⊕ C) :
    memWrite S S' t vars = AcAct.accept RW.write ::
      (testsOf 0 S vars ++ testsOf 2 S' vars ++ [AcAct.preC t, AcAct.doneA RW.write]) := rfl

lemma memRead_cons (S S' : Set F) (t : A ⊕ C) :
    memRead S S' t vars = AcAct.accept RW.read ::
      (AcAct.setC t :: (writesOf 4 S' vars ++ writesOf 3 S vars ++ [AcAct.doneA RW.read])) :=
  rfl

/-- **A component that is not running cannot move while the lock is taken and no request is
open.** -/
lemma compInv_stuck {s : Set (AcFact F A C)} (hs : NoLockNoAsk s) {l : List (AcAct F A C)}
    (h : CompInv D vars bound l) :
    Sched.Stuck (domain D vars bound).toActionModel s l := by
  intro b t hl happ
  rcases h with (⟨S, S', t', rfl⟩ | ⟨S, S', t', rfl, -⟩) | hstep | rfl
  · rw [memWrite_cons, List.cons_append] at hl
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
    exact (hs.2 RW.write) (applicable_accept_iff.1 happ)
  · rw [memRead_cons] at hl
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
    exact (hs.2 RW.read) (applicable_accept_iff.1 happ)
  · obtain ⟨t'', rfl⟩ := yieldSeq_TUPLE_head hstep
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
    exact hs.1 (applicable_lock_iff.1 happ)
  · exact absurd hl (by simp)

/-- **A proof step waiting for an answer cannot move while the answer has not been given.** -/
lemma stuck_waitA {s : Set (AcFact F A C)} {x : RW} (hs : AcFact.key2 x ∉ s)
    {t : List (AcAct F A C)} :
    Sched.Stuck (domain D vars bound).toActionModel s (AcAct.waitA x :: t) := by
  intro b t' hl happ
  obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
  exact hs (applicable_waitA_iff.1 happ)

/-- A memory cell waiting for a request cannot move while the request has not been made. -/
lemma stuck_accept {s : Set (AcFact F A C)} {x : RW} (hs : AcFact.key1 x ∉ s)
    {t : List (AcAct F A C)} :
    Sched.Stuck (domain D vars bound).toActionModel s (AcAct.accept x :: t) := by
  intro b t' hl happ
  obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
  exact hs (applicable_accept_iff.1 happ)

/-! ### Peeling a silent run of the active component -/

/-- **While the active component performs actions that raise no semaphore the plan follows
it.** -/
lemma peel_silent_run {u t : List (AcAct F A C)} {rest : List (List (AcAct F A C))}
    {z : List (AcAct F A C)} {s : Set (AcFact F A C)}
    (hu : ∀ a ∈ u, keySilent a)
    (hsched : Sched ((u ++ t) :: rest) z)
    (happ : (domain D vars bound).SeqApplicable z s)
    (hs : NoLockNoAsk s)
    (hrest : ∀ l ∈ rest, CompInv D vars bound l) :
    ∃ z', z = u ++ z' ∧ Sched (t :: rest) z' :=
  Sched.peel_run (Inv := NoLockNoAsk) hsched happ hs
    (fun a ha _ hs' => noLockNoAsk_transition (D := D) (vars := vars) (bound := bound)
      (hu a ha) hs')
    (fun _ hs' l hl => compInv_stuck hs' (hrest l hl))

/-- The same, with a proof step waiting for an answer among the blocked components. -/
lemma peel_silent_run_waiting {u t : List (AcAct F A C)} {rest : List (List (AcAct F A C))}
    {w : List (AcAct F A C)} {z : List (AcAct F A C)} {s : Set (AcFact F A C)}
    (hu : ∀ a ∈ u, keySilent a)
    (hsched : Sched ((u ++ t) :: w :: rest) z)
    (happ : (domain D vars bound).SeqApplicable z s)
    (hs : KeysDown s)
    (hw : ∃ (x : RW) (t' : List (AcAct F A C)), w = AcAct.waitA x :: t')
    (hrest : ∀ l ∈ rest, CompInv D vars bound l) :
    ∃ z', z = u ++ z' ∧ Sched (t :: w :: rest) z' := by
  obtain ⟨x, t', rfl⟩ := hw
  refine Sched.peel_run (Inv := KeysDown) hsched happ hs
    (fun a ha _ hs' => keysDown_transition (D := D) (vars := vars) (bound := bound)
      (hu a ha) hs') (fun s' hs' l hl => ?_)
  rcases List.mem_cons.1 hl with rfl | hl
  · exact stuck_waitA (hs'.2 x).2
  · exact compInv_stuck hs'.toNoLockNoAsk (hrest l hl)

/-! ### Silent segments of a memory phase -/

lemma keySilent_testsOf {i : Fin 5} {S : Set F} {vs : List F} :
    ∀ a ∈ (testsOf i S vs : List (AcAct F A C)), keySilent a := by
  classical
  intro a ha
  rw [testsOf, List.mem_reverse, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  rw [testAct]
  split <;> simp [keySilent]

lemma keySilent_writesOf {j : Fin 5} {S : Set F} {vs : List F} :
    ∀ a ∈ (writesOf j S vs : List (AcAct F A C)), keySilent a := by
  classical
  intro a ha
  rw [writesOf, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  rw [writeAct]
  split <;> simp [keySilent]

lemma keysDown_transitionSeq : ∀ {u : List (AcAct F A C)} {s : Set (AcFact F A C)},
    (∀ a ∈ u, keySilent a) → KeysDown s →
      KeysDown ((domain D vars bound).transitionSeq u s) := by
  intro u
  induction u with
  | nil => intro s _ h; exact h
  | cons a u ih =>
      intro s hu h
      exact ih (fun b hb => hu b (List.mem_cons_of_mem _ hb))
        (keysDown_transition (hu a List.mem_cons_self) h)

/-! ### Peeling a read handshake -/

/-- **A read request is answered by the whole read phase of one memory cell.**  If the active
proof step asks for a memory cell and waits for the answer, the plan continues with the read
phase of a cell that has latched a triple, and that triple is derivable in the proof-tuple
calculus. -/
lemma peel_readHandshake {t : List (AcAct F A C)} {rest : List (List (AcAct F A C))}
    {z : List (AcAct F A C)} {s : Set (AcFact F A C)}
    (hsched : Sched ((AcAct.ask RW.read :: AcAct.waitA RW.read :: t) :: rest) z)
    (happ : (domain D vars bound).SeqApplicable z s)
    (hs : KeysDown s)
    (hrest : ∀ l ∈ rest, CompInv D vars bound l) :
    ∃ (S S' : Set F) (tt : A ⊕ C) (rest' : List (List (AcAct F A C)))
      (z' : List (AcAct F A C)),
      D.Provable S tt S' ∧ z = readPhase S S' tt vars ++ z' ∧
        Sched (t :: rest') z' ∧ (∀ l ∈ rest', CompInv D vars bound l) := by
  classical
  -- the active step opens the request
  obtain ⟨z₁, rfl, hsch₁⟩ :=
    Sched.peel hsched happ (fun l hl => compInv_stuck hs.toNoLockNoAsk (hrest l hl))
  have happ₁ : (domain D vars bound).SeqApplicable z₁
      ((domain D vars bound).transition (AcAct.ask RW.read) s) := happ.2
  set s₁ := (domain D vars bound).transition (AcAct.ask RW.read) s with hs₁def
  have hk0 : (AcFact.key0 : AcFact F A C) ∉ s₁ := by
    simp [hs₁def, mem_transition_ask, hs.1]
  have hk1W : (AcFact.key1 RW.write : AcFact F A C) ∉ s₁ := by
    simp [hs₁def, mem_transition_ask, (hs.2 RW.write).1]
  have hk2 : ∀ x : RW, (AcFact.key2 x : AcFact F A C) ∉ s₁ := by
    intro x; simp [hs₁def, mem_transition_ask, (hs.2 x).2]
  -- which component answers?
  rcases z₁ with _ | ⟨b, z₂⟩
  · exact absurd (hsch₁.forall_nil _ List.mem_cons_self) (by simp)
  obtain ⟨pre, post, t', hls, hsch₂⟩ := hsch₁.exists_of_cons
  have happb : (domain D vars bound).Applicable b s₁ := happ₁.1
  rcases pre with _ | ⟨c, pre₀⟩
  · exfalso
    simp only [List.nil_append, List.cons.injEq] at hls
    obtain ⟨hb, -⟩ := hls.1
    exact hk2 RW.read (applicable_waitA_iff.1 (hb ▸ happb))
  simp only [List.cons_append, List.cons.injEq] at hls
  obtain ⟨rfl, hrest_eq⟩ := hls
  have hmem : (b :: t') ∈ rest := by rw [hrest_eq]; simp
  have hcomp := hrest _ hmem
  -- it must be a memory cell that has latched a triple
  obtain ⟨S, S', tt, hcell, hprov⟩ :
      ∃ (S S' : Set F) (tt : A ⊕ C), b :: t' = memRead S S' tt vars ∧ D.Provable S tt S' := by
    rcases hcomp with (⟨S, S', tt, hl⟩ | ⟨S, S', tt, hl, hp⟩) | hstep | hnil
    · exfalso
      rw [memWrite_cons, List.cons_append] at hl
      obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
      exact hk1W (applicable_accept_iff.1 happb)
    · exact ⟨S, S', tt, hl, hp⟩
    · exfalso
      obtain ⟨t'', hl⟩ := yieldSeq_TUPLE_head hstep
      obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
      exact hk0 (applicable_lock_iff.1 happb)
    · exact absurd hnil (by simp)
  rw [memRead_cons] at hcell
  obtain ⟨rfl, hrfl⟩ := List.cons_eq_cons.1 hcell
  subst hrfl
  subst hrest_eq
  -- bring the answering cell to the front
  have hperm : ((AcAct.waitA RW.read :: t) ::
      (pre₀ ++ (AcAct.setC tt ::
        (writesOf 4 S' vars ++ writesOf 3 S vars ++ [AcAct.doneA RW.read])) :: post)).Perm
      ((AcAct.setC tt :: (writesOf 4 S' vars ++ writesOf 3 S vars ++ [AcAct.doneA RW.read])) ::
        (AcAct.waitA RW.read :: t) :: (pre₀ ++ post)) :=
    (List.perm_middle.cons _).trans (List.Perm.swap _ _ _)
  have hsch₃ := hsch₂.perm hperm
  have happ₂ : (domain D vars bound).SeqApplicable z₂
      ((domain D vars bound).transition (AcAct.accept RW.read) s₁) := happ₁.2
  set s₂ := (domain D vars bound).transition (AcAct.accept RW.read) s₁ with hs₂def
  have hkd₂ : KeysDown s₂ := by
    refine ⟨by simp [hs₂def, mem_transition_accept, hk0], fun x => ⟨?_, ?_⟩⟩
    · rcases x with _ | _
      · simp [hs₂def, mem_transition_accept]
      · simp [hs₂def, mem_transition_accept, hk1W]
    · simp [hs₂def, mem_transition_accept, hk2 x]
  have hrest₀ : ∀ l ∈ pre₀ ++ post, CompInv D vars bound l := by
    intro l hl
    refine hrest l ?_
    rcases List.mem_append.1 hl with h | h
    · exact List.mem_append.2 (Or.inl h)
    · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h))
  -- the cell runs its phase
  have husil : ∀ a ∈ (AcAct.setC tt :: (writesOf 4 S' vars ++ writesOf 3 S vars) :
      List (AcAct F A C)), keySilent a := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [keySilent]
    · rcases List.mem_append.1 ha with h | h
      · exact keySilent_writesOf a h
      · exact keySilent_writesOf a h
  obtain ⟨z₃, rfl, hsch₄⟩ :=
    peel_silent_run_waiting (D := D) (vars := vars) (bound := bound) husil
      (by simpa [List.append_assoc] using hsch₃) happ₂ hkd₂ ⟨RW.read, t, rfl⟩ hrest₀
  set s₃ := (domain D vars bound).transitionSeq
    (AcAct.setC tt :: (writesOf 4 S' vars ++ writesOf 3 S vars)) s₂ with hs₃def
  have happ₃ : (domain D vars bound).SeqApplicable z₃ s₃ := by
    have := (ActionModel.seqApplicable_append (domain D vars bound).toActionModel
      (AcAct.setC tt :: (writesOf 4 S' vars ++ writesOf 3 S vars)) z₃ s₂).1 happ₂
    exact this.2
  have hkd₃ : KeysDown s₃ := keysDown_transitionSeq husil hkd₂
  -- the cell signals
  obtain ⟨z₄, rfl, hsch₅⟩ :=
    Sched.peel hsch₄ happ₃ (fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · exact stuck_waitA (hkd₃.2 RW.read).2
      · exact compInv_stuck hkd₃.toNoLockNoAsk (hrest₀ l hl))
  have happ₄ : (domain D vars bound).SeqApplicable z₄
      ((domain D vars bound).transition (AcAct.doneA RW.read) s₃) := happ₃.2
  set s₄ := (domain D vars bound).transition (AcAct.doneA RW.read) s₃ with hs₄def
  have hnla₄ : NoLockNoAsk s₄ :=
    noLockNoAsk_transition_doneA (D := D) (vars := vars) (bound := bound) hkd₃.toNoLockNoAsk
  -- the active step consumes the answer
  have hperm₂ : (([] : List (AcAct F A C)) :: (AcAct.waitA RW.read :: t) :: (pre₀ ++ post)).Perm
      ((AcAct.waitA RW.read :: t) :: ([] : List (AcAct F A C)) :: (pre₀ ++ post)) :=
    List.Perm.swap _ _ _
  obtain ⟨z₅, rfl, hsch₆⟩ :=
    Sched.peel (hsch₅.perm hperm₂) happ₄ (fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · exact compInv_stuck hnla₄ compInv_nil
      · exact compInv_stuck hnla₄ (hrest₀ l hl))
  refine ⟨S, S', tt, ([] : List (AcAct F A C)) :: (pre₀ ++ post), z₅, hprov, ?_, hsch₆, ?_⟩
  · simp [readPhase, memRead_cons, List.append_assoc]
  · intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact compInv_nil
    · exact hrest₀ l hl

/-! ### Peeling a write handshake -/

/-- The stored task name of a state is exactly `t`. -/
def TaskOnly (t : A ⊕ C) (s : Set (AcFact F A C)) : Prop :=
  ∀ t' : A ⊕ C, AcFact.task t' ∈ s ↔ t' = t

lemma representsOn_transition_ask {x : RW} {i : Fin 5} {S : Set F} {s : Set (AcFact F A C)}
    (h : RepresentsOn s i S vars) :
    RepresentsOn ((domain D vars bound).transition (AcAct.ask x) s) i S vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transition_ask, mem_transition_ask]
  simpa using ⟨h1, h2⟩

lemma taskOnly_transition_ask {x : RW} {t : A ⊕ C} {s : Set (AcFact F A C)} (h : TaskOnly t s) :
    TaskOnly t ((domain D vars bound).transition (AcAct.ask x) s) := by
  intro t'
  rw [mem_transition_ask]
  simpa using h t'

/-- **A write request is answered by the whole write phase of one untouched memory cell**, and
the cell latches exactly the triple that the state holds. -/
lemma peel_writeHandshake (hvars : ∀ v : F, v ∈ vars) {S S' : Set F} {tt : A ⊕ C}
    {t : List (AcAct F A C)} {rest : List (List (AcAct F A C))}
    {z : List (AcAct F A C)} {s : Set (AcFact F A C)}
    (hsched : Sched ((AcAct.ask RW.write :: AcAct.waitA RW.write :: t) :: rest) z)
    (happ : (domain D vars bound).SeqApplicable z s)
    (hs : KeysDown s)
    (hrest : ∀ l ∈ rest, CompInv D vars bound l)
    (hrep0 : RepresentsOn s 0 S vars) (hrep2 : RepresentsOn s 2 S' vars)
    (htask : TaskOnly tt s) (hprov : D.Provable S tt S') :
    ∃ (rest' : List (List (AcAct F A C))) (z' : List (AcAct F A C)),
      z = writePhase S S' tt vars 1 ++ z' ∧
        Sched (t :: rest') z' ∧ (∀ l ∈ rest', CompInv D vars bound l) := by
  classical
  obtain ⟨z₁, rfl, hsch₁⟩ :=
    Sched.peel hsched happ (fun l hl => compInv_stuck hs.toNoLockNoAsk (hrest l hl))
  have happ₁ : (domain D vars bound).SeqApplicable z₁
      ((domain D vars bound).transition (AcAct.ask RW.write) s) := happ.2
  set s₁ := (domain D vars bound).transition (AcAct.ask RW.write) s with hs₁def
  have hk0 : (AcFact.key0 : AcFact F A C) ∉ s₁ := by
    simp [hs₁def, mem_transition_ask, hs.1]
  have hk1R : (AcFact.key1 RW.read : AcFact F A C) ∉ s₁ := by
    simp [hs₁def, mem_transition_ask, (hs.2 RW.read).1]
  have hk2 : ∀ x : RW, (AcFact.key2 x : AcFact F A C) ∉ s₁ := by
    intro x; simp [hs₁def, mem_transition_ask, (hs.2 x).2]
  have hrep0₁ : RepresentsOn s₁ 0 S vars := representsOn_transition_ask hrep0
  have hrep2₁ : RepresentsOn s₁ 2 S' vars := representsOn_transition_ask hrep2
  have htask₁ : TaskOnly tt s₁ := taskOnly_transition_ask htask
  rcases z₁ with _ | ⟨b, z₂⟩
  · exact absurd (hsch₁.forall_nil _ List.mem_cons_self) (by simp)
  obtain ⟨pre, post, t', hls, hsch₂⟩ := hsch₁.exists_of_cons
  have happb : (domain D vars bound).Applicable b s₁ := happ₁.1
  rcases pre with _ | ⟨c, pre₀⟩
  · exfalso
    simp only [List.nil_append, List.cons.injEq] at hls
    obtain ⟨hb, -⟩ := hls.1
    exact hk2 RW.write (applicable_waitA_iff.1 (hb ▸ happb))
  simp only [List.cons_append, List.cons.injEq] at hls
  obtain ⟨rfl, hrest_eq⟩ := hls
  have hmem : (b :: t') ∈ rest := by rw [hrest_eq]; simp
  have hcomp := hrest _ hmem
  -- it must be an untouched memory cell
  obtain ⟨Sa, Sa', ta, hcell⟩ :
      ∃ (Sa Sa' : Set F) (ta : A ⊕ C),
        b :: t' = memWrite Sa Sa' ta vars ++ memRead Sa Sa' ta vars := by
    rcases hcomp with (⟨Sa, Sa', ta, hl⟩ | ⟨Sa, Sa', ta, hl, -⟩) | hstep | hnil
    · exact ⟨Sa, Sa', ta, hl⟩
    · exfalso
      rw [memRead_cons] at hl
      obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
      exact hk1R (applicable_accept_iff.1 happb)
    · exfalso
      obtain ⟨t'', hl⟩ := yieldSeq_TUPLE_head hstep
      obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
      exact hk0 (applicable_lock_iff.1 happb)
    · exact absurd hnil (by simp)
  rw [memWrite_cons, List.cons_append] at hcell
  obtain ⟨rfl, hrfl⟩ := List.cons_eq_cons.1 hcell
  subst hrfl
  subst hrest_eq
  -- bring the answering cell to the front
  have hperm : ((AcAct.waitA RW.write :: t) ::
      (pre₀ ++ ((testsOf 0 Sa vars ++ testsOf 2 Sa' vars ++
        [AcAct.preC ta, AcAct.doneA RW.write]) ++ memRead Sa Sa' ta vars) :: post)).Perm
      (((testsOf 0 Sa vars ++ testsOf 2 Sa' vars ++
        [AcAct.preC ta, AcAct.doneA RW.write]) ++ memRead Sa Sa' ta vars) ::
        (AcAct.waitA RW.write :: t) :: (pre₀ ++ post)) :=
    (List.perm_middle.cons _).trans (List.Perm.swap _ _ _)
  have hsch₃ := hsch₂.perm hperm
  have happ₂ : (domain D vars bound).SeqApplicable z₂
      ((domain D vars bound).transition (AcAct.accept RW.write) s₁) := happ₁.2
  set s₂ := (domain D vars bound).transition (AcAct.accept RW.write) s₁ with hs₂def
  have hkd₂ : KeysDown s₂ := by
    refine ⟨by simp [hs₂def, mem_transition_accept, hk0], fun x => ⟨?_, ?_⟩⟩
    · rcases x with _ | _
      · simp [hs₂def, mem_transition_accept, hk1R]
      · simp [hs₂def, mem_transition_accept]
    · simp [hs₂def, mem_transition_accept, hk2 x]
  have hrest₀ : ∀ l ∈ pre₀ ++ post, CompInv D vars bound l := by
    intro l hl
    refine hrest l ?_
    rcases List.mem_append.1 hl with h | h
    · exact List.mem_append.2 (Or.inl h)
    · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h))
  -- the cell runs its phase
  have husil : ∀ a ∈ (testsOf 0 Sa vars ++ testsOf 2 Sa' vars ++ [AcAct.preC ta] :
      List (AcAct F A C)), keySilent a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with h | h
      · exact keySilent_testsOf a h
      · exact keySilent_testsOf a h
    · rw [List.mem_singleton] at ha
      subst ha
      simp [keySilent]
  obtain ⟨z₃, rfl, hsch₄⟩ :=
    peel_silent_run_waiting (D := D) (vars := vars) (bound := bound) husil
      (by simpa [List.append_assoc] using hsch₃) happ₂ hkd₂ ⟨RW.write, t, rfl⟩ hrest₀
  set s₃ := (domain D vars bound).transitionSeq
    (testsOf 0 Sa vars ++ testsOf 2 Sa' vars ++ [AcAct.preC ta]) s₂ with hs₃def
  have happ₃ : (domain D vars bound).SeqApplicable z₃ s₃ := by
    have := (ActionModel.seqApplicable_append (domain D vars bound).toActionModel
      (testsOf 0 Sa vars ++ testsOf 2 Sa' vars ++ [AcAct.preC ta]) z₃ s₂).1 happ₂
    exact this.2
  have hkd₃ : KeysDown s₃ := keysDown_transitionSeq husil hkd₂
  obtain ⟨z₄, rfl, hsch₅⟩ :=
    Sched.peel hsch₄ happ₃ (fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · exact stuck_waitA (hkd₃.2 RW.write).2
      · exact compInv_stuck hkd₃.toNoLockNoAsk (hrest₀ l hl))
  have happ₄ : (domain D vars bound).SeqApplicable z₄
      ((domain D vars bound).transition (AcAct.doneA RW.write) s₃) := happ₃.2
  set s₄ := (domain D vars bound).transition (AcAct.doneA RW.write) s₃ with hs₄def
  have hnla₄ : NoLockNoAsk s₄ :=
    noLockNoAsk_transition_doneA (D := D) (vars := vars) (bound := bound) hkd₃.toNoLockNoAsk
  have hperm₂ : ((memRead Sa Sa' ta vars) :: (AcAct.waitA RW.write :: t) :: (pre₀ ++ post)).Perm
      ((AcAct.waitA RW.write :: t) :: (memRead Sa Sa' ta vars) :: (pre₀ ++ post)) :=
    List.Perm.swap _ _ _
  obtain ⟨z₅, rfl, hsch₆⟩ :=
    Sched.peel (hsch₅.perm hperm₂) happ₄ (fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · rw [memRead_cons]
        exact stuck_accept (hnla₄.2 RW.read)
      · exact compInv_stuck hnla₄ (hrest₀ l hl))
  -- the cell latched exactly the triple the state holds
  have hzeq : (AcAct.accept RW.write ::
      ((testsOf 0 Sa vars ++ testsOf 2 Sa' vars ++ [AcAct.preC ta]) ++
        AcAct.doneA RW.write :: AcAct.waitA RW.write :: z₅)) =
      memWrite Sa Sa' ta vars ++ (AcAct.waitA RW.write :: z₅) := by
    simp [memWrite, List.append_assoc]
  rw [hzeq] at happ₁
  have hwapp : (domain D vars bound).SeqApplicable (memWrite Sa Sa' ta vars) s₁ :=
    ((ActionModel.seqApplicable_append (domain D vars bound).toActionModel
      (memWrite Sa Sa' ta vars) (AcAct.waitA RW.write :: z₅) s₁).1 happ₁).1
  obtain ⟨-, h0, h2, hta⟩ := seqApplicable_memWrite_iff.1 hwapp
  have hSa : Sa = S := by
    refine Set.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
    · exact (hrep0₁ v (hvars v)).1.1 ((h0 v (hvars v)).1 hv)
    · by_contra hc
      exact ((hrep0₁ v (hvars v)).2.1 ((h0 v (hvars v)).2 hc)) hv
  have hSa' : Sa' = S' := by
    refine Set.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
    · exact (hrep2₁ v (hvars v)).1.1 ((h2 v (hvars v)).1 hv)
    · by_contra hc
      exact ((hrep2₁ v (hvars v)).2.1 ((h2 v (hvars v)).2 hc)) hv
  have hta' : ta = tt := (htask₁ ta).1 hta
  subst hSa
  subst hSa'
  subst hta'
  refine ⟨(memRead Sa Sa' ta vars) :: (pre₀ ++ post), z₅, ?_, hsch₆, ?_⟩
  · simp [writePhase, memWrite, List.append_assoc]
  · intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact Or.inl (Or.inr ⟨Sa, Sa', ta, rfl, hprov⟩)
    · exact hrest₀ l hl

end ToAc

end HTN
