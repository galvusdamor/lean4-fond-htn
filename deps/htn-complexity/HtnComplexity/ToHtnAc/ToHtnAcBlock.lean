import HtnComplexity.ToHtnAc.ToHtnAcPeel
import HtnComplexity.ToHtnAc.ToHtnAcTupleShape
/-!
# A plan of the compiled problem is a concatenation of blocks

This file completes the *block decomposition* of a plan of the HTN-AC compilation: starting in a
clean state (the lock free, no handshake open), the plan continues with one whole proof step —
its guesses, its comparisons, the read phases of the memory cells answering its read requests,
and the write phases of the memory cells it fills — and reaches a clean state again.  The block
is exactly the `HTN.ToAc.compoundBlock` / `HTN.ToAc.primBlock` of
`HtnComplexity/ToHtnAc/ToHtnAcComplete.lean`, so this is the converse of
`HTN.ToAc.exists_scheduled_blocks`.

The two theorems are

* `HTN.ToAc.peel_writeReqs` — the write requests of a proof step are answered by memory cells
  that latch exactly the triple the step has just proved, and the step then releases the lock;
* `HTN.ToAc.exists_block` — from a clean state a nonempty plan performs one whole proof step;
  the triple it leaves in the state (`copy 0`, the stored task name, `copy 2`) is derivable in
  the proof-tuple calculus, and every component is again in one of the states of
  `HTN.ToAc.CompInv`.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### Frame lemmas for the two phases -/

/-- The key facts after a read phase: the read phase lowers `key₁^R`, raises `key₂^R` and
changes nothing else that is not a copy or the stored task name. -/
lemma key_mem_transitionSeq_memRead {S S' : Set F} {tt : A ⊕ C} {s : Set (AcFact F A C)}
    {f : AcFact F A C} (hpos : ∀ (v : F) (i : Fin 5), f ≠ AcFact.pos v i)
    (hneg : ∀ (v : F) (i : Fin 5), f ≠ AcFact.neg v i)
    (htask : ∀ t' : A ⊕ C, f ≠ AcFact.task t') :
    f ∈ (domain D vars bound).transitionSeq (memRead S S' tt vars) s ↔
      ((f ∈ s ∧ f ≠ AcFact.key1 RW.read) ∨ f = AcFact.key2 RW.read) := by
  classical
  rw [memRead]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    ActionModel.transitionSeq_nil, mem_transition_doneA]
  rw [unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (f := f) (fun w _ => ⟨fun hc => hpos w 3 hc, fun hc => hneg w 3 hc⟩),
    unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (f := f) (fun w _ => ⟨fun hc => hpos w 4 hc, fun hc => hneg w 4 hc⟩),
    mem_transition_setC, mem_transition_accept]
  constructor
  · rintro ((⟨⟨hf, hne⟩, -⟩ | hc) | rfl)
    · exact Or.inl ⟨hf, hne⟩
    · exact absurd hc (htask tt)
    · exact Or.inr rfl
  · rintro (⟨hf, hne⟩ | rfl)
    · exact Or.inl (Or.inl ⟨⟨hf, hne⟩, htask⟩)
    · exact Or.inr rfl

/-- A read phase leaves all semaphores down. -/
lemma keysDown_readPhase {S S' : Set F} {tt : A ⊕ C} {s : Set (AcFact F A C)}
    (h : KeysDown s) :
    KeysDown ((domain D vars bound).transitionSeq (readPhase S S' tt vars) s) := by
  classical
  have hexp : (domain D vars bound).transitionSeq (readPhase S S' tt vars) s =
      (domain D vars bound).transition (AcAct.waitA RW.read)
        ((domain D vars bound).transitionSeq (memRead S S' tt vars)
          ((domain D vars bound).transition (AcAct.ask RW.read) s)) := by
    rw [readPhase]
    simp [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append]
  rw [hexp]
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · rw [mem_transition_waitA, key_mem_transitionSeq_memRead (by simp) (by simp) (by simp),
      mem_transition_ask]
    simp [h.1]
  · rw [mem_transition_waitA, key_mem_transitionSeq_memRead (by simp) (by simp) (by simp),
      mem_transition_ask]
    rcases x with _ | _ <;> simp [(h.2 RW.read).1, (h.2 RW.write).1]
  · rw [mem_transition_waitA, key_mem_transitionSeq_memRead (by simp) (by simp) (by simp),
      mem_transition_ask]
    rcases x with _ | _ <;> simp [(h.2 RW.read).2, (h.2 RW.write).2]

/-- A write handshake changes nothing but the two write semaphores. -/
lemma mem_transitionSeq_writeHandshake {S S' : Set F} {tt : A ⊕ C} {s : Set (AcFact F A C)}
    {f : AcFact F A C} (h1 : f ≠ AcFact.key1 RW.write) (h2 : f ≠ AcFact.key2 RW.write) :
    f ∈ (domain D vars bound).transitionSeq (writePhase S S' tt vars 1) s ↔ f ∈ s := by
  classical
  have hexp : (domain D vars bound).transitionSeq (writePhase S S' tt vars 1) s =
      (domain D vars bound).transition (AcAct.waitA RW.write)
        ((domain D vars bound).transitionSeq (memWrite S S' tt vars)
          ((domain D vars bound).transition (AcAct.ask RW.write) s)) := by
    rw [writePhase_one]
    simp [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append]
  rw [hexp, mem_transition_waitA, mem_transitionSeq_memWrite, mem_transition_ask]
  simp [h1, h2]

/-- A write handshake leaves all semaphores down. -/
lemma keysDown_writeHandshake {S S' : Set F} {tt : A ⊕ C} {s : Set (AcFact F A C)}
    (h : KeysDown s) :
    KeysDown ((domain D vars bound).transitionSeq (writePhase S S' tt vars 1) s) := by
  classical
  have hexp : (domain D vars bound).transitionSeq (writePhase S S' tt vars 1) s =
      (domain D vars bound).transition (AcAct.waitA RW.write)
        ((domain D vars bound).transitionSeq (memWrite S S' tt vars)
          ((domain D vars bound).transition (AcAct.ask RW.write) s)) := by
    rw [writePhase_one]
    simp [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append]
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · rw [mem_transitionSeq_writeHandshake (by simp) (by simp)]
    exact h.1
  · rcases x with _ | _
    · rw [mem_transitionSeq_writeHandshake (by simp) (by simp)]
      exact (h.2 RW.read).1
    · rw [hexp, mem_transition_waitA, mem_transitionSeq_memWrite]
      simp
  · rcases x with _ | _
    · rw [mem_transitionSeq_writeHandshake (by simp) (by simp)]
      exact (h.2 RW.read).2
    · rw [hexp, mem_transition_waitA]
      simp

lemma representsOn_writeHandshake {S S' : Set F} {tt : A ⊕ C} {i : Fin 5} {T : Set F}
    {s : Set (AcFact F A C)} (h : RepresentsOn s i T vars) :
    RepresentsOn ((domain D vars bound).transitionSeq (writePhase S S' tt vars 1) s) i T
      vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transitionSeq_writeHandshake (by simp) (by simp),
    mem_transitionSeq_writeHandshake (by simp) (by simp)]
  exact ⟨h1, h2⟩

lemma taskOnly_writeHandshake {S S' : Set F} {tt t : A ⊕ C} {s : Set (AcFact F A C)}
    (h : TaskOnly t s) :
    TaskOnly t ((domain D vars bound).transitionSeq (writePhase S S' tt vars 1) s) := by
  intro t'
  rw [mem_transitionSeq_writeHandshake (by simp) (by simp)]
  exact h t'

/-! ### The write requests and the release of the lock -/

/-- **The tail of a proof step.**  Every write request of a proof step is answered by an
untouched memory cell, which latches exactly the triple the step has proved; the step then
releases the lock and the state is clean again. -/
lemma peel_writeReqs (hvars : ∀ v : F, v ∈ vars) {S S' : Set F} {tt : A ⊕ C}
    (hprov : D.Provable S tt S') :
    ∀ (w : ℕ) {rest : List (List (AcAct F A C))} {z : List (AcAct F A C)}
      {s : Set (AcFact F A C)},
      Sched ((((List.replicate w
          ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten ++
        [AcAct.unlock]) : List (AcAct F A C)) :: rest) z →
      (domain D vars bound).SeqApplicable z s → KeysDown s →
      (∀ l ∈ rest, CompInv D vars bound l) →
      RepresentsOn s 0 S vars → RepresentsOn s 2 S' vars → TaskOnly tt s →
      ∃ (rest' : List (List (AcAct F A C))) (p z' : List (AcAct F A C)),
        z = p ++ z' ∧ Sched rest' z' ∧ (∀ l ∈ rest', CompInv D vars bound l) ∧
          Clean ((domain D vars bound).transitionSeq p s) ∧
          RepresentsOn ((domain D vars bound).transitionSeq p s) 0 S vars ∧
          RepresentsOn ((domain D vars bound).transitionSeq p s) 2 S' vars ∧
          TaskOnly tt ((domain D vars bound).transitionSeq p s) := by
  intro w
  induction w with
  | zero =>
      intro rest z s hsched happ hkd hrest hrep0 hrep2 htask
      obtain ⟨z', rfl, hsch'⟩ :=
        Sched.peel (by simpa using hsched) happ
          (fun l hl => compInv_stuck hkd.toNoLockNoAsk (hrest l hl))
      refine ⟨([] : List (AcAct F A C)) :: rest, [AcAct.unlock], z', by simp, hsch', ?_,
        ?_, ?_, ?_, ?_⟩
      · intro l hl
        rcases List.mem_cons.1 hl with rfl | hl
        · exact compInv_nil
        · exact hrest l hl
      · refine ⟨by simp, fun x => ⟨?_, ?_⟩⟩
        · simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
            mem_transition_unlock]
          simp [(hkd.2 x).1]
        · simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
            mem_transition_unlock]
          simp [(hkd.2 x).2]
      · intro v hv
        obtain ⟨h1, h2⟩ := hrep0 v hv
        simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
          mem_transition_unlock]
        simpa using ⟨h1, h2⟩
      · intro v hv
        obtain ⟨h1, h2⟩ := hrep2 v hv
        simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
          mem_transition_unlock]
        simpa using ⟨h1, h2⟩
      · intro t'
        simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
          mem_transition_unlock]
        simpa using htask t'
  | succ w ih =>
      intro rest z s hsched happ hkd hrest hrep0 hrep2 htask
      have hsched' : Sched ((AcAct.ask RW.write :: AcAct.waitA RW.write ::
          ((List.replicate w
            ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten ++
              [AcAct.unlock])) :: rest) z := by
        simpa [List.replicate_succ] using hsched
      obtain ⟨rest₁, z₁, rfl, hsch₁, hinv₁⟩ :=
        peel_writeHandshake hvars hsched' happ hkd hrest hrep0 hrep2 htask hprov
      have happ₁ : (domain D vars bound).SeqApplicable z₁
          ((domain D vars bound).transitionSeq (writePhase S S' tt vars 1) s) := by
        have := (ActionModel.seqApplicable_append (domain D vars bound).toActionModel
          (writePhase S S' tt vars 1) z₁ s).1 happ
        exact this.2
      obtain ⟨rest', p, z', rfl, hsch', hinv', hclean', hr0', hr2', ht'⟩ :=
        ih hsch₁ happ₁ (keysDown_writeHandshake hkd) hinv₁
          (representsOn_writeHandshake hrep0) (representsOn_writeHandshake hrep2)
          (taskOnly_writeHandshake htask)
      refine ⟨rest', writePhase S S' tt vars 1 ++ p, z', by simp [List.append_assoc],
        hsch', hinv', ?_, ?_, ?_, ?_⟩ <;>
        rw [ActionModel.transitionSeq_append]
      exacts [hclean', hr0', hr2', ht']

/-! ### Silent gadgets, the lock, and the stored task name -/

lemma keySilent_yieldSeq_SEL {i : Fin 5} {g : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL i)] g) : ∀ a ∈ g, keySilent a :=
  keySilent_of_countP_isSync (countP_yieldSeq_SEL handshakePred_isSync h)

lemma keySilent_yieldSeq_EQ {i j : Fin 5} {g : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ i j)] g) : ∀ a ∈ g, keySilent a :=
  keySilent_of_countP_isSync (countP_yieldSeq_EQ handshakePred_isSync h)

lemma keysDown_transition_lock {s : Set (AcFact F A C)} (h : Clean s) :
    KeysDown ((domain D vars bound).transition (AcAct.lock : AcAct F A C) s) := by
  refine ⟨by simp, fun x => ⟨?_, ?_⟩⟩
  · simp [(h.2 x).1]
  · simp [(h.2 x).2]

/-- After an action storing a task name, that task name is the only one stored. -/
lemma taskOnly_transitionSeq_setC {u : List (AcAct F A C)} {t : A ⊕ C}
    {s : Set (AcFact F A C)} :
    TaskOnly t ((domain D vars bound).transitionSeq (u ++ [AcAct.setC t]) s) := by
  intro t'
  rw [ActionModel.transitionSeq_append]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil]
  rw [mem_transition_setC]
  constructor
  · rintro (⟨-, hne⟩ | hc)
    · exact absurd rfl (hne t')
    · simpa using hc
  · rintro rfl
    exact Or.inr rfl

/-- The guessing, reading and comparing part of a compound proof step leaves all semaphores
down. -/
lemma keysDown_compoundStepPrefix {c : C} {x y : A ⊕ C} {S₁ S₁' S₂ S₂' : Set F}
    {t₁ t₂ : A ⊕ C} {g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)} {s : Set (AcFact F A C)}
    (hg₁ : ∀ a ∈ g₁, keySilent a) (hg₂ : ∀ a ∈ g₂, keySilent a) (hg₃ : ∀ a ∈ g₃, keySilent a)
    (he₁ : ∀ a ∈ e₁, keySilent a) (he₂ : ∀ a ∈ e₂, keySilent a) (he₃ : ∀ a ∈ e₃, keySilent a)
    (he₄ : ∀ a ∈ e₄, keySilent a) (hclean : Clean s) :
    KeysDown ((domain D vars bound).transitionSeq
      (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s) := by
  have hsil₁ : ∀ a ∈ g₁ ++ g₂ ++ g₃, keySilent a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact hg₁ a ha
      · exact hg₂ a ha
    · exact hg₃ a ha
  have hsil₂ : ∀ a ∈ e₁ ++ e₂ ++ [AcAct.preC x], keySilent a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact he₁ a ha
      · exact he₂ a ha
    · rw [List.mem_singleton] at ha; subst ha; simp [keySilent]
  have hsil₃ : ∀ a ∈ e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)], keySilent a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact he₃ a ha
      · exact he₄ a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · simp [keySilent]
      · rw [List.mem_singleton] at ha; subst ha; simp [keySilent]
  have hexp : compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars =
      AcAct.lock :: ((g₁ ++ g₂ ++ g₃) ++ (readPhase S₁ S₁' t₁ vars ++
        ((e₁ ++ e₂ ++ [AcAct.preC x]) ++ (readPhase S₂ S₂' t₂ vars ++
          (e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]))))) := by
    simp [compoundStepPrefix, List.append_assoc]
  have hchain : (domain D vars bound).transitionSeq
      (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s =
      (domain D vars bound).transitionSeq (e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)])
        ((domain D vars bound).transitionSeq (readPhase S₂ S₂' t₂ vars)
          ((domain D vars bound).transitionSeq (e₁ ++ e₂ ++ [AcAct.preC x])
            ((domain D vars bound).transitionSeq (readPhase S₁ S₁' t₁ vars)
              ((domain D vars bound).transitionSeq (g₁ ++ g₂ ++ g₃)
                ((domain D vars bound).transition (AcAct.lock : AcAct F A C) s))))) := by
    rw [hexp]
    simp [ActionModel.transitionSeq_append, ActionModel.transitionSeq_cons, List.append_assoc]
  rw [hchain]
  exact keysDown_transitionSeq hsil₃ (keysDown_readPhase (keysDown_transitionSeq hsil₂
    (keysDown_readPhase (keysDown_transitionSeq hsil₁ (keysDown_transition_lock hclean)))))

/-- The guessing and comparing part of a primitive proof step leaves all semaphores down. -/
lemma keysDown_primStepPrefix {o : A} {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)}
    {s : Set (AcFact F A C)}
    (hg₁ : ∀ a ∈ g₁, keySilent a) (hg₂ : ∀ a ∈ g₂, keySilent a) (hg₃ : ∀ a ∈ g₃, keySilent a)
    (he₁ : ∀ a ∈ e₁, keySilent a) (he₂ : ∀ a ∈ e₂, keySilent a) (hclean : Clean s) :
    KeysDown ((domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s) := by
  have hsil : ∀ a ∈ g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)],
      keySilent a := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ((((((ha | ha) | ha) | ha) | rfl) | ha) | rfl)
    · exact hg₁ a ha
    · exact hg₂ a ha
    · exact hg₃ a ha
    · exact he₁ a ha
    · simp [keySilent]
    · exact he₂ a ha
    · simp [keySilent]
  rw [primStepPrefix]
  simp only [ActionModel.transitionSeq_cons]
  exact keysDown_transitionSeq (by simpa [List.append_assoc] using hsil)
    (keysDown_transition_lock hclean)

/-! ### One block -/

/-- **From a clean state a plan performs one whole proof step.**  The plan continues with the
actions of an unstarted proof step, with the read phases of the memory cells answering its read
requests and the write phases of the memory cells it fills spliced in; it reaches a clean state
again, in which the first copy, the stored task name and the third copy hold a triple that is
derivable in the proof-tuple calculus.  Every component is again in one of the states of
`HTN.ToAc.CompInv` — in particular every cell that has just latched a triple holds a *provable*
one. -/
theorem exists_block (hvars : ∀ v : F, v ∈ vars) (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    {ls : List (List (AcAct F A C))} {z : List (AcAct F A C)} {s : Set (AcFact F A C)}
    (hinv : ∀ l ∈ ls, CompInv D vars bound l) (hclean : Clean s)
    (hsched : Sched ls z) (happ : (domain D vars bound).SeqApplicable z s) (hz : z ≠ []) :
    ∃ (p z' : List (AcAct F A C)) (ls' : List (List (AcAct F A C))) (S S' : Set F)
      (tt : A ⊕ C),
      z = p ++ z' ∧ p ≠ [] ∧ Sched ls' z' ∧ (∀ l ∈ ls', CompInv D vars bound l) ∧
        D.Provable S tt S' ∧ Clean ((domain D vars bound).transitionSeq p s) ∧
        RepresentsOn ((domain D vars bound).transitionSeq p s) 0 S vars ∧
        RepresentsOn ((domain D vars bound).transitionSeq p s) 2 S' vars ∧
        TaskOnly tt ((domain D vars bound).transitionSeq p s) := by
  classical
  rcases z with _ | ⟨b, z₀⟩
  · exact absurd rfl hz
  obtain ⟨pre, post, t, hls, hsch₀⟩ := hsched.exists_of_cons
  have happb : (domain D vars bound).Applicable b s := happ.1
  have hmem : (b :: t) ∈ ls := by rw [hls]; simp
  -- the component that moves is an unstarted proof step
  have hstep : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)]
      (b :: t) := by
    rcases hinv _ hmem with (⟨S, S', tt, hl⟩ | ⟨S, S', tt, hl, -⟩) | h | hnil
    · exfalso
      rw [memWrite_cons, List.cons_append] at hl
      obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
      exact (hclean.2 RW.write).1 (applicable_accept_iff.1 happb)
    · exfalso
      rw [memRead_cons] at hl
      obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hl
      exact (hclean.2 RW.read).1 (applicable_accept_iff.1 happb)
    · exact h
    · exact absurd hnil (by simp)
  have hrest : ∀ l ∈ pre ++ post, CompInv D vars bound l := by
    intro l hl
    refine hinv l ?_
    rw [hls]
    rcases List.mem_append.1 hl with h | h
    · exact List.mem_append.2 (Or.inl h)
    · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h))
  have hsch₁ : Sched (t :: (pre ++ post)) z₀ := hsch₀.perm List.perm_middle
  have happ₀ : (domain D vars bound).SeqApplicable z₀
      ((domain D vars bound).transition b s) := happ.2
  clear hsch₀ hls hmem
  rcases yieldSeq_TUPLE_shape hstep with
    ⟨c, x, y, g₁, g₂, g₃, e₁, e₂, e₃, e₄, w, hmethod, -, hg₁, hg₂, hg₃, he₁, he₂, he₃, he₄,
      hshape⟩ |
    ⟨o, g₁, g₂, g₃, e₁, e₂, w, -, hg₁, hg₂, hg₃, he₁, he₂, hshape⟩
  · -- a compound proof step
    have hsil₁ : ∀ a ∈ g₁ ++ g₂ ++ g₃, keySilent a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · rcases List.mem_append.1 ha with ha | ha
        · exact keySilent_yieldSeq_SEL hg₁ a ha
        · exact keySilent_yieldSeq_SEL hg₂ a ha
      · exact keySilent_yieldSeq_SEL hg₃ a ha
    have hsil₂ : ∀ a ∈ e₁ ++ e₂ ++ [AcAct.preC x], keySilent a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · rcases List.mem_append.1 ha with ha | ha
        · exact keySilent_yieldSeq_EQ he₁ a ha
        · exact keySilent_yieldSeq_EQ he₂ a ha
      · rw [List.mem_singleton] at ha; subst ha; simp [keySilent]
    have hsil₃ : ∀ a ∈ e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)], keySilent a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · rcases List.mem_append.1 ha with ha | ha
        · exact keySilent_yieldSeq_EQ he₃ a ha
        · exact keySilent_yieldSeq_EQ he₄ a ha
      · rcases List.mem_cons.1 ha with rfl | ha
        · simp [keySilent]
        · rw [List.mem_singleton] at ha; subst ha; simp [keySilent]
    have hnorm : b :: t = AcAct.lock :: ((g₁ ++ g₂ ++ g₃) ++
        (AcAct.ask RW.read :: AcAct.waitA RW.read ::
          ((e₁ ++ e₂ ++ [AcAct.preC x]) ++ (AcAct.ask RW.read :: AcAct.waitA RW.read ::
            ((e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]) ++
              ((List.replicate w
                ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten ++
                [AcAct.unlock])))))) := by
      rw [hshape]; simp [tupleCompoundSeq, List.append_assoc]
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 hnorm
    set s₁ := (domain D vars bound).transition (AcAct.lock : AcAct F A C) s with hs₁def
    have hkd₁ : KeysDown s₁ := keysDown_transition_lock hclean
    -- the three guesses
    obtain ⟨z₂, rfl, hsch₂⟩ :=
      peel_silent_run hsil₁ hsch₁ happ₀ hkd₁.toNoLockNoAsk hrest
    have happ₂ : (domain D vars bound).SeqApplicable z₂
        ((domain D vars bound).transitionSeq (g₁ ++ g₂ ++ g₃) s₁) :=
      ((ActionModel.seqApplicable_append _ _ _ _).1 happ₀).2
    set s₂ := (domain D vars bound).transitionSeq (g₁ ++ g₂ ++ g₃) s₁ with hs₂def
    have hkd₂ : KeysDown s₂ := keysDown_transitionSeq hsil₁ hkd₁
    -- the first read handshake
    obtain ⟨S₁, S₁', t₁, rest₁, z₃, hprov₁, rfl, hsch₃, hinv₁⟩ :=
      peel_readHandshake hsch₂ happ₂ hkd₂ hrest
    have happ₃ : (domain D vars bound).SeqApplicable z₃
        ((domain D vars bound).transitionSeq (readPhase S₁ S₁' t₁ vars) s₂) :=
      ((ActionModel.seqApplicable_append _ _ _ _).1 happ₂).2
    set s₃ := (domain D vars bound).transitionSeq (readPhase S₁ S₁' t₁ vars) s₂ with hs₃def
    have hkd₃ : KeysDown s₃ := keysDown_readPhase hkd₂
    -- the first two comparisons
    obtain ⟨z₄, rfl, hsch₄⟩ :=
      peel_silent_run hsil₂ hsch₃ happ₃ hkd₃.toNoLockNoAsk hinv₁
    have happ₄ : (domain D vars bound).SeqApplicable z₄
        ((domain D vars bound).transitionSeq (e₁ ++ e₂ ++ [AcAct.preC x]) s₃) :=
      ((ActionModel.seqApplicable_append _ _ _ _).1 happ₃).2
    set s₄ := (domain D vars bound).transitionSeq (e₁ ++ e₂ ++ [AcAct.preC x]) s₃ with hs₄def
    have hkd₄ : KeysDown s₄ := keysDown_transitionSeq hsil₂ hkd₃
    -- the second read handshake
    obtain ⟨S₂, S₂', t₂, rest₂, z₅, hprov₂, rfl, hsch₅, hinv₂⟩ :=
      peel_readHandshake hsch₄ happ₄ hkd₄ hinv₁
    have happ₅ : (domain D vars bound).SeqApplicable z₅
        ((domain D vars bound).transitionSeq (readPhase S₂ S₂' t₂ vars) s₄) :=
      ((ActionModel.seqApplicable_append _ _ _ _).1 happ₄).2
    set s₅ := (domain D vars bound).transitionSeq (readPhase S₂ S₂' t₂ vars) s₄ with hs₅def
    have hkd₅ : KeysDown s₅ := keysDown_readPhase hkd₄
    -- the last two comparisons and the stored task name
    obtain ⟨z₆, rfl, hsch₆⟩ :=
      peel_silent_run hsil₃ hsch₅ happ₅ hkd₅.toNoLockNoAsk hinv₂
    have happ₆ : (domain D vars bound).SeqApplicable z₆
        ((domain D vars bound).transitionSeq
          (e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]) s₅) :=
      ((ActionModel.seqApplicable_append _ _ _ _).1 happ₅).2
    -- what the step has proved
    have hpfx : (domain D vars bound).transitionSeq
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s =
        (domain D vars bound).transitionSeq
          (e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]) s₅ := by
      rw [hs₅def, hs₄def, hs₃def, hs₂def, hs₁def, compoundStepPrefix]
      simp [ActionModel.transitionSeq_append, ActionModel.transitionSeq_cons,
        List.append_assoc]
    have happpfx : (domain D vars bound).SeqApplicable
        (compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars) s := by
      have hz : (AcAct.lock :: ((g₁ ++ g₂ ++ g₃) ++ (readPhase S₁ S₁' t₁ vars ++
          ((e₁ ++ e₂ ++ [AcAct.preC x]) ++ (readPhase S₂ S₂' t₂ vars ++
            ((e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]) ++ z₆)))))) =
          compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars ++ z₆ := by
        simp [compoundStepPrefix, List.append_assoc]
      rw [hz] at happ
      exact ((ActionModel.seqApplicable_append _ _ _ _).1 happ).1
    obtain ⟨hprov, hrep0, hrep2, -⟩ :=
      compoundStep_provable hvars hmethod hprov₁ hprov₂ hg₁ hg₂ hg₃ he₁ he₂ he₃ he₄ happpfx
    rw [hpfx] at hrep0 hrep2
    have htask : TaskOnly (Sum.inr c)
        ((domain D vars bound).transitionSeq
          (e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]) s₅) := by
      have : (e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)] : List (AcAct F A C)) =
          (e₃ ++ e₄ ++ [AcAct.preC y]) ++ [AcAct.setC (Sum.inr c)] := by
        simp [List.append_assoc]
      rw [this]
      exact taskOnly_transitionSeq_setC
    have hkd₆ : KeysDown ((domain D vars bound).transitionSeq
        (e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]) s₅) :=
      keysDown_transitionSeq hsil₃ hkd₅
    -- the write requests and the release of the lock
    obtain ⟨rest', pw, z', rfl, hsch', hinv', hclean', hr0', hr2', ht'⟩ :=
      peel_writeReqs hvars hprov w hsch₆ happ₆ hkd₆ hinv₂ hrep0 hrep2 htask
    refine ⟨compoundStepPrefix c x y S₁ S₁' S₂ S₂' t₁ t₂ g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars ++ pw,
      z', rest', S₁, S₂', Sum.inr c, by simp [compoundStepPrefix, List.append_assoc],
      by simp [compoundStepPrefix], hsch', hinv', hprov, ?_, ?_, ?_, ?_⟩ <;>
      rw [ActionModel.transitionSeq_append, hpfx]
    exacts [hclean', hr0', hr2', ht']
  · -- a primitive proof step
    have hsil : ∀ a ∈ g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)],
        keySilent a := by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ((((((ha | ha) | ha) | ha) | rfl) | ha) | rfl)
      · exact keySilent_yieldSeq_SEL hg₁ a ha
      · exact keySilent_yieldSeq_SEL hg₂ a ha
      · exact keySilent_yieldSeq_SEL hg₃ a ha
      · exact keySilent_yieldSeq_EQ he₁ a ha
      · simp [keySilent]
      · exact keySilent_yieldSeq_EQ he₂ a ha
      · simp [keySilent]
    have hnorm : b :: t = AcAct.lock ::
        ((g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)]) ++
          ((List.replicate w
            ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten ++
            [AcAct.unlock])) := by
      rw [hshape]; simp [tuplePrimitiveSeq, List.append_assoc]
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 hnorm
    set s₁ := (domain D vars bound).transition (AcAct.lock : AcAct F A C) s with hs₁def
    have hkd₁ : KeysDown s₁ := keysDown_transition_lock hclean
    obtain ⟨z₂, rfl, hsch₂⟩ :=
      peel_silent_run hsil hsch₁ happ₀ hkd₁.toNoLockNoAsk hrest
    have happ₂ : (domain D vars bound).SeqApplicable z₂
        ((domain D vars bound).transitionSeq
          (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)]) s₁) :=
      ((ActionModel.seqApplicable_append _ _ _ _).1 happ₀).2
    have hpfx : (domain D vars bound).transitionSeq (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s =
        (domain D vars bound).transitionSeq
          (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)]) s₁ := by
      rw [hs₁def, primStepPrefix]
      simp [ActionModel.transitionSeq_append, ActionModel.transitionSeq_cons,
        List.append_assoc]
    have happpfx : (domain D vars bound).SeqApplicable (primStepPrefix o g₁ g₂ g₃ e₁ e₂) s := by
      have hz : (AcAct.lock ::
          ((g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)]) ++ z₂)) =
          primStepPrefix o g₁ g₂ g₃ e₁ e₂ ++ z₂ := by
        simp [primStepPrefix, List.append_assoc]
      rw [hz] at happ
      exact ((ActionModel.seqApplicable_append _ _ _ _).1 happ).1
    obtain ⟨S, hprov, hrep0, hrep2, -⟩ :=
      primStep_provable hvars (hdisj o) hg₁ hg₂ hg₃ he₁ he₂ happpfx
    rw [hpfx] at hrep0 hrep2
    have htask : TaskOnly (Sum.inl o)
        ((domain D vars bound).transitionSeq
          (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)]) s₁) :=
      taskOnly_transitionSeq_setC
    have hkd₂ : KeysDown ((domain D vars bound).transitionSeq
        (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)]) s₁) :=
      keysDown_transitionSeq hsil hkd₁
    obtain ⟨rest', pw, z', rfl, hsch', hinv', hclean', hr0', hr2', ht'⟩ :=
      peel_writeReqs hvars hprov w hsch₂ happ₂ hkd₂ hrest hrep0 hrep2 htask
    refine ⟨primStepPrefix o g₁ g₂ g₃ e₁ e₂ ++ pw, z', rest', S, D.transition o S, Sum.inl o,
      by simp [primStepPrefix, List.append_assoc], by simp [primStepPrefix], hsch', hinv',
      hprov, ?_, ?_, ?_, ?_⟩ <;>
      rw [ActionModel.transitionSeq_append, hpfx]
    exacts [hclean', hr0', hr2', ht']

end ToAc

end HTN
