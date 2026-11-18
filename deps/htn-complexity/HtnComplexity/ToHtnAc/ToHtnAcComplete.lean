import HtnComplexity.ToHtnAc.ToHtnAcSchedule
import HtnComplexity.ToHtnAc.ToHtnAcCntPar
/-!
# Completeness of the TO-HTN ⟶ HTN-AC compilation

`HtnComplexity/ToHtnAc/ToHtnAc.lean` compiles a totally ordered HTN problem into an acyclic one.
This file proves the **completeness** half of its correctness: from a derivation of the
proof-tuple calculus of `HtnPlanning/Core/ProofTuples.lean` — equivalently, by
`HTN.Domain.provable_iff_yield`, from a solution of the source problem — a *plan* of the
compiled problem is built.

The plan is assembled out of the gadget refinements that the previous files provide:

* one refinement of `TUPLE` per node of the derivation
  (`HTN.ToAc.yieldSeq_TUPLE_of_compound`, `HTN.ToAc.yieldSeq_TUPLE_of_primitive`),
* one refinement of `MEM` per node (`HTN.ToAc.yieldSeq_MEM_memPhases`), whose write phase is
  spliced into the write handshake of the node's own proof step and whose read phase is spliced
  into one of the two read handshakes of the proof step of the node's parent,
* the whole plan being an interleaving of the memory cells with the proof steps, which is what
  the initial task `t_I` refines into (`HTN.ToAc.netYield_tnI_iff`).

## The goal of the compiled problem

The goal of `HTN.ToAc.instance_` — as printed in the draft — asks for the *fourth* and *fifth*
copies (`pos v 3`, `pos v 4`) at the end of the plan.  Those two copies are written by the read
phase of a memory cell, and a read phase can only run inside the read handshake of an ongoing
proof step, whose subsequent `setC` overwrites the stored task name; the analysis of the gadgets
therefore suggests that with the printed goal the answer cannot be read out at the end of a plan
(this is an observation about the construction, not a formalised theorem).  This file uses the
repaired instance
`HTN.ToAc.instance'`, which checks the *first* and *third* copies — the guesses of the last
proof step itself — and, in order to pin the initial state down exactly, also the negative
copies of the facts outside it.  Nothing in the domain is changed.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### Further transition lemmas -/

@[simp] lemma mem_transition_ask {x : RW} {s : Set (AcFact F A C)} {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition (AcAct.ask x) s ↔ f ∈ s ∨ f = AcFact.key1 x := by
  simp [ActionModel.transition, domain, actionModel, add, del, or_comm]

@[simp] lemma mem_transition_waitA {x : RW} {s : Set (AcFact F A C)} {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition (AcAct.waitA x) s ↔ f ∈ s ∧ f ≠ AcFact.key2 x := by
  simp [ActionModel.transition, domain, actionModel, add, del]

@[simp] lemma mem_transition_unlock {s : Set (AcFact F A C)} {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition AcAct.unlock s ↔ f ∈ s ∨ f = AcFact.key0 := by
  simp [ActionModel.transition, domain, actionModel, add, del, or_comm]

@[simp] lemma applicable_ask {x : RW} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.ask x) s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma applicable_unlock {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.unlock : AcAct F A C) s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma applicable_waitA_iff {x : RW} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.waitA x) s ↔ AcFact.key2 x ∈ s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

/-! ### The spliced memory phases -/

/-- The read handshake of a proof step with the read phase of the memory cell answering it
spliced in. -/
noncomputable def readPhase (S S' : Set F) (t : A ⊕ C) (vars : List F) : List (AcAct F A C) :=
  AcAct.ask RW.read :: (memRead S S' t vars ++ [AcAct.waitA RW.read])

/-- The write handshakes of a proof step with the write phases of the memory cells answering
them spliced in.  The number `w` is how many cells the step fills with its triple: `0` for the
last step of a plan, and in general one per later use of the triple. -/
noncomputable def writePhase (S S' : Set F) (t : A ⊕ C) (vars : List F) (w : ℕ) :
    List (AcAct F A C) :=
  (List.replicate w
    (AcAct.ask RW.write :: (memWrite S S' t vars ++ [AcAct.waitA RW.write]))).flatten

@[simp] lemma writePhase_zero (S S' : Set F) (t : A ⊕ C) (vars : List F) :
    writePhase (F := F) (A := A) (C := C) S S' t vars 0 = [] := by simp [writePhase]

lemma writePhase_succ (S S' : Set F) (t : A ⊕ C) (vars : List F) (w : ℕ) :
    writePhase (F := F) (A := A) (C := C) S S' t vars (w + 1) =
      (AcAct.ask RW.write :: (memWrite S S' t vars ++ [AcAct.waitA RW.write])) ++
        writePhase S S' t vars w := by
  simp [writePhase, List.replicate_succ]

lemma writePhase_one (S S' : Set F) (t : A ⊕ C) (vars : List F) :
    writePhase (F := F) (A := A) (C := C) S S' t vars 1 =
      AcAct.ask RW.write :: (memWrite S S' t vars ++ [AcAct.waitA RW.write]) := by
  simp [writePhase]

/-- A frame lemma for the read phase: it changes only the two read semaphores, the third and
fourth copies and the stored task name. -/
lemma mem_transitionSeq_readPhase_of_frame {S S' : Set F} {t : A ⊕ C}
    {s : Set (AcFact F A C)} {f : AcFact F A C}
    (h3 : ∀ v : F, f ≠ AcFact.pos v 3 ∧ f ≠ AcFact.neg v 3)
    (h4 : ∀ v : F, f ≠ AcFact.pos v 4 ∧ f ≠ AcFact.neg v 4)
    (ht : ∀ t' : A ⊕ C, f ≠ AcFact.task t')
    (hr1 : f ≠ AcFact.key1 RW.read) (hr2 : f ≠ AcFact.key2 RW.read) :
    (f ∈ (domain D vars bound).transitionSeq (readPhase S S' t vars) s ↔ f ∈ s) := by
  classical
  rw [readPhase, memRead]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    ActionModel.transitionSeq_nil]
  rw [mem_transition_waitA, mem_transition_doneA,
    unchanged_writesOf (D := D) (vars := vars) (bound := bound) (fun w _ => h3 w),
    unchanged_writesOf (D := D) (vars := vars) (bound := bound) (fun w _ => h4 w)]
  rw [mem_transition_setC, mem_transition_accept, mem_transition_ask]
  simp [hr1, hr2, ht]

/-- The state copies other than the third and the fourth survive a read phase. -/
lemma representsOn_readPhase_other {S S' T : Set F} {t : A ⊕ C} {i : Fin 5}
    (h3 : i ≠ 3) (h4 : i ≠ 4) {s : Set (AcFact F A C)} (h : RepresentsOn s i T vars) :
    RepresentsOn ((domain D vars bound).transitionSeq (readPhase S S' t vars) s) i T vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transitionSeq_readPhase_of_frame (D := D) (bound := bound)
      (fun w => ⟨by simp [h3], by simp⟩) (fun w => ⟨by simp [h4], by simp⟩)
      (fun t' => by simp) (by simp) (by simp),
    mem_transitionSeq_readPhase_of_frame (D := D) (bound := bound)
      (fun w => ⟨by simp, by simp [h3]⟩) (fun w => ⟨by simp, by simp [h4]⟩)
      (fun t' => by simp) (by simp) (by simp)]
  exact ⟨h1, h2⟩

/-- The key fact `key₁^R` is down after a read phase of a memory cell. -/
lemma key1_read_notMem_memRead (S S' : Set F) (t : A ⊕ C) (s : Set (AcFact F A C)) :
    (AcFact.key1 RW.read : AcFact F A C) ∉
      (domain D vars bound).transitionSeq (memRead S S' t vars) s := by
  classical
  rw [memRead]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    ActionModel.transitionSeq_nil]
  rw [mem_transition_doneA,
    unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (f := (AcFact.key1 RW.read : AcFact F A C)) (fun w _ => ⟨by simp, by simp⟩),
    unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (f := (AcFact.key1 RW.read : AcFact F A C)) (fun w _ => ⟨by simp, by simp⟩),
    mem_transition_setC, mem_transition_accept]
  simp

/-- **What a spliced read phase does.**  It is executable in every state, it installs the
triple `(S, t, S')` of the cell in the third and fourth copy and in the stored task name, and it
leaves both read semaphores down again. -/
theorem readPhase_spec (S S' : Set F) (t : A ⊕ C) (s : Set (AcFact F A C)) :
    (domain D vars bound).SeqApplicable (readPhase S S' t vars) s ∧
      RepresentsOn ((domain D vars bound).transitionSeq (readPhase S S' t vars) s) 3 S vars ∧
      RepresentsOn ((domain D vars bound).transitionSeq (readPhase S S' t vars) s) 4 S' vars ∧
      AcFact.task t ∈ (domain D vars bound).transitionSeq (readPhase S S' t vars) s ∧
      AcFact.key1 RW.read ∉ (domain D vars bound).transitionSeq (readPhase S S' t vars) s ∧
      AcFact.key2 RW.read ∉ (domain D vars bound).transitionSeq (readPhase S S' t vars) s := by
  classical
  set s₁ := (domain D vars bound).transition (AcAct.ask RW.read) s with hs₁
  have hkey : (AcFact.key1 RW.read : AcFact F A C) ∈ s₁ := by
    rw [hs₁, mem_transition_ask]; exact Or.inr rfl
  obtain ⟨hrep3, hrep4, htask, hkey2⟩ :=
    memRead_spec (D := D) (vars := vars) (bound := bound) (S := S) (S' := S') (t := t) (s := s₁)
  set s₂ := (domain D vars bound).transitionSeq (memRead S S' t vars) s₁ with hs₂
  have hexp : (domain D vars bound).transitionSeq (readPhase S S' t vars) s =
      (domain D vars bound).transition (AcAct.waitA RW.read) s₂ := by
    rw [readPhase, hs₂, hs₁]
    simp [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [readPhase, ActionModel.seqApplicable_cons, ActionModel.seqApplicable_append]
    refine ⟨applicable_ask, seqApplicable_memRead hkey, ?_⟩
    rw [← hs₂]
    simpa using hkey2
  · rw [hexp]
    intro v hv
    obtain ⟨h1, h2⟩ := hrep3 v hv
    rw [mem_transition_waitA, mem_transition_waitA]
    simpa using ⟨h1, h2⟩
  · rw [hexp]
    intro v hv
    obtain ⟨h1, h2⟩ := hrep4 v hv
    rw [mem_transition_waitA, mem_transition_waitA]
    simpa using ⟨h1, h2⟩
  · rw [hexp, mem_transition_waitA]
    exact ⟨htask, by simp⟩
  · rw [hexp, mem_transition_waitA]
    rintro ⟨hmem, -⟩
    exact key1_read_notMem_memRead (D := D) (bound := bound) S S' t s₁ hmem
  · rw [hexp, mem_transition_waitA]
    rintro ⟨-, hne⟩
    exact hne rfl

/-- A single write phase does not change the state at all: it lowers and raises the two write
semaphores and tests the copies. -/
theorem transitionSeq_writePhase_one {S S' : Set F} {t : A ⊕ C}
    {s : Set (AcFact F A C)} (h1 : AcFact.key1 RW.write ∉ s) (h2 : AcFact.key2 RW.write ∉ s) :
    (domain D vars bound).transitionSeq (writePhase S S' t vars 1) s = s := by
  classical
  rw [writePhase_one]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    ActionModel.transitionSeq_nil]
  ext f
  rw [mem_transition_waitA, mem_transitionSeq_memWrite, mem_transition_ask]
  constructor
  · rintro ⟨(⟨hf, hne⟩ | rfl), hne2⟩
    · rcases hf with hf | rfl
      · exact hf
      · exact absurd rfl hne
    · exact absurd rfl hne2
  · intro hf
    exact ⟨Or.inl ⟨Or.inl hf, fun hc => h1 (hc ▸ hf)⟩, fun hc => h2 (hc ▸ hf)⟩

/-- A write phase does not change the state at all, however many cells it fills. -/
theorem transitionSeq_writePhase {S S' : Set F} {t : A ⊕ C} {w : ℕ}
    {s : Set (AcFact F A C)} (h1 : AcFact.key1 RW.write ∉ s) (h2 : AcFact.key2 RW.write ∉ s) :
    (domain D vars bound).transitionSeq (writePhase S S' t vars w) s = s := by
  induction w generalizing s with
  | zero => simp
  | succ w ih =>
      rw [writePhase_succ, ActionModel.transitionSeq_append,
        show (domain D vars bound).transitionSeq
            (AcAct.ask RW.write :: (memWrite S S' t vars ++ [AcAct.waitA RW.write])) s = s from
          by rw [← writePhase_one]; exact transitionSeq_writePhase_one h1 h2]
      exact ih h1 h2

/-- A single write phase is executable as soon as the copies hold the triple of the cell. -/
theorem seqApplicable_writePhase_one {S S' : Set F} {t : A ⊕ C}
    {s : Set (AcFact F A C)} (h0 : RepresentsOn s 0 S vars) (h2 : RepresentsOn s 2 S' vars)
    (ht : AcFact.task t ∈ s) :
    (domain D vars bound).SeqApplicable (writePhase S S' t vars 1) s := by
  classical
  rw [writePhase_one, ActionModel.seqApplicable_cons, ActionModel.seqApplicable_append]
  set s₁ := (domain D vars bound).transition (AcAct.ask RW.write) s with hs₁
  have hmem : ∀ f : AcFact F A C, f ∈ s → f ∈ s₁ := by
    intro f hf
    rw [hs₁, mem_transition_ask]
    exact Or.inl hf
  have hw : (domain D vars bound).SeqApplicable (memWrite S S' t vars) s₁ := by
    rw [seqApplicable_memWrite_iff]
    refine ⟨by rw [hs₁, mem_transition_ask]; exact Or.inr rfl, ?_, ?_, hmem _ ht⟩
    · exact fun v hv => ⟨fun hx => hmem _ ((h0 v hv).1.2 hx),
        fun hx => hmem _ ((h0 v hv).2.2 hx)⟩
    · exact fun v hv => ⟨fun hx => hmem _ ((h2 v hv).1.2 hx),
        fun hx => hmem _ ((h2 v hv).2.2 hx)⟩
  refine ⟨applicable_ask, hw, ?_⟩
  simp only [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_nil, and_true,
    applicable_waitA_iff]
  exact mem_transitionSeq_memWrite.2 (Or.inr rfl)

/-- A write phase is executable as soon as the copies hold the triple of the cell, however many
cells it fills: filling a cell does not change the state. -/
theorem seqApplicable_writePhase {S S' : Set F} {t : A ⊕ C} {w : ℕ}
    {s : Set (AcFact F A C)} (hk1 : AcFact.key1 RW.write ∉ s) (hk2 : AcFact.key2 RW.write ∉ s)
    (h0 : RepresentsOn s 0 S vars) (h2 : RepresentsOn s 2 S' vars) (ht : AcFact.task t ∈ s) :
    (domain D vars bound).SeqApplicable (writePhase S S' t vars w) s := by
  induction w generalizing s with
  | zero => simp
  | succ w ih =>
      rw [writePhase_succ, ActionModel.seqApplicable_append]
      refine ⟨?_, ?_⟩
      · rw [← writePhase_one]; exact seqApplicable_writePhase_one h0 h2 ht
      · rw [show (domain D vars bound).transitionSeq
              (AcAct.ask RW.write :: (memWrite S S' t vars ++ [AcAct.waitA RW.write])) s = s from
            by rw [← writePhase_one]; exact transitionSeq_writePhase_one hk1 hk2]
        exact ih hk1 hk2 h0 h2 ht

/-! ### The two kinds of scheduled proof step -/

/-- The memory side of a write phase filling `w` cells: the write phases of the `w` cells,
one after the other. -/
noncomputable def memWrites (S S' : Set F) (t : A ⊕ C) (vars : List F) (w : ℕ) :
    List (AcAct F A C) := (List.replicate w (memWrite S S' t vars)).flatten

@[simp] lemma memWrites_zero (S S' : Set F) (t : A ⊕ C) (vars : List F) :
    memWrites (F := F) (A := A) (C := C) S S' t vars 0 = [] := by simp [memWrites]

lemma memWrites_succ (S S' : Set F) (t : A ⊕ C) (vars : List F) (w : ℕ) :
    memWrites (F := F) (A := A) (C := C) S S' t vars (w + 1) =
      memWrite S S' t vars ++ memWrites S S' t vars w := by
  simp [memWrites, List.replicate_succ]

/-- The proof-step side of a write phase filling `w` cells: `w` write requests. -/
def writeAsks (w : ℕ) : List (AcAct F A C) :=
  (List.replicate w ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten

@[simp] lemma writeAsks_zero : writeAsks (F := F) (A := A) (C := C) 0 = [] := by simp [writeAsks]

lemma writeAsks_succ (w : ℕ) :
    writeAsks (F := F) (A := A) (C := C) (w + 1) =
      [AcAct.ask RW.write, AcAct.waitA RW.write] ++ writeAsks w := by
  simp [writeAsks, List.replicate_succ]

/-- **A write phase is the interleaving of the write phases of the cells it fills with the
write requests of the proof step.** -/
lemma interleave_writePhase (S S' : Set F) (t : A ⊕ C) (vars : List F) (w : ℕ) :
    Interleave (memWrites S S' t vars w) (writeAsks w) (writePhase S S' t vars w) := by
  induction w with
  | zero => simp [Interleave.nil]
  | succ w ih =>
      rw [memWrites_succ, writeAsks_succ, writePhase_succ]
      have h1 : Interleave (memWrite S S' t vars)
          ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))
          (AcAct.ask RW.write :: (memWrite S S' t vars ++ [AcAct.waitA RW.write])) := by
        have := (Interleave.nil_left ([AcAct.ask RW.write] : List (AcAct F A C))).append_append
          (Interleave.append (memWrite S S' t vars)
            ([AcAct.waitA RW.write] : List (AcAct F A C)))
        simpa using this
      exact h1.append_append ih

/-- One **compound proof step** for the method `c ↦ x y`, with the read phases of the two cells
it reads and the write phases of the `w` cells it fills spliced into its handshakes. -/
noncomputable def compoundBlock (c : C) (x y : A ⊕ C) (S S'' S' : Set F)
    (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)) (vars : List F) (w : ℕ) :
    List (AcAct F A C) :=
  AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ readPhase S S'' x vars ++ e₁ ++ e₂ ++ [AcAct.preC x] ++
    readPhase S'' S' y vars ++ e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)] ++
    writePhase S S' (Sum.inr c) vars w ++ [AcAct.unlock])

/-- One **primitive proof step** for the operator `o`, with the write phases of the `w` cells
it fills spliced into its handshake. -/
noncomputable def primBlock (o : A) (S T : Set F) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C))
    (vars : List F) (w : ℕ) : List (AcAct F A C) :=
  AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++ [AcAct.setC (Sum.inl o)] ++
    writePhase S T (Sum.inl o) vars w ++ [AcAct.unlock])

/-- **A scheduled compound step is an interleaving of the memory phases with the actions of the
proof step itself.** -/
lemma interleave_compoundBlock (c : C) (x y : A ⊕ C) (S S'' S' : Set F)
    (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)) (vars : List F) (w : ℕ) :
    Interleave (memRead S S'' x vars ++ memRead S'' S' y vars ++
        memWrites S S' (Sum.inr c) vars w)
      (tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w)
      (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) := by
  classical
  have base : ∀ (a₀ a₁ a₂ m₁ m₂ m₃ z₃ : List (AcAct F A C)) (a₃ : List (AcAct F A C)),
      Interleave m₃ a₃ z₃ →
      Interleave (m₁ ++ m₂ ++ m₃) (a₀ ++ a₁ ++ a₂ ++ a₃)
        (a₀ ++ (m₁ ++ a₁) ++ (m₂ ++ a₂) ++ z₃) := by
    intro a₀ a₁ a₂ m₁ m₂ m₃ z₃ a₃ h₃
    have h := ((Interleave.nil_left a₀).append_append (Interleave.append m₁ a₁)).append_append
      ((Interleave.append m₂ a₂).append_append h₃)
    simpa [List.append_assoc] using h
  have h₃ : Interleave (memWrites S S' (Sum.inr c) vars w)
      (writeAsks (F := F) (A := A) (C := C) w ++ [AcAct.unlock])
      (writePhase S S' (Sum.inr c) vars w ++ [AcAct.unlock]) := by
    simpa using (interleave_writePhase S S' (Sum.inr c) vars w).append_append
      (Interleave.nil_left [AcAct.unlock])
  have h := base (AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ [AcAct.ask RW.read]))
    ([AcAct.waitA RW.read] ++ e₁ ++ e₂ ++ [AcAct.preC x, AcAct.ask RW.read])
    ([AcAct.waitA RW.read] ++ e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)])
    (memRead S S'' x vars) (memRead S'' S' y vars) (memWrites S S' (Sum.inr c) vars w)
    (writePhase S S' (Sum.inr c) vars w ++ [AcAct.unlock])
    (writeAsks (F := F) (A := A) (C := C) w ++ [AcAct.unlock]) h₃
  simpa [compoundBlock, tupleCompoundSeq, readPhase, writeAsks, List.append_assoc] using h

/-- **A scheduled primitive step is an interleaving of the write phases with the actions of the
proof step itself.** -/
lemma interleave_primBlock (o : A) (S T : Set F) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C))
    (vars : List F) (w : ℕ) :
    Interleave (memWrites S T (Sum.inl o) vars w)
      (tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w)
      (primBlock o S T g₁ g₂ g₃ e₁ e₂ vars w) := by
  classical
  have h₃ : Interleave (memWrites S T (Sum.inl o) vars w)
      (writeAsks (F := F) (A := A) (C := C) w ++ [AcAct.unlock])
      (writePhase S T (Sum.inl o) vars w ++ [AcAct.unlock]) := by
    simpa using (interleave_writePhase S T (Sum.inl o) vars w).append_append
      (Interleave.nil_left [AcAct.unlock])
  have h := (Interleave.nil_left
      (AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++
        [AcAct.setC (Sum.inl o)]))).append_append h₃
  simpa [primBlock, tuplePrimitiveSeq, writeAsks, List.append_assoc] using h

/-! ### Executing a scheduled proof step -/

@[simp] lemma applicable_lock_iff {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.lock : AcAct F A C) s ↔ AcFact.key0 ∈ s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

/-- A representation survives the `unlock` action. -/
lemma representsOn_transition_unlock {i : Fin 5} {T : Set F} {s : Set (AcFact F A C)}
    (h : RepresentsOn s i T vars) :
    RepresentsOn ((domain D vars bound).transition AcAct.unlock s) i T vars := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transition_unlock, mem_transition_unlock]
  simpa using ⟨h1, h2⟩

/-- **A compound proof step can be scheduled.**  In a clean state — the lock free and no
handshake pending — the actions of a compound proof step for the method `c ↦ x y`, with the read
phases of the cells holding `(S, x, S'')` and `(S'', y, S')` spliced into its two read
handshakes, are executable; they leave the state clean again, with the first copy holding `S`,
the third copy holding `S'` and the stored task name `c`. -/
theorem exists_compoundBlock (c : C) (x y : A ⊕ C)
    (S S'' S' : Set F) (w : ℕ) {s : Set (AcFact F A C)} (hs : Clean s) :
    ∃ g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C),
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄ ∧
      (domain D vars bound).SeqApplicable
        (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) s ∧
      Clean ((domain D vars bound).transitionSeq
        (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) s) ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) s) 0 S vars ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) s) 2 S' vars ∧
      AcFact.task (Sum.inr c) ∈ (domain D vars bound).transitionSeq
        (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) s := by
  classical
  obtain ⟨hk0, hkeys⟩ := hs
  set t₀ := (domain D vars bound).transition AcAct.lock s with ht₀
  obtain ⟨g₁, hg₁, happ₁, hunch₁, hrep₁⟩ :=
    exists_yieldSeq_SEL (D := D) (vars := vars) (bound := bound) 0 S t₀
  set t₁ := (domain D vars bound).transitionSeq g₁ t₀ with ht₁
  obtain ⟨g₂, hg₂, happ₂, hunch₂, hrep₂⟩ :=
    exists_yieldSeq_SEL (D := D) (vars := vars) (bound := bound) 1 S'' t₁
  set t₂ := (domain D vars bound).transitionSeq g₂ t₁ with ht₂
  obtain ⟨g₃, hg₃, happ₃, hunch₃, hrep₃⟩ :=
    exists_yieldSeq_SEL (D := D) (vars := vars) (bound := bound) 2 S' t₂
  set t₃ := (domain D vars bound).transitionSeq g₃ t₂ with ht₃
  have hrep₀₃ : RepresentsOn t₃ 0 S vars :=
    representsOn_of_unchangedOutside (by decide)
      (representsOn_of_unchangedOutside (by decide) hrep₁ hunch₂) hunch₃
  have hrep₁₃ : RepresentsOn t₃ 1 S'' vars :=
    representsOn_of_unchangedOutside (by decide) hrep₂ hunch₃
  have hkeys₃ : KeysAgree s t₃ := by
    have k0 : KeysAgree s t₀ :=
      keysAgree_transition_lock (D := D) (vars := vars) (bound := bound) s
    have k1 : KeysAgree t₀ t₁ := keysAgree_of_unchangedOutside hunch₁
    have k2 : KeysAgree t₁ t₂ := keysAgree_of_unchangedOutside hunch₂
    have k3 : KeysAgree t₂ t₃ := keysAgree_of_unchangedOutside hunch₃
    exact k0.trans (k1.trans (k2.trans k3))
  have hW₁₃ : (AcFact.key1 RW.write : AcFact F A C) ∉ t₃ := fun hmem =>
    (hkeys RW.write).1 ((hkeys₃ RW.write).1.1 hmem)
  have hW₂₃ : (AcFact.key2 RW.write : AcFact F A C) ∉ t₃ := fun hmem =>
    (hkeys RW.write).2 ((hkeys₃ RW.write).2.1 hmem)
  -- the first read phase
  obtain ⟨happR₁, hr3, hr4, htaskx, -, -⟩ :=
    readPhase_spec (D := D) (bound := bound) S S'' x t₃
  set t₄ := (domain D vars bound).transitionSeq (readPhase S S'' x vars) t₃ with ht₄
  have hrep₀₄ : RepresentsOn t₄ 0 S vars :=
    representsOn_readPhase_other (by decide) (by decide) hrep₀₃
  have hrep₁₄ : RepresentsOn t₄ 1 S'' vars :=
    representsOn_readPhase_other (by decide) (by decide) hrep₁₃
  have hrep₂₄ : RepresentsOn t₄ 2 S' vars :=
    representsOn_readPhase_other (by decide) (by decide) hrep₃
  have hW₁₄ : (AcFact.key1 RW.write : AcFact F A C) ∉ t₄ := by
    rw [ht₄, mem_transitionSeq_readPhase_of_frame (D := D) (bound := bound)
      (fun v => ⟨by simp, by simp⟩) (fun v => ⟨by simp, by simp⟩) (fun t' => by simp)
      (by simp) (by simp)]
    exact hW₁₃
  have hW₂₄ : (AcFact.key2 RW.write : AcFact F A C) ∉ t₄ := by
    rw [ht₄, mem_transitionSeq_readPhase_of_frame (D := D) (bound := bound)
      (fun v => ⟨by simp, by simp⟩) (fun v => ⟨by simp, by simp⟩) (fun t' => by simp)
      (by simp) (by simp)]
    exact hW₂₃
  obtain ⟨e₁, he₁, happe₁⟩ :=
    (eq_executable_iff (D := D) (bound := bound) hrep₀₄ hr3).2 (fun _ _ => Iff.rfl)
  obtain ⟨e₂, he₂, happe₂⟩ :=
    (eq_executable_iff (D := D) (bound := bound) hrep₁₄ hr4).2 (fun _ _ => Iff.rfl)
  -- the second read phase
  obtain ⟨happR₂, hr3', hr4', htasky, hkR1', hkR2'⟩ :=
    readPhase_spec (D := D) (bound := bound) S'' S' y t₄
  set t₅ := (domain D vars bound).transitionSeq (readPhase S'' S' y vars) t₄ with ht₅
  have hrep₀₅ : RepresentsOn t₅ 0 S vars :=
    representsOn_readPhase_other (by decide) (by decide) hrep₀₄
  have hrep₁₅ : RepresentsOn t₅ 1 S'' vars :=
    representsOn_readPhase_other (by decide) (by decide) hrep₁₄
  have hrep₂₅ : RepresentsOn t₅ 2 S' vars :=
    representsOn_readPhase_other (by decide) (by decide) hrep₂₄
  have hW₁₅ : (AcFact.key1 RW.write : AcFact F A C) ∉ t₅ := by
    rw [ht₅, mem_transitionSeq_readPhase_of_frame (D := D) (bound := bound)
      (fun v => ⟨by simp, by simp⟩) (fun v => ⟨by simp, by simp⟩) (fun t' => by simp)
      (by simp) (by simp)]
    exact hW₁₄
  have hW₂₅ : (AcFact.key2 RW.write : AcFact F A C) ∉ t₅ := by
    rw [ht₅, mem_transitionSeq_readPhase_of_frame (D := D) (bound := bound)
      (fun v => ⟨by simp, by simp⟩) (fun v => ⟨by simp, by simp⟩) (fun t' => by simp)
      (by simp) (by simp)]
    exact hW₂₄
  obtain ⟨e₃, he₃, happe₃⟩ :=
    (eq_executable_iff (D := D) (bound := bound) hrep₁₅ hr3').2 (fun _ _ => Iff.rfl)
  obtain ⟨e₄, he₄, happe₄⟩ :=
    (eq_executable_iff (D := D) (bound := bound) hrep₂₅ hr4').2 (fun _ _ => Iff.rfl)
  -- storing the task name
  set t₆ := (domain D vars bound).transition (AcAct.setC (Sum.inr c)) t₅ with ht₆
  have hrep₀₆ : RepresentsOn t₆ 0 S vars := representsOn_transition_setC hrep₀₅
  have hrep₂₆ : RepresentsOn t₆ 2 S' vars := representsOn_transition_setC hrep₂₅
  have htask₆ : (AcFact.task (Sum.inr c) : AcFact F A C) ∈ t₆ :=
    mem_transition_setC.2 (Or.inr rfl)
  have hkeys₆ : ∀ z : RW, (AcFact.key1 z : AcFact F A C) ∉ t₆ ∧
      (AcFact.key2 z : AcFact F A C) ∉ t₆ := by
    intro z
    have hstep : ∀ f : AcFact F A C, (∀ t' : A ⊕ C, f ≠ AcFact.task t') → f ∈ t₆ → f ∈ t₅ := by
      intro f hf hmem
      rw [ht₆, mem_transition_setC] at hmem
      rcases hmem with ⟨hmem, -⟩ | hmem
      · exact hmem
      · exact absurd hmem (hf _)
    cases z with
    | read =>
        exact ⟨fun hmem => hkR1' (hstep _ (fun t' => by simp) hmem),
          fun hmem => hkR2' (hstep _ (fun t' => by simp) hmem)⟩
    | write =>
        exact ⟨fun hmem => hW₁₅ (hstep _ (fun t' => by simp) hmem),
          fun hmem => hW₂₅ (hstep _ (fun t' => by simp) hmem)⟩
  -- the write phase and the unlock
  have happW : (domain D vars bound).SeqApplicable
      (writePhase S S' (Sum.inr c) vars w) t₆ :=
    seqApplicable_writePhase (hkeys₆ RW.write).1 (hkeys₆ RW.write).2 hrep₀₆ hrep₂₆ htask₆
  have htrW : (domain D vars bound).transitionSeq (writePhase S S' (Sum.inr c) vars w) t₆ = t₆ :=
    transitionSeq_writePhase (hkeys₆ RW.write).1 (hkeys₆ RW.write).2
  -- the three spliced phases are treated as opaque blocks from here on
  obtain ⟨R₁, hR₁⟩ : ∃ R : List (AcAct F A C), readPhase S S'' x vars = R := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R : List (AcAct F A C), readPhase S'' S' y vars = R := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ R : List (AcAct F A C), writePhase S S' (Sum.inr c) vars w = R := ⟨_, rfl⟩
  rw [hR₁] at happR₁ ht₄
  rw [hR₂] at happR₂ ht₅
  rw [hW] at happW htrW
  have hexp : (domain D vars bound).transitionSeq
      (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) s =
      (domain D vars bound).transition AcAct.unlock t₆ := by
    rw [compoundBlock, hR₁, hR₂, hW]
    simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
      ActionModel.transitionSeq_nil, transitionSeq_yieldSeq_EQ he₁, transitionSeq_yieldSeq_EQ he₂,
      transitionSeq_yieldSeq_EQ he₃, transitionSeq_yieldSeq_EQ he₄, transition_preC]
    rw [← ht₀, ← ht₁, ← ht₂, ← ht₃, ← ht₄, ← ht₅, ← ht₆, htrW]
  have happ : (domain D vars bound).SeqApplicable
      (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w) s := by
    rw [compoundBlock, hR₁, hR₂, hW]
    simp only [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_append,
      ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
      ActionModel.transitionSeq_nil, ActionModel.seqApplicable_nil, and_true,
      transitionSeq_yieldSeq_EQ he₁, transitionSeq_yieldSeq_EQ he₂,
      transitionSeq_yieldSeq_EQ he₃, transitionSeq_yieldSeq_EQ he₄, transition_preC]
    rw [← ht₀, ← ht₁, ← ht₂, ← ht₃, ← ht₄, ← ht₅, ← ht₆]
    and_intros
    exacts [applicable_lock_iff.2 hk0, happ₁, happ₂, happ₃, happR₁, happe₁, happe₂,
      applicable_preC_iff.2 htaskx, happR₂, happe₃, happe₄, applicable_preC_iff.2 htasky,
      applicable_setC, happW, applicable_unlock]
  refine ⟨g₁, g₂, g₃, e₁, e₂, e₃, e₄, hg₁, hg₂, hg₃, he₁, he₂, he₃, he₄, happ, ?_, ?_, ?_, ?_⟩
  · rw [hexp]
    refine ⟨mem_transition_unlock.2 (Or.inr rfl), fun z => ⟨?_, ?_⟩⟩
    · rw [mem_transition_unlock]
      rintro (hmem | hc)
      · exact (hkeys₆ z).1 hmem
      · simp at hc
    · rw [mem_transition_unlock]
      rintro (hmem | hc)
      · exact (hkeys₆ z).2 hmem
      · simp at hc
  · rw [hexp]; exact representsOn_transition_unlock hrep₀₆
  · rw [hexp]; exact representsOn_transition_unlock hrep₂₆
  · rw [hexp, mem_transition_unlock]; exact Or.inl htask₆

/-- The actions of a scheduled primitive step, split into the part analysed in
`HTN.ToAc.exists_primStep_prefix`, the write phase and the `unlock`. -/
lemma primBlock_eq (o : A) (S T : Set F) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C))
    (vars : List F) (w : ℕ) :
    primBlock o S T g₁ g₂ g₃ e₁ e₂ vars w =
      primStepPrefix o g₁ g₂ g₃ e₁ e₂ ++ writePhase S T (Sum.inl o) vars w ++
        [AcAct.unlock] := by
  simp [primBlock, primStepPrefix, List.append_assoc]

/-- **A primitive proof step can be scheduled.**  In a clean state, the actions of a primitive
proof step for an operator `o` applicable in `S`, with the write phase of the cell it fills
spliced into its write handshake, are executable; they leave the state clean again, with the
first copy holding `S`, the third copy holding `γ(S, o)` and the stored task name `o`. -/
theorem exists_primBlock (hvars : ∀ v : F, v ∈ vars) {o : A} {S : Set F}
    (hprec : D.Applicable o S) (hdisj : Disjoint (D.add o) (D.del o)) (w : ℕ)
    {s : Set (AcFact F A C)} (hs : Clean s) :
    ∃ g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C),
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂ ∧
      (domain D vars bound).SeqApplicable
        (primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars w) s ∧
      Clean ((domain D vars bound).transitionSeq
        (primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars w) s) ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars w) s) 0 S vars ∧
      RepresentsOn ((domain D vars bound).transitionSeq
        (primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars w) s) 2 (D.transition o S) vars ∧
      AcFact.task (Sum.inl o) ∈ (domain D vars bound).transitionSeq
        (primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars w) s := by
  classical
  obtain ⟨hk0, hkeys⟩ := hs
  obtain ⟨g₁, g₂, g₃, e₁, e₂, s', hg₁, hg₂, hg₃, he₁, he₂, happP, hs'eq, hrep0, hrep2,
    htask, hkeys', -⟩ :=
    exists_primStep_prefix (D := D) (vars := vars) (bound := bound) hvars hprec hdisj hk0
  have hkeys'' : ∀ z : RW, (AcFact.key1 z : AcFact F A C) ∉ s' ∧
      (AcFact.key2 z : AcFact F A C) ∉ s' :=
    fun z => ⟨fun hmem => (hkeys z).1 ((hkeys' z).1.1 hmem),
      fun hmem => (hkeys z).2 ((hkeys' z).2.1 hmem)⟩
  have happW : (domain D vars bound).SeqApplicable
      (writePhase S (D.transition o S) (Sum.inl o) vars w) s' :=
    seqApplicable_writePhase (hkeys'' RW.write).1 (hkeys'' RW.write).2 hrep0 hrep2 htask
  have htrW : (domain D vars bound).transitionSeq
      (writePhase S (D.transition o S) (Sum.inl o) vars w) s' = s' :=
    transitionSeq_writePhase (hkeys'' RW.write).1 (hkeys'' RW.write).2
  have hexp : (domain D vars bound).transitionSeq
      (primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars w) s =
      (domain D vars bound).transition AcAct.unlock s' := by
    rw [primBlock_eq]
    simp only [ActionModel.transitionSeq_append, ActionModel.transitionSeq_cons,
      ActionModel.transitionSeq_nil]
    rw [← hs'eq, htrW]
  refine ⟨g₁, g₂, g₃, e₁, e₂, hg₁, hg₂, hg₃, he₁, he₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [primBlock_eq]
    simp only [ActionModel.seqApplicable_append, ActionModel.seqApplicable_cons,
      ActionModel.seqApplicable_nil, ActionModel.transitionSeq_append, and_true]
    rw [← hs'eq, htrW]
    exact ⟨⟨happP, happW⟩, applicable_unlock⟩
  · rw [hexp]
    refine ⟨mem_transition_unlock.2 (Or.inr rfl), fun z => ⟨?_, ?_⟩⟩
    · rw [mem_transition_unlock]
      rintro (hmem | hc)
      · exact (hkeys'' z).1 hmem
      · simp at hc
    · rw [mem_transition_unlock]
      rintro (hmem | hc)
      · exact (hkeys'' z).2 hmem
      · simp at hc
  · rw [hexp]; exact representsOn_transition_unlock hrep0
  · rw [hexp]; exact representsOn_transition_unlock hrep2
  · rw [hexp, mem_transition_unlock]; exact Or.inl htask

/-! ### Combining parallel copies -/

/-- One copy of a sequential task is a refinement of `𝔠^1`. -/
lemma gridYield_replicate_one {c : AcTask F A C} (hc : IsSeqTask c)
    {as : List (AcAct F A C)} (h : (domain D vars bound).YieldSeq [Sum.inr c] as) :
    (domain D vars bound).GridYield (List.replicate 1 [Sum.inr c]) as :=
  (gridYield_replicate_succ hc).2 ⟨as, [], h, by simp, by simpa using Interleave.nil_right as⟩

/-- **Refinements of parallel copies compose.**  An interleaving of a refinement of `m₁` copies
with a refinement of `m₂` copies is a refinement of `m₁ + m₂` copies. -/
lemma gridYield_replicate_add {c : AcTask F A C} (hc : IsSeqTask c) :
    ∀ (m₁ m₂ : ℕ) {as₁ as₂ as : List (AcAct F A C)},
      (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr c]) as₁ →
      (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr c]) as₂ →
      Interleave as₁ as₂ as →
      (domain D vars bound).GridYield (List.replicate (m₁ + m₂) [Sum.inr c]) as := by
  intro m₁
  induction m₁ with
  | zero =>
      intro m₂ as₁ as₂ as h₁ h₂ hint
      rw [gridYield_replicate_zero] at h₁
      subst h₁
      rw [hint.eq_of_nil_left]
      simpa using h₂
  | succ m ih =>
      intro m₂ as₁ as₂ as h₁ h₂ hint
      obtain ⟨u, v, hu, hv, huv⟩ := (gridYield_replicate_succ hc).1 h₁
      obtain ⟨w, hw₁, hw₂⟩ := huv.assoc hint
      rw [show m + 1 + m₂ = (m + m₂) + 1 from by omega]
      exact (gridYield_replicate_succ hc).2 ⟨u, w, hu, ih m₂ hv h₂ hw₁, hw₂⟩

/-! ### From a derivation to a plan -/

/-- **The scheduling theorem.**  Every derivation of the proof-tuple calculus can be scheduled:
there is a number `N` of proof steps such that, as soon as the compiled problem has at least `N`
memory cells and `N` proof steps available, the derivation of `(S, x, S')` is executed by a
block of actions which

* is an interleaving of a refinement of some parallel memory cells (together with, if `b`, the
  write phase of one further cell, the one holding `(S, x, S')` itself) with a refinement of
  some parallel proof steps,
* is executable in every clean state and leaves the state clean again,
* and leaves the first copy holding `S`, the third copy holding `S'` and the stored task
  name `x`.

The source domain is assumed to be binary: every method has exactly two subtasks (the compiled
`TUPLE` task has methods for those and for the operators only). -/
theorem exists_scheduled_blocks (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ x y, xs = [x, y])
    {S S' : Set F} {x : A ⊕ C} (h : D.Provable S x S') :
    ∃ N : ℕ, ∀ bnd : ℕ, N ≤ bnd → ∀ (b : Bool) (s : Set (AcFact F A C)), Clean s →
      ∃ (m k : ℕ) (X tupP blk : List (AcAct F A C)), m + 1 ≤ N ∧ k ≤ N ∧
        (domain D vars bnd).GridYield (List.replicate m [Sum.inr AcTask.MEM]) X ∧
        (domain D vars bnd).GridYield (List.replicate k [Sum.inr AcTask.TUPLE]) tupP ∧
        Interleave (X ++ (if b then memWrite S S' x vars else [])) tupP blk ∧
        (domain D vars bnd).SeqApplicable blk s ∧
        Clean ((domain D vars bnd).transitionSeq blk s) ∧
        RepresentsOn ((domain D vars bnd).transitionSeq blk s) 0 S vars ∧
        RepresentsOn ((domain D vars bnd).transitionSeq blk s) 2 S' vars ∧
        AcFact.task x ∈ (domain D vars bnd).transitionSeq blk s := by
  classical
  induction h with
  | @prim o S hprec =>
      refine ⟨1, fun bnd hbnd b s hs => ?_⟩
      obtain ⟨g₁, g₂, g₃, e₁, e₂, hg₁, hg₂, hg₃, he₁, he₂, happ, hclean, hrep0, hrep2, htask⟩ :=
        exists_primBlock (D := D) (vars := vars) (bound := bnd) hvars hprec (hdisj o)
          (if b then 1 else 0) hs
      refine ⟨0, 1, [], tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ (if b then 1 else 0),
        primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars (if b then 1 else 0),
        le_refl 1, le_refl 1,
        by simp, ?_, ?_, happ, hclean, hrep0, hrep2, htask⟩
      · refine gridYield_replicate_one isSeqTask_TUPLE
          (yieldSeq_TUPLE_of_primitive ?_ hg₁ hg₂ hg₃ he₁ he₂)
        cases b with
        | false => simp
        | true => simp; omega
      · cases b with
        | false =>
            simpa [memWrites] using
              interleave_primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars 0
        | true =>
            simpa [memWrites] using
              interleave_primBlock o S (D.transition o S) g₁ g₂ g₃ e₁ e₂ vars 1
  | @zero c S hbody => exact absurd (hbin c [] hbody) (by simp)
  | @one c z S S' hbody _ _ => exact absurd (hbin c [z] hbody) (by simp)
  | @two c z w S S'' S' hbody _ _ ihx ihy =>
      obtain ⟨Nx, hNx⟩ := ihx
      obtain ⟨Ny, hNy⟩ := ihy
      refine ⟨Nx + Ny + 1, fun bnd hbnd b s hs => ?_⟩
      obtain ⟨m₁, k₁, X₁, T₁, B₁, hm₁, hk₁, hX₁, hT₁, hint₁, happ₁, hclean₁, -, -, -⟩ :=
        hNx bnd (by omega) true s hs
      simp only [if_pos] at hint₁
      set s₁ := (domain D vars bnd).transitionSeq B₁ s with hs₁
      obtain ⟨m₂, k₂, X₂, T₂, B₂, hm₂, hk₂, hX₂, hT₂, hint₂, happ₂, hclean₂, -, -, -⟩ :=
        hNy bnd (by omega) true s₁ hclean₁
      simp only [if_pos] at hint₂
      set s₂ := (domain D vars bnd).transitionSeq B₂ s₁ with hs₂
      obtain ⟨g₁, g₂, g₃, e₁, e₂, e₃, e₄, hg₁, hg₂, hg₃, he₁, he₂, he₃, he₄,
        happ₃, hclean₃, hrep0, hrep2, htask⟩ :=
        exists_compoundBlock (D := D) (vars := vars) (bound := bnd) c z w S S'' S'
          (if b then 1 else 0) hclean₂
      refine ⟨m₁ + m₂ + 2, k₁ + k₂ + 1,
        X₁ ++ memWrite S S'' z vars ++ X₂ ++ memWrite S'' S' w vars ++ memRead S S'' z vars ++
          memRead S'' S' w vars,
        T₁ ++ T₂ ++ tupleCompoundSeq c z w g₁ g₂ g₃ e₁ e₂ e₃ e₄ (if b then 1 else 0),
        B₁ ++ B₂ ++ compoundBlock c z w S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars
          (if b then 1 else 0),
        by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- the memory cells
        have hcellA : (domain D vars bnd).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)]
            (memWrite S S'' z vars ++ memRead S S'' z vars) := yieldSeq_MEM_memPhases _ _ _
        have hcellB : (domain D vars bnd).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)]
            (memWrite S'' S' w vars ++ memRead S'' S' w vars) := yieldSeq_MEM_memPhases _ _ _
        have hXX : (domain D vars bnd).GridYield
            (List.replicate (m₁ + m₂) [Sum.inr (AcTask.MEM : AcTask F A C)]) (X₁ ++ X₂) :=
          gridYield_replicate_add isSeqTask_MEM m₁ m₂ hX₁ hX₂ (Interleave.append _ _)
        have hY : (domain D vars bnd).GridYield
            (List.replicate (m₁ + m₂ + 1) [Sum.inr (AcTask.MEM : AcTask F A C)])
            (X₁ ++ X₂ ++ (memWrite S'' S' w vars ++ memRead S'' S' w vars)) :=
          gridYield_replicate_add isSeqTask_MEM (m₁ + m₂) 1 hXX
            (gridYield_replicate_one isSeqTask_MEM hcellB) (Interleave.append _ _)
        have hint : Interleave (memWrite S S'' z vars ++ memRead S S'' z vars)
            (X₁ ++ X₂ ++ (memWrite S'' S' w vars ++ memRead S'' S' w vars))
            (X₁ ++ memWrite S S'' z vars ++ X₂ ++ memWrite S'' S' w vars ++
              memRead S S'' z vars ++ memRead S'' S' w vars) := by
          have hb := ((Interleave.nil_left X₁).append_append
            (Interleave.append (memWrite S S'' z vars)
              (X₂ ++ memWrite S'' S' w vars))).append_append
            (Interleave.append (memRead S S'' z vars) (memRead S'' S' w vars))
          simpa [List.append_assoc] using hb
        have := gridYield_replicate_add isSeqTask_MEM 1 (m₁ + m₂ + 1)
          (gridYield_replicate_one isSeqTask_MEM hcellA) hY hint
        have he : 1 + (m₁ + m₂ + 1) = m₁ + m₂ + 2 := by omega
        rwa [he] at this
      · -- the proof steps
        have hstep : (domain D vars bnd).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)]
            (tupleCompoundSeq c z w g₁ g₂ g₃ e₁ e₂ e₃ e₄ (if b then 1 else 0)) := by
          refine yieldSeq_TUPLE_of_compound hbody ?_ hg₁ hg₂ hg₃ he₁ he₂ he₃ he₄
          cases b with
        | false => simp
        | true => simp; omega
        have hTT : (domain D vars bnd).GridYield
            (List.replicate (k₁ + k₂) [Sum.inr (AcTask.TUPLE : AcTask F A C)]) (T₁ ++ T₂) :=
          gridYield_replicate_add isSeqTask_TUPLE k₁ k₂ hT₁ hT₂ (Interleave.append _ _)
        exact gridYield_replicate_add isSeqTask_TUPLE (k₁ + k₂) 1 hTT
          (gridYield_replicate_one isSeqTask_TUPLE hstep) (Interleave.append _ _)
      · -- the interleaving
        have hb := (hint₁.append_append hint₂).append_append
          (interleave_compoundBlock c z w S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars
            (if b then 1 else 0))
        cases b <;> simpa [memWrites, List.append_assoc] using hb
      · -- executability
        rw [ActionModel.seqApplicable_append, ActionModel.seqApplicable_append,
          ActionModel.transitionSeq_append]
        exact ⟨⟨happ₁, happ₂⟩, happ₃⟩
      all_goals
        rw [ActionModel.transitionSeq_append, ActionModel.transitionSeq_append, ← hs₁, ← hs₂]
      · exact hclean₃
      · exact hrep0
      · exact hrep2
      · exact htask

/-! ### The repaired compiled problem and the completeness theorem -/

/-- The **repaired** compiled problem instance.  It differs from `HTN.ToAc.instance_` only in
its goal: the answer is read off the copies that the last proof step guesses itself (the first
copy for the initial state and the third copy for the goal), not off the copies that a memory
cell writes.  The negative facts `neg v 0` for the facts outside the initial state are part of
the goal so that the first copy is pinned down exactly, and not merely a superset of `Q.init`.

With the goal printed in the draft — `pos v 3` for the initial state and `pos v 4` for the goal
— the answer does not seem to be readable at the end of a plan: the third and fourth copies are
written only by the read phase of a memory cell, which runs inside the read handshake of a proof
step, and the `setC` of that step then overwrites the stored task name that the goal also asks
for.  (That the printed goal is unreachable is an observation about the construction; it is not
formalised here, and `HTN.ToAc.instance_` is left untouched.) -/
def instance' (Q : Instance F A C I) (tI0 : C) (vars : List F) :
    Instance (AcFact F A C) (AcAct F A C) (AcTask F A C) (ℕ × ℕ) where
  init := {AcFact.key0} ∪ {f | ∃ (v : F) (i : Fin 5), f = AcFact.neg v i}
  goal := (fun v => AcFact.pos v 0) '' Q.init ∪
    (fun v => AcFact.neg v 0) '' {v | v ∈ vars ∧ v ∉ Q.init} ∪
    (fun v => AcFact.pos v 2) '' Q.goal ∪ {AcFact.task (Sum.inr tI0)}
  tnI := TaskNetwork.seq [Sum.inr AcTask.tI]

/-- The compiled problem with the repaired goal. -/
def problem' (D : Domain F A C I) (Q : Instance F A C I) (vars : List F) (bound : ℕ)
    (tI0 : C) : Problem (AcFact F A C) (AcAct F A C) (AcTask F A C) (ℕ × ℕ) :=
  (domain D vars bound).mkProblem (instance' Q tI0 vars)

lemma clean_init (Q : Instance F A C I) (tI0 : C) :
    Clean (F := F) (A := A) (C := C) (instance' Q tI0 vars).init := by
  refine ⟨Or.inl rfl, fun z => ⟨?_, ?_⟩⟩ <;>
    rintro (hc | ⟨v, i, hc⟩) <;> simp_all

/-- **Completeness of the compilation.**  If the proof-tuple calculus derives `(s₀, t_I, S')`
for a state `S'` satisfying the goal of the source problem — equivalently, by
`HTN.Domain.provable_iff_yield`, if the initial task of the source problem can be refined into a
plan — then the compiled problem is solvable, as soon as it provides enough memory cells and
proof steps. -/
theorem solvable_problem'_of_provable (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ x y, xs = [x, y])
    {Q : Instance F A C I} {tI0 : C} {S' : Set F}
    (hprov : D.Provable Q.init (Sum.inr tI0) S') (hgoal : Q.goal ⊆ S') :
    ∃ N : ℕ, ∀ bnd : ℕ, N ≤ bnd → (problem' D Q vars bnd tI0).Solvable := by
  classical
  obtain ⟨N, hN⟩ := exists_scheduled_blocks (vars := vars) hvars hdisj hbin hprov
  refine ⟨N, fun bnd hbnd => ?_⟩
  obtain ⟨m, k, X, tupP, blk, hm, hk, hX, htupP, hint, happ, -, hrep0, hrep2, htask⟩ :=
    hN bnd hbnd false _ (clean_init (vars := vars) Q tI0)
  simp only [Bool.false_eq_true, if_false, List.append_nil] at hint
  refine Problem.solvable_iff_netYield.2 ⟨blk, ?_, happ, ?_⟩
  · exact (netYield_tnI_iff (D := D) (vars := vars) (bound := bnd) (Q := Q) (tI0 := tI0)).2
      ⟨m, k, X, tupP, by omega, hk.trans hbnd, hX, htupP, hint⟩
  · rintro f (((⟨v, hv, rfl⟩ | ⟨v, ⟨hv, hnv⟩, rfl⟩) | ⟨v, hv, rfl⟩) | rfl)
    · exact (hrep0 v (hvars v)).1.2 hv
    · exact (hrep0 v (hvars v)).2.2 hnv
    · exact (hrep2 v (hvars v)).1.2 (hgoal hv)
    · exact htask

/-- **Completeness of the compilation, in terms of the source problem.**  If the initial
compound task `t_I` of the source problem can be refined into an action sequence that is
executable in the initial state and reaches the goal, then the compiled problem is solvable as
soon as it provides enough memory cells and proof steps. -/
theorem solvable_problem'_of_yield (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ x y, xs = [x, y])
    {Q : Instance F A C I} {tI0 : C} {as : List A} (hy : D.Yield (Sum.inr tI0) as)
    (happ : D.SeqApplicable as Q.init) (hg : Q.goal ⊆ D.transitionSeq as Q.init) :
    ∃ N : ℕ, ∀ bnd : ℕ, N ≤ bnd → (problem' D Q vars bnd tI0).Solvable :=
  solvable_problem'_of_provable hvars hdisj hbin (Domain.provable_of_yield hy happ) hg

end ToAc

end HTN
