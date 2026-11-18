import HtnPlanning.Core.PrefixSum
import HtnComplexity.ToHtnAc.ToHtnAcMemPhase
import HtnComplexity.ToHtnAc.ToHtnAcSyncCount
/-!
# How far a memory cell has got is determined by the handshake counters

For the soundness half of the correctness of the TO-HTN ⟶ HTN-AC compilation the global
counting invariants (`HtnComplexity/ToHtnAc/ToHtnAcLockstep.lean`) have to be turned into
*positional* information: at a given point of a plan, which part of its run has each component
already executed?

For a memory cell this is what the present file provides.  A cell run is a write phase followed
by a read phase (`HTN.ToAc.yieldSeq_MEM_phases`), each phase begins with its `accept` and ends
with its `done`, and in between only state copies are tested and written; so the handshake
counters of the part already executed determine that part completely:

* `HTN.ToAc.cell_eq_nil_of_countP_accept_write` — a cell that has not accepted the write
  handshake has not moved at all;
* `HTN.ToAc.cell_prefix_memWrite_of_countP_accept_read` — a cell that has not accepted the read
  handshake is still inside its write phase;
* `HTN.ToAc.cell_memWrite_prefix_of_countP_done_write` — a cell that has signalled `done_W` has
  finished its write phase;
* `HTN.ToAc.cell_eq_memWrite_of_counts` — hence a cell that has signalled `done_W` but has not
  accepted the read handshake has executed exactly its write phase: its triple is latched and
  nothing else has happened;
* `HTN.ToAc.cell_eq_run_of_countP_done_read` — a cell that has signalled `done_R` has finished.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {vars : List F}

open Domain

/-! ### The two phases, split at their last action -/

/-- The write phase without its final `done_W`. -/
noncomputable def memWriteInit (S S' : Set F) (t : A ⊕ C) (vars : List F) :
    List (AcAct F A C) :=
  AcAct.accept RW.write :: (testsOf 0 S vars ++ testsOf 2 S' vars ++ [AcAct.preC t])

/-- The read phase without its final `done_R`. -/
noncomputable def memReadInit (S S' : Set F) (t : A ⊕ C) (vars : List F) :
    List (AcAct F A C) :=
  AcAct.accept RW.read :: AcAct.setC t :: (writesOf 4 S' vars ++ writesOf 3 S vars)

lemma memWrite_eq (S S' : Set F) (t : A ⊕ C) :
    memWrite (A := A) (C := C) S S' t vars =
      memWriteInit S S' t vars ++ [AcAct.doneA RW.write] := by
  simp [memWrite, memWriteInit, List.append_assoc]

lemma memRead_eq (S S' : Set F) (t : A ⊕ C) :
    memRead (A := A) (C := C) S S' t vars =
      memReadInit S S' t vars ++ [AcAct.doneA RW.read] := by
  simp [memRead, memReadInit, List.append_assoc]

/-! ### The handshake actions of the two phases -/

variable {p : AcAct F A C → Bool}

/-- The tests of a state copy are not handshake actions. -/
lemma countP_testsOf (hp : HandshakePred p) (i : Fin 5) (S : Set F) (vs : List F) :
    (testsOf (A := A) (C := C) i S vs).countP p = 0 := by
  classical
  refine List.countP_eq_zero.2 (fun a ha => ?_)
  simp only [testsOf, List.mem_reverse, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  unfold testAct
  split
  · simpa using hp.prePV v i i
  · simpa using hp.preNV v i i

/-- The writes of a state copy are not handshake actions. -/
lemma countP_writesOf (hp : HandshakePred p) (j : Fin 5) (S : Set F) (vs : List F) :
    (writesOf (A := A) (C := C) j S vs).countP p = 0 := by
  classical
  refine List.countP_eq_zero.2 (fun a ha => ?_)
  simp only [writesOf, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  unfold writeAct
  split
  · simpa using hp.setV v j
  · simpa using hp.delV v j

/-- The write phase performs exactly `accept_W` and `done_W`. -/
lemma countP_memWrite (hp : HandshakePred p) (S S' : Set F) (t : A ⊕ C) :
    (memWrite (A := A) (C := C) S S' t vars).countP p =
      ([AcAct.accept RW.write, AcAct.doneA RW.write] : List (AcAct F A C)).countP p := by
  simp [memWrite, List.countP_append, List.countP_cons, countP_testsOf hp, hp.preC,
    Nat.add_comm]

/-- The write phase without its last action performs exactly `accept_W`. -/
lemma countP_memWriteInit (hp : HandshakePred p) (S S' : Set F) (t : A ⊕ C) :
    (memWriteInit (A := A) (C := C) S S' t vars).countP p =
      ([AcAct.accept RW.write] : List (AcAct F A C)).countP p := by
  simp [memWriteInit, List.countP_append, List.countP_cons, countP_testsOf hp, hp.preC]

/-- The read phase performs exactly `accept_R` and `done_R`. -/
lemma countP_memRead (hp : HandshakePred p) (S S' : Set F) (t : A ⊕ C) :
    (memRead (A := A) (C := C) S S' t vars).countP p =
      ([AcAct.accept RW.read, AcAct.doneA RW.read] : List (AcAct F A C)).countP p := by
  simp [memRead, List.countP_append, List.countP_cons, countP_writesOf hp, hp.setC,
    Nat.add_comm]

/-- The read phase without its last action performs exactly `accept_R`. -/
lemma countP_memReadInit (hp : HandshakePred p) (S S' : Set F) (t : A ⊕ C) :
    (memReadInit (A := A) (C := C) S S' t vars).countP p =
      ([AcAct.accept RW.read] : List (AcAct F A C)).countP p := by
  simp [memReadInit, List.countP_append, List.countP_cons, countP_writesOf hp, hp.setC]

/-! ### The classification -/

variable {S S' : Set F} {t : A ⊕ C} {u : List (AcAct F A C)}

/-- A cell that has not accepted the write handshake has not moved. -/
theorem cell_eq_nil_of_countP_accept_write
    (hu : u <+: memWrite (A := A) (C := C) S S' t vars ++ memRead S S' t vars)
    (h : u.countP (isAccept RW.write) = 0) : u = [] := by
  classical
  rcases prefix_append_cases hu with hA | ⟨v, rfl, -⟩
  · cases u with
    | nil => rfl
    | cons a u' =>
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 (by simpa [memWrite] using hA)
        simp [isAccept] at h
  · have hw : (memWrite (A := A) (C := C) S S' t vars).countP (isAccept RW.write) = 1 := by
      rw [countP_memWrite (handshakePred_isAccept RW.write)]
      simp [isAccept]
    rw [List.countP_append, hw] at h
    omega

/-- A cell that has not accepted the read handshake is still inside its write phase. -/
theorem cell_prefix_memWrite_of_countP_accept_read
    (hu : u <+: memWrite (A := A) (C := C) S S' t vars ++ memRead S S' t vars)
    (h : u.countP (isAccept RW.read) = 0) : u <+: memWrite S S' t vars := by
  classical
  rcases prefix_append_cases hu with hA | ⟨v, rfl, hv⟩
  · exact hA
  · cases v with
    | nil => simp
    | cons a v' =>
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 (by simpa [memRead] using hv)
        rw [List.countP_append] at h
        simp [isAccept] at h

/-- A cell that has signalled `done_W` has finished its write phase. -/
theorem cell_memWrite_prefix_of_countP_done_write
    (hu : u <+: memWrite (A := A) (C := C) S S' t vars ++ memRead S S' t vars)
    (h : 1 ≤ u.countP (isDone RW.write)) :
    ∃ v, u = memWrite S S' t vars ++ v ∧ v <+: memRead S S' t vars := by
  classical
  rcases prefix_append_cases hu with hA | ⟨v, rfl, hv⟩
  · rw [memWrite_eq] at hA
    have hinit : (memWriteInit (A := A) (C := C) S S' t vars).countP (isDone RW.write) = 0 := by
      rw [countP_memWriteInit (handshakePred_isDone RW.write)]
      simp [isDone]
    rcases prefix_append_cases hA with hA' | ⟨w, rfl, hw⟩
    · have hle := (hA'.sublist).countP_le (p := (isDone RW.write : AcAct F A C → Bool))
      omega
    · cases w with
      | nil =>
          rw [List.countP_append, hinit] at h
          simp at h
      | cons b w' =>
          obtain ⟨rfl, hw'⟩ := List.cons_prefix_cons.1 hw
          have hnil : w' = [] := List.prefix_nil.1 hw'
          subst hnil
          exact ⟨[], by rw [memWrite_eq]; simp, List.nil_prefix⟩
  · exact ⟨v, rfl, hv⟩

/-- A cell that has signalled `done_W` but has not accepted the read handshake has executed
exactly its write phase: it has latched its triple and has done nothing else. -/
theorem cell_eq_memWrite_of_counts
    (hu : u <+: memWrite (A := A) (C := C) S S' t vars ++ memRead S S' t vars)
    (h₁ : 1 ≤ u.countP (isDone RW.write)) (h₂ : u.countP (isAccept RW.read) = 0) :
    u = memWrite S S' t vars := by
  obtain ⟨v, rfl, hv⟩ := cell_memWrite_prefix_of_countP_done_write hu h₁
  cases v with
  | nil => simp
  | cons a v' =>
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 (by simpa [memRead] using hv)
      rw [List.countP_append] at h₂
      simp [isAccept] at h₂

/-- A cell that has signalled `done_R` has finished its run. -/
theorem cell_eq_run_of_countP_done_read
    (hu : u <+: memWrite (A := A) (C := C) S S' t vars ++ memRead S S' t vars)
    (h : 1 ≤ u.countP (isDone RW.read)) :
    u = memWrite S S' t vars ++ memRead S S' t vars := by
  classical
  have hwrite : (memWrite (A := A) (C := C) S S' t vars).countP (isDone RW.read) = 0 := by
    rw [countP_memWrite (handshakePred_isDone RW.read)]
    simp [isDone]
  have hinit : (memReadInit (A := A) (C := C) S S' t vars).countP (isDone RW.read) = 0 := by
    rw [countP_memReadInit (handshakePred_isDone RW.read)]
    simp [isDone]
  rcases prefix_append_cases hu with hA | ⟨v, rfl, hv⟩
  · have hle := (hA.sublist).countP_le (p := (isDone RW.read : AcAct F A C → Bool))
    omega
  · rw [memRead_eq] at hv
    rcases prefix_append_cases hv with hv' | ⟨w, rfl, hw⟩
    · have hle := (hv'.sublist).countP_le (p := (isDone RW.read : AcAct F A C → Bool))
      rw [List.countP_append, hwrite] at h
      omega
    · cases w with
      | nil =>
          rw [List.countP_append, List.countP_append, hwrite, hinit] at h
          simp at h
      | cons b w' =>
          obtain ⟨rfl, hw'⟩ := List.cons_prefix_cons.1 hw
          have hnil : w' = [] := List.prefix_nil.1 hw'
          subst hnil
          rw [memRead_eq]

end ToAc

end HTN
