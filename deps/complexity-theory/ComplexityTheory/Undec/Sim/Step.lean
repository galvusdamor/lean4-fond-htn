import ComplexityTheory.Undec.Sim.Trans
/-!
# Elementary steps of the simulating machine

This file records, for each control state of `HTN.Undec.Sim.simTSM`, the step it takes — both as
an existence statement (used to replay a run of the Turing machine) and, in
`ComplexityTheory/Undec/Sim/Backward.lean`, as an exhaustive case distinction.
-/

namespace HTN

namespace Undec

namespace Sim

open Turing

open scoped Classical

variable {Γ : Type*} [Inhabited Γ] [Fintype Γ] {Λ : Type*} [Inhabited Λ]
variable {N : TM0.Machine Γ Λ} {S : Finset Λ} {q0 : Λ}

/-! ### The stack encoding -/

omit [Inhabited Γ] in
theorem encL_nil : encL ([] : List Γ) = [0] := rfl

omit [Inhabited Γ] in
theorem encL_cons (c : Γ) (L : List Γ) : encL (c :: L) = symCode c :: encL L := rfl

/-- The tape with head symbol `a`, left half `L` and right half `R`. -/
def tapeOf (a : Γ) (L R : List Γ) : Tape Γ := ⟨a, ListBlank.mk L, ListBlank.mk R⟩

omit [Fintype Γ] in
theorem tapeOf_mk₁ (l : List Γ) : Tape.mk₁ l = tapeOf l.headI [] l.tail := by
  simp [Tape.mk₁, tapeOf]
  rfl

omit [Fintype Γ] in
theorem tapeOf_write (b a : Γ) (L R : List Γ) :
    Tape.write b (tapeOf a L R) = tapeOf b L R := rfl

omit [Fintype Γ] in
theorem tapeOf_move_right (a : Γ) (L R : List Γ) :
    Tape.move Dir.right (tapeOf a L R) = tapeOf R.headI (a :: L) R.tail := by
  simp [Tape.move, tapeOf, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

omit [Fintype Γ] in
theorem tapeOf_move_left (a : Γ) (L R : List Γ) :
    Tape.move Dir.left (tapeOf a L R) = tapeOf L.headI L.tail (a :: R) := by
  simp [Tape.move, tapeOf, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

/-! ### Equations for `trsOf` at a `run` state -/

theorem trsOf_run_none {q : Λ} {a : Γ} (h : N q a = none) :
    trsOf N S q0 (St.run q a) =
      (allSyms Γ).map fun s => ⟨stCode S (St.run q a), false, s, [s], 1⟩ := by
  simp only [trsOf, h]

theorem trsOf_run_write {q q' : Λ} {a b : Γ} (h : N q a = some (q', TM0.Stmt.write b)) :
    trsOf N S q0 (St.run q a) =
      (allSyms Γ).map fun s =>
        ⟨stCode S (St.run q a), false, s, [s], stCode S (St.run q' b)⟩ := by
  simp only [trsOf, h]

theorem trsOf_run_right {q q' : Λ} {a : Γ}
    (h : N q a = some (q', TM0.Stmt.move Dir.right)) :
    trsOf N S q0 (St.run q a) =
      ⟨stCode S (St.run q a), true, 0, [0], stCode S (St.pl q' default a)⟩ ::
        (symList Γ).map fun c =>
          ⟨stCode S (St.run q a), true, symCode c, [], stCode S (St.pl q' c a)⟩ := by
  simp only [trsOf, h]

theorem trsOf_run_left {q q' : Λ} {a : Γ}
    (h : N q a = some (q', TM0.Stmt.move Dir.left)) :
    trsOf N S q0 (St.run q a) =
      ⟨stCode S (St.run q a), false, 0, [0], stCode S (St.pr q' default a)⟩ ::
        (symList Γ).map fun c =>
          ⟨stCode S (St.run q a), false, symCode c, [], stCode S (St.pr q' c a)⟩ := by
  simp only [trsOf, h]

/-! ### One step, in each state -/

/-- A transition of the machine, from its source state. -/
theorem step_of_left {s : St Γ Λ} {t : Tr} (hs : StOk S s) (ht : t ∈ trsOf N S q0 s)
    (hstk : t.stk = false) (rest s2 : List ℕ) :
    (simTSM N S q0).Step ⟨stCode S s, t.pop :: rest, s2⟩ ⟨t.tgt, t.push ++ rest, s2⟩ :=
  TSM.step_left (mem_trans hs ht) hstk _ (src_of_mem_trsOf ht).symm rest s2

/-- A transition of the machine acting on the second stack. -/
theorem step_of_right {s : St Γ Λ} {t : Tr} (hs : StOk S s) (ht : t ∈ trsOf N S q0 s)
    (hstk : t.stk = true) (s1 rest : List ℕ) :
    (simTSM N S q0).Step ⟨stCode S s, s1, t.pop :: rest⟩ ⟨t.tgt, s1, t.push ++ rest⟩ :=
  TSM.step_right (mem_trans hs ht) hstk _ (src_of_mem_trsOf ht).symm s1 rest

/-! ### Flushing -/

theorem flush1_reaches (L : List Γ) (s2 : List ℕ) :
    (simTSM N S q0).Reaches ⟨1, encL L, s2⟩ ⟨2, [], s2⟩ := by
  induction L with
  | nil =>
      refine Relation.ReflTransGen.single ?_
      have ht : (⟨1, false, 0, [], 2⟩ : Tr) ∈ trsOf N S q0 (St.flush1 (Γ := Γ)) := by
        simp [trsOf]
      exact step_of_left (s := St.flush1) trivial ht rfl [] s2
  | cons c L ih =>
      refine Relation.ReflTransGen.head ?_ ih
      have ht : (⟨1, false, symCode c, [], 1⟩ : Tr) ∈ trsOf N S q0 (St.flush1 (Γ := Γ)) := by
        simp only [trsOf, List.mem_cons, List.mem_map]
        exact Or.inr ⟨c, mem_symList c, rfl⟩
      have := step_of_left (N := N) (q0 := q0) (s := St.flush1 (Γ := Γ)) trivial ht rfl
        (encL L) s2
      simpa [encL_cons] using this

theorem flush2_reaches (R : List Γ) :
    (simTSM N S q0).Reaches ⟨2, [], encL R⟩ ⟨3, [], []⟩ := by
  induction R with
  | nil =>
      refine Relation.ReflTransGen.single ?_
      have ht : (⟨2, true, 0, [], 3⟩ : Tr) ∈ trsOf N S q0 (St.flush2 (Γ := Γ)) := by
        simp [trsOf]
      exact step_of_right (s := St.flush2) trivial ht rfl [] []
  | cons c R ih =>
      refine Relation.ReflTransGen.head ?_ ih
      have ht : (⟨2, true, symCode c, [], 2⟩ : Tr) ∈ trsOf N S q0 (St.flush2 (Γ := Γ)) := by
        simp only [trsOf, List.mem_cons, List.mem_map]
        exact Or.inr ⟨c, mem_symList c, rfl⟩
      have := step_of_right (N := N) (q0 := q0) (s := St.flush2 (Γ := Γ)) trivial ht rfl
        [] (encL R)
      simpa [encL_cons] using this

theorem flush_reaches (L R : List Γ) :
    (simTSM N S q0).Reaches ⟨1, encL L, encL R⟩ ⟨3, [], []⟩ :=
  (flush1_reaches L (encL R)).trans (flush2_reaches R)

end Sim

end Undec

end HTN
