import ComplexityTheory.Undec.Machine
import Mathlib.Computability.PostTuringMachine

/-!
# Simulating a Turing machine by a two-stack machine — the construction

A `Turing.TM0` machine is a finite control acting on a two-way infinite tape.  A two-stack
machine (`HTN.Undec.TSM`) simulates it in the classical way: the *left* half of the tape is the
first stack (nearest cell on top), the *right* half of the tape is the second stack, and the
symbol under the head is kept in the control state.

Two adjustments are needed because a `TSM` transition must always pop a symbol, and because a
`TSM` accepts with *both stacks empty*:

* every stack carries a **bottom marker** (the symbol `0`, which is not the code of any tape
  symbol).  Popping it and pushing it straight back models reading a blank beyond the end of the
  written part of the tape, so the tape stays two-way infinite, and it makes "the stack is
  empty" observable.
* when the simulated machine halts, the two-stack machine enters a **flush** phase, which pops
  both stacks empty and then moves to the accepting state.

This file defines the states, their codes, the transition list and the machine `simTSM`.  The
correctness proof is in the sibling files.
-/

namespace HTN

namespace Undec

namespace Sim

open Turing

open scoped Classical

variable {Γ : Type*} [Inhabited Γ] [Fintype Γ] {Λ : Type*} [Inhabited Λ]

/-! ### Codes for tape symbols and control states -/

/-- The code of a tape symbol: a positive natural number.  `0` is reserved for the bottom
marker of the two stacks. -/
noncomputable def symCode (a : Γ) : ℕ := (Fintype.equivFin Γ a : ℕ) + 1

omit [Inhabited Γ] in
theorem symCode_pos (a : Γ) : 0 < symCode a := Nat.succ_pos _

omit [Inhabited Γ] in
theorem symCode_ne_zero (a : Γ) : symCode a ≠ 0 := Nat.succ_ne_zero _

omit [Inhabited Γ] in
theorem symCode_injective : Function.Injective (symCode (Γ := Γ)) := by
  intro a b h
  have : (Fintype.equivFin Γ a : ℕ) = (Fintype.equivFin Γ b : ℕ) := by
    simpa [symCode] using h
  exact (Fintype.equivFin Γ).injective (Fin.ext this)

/-- The index of a control state inside the finite set `S` of relevant control states. -/
noncomputable def stIdx (S : Finset Λ) (q : Λ) : ℕ :=
  if h : q ∈ S then ((Fintype.equivFin { x // x ∈ S } ⟨q, h⟩ : Fin _) : ℕ) else 0

omit [Inhabited Λ] in
theorem stIdx_inj {S : Finset Λ} {q q' : Λ} (hq : q ∈ S) (hq' : q' ∈ S)
    (h : stIdx S q = stIdx S q') : q = q' := by
  rw [stIdx, dif_pos hq, stIdx, dif_pos hq'] at h
  have := (Fintype.equivFin { x // x ∈ S }).injective (Fin.ext h)
  exact congrArg Subtype.val this

/-- The control states of the simulating two-stack machine. -/
inductive St (Γ : Type*) (Λ : Type*)
  /-- The initial state: reads the first input symbol off the second stack. -/
  | start
  /-- Emptying the first stack. -/
  | flush1
  /-- Emptying the second stack. -/
  | flush2
  /-- The accepting state. -/
  | acc
  /-- Simulating the machine in control state `q` with `a` under the head. -/
  | run (q : Λ) (a : Γ)
  /-- After a right move: the new head symbol is `y`, and `b` still has to be pushed onto the
  first stack. -/
  | pl (q : Λ) (y b : Γ)
  /-- After a left move: the new head symbol is `y`, and `b` still has to be pushed onto the
  second stack. -/
  | pr (q : Λ) (y b : Γ)

/-- The code of a control state of the simulating machine. -/
noncomputable def stCode (S : Finset Λ) : St Γ Λ → ℕ
  | .start => 0
  | .flush1 => 1
  | .flush2 => 2
  | .acc => 3
  | .run q a => 4 + Nat.pair 0 (Nat.pair (stIdx S q) (Nat.pair (symCode a) 0))
  | .pl q y b => 4 + Nat.pair 1 (Nat.pair (stIdx S q) (Nat.pair (symCode y) (symCode b)))
  | .pr q y b => 4 + Nat.pair 2 (Nat.pair (stIdx S q) (Nat.pair (symCode y) (symCode b)))

/-! ### The transitions -/

/-- The list of all tape symbols. -/
noncomputable def symList (Γ : Type*) [Fintype Γ] : List Γ := (Finset.univ : Finset Γ).toList

omit [Inhabited Γ] in
theorem mem_symList (a : Γ) : a ∈ symList Γ := by
  simp [symList]

/-- All symbols that can occur on a stack: the bottom marker and the codes of tape symbols. -/
noncomputable def allSyms (Γ : Type*) [Inhabited Γ] [Fintype Γ] : List ℕ :=
  0 :: (symList Γ).map symCode

theorem zero_mem_allSyms : (0 : ℕ) ∈ allSyms Γ := List.mem_cons_self ..

theorem symCode_mem_allSyms (a : Γ) : symCode a ∈ allSyms Γ :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_symList a))

variable (N : TM0.Machine Γ Λ) (S : Finset Λ) (q0 : Λ)

/-- The transitions issuing from a given control state of the simulating machine. -/
noncomputable def trsOf : St Γ Λ → List Tr
  | .start =>
      ⟨0, true, 0, [0], stCode S (St.run (Γ := Γ) q0 default)⟩ ::
        (symList Γ).map fun c => ⟨0, true, symCode c, [], stCode S (St.run (Γ := Γ) q0 c)⟩
  | .flush1 =>
      ⟨1, false, 0, [], 2⟩ :: (symList Γ).map fun c => ⟨1, false, symCode c, [], 1⟩
  | .flush2 =>
      ⟨2, true, 0, [], 3⟩ :: (symList Γ).map fun c => ⟨2, true, symCode c, [], 2⟩
  | .acc => []
  | .run q a =>
      match N q a with
      | none => (allSyms Γ).map fun s => ⟨stCode S (St.run q a), false, s, [s], 1⟩
      | some (q', TM0.Stmt.write b) =>
          (allSyms Γ).map fun s =>
            ⟨stCode S (St.run q a), false, s, [s], stCode S (St.run q' b)⟩
      | some (q', TM0.Stmt.move Dir.right) =>
          ⟨stCode S (St.run q a), true, 0, [0], stCode S (St.pl q' default a)⟩ ::
            (symList Γ).map fun c =>
              ⟨stCode S (St.run q a), true, symCode c, [], stCode S (St.pl q' c a)⟩
      | some (q', TM0.Stmt.move Dir.left) =>
          ⟨stCode S (St.run q a), false, 0, [0], stCode S (St.pr q' default a)⟩ ::
            (symList Γ).map fun c =>
              ⟨stCode S (St.run q a), false, symCode c, [], stCode S (St.pr q' c a)⟩
  | .pl q y b =>
      (allSyms Γ).map fun s =>
        ⟨stCode S (St.pl q y b), false, s, [symCode b, s], stCode S (St.run q y)⟩
  | .pr q y b =>
      (allSyms Γ).map fun s =>
        ⟨stCode S (St.pr q y b), true, s, [symCode b, s], stCode S (St.run q y)⟩

/-- All control states that the simulating machine can be in. -/
noncomputable def allSt : List (St Γ Λ) :=
  [St.start, St.flush1, St.flush2, St.acc] ++
    S.toList.flatMap (fun q => (symList Γ).map fun a => St.run q a) ++
    S.toList.flatMap (fun q => (symList Γ).flatMap fun y =>
      (symList Γ).flatMap fun b => [St.pl q y b, St.pr q y b])

/-- **The two-stack machine simulating the `TM0` machine `N`**, whose control states relevant to
the run are listed in `S`, started in the control state `q0`. -/
noncomputable def simTSM : TSM where
  trans := (allSt S (Γ := Γ)).flatMap (trsOf N S q0)
  start := 0
  acc := 3

/-- The encoding of one half of the tape as a stack: the codes of the symbols, bottom marker
last. -/
noncomputable def encL (l : List Γ) : List ℕ := l.map symCode ++ [0]

omit [Inhabited Γ] in
theorem encL_injective : Function.Injective (encL (Γ := Γ)) := by
  intro l l' h
  have := List.append_inj_left' h rfl
  exact List.map_injective_iff.2 symCode_injective this

end Sim

end Undec

end HTN
