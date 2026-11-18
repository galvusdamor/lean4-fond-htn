import Mathlib.Computability.TMComputable
import ComplexityTheory.Complexity.CobhamTM.Prog
/-!
# Compiling stack programs to TM2 machines

A stack program is compiled to a flat list of instructions with absolute jump targets
(`Prog.compile`); a list of instructions is a TM2 program whose labels are the instruction
addresses (`Prog.progM`), one TM2 step per instruction.  `Prog.reach_compile`: a terminating run
of a program in `t` steps becomes a run of the machine in at most `2 * t` steps, from the address
where the code of the program starts to the address just after it.
-/

namespace HTN.PTime.CobhamTM

namespace Prog

open Turing

/-- Flat instructions with absolute jump targets. -/
inductive Instr where
  | push (k : ℕ) (b : Bool)
  | pop (k : ℕ)
  | br (k aNil aF aT : ℕ)
  | jmp (a : ℕ)

/-- The number of instructions of a compiled program. -/
def size : Prog → ℕ
  | skip => 0
  | push _ _ => 1
  | pop _ => 1
  | seq p q => size p + size q
  | ifTop _ p₀ pF pT => size p₀ + size pF + size pT + 3
  | loop _ p => size p + 2

/-- Compilation of a program placed at address `o`. -/
def compile : Prog → ℕ → List Instr
  | skip, _ => []
  | push k b, _ => [.push k b]
  | pop k, _ => [.pop k]
  | seq p q, o => compile p o ++ compile q (o + size p)
  | ifTop k p₀ pF pT, o =>
    [.br k (o + 1) (o + size p₀ + 2) (o + size p₀ + size pF + 3)] ++ compile p₀ (o + 1) ++
      [.jmp (o + size p₀ + size pF + size pT + 3)] ++ compile pF (o + size p₀ + 2) ++
      [.jmp (o + size p₀ + size pF + size pT + 3)] ++ compile pT (o + size p₀ + size pF + 3)
  | loop k p, o => [.br k (o + size p + 2) (o + 1) (o + 1)] ++ compile p (o + 1) ++ [.jmp o]

theorem length_compile (p : Prog) (o : ℕ) : (compile p o).length = size p := by
  induction p generalizing o with
  | skip => rfl
  | push => rfl
  | pop => rfl
  | seq p q ihp ihq => simp [compile, size, ihp, ihq]
  | ifTop k p₀ pF pT ih₀ ihF ihT => simp [compile, size, ih₀, ihF, ihT]; omega
  | loop k p ih => simp [compile, size, ih]

/-- The largest stack index used by a program. -/
def maxStack : Prog → ℕ
  | skip => 0
  | push k _ => k
  | pop k => k
  | seq p q => max (maxStack p) (maxStack q)
  | ifTop k p₀ pF pT => max k (max (maxStack p₀) (max (maxStack pF) (maxStack pT)))
  | loop k p => max k (maxStack p)

/-! ### The machine of a list of instructions -/

/-- The stacks of the machine: `Fin (N + 1)`, all over the alphabet `Bool`. -/
abbrev Γb (N : ℕ) : Fin (N + 1) → Type := fun _ => Bool

/-- A stack index as a stack of the machine (indices above `N` are clamped). -/
def stk (N k : ℕ) : Fin (N + 1) := ⟨min k N, by omega⟩

/-- An address as a label (addresses above `L` are clamped to the final label `L`). -/
def lab (L o : ℕ) : Fin (L + 1) := ⟨min o L, by omega⟩

/-- The statement of one instruction at address `i`. -/
def instrStmt (L N i : ℕ) : Instr → TM2.Stmt (Γb N) (Fin (L + 1)) (Option Bool)
  | .push k b => .push (stk N k) (fun _ => b) (.goto fun _ => lab L (i + 1))
  | .pop k => .pop (stk N k) (fun v _ => v) (.goto fun _ => lab L (i + 1))
  | .br k a₀ aF aT => .peek (stk N k) (fun _ o => o)
      (.branch (fun v => v.isNone) (.goto fun _ => lab L a₀)
        (.branch (fun v => v.getD false) (.goto fun _ => lab L aT) (.goto fun _ => lab L aF)))
  | .jmp a => .goto fun _ => lab L a

/-- The TM2 program of a list of instructions: label `i < L` runs instruction `i`, the final
label `L` resets the internal state and halts. -/
def progM (C : List Instr) (N : ℕ) (l : Fin (C.length + 1)) :
    TM2.Stmt (Γb N) (Fin (C.length + 1)) (Option Bool) :=
  if h : l.val < C.length then instrStmt C.length N l.val C[l.val] else .load (fun _ => none) .halt

/-- The configurations of the machine. -/
abbrev MCfgP (L N : ℕ) : Type := TM2.Cfg (Γb N) (Fin (L + 1)) (Option Bool)

/-- The stacks of the machine for a store. -/
def stkOf (N : ℕ) (S : Store) : ∀ _ : Fin (N + 1), List Bool := fun j => S j.val

/-- Reachability in at most `k` steps. -/
def Reach {α : Type} (f : α → Option α) (a b : α) (k : ℕ) : Prop :=
  ∃ k' ≤ k, (flip Option.bind f)^[k'] (some a) = some b

theorem Reach.refl {α : Type} (f : α → Option α) (a : α) : Reach f a a 0 := ⟨0, le_rfl, rfl⟩

theorem Reach.trans {α : Type} {f : α → Option α} {a b c : α} {k₁ k₂ : ℕ}
    (h₁ : Reach f a b k₁) (h₂ : Reach f b c k₂) : Reach f a c (k₁ + k₂) := by
  obtain ⟨k₁', hk₁, e₁⟩ := h₁
  obtain ⟨k₂', hk₂, e₂⟩ := h₂
  exact ⟨k₂' + k₁', by omega, by rw [Function.iterate_add_apply, e₁, e₂]⟩

theorem Reach.mono {α : Type} {f : α → Option α} {a b : α} {k k' : ℕ} (h : Reach f a b k)
    (hk : k ≤ k') : Reach f a b k' := let ⟨j, hj, e⟩ := h; ⟨j, le_trans hj hk, e⟩

theorem Reach.single {α : Type} {f : α → Option α} {a b : α} (h : f a = some b) :
    Reach f a b 1 := ⟨1, le_rfl, by simpa [flip] using h⟩

theorem stkOf_update {N k : ℕ} (hk : k ≤ N) (S : Store) (l : List Bool) :
    stkOf N (Function.update S k l) = Function.update (stkOf N S) (stk N k) l := by
  funext j
  by_cases hj : j = stk N k
  · subst hj
    simp only [stkOf, stk, Function.update_self]
    rw [Nat.min_eq_left hk, Function.update_self]
  · have : j.val ≠ k := by
      intro h; apply hj; ext; simp [stk, Nat.min_eq_left hk, h]
    simp [stkOf, Function.update_of_ne hj, Function.update_of_ne this]

theorem stkOf_apply {N k : ℕ} (hk : k ≤ N) (S : Store) : stkOf N S (stk N k) = S k := by
  simp [stkOf, stk, Nat.min_eq_left hk]

/-- The code `c` sits at address `o` of `C`. -/
def At (C : List Instr) (o : ℕ) (cd : List Instr) : Prop := ∀ i < cd.length, C[o + i]? = cd[i]?

theorem At.append_left {C : List Instr} {o : ℕ} {c d : List Instr} (h : At C o (c ++ d)) :
    At C o c := fun i hi => by
  rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem At.append_right {C : List Instr} {o : ℕ} {c d : List Instr} (h : At C o (c ++ d)) :
    At C (o + c.length) d := fun i hi => by
  rw [Nat.add_assoc, h (c.length + i) (by simp; omega), List.getElem?_append_right (by omega)]
  simp

theorem At.get {C : List Instr} {o : ℕ} {ins : Instr} {c : List Instr} (h : At C (o) (ins :: c)) :
    ∃ h' : o < C.length, C[o] = ins := by
  have := h 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero] at this
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 this
  exact ⟨h1, h2⟩

theorem progM_lab {C : List Instr} {N o : ℕ} (ho : o < C.length) :
    progM C N (lab C.length o) = instrStmt C.length N o C[o] := by
  have : (lab C.length o).val = o := by simp [lab]; omega
  simp only [progM, this, ho, dite_true]

/-- One instruction is one step of the machine. -/
theorem step_lab {C : List Instr} {N o : ℕ} (ho : o < C.length) (v : Option Bool)
    (T : ∀ _ : Fin (N + 1), List Bool) :
    TM2.step (progM C N) ⟨some (lab C.length o), v, T⟩ =
      some (TM2.stepAux (instrStmt C.length N o C[o]) v T) := by
  simp [TM2.step, progM_lab ho]

/-! ### Correctness of the compilation -/

theorem At.congr {C : List Instr} {o o' : ℕ} {c : List Instr} (h : At C o c) (e : o = o') :
    At C o' c := e ▸ h

/-- **Compilation is correct**: a run of `p` in `t` steps is a run of the machine in at most
`2 * t` steps, from the start of the code of `p` to the address just after it. -/
theorem reach_compile {C : List Instr} {N : ℕ} :
    ∀ {p : Prog} {S S' : Store} {t : ℕ}, Eval p S S' t → ∀ {o : ℕ}, maxStack p ≤ N →
      At C o (compile p o) → o + size p ≤ C.length → ∀ v : Option Bool, ∃ v',
        Reach (TM2.step (progM C N)) ⟨some (lab C.length o), v, stkOf N S⟩
          ⟨some (lab C.length (o + size p)), v', stkOf N S'⟩ (2 * t) := by
  intro p S S' t e
  induction e with
  | skip S => intro o _ _ _ v; exact ⟨v, by simpa [size] using Reach.refl _ _⟩
  | push k b S =>
    intro o hN hat hL v
    obtain ⟨ho, hC⟩ := At.get (c := []) hat
    refine ⟨v, (Reach.single ?_).mono (by omega)⟩
    rw [step_lab ho, hC]
    simp only [instrStmt, TM2.stepAux, size]
    rw [stkOf_update (by simpa [maxStack] using hN), stkOf_apply (by simpa [maxStack] using hN)]
  | pop k S =>
    intro o hN hat hL v
    obtain ⟨ho, hC⟩ := At.get (c := []) hat
    refine ⟨v, (Reach.single ?_).mono (by omega)⟩
    rw [step_lab ho, hC]
    simp only [instrStmt, TM2.stepAux, size]
    rw [stkOf_update (by simpa [maxStack] using hN), stkOf_apply (by simpa [maxStack] using hN)]
  | @seq p q S S₁ S₂ t₁ t₂ _ _ ih₁ ih₂ =>
    intro o hN hat hL v
    simp only [maxStack, max_le_iff] at hN
    rw [size] at hL
    simp only [compile] at hat
    have hat₁ := hat.append_left
    have hat₂ := hat.append_right
    rw [length_compile] at hat₂
    obtain ⟨v₁, r₁⟩ := ih₁ hN.1 hat₁ (by omega) v
    obtain ⟨v₂, r₂⟩ := ih₂ hN.2 hat₂ (by omega) v₁
    rw [show o + size (Prog.seq p q) = o + size p + size q by simp only [size]; omega]
    exact ⟨v₂, (r₁.trans r₂).mono (by omega)⟩
  | @ifNil k p₀ pF pT S S' t hk _ ih =>
    intro o hN hat hL v
    simp only [maxStack, max_le_iff] at hN
    rw [size] at hL
    simp only [compile] at hat
    obtain ⟨ho, hC⟩ := At.get hat.append_left.append_left.append_left.append_left.append_left
    have hat₀ : At C (o + 1) (compile p₀ (o + 1)) :=
      hat.append_left.append_left.append_left.append_left.append_right.congr (by simp)
    have hjmp : At C (o + 1 + size p₀) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨hoj, hCj⟩ := At.get hjmp
    have r₀ : Reach (TM2.step (progM C N)) ⟨some (lab C.length o), v, stkOf N S⟩
        ⟨some (lab C.length (o + 1)), none, stkOf N S⟩ 1 := by
      refine Reach.single ?_
      rw [step_lab ho, hC]
      simp [instrStmt, TM2.stepAux, stkOf_apply hN.1, hk]
    obtain ⟨v₁, r₁⟩ := ih hN.2.1 hat₀ (by omega) none
    have r₂ : Reach (TM2.step (progM C N)) ⟨some (lab C.length (o + 1 + size p₀)), v₁, stkOf N S'⟩
        ⟨some (lab C.length (o + size (ifTop k p₀ pF pT))), v₁, stkOf N S'⟩ 1 := by
      refine Reach.single ?_
      rw [step_lab hoj, hCj]
      simp only [instrStmt, TM2.stepAux, size]
      congr 4; omega
    exact ⟨v₁, ((r₀.trans r₁).trans r₂).mono (by omega)⟩
  | @ifF k p₀ pF pT S S' t r hk _ ih =>
    intro o hN hat hL v
    simp only [maxStack, max_le_iff] at hN
    rw [size] at hL
    simp only [compile] at hat
    obtain ⟨ho, hC⟩ := At.get hat.append_left.append_left.append_left.append_left.append_left
    have hatF : At C (o + size p₀ + 2) (compile pF (o + size p₀ + 2)) :=
      hat.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    have hjmp : At C (o + size p₀ + 2 + size pF) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨hoj, hCj⟩ := At.get hjmp
    have r₀ : Reach (TM2.step (progM C N)) ⟨some (lab C.length o), v, stkOf N S⟩
        ⟨some (lab C.length (o + size p₀ + 2)), some false, stkOf N S⟩ 1 := by
      refine Reach.single ?_
      rw [step_lab ho, hC]
      simp [instrStmt, TM2.stepAux, stkOf_apply hN.1, hk]
    obtain ⟨v₁, r₁⟩ := ih hN.2.2.1 hatF (by omega) (some false)
    have r₂ : Reach (TM2.step (progM C N))
        ⟨some (lab C.length (o + size p₀ + 2 + size pF)), v₁, stkOf N S'⟩
        ⟨some (lab C.length (o + size (ifTop k p₀ pF pT))), v₁, stkOf N S'⟩ 1 := by
      refine Reach.single ?_
      rw [step_lab hoj, hCj]
      simp only [instrStmt, TM2.stepAux, size]
      congr 4; omega
    exact ⟨v₁, ((r₀.trans r₁).trans r₂).mono (by omega)⟩
  | @ifT k p₀ pF pT S S' t r hk _ ih =>
    intro o hN hat hL v
    simp only [maxStack, max_le_iff] at hN
    rw [size] at hL
    simp only [compile] at hat
    obtain ⟨ho, hC⟩ := At.get hat.append_left.append_left.append_left.append_left.append_left
    have hatT : At C (o + size p₀ + size pF + 3) (compile pT (o + size p₀ + size pF + 3)) :=
      hat.append_right.congr (by simp [length_compile]; omega)
    have r₀ : Reach (TM2.step (progM C N)) ⟨some (lab C.length o), v, stkOf N S⟩
        ⟨some (lab C.length (o + size p₀ + size pF + 3)), some true, stkOf N S⟩ 1 := by
      refine Reach.single ?_
      rw [step_lab ho, hC]
      simp [instrStmt, TM2.stepAux, stkOf_apply hN.1, hk]
    obtain ⟨v₁, r₁⟩ := ih hN.2.2.2 hatT (by omega) (some true)
    have e : o + size p₀ + size pF + 3 + size pT = o + size (ifTop k p₀ pF pT) := by
      simp only [size]; omega
    rw [e] at r₁
    exact ⟨v₁, (r₀.trans r₁).mono (by omega)⟩
  | @loopNil k p S hk =>
    intro o hN hat hL v
    simp only [maxStack, max_le_iff] at hN
    simp only [compile] at hat
    obtain ⟨ho, hC⟩ := At.get hat.append_left.append_left
    refine ⟨none, (Reach.single ?_).mono (by omega)⟩
    rw [step_lab ho, hC]
    simp only [instrStmt, TM2.stepAux, stkOf_apply hN.1, hk, size]
    simp [Nat.add_assoc]
  | @loopCons k p S S₁ S₂ t₁ t₂ hk _ _ ih₁ ih₂ =>
    intro o hN hat hL v
    have hN' := hN
    simp only [maxStack, max_le_iff] at hN
    have hat' := hat
    have hL' := hL
    rw [size] at hL
    simp only [compile] at hat
    obtain ⟨ho, hC⟩ := At.get hat.append_left.append_left
    have hatb : At C (o + 1) (compile p (o + 1)) :=
      hat.append_left.append_right.congr (by simp)
    have hjmp : At C (o + 1 + size p) [.jmp o] :=
      hat.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨hoj, hCj⟩ := At.get hjmp
    obtain ⟨b, r, hkr⟩ := List.exists_cons_of_ne_nil hk
    have r₀ : Reach (TM2.step (progM C N)) ⟨some (lab C.length o), v, stkOf N S⟩
        ⟨some (lab C.length (o + 1)), some b, stkOf N S⟩ 1 := by
      refine Reach.single ?_
      rw [step_lab ho, hC]
      cases b <;> simp [instrStmt, TM2.stepAux, stkOf_apply hN.1, hkr]
    obtain ⟨v₁, r₁⟩ := ih₁ hN.2 hatb (by omega) (some b)
    have r₂ : Reach (TM2.step (progM C N)) ⟨some (lab C.length (o + 1 + size p)), v₁, stkOf N S₁⟩
        ⟨some (lab C.length o), v₁, stkOf N S₁⟩ 1 := by
      refine Reach.single ?_
      rw [step_lab hoj, hCj]
      simp [instrStmt, TM2.stepAux]
    obtain ⟨v₂, r₃⟩ := ih₂ hN' hat' hL' v₁
    exact ⟨v₂, (((r₀.trans r₁).trans r₂).trans r₃).mono (by omega)⟩

end Prog

end HTN.PTime.CobhamTM
