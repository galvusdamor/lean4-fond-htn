import HtnComplexity.NPHard.StackCNF
import ComplexityTheory.Complexity.CobhamTM.CobhamToTM
/-!
# The machine of a compiled stack program as a stack tableau

A flat instruction list `C` (`HTN.PTime.CobhamTM.Prog.Instr`) over the stacks `0, …, N` of bits
is a machine in the sense of `StackCNF.lean`: the controls are the addresses `Fin (C.length + 1)`
(the last one is the halting address), every instruction changes at most one stack by one push
or pop, and the next address depends on the top of one stack only.

* `HTN.NPHard.next_proj` — one step of the TM2 machine `progM C N` is one step of the tableau
  machine `codeStep C N`;
* `HTN.NPHard.iterate_next_eq_halt` — so a run of the TM2 machine to a halting configuration in
  `s ≤ T` steps is the run of `T` steps of the tableau machine.
-/

namespace HTN.NPHard

open HTN.PTime.CobhamTM HTN.PTime.CobhamTM.Prog Turing
open HTN.PTime.CobhamTM.TMSim (Act actAt)

/-- The step of the tableau machine of a code. -/
def codeStep (C : List Instr) (N : ℕ) (c : Fin (C.length + 1)) (h : Fin (N + 1) → Option Bool) :
    Fin (C.length + 1) × (Fin (N + 1) → Act Bool) :=
  if hc : c.val < C.length then
    match C[c.val] with
    | .push k b => (lab C.length (c.val + 1), actAt (Γ := fun _ => Bool) (stk N k) (.push b))
    | .pop k => (lab C.length (c.val + 1), actAt (Γ := fun _ => Bool) (stk N k) .pop)
    | .br k a₀ aF aT =>
      (match h (stk N k) with
        | none => lab C.length a₀
        | some false => lab C.length aF
        | some true => lab C.length aT, fun _ => .keep)
    | .jmp a => (lab C.length a, fun _ => .keep)
  else (c, fun _ => .keep)

/-- The tableau configuration of a TM2 configuration (halted configurations sit at the last
address). -/
def projCfg {C : List Instr} {N : ℕ} (g : MCfgP C.length N) :
    Fin (C.length + 1) × (Fin (N + 1) → List Bool) :=
  (g.l.getD (Fin.last C.length), g.stk)

/-- One step of the tableau machine (the `Tab.next` of a tableau with step `codeStep C N`). -/
def codeNext (C : List Instr) (N : ℕ) (g : Fin (C.length + 1) × (Fin (N + 1) → List Bool)) :
    Fin (C.length + 1) × (Fin (N + 1) → List Bool) :=
  let r := codeStep C N g.1 (fun k => (g.2 k).head?)
  (r.1, fun k => (r.2 k).apply (g.2 k))

theorem actAt_apply' {N : ℕ} (k : Fin (N + 1)) (a : Act Bool) (S : Fin (N + 1) → List Bool) :
    (fun k' => (actAt (Γ := fun _ => Bool) k a k').apply (S k')) =
      Function.update S k (a.apply (S k)) :=
  TMSim.actAt_apply_update (Γ := fun _ => Bool) k a S

theorem keep_apply' {N : ℕ} (S : Fin (N + 1) → List Bool) :
    (fun k => (Act.keep : Act Bool).apply (S k)) = S := rfl

/-- **One TM2 step is one tableau step.** -/
theorem next_proj (C : List Instr) (N : ℕ) (g g' : MCfgP C.length N)
    (h : TM2.step (progM C N) g = some g') : codeNext C N (projCfg g) = projCfg g' := by
  obtain ⟨l, v, S⟩ := g
  cases l with
  | none => simp at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    by_cases hl : l.val < C.length
    · simp only [codeNext, projCfg, Option.getD_some, codeStep, dif_pos hl, progM]
      cases hC : C[l.val] with
      | push k b =>
        simp only [instrStmt, TM2.stepAux, Option.getD_some]
        rw [actAt_apply']; rfl
      | pop k =>
        simp only [instrStmt, TM2.stepAux, Option.getD_some]
        rw [actAt_apply']; rfl
      | br k a₀ aF aT =>
        simp only [instrStmt, TM2.stepAux]
        rcases hS : S (stk N k) with _ | ⟨b, r⟩
        · simp [hS, Act.apply]
        · cases b <;> simp [hS, Act.apply]
      | jmp a =>
        simp only [instrStmt, TM2.stepAux, Option.getD_some]; rfl
    · have hlL : l = Fin.last C.length := Fin.ext (by have := l.isLt; simp; omega)
      simp only [codeNext, projCfg, Option.getD_some, codeStep, dif_neg hl, progM]
      simp [TM2.stepAux, hlL, Act.apply]

/-- The halting address is a fixed point. -/
theorem codeNext_last (C : List Instr) (N : ℕ) (S : Fin (N + 1) → List Bool) :
    codeNext C N (Fin.last C.length, S) = (Fin.last C.length, S) := by
  simp [codeNext, codeStep, Act.apply]

theorem iterate_codeNext_last (C : List Instr) (N : ℕ) (S : Fin (N + 1) → List Bool) (n : ℕ) :
    (codeNext C N)^[n] (Fin.last C.length, S) = (Fin.last C.length, S) :=
  Function.iterate_fixed (codeNext_last C N S) n

/-- A run of the TM2 machine is a run of the tableau machine. -/
theorem iterate_next_proj (C : List Instr) (N : ℕ) : ∀ (s : ℕ) (g g' : MCfgP C.length N),
    (flip Option.bind (TM2.step (progM C N)))^[s] (some g) = some g' →
      (codeNext C N)^[s] (projCfg g) = projCfg g'
  | 0, g, g', h => by simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h; rw [h]; rfl
  | s + 1, g, g', h => by
    rw [Function.iterate_succ_apply] at h
    rcases hs : TM2.step (progM C N) g with _ | g₁
    · simp only [flip, hs, Option.bind_some, Option.bind_none] at h
      rw [TMSim.iterate_bind_none] at h; cases h
    · simp only [flip, hs, Option.bind_some] at h
      rw [Function.iterate_succ_apply, next_proj C N g g₁ hs]
      exact iterate_next_proj C N s g₁ g' h

/-- **A halting run, padded to `T` steps.** -/
theorem iterate_next_eq_halt (C : List Instr) (N : ℕ) {s T : ℕ} (hsT : s ≤ T)
    (g : MCfgP C.length N) (v : Option Bool) (S : Fin (N + 1) → List Bool)
    (h : (flip Option.bind (TM2.step (progM C N)))^[s] (some g) = some ⟨none, v, S⟩) :
    (codeNext C N)^[T] (projCfg g) = (Fin.last C.length, S) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsT
  rw [show s + d = d + s from Nat.add_comm s d, Function.iterate_add_apply,
    iterate_next_proj C N s g _ h]
  exact iterate_codeNext_last C N S d

end HTN.NPHard
