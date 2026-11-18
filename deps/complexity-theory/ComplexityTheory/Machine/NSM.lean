import ComplexityTheory.Complexity.CobhamTM.ProgTM
/-!
# Nondeterministic stack machines

A **stack machine** is a list of instructions with absolute jump targets over infinitely many
stacks of bits (`HTN.PTime.CobhamTM.Store`): push a bit, pop, branch on the top of a stack, jump —
the instructions the stack programs of `ComplexityTheory/Complexity/CobhamTM/Prog.lean` compile
to — together with three new ones:

* `guess k` pushes a *nondeterministically chosen* bit on stack `k`;
* `choose a₁ a₂` jumps *nondeterministically* to `a₁` or `a₂`;
* `accept` accepts (and halts).

A machine halts without accepting when its program counter leaves the program.  It is the
intermediate language between programs of the polynomial-time and polynomial-space classes and
the single-tape Turing machines of `ComplexityTheory/TM/Basic.lean`
(`ComplexityTheory/Machine/Sim.lean`).

* `HTN.Mach.SStep`, `HTN.Mach.SReach` — the step relation and `n`-step reachability;
* `HTN.Mach.reach_compile` — a compiled stack program (`Prog.compile`) runs on the stack machine
  in at most twice its number of steps (the counterpart of `Prog.reach_compile` for TM2).
-/

namespace HTN

namespace Mach

open PTime CobhamTM

/-- The instructions of a stack machine. -/
inductive Ins where
  | push (k : ℕ) (b : Bool)
  | pop (k : ℕ)
  | br (k a₀ aF aT : ℕ)
  | jmp (a : ℕ)
  | guess (k : ℕ)
  | choose (a₁ a₂ : ℕ)
  | accept
  deriving DecidableEq

/-- The deterministic instructions of compiled stack programs. -/
def Ins.ofInstr : Prog.Instr → Ins
  | .push k b => .push k b
  | .pop k => .pop k
  | .br k a₀ aF aT => .br k a₀ aF aT
  | .jmp a => .jmp a

/-- A configuration: the program counter and the stacks. -/
structure SCfg where
  pc : ℕ
  S : Store

/-- **One step** of the machine `C`. -/
inductive SStep (C : List Ins) : SCfg → SCfg → Prop
  | push {pc k b S} : C[pc]? = some (.push k b) →
      SStep C ⟨pc, S⟩ ⟨pc + 1, Function.update S k (b :: S k)⟩
  | pop {pc k S} : C[pc]? = some (.pop k) → SStep C ⟨pc, S⟩ ⟨pc + 1, Function.update S k (S k).tail⟩
  | brNil {pc k a₀ aF aT S} : C[pc]? = some (.br k a₀ aF aT) → S k = [] → SStep C ⟨pc, S⟩ ⟨a₀, S⟩
  | brF {pc k a₀ aF aT S r} : C[pc]? = some (.br k a₀ aF aT) → S k = false :: r →
      SStep C ⟨pc, S⟩ ⟨aF, S⟩
  | brT {pc k a₀ aF aT S r} : C[pc]? = some (.br k a₀ aF aT) → S k = true :: r →
      SStep C ⟨pc, S⟩ ⟨aT, S⟩
  | jmp {pc a S} : C[pc]? = some (.jmp a) → SStep C ⟨pc, S⟩ ⟨a, S⟩
  | guess {pc k S} (b : Bool) : C[pc]? = some (.guess k) →
      SStep C ⟨pc, S⟩ ⟨pc + 1, Function.update S k (b :: S k)⟩
  | choose₁ {pc a₁ a₂ S} : C[pc]? = some (.choose a₁ a₂) → SStep C ⟨pc, S⟩ ⟨a₁, S⟩
  | choose₂ {pc a₁ a₂ S} : C[pc]? = some (.choose a₁ a₂) → SStep C ⟨pc, S⟩ ⟨a₂, S⟩

/-- `n`-step reachability. -/
def SReach (C : List Ins) : ℕ → SCfg → SCfg → Prop
  | 0, σ, σ' => σ = σ'
  | n + 1, σ, σ' => ∃ τ, SStep C σ τ ∧ SReach C n τ σ'

/-- Reachability in at most `T` steps. -/
def SRun (C : List Ins) (σ σ' : SCfg) (T : ℕ) : Prop := ∃ n ≤ T, SReach C n σ σ'

/-- A configuration is accepting iff its instruction is `accept`. -/
def Accepting (C : List Ins) (σ : SCfg) : Prop := C[σ.pc]? = some .accept

variable {C : List Ins}

theorem SReach.trans {m n : ℕ} {σ τ υ : SCfg} (h₁ : SReach C m σ τ) (h₂ : SReach C n τ υ) :
    SReach C (m + n) σ υ := by
  induction m generalizing σ with
  | zero => cases h₁; simpa using h₂
  | succ m ih =>
    obtain ⟨x, hx, hxd⟩ := h₁
    rw [show m + 1 + n = (m + n) + 1 by omega]
    exact ⟨x, hx, ih hxd⟩

theorem SReach.single {σ τ : SCfg} (h : SStep C σ τ) : SReach C 1 σ τ := ⟨τ, h, rfl⟩

theorem SRun.refl (σ : SCfg) : SRun C σ σ 0 := ⟨0, le_rfl, rfl⟩

theorem SRun.trans {σ τ υ : SCfg} {T₁ T₂ : ℕ} (h₁ : SRun C σ τ T₁) (h₂ : SRun C τ υ T₂) :
    SRun C σ υ (T₁ + T₂) := by
  obtain ⟨n₁, h₁', r₁⟩ := h₁
  obtain ⟨n₂, h₂', r₂⟩ := h₂
  exact ⟨n₁ + n₂, by omega, r₁.trans r₂⟩

theorem SRun.mono {σ τ : SCfg} {T T' : ℕ} (h : SRun C σ τ T) (hT : T ≤ T') : SRun C σ τ T' :=
  let ⟨n, hn, r⟩ := h; ⟨n, le_trans hn hT, r⟩

theorem SRun.single {σ τ : SCfg} (h : SStep C σ τ) : SRun C σ τ 1 := ⟨1, le_rfl, SReach.single h⟩

/-! ### Running compiled stack programs -/

/-- The compiled code `cd` sits at address `o` of `C`. -/
def AtS (C : List Ins) (o : ℕ) (cd : List Prog.Instr) : Prop :=
  ∀ i < cd.length, C[o + i]? = (cd[i]?).map Ins.ofInstr

theorem AtS.append_left {o : ℕ} {c d : List Prog.Instr} (h : AtS C o (c ++ d)) : AtS C o c :=
  fun i hi => by rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem AtS.append_right {o : ℕ} {c d : List Prog.Instr} (h : AtS C o (c ++ d)) :
    AtS C (o + c.length) d := fun i hi => by
  rw [Nat.add_assoc, h (c.length + i) (by simp; omega), List.getElem?_append_right (by omega)]
  simp

theorem AtS.get {o : ℕ} {ins : Prog.Instr} {c : List Prog.Instr} (h : AtS C o (ins :: c)) :
    C[o]? = some (Ins.ofInstr ins) := by
  have := h 0 (by simp)
  simpa using this

theorem AtS.congr {o o' : ℕ} {c : List Prog.Instr} (h : AtS C o c) (e : o = o') : AtS C o' c :=
  e ▸ h

open Prog in
/-- **Compiled programs run on the stack machine**: a run of `p` in `t` steps is a run of the
machine in at most `2 * t` steps, from the start of its code to the address just after it. -/
theorem reach_compile : ∀ {p : Prog} {S S' : Store} {t : ℕ}, Eval p S S' t → ∀ {o : ℕ},
    AtS C o (compile p o) → SRun C ⟨o, S⟩ ⟨o + size p, S'⟩ (2 * t) := by
  intro p S S' t e
  induction e with
  | skip S => intro o _; simpa [size] using SRun.refl _
  | push k b S =>
    intro o hat
    exact (SRun.single (SStep.push (by simpa [compile, Ins.ofInstr] using hat.get))).mono
      (by omega)
  | pop k S =>
    intro o hat
    exact (SRun.single (SStep.pop (by simpa [compile, Ins.ofInstr] using hat.get))).mono
      (by omega)
  | @seq p q S S₁ S₂ t₁ t₂ _ _ ih₁ ih₂ =>
    intro o hat
    simp only [compile] at hat
    have hat₂ := hat.append_right
    rw [length_compile] at hat₂
    have r := (ih₁ hat.append_left).trans (ih₂ hat₂)
    rw [show o + size (Prog.seq p q) = o + size p + size q by simp only [size]; omega]
    exact r.mono (by omega)
  | @ifNil k p₀ pF pT S S' t hk _ ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hat₀ : AtS C (o + 1) (compile p₀ (o + 1)) :=
      hat.append_left.append_left.append_left.append_left.append_right.congr (by simp)
    have hjmp : AtS C (o + 1 + size p₀) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    have r₀ : SRun C ⟨o, S⟩ ⟨o + 1, S⟩ 1 := SRun.single (SStep.brNil (by simpa [Ins.ofInstr] using hC) hk)
    have r₂ : SRun C ⟨o + 1 + size p₀, S'⟩ ⟨o + size (ifTop k p₀ pF pT), S'⟩ 1 := by
      rw [show o + size (ifTop k p₀ pF pT) = o + size p₀ + size pF + size pT + 3 by
        simp only [size]; omega]
      exact SRun.single (SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get))
    exact ((r₀.trans (ih hat₀)).trans r₂).mono (by omega)
  | @ifF k p₀ pF pT S S' t r hk _ ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hatF : AtS C (o + size p₀ + 2) (compile pF (o + size p₀ + 2)) :=
      hat.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    have hjmp : AtS C (o + size p₀ + 2 + size pF) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_right.congr (by simp [length_compile]; omega)
    have r₀ : SRun C ⟨o, S⟩ ⟨o + size p₀ + 2, S⟩ 1 :=
      SRun.single (SStep.brF (by simpa [Ins.ofInstr] using hC) hk)
    have r₂ : SRun C ⟨o + size p₀ + 2 + size pF, S'⟩ ⟨o + size (ifTop k p₀ pF pT), S'⟩ 1 := by
      rw [show o + size (ifTop k p₀ pF pT) = o + size p₀ + size pF + size pT + 3 by
        simp only [size]; omega]
      exact SRun.single (SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get))
    exact ((r₀.trans (ih hatF)).trans r₂).mono (by omega)
  | @ifT k p₀ pF pT S S' t r hk _ ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hatT : AtS C (o + size p₀ + size pF + 3) (compile pT (o + size p₀ + size pF + 3)) :=
      hat.append_right.congr (by simp [length_compile]; omega)
    have r₀ : SRun C ⟨o, S⟩ ⟨o + size p₀ + size pF + 3, S⟩ 1 :=
      SRun.single (SStep.brT (by simpa [Ins.ofInstr] using hC) hk)
    have r₁ := ih hatT
    rw [show o + size p₀ + size pF + 3 + size pT = o + size (ifTop k p₀ pF pT) by
      simp only [size]; omega] at r₁
    exact (r₀.trans r₁).mono (by omega)
  | @loopNil k p S hk =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.get
    rw [show o + size (loop k p) = o + size p + 2 by simp only [size]; omega]
    exact (SRun.single (SStep.brNil (by simpa [Ins.ofInstr] using hC) hk)).mono (by omega)
  | @loopCons k p S S₁ S₂ t₁ t₂ hk _ _ ih₁ ih₂ =>
    intro o hat
    have hat' := hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.get
    have hatb : AtS C (o + 1) (compile p (o + 1)) := hat.append_left.append_right.congr (by simp)
    have hjmp : AtS C (o + 1 + size p) [.jmp o] :=
      hat.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨b, r, hkr⟩ := List.exists_cons_of_ne_nil hk
    have r₀ : SRun C ⟨o, S⟩ ⟨o + 1, S⟩ 1 := by
      cases b
      · exact SRun.single (SStep.brF (by simpa [Ins.ofInstr] using hC) hkr)
      · exact SRun.single (SStep.brT (by simpa [Ins.ofInstr] using hC) hkr)
    have r₂ : SRun C ⟨o + 1 + size p, S₁⟩ ⟨o, S₁⟩ 1 :=
      SRun.single (SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get))
    exact (((r₀.trans (ih₁ hatb)).trans r₂).trans (ih₂ hat')).mono (by omega)

end Mach

end HTN
