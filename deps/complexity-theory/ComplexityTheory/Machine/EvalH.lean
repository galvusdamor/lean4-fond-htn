import ComplexityTheory.Machine.Kit
/-!
# Stack programs with bounded stacks

For polynomial *space* the running time of a stack program is irrelevant (it may be exponential);
what matters is the height of the stacks.  `HTN.Mach.EvalH h p S S'` is the big-step semantics of
stack programs (`HTN.PTime.CobhamTM.Prog.Eval`) in which every store passed through has all its
stacks of height at most `h` (`HTN.Mach.HB h`).

* `HTN.Mach.EvalH.eval` — a bounded evaluation is an evaluation;
* `HTN.Mach.evalH_of_eval` — an evaluation of `t` steps from stacks of height at most `h₀` is
  bounded by `h₀ + t`;
* `HTN.Mach.reach_compileH` — a bounded evaluation of a compiled program is a run of the stack
  machine along which all stacks stay of height at most `h`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog

/-- All stacks of `S` have height at most `h`. -/
def HB (h : ℕ) (S : Store) : Prop := ∀ j, (S j).length ≤ h

theorem HB.mono {h h' : ℕ} {S : Store} (hb : HB h S) (hh : h ≤ h') : HB h' S :=
  fun j => le_trans (hb j) hh

theorem HB.update {h : ℕ} {S : Store} (hb : HB h S) {k : ℕ} {l : List Bool} (hl : l.length ≤ h) :
    HB h (Function.update S k l) := by
  intro j
  by_cases hj : j = k
  · subst hj; simpa using hl
  · rw [Function.update_of_ne hj]; exact hb j

/-- **Evaluation with bounded stacks.** -/
inductive EvalH (h : ℕ) : Prog → Store → Store → Prop
  | skip {S : Store} : HB h S → EvalH h skip S S
  | push {k : ℕ} {b : Bool} {S : Store} : HB h S → HB h (Function.update S k (b :: S k)) →
      EvalH h (push k b) S (Function.update S k (b :: S k))
  | pop {k : ℕ} {S : Store} : HB h S → EvalH h (pop k) S (Function.update S k (S k).tail)
  | seq {p q : Prog} {S S₁ S₂ : Store} : EvalH h p S S₁ → EvalH h q S₁ S₂ → EvalH h (seq p q) S S₂
  | ifNil {k : ℕ} {p₀ pF pT : Prog} {S S' : Store} :
      S k = [] → EvalH h p₀ S S' → EvalH h (ifTop k p₀ pF pT) S S'
  | ifF {k : ℕ} {p₀ pF pT : Prog} {S S' : Store} {r : List Bool} :
      S k = false :: r → EvalH h pF S S' → EvalH h (ifTop k p₀ pF pT) S S'
  | ifT {k : ℕ} {p₀ pF pT : Prog} {S S' : Store} {r : List Bool} :
      S k = true :: r → EvalH h pT S S' → EvalH h (ifTop k p₀ pF pT) S S'
  | loopNil {k : ℕ} {p : Prog} {S : Store} : HB h S → S k = [] → EvalH h (loop k p) S S
  | loopCons {k : ℕ} {p : Prog} {S S₁ S₂ : Store} :
      S k ≠ [] → EvalH h p S S₁ → EvalH h (loop k p) S₁ S₂ → EvalH h (loop k p) S S₂

theorem EvalH.hb_start {h : ℕ} {p : Prog} {S S' : Store} (e : EvalH h p S S') : HB h S := by
  induction e with
  | skip hb => exact hb
  | push hb _ => exact hb
  | pop hb => exact hb
  | seq _ _ ih _ => exact ih
  | ifNil _ _ ih => exact ih
  | ifF _ _ ih => exact ih
  | ifT _ _ ih => exact ih
  | loopNil hb _ => exact hb
  | loopCons _ _ _ ih _ => exact ih

theorem EvalH.hb_end {h : ℕ} {p : Prog} {S S' : Store} (e : EvalH h p S S') : HB h S' := by
  induction e with
  | skip hb => exact hb
  | push _ hb => exact hb
  | @pop k S hb =>
    intro j
    by_cases hj : j = k
    · subst hj; simp only [Function.update_self, List.length_tail]; have := hb j; omega
    · rw [Function.update_of_ne hj]; exact hb j
  | seq _ _ _ ih => exact ih
  | ifNil _ _ ih => exact ih
  | ifF _ _ ih => exact ih
  | ifT _ _ ih => exact ih
  | loopNil hb _ => exact hb
  | loopCons _ _ _ _ ih => exact ih

theorem EvalH.mono {h h' : ℕ} (hh : h ≤ h') {p : Prog} {S S' : Store} (e : EvalH h p S S') :
    EvalH h' p S S' := by
  induction e with
  | skip hb => exact .skip (hb.mono hh)
  | push hb hb' => exact .push (hb.mono hh) (hb'.mono hh)
  | pop hb => exact .pop (hb.mono hh)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifNil hk _ ih => exact .ifNil hk ih
  | ifF hk _ ih => exact .ifF hk ih
  | ifT hk _ ih => exact .ifT hk ih
  | loopNil hb hk => exact .loopNil (hb.mono hh) hk
  | loopCons hk _ _ ih₁ ih₂ => exact .loopCons hk ih₁ ih₂

/-- A bounded evaluation is an evaluation. -/
theorem EvalH.eval {h : ℕ} {p : Prog} {S S' : Store} (e : EvalH h p S S') : ∃ t, Eval p S S' t := by
  induction e with
  | skip _ => exact ⟨0, .skip _⟩
  | push _ _ => exact ⟨1, .push _ _ _⟩
  | pop _ => exact ⟨1, .pop _ _⟩
  | seq _ _ ih₁ ih₂ => obtain ⟨t₁, e₁⟩ := ih₁; obtain ⟨t₂, e₂⟩ := ih₂; exact ⟨_, .seq e₁ e₂⟩
  | ifNil hk _ ih => obtain ⟨t, e⟩ := ih; exact ⟨_, .ifNil hk e⟩
  | ifF hk _ ih => obtain ⟨t, e⟩ := ih; exact ⟨_, .ifF hk e⟩
  | ifT hk _ ih => obtain ⟨t, e⟩ := ih; exact ⟨_, .ifT hk e⟩
  | loopNil _ hk => exact ⟨_, .loopNil hk⟩
  | loopCons hk _ _ ih₁ ih₂ =>
    obtain ⟨t₁, e₁⟩ := ih₁; obtain ⟨t₂, e₂⟩ := ih₂; exact ⟨_, .loopCons hk e₁ e₂⟩

/-- Stacks grow by at most one per step. -/
theorem _root_.HTN.PTime.CobhamTM.Prog.Eval.hb {p : Prog} {S S' : Store} {t : ℕ} (e : Eval p S S' t) {h : ℕ} (hb : HB h S) :
    HB (h + t) S' := by
  induction e generalizing h with
  | skip S => simpa using hb
  | push k b S =>
    intro j
    by_cases hj : j = k
    · subst hj; simp; have := hb j; omega
    · rw [Function.update_of_ne hj]; have := hb j; omega
  | pop k S =>
    intro j
    by_cases hj : j = k
    · subst hj; simp only [Function.update_self, List.length_tail]; have := hb j; omega
    · rw [Function.update_of_ne hj]; have := hb j; omega
  | seq _ _ ih₁ ih₂ => have := ih₂ (ih₁ hb); exact this.mono (by omega)
  | ifNil _ _ ih => exact (ih hb).mono (by omega)
  | ifF _ _ ih => exact (ih hb).mono (by omega)
  | ifT _ _ ih => exact (ih hb).mono (by omega)
  | loopNil _ => exact hb.mono (by omega)
  | loopCons _ _ _ ih₁ ih₂ => have := ih₂ (ih₁ hb); exact this.mono (by omega)

/-- **An evaluation of `t` steps is bounded by the initial heights plus `t`.** -/
theorem evalH_of_eval {p : Prog} {S S' : Store} {t : ℕ} (e : Eval p S S' t) {h : ℕ}
    (hb : HB h S) : EvalH (h + t) p S S' := by
  induction e generalizing h with
  | skip S => exact .skip (by simpa using hb)
  | push k b S => exact .push (hb.mono (by omega)) ((Eval.push k b S).hb hb)
  | pop k S => exact .pop (hb.mono (by omega))
  | @seq p q S S₁ S₂ t₁ t₂ e₁ _ ih₁ ih₂ =>
    exact .seq ((ih₁ hb).mono (by omega)) ((ih₂ (e₁.hb hb)).mono (by omega))
  | ifNil hk _ ih => exact .ifNil hk ((ih hb).mono (by omega))
  | ifF hk _ ih => exact .ifF hk ((ih hb).mono (by omega))
  | ifT hk _ ih => exact .ifT hk ((ih hb).mono (by omega))
  | loopNil hk => exact .loopNil (hb.mono (by omega)) hk
  | @loopCons k p S S₁ S₂ t₁ t₂ hk e₁ _ ih₁ ih₂ =>
    exact .loopCons hk ((ih₁ hb).mono (by omega)) ((ih₂ (e₁.hb hb)).mono (by omega))

/-! ### Compiled programs with bounded stacks -/

theorem SReachP.single' {C : List Ins} {P : SCfg → Prop} {σ τ : SCfg} (hs : SStep C σ τ) (hσ : P σ)
    (hτ : P τ) : SReachP C P 1 σ τ := ⟨hσ, τ, hs, rfl, hτ⟩

theorem SReachP.refl' {C : List Ins} {P : SCfg → Prop} {σ : SCfg} (hσ : P σ) : SReachP C P 0 σ σ :=
  ⟨rfl, hσ⟩

open Prog in
/-- **Compiled programs run with bounded stacks.** -/
theorem reach_compileH {C : List Ins} {h : ℕ} : ∀ {p : Prog} {S S' : Store}, EvalH h p S S' →
    ∀ {o : ℕ}, AtS C o (compile p o) →
      ∃ n, SReachP C (fun σ => HB h σ.S) n ⟨o, S⟩ ⟨o + size p, S'⟩ := by
  intro p S S' e
  induction e with
  | skip hb => intro o _; exact ⟨0, by simpa [size] using SReachP.refl' (C := C) (P := fun σ => HB h σ.S) (σ := ⟨o, _⟩) hb⟩
  | push hb hb' =>
    intro o hat
    exact ⟨1, SReachP.single' (SStep.push (by simpa [compile, Ins.ofInstr] using hat.get)) hb hb'⟩
  | pop hb =>
    intro o hat
    refine ⟨1, SReachP.single' (SStep.pop (by simpa [compile, Ins.ofInstr] using hat.get)) hb ?_⟩
    exact (EvalH.pop hb (k := _)).hb_end
  | @seq p q S S₁ S₂ _ _ ih₁ ih₂ =>
    intro o hat
    simp only [compile] at hat
    have hat₂ := hat.append_right
    rw [length_compile] at hat₂
    obtain ⟨n₁, r₁⟩ := ih₁ hat.append_left
    obtain ⟨n₂, r₂⟩ := ih₂ hat₂
    rw [show o + size (Prog.seq p q) = o + size p + size q by simp only [size]; omega]
    exact ⟨_, r₁.trans r₂⟩
  | @ifNil k p₀ pF pT S S' hk e ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hat₀ : AtS C (o + 1) (compile p₀ (o + 1)) :=
      hat.append_left.append_left.append_left.append_left.append_right.congr (by simp)
    have hjmp : AtS C (o + 1 + size p₀) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨n, r⟩ := ih hat₀
    have r₀ := SReachP.single' (C := C) (P := fun σ => HB h σ.S) (σ := ⟨o, S⟩) (τ := ⟨o + 1, S⟩)
      (SStep.brNil (by simpa [Ins.ofInstr] using hC) hk) e.hb_start e.hb_start
    have r₂ := SReachP.single' (C := C) (P := fun σ => HB h σ.S) (σ := ⟨o + 1 + size p₀, S'⟩)
      (τ := ⟨o + size (ifTop k p₀ pF pT), S'⟩)
      (by rw [show o + size (ifTop k p₀ pF pT) = o + size p₀ + size pF + size pT + 3 by
            simp only [size]; omega]
          exact SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get)) e.hb_end e.hb_end
    exact ⟨_, (r₀.trans r).trans r₂⟩
  | @ifF k p₀ pF pT S S' r hk e ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hatF : AtS C (o + size p₀ + 2) (compile pF (o + size p₀ + 2)) :=
      hat.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    have hjmp : AtS C (o + size p₀ + 2 + size pF) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨n, rr⟩ := ih hatF
    have r₀ := SReachP.single' (C := C) (P := fun σ => HB h σ.S) (σ := ⟨o, S⟩)
      (τ := ⟨o + size p₀ + 2, S⟩) (SStep.brF (by simpa [Ins.ofInstr] using hC) hk)
      e.hb_start e.hb_start
    have r₂ := SReachP.single' (C := C) (P := fun σ => HB h σ.S) (σ := ⟨o + size p₀ + 2 + size pF, S'⟩)
      (τ := ⟨o + size (ifTop k p₀ pF pT), S'⟩)
      (by rw [show o + size (ifTop k p₀ pF pT) = o + size p₀ + size pF + size pT + 3 by
            simp only [size]; omega]
          exact SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get)) e.hb_end e.hb_end
    exact ⟨_, (r₀.trans rr).trans r₂⟩
  | @ifT k p₀ pF pT S S' r hk e ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hatT : AtS C (o + size p₀ + size pF + 3) (compile pT (o + size p₀ + size pF + 3)) :=
      hat.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨n, rr⟩ := ih hatT
    have r₀ := SReachP.single' (C := C) (P := fun σ => HB h σ.S) (σ := ⟨o, S⟩)
      (τ := ⟨o + size p₀ + size pF + 3, S⟩) (SStep.brT (by simpa [Ins.ofInstr] using hC) hk)
      e.hb_start e.hb_start
    rw [show o + size p₀ + size pF + 3 + size pT = o + size (ifTop k p₀ pF pT) by
      simp only [size]; omega] at rr
    exact ⟨_, r₀.trans rr⟩
  | @loopNil k p S hb hk =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.get
    rw [show o + size (loop k p) = o + size p + 2 by simp only [size]; omega]
    exact ⟨1, SReachP.single' (SStep.brNil (by simpa [Ins.ofInstr] using hC) hk) hb hb⟩
  | @loopCons k p S S₁ S₂ hk e₁ e₂ ih₁ ih₂ =>
    intro o hat
    have hat' := hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.get
    have hatb : AtS C (o + 1) (compile p (o + 1)) := hat.append_left.append_right.congr (by simp)
    have hjmp : AtS C (o + 1 + size p) [.jmp o] :=
      hat.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨b, r, hkr⟩ := List.exists_cons_of_ne_nil hk
    have r₀ : SReachP C (fun σ => HB h σ.S) 1 ⟨o, S⟩ ⟨o + 1, S⟩ := by
      cases b
      · exact SReachP.single' (SStep.brF (by simpa [Ins.ofInstr] using hC) hkr) e₁.hb_start e₁.hb_start
      · exact SReachP.single' (SStep.brT (by simpa [Ins.ofInstr] using hC) hkr) e₁.hb_start e₁.hb_start
    obtain ⟨n₁, r₁⟩ := ih₁ hatb
    have r₂ : SReachP C (fun σ => HB h σ.S) 1 ⟨o + 1 + size p, S₁⟩ ⟨o, S₁⟩ :=
      SReachP.single' (SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get)) e₁.hb_end e₁.hb_end
    obtain ⟨n₂, r₃⟩ := ih₂ hat'
    exact ⟨_, ((r₀.trans r₁).trans r₂).trans r₃⟩

end Mach

end HTN
