import ComplexityTheory.Machine.SimMain
import ComplexityTheory.Complexity.CobhamTM.Realize
import ComplexityTheory.Complexity.PolyExp
/-!
# Reasoning about stack machines

* **Deterministic runs.** `HTN.Mach.SReachD` — a run all of whose configurations but the last
  sit on a deterministic instruction (one coming from a compiled stack program).  Such a run is
  the only way forward: an accepting run from its start passes through its end
  (`HTN.Mach.AccFrom.of_sReachD`).  `HTN.Mach.reach_compileD` — compiled stack programs run
  deterministically (the strengthening of `HTN.Mach.reach_compile`).
* **Acceptance.** `HTN.Mach.AccFrom C σ` — some run from `σ` accepts.
* **Growth.** `HTN.Mach.exists_two_pow_bound` — a polynomial applied to a number of size
  `2 ^ a(n)` is at most `2 ^ q(n)` for a polynomial `q`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM

variable {C : List Ins}

/-- `σ` sits on a deterministic instruction. -/
def DetAt (C : List Ins) (σ : SCfg) : Prop := ∃ ins, C[σ.pc]? = some (Ins.ofInstr ins)

/-- A run along deterministic instructions (except possibly at its last configuration). -/
def SReachD (C : List Ins) : ℕ → SCfg → SCfg → Prop
  | 0, σ, σ' => σ = σ'
  | n + 1, σ, σ' => DetAt C σ ∧ ∃ τ, SStep C σ τ ∧ SReachD C n τ σ'

/-- A deterministic run of at most `T` steps. -/
def SRunD (C : List Ins) (σ σ' : SCfg) (T : ℕ) : Prop := ∃ n ≤ T, SReachD C n σ σ'

/-- Some run from `σ` accepts. -/
def AccFrom (C : List Ins) (σ : SCfg) : Prop := ∃ T σ', SReach C T σ σ' ∧ Accepting C σ'

theorem SReachD.sReach {n : ℕ} {σ σ' : SCfg} (h : SReachD C n σ σ') : SReach C n σ σ' := by
  induction n generalizing σ with
  | zero => exact h
  | succ n ih => obtain ⟨-, τ, hs, h'⟩ := h; exact ⟨τ, hs, ih h'⟩

theorem SReachD.trans {m n : ℕ} {σ τ υ : SCfg} (h₁ : SReachD C m σ τ) (h₂ : SReachD C n τ υ) :
    SReachD C (m + n) σ υ := by
  induction m generalizing σ with
  | zero => cases h₁; simpa using h₂
  | succ m ih =>
    obtain ⟨hd, x, hx, hxd⟩ := h₁
    rw [show m + 1 + n = (m + n) + 1 by omega]
    exact ⟨hd, x, hx, ih hxd⟩

theorem SRunD.refl (σ : SCfg) : SRunD C σ σ 0 := ⟨0, le_rfl, rfl⟩

theorem SRunD.trans {σ τ υ : SCfg} {T₁ T₂ : ℕ} (h₁ : SRunD C σ τ T₁) (h₂ : SRunD C τ υ T₂) :
    SRunD C σ υ (T₁ + T₂) := by
  obtain ⟨n₁, h₁', r₁⟩ := h₁
  obtain ⟨n₂, h₂', r₂⟩ := h₂
  exact ⟨n₁ + n₂, by omega, r₁.trans r₂⟩

theorem SRunD.mono {σ τ : SCfg} {T T' : ℕ} (h : SRunD C σ τ T) (hT : T ≤ T') : SRunD C σ τ T' :=
  let ⟨n, hn, r⟩ := h; ⟨n, le_trans hn hT, r⟩

theorem SRunD.single {σ τ : SCfg} (hd : DetAt C σ) (h : SStep C σ τ) : SRunD C σ τ 1 :=
  ⟨1, le_rfl, hd, τ, h, rfl⟩

theorem SRunD.sRun {σ τ : SCfg} {T : ℕ} (h : SRunD C σ τ T) : SRun C σ τ T :=
  let ⟨n, hn, r⟩ := h; ⟨n, hn, r.sReach⟩

/-- **Deterministic instructions have a unique successor.** -/
theorem SStep.det {σ τ₁ τ₂ : SCfg} (hd : DetAt C σ) (h₁ : SStep C σ τ₁) (h₂ : SStep C σ τ₂) :
    τ₁ = τ₂ := by
  obtain ⟨ins, hins⟩ := hd
  cases h₁ <;> cases h₂ <;> simp_all <;> cases ins <;> simp_all [Ins.ofInstr]

theorem DetAt.not_accepting {σ : SCfg} (hd : DetAt C σ) : ¬ Accepting C σ := by
  obtain ⟨ins, hins⟩ := hd
  intro h
  unfold Accepting at h
  rw [hins] at h
  cases ins <;> simp [Ins.ofInstr] at h

/-- **Acceptance passes through deterministic runs.** -/
theorem AccFrom.of_sReachD {n : ℕ} {σ σ' : SCfg} (hr : SReachD C n σ σ') (ha : AccFrom C σ) :
    AccFrom C σ' := by
  induction n generalizing σ with
  | zero => cases hr; exact ha
  | succ n ih =>
    obtain ⟨hd, τ, hs, hr'⟩ := hr
    obtain ⟨T, σa, hra, hacc⟩ := ha
    cases T with
    | zero => cases hra; exact absurd hacc hd.not_accepting
    | succ T =>
      obtain ⟨τ', hs', hra'⟩ := hra
      obtain rfl := SStep.det hd hs hs'
      exact ih hr' ⟨T, σa, hra', hacc⟩

theorem AccFrom.of_sRunD {σ σ' : SCfg} {T : ℕ} (hr : SRunD C σ σ' T) (ha : AccFrom C σ) :
    AccFrom C σ' := let ⟨_, _, r⟩ := hr; ha.of_sReachD r

/-- An accepting configuration accepts. -/
theorem AccFrom.of_accepting {σ : SCfg} (h : Accepting C σ) : AccFrom C σ := ⟨0, σ, rfl, h⟩

/-- Acceptance after a step. -/
theorem AccFrom.of_step {σ τ : SCfg} (hs : SStep C σ τ) (h : AccFrom C τ) : AccFrom C σ := by
  obtain ⟨T, σ', hr, ha⟩ := h
  exact ⟨T + 1, σ', ⟨τ, hs, hr⟩, ha⟩

/-- A configuration outside the program accepts nothing. -/
theorem not_accFrom_of_none {σ : SCfg} (h : C[σ.pc]? = none) : ¬ AccFrom C σ := by
  rintro ⟨T, σ', hr, ha⟩
  cases T with
  | zero => cases hr; unfold Accepting at ha; rw [h] at ha; cases ha
  | succ T => obtain ⟨τ, hs, -⟩ := hr; cases hs <;> simp_all

/-- The successors of a configuration on a given instruction. -/
theorem AccFrom.inv {σ : SCfg} (h : AccFrom C σ) : Accepting C σ ∨ ∃ τ, SStep C σ τ ∧ AccFrom C τ := by
  obtain ⟨T, σ', hr, ha⟩ := h
  cases T with
  | zero => cases hr; exact Or.inl ha
  | succ T => obtain ⟨τ, hs, hr'⟩ := hr; exact Or.inr ⟨τ, hs, T, σ', hr', ha⟩

/-! ### Compiled programs run deterministically -/

open Prog in
/-- **Compiled programs run deterministically** (`HTN.Mach.reach_compile`, strengthened). -/
theorem reach_compileD : ∀ {p : Prog} {S S' : Store} {t : ℕ}, Eval p S S' t → ∀ {o : ℕ},
    AtS C o (compile p o) → SRunD C ⟨o, S⟩ ⟨o + size p, S'⟩ (2 * t) := by
  intro p S S' t e
  induction e with
  | skip S => intro o _; simpa [size] using SRunD.refl _
  | push k b S =>
    intro o hat
    have hC : C[o]? = some (Ins.ofInstr (.push k b)) := by simpa [compile] using hat.get
    exact (SRunD.single ⟨_, hC⟩ (SStep.push (by simpa [Ins.ofInstr] using hC))).mono (by omega)
  | pop k S =>
    intro o hat
    have hC : C[o]? = some (Ins.ofInstr (.pop k)) := by simpa [compile] using hat.get
    exact (SRunD.single ⟨_, hC⟩ (SStep.pop (by simpa [Ins.ofInstr] using hC))).mono (by omega)
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
    have r₀ : SRunD C ⟨o, S⟩ ⟨o + 1, S⟩ 1 :=
      SRunD.single ⟨_, hC⟩ (SStep.brNil (by simpa [Ins.ofInstr] using hC) hk)
    have r₂ : SRunD C ⟨o + 1 + size p₀, S'⟩ ⟨o + size (ifTop k p₀ pF pT), S'⟩ 1 := by
      rw [show o + size (ifTop k p₀ pF pT) = o + size p₀ + size pF + size pT + 3 by
        simp only [size]; omega]
      exact SRunD.single ⟨_, hjmp.get⟩ (SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get))
    exact ((r₀.trans (ih hat₀)).trans r₂).mono (by omega)
  | @ifF k p₀ pF pT S S' t r hk _ ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hatF : AtS C (o + size p₀ + 2) (compile pF (o + size p₀ + 2)) :=
      hat.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    have hjmp : AtS C (o + size p₀ + 2 + size pF) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_right.congr (by simp [length_compile]; omega)
    have r₀ : SRunD C ⟨o, S⟩ ⟨o + size p₀ + 2, S⟩ 1 :=
      SRunD.single ⟨_, hC⟩ (SStep.brF (by simpa [Ins.ofInstr] using hC) hk)
    have r₂ : SRunD C ⟨o + size p₀ + 2 + size pF, S'⟩ ⟨o + size (ifTop k p₀ pF pT), S'⟩ 1 := by
      rw [show o + size (ifTop k p₀ pF pT) = o + size p₀ + size pF + size pT + 3 by
        simp only [size]; omega]
      exact SRunD.single ⟨_, hjmp.get⟩ (SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get))
    exact ((r₀.trans (ih hatF)).trans r₂).mono (by omega)
  | @ifT k p₀ pF pT S S' t r hk _ ih =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.append_left.append_left.append_left.get
    have hatT : AtS C (o + size p₀ + size pF + 3) (compile pT (o + size p₀ + size pF + 3)) :=
      hat.append_right.congr (by simp [length_compile]; omega)
    have r₀ : SRunD C ⟨o, S⟩ ⟨o + size p₀ + size pF + 3, S⟩ 1 :=
      SRunD.single ⟨_, hC⟩ (SStep.brT (by simpa [Ins.ofInstr] using hC) hk)
    have r₁ := ih hatT
    rw [show o + size p₀ + size pF + 3 + size pT = o + size (ifTop k p₀ pF pT) by
      simp only [size]; omega] at r₁
    exact (r₀.trans r₁).mono (by omega)
  | @loopNil k p S hk =>
    intro o hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.get
    rw [show o + size (loop k p) = o + size p + 2 by simp only [size]; omega]
    exact (SRunD.single ⟨_, hC⟩ (SStep.brNil (by simpa [Ins.ofInstr] using hC) hk)).mono
      (by omega)
  | @loopCons k p S S₁ S₂ t₁ t₂ hk _ _ ih₁ ih₂ =>
    intro o hat
    have hat' := hat
    simp only [compile] at hat
    have hC := hat.append_left.append_left.get
    have hatb : AtS C (o + 1) (compile p (o + 1)) := hat.append_left.append_right.congr (by simp)
    have hjmp : AtS C (o + 1 + size p) [.jmp o] :=
      hat.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨b, r, hkr⟩ := List.exists_cons_of_ne_nil hk
    have r₀ : SRunD C ⟨o, S⟩ ⟨o + 1, S⟩ 1 := by
      cases b
      · exact SRunD.single ⟨_, hC⟩ (SStep.brF (by simpa [Ins.ofInstr] using hC) hkr)
      · exact SRunD.single ⟨_, hC⟩ (SStep.brT (by simpa [Ins.ofInstr] using hC) hkr)
    have r₂ : SRunD C ⟨o + 1 + size p, S₁⟩ ⟨o, S₁⟩ 1 :=
      SRunD.single ⟨_, hjmp.get⟩ (SStep.jmp (by simpa [Ins.ofInstr] using hjmp.get))
    exact (((r₀.trans (ih₁ hatb)).trans r₂).trans (ih₂ hat')).mono (by omega)

/-! ### Growth -/

/-- A polynomial applied to a number below `2 ^ a(n)` is below `2 ^ q(n)`. -/
theorem exists_two_pow_bound (P a : Polynomial ℕ) :
    ∃ q : Polynomial ℕ, ∀ n m, m ≤ 2 ^ a.eval n → P.eval m ≤ 2 ^ q.eval n := by
  obtain ⟨k, hk⟩ := exists_pow_bound P
  refine ⟨Polynomial.C k + Polynomial.C k * (a + 1), fun n m hm => ?_⟩
  have h1 : m + 1 ≤ 2 ^ (a.eval n + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := a.eval n); omega
  have h2 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  calc P.eval m ≤ k * (m + 1) ^ k := hk m
    _ ≤ 2 ^ k * (2 ^ (a.eval n + 1)) ^ k := Nat.mul_le_mul h2 (Nat.pow_le_pow_left h1 k)
    _ = 2 ^ (Polynomial.C k + Polynomial.C k * (a + 1)).eval n := by
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_one]
      rw [← pow_mul, ← pow_add]; ring_nf

end Mach

end HTN
