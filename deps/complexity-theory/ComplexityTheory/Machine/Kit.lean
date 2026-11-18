import ComplexityTheory.Machine.Logic
import ComplexityTheory.Complexity.CobhamTM.CobhamToTM
/-!
# A toolkit for writing stack machines

* code layout: `HTN.Mach.atS_of_append` (a compiled block inside a program),
  `HTN.Mach.stk_compile` (the stacks a compiled block uses), `HTN.Mach.getElem?_append_at`;
* `HTN.Mach.realizer_eval` — running the program of a realizer of a function of Cobham's class
  on arguments placed on stacks;
* `HTN.Mach.AccIn` — acceptance within a given number of steps, and its behaviour along
  deterministic runs and single steps (for inductions on the length of accepting runs);
* `HTN.Mach.SReachP.trans`, `HTN.Mach.sReachP_of_sRun` — runs with a bound on the heights of
  the stacks;
* **the guessing loop** `choose (g + 1) (g + 3); guess k; jmp g` at address `g`, which pushes an
  arbitrary string on stack `k`: `HTN.Mach.loop_run`, `HTN.Mach.loop_sound`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog

variable {C : List Ins}

/-! ### Code layout -/

theorem atS_of_append {C pre post : List Ins} {cd : List Prog.Instr} {o : ℕ}
    (hC : C = pre ++ cd.map Ins.ofInstr ++ post) (ho : pre.length = o) : AtS C o cd := by
  intro i hi
  subst hC; subst ho
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using hi), List.getElem?_map]

theorem stk_compile : ∀ (p : Prog) (o : ℕ) (ins : Prog.Instr), ins ∈ compile p o →
    ∀ k, (Ins.ofInstr ins).stk = some k → k ≤ maxStack p := by
  intro p
  induction p with
  | skip => intro o ins h; simp [compile] at h
  | push k b => intro o ins h k' hk; simp [compile] at h; subst h; simp [Ins.ofInstr, Ins.stk] at hk; simp [maxStack, hk]
  | pop k => intro o ins h k' hk; simp [compile] at h; subst h; simp [Ins.ofInstr, Ins.stk] at hk; simp [maxStack, hk]
  | seq p q ihp ihq =>
    intro o ins h k hk
    simp only [compile, List.mem_append] at h
    rcases h with h | h
    · exact le_trans (ihp _ _ h k hk) (le_max_left _ _)
    · exact le_trans (ihq _ _ h k hk) (le_max_right _ _)
  | ifTop k' p₀ pF pT ih₀ ihF ihT =>
    intro o ins h k hk
    simp only [compile, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
    simp only [maxStack]
    rcases h with ((((h | h) | h) | h) | h) | h
    · subst h; simp [Ins.ofInstr, Ins.stk] at hk; omega
    · exact le_trans (ih₀ _ _ h k hk) (by omega)
    · subst h; simp [Ins.ofInstr, Ins.stk] at hk
    · exact le_trans (ihF _ _ h k hk) (by omega)
    · subst h; simp [Ins.ofInstr, Ins.stk] at hk
    · exact le_trans (ihT _ _ h k hk) (by omega)
  | loop k' p ih =>
    intro o ins h k hk
    simp only [compile, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
    simp only [maxStack]
    rcases h with (h | h) | h
    · subst h; simp [Ins.ofInstr, Ins.stk] at hk; omega
    · exact le_trans (ih _ _ h k hk) (by omega)
    · subst h; simp [Ins.ofInstr, Ins.stk] at hk

theorem getElem?_append_at {α : Type*} (l₁ l₂ : List α) {i : ℕ} :
    (l₁ ++ l₂)[l₁.length + i]? = l₂[i]? := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-! ### Running a realizer -/

/-- **The program of a realizer computes its function** on arguments placed on stacks. -/
theorem realizer_eval {f : Fn} (R : Realizer f) (inp : ℕ → ℕ) (out base : ℕ) (args : Args)
    (S : Store) (hinp : ∀ i < R.A, inp i < base) (hout : out < base)
    (hne : ∀ i < R.A, inp i ≠ out) (hS : ∀ i < R.A, S (inp i) = args.getD i [])
    (hout0 : S out = []) (hc : Clean base S) :
    ∃ t ≤ R.time.eval (argSize args), Eval (R.P inp out base) S (Function.update S out (f args)) t := by
  have r := R.spec inp out base S hinp hout hne hout0 hc
  have hf : f (argsOf R.A inp S) = f args :=
    (R.reads.congr fun i hi => by rw [getD_argsOf hi, hS i hi, getD_padArgs hi]).trans
      (R.reads _).symm
  have hsz : argSize (argsOf R.A inp S) ≤ argSize args := Prog.argSize_argsOf_le_of_getD hS
  rw [hf] at r
  obtain ⟨t, ht, e⟩ := r
  exact ⟨t, le_trans ht (Polynomial.eval_mono_nat _ hsz), e⟩

/-! ### Acceptance within a number of steps -/

/-- Some run of exactly `T` steps from `σ` accepts. -/
def AccIn (C : List Ins) (T : ℕ) (σ : SCfg) : Prop := ∃ σ', SReach C T σ σ' ∧ Accepting C σ'

theorem AccIn.accFrom {T : ℕ} {σ : SCfg} (h : AccIn C T σ) : AccFrom C σ :=
  let ⟨σ', hr, ha⟩ := h; ⟨T, σ', hr, ha⟩

theorem AccIn.of_sReachD {n T : ℕ} {σ σ' : SCfg} (hr : SReachD C n σ σ') (ha : AccIn C T σ) :
    n ≤ T ∧ AccIn C (T - n) σ' := by
  induction n generalizing σ T with
  | zero => cases hr; exact ⟨Nat.zero_le _, by simpa using ha⟩
  | succ n ih =>
    obtain ⟨hd, τ, hs, hr'⟩ := hr
    obtain ⟨σa, hra, hacc⟩ := ha
    cases T with
    | zero => cases hra; exact absurd hacc hd.not_accepting
    | succ T =>
      obtain ⟨τ', hs', hra'⟩ := hra
      obtain rfl := SStep.det hd hs hs'
      obtain ⟨h1, h2⟩ := ih hr' ⟨σa, hra', hacc⟩
      exact ⟨by omega, by rwa [show T + 1 - (n + 1) = T - n by omega]⟩

theorem AccIn.of_sRunD {B T : ℕ} {σ σ' : SCfg} (hr : SRunD C σ σ' B) (ha : AccIn C T σ) :
    ∃ T' ≤ T, AccIn C T' σ' := by
  obtain ⟨n, -, r⟩ := hr
  obtain ⟨h1, h2⟩ := ha.of_sReachD r
  exact ⟨T - n, Nat.sub_le _ _, h2⟩

theorem AccIn.inv {T : ℕ} {σ : SCfg} (h : AccIn C T σ) :
    Accepting C σ ∨ ∃ T' τ, T = T' + 1 ∧ SStep C σ τ ∧ AccIn C T' τ := by
  obtain ⟨σ', hr, ha⟩ := h
  cases T with
  | zero => cases hr; exact Or.inl ha
  | succ T => obtain ⟨τ, hs, hr'⟩ := hr; exact Or.inr ⟨T, τ, rfl, hs, σ', hr', ha⟩

/-- Along a deterministic step. -/
theorem AccIn.of_det {T : ℕ} {σ τ : SCfg} (hd : DetAt C σ) (hs : SStep C σ τ)
    (h : AccIn C T σ) : ∃ T', T = T' + 1 ∧ AccIn C T' τ := by
  rcases h.inv with ha | ⟨T', τ', rfl, hs', h'⟩
  · exact absurd ha hd.not_accepting
  · obtain rfl := SStep.det hd hs hs'
    exact ⟨T', rfl, h'⟩

theorem not_accIn_of_none {T : ℕ} {σ : SCfg} (h : C[σ.pc]? = none) : ¬ AccIn C T σ :=
  fun ha => not_accFrom_of_none h ha.accFrom

theorem accIn_of_accFrom {σ : SCfg} (h : AccFrom C σ) : ∃ T, AccIn C T σ :=
  let ⟨T, σ', hr, ha⟩ := h; ⟨T, σ', hr, ha⟩

/-! ### Runs with bounded stacks -/

theorem SReachP.trans {P : SCfg → Prop} {m n : ℕ} {σ τ υ : SCfg} (h₁ : SReachP C P m σ τ)
    (h₂ : SReachP C P n τ υ) : SReachP C P (m + n) σ υ := by
  induction m generalizing σ with
  | zero => obtain ⟨rfl, -⟩ := h₁; simpa using h₂
  | succ m ih =>
    obtain ⟨hp, x, hx, hxd⟩ := h₁
    rw [show m + 1 + n = (m + n) + 1 by omega]
    exact ⟨hp, x, hx, ih hxd⟩

theorem SReachP.mono {P Q : SCfg → Prop} (hPQ : ∀ σ, P σ → Q σ) {n : ℕ} {σ τ : SCfg}
    (h : SReachP C P n σ τ) : SReachP C Q n σ τ := by
  induction n generalizing σ with
  | zero => exact ⟨h.1, hPQ _ h.2⟩
  | succ n ih => obtain ⟨hp, x, hx, hxd⟩ := h; exact ⟨hPQ _ hp, x, hx, ih hxd⟩

theorem hgt_mono {K H H' : ℕ} {S : Store} (h : Hgt K H S) (hH : H ≤ H') : Hgt K H' S :=
  fun r hr => le_trans (h r hr) hH

/-- A run of at most `T` steps from stacks of height at most `H` keeps them below `H + T`. -/
theorem sReachP_of_sRun {K H T : ℕ} {σ σ' : SCfg} (hr : SRun C σ σ' T) (hH : Hgt K H σ.S) :
    ∃ n ≤ T, SReachP C (fun τ => Hgt K (H + T) τ.S) n σ σ' := by
  obtain ⟨n, hn, r⟩ := hr
  exact ⟨n, hn, (sReachP_of_sReach n r hH).mono fun τ h => hgt_mono h (by omega)⟩

/-! ### The guessing loop -/

section Loop

variable {g k : ℕ} (hc : C[g]? = some (.choose (g + 1) (g + 3))) (hg : C[g + 1]? = some (.guess k))
  (hj : C[g + 2]? = some (.jmp g))
include hc hg hj

/-- **The guessing loop pushes any string.** -/
theorem loop_run : ∀ (u : List Bool) (S : Store),
    SRun C ⟨g, S⟩ ⟨g + 3, Function.update S k (u.reverse ++ S k)⟩ (3 * u.length + 1) := by
  intro u
  induction u with
  | nil =>
    intro S
    simpa [Function.update_eq_self] using SRun.single (SStep.choose₂ (S := S) hc)
  | cons b u ih =>
    intro S
    have r₁ : SRun C ⟨g, S⟩ ⟨g, Function.update S k (b :: S k)⟩ 3 :=
      ((SRun.single (SStep.choose₁ hc)).trans (SRun.single (SStep.guess b hg))).trans
        (SRun.single (SStep.jmp hj))
    have r₂ := ih (Function.update S k (b :: S k))
    have e : Function.update (Function.update S k (b :: S k)) k
        (u.reverse ++ Function.update S k (b :: S k) k) =
        Function.update S k ((b :: u).reverse ++ S k) := by simp
    rw [e] at r₂
    exact (r₁.trans r₂).mono (by simp; omega)

/-- **The guessing loop pushes some string** (soundness, with the length of the run). -/
theorem loop_sound : ∀ T (S : Store), AccIn C T ⟨g, S⟩ →
    ∃ w T', T' < T ∧ AccIn C T' ⟨g + 3, Function.update S k (w ++ S k)⟩ := by
  have hj' : C[g + 1 + 1]? = some (.jmp g) := hj
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    intro S hacc
    rcases hacc.inv with ha | ⟨T₁, τ, rfl, hs, h₁⟩
    · unfold Accepting at ha; rw [hc] at ha; cases ha
    cases hs with
    | choose₁ h =>
      rw [hc] at h; cases h
      rcases h₁.inv with ha | ⟨T₂, τ₂, rfl, hs₂, h₂⟩
      · unfold Accepting at ha; rw [hg] at ha; cases ha
      cases hs₂ with
      | guess b h =>
        rw [hg] at h; cases h
        rcases h₂.inv with ha | ⟨T₃, τ₃, rfl, hs₃, h₃⟩
        · unfold Accepting at ha; rw [hj'] at ha; cases ha
        cases hs₃ with
        | jmp h =>
          rw [hj'] at h; cases h
          obtain ⟨w, T', hT', hw⟩ := ih T₃ (by omega) _ h₃
          refine ⟨w ++ [b], T', by omega, ?_⟩
          simpa [Function.update_idem] using hw
        | _ => simp_all
      | _ => simp_all
    | choose₂ h =>
      rw [hc] at h; cases h
      exact ⟨[], T₁, by omega, by simpa [Function.update_eq_self] using h₁⟩
    | _ => simp_all

end Loop

end Mach

end HTN
