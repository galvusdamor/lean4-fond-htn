import ComplexityTheory.Machine.SimRun
/-!
# A single-tape Turing machine simulating a stack machine: runs

* `HTN.Mach.sim_step` — every step of the stack machine is simulated (completeness, with time
  and space bounds);
* `HTN.Mach.sim_back` — every accepting run of the simulating machine from `good n σ` begins
  with the simulation of a step of the stack machine, unless `σ` accepts (soundness);
* `HTN.Mach.sim_reach` — runs of the stack machine along which the stacks stay of height at most
  `H` are simulated within the space `n + 2 + (H + 1) * (K + 1)`;
* `HTN.Mach.sim_sound` — an accepting run of the simulating machine from `good n σ` gives an
  accepting run of the stack machine from `σ`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM

/-- The stack an instruction works on. -/
def Ins.stk : Ins → Option ℕ
  | .push k _ => some k
  | .pop k => some k
  | .br k _ _ _ => some k
  | .guess k => some k
  | _ => none

/-- The machine only uses the stacks `0, …, K - 1`. -/
def ProgWF (C : List Ins) (K : ℕ) : Prop :=
  ∀ (pc : ℕ) (ins : Ins), C[pc]? = some ins → ∀ k, Ins.stk ins = some k → k < K

/-- All stacks below `K` have height at most `H`. -/
def Hgt (K H : ℕ) (S : Store) : Prop := ∀ r < K, (S r).length ≤ H

variable {C : List Ins} {K kin : ℕ}

theorem hgt_cell {n H : ℕ} {S : Store} (hH : Hgt K H S) {k : ℕ} (hk : k < K) :
    cell K n (S k).length K < n + 2 + (H + 1) * (K + 1) := by
  have := hH k hk
  unfold cell; nlinarith

theorem step_good_stay {n pc : ℕ} {S : Store} {q : QS} :
    nxt (good K n ⟨pc, S⟩) (q, lay K n S (home K n), .stay) = ⟨q, home K n, lay K n S⟩ := by
  simp [nxt, good, Move.apply]

theorem execTr_eq {pc : ℕ} {ins : Ins} (h : C[pc]? = some ins) (γ : Sym) :
    δ C K kin (.base (.exec pc)) γ = execTr C K pc γ := rfl

/-- The simulation of a jump. -/
theorem seg_jmp {Sp n pc a : ℕ} (S : Store) (hpc : C[pc]? = some (.jmp a)) (hSp : home K n < Sp) :
    (simM C K kin).Seg Sp (good K n ⟨pc, S⟩) (good K n ⟨a, S⟩) 1 := by
  have h := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp) (c := good K n ⟨pc, S⟩)
    (t := (.base (.exec a), lay K n S (home K n), .stay))
    (by simp only [good, δ, phaseTr, execTr, hpc]) (notAcc_exec (by rw [hpc]; simp)) hSp hSp
  rwa [step_good_stay] at h

/-- **Completeness for one step.** -/
theorem sim_step (hwf : ProgWF C K) {σ σ' : SCfg} (h : SStep C σ σ') {n H : ℕ}
    (hH : Hgt K H σ.S) :
    ∃ m ≤ 3 * (H + 2) * (K + 1),
      (simM C K kin).ReachesSpace (n + 2 + (H + 1) * (K + 1)) m (good K n σ) (good K n σ') := by
  have hhome : home K n < n + 2 + (H + 1) * (K + 1) := by unfold home; nlinarith
  cases h with
  | @push pc k b S hpc =>
    have hk := hwf _ _ hpc k rfl
    have hl := hH k hk
    refine ⟨_, ?_, (seg_push (kin := kin) S hpc hk (hgt_cell hH hk)).reach⟩
    have : K - k - 1 ≤ K := by omega
    have : K - k ≤ K := by omega
    nlinarith
  | @pop pc k S hpc =>
    have hk := hwf _ _ hpc k rfl
    obtain ⟨m, hs, -, hm⟩ := seg_pop (kin := kin) (n := n) S hpc hk (hgt_cell hH hk)
    exact ⟨m, le_trans hm (by have := hH k hk; nlinarith), hs.reach⟩
  | @brNil pc k a₀ aF aT S hpc hS =>
    have hk := hwf _ _ hpc k rfl
    obtain ⟨m, hs, -, hm⟩ := seg_br (kin := kin) (n := n) S hpc hk (hgt_cell hH hk)
    rw [hS] at hs
    exact ⟨m, le_trans hm (by have := hH k hk; nlinarith), hs.reach⟩
  | @brF pc k a₀ aF aT S r hpc hS =>
    have hk := hwf _ _ hpc k rfl
    obtain ⟨m, hs, -, hm⟩ := seg_br (kin := kin) (n := n) S hpc hk (hgt_cell hH hk)
    rw [hS] at hs
    exact ⟨m, le_trans hm (by have := hH k hk; nlinarith), hs.reach⟩
  | @brT pc k a₀ aF aT S r hpc hS =>
    have hk := hwf _ _ hpc k rfl
    obtain ⟨m, hs, -, hm⟩ := seg_br (kin := kin) (n := n) S hpc hk (hgt_cell hH hk)
    rw [hS] at hs
    exact ⟨m, le_trans hm (by have := hH k hk; nlinarith), hs.reach⟩
  | @jmp pc a S hpc =>
    exact ⟨1, by nlinarith, (seg_jmp (kin := kin) S hpc hhome).reach⟩
  | @guess pc k S b hpc =>
    replace hH : Hgt K H S := hH
    have hk := hwf _ _ hpc k rfl
    have hc := hgt_cell (n := n) hH hk
    have h1 := seg_guess_pre (kin := kin) S hpc hk hc
    set c : Config QS Sym := ⟨QS.base (.scan .guess k (some (pc + 1)) (decide ((S k).length = 0))),
      cell K n (S k).length k, lay K n S⟩ with hcdef
    have hstep : (simM C K kin).Step c (nxt c (mvTo true (K - k) (.rScan (some (pc + 1))), some b,
        .stay)) := by
      rw [step_iff]
      refine ⟨_, ?_, rfl⟩
      rw [show c.tape c.head = lay K n S (cell K n (S k).length k) from rfl, δ_guess S hk]
      cases b <;> simp
    have h2 := seg_push_tail (C := C) (kin := kin) (n := n)
      (Sp := n + 2 + (H + 1) * (K + 1)) S hk b (some (pc + 1)) hc
    have hc' : cell K n (S k).length k < n + 2 + (H + 1) * (K + 1) := by
      unfold cell at hc ⊢; omega
    refine ⟨_, ?_, (h1.reach.trans _ (NTM.ReachesSpace.single _ hstep hc' hc')).trans _ h2.reach⟩
    have hl := hH k hk
    have : K - k - 1 ≤ K := by omega
    have : K - k ≤ K := by omega
    nlinarith
  | @choose₁ pc a₁ a₂ S hpc =>
    refine ⟨1, by nlinarith, NTM.ReachesSpace.single _ ?_ hhome hhome⟩
    rw [step_iff]
    exact ⟨(.base (.exec a₁), lay K n S (home K n), .stay),
      by simp [good, δ, phaseTr, execTr, hpc], step_good_stay.symm⟩
  | @choose₂ pc a₁ a₂ S hpc =>
    refine ⟨1, by nlinarith, NTM.ReachesSpace.single _ ?_ hhome hhome⟩
    rw [step_iff]
    exact ⟨(.base (.exec a₂), lay K n S (home K n), .stay),
      by simp [good, δ, phaseTr, execTr, hpc], step_good_stay.symm⟩

/-- **Soundness for one step.** -/
theorem sim_back (hwf : ProgWF C K) {σ : SCfg} {n N : ℕ} {d : Config QS Sym}
    (hr : (simM C K kin).Reaches N (good K n σ) d) (hd : d.state ∈ (simM C K kin).accept) :
    Accepting C σ ∨ ∃ σ', SStep C σ σ' ∧ ∃ N' < N, (simM C K kin).Reaches N' (good K n σ') d := by
  obtain ⟨pc, S⟩ := σ
  -- a segment out of `good` ending in `good σ'` gives the claim
  have viaSeg : ∀ {σ' : SCfg} {m Sp : ℕ}, SStep C ⟨pc, S⟩ σ' → 1 ≤ m →
      (simM C K kin).Seg Sp (good K n ⟨pc, S⟩) (good K n σ') m →
      ∃ σ', SStep C ⟨pc, S⟩ σ' ∧ ∃ N' < N, (simM C K kin).Reaches N' (good K n σ') d := by
    intro σ' m Sp hs hm hseg
    obtain ⟨hmN, hr'⟩ := hseg.passes N d hr hd
    exact ⟨σ', hs, N - m, by omega, hr'⟩
  rcases hpc : C[pc]? with _ | ins
  · -- outside the program: no transition
    exfalso
    obtain ⟨n', e, -, he, -⟩ := NTM.exists_step_of_reaches hr hd (notAcc_exec (by rw [hpc]; simp))
    rw [step_iff] at he
    obtain ⟨t, ht, -⟩ := he
    simp [good, δ, phaseTr, execTr, hpc] at ht
  cases ins with
  | accept => exact Or.inl hpc
  | push k b =>
    have hk := hwf _ _ hpc k rfl
    exact Or.inr (viaSeg (SStep.push hpc) (by omega)
      (seg_push (kin := kin) (Sp := cell K n (S k).length K + 1) S hpc hk (by omega)))
  | pop k =>
    have hk := hwf _ _ hpc k rfl
    obtain ⟨m, hs, hm, -⟩ := seg_pop (kin := kin) (n := n) (Sp := cell K n (S k).length K + 1)
      S hpc hk (by omega)
    exact Or.inr (viaSeg (SStep.pop hpc) hm hs)
  | br k a₀ aF aT =>
    have hk := hwf _ _ hpc k rfl
    obtain ⟨m, hs, hm, -⟩ := seg_br (kin := kin) (n := n) (Sp := cell K n (S k).length K + 1)
      S hpc hk (by omega)
    rcases hS : S k with _ | ⟨c, r⟩
    · rw [hS] at hs; exact Or.inr (viaSeg (SStep.brNil hpc hS) hm hs)
    · cases c
      · rw [hS] at hs; exact Or.inr (viaSeg (SStep.brF hpc hS) hm hs)
      · rw [hS] at hs; exact Or.inr (viaSeg (SStep.brT hpc hS) hm hs)
  | jmp a =>
    exact Or.inr (viaSeg (SStep.jmp hpc) le_rfl
      (seg_jmp (kin := kin) (Sp := home K n + 1) S hpc (by omega)))
  | guess k =>
    have hk := hwf _ _ hpc k rfl
    have h1 := seg_guess_pre (kin := kin) (n := n) (Sp := cell K n (S k).length K + 1) S hpc hk
      (by omega)
    obtain ⟨hm₁, hr₁⟩ := h1.passes N d hr hd
    obtain ⟨n', e, hn', he, hr₂⟩ := NTM.exists_step_of_reaches hr₁ hd
      (notAcc_base (by intro pc h; cases h))
    rw [step_iff] at he
    obtain ⟨t, ht, rfl⟩ := he
    dsimp only at ht
    rw [δ_guess S hk] at ht
    have key : ∀ b : Bool, t = (mvTo true (K - k) (.rScan (some (pc + 1))), some b, .stay) →
        Accepting C ⟨pc, S⟩ ∨ ∃ σ', SStep C ⟨pc, S⟩ σ' ∧ ∃ N' < N,
          (simM C K kin).Reaches N' (good K n σ') d := by
      rintro b rfl
      have h2 := seg_push_tail (C := C) (kin := kin) (n := n)
        (Sp := cell K n (S k).length K + 1) S hk b (some (pc + 1)) (by omega)
      obtain ⟨hm₂, hr₃⟩ := h2.passes _ d hr₂ hd
      exact Or.inr ⟨_, SStep.guess b hpc, _, by omega, hr₃⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht
    · exact key false ht
    · exact key true ht
  | choose a₁ a₂ =>
    obtain ⟨n', e, hn', he, hr'⟩ := NTM.exists_step_of_reaches hr hd
      (notAcc_exec (by rw [hpc]; simp))
    rw [step_iff] at he
    obtain ⟨t, ht, rfl⟩ := he
    simp only [good, δ, phaseTr, execTr, hpc, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact Or.inr ⟨⟨a₁, S⟩, SStep.choose₁ hpc, n', by omega, by
        rw [show nxt _ _ = good K n ⟨a₁, S⟩ from step_good_stay] at hr'; exact hr'⟩
    · exact Or.inr ⟨⟨a₂, S⟩, SStep.choose₂ hpc, n', by omega, by
        rw [show nxt _ _ = good K n ⟨a₂, S⟩ from step_good_stay] at hr'; exact hr'⟩

/-- **Soundness**: an accepting run of the simulating machine from `good n σ` gives an accepting
run of the stack machine from `σ`. -/
theorem sim_sound (hwf : ProgWF C K) {n : ℕ} :
    ∀ N {σ : SCfg} {d : Config QS Sym}, (simM C K kin).Reaches N (good K n σ) d →
      d.state ∈ (simM C K kin).accept → ∃ T σ', SReach C T σ σ' ∧ Accepting C σ' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro σ d hr hd
    rcases sim_back hwf hr hd with h | ⟨σ', hs, N', hN', hr'⟩
    · exact ⟨0, σ, rfl, h⟩
    · obtain ⟨T, σ'', hT, hacc⟩ := ih N' hN' hr' hd
      exact ⟨T + 1, σ'', ⟨σ', hs, hT⟩, hacc⟩

/-- Runs of the stack machine along which every configuration satisfies `P`. -/
def SReachP (C : List Ins) (P : SCfg → Prop) : ℕ → SCfg → SCfg → Prop
  | 0, σ, σ' => σ = σ' ∧ P σ
  | n + 1, σ, σ' => P σ ∧ ∃ τ, SStep C σ τ ∧ SReachP C P n τ σ'

/-- **Completeness**: a run of `T` steps of the stack machine with stacks of height at most `H`
is simulated in at most `T * 3 * (H + 2) * (K + 1)` steps within the space
`n + 2 + (H + 1) * (K + 1)`. -/
theorem sim_reach (hwf : ProgWF C K) {n H : ℕ} :
    ∀ T {σ σ' : SCfg}, SReachP C (fun τ => Hgt K H τ.S) T σ σ' →
      ∃ m ≤ T * (3 * (H + 2) * (K + 1)),
        (simM C K kin).ReachesSpace (n + 2 + (H + 1) * (K + 1)) m (good K n σ) (good K n σ') := by
  have hhome : home K n < n + 2 + (H + 1) * (K + 1) := by unfold home; nlinarith
  intro T
  induction T with
  | zero =>
    rintro σ σ' ⟨rfl, -⟩
    exact ⟨0, Nat.zero_le _, NTM.ReachesSpace.refl _ hhome⟩
  | succ T ih =>
    rintro σ σ' ⟨hP, τ, hs, hr⟩
    obtain ⟨m₁, hm₁, r₁⟩ := sim_step (kin := kin) (n := n) hwf hs hP
    obtain ⟨m₂, hm₂, r₂⟩ := ih hr
    exact ⟨m₁ + m₂, by rw [Nat.succ_mul]; omega, r₁.trans _ r₂⟩

/-- A step changes the height of each stack by at most one. -/
theorem hgt_step {σ τ : SCfg} (h : SStep C σ τ) {H : ℕ} (hH : Hgt K H σ.S) :
    Hgt K (H + 1) τ.S := by
  intro r hr
  have h0 := hH r hr
  cases h with
  | push _ | guess _ _ =>
    dsimp only at h0 ⊢
    simp only [Function.update_apply]
    split_ifs with e
    · subst e; simp; omega
    · omega
  | pop _ =>
    dsimp only at h0 ⊢
    simp only [Function.update_apply]
    split_ifs with e
    · subst e; simp; omega
    · omega
  | _ => dsimp only at h0 ⊢; omega

/-- Along a run of `T` steps the heights grow by at most `T`. -/
theorem sReachP_of_sReach {H : ℕ} :
    ∀ T {σ σ' : SCfg}, SReach C T σ σ' → Hgt K H σ.S →
      SReachP C (fun τ => Hgt K (H + T) τ.S) T σ σ' := by
  intro T
  induction T generalizing H with
  | zero => rintro σ σ' rfl hH; exact ⟨rfl, by simpa using hH⟩
  | succ T ih =>
    rintro σ σ' ⟨τ, hs, hr⟩ hH
    refine ⟨fun r hr' => by have := hH r hr'; omega, τ, hs, ?_⟩
    have := ih hr (hgt_step hs hH)
    rwa [show H + 1 + T = H + (T + 1) by omega] at this

end Mach

end HTN
