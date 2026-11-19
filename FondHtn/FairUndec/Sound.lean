import FondHtn.FairUndec.Yield
import FondHtn.HardTR.WSafe
/-!
# Fair solutions give infinite runs

**`FOND.FU.inf_of_fair`**: if the description of a two-stack machine has a fair strong cyclic
solution, the machine has an infinite run from the initial configuration.

A fair solution gives the safe word game on the refinements of the initial network
(`FOND.HardTR.lsafe_of_fairWin`).  Its positions are tracked together with a configuration of
the machine: the state is `{fq q}` for the control state `q`, and every word of the residual
language is an interleaving of run-downs of the two stacks, each followed by the drain of its
bottom (`FOND.FU.Gen`).  The empty word is never in the residual language, drains need `fStop`,
so the move of the game is a transition, popping the top of its stack: a step of the machine.
Following the outcome without `fStop` gives the infinite run.
-/

namespace FOND

namespace FU

open HTN HTN.Syn HTN.Article HTN.Undec AcycHard.Sav HardTR HardTR.TD

variable {M : TSM} {s₁ s₂ : List ℕ}

/-- The residual words of a configuration. -/
def Gen (M : TSM) (c : Cfg) (w : List ℕ) : Prop :=
  ∃ w₁ w₂, RD M false c.s1 w₁ ∧ RD M true c.s2 w₂ ∧ Interleave (w₁ ++ [aD]) (w₂ ++ [aD]) w

/-- The stack `b` of a configuration. -/
def stkC (c : Cfg) (b : Bool) : List ℕ := if b then c.s2 else c.s1

/-- The configuration after the transition `n`, the stack `stk n` being `pop :: rest`. -/
def nxt (M : TSM) (c : Cfg) (n : ℕ) (rest : List ℕ) : Cfg :=
  if (tr M n).stk then ⟨(tr M n).tgt, c.s1, (tr M n).push ++ rest⟩
  else ⟨(tr M n).tgt, (tr M n).push ++ rest, c.s2⟩

theorem gen_ne_nil {c : Cfg} (h : Gen M c []) : False := by
  obtain ⟨w₁, w₂, h1, h2, hi⟩ := h
  have := (Interleave.eq_nil_of_left hi).1
  simp at this

/-- **The first letter of a residual word.** -/
theorem gen_cons {c : Cfg} {x : ℕ} {w : List ℕ} (h : Gen M c (x :: w)) :
    x = aD ∨ ∃ n < M.trans.length, x = aT n ∧ ∃ rest,
      stkC c (tr M n).stk = (tr M n).pop :: rest ∧ Gen M (nxt M c n rest) w := by
  obtain ⟨w₁, w₂, h₁, h₂, hi⟩ := h
  generalize hS1 : c.s1 = S1 at h₁
  generalize hS2 : c.s2 = S2 at h₂
  generalize hA : w₁ ++ [aD] = A at hi
  generalize hB : w₂ ++ [aD] = B at hi
  generalize hZ : x :: w = Z at hi
  cases hi with
  | nil => simp at hZ
  | left a h =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hZ
    rcases w₁ with _ | ⟨y, w₁⟩
    · simp at hA; exact Or.inl hA.1.symm
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      cases h₁ with
      | drain _ => exact Or.inl rfl
      | @step n rest _ hn hb hr =>
        refine Or.inr ⟨n, hn, rfl, rest, by simp [stkC, hb, hS1], w₁, w₂, ?_, ?_, ?_⟩
        · simpa [nxt, hb] using hr
        · simpa [nxt, hb, hS2] using h₂
        · rw [hB]; exact h
  | right a h =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hZ
    rcases w₂ with _ | ⟨y, w₂⟩
    · simp at hB; exact Or.inl hB.1.symm
    · simp only [List.cons_append, List.cons.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      cases h₂ with
      | drain _ => exact Or.inl rfl
      | @step n rest _ hn hb hr =>
        refine Or.inr ⟨n, hn, rfl, rest, by simp [stkC, hb, hS2], w₁, w₂, ?_, ?_, ?_⟩
        · simpa [nxt, hb, hS1] using h₁
        · simpa [nxt, hb] using hr
        · rw [hA]; exact h

theorem tr_mem {n : ℕ} (hn : n < M.trans.length) : tr M n ∈ M.trans := by
  rw [tr, List.getD_eq_getElem _ _ hn]; exact List.getElem_mem hn

theorem step_nxt {c : Cfg} {n : ℕ} (hn : n < M.trans.length) (hsrc : c.st = (tr M n).src)
    {rest : List ℕ} (h : stkC c (tr M n).stk = (tr M n).pop :: rest) : M.Step c (nxt M c n rest) := by
  refine ⟨tr M n, tr_mem hn, hsrc, ?_⟩
  cases hb : (tr M n).stk
  · rw [hb] at h
    exact Or.inl ⟨rfl, rest, by simpa [stkC] using h, by simp [nxt, hb]⟩
  · rw [hb] at h
    exact Or.inr ⟨rfl, rest, by simpa [stkC] using h, by simp [nxt, hb]⟩

/-- **Fair solutions give infinite runs.** -/
theorem inf_of_fair (h : (desc M s₁ s₂).toProblem.MPStrongCyclicFairSolvable) :
    Inf M ⟨M.start, s₁, s₂⟩ := by
  set d := desc M s₁ s₂ with hd
  have hv := valid M s₁ s₂
  have hP := FProbDesc.toProblem_wf hv
  have hfw := (Problem.mpStrongCyclicFairSolvable_iff_prog hP.tnI).1 h
  obtain ⟨R, hR0, hcl⟩ := lsafe_of_fairWin hP hfw
  have hD : (skelAt d.toProblem d.toProblem.tnI).domain.methods =
      {m | ∃ e ∈ meths M s₁ s₂, e.toMethod = m} := by
    simp only [skelAt, Problem.skeleton, Problem.domain, FProbDesc.toProblem, hd, desc,
      FProbDesc.methods]
  have hmwf : ∀ m ∈ (skelAt d.toProblem d.toProblem.tnI).domain.methods, m.subtasks.WF := by
    rw [hD]; rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _
  have hne : ∀ x s, (d.toProblem.δ x).Applicable s → ((d.toProblem.δ x).outcomes s).Nonempty := by
    intro x s _
    obtain ⟨⟨e, he⟩, -⟩ := FProbDesc.δ_wf hv x
    exact ⟨_, e, he, rfl⟩
  -- the invariant
  let Inv : Cfg → Set (List ℕ) × Set ℕ → Prop := fun c p =>
    p ∈ R ∧ p.2 = {fq c.st} ∧ ∀ w ∈ p.1, Gen M c w
  have hstep : ∀ c p, Inv c p → ∃ c' p', M.Step c c' ∧ Inv c' p' := by
    rintro c ⟨L, s⟩ ⟨hp, hs, hgen⟩
    simp only at hs hgen
    subst hs
    obtain ⟨-, hmove⟩ := hcl _ hp
    rcases hmove with hnil | ⟨x, happ, hall⟩
    · exact (gen_ne_nil (hgen _ hnil)).elim
    obtain ⟨s'', hs''⟩ := hne x _ happ
    obtain ⟨⟨w, hw⟩, -⟩ := hcl _ (hall s'' hs'')
    rcases gen_cons (hgen _ hw) with rfl | ⟨n, hn, rfl, rest, hrest, -⟩
    · rw [δ_aD, app_aD] at happ
      exact absurd (Set.mem_singleton_iff.1 happ) (fq_ne_stop _).symm
    rw [δ_aT M s₁ s₂ hn, app_aT] at happ
    have hsrc : c.st = (tr M n).src := fq_inj (Set.mem_singleton_iff.1 happ.1).symm
    refine ⟨nxt M c n rest, ({w | aT n :: w ∈ L}, {fq (tr M n).tgt}), step_nxt hn hsrc hrest, ?_, ?_, ?_⟩
    · apply hall
      show _ ∈ ((desc M s₁ s₂).toProblem.δ (aT n)).outcomes {fq c.st}
      rw [δ_aT M s₁ s₂ hn, outcomes_aT]
      left
      ext f
      simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, hsrc]
      tauto
    · simp [nxt]; split_ifs <;> rfl
    · intro w' hw'
      rcases gen_cons (hgen _ hw') with he | ⟨n', hn', he, rest', hrest', hg⟩
      · exact absurd he (aT_ne_aD n)
      obtain rfl := aT_inj he
      rw [hrest] at hrest'
      obtain rfl := (List.cons.inj hrest').2
      exact hg
  have h0 : Inv ⟨M.start, s₁, s₂⟩ ({as | (skelAt d.toProblem d.toProblem.tnI).domain.NetYield
      d.toProblem.tnI as}, d.toProblem.init) := by
    refine ⟨hR0, ?_, fun w hw => ?_⟩
    · ext f; simp [hd, desc, FProbDesc.toProblem, FProbDesc.init]
    · have htn : d.toProblem.tnI = (seqTn [(true, root0)]).toTaskNetwork := by
        simp only [FProbDesc.toProblem, hd, desc, FProbDesc.tnI]
      rw [Set.mem_setOf_eq, htn] at hw
      exact netYield_tnI hmwf hD hw
  let g : ℕ → {q : Cfg × (Set (List ℕ) × Set ℕ) // Inv q.1 q.2} := fun k =>
    Nat.rec ⟨(_, _), h0⟩ (fun _ q => ⟨((hstep _ _ q.2).choose, (hstep _ _ q.2).choose_spec.choose),
      (hstep _ _ q.2).choose_spec.choose_spec.2⟩) k
  exact ⟨fun k => (g k).1.1, rfl, fun k => (hstep _ _ (g k).2).choose_spec.choose_spec.1⟩

end FU

end FOND
