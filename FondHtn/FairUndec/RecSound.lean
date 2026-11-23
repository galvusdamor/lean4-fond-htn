import FondHtn.FairUndec.Complete
import FondHtn.FairUndec.Live
/-!
# Fair solutions give recurrent runs

**`FOND.FU.rec_of_fair`**: if the description with ticks on the transitions into the states
satisfying `tk` has a fair strong cyclic solution, the machine has a run that enters such a state
infinitely often.

The live word game (`FOND.FU.llive_of_fairWin`) is tracked together with a configuration as in
`FOND.FU.inf_of_fair`.  At every position the attractor provides a transition and an outcome of
lower rank.  If that outcome is the tick, the transition enters a `tk`-state; otherwise the run
continues at a position of lower rank.  Ranks cannot decrease forever, so ticks recur.
-/

namespace FOND

namespace FU

open HTN HTN.Syn HTN.Article HTN.Undec AcycHard.Sav HardTR HardTR.TD

variable {M : TSM} {s₁ s₂ : List ℕ} {tk : ℕ → Bool}

/-- **Fair solutions give recurrent runs.** -/
theorem rec_of_fair (h : (desc M s₁ s₂ tk).toProblem.MPStrongCyclicFairSolvable) :
    Rec tk M ⟨M.start, s₁, s₂⟩ := by
  set d := desc M s₁ s₂ tk with hd
  have hv := valid M s₁ s₂ tk
  have hP := FProbDesc.toProblem_wf hv
  have hfw := (Problem.mpStrongCyclicFairSolvable_iff_prog hP.tnI).1 h
  obtain ⟨R, hR0, hcl⟩ := llive_of_fairWin hP hfw
  have hD : (skelAt d.toProblem d.toProblem.tnI).domain.methods =
      {m | ∃ e ∈ meths M s₁ s₂, e.toMethod = m} := by
    simp only [skelAt, Problem.skeleton, Problem.domain, FProbDesc.toProblem, hd, desc,
      FProbDesc.methods]
  have hmwf : ∀ m ∈ (skelAt d.toProblem d.toProblem.tnI).domain.methods, m.subtasks.WF := by
    rw [hD]; rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _
  -- the invariant
  let Inv : Cfg → Set (List ℕ) × Set ℕ → Prop := fun c p =>
    p ∈ R ∧ p.2 = {fq c.st} ∧ ∀ w ∈ p.1, Gen M c w
  let LA := LAttr (fun a s => (d.toProblem.δ a).Applicable s) (fun a s => (d.toProblem.δ a).outcomes s) R
  have hstep : ∀ k c p, LA k p → Inv c p → ∃ c' p', M.Step c c' ∧ Inv c' p' ∧
      (tk c'.st = true ∨ ∃ k' < k, LA k' p') := by
    rintro k c ⟨L, s⟩ hl ⟨hp, hs, hgen⟩
    simp only at hs hgen
    subst hs
    cases hl with
    | goal hnil => exact (gen_ne_nil (hgen _ hnil)).elim
    | @move n _ _ x happ hall s₀ hs₀ hl =>
      obtain ⟨⟨w, hw⟩, -⟩ := hcl _ (hall s₀ hs₀)
      rcases gen_cons (hgen _ hw) with rfl | ⟨n', hn, rfl, rest, hrest, -⟩
      · rw [δ_aD, app_aD] at happ
        exact absurd (Set.mem_singleton_iff.1 happ) (fq_ne_stop _).symm
      rw [δ_aT M s₁ s₂ tk hn, app_aT] at happ
      have hsrc : c.st = (tr M n').src := fq_inj (Set.mem_singleton_iff.1 happ.1).symm
      have hcont : ({fq c.st} \ {fq (tr M n').src}) ∪ {fq (tr M n').tgt} = ({fq (tr M n').tgt} : Set ℕ) := by
        ext f; simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, hsrc]; tauto
      have hout : (d.toProblem.δ (aT n')).outcomes {fq c.st} =
          insert {fq (tr M n').tgt} {s' | tk (tr M n').tgt = true ∧ s' = {fq c.st} ∪ {fStop}} := by
        rw [hd, δ_aT M s₁ s₂ tk hn, outcomes_aT, hcont]
      have hst : (nxt M c n' rest).st = (tr M n').tgt := by simp [nxt]; split_ifs <;> rfl
      refine ⟨nxt M c n' rest, ({w | aT n' :: w ∈ L}, {fq (tr M n').tgt}), step_nxt hn hsrc hrest,
        ⟨hall _ (by rw [hout]; exact Or.inl rfl), by rw [hst], ?_⟩, ?_⟩
      · intro w' hw'
        rcases gen_cons (hgen _ hw') with he | ⟨n'', hn'', he, rest', hrest', hg⟩
        · exact absurd he (aT_ne_aD n')
        obtain rfl := aT_inj he
        rw [hrest] at hrest'
        obtain rfl := (List.cons.inj hrest').2
        exact hg
      · rw [hout] at hs₀
        rcases hs₀ with rfl | ⟨htk, -⟩
        · exact Or.inr ⟨n, by omega, hl⟩
        · exact Or.inl (by rw [hst]; exact htk)
  have h0 : Inv ⟨M.start, s₁, s₂⟩ ({as | (skelAt d.toProblem d.toProblem.tnI).domain.NetYield
      d.toProblem.tnI as}, d.toProblem.init) := by
    refine ⟨hR0, ?_, fun w hw => ?_⟩
    · ext f; simp [hd, desc, FProbDesc.toProblem, FProbDesc.init]
    · have htn : d.toProblem.tnI = (seqTn [(true, root0)]).toTaskNetwork := by
        simp only [FProbDesc.toProblem, hd, desc, FProbDesc.tnI]
      rw [Set.mem_setOf_eq, htn] at hw
      exact netYield_tnI hmwf hD hw
  -- the rank of a position
  have hex : ∀ p, p ∈ R → ∃ k, LA k p := fun p hp => (hcl p hp).2
  open Classical in
  let rk : {q : Cfg × (Set (List ℕ) × Set ℕ) // Inv q.1 q.2} → ℕ := fun q => Nat.find (hex _ q.2.1)
  have hrk : ∀ q, LA (rk q) q.1.2 := fun q => Nat.find_spec (hex _ q.2.1)
  have hrk_le : ∀ q k, LA k q.1.2 → rk q ≤ k := fun q k hk => Nat.find_min' _ hk
  let nx : {q : Cfg × (Set (List ℕ) × Set ℕ) // Inv q.1 q.2} →
      {q : Cfg × (Set (List ℕ) × Set ℕ) // Inv q.1 q.2} := fun q =>
    ⟨((hstep _ _ _ (hrk q) q.2).choose, (hstep _ _ _ (hrk q) q.2).choose_spec.choose),
      (hstep _ _ _ (hrk q) q.2).choose_spec.choose_spec.2.1⟩
  have hnx : ∀ q, M.Step q.1.1 (nx q).1.1 ∧ (tk (nx q).1.1.st = true ∨ rk (nx q) < rk q) := by
    intro q
    have hs := (hstep _ _ _ (hrk q) q.2).choose_spec.choose_spec
    refine ⟨hs.1, ?_⟩
    rcases hs.2.2 with ht | ⟨k', hk', hl⟩
    · exact Or.inl ht
    · exact Or.inr (lt_of_le_of_lt (hrk_le (nx q) k' hl) hk')
  let g : ℕ → {q : Cfg × (Set (List ℕ) × Set ℕ) // Inv q.1 q.2} := fun k =>
    Nat.rec ⟨(_, _), h0⟩ (fun _ q => nx q) k
  refine ⟨fun k => (g k).1.1, rfl, fun k => (hnx (g k)).1, ?_⟩
  have hrec : ∀ r i, rk (g i) = r → ∃ j, i ≤ j ∧ tk (g (j + 1)).1.1.st = true := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro i hi
      rcases (hnx (g i)).2 with ht | hlt
      · exact ⟨i, le_rfl, ht⟩
      · obtain ⟨j, hj, ht⟩ := ih _ (hi ▸ hlt) (i + 1) rfl
        exact ⟨j, by omega, ht⟩
  exact fun i => hrec _ i rfl

/-- **Fair solvability of the description is recurrence.** -/
theorem fair_iff_rec :
    (desc M s₁ s₂ tk).toProblem.MPStrongCyclicFairSolvable ↔ Rec tk M ⟨M.start, s₁, s₂⟩ :=
  ⟨rec_of_fair, fair_of_rec⟩

end FU

end FOND
