import HtnComplexity.TMEnc.TMEncFixSplit
import HtnComplexity.TMEnc.TMEncFixPlanRounds
/-!
# The data of a solution plan of the repaired encoding

`HTN.TMEnc.isSolutionPlanFix_normalForm` says that a solution plan of the repaired problem is an
interleaving of the stream of the head counter, of the runs of `K + 1` cell counters and of the
`(K+1)²` cells of the tape, followed by one accepting test.  `HTN.TMEnc.SolutionPlanData` bundles
that decomposition, so that the lock-step argument can refer to it without carrying a dozen
hypotheses; `HTN.TMEnc.exists_planData` produces it from a solution plan.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- Every element on the right of a `List.Forall₂` is related to one on the left. -/
lemma exists_left_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b}, b ∈ l₂ → ∃ a ∈ l₁, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; simp at hb
  | @cons a b la lb hab _ ih =>
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact ⟨a, by simp, hab⟩
      · obtain ⟨a', ha', hR⟩ := ih hc'
        exact ⟨a', by simp [ha'], hR⟩

/-- Every element on the left of a `List.Forall₂` is related to one on the right. -/
lemma exists_right_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a}, a ∈ l₁ → ∃ b ∈ l₂, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro a ha; simp at ha
  | @cons a b la lb hab _ ih =>
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact ⟨b, by simp, hab⟩
      · obtain ⟨b', hb', hR⟩ := ih hc'
        exact ⟨b', by simp [hb'], hR⟩

/-- **The decomposition of a solution plan of the repaired problem.**

The `K + 1` cell counters are indexed by their position in `ass`; counter `j` has the leading
delay `d j` — the delays are a permutation of `0, …, K` (`dle`, `dinj`) — takes the decisions
`P j t` and tests the symbols `cc j t`. -/
structure SolutionPlanData (N : NTM Q Γ) (w : List Γ) (K : ℕ) where
  /-- The symbols the tape writes out. -/
  sym : ℕ → Option Γ
  /-- The leading delay of the cell counter number `j`. -/
  d : ℕ → ℕ
  /-- The decisions of the cell counter number `j`. -/
  P : ℕ → ℕ → List (TMAct Q Γ)
  /-- The symbols the cell counter number `j` tests. -/
  cc : ℕ → ℕ → Option Γ
  /-- The runs of the `K + 1` cell counters. -/
  ass : List (List (TMAct Q Γ))
  /-- The interleaving of the cell counters. -/
  ac : List (TMAct Q Γ)
  /-- The interleaving of the cell counters with the tape. -/
  bs : List (TMAct Q Γ)
  /-- The plan without its final accepting test. -/
  as₁ : List (TMAct Q Γ)
  /-- The accepting state the plan tests for. -/
  f : Q
  /-- The first block of the tape is the input, padded with blanks. -/
  initSym : ∀ j ≤ K, sym j = tapeInitSym N w j
  /-- Every block of the tape starts with the separator. -/
  sepSym : ∀ i ≤ K, sym (i * (K + 1)) = none
  /-- There are `K + 1` cell counters. -/
  card : ass.length = K + 1
  /-- No counter waits longer than a block. -/
  dle : ∀ j < K + 1, d j ≤ K
  /-- Different counters have different delays. -/
  dinj : ∀ j₁ < K + 1, ∀ j₂ < K + 1, d j₁ = d j₂ → j₁ = j₂
  /-- Every decision of every counter is a decision of the encoding. -/
  decisions : ∀ j < K + 1, ∀ t < K, StepDecision N w K (P j t)
  /-- Each component is the run of the corresponding cell counter. -/
  runs : ∀ j, ∀ hj : j < ass.length, ass[j] = counterRun Q Γ K (d j) (K - d j) (P j) (cc j)
  /-- The cell counters are interleaved. -/
  hil : InterleaveList ass ac
  /-- The tape is interleaved with them. -/
  hac : Interleave ac (tapeStream Q Γ K sym) bs
  /-- The head counter is interleaved with all of them. -/
  hbs : Interleave (headStream Q Γ K) bs as₁
  /-- The state the plan tests for is accepting. -/
  accept : f ∈ N.accept
  /-- The plan is a solution plan. -/
  isPlan : (problemFix N w K).IsSolutionPlan (as₁ ++ [TMAct.check (TMFact.st f)])

namespace SolutionPlanData

variable (D : SolutionPlanData N w K)

/-- Each component of the decomposition is the run of a cell counter. -/
lemma isCounter : ∀ l ∈ D.ass, ∃ (d e : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ),
    (∀ t < K, StepDecision N w K (P t)) ∧ l = counterRun Q Γ K d e P c := by
  intro l hl
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hj' : j < K + 1 := by rw [← D.card]; exact hj
  exact ⟨D.d j, K - D.d j, D.P j, D.cc j, D.decisions j hj', D.runs j hj⟩

end SolutionPlanData

/-- **Every solution plan of the repaired problem decomposes.** -/
theorem exists_planData (hw : 1 ≤ w.length) (hwK : w.length ≤ K) {as : List (TMAct Q Γ)}
    (h : (problemFix N w K).IsSolutionPlan as) :
    ∃ D : SolutionPlanData N w K, as = D.as₁ ++ [TMAct.check (TMFact.st D.f)] := by
  classical
  obtain ⟨sym, ps, ass, ac, bs, as₁, f, hinit, hsep, hperm, hruns, hil, hint', hint, hf, rfl,
    happ⟩ := isSolutionPlanFix_normalForm hw hwK h
  have hlenps : ps.length = K + 1 := by simpa using hperm.length_eq
  have hlen : ass.length = K + 1 := by
    have h₁ : ps.length = ass.length := hruns.length_eq
    omega
  -- the delays are a permutation of `0, …, K`
  have hmapfst : (ps.map Prod.fst).Perm (List.range (K + 1)) := by
    have := hperm.map Prod.fst
    simpa [List.map_map, Function.comp_def] using this
  have hnodup : (ps.map Prod.fst).Nodup := hmapfst.nodup_iff.2 (List.nodup_range)
  set d : ℕ → ℕ := fun j => (ps.getD j (0, 0)).1 with hd
  have hmem : ∀ j, ∀ hj : j < K + 1, ∃ i ≤ K, ps[j]'(by omega) = (i, K - i) := by
    intro j hj
    have hmem' : ps[j]'(by omega) ∈ ps := List.getElem_mem _
    have := hperm.mem_iff.1 hmem'
    obtain ⟨i, hi, heq⟩ := List.mem_map.1 this
    exact ⟨i, Nat.lt_succ_iff.1 (List.mem_range.1 hi), heq.symm⟩
  have hdj : ∀ j, ∀ hj : j < K + 1, d j = (ps[j]'(by omega)).1 := by
    intro j hj
    have hg : ps.getD j (0, 0) = ps[j]'(by omega) :=
      List.getD_eq_getElem _ _ (show j < ps.length by omega)
    simp only [hd, hg]
  have hdle : ∀ j < K + 1, d j ≤ K := by
    intro j hj
    obtain ⟨i, hi, heq⟩ := hmem j hj
    rw [hdj j hj, heq]
    exact hi
  have hsnd : ∀ j, ∀ hj : j < K + 1, (ps[j]'(by omega)).2 = K - d j := by
    intro j hj
    obtain ⟨i, hi, heq⟩ := hmem j hj
    rw [hdj j hj, heq]
  have hdinj : ∀ j₁ < K + 1, ∀ j₂ < K + 1, d j₁ = d j₂ → j₁ = j₂ := by
    intro j₁ h₁ j₂ h₂ he
    have hlm : (ps.map Prod.fst).length = K + 1 := by simp [hlenps]
    have e₁ : (ps.map Prod.fst)[j₁]'(by omega) = d j₁ := by
      simp [List.getElem_map, hdj j₁ h₁]
    have e₂ : (ps.map Prod.fst)[j₂]'(by omega) = d j₂ := by
      simp [List.getElem_map, hdj j₂ h₂]
    exact (hnodup.getElem_inj_iff (i := j₁) (hi := by omega) (j := j₂) (hj := by omega)).1
      (by rw [e₁, e₂, he])
  -- the decisions and the tested symbols of each counter
  have hex : ∀ j : ℕ, ∃ Pc : (ℕ → List (TMAct Q Γ)) × (ℕ → Option Γ), ∀ hj : j < K + 1,
      (∀ t < K, StepDecision N w K (Pc.1 t)) ∧
        ass[j]'(by omega) = counterRun Q Γ K (d j) (K - d j) Pc.1 Pc.2 := by
    intro j
    by_cases hj : j < K + 1
    · obtain ⟨P, c, hP, hl⟩ := hruns.get (i := j) (by omega) (by omega)
      refine ⟨(P, c), fun _ => ⟨hP, ?_⟩⟩
      have := hl
      simp only [List.get_eq_getElem] at this
      rw [this, hdj j hj, hsnd j hj, hdj j hj]
    · exact ⟨(fun _ => [], fun _ => none), fun hj' => absurd hj' hj⟩
  choose Pc hPc using hex
  exact ⟨⟨sym, d, fun j => (Pc j).1, fun j => (Pc j).2, ass, ac, bs, as₁, f, hinit, hsep, hlen,
    hdle, hdinj, fun j hj => (hPc j hj).1, fun j hj => (hPc j (by omega)).2, hil, hint', hint,
    hf, h⟩, rfl⟩

end TMEnc

end HTN
