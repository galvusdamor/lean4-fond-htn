import HtnComplexity.Regular.RegularToStrips
import HtnPlanning.Core.DerivationLength
/-!
# The compilation of regular HTN problems into STRIPS is plan-length bounded

The compilation of `HtnComplexity/Regular/RegularToStrips.lean` uses one action of the compiled
problem per method application of a derivation, so a priori the length of the compiled plan is
bounded by the *number of methods* of the derivation, not by the length of the original plan —
a derivation may apply arbitrarily many methods with an empty body.

Combining the compilation with the cut-elimination bound of
`HtnPlanning/Core/DerivationLength.lean` closes this gap:

* `HTN.Regular.exists_plan_of_derivesN` — a derivation using `n` methods yields a plan of the
  compiled problem of length exactly `n`;
* `HTN.Regular.exists_solution_length_le` — **if a regular totally ordered HTN problem has a
  solution plan `as`, then the compiled classical problem has a solution of length at most
  `(|as| + 1) · (|C| + 1)`**, where `|C|` is the number of compound task names;
* `HTN.Regular.exists_toStrips_solutionPlan_length_le` — the same statement for the compiled
  problem viewed as a member of the syntactic class `STRIPS` of HTN problems.

So the compilation is plan-length preserving up to a factor that is linear in the size of the
compiled domain, which is the sense in which the source calls it *linear*.
-/

namespace HTN

namespace Regular

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]
variable {D : Domain F A C I} {Q : Instance F A C I}

/-- **A derivation using `n` methods yields a plan of the compiled problem of length `n`.**
This is `HTN.Regular.exists_plan_of_derives` with the plan length recorded. -/
lemma exists_plan_of_derivesN {n : ℕ} {c : C} {as : List A}
    (hd : (D.mkProblem Q).DerivesN n c as) :
    ∀ s : Set F, D.SeqApplicable as s →
      ∃ mplan : List (Method I A C), mplan.length = n ∧
        (macroModel D).SeqApplicable mplan (encP s c) ∧
        (macroModel D).transitionSeq mplan (encP s c) = encD (D.transitionSeq as s) := by
  induction hd with
  | @last c os m hm hc hb =>
      intro s happ
      have husable : Usable D m :=
        ⟨hm, ⟨(os, none), hb⟩, by
          rw [body_eq hb]
          exact ((D.seqApplicable_iff os s).1 happ).1⟩
      have happ' : (macroModel D).Applicable m (encP s c) :=
        (applicable_iff hb husable).2 ⟨hc, happ⟩
      subst hc
      exact ⟨[m], rfl, ⟨happ', trivial⟩, by simpa using transition_eq_none (D := D) hb⟩
  | @cons n c c' os rest m hm hc hb h ih =>
      intro s happ
      rw [D.seqApplicable_append] at happ
      obtain ⟨happ1, happ2⟩ := happ
      obtain ⟨mplan, hlen, hmapp, hmtr⟩ := ih (D.transitionSeq os s) happ2
      have husable : Usable D m :=
        ⟨hm, ⟨(os, some c'), hb⟩, by
          rw [body_eq hb]
          exact ((D.seqApplicable_iff os s).1 happ1).1⟩
      subst hc
      refine ⟨m :: mplan, by simp [hlen], ⟨(applicable_iff hb husable).2 ⟨rfl, happ1⟩, ?_⟩, ?_⟩
      · rw [transition_eq_some hb]
        exact hmapp
      · rw [ActionModel.transitionSeq_cons, transition_eq_some hb, hmtr,
          D.transitionSeq_append]

/-- **The compiled classical problem has a short solution.**  If the regular, totally ordered
HTN problem has a solution plan `as`, then the compiled classical problem has a solution of
length at most `(|as| + 1) · (|C| + 1)`. -/
theorem exists_solution_length_le [Fintype C] [Infinite I]
    (hwf : (D.mkProblem Q).WF) (hreg : (D.mkProblem Q).IsRegularM)
    (hto : (D.mkProblem Q).IsTO_M) {t₀ : I} {c₀ : C} (hT : Q.tnI.T = {t₀})
    (hα : Q.tnI.α t₀ = Sum.inr c₀) {as : List A}
    (hsol : (D.mkProblem Q).IsSolutionPlan as) :
    ∃ mplan : List (Method I A C), (toClassical D Q).IsSolution mplan ∧
      mplan.length ≤ (as.length + 1) * (Fintype.card C + 1) := by
  classical
  have hd : (D.mkProblem Q).Derives c₀ as :=
    Problem.derives_of_isSolutionPlan hwf hreg hto hT hα hsol
  obtain ⟨-, -, -, -, -, -, happ, hgoal⟩ := hsol
  obtain ⟨n, hn, hdn⟩ := Problem.exists_derivesN_le hd
  obtain ⟨mplan, hlen, hmapp, hmtr⟩ := exists_plan_of_derivesN hdn Q.init happ
  have hinit : (toClassical D Q).init = encP Q.init c₀ := toClassical_init hT hα
  refine ⟨mplan, ⟨?_, ?_⟩, by omega⟩
  · rw [hinit]; exact hmapp
  · rw [hinit]
    show RegFact.state '' Q.goal ∪ {RegFact.done} ⊆
      (macroModel D).transitionSeq mplan (encP Q.init c₀)
    rw [hmtr]
    rintro f (hf | hf)
    · obtain ⟨v, hv, rfl⟩ := hf
      exact state_mem_encD.2 (hgoal hv)
    · simp only [Set.mem_singleton_iff] at hf
      subst hf
      exact done_mem_encD

/-- **The compiled STRIPS problem has a short solution plan.**  The HTN version of
`HTN.Regular.exists_solution_length_le`, for the compiled problem as a member of the class
`STRIPS`. -/
theorem exists_toStrips_solutionPlan_length_le [Fintype C] [Infinite I]
    (hwf : (D.mkProblem Q).WF) (hreg : (D.mkProblem Q).IsRegularM)
    (hto : (D.mkProblem Q).IsTO_M) {t₀ : I} {c₀ : C} (hT : Q.tnI.T = {t₀})
    (hα : Q.tnI.α t₀ = Sum.inr c₀) {as : List A}
    (hsol : (D.mkProblem Q).IsSolutionPlan as) :
    ∃ mplan : List (Method I A C),
      ((domTrans D).mkProblem (instTrans Q)).IsSolutionPlan mplan ∧
      mplan.length ≤ (as.length + 1) * (Fintype.card C + 1) := by
  obtain ⟨mplan, hplan, hlen⟩ :=
    exists_solution_length_le hwf hreg hto hT hα hsol
  refine ⟨mplan, ?_, hlen⟩
  rw [domTrans_mkProblem]
  exact Strips.toHTN_isSolutionPlan _ hplan

end Regular

end HTN
