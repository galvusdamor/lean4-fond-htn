import HtnPlanning.Core.Problem
import HtnPlanning.Basic
/-!
# Reachable compound task names and reachable methods

The problem classes of Section 3 of

  P. Bercher, G. Behnke, D. Höller, T. Geier, R. Alford,
  *Propositional Hierarchical Task Network Planning: Problem Classes and Complexity Results*

are not defined in terms of *all* methods of the domain, but only in terms of those methods
that are *reachable from the initial task network* ("this allows for avoiding the worst case
in many cases").  This file defines the standard top-down reachability analysis:

* `Problem.ReachableName P c` — the compound task name `c` occurs in the initial task network,
  or in the subtask network of a reachable method;
* `Problem.ReachableMethod P m` — `m` is a method of `P` whose decomposed task name is
  reachable.

The main result (`Problem.reachableName_of_decomposesTo`) is that this over-approximates the
truth: every compound task name occurring in a task network obtained from `tn_I` by
decomposition is reachable in the above sense, and every method used in such a decomposition
is a reachable method (`Problem.reachableMethod_of_decompStep`).
-/

namespace HTN

namespace Problem

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- All compound task names occurring in a task network are reachable. -/
def NamesReachable (P : Problem F A C I) (tn : TaskNetwork I A C) : Prop :=
  ∀ t ∈ tn.T, ∀ c : C, tn.α t = Sum.inr c → P.ReachableName c

lemma namesReachable_tnI (P : Problem F A C I) : P.NamesReachable P.tnI :=
  fun _ ht _ hc => ReachableName.tnI ht hc

variable [DecidableEq I]

/-- A single decomposition step applied to a task network all of whose compound task names are
reachable uses a reachable method. -/
lemma reachableMethod_of_decompStep {P : Problem F A C I} {tn₁ tn₂ : TaskNetwork I A C} {t : I}
    {m : Method I A C} (h : DecompStep P.methods tn₁ t m tn₂) (hn : P.NamesReachable tn₁) :
    P.ReachableMethod m :=
  ⟨h.1, hn t h.2.1 _ h.2.2.1⟩

/-- A single decomposition step preserves the property that all compound task names of the
network are reachable. -/
lemma namesReachable_of_decompStep {P : Problem F A C I} {tn₁ tn₂ : TaskNetwork I A C} {t : I}
    {m : Method I A C} (h : DecompStep P.methods tn₁ t m tn₂) (hn : P.NamesReachable tn₁) :
    P.NamesReachable tn₂ := by
  obtain ⟨hm, htT, hαt, tn', -, ⟨σ, hbij, -, hα⟩, -, rfl⟩ := h
  intro x hx c hc
  by_cases hx' : x ∈ tn'.T
  · -- the label comes from the (fresh copy of the) method's subtask network
    have hxσ : σ x ∈ m.subtasks.T := by simpa using hbij.mapsTo (by simpa using hx')
    have : m.subtasks.α (σ x) = Sum.inr c := by
      rw [← hα x hx']
      simpa [hx'] using hc
    exact ReachableName.method hm (hn t htT _ hαt) hxσ this
  · have hx₁ : x ∈ tn₁.T := by
      rcases mem_decomposeWith_T.1 hx with ⟨h, -⟩ | h
      · exact h
      · exact absurd h hx'
    exact hn x hx₁ c (by simpa [hx'] using hc)

/-- **Soundness of the reachability analysis (task names).** Every compound task name occurring
in a task network reachable from `tn_I` by decomposition is reachable in the sense of
`Problem.ReachableName`. -/
theorem namesReachable_of_decomposesTo {P : Problem F A C I} {tn : TaskNetwork I A C}
    (h : P.DecomposesTo P.tnI tn) : P.NamesReachable tn := by
  induction h with
  | refl => exact P.namesReachable_tnI
  | tail _ hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact namesReachable_of_decompStep hs ih

theorem reachableName_of_decomposesTo {P : Problem F A C I} {tn : TaskNetwork I A C}
    (h : P.DecomposesTo P.tnI tn) {t : I} (ht : t ∈ tn.T) {c : C} (hc : tn.α t = Sum.inr c) :
    P.ReachableName c :=
  namesReachable_of_decomposesTo h t ht c hc

/-- **Soundness of the reachability analysis (methods).** Every method used in a decomposition
starting from `tn_I` is a reachable method. -/
theorem reachableMethod_of_decomposesTo {P : Problem F A C I} {tn₁ tn₂ : TaskNetwork I A C}
    {t : I} {m : Method I A C} (h : P.DecomposesTo P.tnI tn₁)
    (hstep : DecompStep P.methods tn₁ t m tn₂) : P.ReachableMethod m :=
  reachableMethod_of_decompStep hstep (namesReachable_of_decomposesTo h)

end Problem

end HTN
