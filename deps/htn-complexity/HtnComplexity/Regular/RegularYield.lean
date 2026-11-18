import HtnComplexity.Regular.RegularWeakNormalForm
import HtnPlanning.Interleave.NetYield
/-!
# Refinements of a single compound task in a regular problem are its derivations

`HtnComplexity/Regular/RegularWeakNormalForm.lean` proves the normal form theorem for a *rooted*
regular problem at the level of **solvability**: the problem is solvable exactly when one of the
derivations of its initial compound task is executable and reaches the goal.

For a compilation that has to compare two problems refinement by refinement — rather than only
"solvable or not" — the plan-level statement is needed:

* `HTN.Problem.netYield_iff_derivesW` — for a well-formed regular problem whose initial task
  network is the single compound task `c₀`, the refinements of the initial task network are
  exactly the derivations of `c₀`.

Both halves are already in `RegularWeakNormalForm.lean`; this file only drops the executability
and goal conditions from them.  Since `HTN.Problem.DerivesW` depends on the problem only through
its set of methods, `HTN.Problem.derivesW_congr` transports it between problems over the same
domain.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable [DecidableEq I] {P P' : Problem F A C I}

omit [DecidableEq I] in
/-- Derivations depend on the problem only through its methods. -/
theorem derivesW_congr (h : P.methods = P'.methods) {c : C} {as : List A} :
    P.DerivesW c as ↔ P'.DerivesW c as := by
  constructor
  · intro hd
    induction hd with
    | last hm hc hb => exact DerivesW.last (h ▸ hm) hc hb
    | cons hm hc hb _ ih => exact DerivesW.cons (h ▸ hm) hc hb ih
  · intro hd
    induction hd with
    | last hm hc hb => exact DerivesW.last (h ▸ hm) hc hb
    | cons hm hc hb _ ih => exact DerivesW.cons (h ▸ hm) hc hb ih

/-- **Every refinement of the initial compound task is a derivation.** -/
theorem derivesW_of_netYield (hwf : P.WF) (hreg : P.IsRegularM) {t₀ : I} {c₀ : C}
    (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀) {as : List A}
    (h : P.domain.NetYield P.tnI as) : P.DerivesW c₀ as := by
  obtain ⟨tn, hreach, hprim, l, hlin, hseq⟩ := Domain.netYield_iff.1 h
  obtain ⟨tail, hchain, hcont⟩ :=
    exists_weakChain_contDerivesW hwf hreg hT hα (show P.Reachable tn from hreach)
  have htail : tail = none := by
    cases htail : tail with
    | none => rfl
    | some p =>
        exfalso
        obtain ⟨a, ha⟩ := hprim p.1 (hchain.tailMem p htail)
        have := hchain.tailLabel p htail
        rw [ha] at this
        exact absurd this (by simp)
  subst htail
  exact hcont as ⟨l, by simpa using hlin, hseq, by rintro p ⟨⟩⟩

/-- **Every derivation of the initial compound task is a refinement.** -/
theorem netYield_of_derivesW [Infinite I] (hwf : P.WF) {t₀ : I} {c₀ : C}
    (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀) {as : List A}
    (h : P.DerivesW c₀ as) : P.domain.NetYield P.tnI as := by
  obtain ⟨tn₂, hreach₂, hy₂⟩ :=
    exists_yields_none_of_derivesW hwf h (isWeakChain_tnI hwf.tnI hT hα)
      (yields_tnI hT hα) Relation.ReflTransGen.refl
  rw [List.nil_append] at hy₂
  obtain ⟨l, hlin, hseq, -⟩ := hy₂
  exact Domain.netYield_iff.2
    ⟨tn₂, hreach₂, TaskNetwork.Yields.isPrimitive ⟨l, hlin, hseq, by rintro p ⟨⟩⟩,
      l, by simpa using hlin, hseq⟩

/-- **Derivations of a chain of compound tasks**: the concatenations of derivations of its
entries, in order. -/
def DerivesChainW (P : Problem F A C I) : List C → List A → Prop
  | [], as => as = []
  | c :: ws, as => ∃ as₁ as₂, as = as₁ ++ as₂ ∧ P.DerivesW c as₁ ∧ P.DerivesChainW ws as₂

omit [DecidableEq I] in
@[simp] theorem derivesChainW_nil {as : List A} : P.DerivesChainW [] as ↔ as = [] := Iff.rfl

omit [DecidableEq I] in
theorem derivesChainW_cons {c : C} {ws : List C} {as : List A} :
    P.DerivesChainW (c :: ws) as ↔
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ P.DerivesW c as₁ ∧ P.DerivesChainW ws as₂ := Iff.rfl

/-- **The refinements of a single compound task are its derivations.** -/
theorem netYield_iff_derivesW [Infinite I] (hwf : P.WF) (hreg : P.IsRegularM) {t₀ : I} {c₀ : C}
    (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀) {as : List A} :
    P.domain.NetYield P.tnI as ↔ P.DerivesW c₀ as :=
  ⟨derivesW_of_netYield hwf hreg hT hα, netYield_of_derivesW hwf hT hα⟩

end Problem

end HTN
