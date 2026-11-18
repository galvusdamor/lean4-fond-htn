import HtnPlanning.Core.Classes
import HtnPlanning.Core.Reachability
/-!
# The structure of reachable task networks of regular problems

The characteristic property of *regular* problems (Def. 3.3) is that a decomposition can never
increase the number of compound tasks of a task network: every method inserts at most one
compound task, in place of the one it decomposes.  Consequently, if the initial task network
contains at most one compound task, then so does every task network reachable from it — a
regular problem never needs to remember more than one open compound task, which is the
structural reason for the low complexity of the class.

The main result is `Problem.IsRegularM.reachable_subsingleton_abstract`.
-/

namespace HTN

universe u v w x

variable {I : Type x} {A : Type v} {C : Type w}

namespace TaskNetwork

/-- A task network has at most one compound task. -/
def SubsingletonAbstract (tn : TaskNetwork I A C) : Prop :=
  ∀ t ∈ tn.T, ∀ t' ∈ tn.T, tn.IsAbstractId t → tn.IsAbstractId t' → t = t'

lemma IsRegular.subsingletonAbstract {tn : TaskNetwork I A C} (h : tn.IsRegular) :
    tn.SubsingletonAbstract := h.1

/-- Being abstract is transported along an isomorphism. -/
lemma Iso.isAbstractId {tn tn' : TaskNetwork I A C} {σ : I → I}
    (hα : ∀ t ∈ tn.T, tn.α t = tn'.α (σ t)) {t : I} (ht : t ∈ tn.T) :
    tn.IsAbstractId t ↔ tn'.IsAbstractId (σ t) := by
  unfold IsAbstractId
  rw [hα t ht]

/-- Having at most one compound task is invariant under isomorphism. -/
lemma Iso.subsingletonAbstract {tn tn' : TaskNetwork I A C} (h : tn.Iso tn')
    (h' : tn'.SubsingletonAbstract) : tn.SubsingletonAbstract := by
  obtain ⟨σ, hbij, -, hα⟩ := h
  intro t ht t' ht' habs habs'
  have hσt : σ t ∈ tn'.T := by simpa using hbij.mapsTo (by simpa using ht)
  have hσt' : σ t' ∈ tn'.T := by simpa using hbij.mapsTo (by simpa using ht')
  have := h' _ hσt _ hσt' ((Iso.isAbstractId hα ht).1 habs) ((Iso.isAbstractId hα ht').1 habs')
  exact hbij.injOn (by simpa using ht) (by simpa using ht') this

end TaskNetwork

namespace Problem

variable {F : Type u} [DecidableEq I] {P : Problem F A C I}

/-- **One decomposition step of a regular problem keeps the number of compound tasks below
two.** -/
theorem IsRegularM.decompStep_subsingletonAbstract (hreg : P.IsRegularM)
    {tn₁ tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    (hstep : DecompStep P.methods tn₁ t m tn₂) (hm : P.ReachableMethod m)
    (h₁ : tn₁.SubsingletonAbstract) : tn₂.SubsingletonAbstract := by
  obtain ⟨-, htT, hαt, tn', -, hiso, hdisj, rfl⟩ := hstep
  have habs_t : tn₁.IsAbstractId t := ⟨m.abstractTask, hαt⟩
  have hsub' : tn'.SubsingletonAbstract :=
    TaskNetwork.Iso.subsingletonAbstract hiso (hreg m hm).subsingletonAbstract
  -- an old task id that survives the decomposition is primitive
  have hold : ∀ x ∈ tn₁.T, x ≠ t → ¬ tn₁.IsAbstractId x := by
    intro x hx hxt habs
    exact hxt (h₁ x hx t htT habs habs_t)
  intro x hx y hy habsx habsy
  have hcase : ∀ z ∈ (decomposeWith tn₁ t tn').T,
      (decomposeWith tn₁ t tn').IsAbstractId z → z ∈ tn'.T := by
    intro z hz habsz
    by_cases hz' : z ∈ tn'.T
    · exact hz'
    · exfalso
      rcases mem_decomposeWith_T.1 hz with ⟨hz₁, hzt⟩ | hz''
      · refine hold z hz₁ hzt ?_
        obtain ⟨c, hc⟩ := habsz
        exact ⟨c, by simpa [hz'] using hc⟩
      · exact hz' hz''
  have hxT' : x ∈ tn'.T := hcase x hx habsx
  have hyT' : y ∈ tn'.T := hcase y hy habsy
  refine hsub' x hxT' y hyT' ?_ ?_
  · obtain ⟨c, hc⟩ := habsx
    exact ⟨c, by simpa [hxT'] using hc⟩
  · obtain ⟨c, hc⟩ := habsy
    exact ⟨c, by simpa [hyT'] using hc⟩

/-- **Regular problems never need more than one open compound task.**  If the initial task
network of a regular problem contains at most one compound task, then so does every task
network reachable from it by decomposition. -/
theorem IsRegularM.reachable_subsingleton_abstract (hreg : P.IsRegularM)
    (htnI : P.tnI.SubsingletonAbstract) {tn : TaskNetwork I A C} (h : P.Reachable tn) :
    tn.SubsingletonAbstract := by
  induction h with
  | refl => exact htnI
  | tail hprefix hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact hreg.decompStep_subsingletonAbstract hs
      (reachableMethod_of_decomposesTo hprefix hs) ih

/-- In particular, every solution of a regular problem is reached through task networks with at
most one compound task; the initial task network of the paper's presentation (a single initial
compound task `t_I`) satisfies the hypothesis. -/
theorem IsRegularM.reachable_subsingleton_abstract_of_singleton (hreg : P.IsRegularM)
    {t₀ : I} (htnI : P.tnI.T = {t₀}) {tn : TaskNetwork I A C} (h : P.Reachable tn) :
    tn.SubsingletonAbstract := by
  refine hreg.reachable_subsingleton_abstract ?_ h
  intro x hx y hy _ _
  rw [htnI] at hx hy
  simp only [Finset.mem_singleton] at hx hy
  rw [hx, hy]

end Problem

end HTN
