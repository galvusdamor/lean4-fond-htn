import HtnPlanning.Core.Classes
/-!
# The hierarchy of HTN problem classes

This file proves the inclusions between the problem classes of Section 3 of Bercher et al.
(see `HtnPlanning/Core/Classes.lean`), i.e. Fig. 3.0.1 of that paper and the syntactic
expressiveness hierarchy of the compilability project:

```
                                          HTN
                                       /   |   \
                              HTN-NOOP  TO-HTN HTN-TR
                                 |    /    |    /    \
                          TO-HTN-NOOP   TO-HTN-TR    HTN-REG   HTN-AC
                                           |       \/          /
                                        TO-HTN-REG  TO-HTN-AC
```

The main results are

* `Problem.IsAcyclic.isMostlyAcyclic` : `ACYC ⊆ MOSTLY-ACYC`,
* `Problem.IsMostlyAcyclic.isTailRecursive` : `MOSTLY-ACYC ⊆ TAIL-REC`,
* `Problem.isRegularM_iff_isTailRecursive1` : **Theorem 3.0.1**, a planning problem all of whose
  reachable methods are regular (`REG-M`, the paper's generalised notion; `REG` additionally asks
  for a regular initial task network) iff it is `≤_r`-stratifiable with a stratification of
  height one,
* `Problem.IsRegular.isTailRecursive` : `REG ⊆ TAIL-REC`,
* `Problem.IsNoHTN.isRegular` etc.: `noHTN` is contained in all the classes,

together with the corresponding inclusions of the named classes in the namespace
`HTN.Classes`.
-/

namespace HTN

namespace TaskNetwork

/-- A task network with a single task is regular. -/
theorem isRegular_of_T_eq_singleton {I : Type*} {A : Type*} {C : Type*} {tn : TaskNetwork I A C}
    {t : I} (hT : tn.T = {t}) : tn.IsRegular := by
  refine ⟨fun x hx y hy _ _ => ?_, fun x hx _ y hy hyx => ?_⟩
  · rw [hT] at hx hy
    simp only [Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm
  · rw [hT] at hx hy
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hy.trans hx.symm) hyx

end TaskNetwork

namespace Problem

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### Problems without hierarchy -/

/-- A problem whose initial task network is primitive has no reachable compound task name. -/
theorem IsNoHTN.hasHeightZero {P : Problem F A C I} (h : P.IsNoHTN) : P.HasHeightZero := by
  intro c hc
  induction hc with
  | tnI ht hα =>
    obtain ⟨a, ha⟩ := h _ ht
    exact absurd (ha ▸ hα) (by simp)
  | method _ _ _ _ ih => exact ih

/-- A problem whose initial task network is primitive has no reachable method. -/
theorem IsNoHTN.not_reachableMethod {P : Problem F A C I} (h : P.IsNoHTN)
    {m : Method I A C} : ¬ P.ReachableMethod m :=
  fun hm => h.hasHeightZero _ hm.2

theorem IsNoHTN.isRegularM {P : Problem F A C I} (h : P.IsNoHTN) : P.IsRegularM :=
  fun _ hm => absurd hm h.not_reachableMethod

theorem IsNoHTN.isRegular {P : Problem F A C I} (h : P.IsNoHTN) : P.IsRegular := by
  refine ⟨⟨fun t ht _ _ habs _ => ?_, fun t ht habs _ _ _ => ?_⟩, h.isRegularM⟩ <;>
  · obtain ⟨a, ha⟩ := h _ ht
    obtain ⟨c, hc⟩ := habs
    exact absurd (ha ▸ hc) (by simp)

theorem IsNoHTN.isTO_M {P : Problem F A C I} (h : P.IsNoHTN) : P.IsTO_M :=
  fun _ hm => absurd hm h.not_reachableMethod

/-- A problem without hierarchy is acyclic (with the empty stratification). -/
theorem IsNoHTN.isAcyclic {P : Problem F A C I} (h : P.IsNoHTN) : P.IsAcyclic := by
  refine ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ => Or.inl trivial⟩, ?_, ?_⟩⟩
  · intro c₁ _ hc₁ _ _ _
    exact absurd hc₁ (h.hasHeightZero c₁)
  · intro m hm
    exact absurd hm h.not_reachableMethod

/-! ### `ACYC ⊆ MOSTLY-ACYC ⊆ TAIL-REC ⊆ UNRES-REC` -/

/-- **`ACYC ⊆ MOSTLY-ACYC`**: every `≤₀`-stratification is a `≤₁`-stratification. -/
theorem IsStrat0.isStrat1 {P : Problem F A C I} {le : C → C → Prop} (h : P.IsStrat0 le) :
    P.IsStrat1 le where
  strat := h.strat
  big := fun m hm _ t ht c hc => h.decreasing m hm t ht c hc
  small := fun m hm _ t ht c hc => (h.decreasing m hm t ht c hc).1

theorem IsAcyclic.isMostlyAcyclic {P : Problem F A C I} (h : P.IsAcyclic) :
    P.IsMostlyAcyclic := by
  obtain ⟨le, hle⟩ := h
  exact ⟨le, hle.isStrat1⟩

/-- **`MOSTLY-ACYC ⊆ TAIL-REC`**: every `≤₁`-stratification is a `≤_r`-stratification. -/
theorem IsStrat1.isStratR {P : Problem F A C I} {le : C → C → Prop} (h : P.IsStrat1 le) :
    P.IsStratR le where
  strat := h.strat
  last := by
    intro m hm t ht _ c hc
    rcases lt_or_ge 1 m.subtasks.T.card with hcard | hcard
    · exact (h.big m hm hcard t ht c hc).1
    · have hpos : 0 < m.subtasks.T.card := Finset.card_pos.2 ⟨t, ht⟩
      have : m.subtasks.T.card = 1 := le_antisymm hcard hpos
      exact h.small m hm this t ht c hc
  nonlast := by
    intro m hm t ht hnl c hc
    rcases lt_or_ge 1 m.subtasks.T.card with hcard | hcard
    · exact h.big m hm hcard t ht c hc
    · -- a network with a single task id: that task id is trivially a last task id
      have hpos : 0 < m.subtasks.T.card := Finset.card_pos.2 ⟨t, ht⟩
      have hcard1 : m.subtasks.T.card = 1 := le_antisymm hcard hpos
      have hsingle : m.subtasks.T = {t} := by
        obtain ⟨s, hs⟩ := Finset.card_eq_one.1 hcard1
        rw [hs] at ht ⊢
        simpa using (Finset.mem_singleton.1 ht) ▸ rfl
      exact absurd ⟨ht, fun t' ht' hne => absurd (by simpa [hsingle] using ht') hne⟩ hnl

theorem IsMostlyAcyclic.isTailRecursive {P : Problem F A C I} (h : P.IsMostlyAcyclic) :
    P.IsTailRecursive := by
  obtain ⟨le, hle⟩ := h
  exact ⟨le, hle.isStratR⟩

theorem IsTailRecursive.isUnrestricted {P : Problem F A C I} (_h : P.IsTailRecursive) :
    P.IsUnrestricted := trivial

/-! ### Theorem 3.0.1: regularity equals tail recursion of height one -/

/-- Under a `≤_r`-stratification of height one, no reachable method has a compound non-last
task. -/
theorem isLastId_of_stratR_heightOne {P : Problem F A C I} {le : C → C → Prop}
    (hR : P.IsStratR le) (hh : P.HasHeightOne le) {m : Method I A C} (hm : P.ReachableMethod m)
    {t : I} (ht : t ∈ m.subtasks.T) (habs : m.subtasks.IsAbstractId t) :
    m.subtasks.IsLastId t := by
  by_contra hnl
  obtain ⟨c, hc⟩ := habs
  have hcreach : P.ReachableName c := ReachableName.method hm.1 hm.2 ht hc
  exact (hR.nonlast m hm t ht hnl c hc).2 (hh _ _ hm.2 hcreach)

/-- **Theorem 3.0.1 (⇒).** Every regular planning problem is `≤_r`-stratifiable with a
stratification of height one. -/
theorem IsRegularM.isTailRecursive1 {P : Problem F A C I} (h : P.IsRegularM) :
    P.IsTailRecursive1 := by
  refine ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ => Or.inl trivial⟩, fun _ _ _ _ _ _ _ => trivial, ?_⟩, fun _ _ _ _ => trivial⟩
  intro m hm t ht hnl c hc
  exact absurd ((h m hm).isLastId ht ⟨c, hc⟩) hnl

/-- **Theorem 3.0.1 (⇐).** Every `≤_r`-stratifiable planning problem whose stratification has
height one is regular.  (Well-formedness of the methods is needed to exclude a task network
with two compound tasks each of which is ordered after the other.) -/
theorem IsTailRecursive1.isRegularM {P : Problem F A C I} (hwf : P.WF)
    (h : P.IsTailRecursive1) : P.IsRegularM := by
  obtain ⟨le, hR, hh⟩ := h
  intro m hm
  have hlast : ∀ t ∈ m.subtasks.T, m.subtasks.IsAbstractId t → m.subtasks.IsLastId t :=
    fun t ht habs => isLastId_of_stratR_heightOne hR hh hm ht habs
  refine ⟨?_, fun t ht habs t' ht' hne => (hlast t ht habs).2 t' ht' hne⟩
  intro t ht t' ht' habs habs'
  by_contra hne
  have h₁ := (hlast t ht habs).2 t' ht' (Ne.symm hne)
  have h₂ := (hlast t' ht' habs').2 t ht hne
  exact (hwf.methods m hm.1).asymm h₁ h₂

/-- **Theorem 3.0.1.** A well-formed planning problem is regular iff it is `≤_r`-stratifiable
with a stratification of height one, i.e. `REG = TAIL-REC₁`. -/
theorem isRegularM_iff_isTailRecursive1 {P : Problem F A C I} (hwf : P.WF) :
    P.IsRegularM ↔ P.IsTailRecursive1 :=
  ⟨IsRegularM.isTailRecursive1, IsTailRecursive1.isRegularM hwf⟩

/-- **`REG-M ⊆ TAIL-REC`.** -/
theorem IsRegularM.isTailRecursive {P : Problem F A C I} (h : P.IsRegularM) :
    P.IsTailRecursive := by
  obtain ⟨le, hR, -⟩ := h.isTailRecursive1
  exact ⟨le, hR⟩

/-- **`REG ⊆ TAIL-REC`.** -/
theorem IsRegular.isTailRecursive {P : Problem F A C I} (h : P.IsRegular) :
    P.IsTailRecursive := h.2.isTailRecursive

/-- **`ACYC ⊆ TAIL-REC`.** -/
theorem IsAcyclic.isTailRecursive {P : Problem F A C I} (h : P.IsAcyclic) :
    P.IsTailRecursive := h.isMostlyAcyclic.isTailRecursive

end Problem

/-! ### The inclusions between the named classes -/

namespace Classes

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

theorem subset_HTN (S : Set (Problem F A C I)) : S ⊆ HTN F A C I := fun _ _ => trivial

theorem TO_HTN_subset_HTN : TO_HTN F A C I ⊆ HTN F A C I := subset_HTN _

theorem HTN_NOOP_subset_HTN : HTN_NOOP F A C I ⊆ HTN F A C I := subset_HTN _

theorem HTN_TR_subset_HTN : HTN_TR F A C I ⊆ HTN F A C I := subset_HTN _

theorem TO_HTN_NOOP_subset_TO_HTN : TO_HTN_NOOP F A C I ⊆ TO_HTN F A C I := Set.inter_subset_left

theorem TO_HTN_NOOP_subset_HTN_NOOP : TO_HTN_NOOP F A C I ⊆ HTN_NOOP F A C I :=
  Set.inter_subset_right

theorem TO_HTN_TR_subset_TO_HTN : TO_HTN_TR F A C I ⊆ TO_HTN F A C I := Set.inter_subset_left

theorem TO_HTN_TR_subset_HTN_TR : TO_HTN_TR F A C I ⊆ HTN_TR F A C I := Set.inter_subset_right

theorem HTN_REG_subset_HTN_TR : HTN_REG F A C I ⊆ HTN_TR F A C I :=
  fun _ h => Problem.IsRegular.isTailRecursive h

theorem HTN_AC_subset_MOSTLY_ACYC : HTN_AC F A C I ⊆ MOSTLY_ACYC F A C I :=
  fun _ h => Problem.IsAcyclic.isMostlyAcyclic h

theorem MOSTLY_ACYC_subset_HTN_TR : MOSTLY_ACYC F A C I ⊆ HTN_TR F A C I :=
  fun _ h => Problem.IsMostlyAcyclic.isTailRecursive h

theorem HTN_AC_subset_HTN_TR : HTN_AC F A C I ⊆ HTN_TR F A C I :=
  HTN_AC_subset_MOSTLY_ACYC.trans MOSTLY_ACYC_subset_HTN_TR

theorem TO_HTN_REG_subset_TO_HTN_TR : TO_HTN_REG F A C I ⊆ TO_HTN_TR F A C I :=
  Set.inter_subset_inter_right _ HTN_REG_subset_HTN_TR

theorem TO_HTN_REG_subset_HTN_REG : TO_HTN_REG F A C I ⊆ HTN_REG F A C I := Set.inter_subset_right

theorem TO_HTN_AC_subset_TO_HTN_TR : TO_HTN_AC F A C I ⊆ TO_HTN_TR F A C I :=
  Set.inter_subset_inter_right _ HTN_AC_subset_HTN_TR

theorem TO_HTN_AC_subset_HTN_AC : TO_HTN_AC F A C I ⊆ HTN_AC F A C I := Set.inter_subset_right

/-- Problems without hierarchy are regular, acyclic and (if their initial task network is
totally ordered) totally ordered. -/
theorem noHTN_subset_HTN_REG : noHTN F A C I ⊆ HTN_REG F A C I :=
  fun _ h => Problem.IsNoHTN.isRegular h

theorem noHTN_subset_HTN_AC : noHTN F A C I ⊆ HTN_AC F A C I :=
  fun _ h => Problem.IsNoHTN.isAcyclic h

end Classes

end HTN
