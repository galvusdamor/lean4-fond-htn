import HtnPlanning.Classes.UOHD
/-!
# Two-hole-digging problems (`2-HD-HTN`)

This file adds the class of **two-hole-digging problems** (`2-HD-HTN`) to the classes of
`HtnPlanning/Classes/Basic.lean` and `HtnPlanning/Classes/UOHD.lean`, following

    M. Dekker, G. Behnke, *Barely Decidable Fragments of Planning* (Sect. 6, the class `H₂`),

where the initial task network contains (at most) two compound tasks, but the subtask network of
every method contains at most one (`HTN.Problem.IsHD2`).  Plan existence for `H₂` is
undecidable (Höller, Lin, Erol, Bercher, *From PCP to HTN planning through CFGs*, IPC 2023), in
contrast to `1-HD-HTN` (`H₁`), which is `ACKERMANN`-complete.  As for `1-HD-HTN`, the
condition on methods is imposed only on the methods *reachable* from the initial task network.

The *rooted* variant `2-HD-HTN-1` (a single initial compound task) is a condition on instance
descriptions; it lives in `HtnComplexity/SynClasses/HD2.lean`.  With a single initial compound
task the two classes coincide: a rooted two-hole-digging problem is one-hole-digging.

Besides the definitions this file proves

* the network-level facts `TaskNetwork.IsOneHole.isTwoHole` and `TaskNetwork.isTwoHole_iff`
  (the definition is the counting condition `|α⁻¹[C]| ≤ 2`);
* the inclusions `1-HD-HTN ⊆ 2-HD-HTN` (and hence `HTN-REG ⊆ 2-HD-HTN`, `STRIPS ⊆ 2-HD-HTN`);
* the invariant of decomposition that motivates the class:
  `HTN.Problem.IsHD2.reachable_isTwoHole` (in a two-hole-digging problem *every* reachable task
  network has at most two compound tasks, so a decomposition is an interleaving of two
  sequences of methods, one for each initial compound task).
-/

namespace HTN

universe u v w x

/-! ### The restriction on single task networks -/

namespace TaskNetwork

variable {I : Type x} {A : Type v} {C : Type w}

/-- A task network is **two-hole** iff it contains at most two compound tasks (the condition
`|α⁻¹[C]| ≤ 2`): every finite set of its compound tasks has at most two elements. -/
def IsTwoHole (tn : TaskNetwork I A C) : Prop :=
  ∀ s ⊆ tn.T, (∀ t ∈ s, tn.IsAbstractId t) → s.card ≤ 2

/-- **A one-hole network is two-hole.** -/
theorem IsOneHole.isTwoHole {tn : TaskNetwork I A C} (h : tn.IsOneHole) : tn.IsTwoHole :=
  fun s hs habs => (Finset.card_le_one.2 fun x hx y hy =>
    h x (hs hx) y (hs hy) (habs x hx) (habs y hy)).trans (by norm_num)

/-- `IsTwoHole` is the condition `|α⁻¹[C]| ≤ 2` of Dekker and Behnke: the compound tasks of the
network number at most two. -/
theorem isTwoHole_iff {tn : TaskNetwork I A C} [DecidablePred tn.IsAbstractId] :
    tn.IsTwoHole ↔ (tn.T.filter tn.IsAbstractId).card ≤ 2 :=
  ⟨fun h => h _ (Finset.filter_subset _ _) fun _ ht => (Finset.mem_filter.1 ht).2,
    fun h _ hs habs => (Finset.card_le_card fun x hx =>
      Finset.mem_filter.2 ⟨hs hx, habs x hx⟩).trans h⟩

end TaskNetwork

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### The restriction on problems -/

/-- **`2-HD` (two-hole-digging problems, Dekker and Behnke, Sect. 6)**: the initial task network
contains at most two compound tasks, and the subtask network of every reachable method at most
one. -/
def IsHD2 (P : Problem F A C I) : Prop :=
  P.tnI.IsTwoHole ∧ ∀ m : Method I A C, P.ReachableMethod m → m.subtasks.IsOneHole

/-! ### Elementary relations -/

/-- **A one-hole-digging problem is two-hole-digging.** -/
theorem IsHD1.isHD2 {P : Problem F A C I} (h : P.IsHD1) : P.IsHD2 :=
  ⟨h.1.isTwoHole, h.2⟩

/-- **A regular problem is two-hole-digging.** -/
theorem IsRegular.isHD2 {P : Problem F A C I} (h : P.IsRegular) : P.IsHD2 :=
  h.isHD1.isHD2

/-- **A two-hole-digging problem with a one-hole initial task network is one-hole-digging.** -/
theorem IsHD2.isHD1 {P : Problem F A C I} (h : P.IsHD2) (h₁ : P.tnI.IsOneHole) : P.IsHD1 :=
  ⟨h₁, h.2⟩

/-! ### The invariant of decomposition -/

section Invariant

variable [DecidableEq I]

/-- One decomposition step with a one-hole method, applied to a two-hole network, yields a
two-hole network: the decomposed task was one of the at most two compound tasks, and it is
replaced by at most one. -/
theorem decompStep_isTwoHole {M : Set (Method I A C)} {tn₁ tn₂ : TaskNetwork I A C} {t : I}
    {m : Method I A C} (hstep : DecompStep M tn₁ t m tn₂) (h₁ : tn₁.IsTwoHole)
    (hm : m.subtasks.IsOneHole) : tn₂.IsTwoHole := by
  classical
  obtain ⟨-, htT, hαt, tn', -, ⟨σ, hbij, -, hα⟩, -, rfl⟩ := hstep
  intro s hs habs
  -- split `s` into the tasks of the inserted copy and the remaining tasks of `tn₁`
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (· ∈ tn'.T)
  -- the inserted copy contributes at most one compound task
  have hnew : (s.filter (· ∈ tn'.T)).card ≤ 1 := by
    have key : ∀ x ∈ s.filter (· ∈ tn'.T), x ∈ tn'.T ∧ m.subtasks.IsAbstractId (σ x) := by
      intro x hx
      obtain ⟨hxs, hxu⟩ := Finset.mem_filter.1 hx
      obtain ⟨c, hc⟩ := habs x hxs
      rw [decomposeWith_α, if_pos hxu] at hc
      exact ⟨hxu, c, (hα x hxu) ▸ hc⟩
    refine Finset.card_le_one.2 fun x hx y hy => ?_
    obtain ⟨hxu, hx'⟩ := key x hx
    obtain ⟨hyu, hy'⟩ := key y hy
    exact hbij.injOn (by simpa using hxu) (by simpa using hyu)
      (hm _ (hbij.mapsTo (by simpa using hxu)) _ (hbij.mapsTo (by simpa using hyu)) hx' hy')
  -- the remaining tasks, together with `t`, are compound tasks of `tn₁`
  have hold : (s.filter (· ∉ tn'.T)).card + 1 ≤ 2 := by
    have hmem : ∀ x ∈ s.filter (· ∉ tn'.T), x ∈ tn₁.T ∧ x ≠ t ∧ tn₁.IsAbstractId x := by
      intro x hx
      obtain ⟨hxs, hxu⟩ := Finset.mem_filter.1 hx
      obtain ⟨c, hc⟩ := habs x hxs
      rw [decomposeWith_α, if_neg hxu] at hc
      rcases mem_decomposeWith_T.1 (hs hxs) with ⟨hxT, hxt⟩ | hxu'
      · exact ⟨hxT, hxt, c, hc⟩
      · exact absurd hxu' hxu
    have htn : t ∉ s.filter (· ∉ tn'.T) := fun ht => (hmem t ht).2.1 rfl
    rw [← Finset.card_insert_of_notMem htn]
    refine h₁ _ (Finset.insert_subset htT fun x hx => (hmem x hx).1) fun x hx => ?_
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨_, hαt⟩
    · exact (hmem x hx).2.2
  omega

/-- **In a two-hole-digging problem every reachable task network has at most two compound
tasks** — so a decomposition interleaves two sequences of methods, each applied to the only
compound task descending from one of the (at most two) initial compound tasks. -/
theorem IsHD2.reachable_isTwoHole {P : Problem F A C I} (h : P.IsHD2) {tn : TaskNetwork I A C}
    (hr : P.Reachable tn) : tn.IsTwoHole := by
  induction hr with
  | refl => exact h.1
  | tail hpre hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact decompStep_isTwoHole hs ih (h.2 m (reachableMethod_of_decomposesTo hpre hs))

end Invariant

end Problem

/-! ### The named class -/

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x)

/-- `2-HD-HTN`: two-hole-digging HTN planning problems. -/
def HD2_HTN : Set (Problem F A C I) := {P | P.IsHD2}

theorem HD1_HTN_subset_HD2_HTN : HD1_HTN F A C I ⊆ HD2_HTN F A C I :=
  fun _ h => Problem.IsHD1.isHD2 h

theorem HTN_REG_subset_HD2_HTN : HTN_REG F A C I ⊆ HD2_HTN F A C I :=
  (HTN_REG_subset_HD1_HTN F A C I).trans (HD1_HTN_subset_HD2_HTN F A C I)

theorem STRIPS_subset_HD2_HTN (F A C I : Type) [DecidableEq I] :
    STRIPS F A C I ⊆ HD2_HTN F A C I :=
  fun _ h => ((STRIPS_subset_TO_HD1_HTN F A C I h).2).isHD2

end Classes

namespace Table

namespace Cls

/-- The family `2-HD-HTN`. -/
def HD2_HTN : Family := fun F A C I _ => Classes.HD2_HTN F A C I

end Cls

end Table

end HTN
