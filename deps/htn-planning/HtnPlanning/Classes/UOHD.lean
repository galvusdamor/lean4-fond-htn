import HtnPlanning.Classes.Basic
import HtnPlanning.Core.Reachability
import HtnPlanning.Core.Decomposition
import HtnPlanning.Computable.Classes
/-!
# Two further classes: unordered (`UO-HTN`) and one-hole-digging (`1-HD-HTN`) problems

This file adds two structural restrictions of HTN planning problems to the classes of
`HtnPlanning/Classes/Basic.lean`.

* **Unordered problems** (`UO-HTN`), following

    C. Lauer, D. Höller, P. Bercher, *Unordered HTN Planning is in PSPACE and Models Problems
    Beyond STRIPS* (Def. 2.5),

  where task networks carry no ordering at all.  Here, as for `TO-HTN`, the restriction is a
  condition on the initial task network and on the methods *reachable* from it
  (`HTN.Problem.IsUO`): none of these networks orders two of its tasks.

* **One-hole-digging problems** (`1-HD-HTN`), following

    M. Dekker, G. Behnke, *Barely Decidable Fragments of Planning* (Sect. 3),

  where every task network of the problem — the initial one and the subtask network of every
  (reachable) method — contains at most one compound task (`HTN.Problem.IsHD1`).

The *rooted* variants `UO-HTN-1` and `1-HD-HTN-1` (a single initial compound task) are, as for
all other classes of the project, conditions on instance descriptions; they live in
`HtnComplexity/SynClasses/UOHD.lean`.

Besides the definitions this file proves the elementary relations at the semantic level:

* the network-level facts `TaskNetwork.card_le_one_of_TO_of_UO` (a network that is both totally
  ordered and unordered has at most one task), `TaskNetwork.IsRegular.isOneHole` and
  `TaskNetwork.IsRegular.eq_singleton_of_UO` (an unordered regular network is primitive or a
  single compound task);
* the inclusions `HTN-REG ⊆ 1-HD-HTN`, `TO-HTN-REG ⊆ TO-1-HD-HTN`, `STRIPS ⊆ TO-1-HD-HTN`;
* the two invariants of decomposition that motivate the classes:
  `HTN.Problem.IsHD1.reachable_isOneHole` (in a one-hole-digging problem *every* reachable task
  network has at most one compound task, so a decomposition is a single sequence of methods), and
  `HTN.Problem.IsUO.reachable_isUnordered` (in a well-formed unordered problem every reachable
  task network is unordered, so every linearisation of a primitive one is admissible).
-/

namespace HTN

universe u v w x

/-! ### Restrictions on single task networks -/

namespace TaskNetwork

variable {I : Type x} {A : Type v} {C : Type w}

/-- A task network is **unordered** iff no two of its tasks are ordered. -/
def IsUnordered (tn : TaskNetwork I A C) : Prop :=
  ∀ t ∈ tn.T, ∀ t' ∈ tn.T, ¬ tn.ord t t'

/-- A task network is **one-hole** iff it contains at most one compound task (the condition
`|α⁻¹[C]| ≤ 1` of Dekker and Behnke). -/
def IsOneHole (tn : TaskNetwork I A C) : Prop :=
  ∀ t ∈ tn.T, ∀ t' ∈ tn.T, tn.IsAbstractId t → tn.IsAbstractId t' → t = t'

/-- **A regular task network is one-hole** (the first half of the definition of regularity). -/
theorem IsRegular.isOneHole {tn : TaskNetwork I A C} (h : tn.IsRegular) : tn.IsOneHole := h.1

/-- A primitive task network is one-hole. -/
theorem IsPrimitive.isOneHole {tn : TaskNetwork I A C} (h : tn.IsPrimitive) : tn.IsOneHole :=
  h.isRegular.isOneHole

/-- **Totally ordered and unordered is degenerate**: such a network has at most one task. -/
theorem card_le_one_of_TO_of_UO {tn : TaskNetwork I A C} (hto : tn.IsTotallyOrdered)
    (huo : tn.IsUnordered) : tn.T.card ≤ 1 := by
  refine Finset.card_le_one.2 fun t ht t' ht' => ?_
  by_contra hne
  rcases hto t ht t' ht' hne with h | h
  · exact huo t ht t' ht' h
  · exact huo t' ht' t ht h

/-- **Unordered and regular is degenerate**: such a network is primitive, or it consists of a
single compound task (a compound task must be ordered after all other tasks). -/
theorem IsRegular.eq_singleton_of_UO {tn : TaskNetwork I A C} (hreg : tn.IsRegular)
    (huo : tn.IsUnordered) : tn.IsPrimitive ∨ ∃ t, tn.T = {t} ∧ tn.IsAbstractId t := by
  by_cases hp : tn.IsPrimitive
  · exact Or.inl hp
  · right
    simp only [IsPrimitive, not_forall] at hp
    obtain ⟨t, ht, hnp⟩ := hp
    have habs : tn.IsAbstractId t := by
      rcases h : tn.α t with a | c
      · exact absurd ⟨a, h⟩ hnp
      · exact ⟨c, h⟩
    refine ⟨t, Finset.eq_singleton_iff_unique_mem.2 ⟨ht, fun t' ht' => ?_⟩, habs⟩
    by_contra hne
    exact huo t' ht' t ht (hreg.2 t ht habs t' ht' hne)

end TaskNetwork

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### The two restrictions on problems -/

/-- `UO-tn_I`: the initial task network is unordered. -/
def IsUO_tnI (P : Problem F A C I) : Prop := P.tnI.IsUnordered

/-- `UO-M`: every method reachable from the initial task network is unordered. -/
def IsUO_M (P : Problem F A C I) : Prop :=
  ∀ m : Method I A C, P.ReachableMethod m → m.subtasks.IsUnordered

/-- **`UO` (unordered problems, Lauer et al., Def. 2.5)**: the initial task network and every
reachable method are unordered. -/
def IsUO (P : Problem F A C I) : Prop := P.IsUO_tnI ∧ P.IsUO_M

/-- **`1-HD` (one-hole-digging problems, Dekker and Behnke, Sect. 3)**: the initial task network
and the subtask network of every reachable method contain at most one compound task. -/
def IsHD1 (P : Problem F A C I) : Prop :=
  P.tnI.IsOneHole ∧ ∀ m : Method I A C, P.ReachableMethod m → m.subtasks.IsOneHole

/-! ### Elementary relations -/

/-- **A regular problem is one-hole-digging.** -/
theorem IsRegular.isHD1 {P : Problem F A C I} (h : P.IsRegular) : P.IsHD1 :=
  ⟨h.1.isOneHole, fun m hm => (h.2 m hm).isOneHole⟩

/-- **A STRIPS-like problem is one-hole-digging.** -/
theorem IsStripsLike.isHD1 [DecidableEq I] {P : Problem F A C I} (h : P.IsStripsLike) :
    P.IsHD1 := by
  obtain ⟨c, ⟨t, hT, -⟩, hm⟩ := h
  refine ⟨fun x hx y hy _ _ => ?_, fun m hr => ?_⟩
  · rw [hT, Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm
  · rcases (hm m hr).2 with hempty | ⟨t₁, t₂, -, hT₂, ⟨a, ha⟩, -, -⟩
    · intro x hx
      rw [hempty] at hx
      exact absurd hx (Finset.notMem_empty x)
    · intro x hx y hy hax hay
      have hnot : ∀ z ∈ m.subtasks.T, m.subtasks.IsAbstractId z → z = t₂ := by
        intro z hz hz'
        rw [hT₂, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · obtain ⟨c', hc'⟩ := hz'
          rw [ha] at hc'
          exact absurd hc' (by simp)
        · rfl
      exact (hnot x hx hax).trans (hnot y hy hay).symm

/-- **Totally ordered and unordered problems are degenerate**: every reachable method has at
most one subtask. -/
theorem IsUO.card_le_one_of_isTO {P : Problem F A C I} (huo : P.IsUO) (hto : P.IsTO) :
    P.tnI.T.card ≤ 1 ∧ ∀ m : Method I A C, P.ReachableMethod m → m.subtasks.T.card ≤ 1 :=
  ⟨TaskNetwork.card_le_one_of_TO_of_UO hto.1 huo.1,
    fun m hm => TaskNetwork.card_le_one_of_TO_of_UO (hto.2 m hm) (huo.2 m hm)⟩

/-! ### The two invariants of decomposition -/

section Invariants

variable [DecidableEq I]

/-- One decomposition step with a one-hole method, applied to a one-hole network, yields a
one-hole network: the decomposed task was the only compound task. -/
theorem decompStep_isOneHole {M : Set (Method I A C)} {tn₁ tn₂ : TaskNetwork I A C} {t : I}
    {m : Method I A C} (hstep : DecompStep M tn₁ t m tn₂) (h₁ : tn₁.IsOneHole)
    (hm : m.subtasks.IsOneHole) : tn₂.IsOneHole := by
  obtain ⟨-, htT, hαt, tn', -, ⟨σ, hbij, -, hα⟩, -, rfl⟩ := hstep
  -- a compound task of the result comes from the inserted copy
  have key : ∀ x ∈ (decomposeWith tn₁ t tn').T, (decomposeWith tn₁ t tn').IsAbstractId x →
      x ∈ tn'.T ∧ m.subtasks.IsAbstractId (σ x) := by
    intro x hx ⟨c, hc⟩
    rw [decomposeWith_α] at hc
    by_cases hxu : x ∈ tn'.T
    · rw [if_pos hxu] at hc
      exact ⟨hxu, c, (hα x hxu) ▸ hc⟩
    · rw [if_neg hxu] at hc
      rcases mem_decomposeWith_T.1 hx with ⟨hxT, hxt⟩ | hxu'
      · exact absurd (h₁ x hxT t htT ⟨c, hc⟩ ⟨_, hαt⟩) hxt
      · exact absurd hxu' hxu
  intro x hx y hy hax hay
  obtain ⟨hxu, hx'⟩ := key x hx hax
  obtain ⟨hyu, hy'⟩ := key y hy hay
  exact hbij.injOn (by simpa using hxu) (by simpa using hyu)
    (hm _ (hbij.mapsTo (by simpa using hxu)) _ (hbij.mapsTo (by simpa using hyu)) hx' hy')

/-- **In a one-hole-digging problem every reachable task network has at most one compound
task** — so a decomposition is a single sequence of methods applied to the only compound task
(Dekker and Behnke, Sect. 3). -/
theorem IsHD1.reachable_isOneHole {P : Problem F A C I} (h : P.IsHD1) {tn : TaskNetwork I A C}
    (hr : P.Reachable tn) : tn.IsOneHole := by
  induction hr with
  | refl => exact h.1
  | tail hpre hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact decompStep_isOneHole hs ih (h.2 m (reachableMethod_of_decomposesTo hpre hs))

/-- One decomposition step with an unordered method, applied to a well-formed unordered network,
yields an unordered network. -/
theorem decompStep_isUnordered {M : Set (Method I A C)} {tn₁ tn₂ : TaskNetwork I A C} {t : I}
    {m : Method I A C} (hstep : DecompStep M tn₁ t m tn₂) (hwf : tn₁.WF)
    (h₁ : tn₁.IsUnordered) (hm : m.subtasks.IsUnordered) : tn₂.IsUnordered := by
  obtain ⟨-, htT, -, tn', hwf', ⟨σ, hbij, hord, -⟩, -, rfl⟩ := hstep
  intro a _ b _ hab
  rcases decomposeWith_ord_iff.1 hab with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
  · have ha := hwf'.mem_left h
    have hb := hwf'.mem_right h
    exact hm _ (hbij.mapsTo (by simpa using ha)) _ (hbij.mapsTo (by simpa using hb))
      ((hord a ha b hb).1 h)
  · exact h₁ a (hwf.mem_left h) t htT h
  · exact h₁ t htT b (hwf.mem_right h) h
  · exact h₁ a (hwf.mem_left h) b (hwf.mem_right h) h

/-- **In an unordered problem with a well-formed initial task network every reachable task
network is unordered** — so every linearisation of a reachable primitive network is
admissible. -/
theorem IsUO.reachable_isUnordered {P : Problem F A C I} (h : P.IsUO) (hwf : P.tnI.WF)
    {tn : TaskNetwork I A C} (hr : P.Reachable tn) : tn.IsUnordered := by
  induction hr with
  | refl => exact h.1
  | tail hpre hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact decompStep_isUnordered hs (HTN.DecomposesTo.wf (M := P.methods) hpre hwf) ih
      (h.2 m (reachableMethod_of_decomposesTo hpre hs))

end Invariants

end Problem

/-! ### The named classes -/

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x)

/-- `UO-HTN`: unordered HTN planning problems. -/
def UO_HTN : Set (Problem F A C I) := {P | P.IsUO}

/-- `1-HD-HTN`: one-hole-digging HTN planning problems. -/
def HD1_HTN : Set (Problem F A C I) := {P | P.IsHD1}

/-- `TO-1-HD-HTN`: totally ordered one-hole-digging problems (a sub-type of `1-HD-HTN`). -/
def TO_HD1_HTN : Set (Problem F A C I) := TO_HTN F A C I ∩ HD1_HTN F A C I

/-- `UO-1-HD-HTN`: unordered one-hole-digging problems (the common sub-type of `UO-HTN` and
`1-HD-HTN`). -/
def UO_HD1_HTN : Set (Problem F A C I) := UO_HTN F A C I ∩ HD1_HTN F A C I

theorem HTN_REG_subset_HD1_HTN : HTN_REG F A C I ⊆ HD1_HTN F A C I :=
  fun _ h => Problem.IsRegular.isHD1 h

theorem TO_HTN_REG_subset_TO_HD1_HTN : TO_HTN_REG F A C I ⊆ TO_HD1_HTN F A C I :=
  fun _ h => ⟨h.1, Problem.IsRegular.isHD1 h.2⟩

theorem STRIPS_subset_TO_HD1_HTN (F A C I : Type) [DecidableEq I] :
    STRIPS F A C I ⊆ TO_HD1_HTN F A C I := by
  intro P h
  refine ⟨⟨?_, fun m hm => ?_⟩, Problem.IsStripsLike.isHD1 h⟩
  · obtain ⟨c, ⟨t, hT, -⟩, -⟩ := h
    intro x hx y hy hxy
    rw [hT, Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · obtain ⟨c, -, hm'⟩ := h
    exact (hm' m hm).2.isTotallyOrdered

end Classes

namespace Table

namespace Cls

/-- The family `UO-HTN`. -/
def UO_HTN : Family := fun F A C I _ => Classes.UO_HTN F A C I

/-- The family `1-HD-HTN`. -/
def HD1_HTN : Family := fun F A C I _ => Classes.HD1_HTN F A C I

/-- The family `TO-1-HD-HTN`. -/
def TO_HD1_HTN : Family := fun F A C I _ => Classes.TO_HD1_HTN F A C I

/-- The family `UO-1-HD-HTN`. -/
def UO_HD1_HTN : Family := fun F A C I _ => Classes.UO_HD1_HTN F A C I

end Cls

end Table

end HTN
