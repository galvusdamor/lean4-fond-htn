import HtnComplexity.Computable.AcFreeMid
/-!
# The boot phase of the vocabulary-free wrapper

The first task of the initial task network of `HTN.Syn.AcFree.wrapInst` is the boot action, whose
job is to turn the initial state of the *wrapped* instance — the licences and the receipts of the
source facts — into the initial state the acyclic construction expects.  This file computes that
step, and records the two sets it produces:

* `HTN.Syn.AcFree.acStart V` — the state the acyclic construction starts from, which is exactly
  the initial state of `HTN.Syn.Ac.acInstOf` and consists of facts of the base shape;
* `HTN.Syn.AcFree.wrapExtra V q` — the facts of the wrapper that survive the boot action: all
  licences, and the receipts of the source facts **outside** the vocabulary.  None of them has
  the base shape, so the frame property of `HtnComplexity/Computable/AcFreePhases.lean`
  applies to them.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

variable {V : List ℕ} {d₀ : DomDesc} {q : InstDesc}

/-! ### The two parts of the state after the boot action -/

/-- The state the acyclic construction starts from. -/
def acStart (V : List ℕ) : Set ℕ := {f | f = fKey0 ∨ ∃ v ∈ V, ∃ i < 5, f = fNeg v i}

/-- The facts of the wrapper that survive the boot action. -/
def wrapExtra (V : List ℕ) (q : InstDesc) : Set ℕ :=
  {f | (∃ u ∈ q.initList, f = fLic u) ∨ (∃ u ∈ q.initList, u ∉ V ∧ f = fRes u)}

/-- The state the acyclic construction starts from is the initial state of the compiled
instance. -/
lemma acStart_eq (S goalL : List ℕ) (root : ℕ) :
    {f | f ∈ (acInstOf V S goalL root).initList} = acStart V := by
  ext f
  simp only [acInstOf, InstDesc.initList, Set.mem_setOf_eq, List.mem_cons, List.mem_flatMap,
    List.mem_map, List.mem_range, acStart]
  constructor
  · rintro (rfl | ⟨v, hv, i, hi, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨v, hv, i, hi, rfl⟩
  · rintro (rfl | ⟨v, hv, i, hi, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨v, hv, i, hi, rfl⟩

/-- The state the acyclic construction starts from consists of facts of the base shape. -/
lemma acStart_subset_baseFacts : acStart V ⊆ baseFacts := by
  rintro f (rfl | ⟨v, -, i, -, rfl⟩)
  · exact baseFact_fKey0
  · exact baseFact_fNeg v i

/-- No fact of the wrapper has the base shape. -/
lemma not_baseFact_wrapExtra : ∀ f ∈ wrapExtra V q, f ∉ baseFacts := by
  rintro f (⟨u, -, rfl⟩ | ⟨u, -, -, rfl⟩)
  · exact not_baseFact_fLic u
  · exact not_baseFact_fRes u

/-! ### The boot step -/

/-- **The boot action turns the initial state of the wrapped instance into the initial state of
the acyclic construction, plus the facts of the wrapper that survive.** -/
theorem transition_boot (hshape : BaseShaped d₀) :
    (wrapDom V d₀).toDomain.transition aBoot {f | f ∈ (wrapInst q).initList} =
      acStart V ∪ wrapExtra V q := by
  show ({f | f ∈ (wrapInst q).initList} \ (wrapDom V d₀).del aBoot) ∪
    (wrapDom V d₀).add aBoot = _
  rw [add_boot V d₀ hshape, del_boot V d₀ hshape]
  ext f
  simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, wrapInst_initList, List.mem_append,
    List.mem_map, acStart, wrapExtra]
  constructor
  · rintro (⟨hmem, hdel⟩ | hadd)
    · refine Or.inr ?_
      rcases hmem with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · exact Or.inl ⟨u, hu, rfl⟩
      · exact Or.inr ⟨u, hu, fun hv => hdel ⟨u, hv, rfl⟩, rfl⟩
    · exact Or.inl hadd
  · rintro (hadd | hextra)
    · exact Or.inr hadd
    · refine Or.inl ⟨?_, ?_⟩
      · rcases hextra with ⟨u, hu, rfl⟩ | ⟨u, hu, -, rfl⟩
        · exact Or.inl ⟨u, hu, rfl⟩
        · exact Or.inr ⟨u, hu, rfl⟩
      · rintro ⟨v, hv, hfv⟩
        rcases hextra with ⟨u, -, rfl⟩ | ⟨u, -, hu, rfl⟩
        · exact fLic_ne_fRes u v hfv
        · exact hu (fRes_injective hfv ▸ hv)

/-! ### The goal of the compiled instance -/

/-- The goal facts of the compiled instance, listed. -/
lemma mem_acInstOf_goalList {S goalL : List ℕ} {root f : ℕ} :
    f ∈ (acInstOf V S goalL root).goalList ↔
      (∃ u ∈ S, f = fPos u 0) ∨ (∃ u ∈ V, u ∉ S ∧ f = fNeg u 0) ∨
        (∃ u ∈ goalL, f = fPos u 2) ∨ f = fTask (nC root) := by
  simp only [acInstOf, InstDesc.goalList, List.mem_append, List.mem_map, List.mem_filter,
    List.mem_singleton, Bool.not_eq_true']
  constructor
  · rintro (((⟨u, hu, rfl⟩ | ⟨u, ⟨hu, hs⟩, rfl⟩) | ⟨u, hu, rfl⟩) | rfl)
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr (Or.inl ⟨u, hu, fun hc => by simp [memB_iff.2 hc] at hs, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨u, hu, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, hs, rfl⟩ | ⟨u, hu, rfl⟩ | rfl)
    · exact Or.inl (Or.inl (Or.inl ⟨u, hu, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨u, ⟨hu, Bool.eq_false_iff.2 fun hc => hs (memB_iff.1 hc)⟩, rfl⟩))
    · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
    · exact Or.inr rfl

end AcFree

end Syn

end HTN
