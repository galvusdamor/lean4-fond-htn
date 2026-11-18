import HtnPlanning.Core.UOHDExamples
import HtnPlanning.Classes.HD2
import HtnPlanning.Classes.LU
/-!
# Examples separating `2-HD-HTN` from `1-HD-HTN` and `HTN`

The inclusions `1-HD-HTN ⊆ 2-HD-HTN ⊆ HTN` of `HtnPlanning/Classes/HD2.lean` are strict.  The
witnesses are the example problem `Puo2` of `HtnPlanning/Core/UOHDExamples.lean` together with
one new problem:

| problem | initial network | methods | in | not in |
| --- | --- | --- | --- | --- |
| `Phd2` | `{c, c}` | `c ↦ a` | `2-HD-HTN` | `1-HD-HTN` |
| `Puo2` | `c` | `c ↦ {c, c}` | `UO-HTN` | `2-HD-HTN` |

`Phd2` is moreover loop-unrolling, so it also separates `1-HD-HTN ∩ L` from `2-HD-HTN ∩ L`.
-/

namespace HTN

namespace Examples

/-! ### A new example problem -/

/-- `Phd2`: two unordered initial compound tasks `{c, c}`, each decomposed by `c ↦ a`. -/
def Phd2 : Problem Unit Unit Unit ℕ :=
  mkProblem (tnPairUnord (Sum.inr ()) (Sum.inr ())) {⟨(), tnSingle (Sum.inl ())⟩}

/-! ### Small facts about the example networks -/

variable {A C : Type}

/-- A two-task network is two-hole. -/
lemma tnPairUnord_isTwoHole (v w : A ⊕ C) : (tnPairUnord v w).IsTwoHole :=
  fun _ hs _ => (Finset.card_le_card hs).trans (by simp [tnPairUnord])

/-! ### Membership of the examples -/

lemma Phd2_isHD2 : Phd2.IsHD2 := by
  refine ⟨tnPairUnord_isTwoHole _ _, ?_⟩
  rintro m ⟨hm, -⟩
  simp only [Phd2, mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  exact tnSingle_isOneHole _

lemma Phd2_not_isHD1 : ¬ Phd2.IsHD1 := by
  rintro ⟨h, -⟩
  exact absurd (h 0 (by simp [Phd2, tnPairUnord]) 1 (by simp [Phd2, tnPairUnord]) ⟨(), rfl⟩
    ⟨(), rfl⟩) (by decide)

lemma Phd2_isLU : Phd2.IsLU := by
  refine ⟨Set.subsingleton_of_subsingleton, ?_⟩
  calc {m | Phd2.ReachableMethod m}.encard
      ≤ ({⟨(), tnSingle (Sum.inl ())⟩} : Set (Method ℕ Unit Unit)).encard :=
        Set.encard_le_encard fun _ hm => hm.1
    _ = 1 := Set.encard_singleton _
    _ ≤ 2 := by norm_num

lemma Puo2_not_isHD2 : ¬ Puo2.IsHD2 :=
  fun h => Puo2_not_isHD1 (h.isHD1 (tnSingle_isOneHole _))

/-! ### The separation statements -/

namespace Classes

open HTN.Classes

/-- `1-HD-HTN ⊊ 2-HD-HTN`. -/
theorem HD1_HTN_ssubset_HD2_HTN : HD1_HTN Unit Unit Unit ℕ ⊂ HD2_HTN Unit Unit Unit ℕ :=
  ⟨HD1_HTN_subset_HD2_HTN _ _ _ _, fun h => Phd2_not_isHD1 (h Phd2_isHD2)⟩

/-- `2-HD-HTN ⊊ HTN`. -/
theorem HD2_HTN_ssubset_HTN : HD2_HTN Unit Unit Unit ℕ ⊂ HTN Unit Unit Unit ℕ :=
  ⟨fun _ _ => trivial, fun h => Puo2_not_isHD2 (h trivial)⟩

/-- `1-HD-HTN ∩ L ⊊ 2-HD-HTN ∩ L`. -/
theorem HD1_LU_HTN_ssubset_HD2_LU_HTN :
    HD1_LU_HTN Unit Unit Unit ℕ ⊂ HD2_LU_HTN Unit Unit Unit ℕ :=
  ⟨HD1_LU_HTN_subset_HD2_LU_HTN _ _ _ _, fun h => Phd2_not_isHD1 (h ⟨Phd2_isHD2, Phd2_isLU⟩).1⟩

/-- `UO-HTN ⊄ 2-HD-HTN`. -/
theorem UO_HTN_not_subset_HD2_HTN :
    ¬ UO_HTN Unit Unit Unit ℕ ⊆ HD2_HTN Unit Unit Unit ℕ :=
  fun h => Puo2_not_isHD2 (h Puo2_isUO)

end Classes

end Examples

end HTN
