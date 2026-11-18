import HtnPlanning.Core.ClassExamples
import HtnPlanning.Classes.UOHD
/-!
# Examples separating `UO-HTN`, `1-HD-HTN` and their sub-types from the other classes

The inclusions of `HtnPlanning/Classes/UOHD.lean` are strict, and the remaining pairs are
incomparable.  The witnesses are the example problems of
`HtnPlanning/Core/ClassExamples.lean` together with two new ones:

| problem | methods | in | not in |
| --- | --- | --- | --- |
| `Pnontr` | `c ↦ c ≺ a` | `TO-1-HD-HTN` | `HTN-TR` (so not `HTN-REG`) |
| `Preg` | `c ↦ a ≺ c` | `TO-1-HD-HTN` | `UO-HTN`, `HTN-AC` |
| `Pac` | `t ↦ f ≺ f` | `TO-HTN-AC` | `1-HD-HTN` |
| `Pnonto` | `c ↦ {a, a}` | `UO-1-HD-HTN` | `TO-HTN` |
| `Puo2` | `c ↦ {c, c}` | `UO-HTN` | `1-HD-HTN` |
| `Puohd` | `c ↦ {a, c}` | `UO-1-HD-HTN` | `HTN-TR` (so not `HTN-REG`) |

`Puohd` is the forgetful image of the `STRIPS`-like problem `c ↦ a ≺ c`
(`HtnCompilability/Computable/DropOrder.lean`): its recursion is through a compound task that
is not last, so it is not tail recursive, although it is unordered and one-hole.
-/

namespace HTN

namespace Examples

/-! ### Two new example problems -/

/-- `Puo2`: the unordered problem `c ↦ {c, c}`; it has two compound tasks in a method. -/
def Puo2 : Problem Unit Unit Unit ℕ :=
  mkProblem (tnSingle (Sum.inr ())) {⟨(), tnPairUnord (Sum.inr ()) (Sum.inr ())⟩}

/-- `Puohd`: the unordered one-hole problem `c ↦ {a, c}`. -/
def Puohd : Problem Unit Unit Unit ℕ :=
  mkProblem (tnSingle (Sum.inr ())) {⟨(), tnPairUnord (Sum.inl ()) (Sum.inr ())⟩}

/-! ### Small facts about the example networks -/

variable {A C : Type}

lemma tnSingle_isOneHole (v : A ⊕ C) : (tnSingle v).IsOneHole := by
  intro t ht t' ht' _ _
  simp only [tnSingle, Finset.mem_singleton] at ht ht'
  rw [ht, ht']

lemma tnSingle_isUnordered (v : A ⊕ C) : (tnSingle v).IsUnordered := fun _ _ _ _ h => h

lemma tnSingle_isTotallyOrdered (v : A ⊕ C) : (tnSingle v).IsTotallyOrdered := by
  intro t ht t' ht' hne
  simp only [tnSingle, Finset.mem_singleton] at ht ht'
  exact absurd (ht.trans ht'.symm) hne

lemma tnPairUnord_isUnordered (v w : A ⊕ C) : (tnPairUnord v w).IsUnordered :=
  fun _ _ _ _ h => h

lemma tnPairOrd_isTotallyOrdered (v w : A ⊕ C) : (tnPairOrd v w).IsTotallyOrdered := by
  intro t ht t' ht' hne
  simp only [tnPairOrd, Finset.mem_insert, Finset.mem_singleton] at ht ht'
  rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hne

/-- A two-task network with a primitive second task is one-hole. -/
lemma tnPairOrd_isOneHole_inl (v : A ⊕ C) (a : A) : (tnPairOrd v (Sum.inl a)).IsOneHole := by
  intro t ht t' ht' ⟨c, hc⟩ ⟨c', hc'⟩
  simp only [tnPairOrd, Finset.mem_insert, Finset.mem_singleton] at ht ht'
  rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl <;> simp_all [tnPairOrd]

/-- A two-task network with a primitive first task is one-hole. -/
lemma tnPairUnord_isOneHole_inl (a : A) (w : A ⊕ C) : (tnPairUnord (Sum.inl a) w).IsOneHole := by
  intro t ht t' ht' ⟨c, hc⟩ ⟨c', hc'⟩
  simp only [tnPairUnord, Finset.mem_insert, Finset.mem_singleton] at ht ht'
  rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl <;> simp_all [tnPairUnord]

/-- The problems built by `mkProblem` over a single root, with one method. -/
lemma mkProblem_single_isHD1 {C : Type} (c c' : C) (tn : TaskNetwork ℕ Unit C)
    (h : tn.IsOneHole) : (mkProblem (tnSingle (Sum.inr c)) {⟨c', tn⟩}).IsHD1 := by
  refine ⟨tnSingle_isOneHole _, ?_⟩
  rintro m ⟨hm, -⟩
  simp only [mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  exact h

lemma mkProblem_single_isUO {C : Type} (c c' : C) (tn : TaskNetwork ℕ Unit C)
    (h : tn.IsUnordered) : (mkProblem (tnSingle (Sum.inr c)) {⟨c', tn⟩}).IsUO := by
  refine ⟨tnSingle_isUnordered _, ?_⟩
  rintro m ⟨hm, -⟩
  simp only [mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  exact h

lemma mkProblem_single_isTO {C : Type} (c c' : C) (tn : TaskNetwork ℕ Unit C)
    (h : tn.IsTotallyOrdered) : (mkProblem (tnSingle (Sum.inr c)) {⟨c', tn⟩}).IsTO := by
  refine ⟨tnSingle_isTotallyOrdered _, ?_⟩
  rintro m ⟨hm, -⟩
  simp only [mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  exact h

/-! ### Membership of the examples -/

lemma Pnontr_isHD1 : Pnontr.IsHD1 := mkProblem_single_isHD1 _ _ _ (tnPairOrd_isOneHole_inl _ _)

lemma Pnontr_isTO : Pnontr.IsTO := mkProblem_single_isTO _ _ _ (tnPairOrd_isTotallyOrdered _ _)

lemma Preg_isHD1 : Preg.IsHD1 := Preg_isRegular.isHD1

lemma Preg_isTO : Preg.IsTO := mkProblem_single_isTO _ _ _ (tnPairOrd_isTotallyOrdered _ _)

lemma Preg_not_isUO : ¬ Preg.IsUO := by
  rintro ⟨-, h⟩
  have hm : Preg.ReachableMethod ⟨(), tnPairOrd (Sum.inl ()) (Sum.inr ())⟩ :=
    ⟨by simp [Preg], reachable_root _ _⟩
  exact h _ hm 0 (by simp [tnPairOrd]) 1 (by simp [tnPairOrd]) ⟨rfl, rfl⟩

lemma Pac_isTO : Pac.IsTO := mkProblem_single_isTO _ _ _ (tnPairOrd_isTotallyOrdered _ _)

lemma Pac_not_isHD1 : ¬ Pac.IsHD1 := by
  rintro ⟨-, h⟩
  have hm : Pac.ReachableMethod ⟨true, tnPairOrd (Sum.inr false) (Sum.inr false)⟩ :=
    ⟨by simp [Pac], reachable_root _ _⟩
  exact absurd (h _ hm 0 (by simp [tnPairOrd]) 1 (by simp [tnPairOrd]) ⟨false, rfl⟩
    ⟨false, rfl⟩) (by decide)

lemma Pnonto_isUO : Pnonto.IsUO := mkProblem_single_isUO _ _ _ (tnPairUnord_isUnordered _ _)

lemma Pnonto_isHD1 : Pnonto.IsHD1 := Pnonto_isRegular.isHD1

lemma Puo2_isUO : Puo2.IsUO := mkProblem_single_isUO _ _ _ (tnPairUnord_isUnordered _ _)

lemma Puo2_not_isHD1 : ¬ Puo2.IsHD1 := by
  rintro ⟨-, h⟩
  have hm : Puo2.ReachableMethod ⟨(), tnPairUnord (Sum.inr ()) (Sum.inr ())⟩ :=
    ⟨by simp [Puo2], reachable_root _ _⟩
  exact absurd (h _ hm 0 (by simp [tnPairUnord]) 1 (by simp [tnPairUnord]) ⟨(), rfl⟩
    ⟨(), rfl⟩) (by decide)

lemma Puohd_isUO : Puohd.IsUO := mkProblem_single_isUO _ _ _ (tnPairUnord_isUnordered _ _)

lemma Puohd_isHD1 : Puohd.IsHD1 := mkProblem_single_isHD1 _ _ _ (tnPairUnord_isOneHole_inl _ _)

lemma Puohd_not_isTailRecursive : ¬ Puohd.IsTailRecursive := by
  rintro ⟨le, hle⟩
  have hm : Puohd.ReachableMethod ⟨(), tnPairUnord (Sum.inl ()) (Sum.inr ())⟩ :=
    ⟨by simp [Puohd], reachable_root _ _⟩
  have hnl : ¬ (tnPairUnord (Sum.inl ()) (Sum.inr ()) : TaskNetwork ℕ Unit Unit).IsLastId 1 := by
    rintro ⟨-, h⟩
    exact h 0 (by simp [tnPairUnord]) (by decide)
  obtain ⟨h₁, h₂⟩ := hle.nonlast _ hm 1 (by simp [tnPairUnord]) hnl () (by simp [tnPairUnord])
  exact h₂ h₁

/-! ### The separation statements -/

namespace Classes

open HTN.Classes

/-- `HTN-REG ⊊ 1-HD-HTN`. -/
theorem HTN_REG_ssubset_HD1_HTN : HTN_REG Unit Unit Unit ℕ ⊂ HD1_HTN Unit Unit Unit ℕ :=
  ⟨HTN_REG_subset_HD1_HTN _ _ _ _,
    fun h => Pnontr_not_isTailRecursive (Problem.IsRegular.isTailRecursive (h Pnontr_isHD1))⟩

/-- `TO-HTN-REG ⊊ TO-1-HD-HTN`. -/
theorem TO_HTN_REG_ssubset_TO_HD1_HTN :
    TO_HTN_REG Unit Unit Unit ℕ ⊂ TO_HD1_HTN Unit Unit Unit ℕ :=
  ⟨TO_HTN_REG_subset_TO_HD1_HTN _ _ _ _, fun h => Pnontr_not_isTailRecursive
    (Problem.IsRegular.isTailRecursive (h ⟨Pnontr_isTO, Pnontr_isHD1⟩).2)⟩

/-- `TO-1-HD-HTN ⊄ HTN-TR`: one-hole recursion need not be tail recursion. -/
theorem TO_HD1_HTN_not_subset_HTN_TR :
    ¬ TO_HD1_HTN Unit Unit Unit ℕ ⊆ HTN_TR Unit Unit Unit ℕ :=
  fun h => Pnontr_not_isTailRecursive (h ⟨Pnontr_isTO, Pnontr_isHD1⟩)

/-- `UO-1-HD-HTN ⊄ HTN-TR`. -/
theorem UO_HD1_HTN_not_subset_HTN_TR :
    ¬ UO_HD1_HTN Unit Unit Unit ℕ ⊆ HTN_TR Unit Unit Unit ℕ :=
  fun h => Puohd_not_isTailRecursive (h ⟨Puohd_isUO, Puohd_isHD1⟩)

/-- `UO-1-HD-HTN ⊄ HTN-REG`. -/
theorem UO_HD1_HTN_not_subset_HTN_REG :
    ¬ UO_HD1_HTN Unit Unit Unit ℕ ⊆ HTN_REG Unit Unit Unit ℕ :=
  fun h => Puohd_not_isTailRecursive
    (Problem.IsRegular.isTailRecursive (h ⟨Puohd_isUO, Puohd_isHD1⟩))

/-- `TO-1-HD-HTN ⊄ HTN-AC`. -/
theorem TO_HD1_HTN_not_subset_HTN_AC :
    ¬ TO_HD1_HTN Unit Unit Unit ℕ ⊆ HTN_AC Unit Unit Unit ℕ :=
  fun h => Preg_not_isAcyclic (h ⟨Preg_isTO, Preg_isHD1⟩)

/-- `TO-HTN-AC ⊄ 1-HD-HTN`. -/
theorem TO_HTN_AC_not_subset_HD1_HTN :
    ¬ TO_HTN_AC Unit Unit Bool ℕ ⊆ HD1_HTN Unit Unit Bool ℕ :=
  fun h => Pac_not_isHD1 (h ⟨Pac_isTO, Pac_isAcyclic⟩)

/-- `UO-1-HD-HTN ⊄ TO-HTN`. -/
theorem UO_HD1_HTN_not_subset_TO_HTN :
    ¬ UO_HD1_HTN Unit Unit Unit ℕ ⊆ TO_HTN Unit Unit Unit ℕ :=
  fun h => Pnonto_not_isTO (h ⟨Pnonto_isUO, Pnonto_isHD1⟩)

/-- `TO-1-HD-HTN ⊄ UO-HTN`. -/
theorem TO_HD1_HTN_not_subset_UO_HTN :
    ¬ TO_HD1_HTN Unit Unit Unit ℕ ⊆ UO_HTN Unit Unit Unit ℕ :=
  fun h => Preg_not_isUO (h ⟨Preg_isTO, Preg_isHD1⟩)

/-- `UO-HTN ⊄ 1-HD-HTN`. -/
theorem UO_HTN_not_subset_HD1_HTN :
    ¬ UO_HTN Unit Unit Unit ℕ ⊆ HD1_HTN Unit Unit Unit ℕ :=
  fun h => Puo2_not_isHD1 (h Puo2_isUO)

/-- `UO-1-HD-HTN ⊊ UO-HTN`. -/
theorem UO_HD1_HTN_ssubset_UO_HTN : UO_HD1_HTN Unit Unit Unit ℕ ⊂ UO_HTN Unit Unit Unit ℕ :=
  ⟨Set.inter_subset_left, fun h => Puo2_not_isHD1 (h Puo2_isUO).2⟩

/-- `UO-1-HD-HTN ⊊ 1-HD-HTN`. -/
theorem UO_HD1_HTN_ssubset_HD1_HTN : UO_HD1_HTN Unit Unit Unit ℕ ⊂ HD1_HTN Unit Unit Unit ℕ :=
  ⟨Set.inter_subset_right, fun h => Preg_not_isUO (h Preg_isHD1).1⟩

/-- `TO-1-HD-HTN ⊊ 1-HD-HTN`. -/
theorem TO_HD1_HTN_ssubset_HD1_HTN : TO_HD1_HTN Unit Unit Unit ℕ ⊂ HD1_HTN Unit Unit Unit ℕ :=
  ⟨Set.inter_subset_right, fun h => Pnonto_not_isTO (h Pnonto_isHD1).1⟩

/-- `TO-1-HD-HTN ⊊ TO-HTN`. -/
theorem TO_HD1_HTN_ssubset_TO_HTN : TO_HD1_HTN Unit Unit Bool ℕ ⊂ TO_HTN Unit Unit Bool ℕ :=
  ⟨Set.inter_subset_left, fun h => Pac_not_isHD1 (h Pac_isTO).2⟩

end Classes

end Examples

end HTN
