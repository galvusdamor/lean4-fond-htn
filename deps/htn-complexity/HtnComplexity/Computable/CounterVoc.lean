import HtnComplexity.Computable.CounterFamily
import HtnComplexity.Computable.AcSmall
import HtnPlanning.Computable.Relevance
/-!
# The counting family is small, and lives over one vocabulary

The point of the family of `HtnComplexity/Computable/CounterFamily.lean` is that its `2 ^ r`
domain descriptions are *small* and share *one* vocabulary: this file proves both.

* `HTN.Syn.size_cntDom_le` — the description `cntDom r i` has size at most
  `(2 * r + 1) * (3 * r + 5)`, so quadratic in `r`, uniformly in `i`;
* `HTN.Syn.cntDom_coveredBy` — every one of them is covered by the `2 * r + 1` facts
  `List.range (2 * r + 1)` and the names `List.range (2 * r + 3)`.

The instances are covered by the same vocabulary (`HTN.Syn.wordInst_coveredBy`), so the whole
family of `2 ^ r` problems is a family over a single vocabulary of size `O(r)`.
-/

namespace HTN

namespace Syn

open Bits

variable {r i : ℕ}

/-! ### The facts of the family -/

theorem length_incPrec {j : ℕ} : (incPrec j).length = j + 1 := by simp [incPrec]

theorem length_incAdd {j : ℕ} : (incAdd j).length = j + 1 := by simp [incAdd]

theorem length_stList {l : List Bool} : (stList l).length = l.length := by simp [stList]

theorem mem_incPrec_lt {j f : ℕ} (hj : j < r) (hf : f ∈ incPrec j) : f < 2 * r + 1 := by
  rcases mem_incPrec.1 hf with ⟨k, hk, rfl⟩ | rfl
  · have := bitF_lt (b := true) (show k < r by omega)
    unfold gF at this; omega
  · have := bitF_lt (b := false) hj
    unfold gF at this; omega

theorem mem_incAdd_lt {j f : ℕ} (hj : j < r) (hf : f ∈ incAdd j) : f < 2 * r + 1 := by
  rcases mem_incAdd.1 hf with ⟨k, hk, rfl⟩ | rfl
  · have := bitF_lt (b := false) (show k < r by omega)
    unfold gF at this; omega
  · have := bitF_lt (b := true) hj
    unfold gF at this; omega

theorem mem_stList_cnt_lt {t f : ℕ} (hf : f ∈ stList (cnt r t)) : f < 2 * r + 1 := by
  obtain ⟨k, hk, rfl⟩ := mem_stList.1 hf
  rw [length_cnt] at hk
  have := bitF_lt (b := (cnt r t).getI k) hk
  unfold gF at this; omega

/-- Every fact the `m`-th step mentions is one of the `2 * r + 1` facts of the vocabulary. -/
theorem facts_cntEntry_lt {m f : ℕ} (hm : m < 2 * r + 1)
    (hf : f ∈ (cntEntry r i m).2.1 ∨ f ∈ (cntEntry r i m).2.2.1 ∨ f ∈ (cntEntry r i m).2.2.2) :
    f < 2 * r + 1 := by
  by_cases h1 : m < r
  · rw [cntEntry_inc_lt h1] at hf
    rcases hf with h | h | h
    · exact mem_incPrec_lt h1 h
    · exact mem_incAdd_lt h1 h
    · exact mem_incPrec_lt h1 h
  · by_cases h2 : m < 2 * r
    · have hj : m - r < r := by omega
      rw [cntEntry_inc_ge (by omega) h2] at hf
      rcases hf with h | h | h
      · exact mem_incPrec_lt hj h
      · exact mem_incAdd_lt hj h
      · exact mem_incPrec_lt hj h
    · have hm2 : m = 2 * r := by omega
      subst hm2
      rw [cntEntry_mark] at hf
      rcases hf with h | h | h
      · exact mem_stList_cnt_lt h
      · rcases List.mem_cons.1 h with rfl | h'
        · unfold gF; omega
        · exact mem_stList_cnt_lt h'
      · exact mem_stList_cnt_lt h

/-! ### The vocabulary -/

/-- **The counting family lives over one vocabulary**: the `2 * r + 1` facts and the
`2 * r + 3` names, whatever the index `i`. -/
theorem cntDom_coveredBy :
    (cntDom r i).CoveredBy (List.range (2 * r + 1)) (List.range (2 * r + 3)) := by
  constructor
  · intro a
    by_cases ha : a < 2 * r + 1
    · have hlen : a < (cntP r i).length := by rw [length_cntP]; exact ha
      refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_⟩
      · rw [cntDom, prec_stepDom hlen] at hf
        rw [getI_cntP ha] at hf
        exact List.mem_range.2 (facts_cntEntry_lt ha (Or.inl hf))
      · rw [cntDom, add_stepDom hlen] at hf
        rw [getI_cntP ha] at hf
        exact List.mem_range.2 (facts_cntEntry_lt ha (Or.inr (Or.inl hf)))
      · rw [cntDom, del_stepDom hlen] at hf
        rw [getI_cntP ha] at hf
        exact List.mem_range.2 (facts_cntEntry_lt ha (Or.inr (Or.inr hf)))
    · have hlen : (cntP r i).length ≤ a := by rw [length_cntP]; omega
      refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_⟩
      · rw [cntDom, prec_stepDom_of_le hlen] at hf; exact absurd hf (Set.notMem_empty f)
      · rw [cntDom, add_stepDom_of_le hlen] at hf; exact absurd hf (Set.notMem_empty f)
      · rw [cntDom, del_stepDom_of_le hlen] at hf; exact absurd hf (Set.notMem_empty f)
  · intro e he
    rw [cntDom] at he
    simp only [stepDom_methods, List.mem_map, List.mem_range] at he
    obtain ⟨m, hm, rfl⟩ := he
    rw [length_cntP] at hm
    constructor
    · have hname : ((cntP r i).getI m).1 = cA ∨ ((cntP r i).getI m).1 = cB := by
        rw [getI_cntP hm]
        by_cases h1 : m < r
        · exact Or.inl (by rw [cntEntry_inc_lt h1])
        · by_cases h2 : m < 2 * r
          · exact Or.inr (by rw [cntEntry_inc_ge (by omega) h2])
          · have : m = 2 * r := by omega
            subst this
            exact Or.inr (by rw [cntEntry_mark])
      rcases hname with h | h <;> rw [h] <;> exact List.mem_range.2 (by simp only [cA, cB]; omega)
    · intro c hc
      have hc' : c = 0 ∨ c = m := by simpa [TnDesc.namesOf, TnDesc.lbl] using hc
      rcases hc' with rfl | rfl
      · exact List.mem_range.2 (by omega)
      · exact List.mem_range.2 (by omega)

/-- The names of a chain description are the names of its letters. -/
theorem namesOf_chainTnDesc {S : List ℕ} : (chainTnDesc S).namesOf ⊆ 0 :: S := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc'
  · exact List.mem_cons_self
  · simp only [chainTnDesc, gridDesc, TnDesc.lbl, List.mem_map] at hc'
    obtain ⟨x, hx, rfl⟩ := hc'
    simp only [cellLbl, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i0, hi0, j, hj, rfl⟩ := hx
    have hi0' : i0 = 0 := by
      have : i0 < 1 := by simpa using hi0
      omega
    subst hi0'
    have hjS : j < S.length := by
      rw [gridRow_chain] at hj; simpa using hj
    have hval : (gridRow [S.map fun c => (true, c)] 0).getD j (false, 0) = (true, S.getI j) := by
      rw [gridRow_chain, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hjS]
      simp [List.getI_eq_getElem _ hjS]
    rw [hval]
    exact List.mem_cons_of_mem _ (by rw [List.getI_eq_getElem _ hjS]; exact List.getElem_mem hjS)

/-- The instances of the family live over the same vocabulary. -/
theorem wordInst_coveredBy {w : List Bool} :
    (wordInst r w).CoveredBy (List.range (2 * r + 1)) (List.range (2 * r + 3)) := by
  constructor
  · intro f hf
    exact List.mem_range.2 (mem_stList_cnt_lt (t := 0) (by rw [cnt_zero]; exact hf))
  · intro f hf
    have hf' : f = gF r := by simpa [wordInst, stepInst, InstDesc.goalList] using hf
    subst hf'
    exact List.mem_range.2 (by simp only [gF]; omega)
  · intro c hc
    have hc' : c ∈ 0 :: (w.map letterName) :=
      namesOf_chainTnDesc (by simpa [wordInst, stepInst, InstDesc.tnI] using hc)
    rcases List.mem_cons.1 hc' with rfl | hc''
    · exact List.mem_range.2 (by omega)
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc''
      cases b
      · exact List.mem_range.2 (by simp only [letterName_false, cA]; omega)
      · exact List.mem_range.2 (by simp only [letterName_true, cB]; omega)

/-- **Every fact written in the counting domain** is one of the `2 * r + 1` facts of the
vocabulary. -/
theorem cntDom_domFacts_lt {f : ℕ} (hf : f ∈ (cntDom r i).domFacts) : f < 2 * r + 1 := by
  simp only [DomDesc.domFacts, cntDom, stepDom_actions, List.mem_flatMap, List.mem_map,
    List.mem_range] at hf
  obtain ⟨x, ⟨m, hm, rfl⟩, hx⟩ := hf
  rw [length_cntP] at hm
  rw [getI_cntP hm] at hx
  rcases List.mem_append.1 hx with hx' | hx'
  · rcases List.mem_append.1 hx' with hx'' | hx''
    · exact facts_cntEntry_lt hm (Or.inl hx'')
    · exact facts_cntEntry_lt hm (Or.inr (Or.inl hx''))
  · exact facts_cntEntry_lt hm (Or.inr (Or.inr hx'))

/-- The counting domain writes only facts of the vocabulary. -/
theorem cntDom_domFacts_mem : ∀ f ∈ (cntDom r i).domFacts, f ∈ List.range (2 * r + 1) :=
  fun _ hf => List.mem_range.2 (cntDom_domFacts_lt hf)

/-! ### The size of the family -/

theorem entry_size_le {m : ℕ} (hm : m < 2 * r + 1) :
    1 + (cntEntry r i m).2.1.length + (cntEntry r i m).2.2.1.length +
      (cntEntry r i m).2.2.2.length ≤ 3 * r + 5 := by
  by_cases h1 : m < r
  · rw [cntEntry_inc_lt h1]
    simp only [length_incPrec, length_incAdd]
    omega
  · by_cases h2 : m < 2 * r
    · rw [cntEntry_inc_ge (by omega) h2]
      simp only [length_incPrec, length_incAdd]
      omega
    · have : m = 2 * r := by omega
      subst this
      rw [cntEntry_mark]
      simp only [length_stList, length_cnt, List.length_cons]
      omega

/-- **The counting domain is small**: its size is quadratic in the number of counter bits,
uniformly in the index it reads. -/
theorem size_cntDom_le : (cntDom r i).size ≤ (2 * r + 1) * (3 * r + 5) + (2 * r + 1) * 3 := by
  have hacts : ((cntDom r i).actions.map ActionDesc.size).sum ≤ (2 * r + 1) * (3 * r + 5) := by
    have hbound : ∀ x ∈ (cntDom r i).actions.map ActionDesc.size, x ≤ 3 * r + 5 := by
      intro x hx
      simp only [cntDom, stepDom_actions, List.map_map, List.mem_map, List.mem_range,
        Function.comp_apply] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      rw [length_cntP] at hm
      have := entry_size_le (r := r) (i := i) hm
      rw [getI_cntP hm]
      simpa [ActionDesc.size] using this
    have hlen : ((cntDom r i).actions.map ActionDesc.size).length = 2 * r + 1 := by
      simp [cntDom, stepDom_actions]
    calc ((cntDom r i).actions.map ActionDesc.size).sum
        ≤ ((cntDom r i).actions.map ActionDesc.size).length • (3 * r + 5) :=
          List.sum_le_card_nsmul _ _ hbound
      _ = (2 * r + 1) * (3 * r + 5) := by rw [hlen, smul_eq_mul]
  have hmeths : ((cntDom r i).methods.map MethodDesc.size).sum ≤ (2 * r + 1) * 3 := by
    have hbound : ∀ x ∈ (cntDom r i).methods.map MethodDesc.size, x ≤ 3 := by
      intro x hx
      simp only [cntDom, stepDom_methods, List.map_map, List.mem_map, List.mem_range,
        Function.comp_apply] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      simp [MethodDesc.size, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
    have hlen : ((cntDom r i).methods.map MethodDesc.size).length = 2 * r + 1 := by
      simp [cntDom, stepDom_methods]
    calc ((cntDom r i).methods.map MethodDesc.size).sum
        ≤ ((cntDom r i).methods.map MethodDesc.size).length • 3 :=
          List.sum_le_card_nsmul _ _ hbound
      _ = (2 * r + 1) * 3 := by rw [hlen, smul_eq_mul]
  simpa [DomDesc.size] using Nat.add_le_add hacts hmeths

end Syn

end HTN
