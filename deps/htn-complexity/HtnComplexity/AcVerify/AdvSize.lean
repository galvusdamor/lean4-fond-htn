import HtnComplexity.AcVerify.CertSize
/-!
# The length of the advice

If every name of the domain description `d` is below `2 ^ B` (and so is the number of methods
plus one), the advice `advOf d` has length at most `advBound d.size B`, a polynomial in the two
parameters (`HTN.Syn.AcVer.length_advOf_le`).
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc}

/-- The empty instance description (used only to apply the record bounds to method steps). -/
def emptyInst : InstDesc := ([], [], ([], [], []))

/-- **All names of the domain description are below `2 ^ B`**, and so is the number of methods
plus one. -/
structure DomNamesLt (d : DomDesc) (B : ℕ) : Prop where
  dom : ∀ x ∈ d.names, x < 2 ^ B
  meth : d.methods.length + 1 < 2 ^ B

theorem DomNamesLt.namesLt {B : ℕ} (h : DomNamesLt d B) : NamesLt d emptyInst B where
  dom := h.dom
  inst := by simp [emptyInst, InstDesc.names, InstDesc.initList, InstDesc.goalList,
    InstDesc.tnI, TnDesc.names, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  meth := h.meth

/-- The bound on one row of a table. -/
def rowBound (sd B : ℕ) : ℕ := 3 * (1 + sd * (2 * B + 2)) + 8 * B + 4

/-- The bound on the advice. -/
def advBound (sd B : ℕ) : ℕ := 5 * (1 + (sd + 1) ^ 2 * (2 * rowBound sd B + 2))

theorem length_methods_le (d : DomDesc) : d.methods.length ≤ d.size := by
  have : d.methods.length ≤ (d.methods.map MethodDesc.size).sum := by
    have := List.sum_le_sum (l := d.methods) (f := fun _ => 1) (g := MethodDesc.size)
      fun m _ => by simp only [MethodDesc.size]; omega
    simpa [List.map_const', List.sum_replicate] using this
  simp only [DomDesc.size]; omega

theorem length_actions_le (d : DomDesc) : d.actions.length ≤ d.size := by
  have : d.actions.length ≤ (d.actions.map ActionDesc.size).sum := by
    have := List.sum_le_sum (l := d.actions) (f := fun _ => 1) (g := ActionDesc.size)
      fun m _ => by simp only [ActionDesc.size]; omega
    simpa [List.map_const', List.sum_replicate] using this
  simp only [DomDesc.size]; omega

theorem sum_ids_le (d : DomDesc) :
    ((mIdx d).map fun k => (methodAt d k).2.ids.length).sum ≤ d.size := by
  have h1 : ((mIdx d).map fun k => (methodAt d k).2.ids.length) =
      d.methods.map fun e => e.2.ids.length := by
    rw [← map_methodAt_mIdx d, List.map_map]; rfl
  have h2 : (d.methods.map fun e => e.2.ids.length).sum ≤ (d.methods.map MethodDesc.size).sum :=
    List.sum_le_sum fun e _ => by simp only [MethodDesc.size, TnDesc.size]; omega
  rw [h1]; simp only [DomDesc.size]; omega

theorem ids_le_size {k : ℕ} (hk : k ∈ mIdx d) : (methodAt d k).2.ids.length ≤ d.size := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun k => (methodAt d k).2.ids.length) hk)
  exact this.trans (sum_ids_le d)

theorem length_table_le {T : List (List Bool)} {sd M : ℕ} (hT : T.length ≤ (sd + 1) ^ 2)
    (hM : ∀ s ∈ T, s.length ≤ M) : (blist T).length ≤ 1 + (sd + 1) ^ 2 * (2 * M + 2) :=
  (length_blist_le' hM).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hT) _)

theorem length_recM_le {B : ℕ} (hB : DomNamesLt d B) {k j : ℕ} (hk : k ∈ mIdx d)
    (hj : j = 0 ∨ j ∈ (methodAt d k).2.ids) : (recM d (k, j)).length ≤ rowBound d.size B := by
  rw [← recOf_eq_recM (q := emptyInst) (mIdx_ne_zero hk)]
  have := length_recOf_le hB.namesLt (z := (k, j)) (by
    simp only [allSteps, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons]
    exact Or.inr ⟨k, hk, j, hj, rfl⟩)
  unfold rowBound; omega

/-- **The advice is short.** -/
theorem length_advOf_le {B : ℕ} (hB : DomNamesLt d B) :
    (advOf d).length ≤ advBound d.size B := by
  have hsz : d.size ≤ (d.size + 1) ^ 2 := by nlinarith
  have hkB : ∀ k ∈ mIdx d, k < 2 ^ B := fun k hk => by
    have := mem_mIdx.1 hk; have := hB.meth; omega
  have hmeth : ∀ k ∈ mIdx d, ∀ x ∈ (methodAt d k).2.names, x < 2 ^ B :=
    fun k hk => methodAt_names_lt hB.namesLt hk
  -- the five tables
  have h1 : (blist (mstepT d)).length ≤ 1 + (d.size + 1) ^ 2 * (2 * rowBound d.size B + 2) := by
    refine length_table_le ?_ ?_
    · simp only [mstepT, List.length_flatMap, List.length_map]
      exact (sum_ids_le d).trans hsz
    · intro s hs
      simp only [mstepT, List.mem_flatMap, List.mem_map] at hs
      obtain ⟨k, hk, j, hj, rfl⟩ := hs
      exact length_recM_le hB hk (Or.inr hj)
  have h2 : (blist (dummyT d)).length ≤ 1 + (d.size + 1) ^ 2 * (2 * rowBound d.size B + 2) := by
    refine length_table_le ?_ ?_
    · simp only [dummyT, List.length_map]
      refine (List.length_filter_le _ _).trans ?_
      simp only [mIdx, List.length_map, List.length_range]
      exact (length_methods_le d).trans hsz
    · intro s hs
      simp only [dummyT, List.mem_map, List.mem_filter] at hs
      obtain ⟨k, ⟨hk, -⟩, rfl⟩ := hs
      exact length_recM_le hB hk (Or.inl rfl)
  have h3 : (blist (headT d)).length ≤ 1 + (d.size + 1) ^ 2 * (2 * rowBound d.size B + 2) := by
    refine length_table_le ?_ ?_
    · simp only [headT, mIdx, List.length_map, List.length_range]
      exact (length_methods_le d).trans hsz
    · intro s hs
      simp only [headT, List.mem_map] at hs
      obtain ⟨k, hk, rfl⟩ := hs
      have hhead : (methodAt d k).1 < 2 ^ B := by
        have := mem_mIdx.1 hk
        exact hB.dom _ (DomDesc.method_names_subset (methodAt_mem (k := k) this.2) _
          (by simp [MethodDesc.names]))
      have := length_serNat_le_of_lt (hkB k hk)
      have := length_serNat_le_of_lt hhead
      simp only [List.length_append]
      unfold rowBound; omega
  have h4 : (blist (ordT d)).length ≤ 1 + (d.size + 1) ^ 2 * (2 * rowBound d.size B + 2) := by
    refine length_table_le ?_ ?_
    · simp only [ordT, List.length_flatMap, List.length_map]
      have : ∀ k ∈ mIdx d, ((((methodAt d k).2.ids ×ˢ (methodAt d k).2.ids).filter fun p =>
          decide ((methodAt d k).2.ordOf p.1 p.2))).length ≤
          d.size * (methodAt d k).2.ids.length := by
        intro k hk
        refine (List.length_filter_le _ _).trans ?_
        rw [List.length_product]
        exact Nat.mul_le_mul_right _ (ids_le_size hk)
      refine (List.sum_le_sum this).trans ?_
      rw [List.sum_map_mul_left]
      have := sum_ids_le d
      nlinarith
    · intro s hs
      simp only [ordT, List.mem_flatMap, List.mem_map, List.mem_filter] at hs
      obtain ⟨k, hk, p, ⟨hp, -⟩, rfl⟩ := hs
      obtain ⟨hp1, hp2⟩ := List.mem_product.1 hp
      have := length_serNat_le_of_lt (hkB k hk)
      have := length_serNat_le_of_lt (hmeth k hk p.1 ((methodAt d k).2.ids_subset_names _ hp1))
      have := length_serNat_le_of_lt (hmeth k hk p.2 ((methodAt d k).2.ids_subset_names _ hp2))
      simp only [List.length_append]
      unfold rowBound; omega
  have h5 : (blist (actT d)).length ≤ 1 + (d.size + 1) ^ 2 * (2 * rowBound d.size B + 2) := by
    refine length_table_le ?_ ?_
    · simp only [actT, List.length_map]
      exact (length_actions_le d).trans hsz
    · intro s hs
      simp only [actT, List.mem_map] at hs
      obtain ⟨a, ⟨x, hx, rfl⟩, rfl⟩ := hs
      have ha : x.1 < 2 ^ B := hB.dom _ (DomDesc.action_names_subset hx _
        (by simp [ActionDesc.names]))
      have := length_serNat_le_of_lt ha
      have hp := length_actS_le hB.namesLt (l := (actLists d x.1).1) (a := x.1) (Or.inl rfl)
      have hd := length_actS_le hB.namesLt (l := (actLists d x.1).2.1) (a := x.1)
        (Or.inr (Or.inl rfl))
      have hdl := length_actS_le hB.namesLt (l := (actLists d x.1).2.2) (a := x.1)
        (Or.inr (Or.inr rfl))
      simp only [actSer, List.length_append]
      unfold rowBound; omega
  unfold advOf advBound
  simp only [List.length_append]
  omega

theorem advBound_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    advBound a b ≤ advBound a' b' := by
  unfold advBound rowBound
  gcongr

end AcVer

end Syn

end HTN
