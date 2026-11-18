import HtnComplexity.SpaceEnc.RenderTR
/-!
# The size of the rendered encoding

`HTN.SpaceEnc.size_domDesc_rend_le`: the domain description of the encoding has size at most
`3 B · C + 10 B`, where `B = 2 n' + 16 m + 2 |Γ| + 3 |Q|² |Γ|² + |Q| + 30` bounds the number
of methods and `C = 3 m + |Γ| + 21` bounds the size of a single action.  So for `m = p(n)` and
`n' = n` the domain descriptions are of polynomial size.
-/

namespace HTN

namespace SpaceEnc

open TM Syn

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] (m n' : ℕ) (ι : Bool → Γ) (N : NTM Q Γ)

/-- The size of the description of a single action. -/
noncomputable def aLen (a : Act Q Γ) : ℕ :=
  1 + (precL m n' a).length + (addL m ι N a).length + (delL m a).length

/-- The counter indices of the actions occurring in the methods are at most `m`. -/
def SmallIdx (m : ℕ) : Act Q Γ → Prop
  | .inc _ k => k ≤ m
  | .hinc _ k => k ≤ m
  | .hdec _ k => k ≤ m
  | _ => True

omit [Fintype Q] in
theorem length_symFacts : (symFacts (Q := Q) (Γ := Γ)).length = Fintype.card Γ := by
  simp [symFacts]

omit [Fintype Q] in
theorem aLen_le {a : Act Q Γ} (h : SmallIdx m a) : aLen m n' ι N a ≤ 3 * m + Fintype.card Γ + 21 := by
  cases a <;> simp [aLen, precL, addL, delL, SmallIdx, length_symFacts] at h ⊢ <;>
    first | omega | (split_ifs <;> simp)

/-- Every method body has at most three cells, and its actions have small indices. -/
theorem bodies_ok : ∀ b ∈ bodies m n' N,
    (b.2.map List.length).sum ≤ 3 ∧ ∀ a, Sum.inl a ∈ b.2.flatten → SmallIdx m a := by
  simp only [bodies, bodiesP, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.forall_mem_flatMap, List.mem_range]
  simp [SmallIdx]
  exact fun j hj => hj.le

theorem length_transL_le : (transL N).length ≤ 3 * (Fintype.card Q ^ 2 * Fintype.card Γ ^ 2) := by
  unfold transL
  refine (List.length_filter_le _ _).trans ?_
  simp [List.length_flatMap, allMoves]
  ring_nf; rfl

omit [Fintype Γ] in
theorem length_accL_le : (accL N).length ≤ Fintype.card Q := by
  unfold accL
  exact (List.length_filter_le _ _).trans (by simp)

/-- The number of methods. -/
noncomputable def bodiesBound (Q Γ : Type) [Fintype Q] [Fintype Γ] (m n' : ℕ) : ℕ :=
  2 * n' + 16 * m + 2 * Fintype.card Γ + 6 * (Fintype.card Q ^ 2 * Fintype.card Γ ^ 2) +
    Fintype.card Q + 30

theorem length_bodies_le : (bodies m n' N).length ≤ bodiesBound Q Γ m n' := by
  have h1 := length_transL_le N
  have h2 := length_accL_le N
  simp only [bodies, bodiesP, List.length_flatMap, List.length_append, List.length_cons,
    List.length_nil, List.length_map, List.length_range, Finset.length_toList, Finset.card_univ,
    List.map_const', List.sum_replicate, smul_eq_mul, bodiesBound]
  generalize Fintype.card Q ^ 2 * Fintype.card Γ ^ 2 = c at h1 ⊢
  norm_num
  omega

theorem smallIdx_of_mem_actsL {a : Act Q Γ} (ha : a ∈ actsL m n' N) : SmallIdx m a := by
  simp only [actsL, List.mem_flatMap, List.mem_filterMap] at ha
  obtain ⟨b, hb, x, hx, hxa⟩ := ha
  have : x = Sum.inl a := by
    cases x with
    | inl y => simp at hxa; rw [hxa]
    | inr y => simp at hxa
  subst this
  exact (bodies_ok m n' N b hb).2 a hx

theorem length_actsL_le : (actsL m n' N).length ≤ 3 * (bodies m n' N).length := by
  unfold actsL
  rw [List.length_flatMap]
  have := List.sum_le_card_nsmul ((bodies m n' N).map fun b =>
    (b.2.flatten.filterMap fun x => x.getLeft?).length) 3 (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      refine (List.length_filterMap_le _ _).trans ?_
      rw [List.length_flatten]
      exact (bodies_ok m n' N b hb).1)
  simp only [List.length_map, smul_eq_mul] at this
  omega

/-- **The size of the domain description of the encoding.** -/
theorem size_domDesc_rend_le (n : ℕ) (w : List Bool) :
    (rend m n' ι N n w).domDesc.size ≤
      3 * bodiesBound Q Γ m n' * (3 * m + Fintype.card Γ + 21) + 10 * bodiesBound Q Γ m n' := by
  set R := rend m n' ι N n w with hR
  have h := R.size_domDesc_le
  have hB := length_bodies_le m n' N
  have hA := length_actsL_le m n' N
  have h1 : (R.acts.map fun o => 1 + (R.precL o).length + (R.addL o).length +
      (R.delL o).length).sum ≤ (actsL m n' N).length * (3 * m + Fintype.card Γ + 21) := by
    have := List.sum_le_card_nsmul (R.acts.map fun o => 1 + (R.precL o).length +
      (R.addL o).length + (R.delL o).length) (3 * m + Fintype.card Γ + 21) (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact aLen_le m n' ι N (smallIdx_of_mem_actsL m n' N ha))
    simpa [hR, rend] using this
  have h2 : (R.bodies.map fun p => 1 + 3 * p.2.cells + p.2.after).sum ≤
      (bodies m n' N).length * 10 := by
    have := List.sum_le_card_nsmul (R.bodies.map fun p => 1 + 3 * p.2.cells + p.2.after) 10 (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        simp only [hR, rend, List.mem_map] at hp
        obtain ⟨b, hb, rfl⟩ := hp
        have := (bodies_ok m n' N b hb).1
        simp only [Shape.cells]
        omega)
    simpa [hR, rend] using this
  have h3 : (actsL m n' N).length * (3 * m + Fintype.card Γ + 21) ≤
      3 * bodiesBound Q Γ m n' * (3 * m + Fintype.card Γ + 21) :=
    Nat.mul_le_mul_right _ (hA.trans (by omega))
  omega

end SpaceEnc

end HTN
