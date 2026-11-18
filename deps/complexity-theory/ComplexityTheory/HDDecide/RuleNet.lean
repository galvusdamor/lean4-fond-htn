import ComplexityTheory.HDDecide.Petri
/-!
# Multiset rewriting with a control state, as a Petri net

A *rule system* over control states `C` and items `P` is a list of rules `(c, o, c', N)`: in
control state `c`, consume the item `o` (if any) and switch to `c'`, producing the items `N`.
Its configurations are pairs (control state, multiset of items).  Such a system is a Petri net
with places `C ⊕ P` whose markings carry exactly one control token (`HTN.Petri.ruleNet`), and
reachability is preserved (`HTN.Petri.reach_mk_iff`).
-/

namespace HTN

namespace Petri

variable {C P : Type*} [DecidableEq C] [DecidableEq P]

/-- A rule: control state, consumed item (if any), new control state, produced items. -/
abbrev Rule (C P : Type*) : Type _ := C × Option P × C × List P

/-- The Petri net of a rule system. -/
def ruleNet (R : List (Rule C P)) : List (Trans (C ⊕ P)) :=
  R.map fun r => (Sum.inl r.1 :: r.2.1.toList.map Sum.inr, Sum.inl r.2.2.1 :: r.2.2.2.map Sum.inr)

/-- One step of a rule system. -/
def RStep (R : List (Rule C P)) (x y : C × Multiset P) : Prop :=
  ∃ r ∈ R, r.1 = x.1 ∧ (r.2.1.toList : Multiset P) ≤ x.2 ∧
    y = (r.2.2.1, x.2 - (r.2.1.toList : Multiset P) + (r.2.2.2 : Multiset P))

/-- The marking of a configuration. -/
def mk (x : C × Multiset P) : Multiset (C ⊕ P) := Sum.inl x.1 ::ₘ x.2.map Sum.inr

omit [DecidableEq C] in
theorem cons_sub_cons' {Q : Type*} [DecidableEq Q] (a : Q) (s t : Multiset Q) :
    (a ::ₘ s) - (a ::ₘ t) = s - t := by
  rw [← Multiset.singleton_add, ← Multiset.singleton_add, add_tsub_add_eq_tsub_left]

omit [DecidableEq C] [DecidableEq P] in
theorem coe_map_inr (l : List P) :
    ((l.map Sum.inr : List (C ⊕ P)) : Multiset (C ⊕ P)) = (l : Multiset P).map Sum.inr := by
  simp

theorem fire_mk_iff {R : List (Rule C P)} {x : C × Multiset P} {z : Multiset (C ⊕ P)} :
    Fire (ruleNet R) (mk x) z ↔ ∃ y, z = mk y ∧ RStep R x y := by
  obtain ⟨c, M⟩ := x
  constructor
  · rintro ⟨t, ht, hle, rfl⟩
    obtain ⟨⟨c0, o, c1, N⟩, hr, rfl⟩ := List.mem_map.1 ht
    simp only [mk] at hle ⊢
    rw [← Multiset.cons_coe, coe_map_inr] at hle
    have hc : c0 = c := by
      have hm := Multiset.mem_of_le hle (Multiset.mem_cons_self _ _)
      rcases Multiset.mem_cons.1 hm with h | h
      · exact Sum.inl_injective h
      · simp at h
    subst hc
    rw [Multiset.cons_le_cons_iff, Multiset.map_le_map_iff Sum.inr_injective] at hle
    refine ⟨(c1, M - (o.toList : Multiset P) + (N : Multiset P)), ?_, ⟨(c0, o, c1, N), hr, rfl, hle,
      ?_⟩⟩
    · rw [← Multiset.cons_coe, ← Multiset.cons_coe, coe_map_inr, coe_map_inr,
        cons_sub_cons', ← Petri.map_sub_of_le _ hle]
      simp [Multiset.map_add, -Multiset.cons_coe, Multiset.add_cons]
    · rfl
  · rintro ⟨y, rfl, ⟨c0, o, c1, N⟩, hr, hc, hle, rfl⟩
    simp only at hc hle
    subst hc
    refine ⟨_, List.mem_map_of_mem hr, ?_, ?_⟩
    · simp only [mk]
      rw [← Multiset.cons_coe, coe_map_inr, Multiset.cons_le_cons_iff,
        Multiset.map_le_map_iff Sum.inr_injective]
      exact hle
    · simp only [mk]
      rw [← Multiset.cons_coe, ← Multiset.cons_coe, coe_map_inr, coe_map_inr,
        cons_sub_cons', ← Petri.map_sub_of_le _ hle]
      simp [Multiset.map_add, -Multiset.cons_coe, Multiset.add_cons]

/-- **Reachability in a rule system is reachability in its Petri net.** -/
theorem reach_mk_iff {R : List (Rule C P)} {x y : C × Multiset P} :
    Reach (ruleNet R) (mk x) (mk y) ↔ Relation.ReflTransGen (RStep R) x y := by
  constructor
  · intro h
    have key : ∀ z, Reach (ruleNet R) (mk x) z → ∃ y', z = mk y' ∧
        Relation.ReflTransGen (RStep R) x y' := by
      intro z hz
      induction hz with
      | refl => exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hstep ih =>
        obtain ⟨y', rfl, hr⟩ := ih
        obtain ⟨y'', rfl, hs⟩ := fire_mk_iff.1 hstep
        exact ⟨y'', rfl, hr.tail hs⟩
    obtain ⟨y', he, hr⟩ := key _ h
    have : y = y' := by
      obtain ⟨c, M⟩ := y
      obtain ⟨c', M'⟩ := y'
      simp only [mk] at he
      have h1 := Multiset.mem_cons_self (Sum.inl c : C ⊕ P) (M.map Sum.inr)
      rw [he] at h1
      have hc : c = c' := by
        rcases Multiset.mem_cons.1 h1 with h | h
        · exact Sum.inl_injective h
        · simp at h
      subst hc
      rw [Multiset.cons_inj_right] at he
      rw [Multiset.map_injective Sum.inr_injective he]
    rwa [this]
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (fire_mk_iff.2 ⟨_, rfl, hstep⟩)

end Petri

end HTN
