import Mathlib

/-!
# Permutations that fix a finite set and compress another one

The counting argument of `HtnComplexity/Complexity/AdviceCount.lean` needs to replace a
description by one whose names come from a **pool fixed in advance**, without changing how it
interacts with a given finite family of instances.  The tool is a permutation of `ℕ` that

* fixes every name the instances use, so the instances themselves are unchanged, and
* maps every name of the description into the pool.

`HTN.exists_perm_fixing` builds it: if `B` is a list of distinct names avoiding `S` and at
least as long as `Y`, then some permutation of `ℕ` fixes `S` pointwise and maps `Y` into
`S ++ B`.  `HTN.freshBlock` is the concrete choice of `B` used in practice — the `k` numbers
just above everything in `S`.
-/

namespace HTN

/-- The `k` names just above every name of `S`. -/
def freshBlock (S : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).map fun i => S.foldr max 0 + 1 + i

@[simp] lemma length_freshBlock (S : List ℕ) (k : ℕ) : (freshBlock S k).length = k := by
  simp [freshBlock]

/-- Every entry of a list is at most its `max`-fold. -/
lemma le_foldr_max (S : List ℕ) : ∀ x ∈ S, x ≤ S.foldr max 0 := by
  induction S with
  | nil => simp
  | cons a t ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · exact le_trans (ih x hx) (by simp)

lemma freshBlock_nodup (S : List ℕ) (k : ℕ) : (freshBlock S k).Nodup :=
  List.Nodup.map (fun a b hab => by omega) List.nodup_range

lemma freshBlock_notMem (S : List ℕ) (k : ℕ) : ∀ b ∈ freshBlock S k, b ∉ S := by
  intro b hb hbS
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
  have := le_foldr_max S _ hbS
  omega

/-- **A permutation that fixes `S` and moves `Y` into the pool `S ++ B`.** -/
theorem exists_perm_fixing (S B : List ℕ) (hB : B.Nodup) (hSB : ∀ b ∈ B, b ∉ S) :
    ∀ Y : List ℕ, Y.length ≤ B.length →
      ∃ π : Equiv.Perm ℕ, (∀ x ∈ S, π x = x) ∧ ∀ y ∈ Y, π y ∈ S ++ B := by
  intro Y
  induction Y with
  | nil => intro _; exact ⟨Equiv.refl ℕ, fun x _ => rfl, by simp⟩
  | cons y Y ih =>
    intro hlen
    simp only [List.length_cons] at hlen
    obtain ⟨π₀, hfix, hmap⟩ := ih (by omega)
    by_cases hy : π₀ y ∈ S ++ B
    · refine ⟨π₀, hfix, ?_⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact hmap z hz
    · obtain ⟨b, hbB, hbY⟩ : ∃ b ∈ B, b ∉ Y.map π₀ := by
        by_contra hcon
        push_neg at hcon
        have hsub : B.toFinset ⊆ (Y.map π₀).toFinset := fun x hx =>
          List.mem_toFinset.2 (hcon x (List.mem_toFinset.1 hx))
        have h1 : B.toFinset.card = B.length := List.toFinset_card_of_nodup hB
        have h2 := Finset.card_le_card hsub
        have h3 : (Y.map π₀).toFinset.card ≤ (Y.map π₀).length := List.toFinset_card_le _
        simp only [List.length_map] at h3
        omega
      refine ⟨π₀.trans (Equiv.swap (π₀ y) b), ?_, ?_⟩
      · intro x hx
        have hx1 : π₀ x = x := hfix x hx
        have hne1 : x ≠ π₀ y := by
          rintro rfl
          exact hy (List.mem_append_left _ hx)
        have hne2 : x ≠ b := fun h => hSB b hbB (h ▸ hx)
        simp [hx1, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
          exact List.mem_append_right _ hbB
        · have hmz := hmap z hz
          have hne1 : π₀ z ≠ π₀ y := by
            rintro h
            exact hy (h ▸ hmz)
          have hne2 : π₀ z ≠ b := fun h => hbY (h ▸ List.mem_map_of_mem hz)
          simpa [Equiv.swap_apply_of_ne_of_ne hne1 hne2] using hmz

end HTN
