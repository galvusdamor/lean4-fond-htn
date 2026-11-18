import ComplexityTheory.Complexity.PrimDiag.Diag
/-!
# The diagonal language restricted by an eventually true side condition

`not_inNTowPoly_restrict` — for any condition `S c n` on candidates and lengths that holds for
all large `n` (each `c`), the language `x ↦ S (cand |x|) |x| ∧ dg x` is in no `InNTowPoly j`:
the length reserved for a candidate can be taken as large as needed.
-/

namespace HTN.PrimDiag

open HTN.PTime HTN.PTime.CobhamTM HTN.PTime.CobhamTM.Prog

/-- **The restricted diagonal language is in no `InNTowPoly j`.** -/
theorem not_inNTowPoly_restrict (S : Cand → ℕ → Prop) (hS : ∀ c, ∃ N, ∀ n ≥ N, S c n) (j : ℕ) :
    ¬ InNTowPoly j (fun x => S (cand x.length) x.length ∧ dg x = true) := by
  rintro ⟨V, p, r, adv, hV, hadv, hcorr⟩
  obtain ⟨C, M, A, m₁, hm₁, hU⟩ := exists_uevalB hV
  obtain ⟨m₂, hm₂, hr⟩ := exists_powSelf_bound r
  obtain ⟨pc, hpc⟩ := exists_polyL p
  let c : Cand := ((C, M, A), (m₁ + m₂, j, pc))
  obtain ⟨N₀, hN₀⟩ := exists_large (m₁ + m₂)
  obtain ⟨N₁, hN₁⟩ := hS c
  let N := max N₀ N₁
  let n := Nat.pair (Encodable.encode c) N
  have hn : N ≤ n := Nat.right_le_pair _ _
  have hcand : cand n = c := by simp [cand, n, Nat.unpair_pair, Encodable.encodek]
  have hSn : S (cand n) n := by rw [hcand]; exact hN₁ n (le_trans (le_max_right _ _) hn)
  have hcorr' : ∀ x : List Bool, x.length = n → (dg x = true ↔ ∃ w : List Bool,
      w.length ≤ tow j (p.eval x.length) ∧ V [x, adv x.length, w] = true) := by
    intro x hx
    rw [← hcorr x]
    simp only [hx]
    exact ⟨fun h => ⟨hSn, h⟩, fun h => h.2⟩
  have hK : Rc c n + 1 ≤ 2 ^ n := hN₀ n (le_trans (le_max_left _ _) hn)
  have hVc : ∀ args, Vc c args = V args := fun args =>
    hU args _ (pow_bound_mono (m' := m₁ + m₂) hm₁ (by omega))
  have hBc : Bc c n = tow j (p.eval n) := by simp [Bc, c, hpc]
  have hg : ∀ y : List Bool, y.length = n → (gc c n (adv n) y = true ↔ dg y = true) := by
    intro y hy
    rw [gc, anyB_eq_true, hcorr' y hy, hy]
    constructor
    · rintro ⟨w, hw, hwV⟩
      exact ⟨w, by rw [← hBc]; exact mem_upTo.1 hw, by rw [← hVc]; exact hwV⟩
    · rintro ⟨w, hw, hwV⟩
      exact ⟨w, mem_upTo.2 (by rw [hBc]; exact hw), by rw [hVc]; exact hwV⟩
  have hdg : ∀ i < Rc c n + 1, dg (padW n i) = bitB (fstar c n) i := by
    intro i hi
    have hi' : i < 2 ^ n := lt_of_lt_of_le hi hK
    simp [dg, length_padW, hcand, nob_padW, Nat.mod_eq_of_lt hi', hi]
  obtain ⟨-, hfalse⟩ := findF_spec (exists_not_realized c n)
  have hadvR : (adv n).length ≤ Rc c n :=
    calc (adv n).length ≤ r.eval n := hadv n
      _ ≤ (n + m₂) ^ m₂ := hr n
      _ ≤ (n + (m₁ + m₂)) ^ (m₁ + m₂) := pow_bound_mono hm₂ (by omega)
  have htrue : realizedB c n (fstar c n) = true := by
    rw [realizedB, anyB_eq_true]
    refine ⟨adv n, mem_upTo.2 hadvR, allB_eq_true.2 fun i hi => ?_⟩
    rw [List.mem_range] at hi
    rw [cond_not_eq_true, ← hdg i hi]
    exact Bool.eq_iff_iff.2 (hg _ (length_padW n i)).symm
  rw [fstar] at htrue
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

end HTN.PrimDiag
