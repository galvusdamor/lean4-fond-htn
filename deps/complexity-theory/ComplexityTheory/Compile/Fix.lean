import ComplexityTheory.Collapse.Alt
/-!
# The acceptance of an alternating machine is reached at the horizon

`HTN.PSpace.ASpace.L` reads acceptance off at the *horizon* `2 ^ (w + 1) - 1`, while a machine
that simulates the same computation accepts exactly when *some* finite number of rounds
suffices.  The two agree, because the sets

    A t = { c : |c| = w and `M.accWithin x t c` }

increase with `t` and live inside the `2 ^ w` strings of width `w`: once the sequence stops
growing it is constant, so it is constant from `2 ^ w` on, and the horizon is beyond that.

* `HTN.PSpace.ASpace.accWithin_horizon` — a configuration of width `w` that accepts within some
  number of rounds accepts within the horizon;
* `HTN.PSpace.ASpace.L_iff_exists` — the language, read as "some finite computation accepts".
-/

namespace HTN

namespace PSpace

/-- There are `2 ^ m` strings of length `m`. -/
theorem length_allLen (m : ℕ) : (allLen m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [allLen, List.length_flatMap]
    simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate,
      smul_eq_mul, ih]
    ring

/-- Two tests that agree on the members of a list give the same universal answer. -/
private theorem all_congr_mem : ∀ {l : List (List Bool)} {f g : List Bool → Bool},
    (∀ a ∈ l, f a = g a) → l.all f = l.all g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_congr_mem fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- Two tests that agree on the members of a list give the same existential answer. -/
private theorem any_congr_mem : ∀ {l : List (List Bool)} {f g : List Bool → Bool},
    (∀ a ∈ l, f a = g a) → l.any f = l.any g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr_mem fun b hb => h b (List.mem_cons_of_mem _ hb)]

namespace ASpace

variable (M : ASpace)

/-- The configurations of the machine's width accepting within `t` rounds. -/
private noncomputable def accSet (x : List Bool) (t : ℕ) : Finset (List Bool) :=
  (allLen (M.w x)).toFinset.filter fun c => M.accWithin x t c = true

private theorem accSet_subset (x : List Bool) (t : ℕ) : M.accSet x t ⊆ M.accSet x (t + 1) := by
  intro c hc
  rw [accSet, Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, M.accWithin_succ_of x t c hc.2⟩

private theorem card_accSet_le (x : List Bool) (t : ℕ) :
    (M.accSet x t).card ≤ 2 ^ M.w x := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  refine le_trans (List.toFinset_card_le _) ?_
  rw [length_allLen]

/-- One round of stability at the machine's width is stability for ever. -/
private theorem accWithin_stable {x : List Bool} {t : ℕ}
    (h : ∀ c, c.length = M.w x → M.accWithin x (t + 1) c = M.accWithin x t c) :
    ∀ s, t ≤ s → ∀ c, c.length = M.w x → M.accWithin x s c = M.accWithin x t c := by
  have gen : ∀ s : ℕ, (∀ c : List Bool, c.length = M.w x →
        M.accWithin x (s + 1) c = M.accWithin x s c) →
      ∀ c : List Bool, M.accWithin x (s + 1 + 1) c = M.accWithin x (s + 1) c := by
    intro s hs c
    rw [accWithin_succ, accWithin_succ]
    have e1 : (allLenB (M.w x) fun c' => !M.stepB [c', c, x] || M.accWithin x (s + 1) c')
        = (allLenB (M.w x) fun c' => !M.stepB [c', c, x] || M.accWithin x s c') := by
      refine all_congr_mem fun y hy => ?_
      rw [hs y ((mem_allLen _ _).1 hy)]
    have e2 : (anyLen (M.w x) fun c' => M.stepB [c', c, x] && M.accWithin x (s + 1) c')
        = (anyLen (M.w x) fun c' => M.stepB [c', c, x] && M.accWithin x s c') := by
      refine any_congr_mem fun y hy => ?_
      rw [hs y ((mem_allLen _ _).1 hy)]
    rw [e1, e2]
  have key : ∀ d, ∀ c, c.length = M.w x →
      M.accWithin x (t + d + 1) c = M.accWithin x (t + d) c := by
    intro d
    induction d with
    | zero => simpa using h
    | succ d ih =>
      intro c _
      have hgen := gen (t + d) ih c
      rw [show t + (d + 1) + 1 = (t + d + 1) + 1 by omega, show t + (d + 1) = t + d + 1 by omega]
      exact hgen
  intro s hs c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  clear hs
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show t + (d + 1) = (t + d) + 1 by omega, key d c hc]
    exact ih

/-- **The sequence of accepting sets is constant from `2 ^ w` on.** -/
private theorem exists_stable (x : List Bool) :
    ∃ t ≤ 2 ^ M.w x, ∀ c, c.length = M.w x →
      M.accWithin x (t + 1) c = M.accWithin x t c := by
  by_contra hcon
  push_neg at hcon
  have hne : ∀ t ≤ 2 ^ M.w x, M.accSet x t ≠ M.accSet x (t + 1) := by
    intro t ht heq
    obtain ⟨c, hc, hne⟩ := hcon t ht
    have h1 : M.accWithin x (t + 1) c = true ↔ M.accWithin x t c = true := by
      constructor
      · intro h
        have : c ∈ M.accSet x (t + 1) := by
          rw [accSet, Finset.mem_filter]
          exact ⟨List.mem_toFinset.2 ((mem_allLen _ _).2 hc), h⟩
        rw [← heq, accSet, Finset.mem_filter] at this
        exact this.2
      · exact M.accWithin_succ_of x t c
    rcases Bool.eq_false_or_eq_true (M.accWithin x t c) with h0 | h0 <;>
      rcases Bool.eq_false_or_eq_true (M.accWithin x (t + 1) c) with h1' | h1' <;>
      simp_all
  have hgrow : ∀ t ≤ 2 ^ M.w x + 1, t ≤ (M.accSet x t).card := by
    intro t
    induction t with
    | zero => intro _; exact Nat.zero_le _
    | succ t ih =>
      intro ht
      have h1 : t ≤ (M.accSet x t).card := ih (by omega)
      have h2 : M.accSet x t ⊂ M.accSet x (t + 1) :=
        lt_of_le_of_ne (M.accSet_subset x t) (hne t (by omega))
      have := Finset.card_lt_card h2
      omega
  have h1 := hgrow (2 ^ M.w x + 1) le_rfl
  have h2 := M.card_accSet_le x (2 ^ M.w x + 1)
  omega

/-- **A configuration of the machine's width that accepts at all accepts within the
horizon.** -/
theorem accWithin_horizon {x c : List Bool} (hc : c.length = M.w x) {t : ℕ}
    (h : M.accWithin x t c = true) : M.accWithin x (M.horizon x) c = true := by
  obtain ⟨t₀, ht₀, hstab⟩ := M.exists_stable x
  have hhor : t₀ ≤ M.horizon x := by
    have h1 : 2 ^ M.w x ≤ 2 ^ (M.w x + 1) - 1 := by
      have : 2 ^ (M.w x + 1) = 2 * 2 ^ M.w x := by ring
      have hpos : 0 < 2 ^ M.w x := Nat.two_pow_pos _
      omega
    exact le_trans ht₀ (by rw [horizon]; exact h1)
  rcases Nat.le_total t (M.horizon x) with hle | hle
  · exact M.accWithin_mono x c hle h
  · have e1 := M.accWithin_stable hstab t (le_trans hhor hle) c hc
    have e2 := M.accWithin_stable hstab (M.horizon x) hhor c hc
    rw [e1] at h
    rw [e2]
    exact h

/-- **The language of the machine**, as "some finite computation accepts". -/
theorem L_iff_exists (x : List Bool) :
    M.L x ↔ ∃ t, M.accWithin x t (M.initF [x]) = true := by
  constructor
  · intro h
    exact ⟨M.horizon x, h⟩
  · rintro ⟨t, ht⟩
    exact M.accWithin_horizon (c := M.initF [x]) (M.initF_length x) ht

end ASpace

end PSpace

end HTN
