import ComplexityTheory.Collapse.Alt
/-!
# Checking a claimed table of acceptance values

The advice-elimination argument brute-forces the advice, and the only thing that makes the
brute force sound is that a *candidate* can be checked.  This file is the mathematics of that
check, with no complexity theory in it: a claimed table

    Q : configuration → counter → Bool

is **consistent** when it satisfies the two local equations of `HTN.PSpace.ASpace.accWithin` —
at the counter `0…0` it is the acceptance test, and at a counter `succB t'` it is the local rule
read off the values at `t'`.  The theorem is that a consistent table *is* the table of
`accWithin` (`HTN.PSpace.consistent_eq`), by induction on the value of the counter, and that the
table of `accWithin` is consistent (`HTN.PSpace.consistent_accWithin`).

The counter is what makes this work: without it the local rule has other solutions — the
constant `true` satisfies it on every configuration with a successor — and a brute force over
advice strings would accept the wrong answer.
-/

namespace HTN

namespace PSpace

open PTime

namespace ASpace

variable (M : ASpace) (x : List Bool) (Q : List Bool → List Bool → Bool)

/-- The local rule at a configuration, read off a claimed table at the previous counter. -/
def ruleV (c t' : List Bool) : Bool :=
  M.accB [c, x] ||
    (if M.univB [c, x] = true then
        allLenB (M.w x) (fun c' => !M.stepB [c', c, x] || Q c' t')
      else anyLen (M.w x) (fun c' => M.stepB [c', c, x] && Q c' t'))

/-- A claimed table is **consistent** when it satisfies the two local equations. -/
structure Consistent : Prop where
  /-- At the counter `0…0` the table is the acceptance test. -/
  base : ∀ c, c.length = M.w x → Q c (zeros (M.w x + 1)) = M.accB [c, x]
  /-- At a counter `succB t'` the table is the local rule read off its values at `t'`. -/
  step : ∀ t', t'.length = M.w x + 1 → t' ≠ ones (M.w x + 1) →
    ∀ c, c.length = M.w x → Q c (succB t') = ruleV M x Q c t'

variable {M x Q}

theorem allLenB_congr {m : ℕ} {f g : List Bool → Bool} (h : ∀ y, y.length = m → f y = g y) :
    allLenB m f = allLenB m g := by
  rw [Bool.eq_iff_iff, allLenB_eq_true, allLenB_eq_true]
  constructor
  · intro hf y hy; rw [← h y hy]; exact hf y hy
  · intro hg y hy; rw [h y hy]; exact hg y hy

theorem anyLen_congr {m : ℕ} {f g : List Bool → Bool} (h : ∀ y, y.length = m → f y = g y) :
    anyLen m f = anyLen m g := by
  rw [Bool.eq_iff_iff, anyLen_eq_true, anyLen_eq_true]
  constructor
  · rintro ⟨y, hy, hfy⟩; exact ⟨y, hy, by rw [← h y hy]; exact hfy⟩
  · rintro ⟨y, hy, hgy⟩; exact ⟨y, hy, by rw [h y hy]; exact hgy⟩

/-- The rule only reads the table at configurations of the right width. -/
theorem ruleV_congr {Q' : List Bool → List Bool → Bool} {c t' : List Bool}
    (h : ∀ c', c'.length = M.w x → Q c' t' = Q' c' t') :
    ruleV M x Q c t' = ruleV M x Q' c t' := by
  unfold ruleV
  by_cases hu : M.univB [c, x] = true
  · rw [if_pos hu, if_pos hu]
    exact congrArg _ (allLenB_congr fun y hy => by rw [h y hy])
  · rw [if_neg hu, if_neg hu]
    exact congrArg _ (anyLen_congr fun y hy => by rw [h y hy])

/-- The unrolling of `accWithin` is the local rule of a table. -/
theorem accWithin_succ_eq_ruleV (t : ℕ) (c : List Bool) (t' : List Bool)
    (ht : val t' = t) :
    M.accWithin x (t + 1) c = ruleV M x (fun c' t'' => M.accWithin x (val t'') c') c t' := by
  rw [accWithin_succ, ruleV, ht]

/-- **A consistent table is the table of `accWithin`.** -/
theorem consistent_eq (h : Consistent M x Q) :
    ∀ (k : ℕ) (t : List Bool), val t = k → t.length = M.w x + 1 → ∀ c, c.length = M.w x →
      Q c t = M.accWithin x (val t) c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t hk ht c hc
    rcases Nat.eq_zero_or_pos (val t) with h0 | hpos
    · have hz : t = zeros (M.w x + 1) :=
        val_inj_of_length_eq _ _ (by simp [ht]) (by rw [val_zeros, h0])
      subst hz
      rw [h.base c hc, val_zeros, accWithin_zero]
    · obtain ⟨j, hj⟩ : ∃ j, val t = j + 1 := ⟨val t - 1, by omega⟩
      have hlt1 : j + 1 < 2 ^ (M.w x + 1) := by
        have hb := val_lt_two_pow t
        rw [ht] at hb
        omega
      have hlt : j < 2 ^ (M.w x + 1) := by omega
      obtain ⟨t', hlen', hval'⟩ := exists_val_eq (M.w x + 1) j hlt
      have hsucc : succB t' = t :=
        val_inj_of_length_eq _ _ (by simp [hlen', ht])
          (by rw [val_succB, hlen', hval', Nat.mod_eq_of_lt (by omega), hj])
      have hne : t' ≠ ones (M.w x + 1) := by
        intro hcon
        have h1 : val t' = 2 ^ (M.w x + 1) - 1 := by rw [hcon, val_ones]
        have hb := val_lt_two_pow t
        rw [ht] at hb
        omega
      have hstep := h.step t' hlen' hne c hc
      rw [hsucc] at hstep
      have hih : ∀ c', c'.length = M.w x →
          Q c' t' = (fun (c'' : List Bool) (t'' : List Bool) => M.accWithin x (val t'') c'')
            c' t' := by
        intro c' hc'
        exact ih j (by omega) t' hval' hlen' c' hc'
      rw [hstep, ruleV_congr (Q' := fun (c'' : List Bool) (t'' : List Bool) =>
        M.accWithin x (val t'') c'') hih, hj]
      exact (accWithin_succ_eq_ruleV (M := M) (x := x) j c t' hval').symm

/-- **The table of `accWithin` is consistent.** -/
theorem consistent_accWithin :
    Consistent M x (fun c t => M.accWithin x (val t) c) where
  base := by
    intro c _
    rw [val_zeros]
    simp
  step := by
    intro t' ht' hne c _
    have hval : val (succB t') = val t' + 1 := by
      have hlt : val t' + 1 < 2 ^ (M.w x + 1) := by
        have h1 := val_lt_two_pow t'
        rw [ht'] at h1
        have h2 : val t' ≠ 2 ^ (M.w x + 1) - 1 := by
          intro hcon
          exact hne (val_inj_of_length_eq _ _ (by simp [ht']) (by rw [hcon, val_ones]))
        omega
      rw [val_succB, ht', Nat.mod_eq_of_lt hlt]
    rw [hval]
    exact accWithin_succ_eq_ruleV (M := M) (x := x) (val t') c t' rfl

end ASpace

end PSpace

end HTN
