import ComplexityTheory.Savitch.State
/-!
# The depth-first search computes Savitch's recursion

This file proves the correctness of the search of `ComplexityTheory/Savitch/State.lean`: from
the state that calls the recursion at level `k` on a pair `(u, v)`, the machine reaches, in at
most `HTN.Savitch.cost E k` steps, the state that returns `HTN.Savitch.Rec stp E k u v` to the
caller, leaving the rest of the stack untouched (`HTN.Savitch.dfs_correct`).

The proof is an induction on the level, inside which the enumeration of the midpoints is handled
by a second, downward induction on the number of midpoints left to try.  The value a frame
returns once the midpoints from `m` on have been tried is `HTN.Savitch.orFrom`, and the two
inductions meet in `HTN.Savitch.orFrom_zero`: trying every midpoint is the recursion one level
up.
-/

namespace HTN

namespace Savitch

open PTime PSpace

/-! ### The level of a frame -/

/-- **The frame on top of `st` is at level `k`**: the stack below it is exactly `K - k` frames
tall, so that the bottom of the recursion — where the value is read off the one-step test — is
recognised by the stack below being `K` frames tall. -/
def AtLevel (E K k : ℕ) (st : List Bool) : Prop := st.length + k * frW E = K * frW E

theorem AtLevel.push {E K k : ℕ} {st fr : List Bool} (h : AtLevel E K (k + 1) st)
    (hfr : fr.length = frW E) : AtLevel E K k (fr ++ st) := by
  simp only [AtLevel, List.length_append, hfr, Nat.succ_mul] at h ⊢
  omega

/-- Above the bottom of the recursion there is room for one more frame. -/
theorem AtLevel.room {E K k : ℕ} {st : List Bool} (h : AtLevel E K (k + 1) st) :
    st.length + frW E ≤ K * frW E := by
  simp only [AtLevel, Nat.succ_mul] at h
  omega

/-- At the bottom of the recursion there is no room for another frame. -/
theorem AtLevel.no_room {E K : ℕ} {st : List Bool} (h : AtLevel E K 0 st) :
    ¬ (st.length + frW E ≤ K * frW E) := by
  simp only [AtLevel, Nat.zero_mul, Nat.add_zero] at h
  have hp := frW_pos E
  omega

/-! ### The value a frame still has to compute -/

/-- **The disjunction over the midpoints not yet tried**: the value a frame returns once the
midpoints of value below `i` have been tried and failed. -/
def orFrom (stp : List Bool → List Bool → Bool) (E k : ℕ) (u v : List Bool) (i : ℕ) : Bool :=
  anyLen E (fun m => decide (i ≤ val m) && Rec stp E k u m && Rec stp E k m v)

variable {stp : List Bool → List Bool → Bool} {E : ℕ}

theorem orFrom_eq_true {k i : ℕ} {u v : List Bool} :
    orFrom stp E k u v i = true ↔ ∃ m : List Bool, m.length = E ∧ i ≤ val m ∧
      Rec stp E k u m = true ∧ Rec stp E k m v = true := by
  rw [orFrom, anyLen_eq_true]
  constructor
  · rintro ⟨m, hm, hmv⟩
    rcases Bool.and_eq_true_iff.1 hmv with ⟨h₁, h₂⟩
    rcases Bool.and_eq_true_iff.1 h₁ with ⟨hi, h₃⟩
    exact ⟨m, hm, by simpa using hi, h₃, h₂⟩
  · rintro ⟨m, hm, hi, h₁, h₂⟩
    exact ⟨m, hm, by simp [hi, h₁, h₂]⟩

theorem orFrom_eq_false {k i : ℕ} {u v : List Bool} :
    orFrom stp E k u v i = false ↔ ¬ ∃ m : List Bool, m.length = E ∧ i ≤ val m ∧
      Rec stp E k u m = true ∧ Rec stp E k m v = true := by
  rw [← Bool.not_eq_true, orFrom_eq_true]

/-- Trying every midpoint is the recursion one level up. -/
theorem orFrom_zero (k : ℕ) (u v : List Bool) :
    orFrom stp E k u v 0 = Rec stp E (k + 1) u v := by
  rw [Bool.eq_iff_iff, orFrom_eq_true, Rec_succ, anyLen_eq_true]
  constructor
  · rintro ⟨m, hm, -, h₁, h₂⟩
    exact ⟨m, hm, by rw [h₁, h₂]; rfl⟩
  · rintro ⟨m, hm, hmv⟩
    rcases Bool.and_eq_true_iff.1 hmv with ⟨h₁, h₂⟩
    exact ⟨m, hm, Nat.zero_le _, h₁, h₂⟩

/-- A midpoint that works makes the disjunction true. -/
theorem orFrom_of_true {k : ℕ} {u v m : List Bool} (hm : m.length = E)
    (h₁ : Rec stp E k u m = true) (h₂ : Rec stp E k m v = true) :
    orFrom stp E k u v (val m) = true := by
  rw [orFrom_eq_true]
  exact ⟨m, hm, le_rfl, h₁, h₂⟩

/-- A midpoint that fails may be skipped. -/
theorem orFrom_succ_of_false {k : ℕ} {u v m : List Bool} (hm : m.length = E)
    (h : (Rec stp E k u m && Rec stp E k m v) = false) :
    orFrom stp E k u v (val m) = orFrom stp E k u v (val m + 1) := by
  rw [Bool.eq_iff_iff, orFrom_eq_true, orFrom_eq_true]
  constructor
  · rintro ⟨m', hm', hle, h₁, h₂⟩
    rcases Nat.lt_or_ge (val m) (val m') with hlt | hge
    · exact ⟨m', hm', by omega, h₁, h₂⟩
    · have hval : val m' = val m := by omega
      have hmm : m' = m := val_inj_of_length_eq _ _ (by rw [hm', hm]) hval
      subst hmm
      rw [h₁, h₂] at h
      simp at h
  · rintro ⟨m', hm', hle, h₁, h₂⟩
    exact ⟨m', hm', by omega, h₁, h₂⟩

/-- Once the last midpoint has failed, the disjunction is false. -/
theorem orFrom_last {k : ℕ} {u v m : List Bool} (hm : m.length = E) (hones : m = ones E)
    (h : (Rec stp E k u m && Rec stp E k m v) = false) :
    orFrom stp E k u v (val m) = false := by
  rw [orFrom_eq_false]
  rintro ⟨m', hm', hle, h₁, h₂⟩
  have hlt : val m' < 2 ^ E := by
    have hv := val_lt_two_pow m'
    rwa [hm'] at hv
  have hvm : val m = 2 ^ E - 1 := by rw [hones, ones, val_replicate_true]
  have hone : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hval : val m' = val m := by omega
  have hmm : m' = m := val_inj_of_length_eq _ _ (by rw [hm', hm]) hval
  subst hmm
  rw [h₁, h₂] at h
  simp at h

/-! ### The cost -/

/-- A bound on the number of steps the search at level `k` takes. -/
def cost (E : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (E + 3)
  | k + 1 => 2 ^ (E + 3) * cost E k

theorem one_le_cost (E k : ℕ) : 1 ≤ cost E k := by
  induction k with
  | zero => exact Nat.one_le_two_pow
  | succ k ih =>
    have h : 1 ≤ 2 ^ (E + 3) := Nat.one_le_two_pow
    rw [cost]
    calc 1 = 1 * 1 := by ring
      _ ≤ 2 ^ (E + 3) * cost E k := Nat.mul_le_mul h ih

theorem loop_bound_le (E k : ℕ) : 1 + 2 ^ E * (2 * cost E k + 2) ≤ cost E (k + 1) := by
  have hc : 1 ≤ cost E k := one_le_cost E k
  have hE : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (E + 3) = 8 * 2 ^ E := by rw [pow_add]; ring
  have h1 : 1 ≤ 2 ^ E * cost E k := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : 2 * 2 ^ E ≤ 2 * (2 ^ E * cost E k) :=
    Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ (by omega))
  rw [cost, hpow]
  calc 1 + 2 ^ E * (2 * cost E k + 2)
      = 1 + 2 * (2 ^ E * cost E k) + 2 * 2 ^ E := by ring
    _ ≤ 2 ^ E * cost E k + 2 * (2 ^ E * cost E k) + 2 * (2 ^ E * cost E k) := by omega
    _ ≤ 8 * 2 ^ E * cost E k := by ring_nf; omega

/-! ### The search is correct -/

/-- **The depth-first search computes the recursion.**  Started on a fresh frame for the pair
`(u, v)` at level `k`, the machine returns `Rec stp E k u v` to the caller within `cost E k`
steps, leaving the stack below untouched. -/
theorem dfs_correct (K : ℕ) :
    ∀ (k : ℕ), k ≤ K → ∀ u v st : List Bool, u.length = E → v.length = E →
      AtLevel E K k st →
      ∃ j ≤ cost E k, run E (K * frW E) stp j (callSt E u v st)
        = retSt (Rec stp E k u v) st := by
  intro k
  induction k with
  | zero =>
    intro _ u v st hu hv hst
    refine ⟨1, one_le_cost E 0, ?_⟩
    rw [run_succ, run_zero]
    rw [step_call_base hu hv hst.no_room, Rec_zero]
  | succ k ih =>
    intro hk u v st hu hv hst
    have hk' : k ≤ K := by omega
    have hzl : (zeros E).length = E := by simp
    have hcost := one_le_cost E k
    -- the loop over the midpoints
    have loop : ∀ (d : ℕ) (m : List Bool), m.length = E → 2 ^ E - val m ≤ d →
        ∃ j ≤ (2 ^ E - val m) * (2 * cost E k + 2),
          run E (K * frW E) stp j (callSt E u m (frame [true, false] u v m ++ st))
            = retSt (orFrom stp E k u v (val m)) st := by
      intro d
      induction d with
      | zero =>
        intro m hm hd
        have hlt : val m < 2 ^ E := by
          have hv' := val_lt_two_pow m
          rwa [hm] at hv'
        omega
      | succ d ihd =>
        intro m hm hd
        have hlt : val m < 2 ^ E := by
          have hv' := val_lt_two_pow m
          rwa [hm] at hv'
        have hNm : 1 ≤ 2 ^ E - val m := by omega
        have hsplit : (2 ^ E - val m) * (2 * cost E k + 2)
            = (2 * cost E k + 2) + (2 ^ E - val m - 1) * (2 * cost E k + 2) := by
          obtain ⟨t, htN⟩ : ∃ t, 2 ^ E - val m = t + 1 := ⟨2 ^ E - val m - 1, by omega⟩
          rw [htN]
          simp only [Nat.add_sub_cancel]
          ring
        have hfrl : (frame [true, false] u v m).length = frW E := length_frame rfl hu hv hm
        have hst' : AtLevel E K k (frame [true, false] u v m ++ st) := hst.push hfrl
        -- the advance to the next midpoint, shared by the two failing cases
        have advance : ∀ (jpre : ℕ) (ph : List Bool),
            step E (K * frW E) stp (retSt false (frame ph u v m ++ st))
              = (if m = ones E then retSt false st
                  else callSt E u (succB m) (frame [true, false] u v (succB m) ++ st)) →
            run E (K * frW E) stp jpre (callSt E u m (frame [true, false] u v m ++ st))
              = retSt false (frame ph u v m ++ st) →
            (Rec stp E k u m && Rec stp E k m v) = false →
            ∃ j ≤ jpre + 1 + (2 ^ E - val m - 1) * (2 * cost E k + 2),
              run E (K * frW E) stp j (callSt E u m (frame [true, false] u v m ++ st))
                = retSt (orFrom stp E k u v (val m)) st := by
          intro jpre ph hstep hpre hfalse
          by_cases hones : m = ones E
          · refine ⟨jpre + 1, by omega, ?_⟩
            rw [run_add, hpre, run_succ, run_zero, hstep, if_pos hones,
              orFrom_last hm hones hfalse]
          · have hvne : val m ≠ 2 ^ E - 1 := by
              intro hcon
              refine hones (val_inj_of_length_eq _ _ (by simp [hm]) ?_)
              rw [ones, val_replicate_true, hcon]
            have hvsucc : val (succB m) = val m + 1 := by
              rw [val_succB, hm, Nat.mod_eq_of_lt (by omega)]
            have hsl : (succB m).length = E := by rw [length_succB, hm]
            obtain ⟨j₂, hj₂, hrun₂⟩ := ihd (succB m) hsl (by omega)
            have hj₂' : j₂ ≤ (2 ^ E - val m - 1) * (2 * cost E k + 2) := by
              have heq : 2 ^ E - val (succB m) = 2 ^ E - val m - 1 := by omega
              rwa [heq] at hj₂
            refine ⟨jpre + 1 + j₂, by omega, ?_⟩
            rw [run_add, run_add, hpre, run_succ, run_zero, hstep, if_neg hones, hrun₂,
              hvsucc, ← orFrom_succ_of_false hm hfalse]
        -- the first child
        obtain ⟨j₁, hj₁, hrun₁⟩ := ih hk' u m (frame [true, false] u v m ++ st) hu hm hst'
        rcases hb₁ : Rec stp E k u m with _ | _
        · -- it failed: advance
          have hfalse : (Rec stp E k u m && Rec stp E k m v) = false := by rw [hb₁]; rfl
          obtain ⟨j, hj, hrun⟩ := advance j₁ [true, false]
            (step_ret_first_false hu hv hm hst.room) (by rw [hrun₁, hb₁]) hfalse
          exact ⟨j, by omega, hrun⟩
        · -- it succeeded: call the second child
          have hafter : run E (K * frW E) stp (j₁ + 1)
              (callSt E u m (frame [true, false] u v m ++ st))
              = callSt E m v (frame [false, true] u v m ++ st) := by
            rw [run_add, hrun₁, hb₁, run_succ, run_zero, step_ret_first_true hu hv hm hst.room]
          have hfrl₂ : (frame [false, true] u v m).length = frW E := length_frame rfl hu hv hm
          have hst₂ : AtLevel E K k (frame [false, true] u v m ++ st) := hst.push hfrl₂
          obtain ⟨j₂, hj₂, hrun₂⟩ := ih hk' m v (frame [false, true] u v m ++ st) hm hv hst₂
          have hstate₂ : run E (K * frW E) stp (j₁ + 1 + j₂)
              (callSt E u m (frame [true, false] u v m ++ st))
              = retSt (Rec stp E k m v) (frame [false, true] u v m ++ st) := by
            rw [run_add, hafter, hrun₂]
          rcases hb₂ : Rec stp E k m v with _ | _
          · -- the second child failed: advance
            have hfalse : (Rec stp E k u m && Rec stp E k m v) = false := by rw [hb₂]; simp
            obtain ⟨j, hj, hrun⟩ := advance (j₁ + 1 + j₂) [false, true]
              (step_ret_second_false hu hv hm hst.room) (by rw [hstate₂, hb₂]) hfalse
            exact ⟨j, by omega, hrun⟩
          · -- both children succeeded
            refine ⟨j₁ + 1 + j₂ + 1, by omega, ?_⟩
            rw [run_add, hstate₂, hb₂, run_succ, run_zero, step_ret_second_true hu hv hm,
              orFrom_of_true hm hb₁ hb₂]
    -- the search starts by pushing the child for the midpoint `0…0`
    have hfirst : run E (K * frW E) stp 1 (callSt E u v st)
        = callSt E u (zeros E) (frame [true, false] u v (zeros E) ++ st) := by
      rw [run_succ, run_zero, step_call_push hu hv hst.room]
    obtain ⟨j, hj, hrun⟩ := loop (2 ^ E) (zeros E) hzl (by simp)
    have hjz : j ≤ 2 ^ E * (2 * cost E k + 2) := by simpa using hj
    refine ⟨1 + j, ?_, ?_⟩
    · have hb := loop_bound_le E k
      omega
    · rw [run_add, hfirst, hrun]
      simp only [val_zeros]
      rw [orFrom_zero]

end Savitch

end HTN
