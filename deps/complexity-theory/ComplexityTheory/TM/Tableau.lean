import ComplexityTheory.TM.Theory.Machine
/-!
# The tableau of a deterministic run

For a machine with at most one transition per state and symbol, the run on an input is a
sequence of configurations (`TM.NTM.run`, frozen once an accepting state or a configuration
without transition is reached).  Its **tableau** (`TM.NTM.tab`) records, for every time `t` and
cell `i`, the symbol of the cell and — if the head is there — the state.

* `TM.NTM.tab_succ` — **the local rule**: the entry at `(t + 1, i)` is a fixed function
  `TM.NTM.F` of the entries at `(t, i - 1)` (or the left border), `(t, i)` and `(t, i + 1)`;
* `TM.NTM.tab_zero` — the first row is the input, with the head on cell `0` in the initial state;
* `TM.NTM.acceptsWithin_iff_run` — a deterministic machine accepts within `T` steps iff the
  configuration at time `T` is accepting.
-/

namespace TM

namespace NTM

open Classical

variable {Q Γ : Type*} (M : NTM Q Γ)

/-- **The transition taken** in state `q` reading `γ`: none in an accepting state or without
transition. -/
noncomputable def act (q : Q) (γ : Γ) : Option (Q × Γ × Move) :=
  if q ∈ M.accept then none else if h : (M.step q γ).Nonempty then some h.some else none

/-- **One step of the deterministic run** (the configuration is kept if no step is taken). -/
noncomputable def nxt (c : Config Q Γ) : Config Q Γ :=
  match M.act c.state (c.tape c.head) with
  | none => c
  | some t => ⟨t.1, t.2.2.apply c.head, Function.update c.tape c.head t.2.1⟩

/-- **The run** on the input `w`. -/
noncomputable def run (w : List Γ) (t : ℕ) : Config Q Γ := M.nxt^[t] (M.initConfig w)

/-- The entries of the tableau: a symbol, with the state if the head is on the cell. -/
abbrev CSym (Q Γ : Type*) : Type _ := Option Q × Γ

/-- **The tableau** of the run on `w`. -/
noncomputable def tab (w : List Γ) (t i : ℕ) : CSym Q Γ :=
  (if (M.run w t).head = i then some (M.run w t).state else none, (M.run w t).tape i)

/-- The state entering a cell from its left neighbour `l` (`none`: the border). -/
noncomputable def fromL : Option (CSym Q Γ) → Option Q
  | some (some q, γ) =>
    match M.act q γ with
    | some (q', _, .right) => some q'
    | _ => none
  | _ => none

/-- The state entering a cell from its right neighbour. -/
noncomputable def fromR : CSym Q Γ → Option Q
  | (some q, γ) =>
    match M.act q γ with
    | some (q', _, .left) => some q'
    | _ => none
  | _ => none

/-- **The local rule** of the tableau: the new entry of a cell from the entries of its left
neighbour (`none` at the left border), itself and its right neighbour. -/
noncomputable def F (l : Option (CSym Q Γ)) (c r : CSym Q Γ) : CSym Q Γ :=
  match c.1 with
  | some q =>
    match M.act q c.2 with
    | none => c
    | some (q', γ', m) =>
      if m = .stay ∨ (m = .left ∧ l = none) then (some q', γ') else (none, γ')
  | none => ((M.fromL l).or (M.fromR r), c.2)

theorem run_succ (w : List Γ) (t : ℕ) : M.run w (t + 1) = M.nxt (M.run w t) := by
  unfold run
  rw [Function.iterate_succ_apply']

theorem fromR_none (γ : Γ) : M.fromR ((none, γ) : CSym Q Γ) = none := rfl

/-- The right neighbour matters only through its head. -/
theorem F_right (l : Option (CSym Q Γ)) (c : CSym Q Γ) (γ γ' : Γ) :
    M.F l c (none, γ) = M.F l c (none, γ') := by
  unfold F
  rcases c with ⟨_ | q, a⟩
  · simp [fromR_none]
  · rfl

/-- **The local rule.** -/
theorem tab_succ (w : List Γ) (t i : ℕ) :
    M.tab w (t + 1) i =
      M.F (if i = 0 then none else some (M.tab w t (i - 1))) (M.tab w t i) (M.tab w t (i + 1)) := by
  set c := M.run w t with hc
  have hrs := M.run_succ w t
  rw [← hc] at hrs
  unfold tab
  rw [hrs, ← hc]
  unfold nxt
  rcases ha : M.act c.state (c.tape c.head) with _ | ⟨q', γ', m⟩
  · -- no step
    by_cases hi : c.head = i
    · subst hi
      simp [F, ha]
    · simp only [hi, if_false, F]
      have hL : M.fromL (if i = 0 then none else some
          ((if c.head = i - 1 then some c.state else none), c.tape (i - 1))) = none := by
        split_ifs with h0 h1
        · rfl
        · rw [← h1]; simp [fromL, ha]
        · rfl
      have hR : M.fromR ((if c.head = i + 1 then some c.state else none), c.tape (i + 1)) = none := by
        split_ifs with h1
        · rw [← h1]; simp [fromR, ha]
        · rfl
      rw [hL, hR]
      rfl
  · simp only
    by_cases hi : c.head = i
    · subst hi
      simp only [if_true, F, ha, Function.update_self]
      cases m with
      | stay => simp
      | right => simp
      | left =>
        by_cases h0 : c.head = 0
        · simp [h0]
        · simp only [Move.apply, h0, if_false]
          rw [if_neg (by omega)]
          simp
    · simp only [hi, if_false, F, Function.update_of_ne (Ne.symm hi)]
      congr 1
      cases m with
      | stay =>
        simp only [Move.apply, hi, if_false]
        have hL : M.fromL (if i = 0 then none else some
            ((if c.head = i - 1 then some c.state else none), c.tape (i - 1))) = none := by
          split_ifs with h0 h1
          · rfl
          · rw [← h1]; simp [fromL, ha]
          · rfl
        have hR : M.fromR ((if c.head = i + 1 then some c.state else none), c.tape (i + 1)) =
            none := by
          split_ifs with h1
          · rw [← h1]; simp [fromR, ha]
          · rfl
        rw [hL, hR]; rfl
      | right =>
        have hR : M.fromR ((if c.head = i + 1 then some c.state else none), c.tape (i + 1)) =
            none := by
          split_ifs with h1
          · rw [← h1]; simp [fromR, ha]
          · rfl
        rw [hR, Option.or_none]
        simp only [Move.apply]
        by_cases h1 : c.head + 1 = i
        · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]
          rw [show i - 1 = c.head by omega]; simp [fromL, ha]
        · rw [if_neg h1]
          split_ifs with h0 h2
          · rfl
          · omega
          · rfl
      | left =>
        have hL : M.fromL (if i = 0 then none else some
            ((if c.head = i - 1 then some c.state else none), c.tape (i - 1))) = none := by
          split_ifs with h0 h1
          · rfl
          · rw [← h1]; simp [fromL, ha]
          · rfl
        rw [hL, Option.none_or]
        simp only [Move.apply]
        by_cases h1 : c.head = i + 1
        · rw [if_pos (by omega), if_pos h1, ← h1]
          simp [fromR, ha]
        · rw [if_neg h1]
          split_ifs with h2
          · omega
          · rfl

/-- **The first row** of the tableau. -/
theorem tab_zero (w : List Γ) (i : ℕ) :
    M.tab w 0 i = (if i = 0 then some M.init else none, w.getD i M.blank) := by
  unfold tab run
  simp only [Function.iterate_zero, id, initConfig]
  by_cases h : i = 0
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The head moves at most one cell per step. -/
theorem head_run_le (w : List Γ) (t : ℕ) : (M.run w t).head ≤ t := by
  induction t with
  | zero => simp [run, initConfig]
  | succ t ih =>
    rw [run_succ]
    unfold nxt
    rcases M.act (M.run w t).state ((M.run w t).tape (M.run w t).head) with _ | ⟨q', γ', m⟩
    · simp only; omega
    · simp only; have := Move.apply_le m (M.run w t).head; omega

/-- The head is where the tableau shows a state. -/
theorem tab_head (w : List Γ) (t : ℕ) :
    M.tab w t (M.run w t).head = (some (M.run w t).state, (M.run w t).tape (M.run w t).head) := by
  simp [tab]

theorem tab_fst_eq_some {w : List Γ} {t i : ℕ} {q : Q} (h : (M.tab w t i).1 = some q) :
    i = (M.run w t).head ∧ q = (M.run w t).state := by
  unfold tab at h
  split_ifs at h with hi
  cases h; exact ⟨hi.symm, rfl⟩

/-! ### Acceptance -/

variable {M}

/-- A step of a deterministic machine from a non-accepting configuration is the step of the
run. -/
theorem nxt_of_step (hdet : ∀ q γ, (M.step q γ).Subsingleton) {c d : Config Q Γ}
    (hs : M.Step c d) (hna : c.state ∉ M.accept) : M.nxt c = d := by
  obtain ⟨q', γ', m, hmem, rfl⟩ := hs
  have hne : (M.step c.state (c.tape c.head)).Nonempty := ⟨_, hmem⟩
  have hact : M.act c.state (c.tape c.head) = some hne.some := by
    simp [act, hna, hne]
  have heq : hne.some = (q', γ', m) := hdet _ _ hne.some_mem hmem
  unfold nxt
  rw [hact, heq]

/-- The run is frozen in an accepting configuration. -/
theorem nxt_of_accept {c : Config Q Γ} (h : c.state ∈ M.accept) : M.nxt c = c := by
  unfold nxt
  have : M.act c.state (c.tape c.head) = none := by simp [act, h]
  rw [this]

theorem iterate_frozen {c : Config Q Γ} (h : c.state ∈ M.accept) (n : ℕ) : M.nxt^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, nxt_of_accept h]

theorem reaches_iterate (hdet : ∀ q γ, (M.step q γ).Subsingleton) :
    ∀ (n : ℕ) {c d : Config Q Γ}, M.Reaches n c d →
      M.nxt^[n] c = d ∨ ∃ m ≤ n, (M.nxt^[m] c).state ∈ M.accept := by
  intro n
  induction n with
  | zero => intro c d h; exact Or.inl h
  | succ n ih =>
    intro c d h
    obtain ⟨e, hs, hr⟩ := h
    by_cases hna : c.state ∈ M.accept
    · exact Or.inr ⟨0, Nat.zero_le _, hna⟩
    · rw [← nxt_of_step hdet hs hna] at hr
      rcases ih hr with h | ⟨m, hm, ha⟩
      · exact Or.inl (by rw [Function.iterate_succ_apply]; exact h)
      · exact Or.inr ⟨m + 1, by omega, by rw [Function.iterate_succ_apply]; exact ha⟩

theorem reaches_nxt (c : Config Q Γ) : M.nxt c = c ∨ M.Step c (M.nxt c) := by
  unfold nxt
  rcases ha : M.act c.state (c.tape c.head) with _ | ⟨q', γ', m⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨q', γ', m, ?_, rfl⟩
    unfold act at ha
    split_ifs at ha with h1 h2
    rw [← Option.some.inj ha]
    exact h2.some_mem

theorem exists_reaches_iterate (c : Config Q Γ) :
    ∀ t, ∃ n ≤ t, M.Reaches n c (M.nxt^[t] c) := by
  intro t
  induction t with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ t ih =>
    obtain ⟨n, hn, hr⟩ := ih
    rw [Function.iterate_succ_apply']
    rcases reaches_nxt (M.nxt^[t] c) with h | h
    · rw [h]; exact ⟨n, by omega, hr⟩
    · exact ⟨n + 1, by omega, NTM.Reaches.trans M hr (⟨_, h, rfl⟩ : M.Reaches 1 _ _)⟩

/-- **A deterministic machine accepts within `T` steps iff the run is accepting at time `T`.** -/
theorem acceptsWithin_iff_run (hdet : ∀ q γ, (M.step q γ).Subsingleton) (w : List Γ) (T : ℕ) :
    M.AcceptsWithin w T ↔ (M.run w T).state ∈ M.accept := by
  constructor
  · rintro ⟨n, hn, d, hr, ha⟩
    have key : ∃ m ≤ n, (M.run w m).state ∈ M.accept := by
      rcases reaches_iterate hdet n hr with h | h
      · exact ⟨n, le_rfl, by unfold run; rw [h]; exact ha⟩
      · exact h
    obtain ⟨m, hm, ha'⟩ := key
    have : M.run w T = M.run w m := by
      unfold run
      rw [show T = (T - m) + m by omega, Function.iterate_add_apply]
      exact iterate_frozen ha' _
    rw [this]; exact ha'
  · intro h
    obtain ⟨n, hn, hr⟩ := exists_reaches_iterate (M := M) (M.initConfig w) T
    exact ⟨n, hn, _, hr, h⟩

/-- **Acceptance read off the tableau**: the run accepts at time `T` iff some cell at most `T`
shows an accepting state. -/
theorem run_accept_iff_tab (w : List Γ) (T : ℕ) :
    (M.run w T).state ∈ M.accept ↔ ∃ i ≤ T, ∃ q ∈ M.accept, ∃ γ, M.tab w T i = (some q, γ) := by
  constructor
  · intro h
    exact ⟨_, head_run_le M w T, _, h, _, tab_head M w T⟩
  · rintro ⟨i, -, q, hq, γ, h⟩
    have := tab_fst_eq_some M (by rw [h])
    rw [← this.2]; exact hq

end NTM

end TM
