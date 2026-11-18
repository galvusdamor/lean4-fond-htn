import FondHtn.DB25Games.Sem
/-!
# The hardness game decides space-bounded acceptance

* `FOND.DBG.Good` — the abstract claim game (one cycle = one backward step of the tableau);
* `FOND.DBG.win_main` — the STRIPS game realises it: from a turn-0 state, Éloise wins with `T`
  actions remaining iff `T = 4 (t + 1)` and the claim is good at time `t + 1`;
* `FOND.DBG.good_iff` — good claims are true entries of the truncated tableau (and the
  existential claim is `FOND.DBG.AccW`);
* **`FOND.DBG.chosen_iff_accepts`** — for a deterministic machine, the chosen-length game of
  `FOND.DBG.hardDesc M m u` is won iff `M` accepts `u` in space `2 ^ m`.
-/

namespace FOND

namespace DBG

open TM TM.NTM

variable {k : ℕ} (M : NTM (Fin k) Sym) (u : List Sym)

/-- **The claim game.** -/
def Good (S : ℕ) : ℕ → ℕ → V k → Prop
  | 0, i, X => X = some (row0 M u i)
  | t + 1, i, X =>
    (∃ l c r : CS k, ((i ≠ 0 ∧ Matches M X (M.F (some l) c r)) ∨ (i = 0 ∧ Matches M X (M.F none c r))) ∧
      (i ≠ 0 → Good S t (i - 1) (some l)) ∧ Good S t i (some c) ∧
      (i + 1 < S → Good S t (i + 1) (some r)) ∧ (i + 1 = S → r.1 = none)) ∨
    (X = none ∧ i + 1 < S ∧ Good S t (i + 1) none)

theorem row0_iff (i : ℕ) (X : V k) :
    (∃ G, GOk u.length G ∧ G ≠ .none ∧ ¬ Refut M u i X G) ↔ X = some (row0 M u i) := by
  constructor
  · rintro ⟨G, hG, hne, hr⟩
    cases G with
    | none => exact absurd rfl hne
    | j j =>
      simp only [Refut, not_or, not_not] at hr
      obtain ⟨rfl, hX⟩ := hr; exact hX
    | b =>
      simp only [Refut, not_or, not_le, not_not] at hr
      obtain ⟨hlt, hX⟩ := hr
      rw [hX, row0, if_neg (by omega), List.getD_eq_default _ _ (by omega)]
  · intro hX
    by_cases hi : i ≤ u.length
    · exact ⟨.j i, hi, by simp, by simp [Refut, hX]⟩
    · refine ⟨.b, trivial, by simp, ?_⟩
      simp only [Refut, not_or, not_not]
      refine ⟨by omega, ?_⟩
      rw [hX, row0, if_neg (by omega), List.getD_eq_default _ _ (by omega)]

variable (m : ℕ)

/-- **The STRIPS game realises the claim game.** -/
theorem win_main : ∀ T,
    (∀ i < 2 ^ m, ∀ (X : V k) G, GOk u.length G →
      (Win (acts M m u) goal T true (st 0 i X .none G) ↔
        (T = 0 ∧ G ≠ .none) ∨ ∃ t, T = 4 * t + 4 ∧ Good M u (2 ^ m) (t + 1) i X)) ∧
    (∀ i < 2 ^ m, ∀ (X : V k),
      (Win (acts M m u) goal T true (st 2 i X .none .none) ↔ ∃ t, T = 4 * t + 2 ∧ Good M u (2 ^ m) t i X)) := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  constructor
  · intro i hi X G hG
    match T with
    | 0 => rw [win_zero_ph0]; simp
    | 1 =>
      rw [win_ph0 M m u hi X G hG 0]
      constructor
      · rintro ⟨P, -, hw⟩; exact absurd hw (not_win_zero M m u (by omega) _ _ _ _)
      · rintro (⟨h, -⟩ | ⟨t, ht, -⟩) <;> omega
    | T' + 2 =>
      rw [win_ph0 M m u hi X G hG (T' + 1)]
      have hst2 := (ih T' (by omega)).2
      by_cases hT : ∃ t, T' = 4 * t + 2
      · obtain ⟨t0, rfl⟩ := hT
        have key : ∀ j < 2 ^ m, ∀ Y : V k, Win (acts M m u) goal (4 * t0 + 2) true (st 2 j Y .none .none) ↔
            Good M u (2 ^ m) t0 j Y := fun j hj Y => by
          rw [hst2 j hj Y]
          constructor
          · rintro ⟨t, ht, h⟩
            obtain rfl : t = t0 := by omega
            exact h
          · exact fun h => ⟨t0, rfl, h⟩
        have hR : ((4 * t0 + 2 + 2 = 0 ∧ G ≠ .none) ∨ ∃ t, 4 * t0 + 2 + 2 = 4 * t + 4 ∧
            Good M u (2 ^ m) (t + 1) i X) ↔ Good M u (2 ^ m) (t0 + 1) i X :=
          ⟨fun h => by
            rcases h with ⟨h, -⟩ | ⟨t, ht, h⟩
            · omega
            · obtain rfl : t = t0 := by omega
              exact h, fun h => Or.inr ⟨t0, by omega, h⟩⟩
        rw [hR, Good]
        constructor
        · rintro ⟨P, hP, hw⟩
          cases P with
          | none => exact hP.elim
          | tri l c r =>
            rw [win_ph1_tri M m u hi] at hw
            obtain ⟨hL, hC, hRr, hK⟩ := hw
            exact Or.inl ⟨l, c, r, hP, fun h => (key _ (by omega) _).1 (hL h), (key _ hi _).1 hC,
              fun h => (key _ h _).1 (hRr h), hK⟩
          | shift =>
            obtain ⟨rfl, hlt⟩ := hP
            rw [win_ph1_shift M m u hlt] at hw
            exact Or.inr ⟨rfl, hlt, (key _ hlt _).1 hw⟩
        · rintro (⟨l, c, r, hv, hl, hc, hr, hb⟩ | ⟨rfl, hlt, hg⟩)
          · refine ⟨.tri l c r, hv, ?_⟩
            rw [win_ph1_tri M m u hi]
            exact ⟨fun h => (key _ (by omega) _).2 (hl h), (key _ hi _).2 hc,
              fun h => (key _ h _).2 (hr h), hb⟩
          · refine ⟨.shift, ⟨rfl, hlt⟩, ?_⟩
            rw [win_ph1_shift M m u hlt]
            exact (key _ hlt _).2 hg
      · constructor
        · rintro ⟨P, hP, hw⟩
          cases P with
          | none => exact hP.elim
          | tri l c r =>
            rw [win_ph1_tri M m u hi] at hw
            obtain ⟨t, ht, -⟩ := (hst2 i hi _).1 hw.2.1
            exact absurd ⟨t, ht⟩ hT
          | shift =>
            obtain ⟨rfl, hlt⟩ := hP
            rw [win_ph1_shift M m u hlt] at hw
            obtain ⟨t, ht, -⟩ := (hst2 _ hlt _).1 hw
            exact absurd ⟨t, ht⟩ hT
        · rintro (⟨h, -⟩ | ⟨t, ht, -⟩)
          · omega
          · exact absurd ⟨t, by omega⟩ hT
  · intro i hi X
    match T with
    | 0 =>
      constructor
      · intro h; exact absurd h (not_win_zero M m u (by omega) _ _ _ _)
      · rintro ⟨t, ht, -⟩; omega
    | 1 =>
      rw [win_ph2]
      constructor
      · rintro ⟨G, -, hw⟩; exact absurd hw (not_win_zero M m u (by omega) _ _ _ _)
      · rintro ⟨t, ht, -⟩; omega
    | T'' + 2 =>
      rw [win_ph2]
      have hst0 := (ih T'' (by omega)).1 i hi X
      constructor
      · rintro ⟨G, hG, hw⟩
        rw [win_ph3 M m u hi X G hG, hst0 G hG] at hw
        obtain ⟨hnr, (⟨rfl, hne⟩ | ⟨t, rfl, hg⟩)⟩ := hw
        · exact ⟨0, rfl, (row0_iff M u i X).1 ⟨G, hG, hne, hnr⟩⟩
        · exact ⟨t + 1, by omega, hg⟩
      · rintro ⟨t, ht, hg⟩
        cases t with
        | zero =>
          obtain ⟨G, hG, hne, hnr⟩ := (row0_iff M u i X).2 hg
          refine ⟨G, hG, ?_⟩
          rw [win_ph3 M m u hi X G hG, hst0 G hG]
          exact ⟨hnr, Or.inl ⟨by omega, hne⟩⟩
        | succ t =>
          refine ⟨.none, trivial, ?_⟩
          rw [win_ph3 M m u hi X .none trivial, hst0 .none trivial]
          exact ⟨id, Or.inr ⟨t, by omega, hg⟩⟩

/-! ## Good claims are true -/

variable (S : ℕ)

theorem good_step (t i : ℕ) (hi : i < S)
    (IH : ∀ j < S, ∀ x : CS k, Good M u S t j (some x) ↔ x = tabT M S u t j) (P : CS k → Prop) :
    (∃ l c r : CS k, ((i ≠ 0 ∧ P (M.F (some l) c r)) ∨ (i = 0 ∧ P (M.F none c r))) ∧
      (i ≠ 0 → Good M u S t (i - 1) (some l)) ∧ Good M u S t i (some c) ∧
      (i + 1 < S → Good M u S t (i + 1) (some r)) ∧ (i + 1 = S → r.1 = none)) ↔
    P (tabT M S u (t + 1) i) := by
  rw [tabT_succ]
  set rgt : CS k := if i + 1 < S then tabT M S u t (i + 1) else (none, M.blank) with hrgt
  constructor
  · rintro ⟨l, c, r, hv, hl, hc, hr, hb⟩
    rw [IH i hi] at hc
    subst hc
    have hF : ∀ L, M.F L (tabT M S u t i) r = M.F L (tabT M S u t i) rgt := by
      intro L
      by_cases h1 : i + 1 < S
      · rw [hrgt, if_pos h1, ← (IH _ h1 r).1 (hr h1)]
      · rw [hrgt, if_neg h1]
        obtain ⟨r1, r2⟩ := r
        have : r1 = none := hb (by omega)
        subst this
        exact F_right M L _ r2 M.blank
    by_cases h0 : i = 0
    · rw [if_pos h0, ← hF]
      rcases hv with ⟨h, -⟩ | ⟨-, hv⟩
      · exact absurd h0 h
      · exact hv
    · rw [if_neg h0, ← hF, ← (IH _ (by omega) l).1 (hl h0)]
      rcases hv with ⟨-, hv⟩ | ⟨h, -⟩
      · exact hv
      · exact absurd h h0
  · intro hP
    refine ⟨tabT M S u t (i - 1), tabT M S u t i, rgt, ?_, fun _ => (IH _ (by omega) _).2 rfl,
      (IH _ hi _).2 rfl, fun h => ?_, fun h => ?_⟩
    · by_cases h0 : i = 0
      · rw [if_pos h0] at hP; exact Or.inr ⟨h0, hP⟩
      · rw [if_neg h0] at hP; exact Or.inl ⟨h0, hP⟩
    · rw [hrgt, if_pos h]; exact (IH _ h _).2 rfl
    · rw [hrgt, if_neg (by omega)]

theorem matches_some (x y : CS k) : Matches M (some x) y ↔ x = y := by
  simp [Matches]

theorem matches_none (y : CS k) : Matches M none y ↔ ∃ q ∈ M.accept, ∃ γ, y = (some q, γ) := by
  simp only [Matches, reduceCtorEq, false_or, true_and]
  constructor
  · rintro ⟨q, hq, h⟩; exact ⟨q, hq, y.2, by rw [← h]⟩
  · rintro ⟨q, hq, γ, rfl⟩; exact ⟨q, hq, rfl⟩

/-- **Good claims are true entries.** -/
theorem good_iff : ∀ t i, i < S →
    (∀ x : CS k, Good M u S t i (some x) ↔ x = tabT M S u t i) ∧ (Good M u S t i none ↔ AccW M S u t i) := by
  intro t
  induction t with
  | zero =>
    intro i _
    refine ⟨fun x => ?_, ?_⟩
    · simp [Good, tabT_zero, row0]
    · simp [Good, AccW]
  | succ t ih =>
    intro i hi
    have IH : ∀ j < S, ∀ x : CS k, Good M u S t j (some x) ↔ x = tabT M S u t j :=
      fun j hj => (ih j hj).1
    refine ⟨fun x => ?_, ?_⟩
    · rw [Good, good_step M u S t i hi IH (Matches M (some x)), matches_some]
      simp
    · rw [Good, good_step M u S t i hi IH (Matches M none), matches_none, AccW]
      refine or_congr Iff.rfl ?_
      simp only [true_and]
      exact and_congr_right fun h => (ih (i + 1) h).2

/-! ## The initial state and the theorem -/

theorem stOf_init : stOf (init : List (Fct k)) = st 0 0 none .none .none := by
  funext f
  cases f <;> simp [stOf, init, st, eq_comm]

/-- **For a deterministic machine, the chosen-length game is won iff `M` accepts `u` in space
`2 ^ m`.** -/
theorem chosen_iff_accepts (hdet : ∀ q γ, (M.step q γ).Subsingleton) :
    (∃ r, Win (acts M m u) goal r true (stOf init)) ↔ M.AcceptsInSpace u (2 ^ m) := by
  have hS : 0 < 2 ^ m := Nat.two_pow_pos m
  rw [stOf_init, ← tabT_accept_iff M (2 ^ m) u hdet, ← exists_accW_iff M (2 ^ m) u hS]
  constructor
  · rintro ⟨r, hr⟩
    rw [((win_main M u m r).1 0 hS none .none trivial)] at hr
    rcases hr with ⟨-, h⟩ | ⟨t, -, hg⟩
    · exact absurd rfl h
    · exact ⟨t + 1, ((good_iff M u (2 ^ m) (t + 1) 0 hS).2).1 hg⟩
  · rintro ⟨t, ht⟩
    cases t with
    | zero => exact ht.elim
    | succ t =>
      refine ⟨4 * t + 4, ?_⟩
      rw [((win_main M u m _).1 0 hS none .none trivial)]
      exact Or.inr ⟨t, rfl, ((good_iff M u (2 ^ m) (t + 1) 0 hS).2).2 ht⟩

end DBG

end FOND
