import ComplexityTheory.Lang.Basic
/-!
# The Savitch game: an alternating source for `EXPSPACE`

For a nondeterministic single-tape machine `N` and a space bound `S`:

* `FOND.ATM.SavWin N S k c c'` — the **Savitch game**: the existential player claims that `c'`
  is reachable from `c` in at most `2 ^ k` steps within space `S`; for `k + 1` she names a
  midpoint configuration `d`, and the universal player picks one of the halves `(c, d)`,
  `(d, c')` to continue with (the conjunction); for `k = 0` the claim is checked locally
  (`c = c'`, or one step of `N`, the heads on the cells `0 … S - 1`).
* `FOND.ATM.savWin_iff` — the claim wins iff `c'` is reachable in at most `2 ^ k` steps.
* `FOND.ATM.reachesSpace_short` — **short runs suffice**: whatever is reachable within space `S`
  is reachable in at most `|Q| · S · |Γ| ^ S` steps (the configurations of a run agree with the
  start outside the cells `0 … S - 1`).
* **`FOND.ATM.expspace_savWin`** — every language of `EXPSPACE` (`HTN.Space.InExpSpace`) is
  characterised by the Savitch game of a fixed machine with `S = 2 ^ p(|w|)` and
  `k = |Q| + p(|w|) + 2 · 2 ^ p(|w|)`: `w ∈ L` iff for some accepting configuration `c` the
  existential player wins `(k, initConfig w, c)`.

Positions of the game are pairs of configurations with tapes of `2 ^ p(|w|)` cells (exponential
size), and the game lasts `k` (exponentially many) rounds: an alternating exponential-time
computation (`AEXPTIME = EXPSPACE`).
-/

namespace FOND

namespace ATM

open HTN TM

section Reach

variable {Q Γ : Type} (N : NTM Q Γ) (S : ℕ)

theorem head_lt_of_reachesSpace : ∀ {n : ℕ} {c c' : Config Q Γ}, N.ReachesSpace S n c c' →
    c.head < S
  | 0, _, _, h => h.2
  | _ + 1, _, _, h => h.1

theorem reachesSpace_add : ∀ (a b : ℕ) (c c' : Config Q Γ),
    N.ReachesSpace S (a + b) c c' ↔ ∃ d, N.ReachesSpace S a c d ∧ N.ReachesSpace S b d c' := by
  intro a
  induction a with
  | zero =>
    intro b c c'
    simp only [Nat.zero_add, NTM.ReachesSpace]
    constructor
    · intro h; exact ⟨c, ⟨rfl, head_lt_of_reachesSpace N S h⟩, h⟩
    · rintro ⟨d, ⟨rfl, -⟩, h⟩; exact h
  | succ a ih =>
    intro b c c'
    rw [show a + 1 + b = (a + b) + 1 by ring]
    simp only [NTM.ReachesSpace]
    constructor
    · rintro ⟨hc, e, he, h⟩
      obtain ⟨d, h1, h2⟩ := (ih b e c').1 h
      exact ⟨d, ⟨hc, e, he, h1⟩, h2⟩
    · rintro ⟨d, ⟨hc, e, he, h1⟩, h2⟩
      exact ⟨hc, e, he, (ih b e c').2 ⟨d, h1, h2⟩⟩

/-- **The Savitch game.** -/
def SavWin : ℕ → Config Q Γ → Config Q Γ → Prop
  | 0, c, c' => (c = c' ∧ c.head < S) ∨ (c.head < S ∧ N.Step c c' ∧ c'.head < S)
  | k + 1, c, c' => ∃ d, SavWin k c d ∧ SavWin k d c'

theorem savWin_zero_iff (c c' : Config Q Γ) :
    SavWin N S 0 c c' ↔ ∃ n ≤ 1, N.ReachesSpace S n c c' := by
  simp only [SavWin]
  constructor
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, le_rfl, h1, c', h2, rfl, h3⟩
  · rintro ⟨n, hn, h⟩
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · exact Or.inl h
    · obtain ⟨h1, d, h2, rfl, h3⟩ := h
      exact Or.inr ⟨h1, h2, h3⟩

/-- **A claim wins iff it is true.** -/
theorem savWin_iff : ∀ (k : ℕ) (c c' : Config Q Γ),
    SavWin N S k c c' ↔ ∃ n ≤ 2 ^ k, N.ReachesSpace S n c c' := by
  intro k
  induction k with
  | zero => intro c c'; rw [savWin_zero_iff]; simp
  | succ k ih =>
    intro c c'
    simp only [SavWin]
    constructor
    · rintro ⟨d, h1, h2⟩
      obtain ⟨n₁, hn₁, r₁⟩ := (ih c d).1 h1
      obtain ⟨n₂, hn₂, r₂⟩ := (ih d c').1 h2
      exact ⟨n₁ + n₂, by rw [pow_succ]; omega, (reachesSpace_add N S _ _ _ _).2 ⟨d, r₁, r₂⟩⟩
    · rintro ⟨n, hn, h⟩
      have hsplit : n = min n (2 ^ k) + (n - min n (2 ^ k)) := by omega
      rw [hsplit] at h
      obtain ⟨d, r₁, r₂⟩ := (reachesSpace_add N S _ _ _ _).1 h
      refine ⟨d, (ih c d).2 ⟨_, min_le_right _ _, r₁⟩, (ih d c').2 ⟨_, ?_, r₂⟩⟩
      rw [pow_succ] at hn
      omega

end Reach

/-! ## Short runs -/

section Short

variable {Q Γ : Type} (N : NTM Q Γ) (S : ℕ) (c₀ : Config Q Γ)

/-- Runs leave the cells outside `0 … S - 1` untouched. -/
theorem tape_of_reachesSpace : ∀ {n : ℕ} {c c' : Config Q Γ}, N.ReachesSpace S n c c' →
    (∀ j, S ≤ j → c'.tape j = c.tape j) ∧ c'.head < S
  | 0, _, _, h => by obtain ⟨rfl, h⟩ := h; exact ⟨fun _ _ => rfl, h⟩
  | _ + 1, c, c', h => by
    obtain ⟨hc, d, ⟨q', γ', m, -, rfl⟩, hr⟩ := h
    obtain ⟨h1, h2⟩ := tape_of_reachesSpace hr
    refine ⟨fun j hj => ?_, h2⟩
    rw [h1 j hj]
    simp only
    rw [Function.update_of_ne (by omega)]

/-- The key of a configuration: state, head and the cells `0 … S - 1`. -/
def keyOf (hS : 0 < S) (c : Config Q Γ) : Q × Fin S × (Fin S → Γ) :=
  (c.state, ⟨c.head % S, Nat.mod_lt _ hS⟩, fun j => c.tape j)

/-- The configurations reachable from `c₀` in at most `m` steps. -/
def Rm (m : ℕ) : Set (Config Q Γ) := {c | ∃ n ≤ m, N.ReachesSpace S n c₀ c}

theorem keyOf_injOn (hS : 0 < S) :
    Set.InjOn (keyOf S hS) {c : Config Q Γ | (∀ j, S ≤ j → c.tape j = c₀.tape j) ∧ c.head < S} := by
  rintro ⟨q, h, t⟩ ⟨hc₁, hc₂⟩ ⟨q', h', t'⟩ ⟨hc₁', hc₂'⟩ he
  simp only [keyOf, Prod.mk.injEq, Fin.mk.injEq] at he hc₁ hc₂ hc₁' hc₂'
  obtain ⟨rfl, hh, ht⟩ := he
  rw [Nat.mod_eq_of_lt hc₂, Nat.mod_eq_of_lt hc₂'] at hh
  subst hh
  congr 1
  funext j
  by_cases hj : j < S
  · exact congrFun ht ⟨j, hj⟩
  · rw [hc₁ j (by omega), hc₁' j (by omega)]

theorem Rm_sub (m : ℕ) :
    Rm N S c₀ m ⊆ {c | (∀ j, S ≤ j → c.tape j = c₀.tape j) ∧ c.head < S} := by
  rintro c ⟨n, -, h⟩
  exact tape_of_reachesSpace N S h

theorem Rm_mono {m m' : ℕ} (h : m ≤ m') : Rm N S c₀ m ⊆ Rm N S c₀ m' := by
  rintro c ⟨n, hn, hr⟩; exact ⟨n, by omega, hr⟩

theorem Rm_stable {m : ℕ} (hst : Rm N S c₀ (m + 1) ⊆ Rm N S c₀ m) :
    ∀ j, Rm N S c₀ (m + j) ⊆ Rm N S c₀ m := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rintro c ⟨n, hn, hr⟩
    by_cases hnj : n ≤ m + j
    · exact ih ⟨n, hnj, hr⟩
    · obtain rfl : n = (m + j) + 1 := by omega
      obtain ⟨d, h1, h2⟩ := (reachesSpace_add N S _ _ _ _).1 hr
      obtain ⟨nd, hnd, hd⟩ := ih ⟨m + j, le_rfl, h1⟩
      exact hst ⟨nd + 1, by omega, (reachesSpace_add N S _ _ _ _).2 ⟨d, hd, h2⟩⟩

theorem Rm_growth [Fintype Q] [Fintype Γ] (hS : 0 < S) (h₀ : c₀.head < S) : ∀ m,
    (∃ j ≤ m, Rm N S c₀ (j + 1) ⊆ Rm N S c₀ j) ∨
      m + 1 ≤ (keyOf S hS '' Rm N S c₀ m).ncard := by
  intro m
  induction m with
  | zero =>
    right
    rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Set.toFinite _)]
    exact Set.Nonempty.ne_empty ⟨_, c₀, ⟨0, le_rfl, rfl, h₀⟩, rfl⟩
  | succ m ih =>
    rcases ih with ⟨j, hj, hst⟩ | ih
    · exact Or.inl ⟨j, by omega, hst⟩
    by_cases hst : Rm N S c₀ (m + 1) ⊆ Rm N S c₀ m
    · exact Or.inl ⟨m, Nat.le_succ m, hst⟩
    right
    obtain ⟨c, hc, hcn⟩ := Set.not_subset.1 hst
    have hsub : keyOf S hS '' Rm N S c₀ m ⊂ keyOf S hS '' Rm N S c₀ (m + 1) := by
      refine (Set.ssubset_iff_of_subset (Set.image_mono (Rm_mono N S c₀ (by omega)))).2
        ⟨keyOf S hS c, ⟨c, hc, rfl⟩, ?_⟩
      rintro ⟨d, hd, hdc⟩
      have := keyOf_injOn S c₀ hS (Rm_sub N S c₀ m hd) (Rm_sub N S c₀ (m + 1) hc) hdc
      exact hcn (this ▸ hd)
    have := Set.ncard_lt_ncard hsub (Set.toFinite _)
    omega

/-- **Short runs suffice.** -/
theorem reachesSpace_short [Fintype Q] [Fintype Γ] (hS : 0 < S) (h₀ : c₀.head < S) {n : ℕ} {c : Config Q Γ}
    (h : N.ReachesSpace S n c₀ c) :
    ∃ n' ≤ Fintype.card Q * S * Fintype.card Γ ^ S, N.ReachesSpace S n' c₀ c := by
  set M := Fintype.card Q * S * Fintype.card Γ ^ S with hM
  have hcard : ∀ X : Set (Q × Fin S × (Fin S → Γ)), X.ncard ≤ M := by
    intro X
    have := Set.ncard_le_ncard (Set.subset_univ X) (Set.toFinite _)
    rw [Set.ncard_univ] at this
    simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, hM, mul_assoc] using this
  rcases Rm_growth N S c₀ hS h₀ M with ⟨j, hj, hst⟩ | hbig
  · have h1 := Rm_stable N S c₀ hst n
    obtain ⟨n', hn', hr⟩ := h1 ⟨n, by omega, h⟩
    exact ⟨n', by omega, hr⟩
  · have := hcard (keyOf S hS '' Rm N S c₀ M)
    omega

end Short

/-! ## `EXPSPACE` -/

/-- **Every `EXPSPACE` language is characterised by the Savitch game of a fixed machine.** -/
theorem expspace_savWin {L : Cx.Language} (hL : Cx.EXPSPACE L) :
    ∃ (k : ℕ) (N : NTM (Fin k) Space.TapeSym) (p : Polynomial ℕ), ∀ w,
      L w ↔ ∃ c : Config (Fin k) Space.TapeSym, c.state ∈ N.accept ∧
        SavWin N (2 ^ p.eval w.length) (k + p.eval w.length + 2 * 2 ^ p.eval w.length)
          (N.initConfig (w.map some)) c := by
  obtain ⟨k, N, p, hN⟩ := hL
  refine ⟨k, N, p, fun w => ?_⟩
  rw [hN]
  set S := 2 ^ p.eval w.length with hSdef
  have hS : 0 < S := Nat.two_pow_pos _
  have hbound : k * S * 3 ^ S ≤ 2 ^ (k + p.eval w.length + 2 * S) := by
    have h1 : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    have h3 : 3 ^ S ≤ 2 ^ (2 * S) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) S
    rw [pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) h3
  constructor
  · rintro ⟨n, c, hr, hc⟩
    have h₀ : (N.initConfig (w.map some)).head < S := hS
    obtain ⟨n', hn', hr'⟩ := reachesSpace_short N S _ hS h₀ hr
    refine ⟨c, hc, (savWin_iff N S _ _ _).2 ⟨n', ?_, hr'⟩⟩
    simp only [Fintype.card_fin, Fintype.card_option, Fintype.card_bool,
      show (2 : ℕ) + 1 = 3 from rfl] at hn'
    omega
  · rintro ⟨c, hc, hw⟩
    obtain ⟨n, -, hr⟩ := (savWin_iff N S _ _ _).1 hw
    exact ⟨n, c, hr, hc⟩

end ATM

end FOND
