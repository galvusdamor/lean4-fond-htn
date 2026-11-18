import ComplexityTheory.TM.Tableau
import ComplexityTheory.Complexity.Hypotheses
/-!
# The truncated tableau of a space-bounded deterministic run

For a machine `M` and a space bound `S`, `FOND.DBG.tabT M S u t i` (`i < S`) is the tableau of
the run on `u` restricted to the cells `0, …, S - 1`, with a head-less right border
(`(none, blank)`): a head leaving the space simply disappears.

* `FOND.DBG.tabT_eq_tab` — while the head stays below `S`, it is the true tableau;
* `FOND.DBG.tabT_accept_iff` — **some cell below `S` of the truncated tableau shows an accepting
  state iff a deterministic `M` accepts `u` in space `S`**;
* `FOND.DBG.AccW` — the claim "an accepting state is shown at some cell `j ≥ i` at time
  `t - (j - i)`" (the existential start of the hardness game), and
  `FOND.DBG.exists_accW_iff`.
-/

namespace FOND

namespace DBG

open TM TM.NTM

section

variable {Q Γ : Type} (M : NTM Q Γ) (S : ℕ) (u : List Γ)

/-- **The truncated tableau.** -/
noncomputable def tabT : ℕ → ℕ → CSym Q Γ
  | 0, i => (if i = 0 then some M.init else none, u.getD i M.blank)
  | t + 1, i => M.F (if i = 0 then none else some (tabT t (i - 1))) (tabT t i)
      (if i + 1 < S then tabT t (i + 1) else (none, M.blank))

theorem tabT_zero (i : ℕ) : tabT M S u 0 i = (if i = 0 then some M.init else none, u.getD i M.blank) :=
  rfl

theorem tabT_succ (t i : ℕ) : tabT M S u (t + 1) i = M.F (if i = 0 then none else some (tabT M S u t (i - 1)))
    (tabT M S u t i) (if i + 1 < S then tabT M S u t (i + 1) else (none, M.blank)) := rfl

/-- While the head stays below `S`, the truncated tableau is the tableau. -/
theorem tabT_eq_tab : ∀ t, (∀ t' < t, (M.run u t').head < S) → ∀ i < S, tabT M S u t i = M.tab u t i := by
  intro t
  induction t with
  | zero => intro _ i _; rw [tabT_zero, tab_zero]
  | succ t ih =>
    intro hh i hi
    have ih' := ih (fun t' ht' => hh t' (by omega))
    rw [tabT_succ, tab_succ]
    have hl : (if i = 0 then none else some (tabT M S u t (i - 1))) =
        (if i = 0 then none else some (M.tab u t (i - 1))) := by
      split_ifs with h0
      · rfl
      · rw [ih' (i - 1) (by omega)]
    rw [hl, ih' i hi]
    by_cases h1 : i + 1 < S
    · rw [if_pos h1, ih' (i + 1) h1]
    · rw [if_neg h1]
      have hS : i + 1 = S := by omega
      have hne : (M.run u t).head ≠ i + 1 := by have := hh t (by omega); omega
      have : M.tab u t (i + 1) = (none, (M.run u t).tape (i + 1)) := by
        simp [tab, hne]
      rw [this, F_right]

/-- A row without head stays without head. -/
theorem tabT_noHead {t : ℕ} (h : ∀ i < S, (tabT M S u t i).1 = none) :
    ∀ i < S, (tabT M S u (t + 1) i).1 = none := by
  intro i hi
  rw [tabT_succ]
  have hc := h i hi
  unfold F
  rw [hc]
  simp only
  have hL : M.fromL (if i = 0 then none else some (tabT M S u t (i - 1))) = none := by
    split_ifs with h0
    · rfl
    · have := h (i - 1) (by omega)
      unfold fromL
      rcases e : tabT M S u t (i - 1) with ⟨_ | q, γ⟩
      · rfl
      · rw [e] at this; simp at this
  have hR : M.fromR (if i + 1 < S then tabT M S u t (i + 1) else (none, M.blank)) = none := by
    split_ifs with h1
    · have := h (i + 1) h1
      rcases e : tabT M S u t (i + 1) with ⟨_ | q, γ⟩
      · rfl
      · rw [e] at this; simp at this
    · rfl
  rw [hL, hR]; rfl

theorem tabT_noHead_after {t : ℕ} (h : ∀ i < S, (tabT M S u t i).1 = none) :
    ∀ d, ∀ i < S, (tabT M S u (t + d) i).1 = none := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih => exact tabT_noHead M S u ih

/-- **Frozen accepting entries.** -/
theorem tabT_frozen {t i : ℕ} {q : Q} {γ : Γ} (hq : q ∈ M.accept) (h : tabT M S u t i = (some q, γ)) :
    tabT M S u (t + 1) i = (some q, γ) := by
  rw [tabT_succ, h]
  unfold F
  have : M.act q γ = none := by simp [act, hq]
  simp [this]

theorem tabT_frozen_add {t i : ℕ} {q : Q} {γ : Γ} (hq : q ∈ M.accept) (h : tabT M S u t i = (some q, γ)) :
    ∀ d, tabT M S u (t + d) i = (some q, γ) := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih => exact tabT_frozen M S u hq ih

/-! ### Runs in space -/

theorem reachesSpace_snoc {S : ℕ} : ∀ (n : ℕ) {c d e : Config Q Γ}, M.ReachesSpace S n c d → M.Step d e →
    e.head < S → M.ReachesSpace S (n + 1) c e
  | 0, c, d, e, h, hs, he => by
    obtain ⟨rfl, hc⟩ := h
    exact ⟨hc, e, hs, rfl, he⟩
  | n + 1, c, d, e, h, hs, he => by
    obtain ⟨hc, x, hx, hr⟩ := h
    exact ⟨hc, x, hx, reachesSpace_snoc n hr hs he⟩

theorem reachesSpace_run : ∀ t, (∀ t' ≤ t, (M.run u t').head < S) →
    ∃ n, M.ReachesSpace S n (M.initConfig u) (M.run u t) := by
  intro t
  induction t with
  | zero => intro h; exact ⟨0, rfl, by simpa [run] using h 0 le_rfl⟩
  | succ t ih =>
    intro h
    obtain ⟨n, hn⟩ := ih fun t' ht' => h t' (by omega)
    rw [run_succ]
    rcases reaches_nxt (M := M) (M.run u t) with he | he
    · rw [he]; exact ⟨n, hn⟩
    · exact ⟨n + 1, reachesSpace_snoc M n hn he (by rw [← run_succ]; exact h _ le_rfl)⟩

theorem iterate_of_reachesSpace (hdet : ∀ q γ, (M.step q γ).Subsingleton) :
    ∀ (n : ℕ) {c₀ c : Config Q Γ}, M.ReachesSpace S n c₀ c → c.state ∈ M.accept →
      ∃ m, (∀ t' ≤ m, (M.nxt^[t'] c₀).head < S) ∧ (M.nxt^[m] c₀).state ∈ M.accept
  | 0, c₀, c, h, hc => by
    obtain ⟨rfl, h0⟩ := h
    exact ⟨0, fun t' ht' => by rw [Nat.le_zero.1 ht']; exact h0, hc⟩
  | n + 1, c₀, c, h, hc => by
    obtain ⟨h0, d, hs, hr⟩ := h
    by_cases hna : c₀.state ∈ M.accept
    · exact ⟨0, fun t' ht' => by rw [Nat.le_zero.1 ht']; exact h0, hna⟩
    · obtain ⟨m, hm, ha⟩ := iterate_of_reachesSpace hdet n hr hc
      have hd : M.nxt c₀ = d := nxt_of_step hdet hs hna
      refine ⟨m + 1, fun t' ht' => ?_, by rw [Function.iterate_succ_apply, hd]; exact ha⟩
      rcases t' with _ | t'
      · exact h0
      · rw [Function.iterate_succ_apply, hd]; exact hm t' (by omega)

/-- **Acceptance read off the truncated tableau** (deterministic machines). -/
theorem tabT_accept_iff (hdet : ∀ q γ, (M.step q γ).Subsingleton) :
    (∃ t i, i < S ∧ ∃ q ∈ M.accept, ∃ γ, tabT M S u t i = (some q, γ)) ↔ M.AcceptsInSpace u S := by
  constructor
  · rintro ⟨t, i, hi, q, hq, γ, h⟩
    -- the head stays below `S` up to `t`
    have hall : ∀ t' ≤ t, (M.run u t').head < S := by
      by_contra hc
      push_neg at hc
      obtain ⟨t0, ht0, hS⟩ := hc
      classical
      let P : ℕ → Prop := fun t' => t' ≤ t ∧ S ≤ (M.run u t').head
      have hP : ∃ t', P t' := ⟨t0, ht0, hS⟩
      let t1 := Nat.find hP
      have ht1 : P t1 := Nat.find_spec hP
      have hmin : ∀ t' < t1, (M.run u t').head < S := fun t' ht' => by
        have := Nat.find_min hP ht'
        simp only [P, not_and, not_le] at this
        exact this (by have := ht1.1; omega)
      have hrow : ∀ j < S, (tabT M S u t1 j).1 = none := by
        intro j hj
        rw [tabT_eq_tab M S u t1 hmin j hj]
        simp only [tab]
        rw [if_neg (by have := ht1.2; omega)]
      have := tabT_noHead_after M S u hrow (t - t1) i hi
      rw [show t1 + (t - t1) = t by have := ht1.1; omega, h] at this
      simp at this
    have he := tabT_eq_tab M S u t (fun t' ht' => hall t' ht'.le) i hi
    rw [h] at he
    obtain ⟨-, hst⟩ := tab_fst_eq_some M (by rw [← he])
    obtain ⟨n, hn⟩ := reachesSpace_run M S u t hall
    exact ⟨n, _, hn, hst ▸ hq⟩
  · rintro ⟨n, c, hr, hc⟩
    obtain ⟨m, hm, ha⟩ := iterate_of_reachesSpace M S hdet n hr hc
    have hm' : ∀ t' ≤ m, (M.run u t').head < S := hm
    refine ⟨m, (M.run u m).head, hm' m le_rfl, _, ha, (M.run u m).tape (M.run u m).head, ?_⟩
    rw [tabT_eq_tab M S u m (fun t' ht' => hm' t' ht'.le) _ (hm' m le_rfl)]
    exact tab_head M u m

/-! ### The existential start -/

/-- `AccW t i`: some cell `j ≥ i` below `S` shows an accepting state at time `t - (j - i)`
(with at least one step to go). -/
def AccW : ℕ → ℕ → Prop
  | 0, _ => False
  | t + 1, i => (∃ q ∈ M.accept, ∃ γ, tabT M S u (t + 1) i = (some q, γ)) ∨ (i + 1 < S ∧ AccW t (i + 1))

theorem accW_sound : ∀ t i, i < S → AccW M S u t i →
    ∃ t' j, j < S ∧ ∃ q ∈ M.accept, ∃ γ, tabT M S u t' j = (some q, γ) := by
  intro t
  induction t with
  | zero => intro i _ h; exact h.elim
  | succ t ih =>
    intro i hi h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨t + 1, i, hi, h⟩
    · exact ih (i + 1) h1 h2

theorem accW_complete {t j : ℕ} (hj : j < S) {q : Q} (hq : q ∈ M.accept) {γ : Γ}
    (h : tabT M S u t j = (some q, γ)) : ∀ d i, j = i + d → AccW M S u (t + 1 + d) i := by
  intro d
  induction d with
  | zero =>
    intro i hij; subst hij
    exact Or.inl ⟨q, hq, γ, tabT_frozen M S u hq h⟩
  | succ d ih =>
    intro i hij
    exact Or.inr ⟨by omega, ih (i + 1) (by omega)⟩

theorem exists_accW_iff (hS : 0 < S) :
    (∃ t, AccW M S u t 0) ↔ ∃ t' j, j < S ∧ ∃ q ∈ M.accept, ∃ γ, tabT M S u t' j = (some q, γ) := by
  constructor
  · rintro ⟨t, h⟩; exact accW_sound M S u t 0 hS h
  · rintro ⟨t, j, hj, q, hq, γ, h⟩
    exact ⟨_, accW_complete M S u hj hq h j 0 (by omega)⟩

end

end DBG

end FOND
