import FondHtn.Cx.Exp2
import ComplexityTheory.Machine.PTime
import ComplexityTheory.TM.Tableau
/-!
# The tableau game: an alternating source for `2-EXPTIME`

The Chandra–Kozen–Stockmeyer check of the tableau of a deterministic computation as a game:

* `FOND.ATM.TabWin F row0 t i σ` — the existential player claims that the entry of cell `i` at
  time `t` is `σ`; at time `0` the claim is checked against the first row; at time `t + 1` the
  existential player names the three entries `l, c, r` of the cells `i - 1, i, i + 1` at time
  `t` with `F l c r = σ`, and the universal player picks one of the three claims to continue
  with (the conjunction).
* `FOND.ATM.tabWin_iff` — **the claim wins iff it is true**: `TabWin t i σ ↔ σ = tabF t i`, the
  tableau defined by the local rule.
* **`FOND.ATM.exptime2_tabWin`** — every language of `2-EXPTIME` (`HTN.Cx.EXPTIME2`: a doubly
  exponential padding is in `P`) is characterised by the tableau game of a fixed deterministic
  single-tape machine `M` on the padded input: `x ∈ L` iff for some cell `i ≤ T x` and some
  accepting entry the existential player wins the claim at time `T x = r(|padExp2 q x|)`.

Positions of the game are `(t, i, σ)` with `t, i ≤ T x`, numbers of `O(2 ^ q(|x|))` bits, and the
game lasts `T x` (doubly exponentially many) rounds: an alternating exponential-space
computation (`AEXPSPACE = 2-EXPTIME`).  The first row is given locally by the input:
`row0 x i = (if i = 0 then some q₀ else none, (padExp2 q x).getD i)`, where
`padExp2 q x = x.flatMap (b ↦ [b, b]) ++ [false, true] ++ 1^(2^2^q(|x|))`.
-/

namespace FOND

namespace ATM

open HTN TM

section Game

variable {S : Type} (F : Option S → S → S → S) (row0 : ℕ → S)

/-- **The tableau game.** -/
def TabWin : ℕ → ℕ → S → Prop
  | 0, i, σ => σ = row0 i
  | t + 1, i, σ => ∃ l c r : S, F (if i = 0 then none else some l) c r = σ ∧
      (i ≠ 0 → TabWin t (i - 1) l) ∧ TabWin t i c ∧ TabWin t (i + 1) r

/-- The tableau of the local rule. -/
def tabF : ℕ → ℕ → S
  | 0, i => row0 i
  | t + 1, i => F (if i = 0 then none else some (tabF t (i - 1))) (tabF t i) (tabF t (i + 1))

/-- **A claim wins iff it is true.** -/
theorem tabWin_iff : ∀ t i σ, TabWin F row0 t i σ ↔ σ = tabF F row0 t i := by
  intro t
  induction t with
  | zero => intro i σ; rfl
  | succ t ih =>
    intro i σ
    simp only [TabWin, tabF]
    constructor
    · rintro ⟨l, c, r, hF, hl, hc, hr⟩
      rw [(ih i c).1 hc, (ih (i + 1) r).1 hr] at hF
      rw [← hF]
      by_cases hi : i = 0
      · simp [hi]
      · simp only [hi, if_false]
        rw [(ih (i - 1) l).1 (hl hi)]
    · rintro rfl
      exact ⟨tabF F row0 t (i - 1), tabF F row0 t i, tabF F row0 t (i + 1), by
        by_cases hi : i = 0 <;> simp [hi], fun _ => (ih _ _).2 rfl, (ih _ _).2 rfl,
        (ih _ _).2 rfl⟩

end Game

section Machine

variable {Q Γ : Type} (M : NTM Q Γ)

/-- The tableau of a run is the tableau of the local rule `M.F`. -/
theorem tab_eq_tabF (w : List Γ) : ∀ t i, M.tab w t i = tabF M.F (M.tab w 0) t i := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    rw [NTM.tab_succ, tabF, ih, ih, ih]

end Machine

/-! ## `2-EXPTIME` -/

theorem padExp2_inj {q : Polynomial ℕ} {x x' : List Bool} (h : Cx.padExp2 q x = Cx.padExp2 q x') :
    x = x' := by
  have := congrArg (fun y => (Syn.PolyDom.unpairS y).1) h
  simpa [Cx.padExp2, Syn.PolyDom.unpairS_pairStr] using this

/-- The first row of the tableau of `M` on the padded input. -/
noncomputable def row0 {k : ℕ} (M : NTM (Fin k) (Option Bool)) (q : Polynomial ℕ)
    (x : List Bool) (i : ℕ) : NTM.CSym (Fin k) (Option Bool) :=
  (if i = 0 then some M.init else none, ((Cx.padExp2 q x).map some).getD i M.blank)

/-- **Every `2-EXPTIME` language is characterised by the tableau game of a deterministic
machine on the doubly exponentially padded input.** -/
theorem exptime2_tabWin {L : Cx.Language} (hL : Cx.EXPTIME2 L) :
    ∃ (k : ℕ) (M : NTM (Fin k) (Option Bool)) (q r : Polynomial ℕ),
      M.blank = none ∧ (∀ q γ, (M.step q γ).Subsingleton) ∧ ∀ x,
        L x ↔ ∃ i ≤ r.eval (Cx.padExp2 q x).length, ∃ qa ∈ M.accept, ∃ γ,
          TabWin M.F (row0 M q x) (r.eval (Cx.padExp2 q x).length) i (some qa, γ) := by
  obtain ⟨q, hP⟩ := hL
  obtain ⟨k, M, r, hblank, hdet, hM⟩ := Mach.exists_dtm_of_inP hP
  refine ⟨k, M, q, r, hblank, hdet, fun x => ?_⟩
  have hrow : M.tab ((Cx.padExp2 q x).map some) 0 = row0 M q x := by
    funext i; rw [NTM.tab_zero]; rfl
  have key : ∀ T, (M.run ((Cx.padExp2 q x).map some) T).state ∈ M.accept ↔
      ∃ i ≤ T, ∃ qa ∈ M.accept, ∃ γ, TabWin M.F (row0 M q x) T i (some qa, γ) := by
    intro T
    rw [NTM.run_accept_iff_tab]
    refine exists_congr fun i => and_congr_right fun _ => exists_congr fun qa =>
      and_congr_right fun _ => exists_congr fun γ => ?_
    rw [tabWin_iff, tab_eq_tabF, hrow, eq_comm]
  constructor
  · intro hx
    have hacc := (hM _).1 ⟨x, rfl, hx⟩
    rw [NTM.acceptsWithin_iff_run hdet] at hacc
    exact (key _).1 hacc
  · intro h
    have hacc := (NTM.acceptsWithin_iff_run hdet _ _).2 ((key _).2 h)
    obtain ⟨n, -, c, hr, hc⟩ := hacc
    obtain ⟨x', hx', hLx'⟩ := (hM _).2 ⟨n, c, hr, hc⟩
    rw [padExp2_inj hx']; exact hLx'

end ATM

end FOND
