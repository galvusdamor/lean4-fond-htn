import ComplexityTheory.TOtoHD.Amp.Loop
/-!
# The amplifier: setting up the levels

`setup_run`: from `start`, the vector addition system can fill the pairs of every level `≤ L`
(`B k` tokens on each `false` side) and produce exactly the budgets needed later, leaving
`dz` tests and `2 B L dz` moves of level `L` for the simulation of the counter machine.
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

/-- The pairs of level `k` at rest. -/
def Lv (k : ℕ) : Mk := B k • δ (.side k false false) + B k • δ (.side k true false)

mutual
/-- The pairs of the levels `< k` at rest. -/
def Rb : ℕ → Mk
  | 0 => 0
  | k + 1 => Rr k
/-- The pairs of the levels `≤ k` at rest. -/
def Rr : ℕ → Mk
  | k => Rb k + Lv k
end

theorem Rr_eq (k : ℕ) : Rr k = Rb k + Lv k := by rw [Rr]

theorem Rb_succ (k : ℕ) : Rb (k + 1) = Rr k := by rw [Rb]

/-- A budget of `x` tests (and the matching `2 B k x` moves) of level `k`. -/
def Bd (k x : ℕ) : Mk := x • δ (.d k) + (2 * B k * x) • δ (.c k)

/-- The number of tests per multiplication loop over level `k`. -/
def DL (k : ℕ) : ℕ := 2 * B k + 2

/-- The number of tests of each level needed when the machine performs `dz` zero tests, counted
from level `L` downwards. -/
def ddA (L dz : ℕ) : ℕ → ℕ
  | 0 => dz
  | j + 1 => (2 + 2 * ddA L dz j) * DL (L - j - 1)

/-- The number of tests of level `k` needed. -/
def dd (L dz k : ℕ) : ℕ := ddA L dz (L - k)

theorem dd_L (L dz : ℕ) : dd L dz L = dz := by simp [dd, ddA]

theorem dd_lt {L dz k : ℕ} (hk : k < L) :
    dd L dz k = DL k + DL k + dd L dz (k + 1) * (2 * DL k) := by
  have h : L - k = (L - (k + 1)) + 1 := by omega
  simp only [dd, h, ddA]
  rw [show L - (L - (k + 1)) - 1 = k by omega]
  ring

section levels

variable {P : CM Q Φ} {L : ℕ} {S : Finset Φ}

/-- One budget round of level `k + 1`. -/
theorem round_run {k : ℕ} (hk : k < L) (j y : ℕ) :
    Reach P L (.bl (k + 1), S, Rr (k + 1) + Bd k ((j + 1) * (2 * DL k)) + Bd (k + 1) y)
      (.bl (k + 1), S, Rr (k + 1) + Bd k (j * (2 * DL k)) + Bd (k + 1) (y + 1)) := by
  have h0 := astep0 (S := S) (IsRule.blBud (P := P) k hk)
    (m := Rr (k + 1) + Bd k ((j + 1) * (2 * DL k)) + Bd (k + 1) y)
    (m' := Rr (k + 1) + Bd k ((j + 1) * (2 * DL k)) + Bd (k + 1) y + δ (.d (k + 1)))
    (fun p => by simp) (by rw [Rr_eq, Rb_succ, Rr_eq]; simp only [Lv, Bd]; mk_eq')
  have h1 := loop_run (P := P) (S := S) (s := .bud false) hk
  simp only [after, tgt] at h1
  have h1' := reach_frame h1
    (m0 := Rb k + Lv (k + 1) + Bd k (j * (2 * DL k) + DL k) + Bd (k + 1) y + δ (.d (k + 1)))
    (m := Rr (k + 1) + Bd k ((j + 1) * (2 * DL k)) + Bd (k + 1) y + δ (.d (k + 1)))
    (m' := Rr (k + 1) + Bd k (j * (2 * DL k) + DL k) + Bd (k + 1) y + δ (.d (k + 1)) +
      B (k + 1) • δ (.c (k + 1)))
    (by rw [Rr_eq, Rb_succ, Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
    (by rw [Rr_eq, Rb_succ, Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
  have h2 := loop_run (P := P) (S := S) (s := .bud true) hk
  simp only [after, tgt] at h2
  have h2' := reach_frame h2
    (m0 := Rb k + Lv (k + 1) + Bd k (j * (2 * DL k)) + Bd (k + 1) y + δ (.d (k + 1)) +
      B (k + 1) • δ (.c (k + 1)))
    (m := Rr (k + 1) + Bd k (j * (2 * DL k) + DL k) + Bd (k + 1) y + δ (.d (k + 1)) +
      B (k + 1) • δ (.c (k + 1)))
    (m' := Rr (k + 1) + Bd k (j * (2 * DL k)) + Bd (k + 1) (y + 1))
    (by rw [Rr_eq, Rb_succ, Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
    (by rw [Rr_eq, Rb_succ, Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
  exact (h1'.head h0).trans h2'

theorem rounds_run {k : ℕ} (hk : k < L) : ∀ j y : ℕ,
    Reach P L (.bl (k + 1), S, Rr (k + 1) + Bd k (j * (2 * DL k)) + Bd (k + 1) y)
      (.bl (k + 1), S, Rr (k + 1) + Bd k 0 + Bd (k + 1) (y + j)) := by
  intro j
  induction j with
  | zero => intro y; apply reach_of_eq; simp
  | succ j ih =>
    intro y
    have := ih (y + 1)
    rw [show y + 1 + j = y + (j + 1) by omega] at this
    exact (round_run hk j y).trans this

/-- **From level `k` to level `k + 1`.** -/
theorem level_step {dz k : ℕ} (hk : k < L) :
    Reach P L (.bl k, S, Rr k + Bd k (dd L dz k))
      (.bl (k + 1), S, Rr (k + 1) + Bd (k + 1) (dd L dz (k + 1))) := by
  rw [dd_lt hk]
  set x := dd L dz (k + 1)
  have h0 := astep0 (S := S) (IsRule.blNext (P := P) k hk)
    (m := Rr k + Bd k (DL k + DL k + x * (2 * DL k)))
    (m' := Rr k + Bd k (DL k + DL k + x * (2 * DL k)))
    (fun p => by simp) (mv_nn _)
  have h1 := loop_run (P := P) (S := S) (s := .comp false) hk
  simp only [after, tgt] at h1
  have h1' := reach_frame h1
    (m0 := Rb k + Bd k (DL k + x * (2 * DL k)))
    (m := Rr k + Bd k (DL k + DL k + x * (2 * DL k)))
    (m' := Rr k + Bd k (DL k + x * (2 * DL k)) + B (k + 1) • δ (.side (k + 1) false false))
    (by rw [Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
    (by rw [Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
  have h2 := loop_run (P := P) (S := S) (s := .comp true) hk
  simp only [after, tgt] at h2
  have h2' := reach_frame h2
    (m0 := Rb k + Bd k (x * (2 * DL k)) + B (k + 1) • δ (.side (k + 1) false false))
    (m := Rr k + Bd k (DL k + x * (2 * DL k)) + B (k + 1) • δ (.side (k + 1) false false))
    (m' := Rr (k + 1) + Bd k (x * (2 * DL k)) + Bd (k + 1) 0)
    (by rw [Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
    (by rw [Rr_eq (k + 1), Rb_succ, Rr_eq]; simp only [Lv, Bd, DL]; mk_eq')
  have h3 := rounds_run (P := P) (S := S) hk x 0
  refine ((h1'.head h0).trans h2').trans (h3.trans (reach_of_eq ?_))
  congr 2
  simp only [Bd]; mk_eq'

theorem bl0_run (x : ℕ) :
    Reach P L (.bl 0, S, Rr 0 + Bd 0 0) (.bl 0, S, Rr 0 + Bd 0 x) := by
  induction x with
  | zero => exact .refl
  | succ x ih =>
    refine ih.tail (astep0 IsRule.bl0 (fun p => by simp) ?_)
    simp only [Rr_eq, Rb, Lv, Bd, B_zero]; mk_eq'

/-- **Setting up all levels.** -/
theorem setup_run (dz : ℕ) :
    Reach P L (.start, S, 0) (.bl L, S, Rr L + Bd L dz) := by
  have h0 := astep0 (S := S) (IsRule.start (P := P) (L := L)) (m := 0)
    (m' := Rr 0 + Bd 0 0) (fun p => by simp)
    (by simp only [Rr_eq, Rb, Lv, Bd, B_zero]; mk_eq')
  have h1 := bl0_run (P := P) (L := L) (S := S) (dd L dz 0)
  have key : ∀ k ≤ L, Reach P L (.bl 0, S, Rr 0 + Bd 0 (dd L dz 0))
      (.bl k, S, Rr k + Bd k (dd L dz k)) := by
    intro k
    induction k with
    | zero => intro _; exact .refl
    | succ k ih => intro hk; exact (ih (by omega)).trans (level_step (by omega))
  have h2 := key L le_rfl
  rw [dd_L] at h2
  exact (h1.head h0).trans h2

end levels

end Amp

end HTN
