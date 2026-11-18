import Mathlib

/-!
# Nested path schemes and their polynomial-time check

A vector addition system with states is given by transitions `t` with a source and a target
control state (`src t`, `tgt t`) and an effect `eff t : P → ℤ`.  A step from `(h, x)` with
`h = src t` goes to `(tgt t, x + eff t)` if the result is non-negative.

A **nested path scheme** is a transition, a concatenation of two schemes, or an iteration
`S^e`.  Its *effect* `Δ` and its *minimal prefix effect* `μ` (componentwise minimum over all
prefixes, `0` included) are computed by recursion; the iteration needs only the first and the
last round:

* `μ (S₁ · S₂) = min (μ S₁) (Δ S₁ + μ S₂)`,
* `μ (S^(e+1)) = μ S + min 0 (e · Δ S)`,

componentwise.

* **`HTN.RegRounds.Scheme.run_of_ok`** — if a scheme is well formed for the control (`ctrlOK`)
  and `x + μ S ≥ 0`, then its unfolding is a run from `(h, x)` to `(h', x + Δ S)`.

With the exponents in binary, `Δ` and `μ` are computed in time polynomial in the size of the
scheme.  So nested schemes are certificates for long but regular runs (PROOFIDEAS §15.12): a
Lipton zero test at level `j` is a loop nest of depth `j`.
-/

namespace HTN

namespace RegRounds

namespace Scheme

variable {H P T : Type*}

/-- A vector addition system with states, by its transitions. -/
structure Sys (H P T : Type*) where
  src : T → H
  tgt : T → H
  eff : T → P → ℤ

/-- **Nested path schemes.** -/
inductive Sch (T : Type*) where
  | tr (t : T)
  | cat (a b : Sch T)
  | it (a : Sch T) (e : ℕ)

variable (V : Sys H P T)

/-- One step: the source control state, a non-negative result. -/
def Step (c c' : H × (P → ℤ)) : Prop :=
  ∃ t, c.1 = V.src t ∧ c'.1 = V.tgt t ∧ c'.2 = c.2 + V.eff t ∧ 0 ≤ c'.2

/-- The effect of a scheme. -/
def eff : Sch T → (P → ℤ)
  | .tr t => V.eff t
  | .cat a b => eff a + eff b
  | .it a e => (e : ℤ) • eff a

/-- The minimal prefix effect of a scheme (`0` for the empty prefix), componentwise. -/
def mpe : Sch T → (P → ℤ)
  | .tr t => fun p => min 0 (V.eff t p)
  | .cat a b => fun p => min (mpe a p) (eff V a p + mpe b p)
  | .it _ 0 => 0
  | .it a (e + 1) => fun p => mpe a p + min 0 ((e : ℤ) * eff V a p)

/-- A scheme fits the control from `h` to `h'`; iterated parts are closed. -/
def ctrlOK : Sch T → H → H → Prop
  | .tr t, h, h' => V.src t = h ∧ V.tgt t = h'
  | .cat a b, h, h' => ∃ h₁, ctrlOK a h h₁ ∧ ctrlOK b h₁ h'
  | .it _ 0, h, h' => h = h'
  | .it a (_ + 1), h, h' => h = h' ∧ ctrlOK a h h

theorem eff_it (a : Sch T) (e : ℕ) (p : P) : eff V (.it a e) p = (e : ℤ) * eff V a p := by
  simp [eff]

/-- **A checked scheme unfolds to a run.** -/
theorem run_of_ok : ∀ (S : Sch T) (h h' : H) (x : P → ℤ), ctrlOK V S h h' →
    (∀ p, 0 ≤ x p + mpe V S p) → Relation.ReflTransGen (Step V) (h, x) (h', x + eff V S)
  | .tr t, h, h', x, ⟨hs, ht⟩, hx => by
    refine Relation.ReflTransGen.single ⟨t, hs.symm, ht.symm, rfl, fun p => ?_⟩
    have := hx p
    simp only [mpe] at this
    show 0 ≤ x p + V.eff t p
    have : min 0 (V.eff t p) ≤ V.eff t p := min_le_right _ _
    linarith [hx p, show mpe V (.tr t) p = min 0 (V.eff t p) from rfl]
  | .cat a b, h, h', x, ⟨h₁, ha, hb⟩, hx => by
    have hxa : ∀ p, 0 ≤ x p + mpe V a p := fun p => by
      have h1 := hx p
      have h2 : mpe V (.cat a b) p ≤ mpe V a p := min_le_left _ _
      linarith
    have hxb : ∀ p, 0 ≤ (x + eff V a) p + mpe V b p := fun p => by
      have h1 := hx p
      have h2 : mpe V (.cat a b) p ≤ eff V a p + mpe V b p := min_le_right _ _
      simp only [Pi.add_apply]
      linarith
    have r1 := run_of_ok a h h₁ x ha hxa
    have r2 := run_of_ok b h₁ h' (x + eff V a) hb hxb
    have e1 : x + eff V a + eff V b = x + eff V (.cat a b) := by
      simp [eff, add_assoc]
    rw [e1] at r2
    exact r1.trans r2
  | .it a 0, h, h', x, hc, _ => by
    subst hc
    have : x + eff V (.it a 0) = x := by funext p; simp [eff]
    rw [this]
  | .it a (e + 1), h, h', x, ⟨hh, ha⟩, hx => by
    subst hh
    -- every round starts at `x + i • Δ` with `i ≤ e`; it stays non-negative because the
    -- minimum over the rounds is attained at `i = 0` or `i = e`.
    have key : ∀ i ≤ e + 1, Relation.ReflTransGen (Step V) (h, x) (h, x + (i : ℤ) • eff V a) := by
      intro i
      induction i with
      | zero =>
        intro _
        have : x + ((0 : ℕ) : ℤ) • eff V a = x := by funext p; simp
        rw [this]
      | succ i ih =>
        intro hi
        have r := ih (by omega)
        have hround : ∀ p, 0 ≤ (x + (i : ℤ) • eff V a) p + mpe V a p := by
          intro p
          have hp : 0 ≤ x p + (mpe V a p + min 0 ((e : ℤ) * eff V a p)) := hx p
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have hmin : min 0 ((e : ℤ) * eff V a p) ≤ (i : ℤ) * eff V a p := by
            rcases le_or_gt 0 (eff V a p) with hpos | hneg
            · exact (min_le_left _ _).trans (mul_nonneg (by positivity) hpos)
            · have hie : (i : ℤ) ≤ e := by exact_mod_cast (by omega : i ≤ e)
              have : (e : ℤ) * eff V a p ≤ (i : ℤ) * eff V a p := by nlinarith
              exact (min_le_right _ _).trans this
          linarith
        have r2 := run_of_ok a h h (x + (i : ℤ) • eff V a) ha hround
        have : x + (i : ℤ) • eff V a + eff V a = x + ((i + 1 : ℕ) : ℤ) • eff V a := by
          funext p; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
        rw [this] at r2
        exact r.trans r2
    have := key (e + 1) le_rfl
    have e2 : x + ((e + 1 : ℕ) : ℤ) • eff V a = x + eff V (.it a (e + 1)) := by
      funext p; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eff_it]
    rw [e2] at this
    exact this

end Scheme

end RegRounds

end HTN
