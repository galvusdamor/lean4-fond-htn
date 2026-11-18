import Mathlib

/-!
# Polynomially and exponentially bounded functions

* `HTN.ACHD.PB f` — `f n ≤ a (n + 1)^c`; closed under constants, `+`, `*`, composition;
* `HTN.ACHD.EB f` — `f n ≤ 2^(E n)` with `PB E`; closed under `+`, `*`, `x^E`, polynomials;
* `HTN.ACHD.pb_log` — the logarithm of an exponentially bounded function is polynomially
  bounded;
* `HTN.ACHD.PB.exists_poly` — a polynomially bounded function is bounded by a polynomial.
-/

namespace HTN

namespace ACHD

/-- **Polynomially bounded.** -/
def PB (f : ℕ → ℕ) : Prop := ∃ c a : ℕ, ∀ n, f n ≤ a * (n + 1) ^ c

namespace PB

theorem const (k : ℕ) : PB fun _ => k := ⟨0, k, fun n => by simp⟩

theorem id : PB fun n => n := ⟨1, 1, fun n => by simp⟩

theorem mono {f g : ℕ → ℕ} (hg : PB g) (h : ∀ n, f n ≤ g n) : PB f := by
  obtain ⟨c, a, hc⟩ := hg; exact ⟨c, a, fun n => (h n).trans (hc n)⟩

theorem add {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB fun n => f n + g n := by
  obtain ⟨c₁, a₁, h₁⟩ := hf
  obtain ⟨c₂, a₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, a₁ + a₂, fun n => ?_⟩
  have e1 : (n + 1) ^ c₁ ≤ (n + 1) ^ (c₁ + c₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (n + 1) ^ c₂ ≤ (n + 1) ^ (c₁ + c₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have := h₁ n; have := h₂ n
  nlinarith

theorem mul {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB fun n => f n * g n := by
  obtain ⟨c₁, a₁, h₁⟩ := hf
  obtain ⟨c₂, a₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, a₁ * a₂, fun n => ?_⟩
  calc f n * g n ≤ (a₁ * (n + 1) ^ c₁) * (a₂ * (n + 1) ^ c₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = a₁ * a₂ * (n + 1) ^ (c₁ + c₂) := by ring

theorem pow {f : ℕ → ℕ} (hf : PB f) (k : ℕ) : PB fun n => f n ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem comp {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB fun n => f (g n) := by
  obtain ⟨c₁, a₁, h₁⟩ := hf
  obtain ⟨c₂, a₂, h₂⟩ := hg
  refine ⟨c₂ * c₁, a₁ * (a₂ + 1) ^ c₁, fun n => ?_⟩
  have hb : g n + 1 ≤ (a₂ + 1) * (n + 1) ^ c₂ := by
    have := h₂ n
    have : 1 ≤ (n + 1) ^ c₂ := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc f (g n) ≤ a₁ * (g n + 1) ^ c₁ := h₁ _
    _ ≤ a₁ * ((a₂ + 1) * (n + 1) ^ c₂) ^ c₁ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
    _ = a₁ * (a₂ + 1) ^ c₁ * (n + 1) ^ (c₂ * c₁) := by rw [mul_pow, ← pow_mul]; ring

theorem poly (p : Polynomial ℕ) : PB fun n => p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.eval_add] using hp.add hq
  | monomial k a =>
    refine ⟨k, a, fun n => ?_⟩
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- **A polynomially bounded function is bounded by a polynomial.** -/
theorem exists_poly {f : ℕ → ℕ} (hf : PB f) : ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n := by
  obtain ⟨c, a, h⟩ := hf
  exact ⟨Polynomial.C a * (Polynomial.X + 1) ^ c, fun n => by simpa using h n⟩

end PB

/-- **Exponentially bounded**: `f n ≤ 2^(E n)` with `E` polynomially bounded. -/
def EB (f : ℕ → ℕ) : Prop := ∃ E : ℕ → ℕ, PB E ∧ ∀ n, f n ≤ 2 ^ E n

namespace EB

theorem of_pb {f : ℕ → ℕ} (hf : PB f) : EB f :=
  ⟨f, hf, fun n => (Nat.lt_two_pow_self).le⟩

theorem mono {f g : ℕ → ℕ} (hg : EB g) (h : ∀ n, f n ≤ g n) : EB f := by
  obtain ⟨E, hE, hg⟩ := hg; exact ⟨E, hE, fun n => (h n).trans (hg n)⟩

theorem add {f g : ℕ → ℕ} (hf : EB f) (hg : EB g) : EB fun n => f n + g n := by
  obtain ⟨E₁, hE₁, h₁⟩ := hf
  obtain ⟨E₂, hE₂, h₂⟩ := hg
  refine ⟨fun n => E₁ n + E₂ n + 1, (hE₁.add hE₂).add (PB.const 1), fun n => ?_⟩
  have a1 : 2 ^ E₁ n ≤ 2 ^ (E₁ n + E₂ n) := Nat.pow_le_pow_right (by omega) (by omega)
  have a2 : 2 ^ E₂ n ≤ 2 ^ (E₁ n + E₂ n) := Nat.pow_le_pow_right (by omega) (by omega)
  have := h₁ n; have := h₂ n
  show f n + g n ≤ _
  rw [pow_succ]; omega

theorem mul {f g : ℕ → ℕ} (hf : EB f) (hg : EB g) : EB fun n => f n * g n := by
  obtain ⟨E₁, hE₁, h₁⟩ := hf
  obtain ⟨E₂, hE₂, h₂⟩ := hg
  refine ⟨fun n => E₁ n + E₂ n, hE₁.add hE₂, fun n => ?_⟩
  rw [pow_add]; exact Nat.mul_le_mul (h₁ n) (h₂ n)

/-- A polynomially bounded base to a polynomially bounded power. -/
theorem pow {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : EB fun n => f n ^ g n := by
  refine ⟨fun n => f n * g n, hf.mul hg, fun n => ?_⟩
  calc f n ^ g n ≤ (2 ^ f n) ^ g n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
    _ = 2 ^ (f n * g n) := by rw [← pow_mul]

/-- A polynomial of an exponentially bounded function. -/
theorem poly (p : Polynomial ℕ) {f : ℕ → ℕ} (hf : EB f) : EB fun n => p.eval (f n) := by
  obtain ⟨c, a, hp⟩ := PB.poly p
  obtain ⟨E, hE, h⟩ := hf
  refine ⟨fun n => a + c * (E n + 1), (PB.const a).add ((PB.const c).mul (hE.add (PB.const 1))),
    fun n => ?_⟩
  have h1 : f n + 1 ≤ 2 ^ (E n + 1) := by
    have := h n; have : 1 ≤ 2 ^ E n := Nat.one_le_two_pow; rw [pow_succ]; omega
  calc p.eval (f n) ≤ a * (f n + 1) ^ c := hp _
    _ ≤ 2 ^ a * (2 ^ (E n + 1)) ^ c :=
        Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left h1 _)
    _ = 2 ^ (a + c * (E n + 1)) := by rw [← pow_mul, ← pow_add, mul_comm (E n + 1)]

end EB

/-- **The logarithm of an exponentially bounded function is polynomially bounded.** -/
theorem pb_log {f : ℕ → ℕ} (hf : EB f) : PB fun n => Nat.log 2 (f n) := by
  obtain ⟨E, hE, h⟩ := hf
  refine hE.mono fun n => ?_
  rcases Nat.eq_zero_or_pos (f n) with h0 | hpos
  · simp [h0]
  · have := Nat.log_mono_right (b := 2) (h n)
    rwa [Nat.log_pow (by norm_num)] at this

end ACHD

end HTN
