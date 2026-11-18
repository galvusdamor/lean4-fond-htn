import HtnComplexity.PT.Pred
/-!
# Division and remainder by a constant in the polynomial-time calculus

* `HTN.Syn.PolyDom.PT.subC` — subtracting a constant;
* `HTN.Syn.PolyDom.PT.divC`, `HTN.Syn.PolyDom.PT.modC` — division and remainder by a constant,
  computed by long division over the binary digits, most significant first.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime Compress TOPlan PolyInst

variable {α β γ δ σ : Type} [BEnc α] [BEnc β] [BEnc γ] [BEnc δ] [BEnc σ]

theorem PT.subC {f : α → ℕ} (hf : PT f) : ∀ c : ℕ, PT fun a => f a - c
  | 0 => hf
  | c + 1 => (PT.pred (PT.subC hf c)).of_eq fun a => by omega

/-- One step of long division by `c`: shift in the next binary digit. -/
def divStep (c : ℕ) (b : Bool) (s : ℕ × ℕ) : ℕ × ℕ :=
  if c ≤ 2 * s.2 + (if b then 1 else 0) then (2 * s.1 + 1, 2 * s.2 + (if b then 1 else 0) - c)
  else (2 * s.1, 2 * s.2 + (if b then 1 else 0))

theorem foldr_divStep {c : ℕ} (hc : 0 < c) :
    ∀ w : List Bool, w.foldr (divStep c) (0, 0) = (natOfBits w / c, natOfBits w % c)
  | [] => by simp
  | b :: w => by
    rw [List.foldr_cons, foldr_divStep hc w, natOfBits_cons]
    unfold divStep
    simp only
    have he1 : (if b = true then 1 else 0) ≤ 1 := by split <;> omega
    generalize (if b = true then 1 else 0) = e at he1 ⊢
    generalize natOfBits w = N
    have hq := Nat.div_add_mod N c
    have hr := Nat.mod_lt N hc
    split_ifs with h
    · have h1 : e + 2 * N = c * (2 * (N / c) + 1) + (2 * (N % c) + e - c) := by
        zify [h] at hq ⊢; nlinarith [hq]
      have h2 : 2 * (N % c) + e - c < c := by omega
      rw [h1, Nat.mul_add_div hc, Nat.mul_add_mod, Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2]
    · have h1 : e + 2 * N = c * (2 * (N / c)) + (2 * (N % c) + e) := by
        nlinarith [hq]
      have h2 : 2 * (N % c) + e < c := by omega
      rw [h1, Nat.mul_add_div hc, Nat.mul_add_mod, Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2]
      simp

theorem sz_two_mul_add_le (x e : ℕ) (he : e ≤ 1) : sz (2 * x + e) ≤ sz x + 2 := by
  have hmono : sz (2 * x + e) ≤ sz (2 * x + 1) := by
    rw [sz_nat, sz_nat]; have := length_bitsOfNat_mono (a := 2 * x + e) (b := 2 * x + 1) (by omega)
    omega
  have h1 : sz (2 * x + 1) = sz x + 2 := by
    rw [sz_nat, sz_nat]
    have : bitsOfNat (2 * x + 1) = true :: bitsOfNat x := by
      rw [show 2 * x + 1 = (2 * x) + 1 from rfl, bitsOfNat_succ]
      congr 1
      · simp
      · congr 1; omega
    rw [this]; simp; omega
  omega

theorem sz_sub_le (x c : ℕ) : sz (x - c) ≤ sz x := by
  rw [sz_nat, sz_nat]; have := length_bitsOfNat_mono (a := x - c) (b := x) (by omega); omega

theorem PT.divModC {f : α → ℕ} (hf : PT f) {c : ℕ} (hc : 0 < c) :
    PT fun a => (f a / c, f a % c) := by
  have hstep : PT fun q : α × Bool × (ℕ × ℕ) => divStep c q.2.1 q.2.2 := by
    unfold divStep
    have hr : PT fun q : α × Bool × (ℕ × ℕ) => 2 * q.2.2.2 + (if q.2.1 = true then 1 else 0) :=
      PT.add (PT.affine 2 0 (PT.snd.comp (PT.snd.comp PT.snd)) |>.of_eq fun _ => by ring)
        (PT.ite (PT.decBool (PT.fst.comp PT.snd)) (PT.const 1) (PT.const 0))
    exact PT.ite (PT.le (PT.const c) hr)
      (PT.pair (PT.affine 2 1 (PT.fst.comp (PT.snd.comp PT.snd))) (PT.subC hr c))
      (PT.pair (PT.affine 2 0 (PT.fst.comp (PT.snd.comp PT.snd)) |>.of_eq fun _ => by ring) hr)
  have hfold := PT.foldr (l := fun a => bitsOfNat (f a)) (init := fun _ => ((0 : ℕ), (0 : ℕ)))
    (g := fun _ b s => divStep c b s) (PT.bits.comp hf) (PT.const _) hstep (c := 0) (d := 4)
    (fun a s b _ => by
      simp only [pow_zero, mul_one]
      obtain ⟨q, r⟩ := s
      unfold divStep
      have he : (if b = true then 1 else 0) ≤ 1 := by split <;> omega
      generalize (if b = true then 1 else 0) = e at he ⊢
      simp only
      split_ifs <;> simp only [sz_prod]
      · have h1 := sz_two_mul_add_le q 1 le_rfl
        have h2 := sz_two_mul_add_le r _ he
        have h3 := sz_sub_le (2 * r + e) c
        omega
      · have h1 := sz_two_mul_add_le q 0 (by omega)
        have h2 := sz_two_mul_add_le r _ he
        simp only [add_zero] at h1
        omega)
  exact hfold.of_eq fun a => by
    simp only
    rw [foldr_divStep hc, natOfBits_bitsOfNat]

theorem PT.divC {f : α → ℕ} (hf : PT f) {c : ℕ} (hc : 0 < c) : PT fun a => f a / c :=
  PT.fst' (PT.divModC hf hc)

theorem PT.modC {f : α → ℕ} (hf : PT f) {c : ℕ} (hc : 0 < c) : PT fun a => f a % c :=
  PT.snd' (PT.divModC hf hc)

end PolyDom

end Syn

end HTN
