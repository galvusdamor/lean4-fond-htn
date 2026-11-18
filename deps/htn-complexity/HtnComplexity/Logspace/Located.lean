import HtnComplexity.PT.Core
import ComplexityTheory.Lang.LogCalc
/-!
# Strings located in the input at a stride

The bit codes of descriptions nest self-delimiting strings (`HTN.Syn.bstr`: every bit `b` is
written `true, b`, then `false` ends the string).  The content of a string nested `d` times sits
in the input at an arithmetic progression of stride `2^d`.  So a value of the code is reached by a
**location** `(d, p)`: its bit `k` is the input bit `p + 2^d k` (`HTN.Logspace.rd`).

* `HTN.Logspace.virt y d p L` — the `L` bits at the location (`false` beyond the input);
* `HTN.Logspace.LocS y d p w` — the string `w` is written at the location;
* `HTN.Logspace.LocS.layer` — the content of a self-delimiting string written at `(d, p)` is
  written at `(d + 1, p + 2^d)`;
* the terms `HTN.Logspace.posT`, `HTN.Logspace.btT`: the input position of a bit of a located
  string and the bit itself (`HTN.Logspace.eval_btT`).
-/

namespace HTN

namespace Logspace

open Cx Cx.LTerm Syn

/-! ### Located strings -/

/-- Bit `k` of the location `(d, p)`. -/
def rd (y : List Bool) (d p k : ℕ) : Bool := y.getD (p + 2 ^ d * k) false

/-- The first `L` bits of the location `(d, p)`. -/
def virt (y : List Bool) (d p L : ℕ) : List Bool := (List.range L).map (rd y d p)

/-- Bit `i` of a string, `false` beyond its end. -/
def bt (w : List Bool) (i : ℕ) : Bool := w.getD i false

@[simp] theorem length_virt (y : List Bool) (d p L : ℕ) : (virt y d p L).length = L := by
  simp [virt]

theorem bt_virt (y : List Bool) (d p L i : ℕ) :
    bt (virt y d p L) i = (decide (i < L) && rd y d p i) := by
  unfold bt virt
  by_cases h : i < L
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem virt_add (y : List Bool) (d p a b : ℕ) :
    virt y d p (a + b) = virt y d p a ++ virt y d (p + 2 ^ d * a) b := by
  simp only [virt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, rd]
  congr 1; ring

theorem virt_drop (y : List Bool) (d p L s : ℕ) :
    (virt y d p L).drop s = virt y d (p + 2 ^ d * s) (L - s) := by
  rcases Nat.le_total s L with h | h
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [virt_add, List.drop_left' (by simp)]
    congr 1; omega
  · rw [List.drop_eq_nil_of_le (by simpa using h), Nat.sub_eq_zero_of_le h]
    rfl

/-- **`w` is written at the location `(d, p)`.** -/
def LocS (y : List Bool) (d p : ℕ) (w : List Bool) : Prop :=
  ∀ k < w.length, p + 2 ^ d * k < y.length ∧ rd y d p k = w.getD k false

variable {y : List Bool} {d p : ℕ}

theorem LocS.virt_eq {w : List Bool} (h : LocS y d p w) : virt y d p w.length = w := by
  apply List.ext_getElem (by simp)
  intro k hk _
  simp only [virt, List.getElem_map, List.getElem_range]
  rw [(h k (by simpa using hk)).2, List.getD_eq_getElem _ _ (by simpa using hk)]

theorem LocS.length_le {w : List Bool} (h : LocS y d p w) : w.length ≤ y.length := by
  rcases Nat.eq_zero_or_pos w.length with h0 | h0
  · omega
  · have := (h (w.length - 1) (by omega)).1
    have : w.length - 1 ≤ 2 ^ d * (w.length - 1) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos d)
    omega

/-- **A located string is a prefix of the bits of its location.** -/
theorem LocS.virt_append {w : List Bool} (h : LocS y d p w) {L : ℕ} (hL : w.length ≤ L) :
    virt y d p L = w ++ virt y d (p + 2 ^ d * w.length) (L - w.length) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hL
  rw [virt_add, h.virt_eq]
  congr 2; omega

theorem LocS.append {w₁ w₂ : List Bool} :
    LocS y d p (w₁ ++ w₂) ↔ LocS y d p w₁ ∧ LocS y d (p + 2 ^ d * w₁.length) w₂ := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · obtain ⟨h1, h2⟩ := h k (by simp; omega)
      exact ⟨h1, by rw [h2, List.getD_append _ _ _ _ hk]⟩
    · obtain ⟨h1, h2⟩ := h (w₁.length + k) (by simp; omega)
      refine ⟨by rw [mul_add] at h1; omega, ?_⟩
      unfold rd at h2 ⊢
      rw [show p + 2 ^ d * w₁.length + 2 ^ d * k = p + 2 ^ d * (w₁.length + k) by ring, h2,
        List.getD_append_right _ _ _ _ (by omega)]
      congr 1; omega
  · rintro ⟨h1, h2⟩ k hk
    by_cases hk1 : k < w₁.length
    · obtain ⟨e1, e2⟩ := h1 k hk1
      exact ⟨e1, by rw [e2, List.getD_append _ _ _ _ hk1]⟩
    · obtain ⟨e1, e2⟩ := h2 (k - w₁.length) (by simp at hk; omega)
      have hk' : p + 2 ^ d * w₁.length + 2 ^ d * (k - w₁.length) = p + 2 ^ d * k := by
        rw [add_assoc, ← mul_add]; congr 2; omega
      refine ⟨by rw [hk'] at e1; exact e1, ?_⟩
      unfold rd at e2 ⊢
      rw [hk'] at e2
      rw [e2, List.getD_append_right _ _ _ _ (by omega)]

theorem bstr_getD_odd : ∀ (c : List Bool) (j : ℕ), j < c.length →
    (bstr c).getD (2 * j + 1) false = c.getD j false := by
  intro c
  induction c with
  | nil => intro j hj; simp at hj
  | cons b c ih =>
    intro j hj
    cases j with
    | zero => simp [bstr]
    | succ j =>
      have := ih j (by simpa using hj)
      simp only [bstr, List.foldr_cons] at this ⊢
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring]
      simpa using this

theorem bstr_getD_even : ∀ (c : List Bool) (j : ℕ), j ≤ c.length →
    (bstr c).getD (2 * j) false = decide (j < c.length) := by
  intro c
  induction c with
  | nil => intro j hj; simp at hj; subst hj; simp [bstr]
  | cons b c ih =>
    intro j hj
    cases j with
    | zero => simp [bstr]
    | succ j =>
      have := ih j (by simpa using hj)
      simp only [bstr, List.foldr_cons] at this ⊢
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simpa using this

theorem length_bstr (c : List Bool) : (bstr c).length = 2 * c.length + 1 := by
  induction c with
  | nil => simp [bstr]
  | cons b c ih => simp only [bstr, List.foldr_cons, List.length_cons] at ih ⊢; omega

/-- **Entering a self-delimiting string.** -/
theorem LocS.layer {c r : List Bool} (h : LocS y d p (bstr c ++ r)) : LocS y (d + 1) (p + 2 ^ d) c := by
  have hb := (LocS.append.1 h).1
  intro k hk
  have hl := length_bstr c
  obtain ⟨e1, e2⟩ := hb (2 * k + 1) (by omega)
  have hpos : p + 2 ^ d * (2 * k + 1) = p + 2 ^ d + 2 ^ (d + 1) * k := by ring
  refine ⟨by rw [hpos] at e1; exact e1, ?_⟩
  unfold rd at e2 ⊢
  rw [← hpos, e2, bstr_getD_odd c k hk]

/-! ### Terms -/

/-- `2^d · t` (saturated). -/
def mulPow : ℕ → LTerm → LTerm
  | 0, t => .add t (.lit 0)
  | d + 1, t => let u := mulPow d t; .add u u

/-- The input position `p + 2^d k` of bit `k` of the location `(d, p)`. -/
def posT (d : ℕ) (p k : LTerm) : LTerm := .add p (mulPow d k)

/-- Bit `i` of the first `L` bits of the location `(d, p)`. -/
def btT (d : ℕ) (p L i : LTerm) : LTerm := and (.lt i L) (.bit (posT d p i))

variable {x : List Bool} {M : ℕ}

theorem eval_mulPow (env : List ℕ) (t : LTerm) :
    ∀ d, eval x M env (mulPow d t) = min (2 ^ d * eval x M env t) M := by
  intro d
  induction d with
  | zero => simp [mulPow, eval]
  | succ d ih =>
    simp only [mulPow, eval, ih, pow_succ]
    rcases le_total (2 ^ d * eval x M env t) M with h | h
    · rw [min_eq_left h]; ring_nf
    · rw [min_eq_right h]
      have : M ≤ 2 ^ d * 2 * eval x M env t := by nlinarith
      omega

theorem eval_posT (env : List ℕ) (d : ℕ) (p k : LTerm) :
    eval x M env (posT d p k) = min (eval x M env p + 2 ^ d * eval x M env k) M := by
  simp only [posT, eval, eval_mulPow]
  omega

theorem rd_min (hM : y.length ≤ M) (d p i : ℕ) : y.getD (min (p + 2 ^ d * i) M) false = rd y d p i := by
  unfold rd
  rcases le_total (p + 2 ^ d * i) M with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem bt_virt_min {L : ℕ} (hL : L ≤ M) (i : ℕ) : bt (virt y d p L) (min i M) = bt (virt y d p L) i := by
  rw [bt_virt, bt_virt]
  rcases le_total i M with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]; simp [show ¬ M < L by omega, show ¬ i < L by omega]

/-- **The meaning of `btT`.** -/
theorem eval_btT (hM : x.length ≤ M) (env : List ℕ) (d : ℕ) (p L i : LTerm) :
    eval x M env (btT d p L i) =
      if bt (virt x d (eval x M env p) (eval x M env L)) (eval x M env i) then 1 else 0 := by
  simp only [btT, eval_and, eval, eval_posT, rd_min hM, bt_virt]
  by_cases h : eval x M env i < eval x M env L <;> by_cases h' : rd x d (eval x M env p) (eval x M env i) <;>
    simp [h, h']

end Logspace

end HTN
