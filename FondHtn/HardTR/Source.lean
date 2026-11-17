import FondHtn.ATM.Tableau
import ComplexityTheory.Machine.Logic
/-!
# CB22 Thm 5, package P5: the source with counters of `2 ^ e(|x|)` bits

* **`FOND.HardTR.exptime2_tabWin_pow`** — every `2-EXPTIME` language is characterised by the
  tableau game of a fixed deterministic machine started at the time `2 ^ B - 1` (all ones) with
  `B = 2 ^ e(|x|)`, `e` a polynomial: `x ∈ L` iff the existential player wins the claim
  `(2 ^ B - 1, i, (some qa, γ))` for some cell `i < 2 ^ B` and accepting entry.  The time
  counter therefore starts as `B` ones, which an encoding generates without knowing the exact
  running time (the run is frozen once accepting).
* **Counters as bit lists** (least significant bit first), updated by one left-to-right pass with
  a borrow (`FOND.HardTR.decB`) or a carry (`FOND.HardTR.incB`) — exactly the passes an encoding
  performs bit by bit: `natOfBits_decB`, `natOfBits_incB`, `isZeroB_iff`.
-/

namespace FOND

namespace HardTR

open HTN TM ATM PTime

/-! ## The width -/

/-- **Every `2-EXPTIME` language, with the time counter starting at `2 ^ 2 ^ e(|x|) - 1`.** -/
theorem exptime2_tabWin_pow {L : Cx.Language} (hL : Cx.EXPTIME2 L) :
    ∃ (k : ℕ) (M : NTM (Fin k) (Option Bool)) (q e : Polynomial ℕ),
      M.blank = none ∧ (∀ q γ, (M.step q γ).Subsingleton) ∧ ∀ x,
        L x ↔ ∃ i < 2 ^ 2 ^ e.eval x.length, ∃ qa ∈ M.accept, ∃ γ,
          TabWin M.F (row0 M q x) (2 ^ 2 ^ e.eval x.length - 1) i (some qa, γ) := by
  obtain ⟨q, hP⟩ := hL
  obtain ⟨k, M, r, hblank, hdet, hM⟩ := Mach.exists_dtm_of_inP hP
  obtain ⟨c, hc⟩ := exists_pow_bound r
  let e : Polynomial ℕ := q + Polynomial.X + Polynomial.C (c + 3)
  refine ⟨k, M, q, e, hblank, hdet, fun x => ?_⟩
  set n := x.length
  set Q := q.eval n
  set B := 2 ^ e.eval n with hB
  have heB : e.eval n = Q + n + (c + 3) := by simp [e, Q, n]
  -- the running time fits
  have hT : r.eval (Cx.padExp2 q x).length < 2 ^ B := by
    have hN : (Cx.padExp2 q x).length + 1 ≤ 2 ^ (2 ^ Q + n + 2) := by
      simp only [Cx.padExp2, Syn.pairStr, List.length_append, List.length_flatMap,
        List.length_cons, List.length_nil, List.length_replicate]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul]
      rw [pow_add, pow_add]
      have h1 : n < 2 ^ n := Nat.lt_two_pow_self
      have h2 : 1 ≤ 2 ^ 2 ^ Q := Nat.one_le_two_pow
      nlinarith
    have h1 := hc (Cx.padExp2 q x).length
    have h2 : c * ((Cx.padExp2 q x).length + 1) ^ c ≤ 2 ^ c * (2 ^ (2 ^ Q + n + 2)) ^ c :=
      Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hN c)
    have h3 : 2 ^ c * (2 ^ (2 ^ Q + n + 2)) ^ c = 2 ^ (c + (2 ^ Q + n + 2) * c) := by
      rw [← pow_mul, ← pow_add]
    have h4 : c + (2 ^ Q + n + 2) * c < B := by
      rw [hB, heB]
      have e1 : 2 ^ Q + n + 3 ≤ 2 ^ (Q + n + 2) := by
        rw [pow_add, pow_add]
        have := Nat.lt_two_pow_self (n := n)
        have : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
        nlinarith
      have e2 : c < 2 ^ c := Nat.lt_two_pow_self
      have e3 : (2 ^ Q + n + 3) * c ≤ 2 ^ (Q + n + 2) * 2 ^ c := Nat.mul_le_mul e1 e2.le
      have e4 : 2 ^ (Q + n + 2) * 2 ^ c * 2 ≤ 2 ^ (Q + n + (c + 3)) := by
        rw [← pow_add, ← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have e5 : 1 ≤ 2 ^ (Q + n + 2) * 2 ^ c := Nat.one_le_iff_ne_zero.2 (by positivity)
      nlinarith
    calc r.eval (Cx.padExp2 q x).length ≤ 2 ^ (c + (2 ^ Q + n + 2) * c) := h1.trans (h3 ▸ h2)
      _ < 2 ^ B := Nat.pow_lt_pow_right (by norm_num) h4
  have hrow : M.tab ((Cx.padExp2 q x).map some) 0 = row0 M q x := by
    funext i; rw [NTM.tab_zero]; rfl
  have key : (M.run ((Cx.padExp2 q x).map some) (2 ^ B - 1)).state ∈ M.accept ↔
      ∃ i < 2 ^ B, ∃ qa ∈ M.accept, ∃ γ, TabWin M.F (row0 M q x) (2 ^ B - 1) i (some qa, γ) := by
    rw [NTM.run_accept_iff_tab]
    have hpos : 0 < 2 ^ B := Nat.two_pow_pos _
    constructor
    · rintro ⟨i, hi, qa, hqa, γ, h⟩
      refine ⟨i, by omega, qa, hqa, γ, ?_⟩
      rw [tabWin_iff, ← h, tab_eq_tabF, hrow]
    · rintro ⟨i, hi, qa, hqa, γ, h⟩
      refine ⟨i, by omega, qa, hqa, γ, ?_⟩
      rw [tabWin_iff] at h
      rw [h, tab_eq_tabF, hrow]
  constructor
  · intro hx
    have hacc := (hM _).1 ⟨x, rfl, hx⟩
    have hacc' := NTM.acceptsWithin_mono M (show r.eval (Cx.padExp2 q x).length ≤
      2 ^ B - 1 by omega) hacc
    rw [NTM.acceptsWithin_iff_run hdet] at hacc'
    exact key.1 hacc'
  · intro h
    obtain ⟨n', -, c', hr, hc'⟩ := (NTM.acceptsWithin_iff_run hdet _ _).2 (key.2 h)
    obtain ⟨x', hx', hLx'⟩ := (hM _).2 ⟨n', c', hr, hc'⟩
    rw [padExp2_inj hx']; exact hLx'

/-! ## Counters as bit lists -/

/-- Subtract the borrow `bo`, least significant bit first. -/
def decB : Bool → List Bool → List Bool
  | _, [] => []
  | bo, b :: l => (xor b bo) :: decB (bo && !b) l

/-- Add the carry `co`, least significant bit first. -/
def incB : Bool → List Bool → List Bool
  | _, [] => []
  | co, b :: l => (xor b co) :: incB (co && b) l

/-- The zero test. -/
def isZeroB (l : List Bool) : Bool := l.all fun b => !b

theorem length_decB : ∀ (bo : Bool) (l : List Bool), (decB bo l).length = l.length
  | _, [] => rfl
  | bo, b :: l => by simp [decB, length_decB]

theorem length_incB : ∀ (co : Bool) (l : List Bool), (incB co l).length = l.length
  | _, [] => rfl
  | co, b :: l => by simp [incB, length_incB]

theorem natOfBits_decB : ∀ (bo : Bool) (l : List Bool), (if bo then 1 else 0) ≤ natOfBits l →
    natOfBits (decB bo l) = natOfBits l - (if bo then 1 else 0)
  | bo, [], h => by cases bo <;> simp_all [decB]
  | bo, b :: l, h => by
    have ih := natOfBits_decB (bo && !b) l
    cases bo <;> cases b <;> simp_all [decB, natOfBits_cons]
    all_goals omega

theorem natOfBits_incB : ∀ (co : Bool) (l : List Bool),
    natOfBits l + (if co then 1 else 0) < 2 ^ l.length →
    natOfBits (incB co l) = natOfBits l + (if co then 1 else 0)
  | co, [], h => by cases co <;> simp_all [incB]
  | co, b :: l, h => by
    have ih := natOfBits_incB (co && b) l
    simp only [List.length_cons, pow_succ] at h
    cases co <;> cases b <;> simp_all [incB, natOfBits_cons] <;> omega

theorem isZeroB_iff (l : List Bool) : isZeroB l = true ↔ natOfBits l = 0 := by
  induction l with
  | nil => simp [isZeroB]
  | cons b l ih =>
    simp only [isZeroB, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at ih ⊢
    rw [ih, natOfBits_cons]
    cases b <;> simp

end HardTR

end FOND
