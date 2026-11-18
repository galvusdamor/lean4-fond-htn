import FondHtn.HardTR.Row
import FondHtn.HardTR.Source
/-!
# CB22 Thm 5, P3a: soundness of the tableau transducer for the source

* `FOND.HardTR.exptime2_tabWin_pow'` — `exptime2_tabWin_pow` (`Source.lean`) with the size bound
  `2 ^ q(n) + n + 3 ≤ 2 ^ e(n)` (the same proof).
* `FOND.HardTR.TT.row0_long`, `row0_blank` — the first row on the padded input is constant on the
  padding ones and on the blanks.
* `FOND.HardTR.TT.srcSpec` — the transducer parameters for the input `x`.
* **`FOND.HardTR.TT.src_sound`** — a won boot round of the transducer for `x` gives `x ∈ L`.
-/

namespace FOND

namespace HardTR

open HTN TM ATM PTime

theorem exptime2_tabWin_pow' {L : Cx.Language} (hL : Cx.EXPTIME2 L) :
    ∃ (k : ℕ) (M : NTM (Fin k) (Option Bool)) (q e : Polynomial ℕ),
      M.blank = none ∧ (∀ q γ, (M.step q γ).Subsingleton) ∧
      (∀ n, 2 ^ q.eval n + n + 3 ≤ 2 ^ e.eval n) ∧ ∀ x,
        L x ↔ ∃ i < 2 ^ 2 ^ e.eval x.length, ∃ qa ∈ M.accept, ∃ γ,
          TabWin M.F (row0 M q x) (2 ^ 2 ^ e.eval x.length - 1) i (some qa, γ) := by
  obtain ⟨q, hP⟩ := hL
  obtain ⟨k, M, r, hblank, hdet, hM⟩ := Mach.exists_dtm_of_inP hP
  obtain ⟨c, hc⟩ := exists_pow_bound r
  let e : Polynomial ℕ := q + Polynomial.X + Polynomial.C (c + 3)
  refine ⟨k, M, q, e, hblank, hdet, fun n => ?_, fun x => ?_⟩
  · have he : e.eval n = q.eval n + (n + 3) + c := by simp [e]; ring
    rw [he, pow_add, pow_add]
    have h1 : n + 4 ≤ 2 ^ (n + 3) := by
      have := Nat.lt_two_pow_self (n := n + 3); omega
    have h2 : 1 ≤ 2 ^ q.eval n := Nat.one_le_two_pow
    have h4 : 2 ^ q.eval n * (n + 4) ≤ 2 ^ q.eval n * 2 ^ (n + 3) := Nat.mul_le_mul_left _ h1
    have h5 : 2 ^ q.eval n * 2 ^ (n + 3) ≤ 2 ^ q.eval n * 2 ^ (n + 3) * 2 ^ c :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have h6 : n + 3 ≤ 2 ^ q.eval n * (n + 3) := Nat.le_mul_of_pos_left _ (by positivity)
    nlinarith
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


namespace TT

theorem getD_map_some (l : List Bool) (i : ℕ) : (l.map some).getD i none = l[i]? := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem length_padExp2 (q : Polynomial ℕ) (x : List Bool) :
    (Cx.padExp2 q x).length = rA x.length (2 ^ q.eval x.length) := by
  simp only [Cx.padExp2, Syn.pairStr, List.length_append, List.length_flatMap, List.length_cons,
    List.length_nil, List.length_replicate, rA]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  ring

theorem padExp2_long (q : Polynomial ℕ) (x : List Bool) {i : ℕ} (h1 : 2 * x.length + 1 ≤ i)
    (h2 : i < rA x.length (2 ^ q.eval x.length)) : (Cx.padExp2 q x)[i]? = some true := by
  have hl : (x.flatMap fun b => [b, b]).length = 2 * x.length := by
    simp only [List.length_flatMap, List.length_cons, List.length_nil]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]; ring
  simp only [Cx.padExp2, Syn.pairStr]
  rw [List.append_assoc, List.getElem?_append_right (by omega), hl]
  unfold rA at h2
  by_cases hi : i = 2 * x.length + 1
  · subst hi; simp
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil]
    rw [List.getElem?_replicate, if_pos (by omega)]

theorem padExp2_blank (q : Polynomial ℕ) (x : List Bool) {i : ℕ}
    (h : rA x.length (2 ^ q.eval x.length) ≤ i) : (Cx.padExp2 q x)[i]? = none :=
  List.getElem?_eq_none (by rw [length_padExp2]; exact h)

variable {k : ℕ} (M : NTM (Fin k) (Option Bool)) (q : Polynomial ℕ) (x : List Bool)

variable {M} in
theorem row0_long (hb : M.blank = none) {i : ℕ} (h1 : 2 * x.length + 1 ≤ i) (h2 : i < rA x.length (2 ^ q.eval x.length)) :
    row0 M q x i = row0 M q x (2 * x.length + 1) := by
  have h2' : 2 * x.length + 1 < rA x.length (2 ^ q.eval x.length) := Nat.lt_of_le_of_lt h1 h2
  unfold row0
  rw [if_neg (by omega), if_neg (by omega), hb, getD_map_some, getD_map_some,
    padExp2_long q x h1 h2, padExp2_long q x le_rfl h2']

variable {M} in
theorem row0_blank (hb : M.blank = none) {i : ℕ} (h : rA x.length (2 ^ q.eval x.length) ≤ i) :
    row0 M q x i = row0 M q x (rA x.length (2 ^ q.eval x.length)) := by
  have h0 : 0 < rA x.length (2 ^ q.eval x.length) := by
    unfold rA; exact Nat.add_pos_left (by omega) _
  unfold row0
  rw [if_neg (by omega), if_neg (by omega), hb, getD_map_some, getD_map_some,
    padExp2_blank q x h, padExp2_blank q x le_rfl]

/-- The accepting claims. -/
def accSet : Set (NTM.CSym (Fin k) (Option Bool)) := {σ | ∃ qa ∈ M.accept, ∃ γ, σ = (some qa, γ)}

/-- **The transducer parameters for the input `x`.** -/
noncomputable def srcSpec (e : Polynomial ℕ) : Spec (NTM.CSym (Fin k) (Option Bool)) :=
  rowSpec M.F (row0 M q x) (accSet M) (e.eval x.length) x.length (2 ^ q.eval x.length)

variable {M q x} in
theorem srcSpec_valid {e : Polynomial ℕ} (hb : M.blank = none)
    (hB : ∀ n, 2 ^ q.eval n + n + 3 ≤ 2 ^ e.eval n) : (srcSpec M q x e).Valid :=
  rowSpec_valid (hB x.length) (fun _ h1 h2 => row0_long q x hb h1 h2)
    (fun _ h => row0_blank q x hb h)

variable {M q x} in
/-- **Soundness of the tableau transducer for the source**: a won boot round gives `x ∈ L`. -/
theorem src_sound {L : Cx.Language} {e : Polynomial ℕ} (hb : M.blank = none)
    (hB : ∀ n, 2 ^ q.eval n + n + 3 ≤ 2 ^ e.eval n)
    (hL : L x ↔ ∃ i < 2 ^ 2 ^ e.eval x.length, ∃ qa ∈ M.accept, ∃ γ,
      TabWin M.F (row0 M q x) (2 ^ 2 ^ e.eval x.length - 1) i (some qa, γ))
    {ρ y : Bool} {σ : NTM.CSym (Fin k) (Option Bool)}
    (h : (srcSpec M q x e).mach.Win {TL.cfg ρ 0 0} ⟨.wb 0, 0, ρ, y, g0 σ⟩) : L x := by
  obtain ⟨σ', ⟨qa, hqa, γ, rfl⟩, i, hi, htab⟩ := Spec.boot_win (srcSpec_valid hb hB) h
  exact hL.2 ⟨i, hi, qa, hqa, γ, htab⟩

end TT

end HardTR

end FOND
