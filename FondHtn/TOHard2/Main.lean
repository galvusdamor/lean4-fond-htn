import FondHtn.TOHard2.PT
import FondHtn.Cx.Exp2
import FondHtn.MPStrong.TODesc
/-!
# Totally ordered MP strong plan existence is 2-EXPTIME-hard

**`FOND.TOHard2.hard_TO_mpStrong`**: `PlanExMP .strong FClass.TO` is 2-EXPTIME-hard (ideas file,
"Total order — hardness"; construction `doc/notes_to_hard.md`); with `FOND.strongMP_TO_mem`,
**`FOND.TOHard2.complete_TO_mpStrong`**: it is 2-EXPTIME-complete.

A language `L` of 2-EXPTIME has a doubly exponential padding in `P`, decided by a deterministic
single-tape machine `M` in polynomial time `r`.  On the padded word of length
`c₂ = 2|x| + 2 + 2 ^ E`, `E = 2 ^ q(|x|)`, the run takes fewer than `2 ^ D` steps for
`D = 2 ^ b`, `b` polynomial in `|x|`; the description `desc (parOf M b E x)` checks the tableau of
the run with numbers of `D` digits (`FOND.TOHard2.mpStrong_parOf_iff`).
-/

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HTN.Syn.PolyDom PTime TM

/-- The bound on the padded length. -/
theorem c₂_le (q : Polynomial ℕ) (n : ℕ) :
    2 * n + 1 + 1 + 2 ^ 2 ^ q.eval n ≤ 2 ^ 2 ^ (q + Polynomial.X + 2).eval n := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  set E := 2 ^ q.eval n with hE
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  have h2 : E + n + 2 ≤ 2 ^ (q + Polynomial.X + 2).eval n := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, pow_add, ← hE]
    have : n + 2 < 2 ^ n * 2 ^ 2 := by nlinarith
    nlinarith
  refine le_trans ?_ (Nat.pow_le_pow_right (by norm_num) h2)
  have h3 : 2 * n + 2 ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
  have h4 : 2 ^ (n + 1) ≤ 2 ^ (E + n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ E ≤ 2 ^ (E + n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show E + n + 2 = (E + n + 1) + 1 by omega, pow_succ]; omega

theorem padExp2_eq (q : Polynomial ℕ) (x : List Bool) :
    Cx.padExp2 q x = Cx.padExp (Polynomial.C (2 ^ q.eval x.length)) x := by
  simp [Cx.padExp2, Cx.padExp]

/-- `2 ^ min E m` as a list computation. -/
theorem pow_min_eq (E m : ℕ) :
    natOfBits (((List.range m).filter fun r => decide (r < E)).map (fun _ => false) ++ [true]) =
      2 ^ min E m := by
  rw [List.map_const', natOfBits_pow]
  congr 1
  rcases le_total E m with h | h
  · rw [range_filter_lt h, List.length_range, min_eq_left h]
  · rw [List.filter_eq_self.2 (fun r hr => by simp at hr; simp; omega), List.length_range,
      min_eq_right h]

section PTx

variable {α : Type} [BEnc α]

theorem pt_onesL {c : α → ℕ} (hc : PT c) : PT fun a => onesL (c a) := by
  unfold onesL
  exact PT.filter (PT.rangeLength (PT.bits.comp hc)) (PT.getI (PT.bits.comp (hc.comp PT.fst)) PT.snd)

theorem pt_onesPow {A E : α → ℕ} (hA : PT A) (hE : PT E) : PT fun a => onesPow (A a) (E a) := by
  unfold onesPow
  have hlen : PT fun a => (bitsOfNat (A a)).length := PT.length (PT.bits.comp hA)
  have hpow : PT fun a => 2 ^ min (E a) (bitsOfNat (A a)).length :=
    (PT.ofBits (PT.append (PT.map (PT.filter (p := fun a r => decide (r < E a))
      (PT.rangeLength (PT.bits.comp hA))
      (PT.lt PT.snd (hE.comp PT.fst))) (g := fun _ _ => false) (PT.const false)) (PT.const [true]))).of_eq fun a =>
        pow_min_eq _ _
  exact PT.ite (PT.le hlen hE) (PT.append (pt_onesL hA) (PT.single hE)) (pt_onesL (PT.add hA hpow))

end PTx

/-- **The reduction is computed in polynomial time.** -/
theorem pt_red {k : ℕ} (M : NTM (Fin k) (Option Bool)) {Bl Nl : List Bool → List Unit} (hBl : PT Bl)
    (hNl : PT Nl) : PT fun x => desc (parOf M (Bl x).length (2 ^ (Nl x).length) x) := by
  have hp := pt_prefW
  have hE : PT fun x : List Bool => 2 ^ (Nl x).length :=
    (PT.ofBits (PT.append (PT.map (g := fun _ _ => false) hNl (PT.const false)) (PT.const [true]))).of_eq
      fun x => by rw [List.map_const', natOfBits_pow]
  have hL : PT fun x : List Bool => (prefW x).length := PT.length hp
  refine pt_desc (P := fun x => parOf M (Bl x).length (2 ^ (Nl x).length) x)
    ((PT.rangeLength hBl).of_eq fun x => rfl) ?_ (PT.const _) (PT.const _) (PT.const _) (PT.const _) ?_
    (PT.const _) (PT.const _)
  · show PT fun x => csOf (2 ^ (Nl x).length) x
    unfold csOf
    exact PT.append (PT.cons (pt_onesL hL) (PT.single (pt_onesPow (PT.succ hL) hE)))
      (PT.map (PT.rangeLength hp) (pt_onesL PT.snd))
  · show PT fun x => (List.range (prefW x).length).map (baseCode M.init.val x)
    refine PT.map (PT.rangeLength hp) ?_
    unfold baseCode
    exact PT.add (PT.ite (PT.eq PT.snd (PT.const 0)) (PT.const _) (PT.const 0))
      (PT.ite (PT.eq (PT.getI (hp.comp PT.fst) PT.snd) (PT.const true)) (PT.const 2) (PT.const 1))

/-- **Totally ordered strong method-based plan existence is 2-EXPTIME-hard** (ideas file). -/
theorem hard_TO_mpStrong : Cx.Hard Cx.EXPTIME2 (PlanExMP .strong FClass.TO) := by
  intro L ⟨q, hP⟩
  obtain ⟨k, M, r, hblank, hdet, hM⟩ := Mach.exists_dtm_of_inP hP
  set Q : Polynomial ℕ := q + Polynomial.X + 2 with hQ
  obtain ⟨q₁, hq₁⟩ := Mach.exists_two_pow_bound (Polynomial.X + r + 1) Polynomial.X
  obtain ⟨q₂, hq₂⟩ := Mach.exists_two_pow_bound q₁ Q
  obtain ⟨Bl, hBl, hBlen⟩ := PolyDom.exists_pt_polyLen (q₂ + 1)
  obtain ⟨Nl, hNl, hNlen⟩ := PolyDom.exists_pt_polyLen q
  -- the bound: `c₂ + r(c₂) < 2 ^ D`
  have hbound : ∀ x : List Bool, (prefW x).length + 1 + 2 ^ 2 ^ q.eval x.length +
      r.eval ((prefW x).length + 1 + 2 ^ 2 ^ q.eval x.length) < 2 ^ 2 ^ (Bl x).length := by
    intro x
    set n := x.length
    set c₂ := (prefW x).length + 1 + 2 ^ 2 ^ q.eval n
    have hc : c₂ ≤ 2 ^ Polynomial.X.eval (2 ^ Q.eval n) := by
      simp only [Polynomial.eval_X, c₂, length_prefW, n]
      have := c₂_le q x.length; omega
    have h1 := hq₁ _ _ hc
    have h2 := hq₂ n (2 ^ Q.eval n) le_rfl
    have e1 : (Polynomial.X + r + 1).eval c₂ = c₂ + r.eval c₂ + 1 := by simp
    rw [e1] at h1
    have h3 : 2 ^ q₁.eval (2 ^ Q.eval n) ≤ 2 ^ 2 ^ q₂.eval n := Nat.pow_le_pow_right (by norm_num) h2
    have h4 : 2 ^ 2 ^ q₂.eval n < 2 ^ 2 ^ (Bl x).length := by
      rw [hBlen, Polynomial.eval_add, Polynomial.eval_one]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
    show c₂ + r.eval c₂ < 2 ^ 2 ^ (Bl x).length
    omega
  set f : List Bool → FProbDesc := fun x => desc (parOf M (Bl x).length (2 ^ (Nl x).length) x)
  have hf : PT f := pt_red M hBl hNl
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun x => ?_⟩
  show L x ↔ PlanExMP .strong FClass.TO (enc (f x))
  rw [planExMP_enc_iff]
  have hNx : (Nl x).length = q.eval x.length := hNlen x
  have hfx : f x = desc (parOf M (Bl x).length (2 ^ q.eval x.length) x) := by simp only [f, hNx]
  have hc₂ : (prefW x).length + 1 + 2 ^ 2 ^ q.eval x.length < 2 ^ 2 ^ (Bl x).length := by
    have := hbound x; omega
  rw [hfx, MPCrit.Solvable, mpStrong_parOf_iff M hdet hblank hc₂, ← padExp2_eq]
  have hlen : ((Cx.padExp2 q x).map some).length = (prefW x).length + 1 + 2 ^ 2 ^ q.eval x.length := by
    rw [padExp2_eq, List.length_map, padExp_eq]; simp; omega
  constructor
  · intro hx
    have hacc := (hM _).1 ⟨x, rfl, hx⟩
    refine ⟨desc_valid _, desc_TO _, NTM.acceptsWithin_mono M ?_ hacc⟩
    rw [List.length_map] at hlen
    rw [hlen]
    have := hbound x
    omega
  · rintro ⟨-, -, n, -, c, hr, hc⟩
    obtain ⟨x', hx', hLx'⟩ := (hM _).2 ⟨n, c, hr, hc⟩
    have : x = x' := by
      have := congrArg unpairS hx'
      simp only [Cx.padExp2, unpairS_pairStr, Prod.mk.injEq] at this
      exact this.1
    rwa [this]

/-- **Totally ordered strong method-based plan existence is 2-EXPTIME-complete.** -/
theorem complete_TO_mpStrong : Cx.Complete Cx.EXPTIME2 (PlanExMP .strong FClass.TO) :=
  ⟨strongMP_TO_mem, hard_TO_mpStrong⟩

end TOHard2

end FOND
