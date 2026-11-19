import FondHtn.TOHard2.FSound
import FondHtn.TOHard2.Main
import FondHtn.HardTR.TFair
import FondHtn.MPStrong.TOFair2Desc
/-!
# Totally ordered fair strong cyclic MP plan existence is 2-EXPTIME-hard

The reduction of `FondHtn/TOHard2/` (claims about the tableau of a doubly exponential run,
verified by challenged digit chains) is also sound for the fair reading of strong cyclic
solutions (`FondHtn/TOHard2/FSound.lean`): a fair policy of the description gives the fair list
game of the grammar (`FOND.TOHard2.fair_compile`), whose claims are sound
(`FOND.TOHard2.root_soundF`); strong solutions are fair.

* **`FOND.TOHard2.mpFair_desc_iff`** — fair solvability of the description is acceptance;
* **`FOND.TOHard2.hard_TO_mpFair`**, **`FOND.TOHard2.complete_TO_mpFair`** — with
  `FOND.fairMP_TO_mem`, `PlanExMPFair FClass.TO` is 2-EXPTIME-complete.
-/

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HTN.Syn.PolyDom PTime TM HardMP

/-- **Fair solvability of the description is acceptance.** -/
theorem mpFair_desc_iff {P : Par} {d : TabData} {tabC : ℕ → ℕ → ℕ} (H : Hyp P d tabC) :
    (desc P).toProblem.MPStrongCyclicFairSolvable ↔ ∃ i < 2 ^ d.B, tabC (2 ^ d.B - 1) i ∈ d.acc := by
  constructor
  · intro h
    obtain ⟨Y, hY, hr⟩ := fair_compile (gram_good P) (compile_valid (gram_good P) _ _) enc_s₀ h
    exact root_soundF H hY hr
  · intro h
    exact Problem.fair_of_mpStrongSolvable ((mpStrong_desc_iff H).2 h)

theorem mpFair_parOf_iff {k : ℕ} (M : NTM (Fin k) (Option Bool)) (hdet : ∀ q γ, (M.step q γ).Subsingleton)
    (hblank : M.blank = none) {b E : ℕ} {x : List Bool} (hc₂ : (prefW x).length + 1 + 2 ^ E < 2 ^ 2 ^ b) :
    (desc (parOf M b E x)).toProblem.MPStrongCyclicFairSolvable ↔
      M.AcceptsWithin ((Cx.padExp (Polynomial.C E) x).map some) (2 ^ 2 ^ b - 1) := by
  have H := hyp_parOf M hdet hblank hc₂
  rw [mpFair_desc_iff H, ← mpStrong_desc_iff H]
  exact mpStrong_parOf_iff M hdet hblank hc₂

/-- **Totally ordered fair strong cyclic MP plan existence is 2-EXPTIME-hard.** -/
theorem hard_TO_mpFair : Cx.Hard Cx.EXPTIME2 (PlanExMPFair FClass.TO) := by
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
  show L x ↔ PlanExMPFair FClass.TO (enc (f x))
  rw [HardTR.planExMPFair_enc_iff]
  have hNx : (Nl x).length = q.eval x.length := hNlen x
  have hfx : f x = desc (parOf M (Bl x).length (2 ^ q.eval x.length) x) := by simp only [f, hNx]
  have hc₂ : (prefW x).length + 1 + 2 ^ 2 ^ q.eval x.length < 2 ^ 2 ^ (Bl x).length := by
    have := hbound x; omega
  rw [hfx, mpFair_parOf_iff M hdet hblank hc₂, ← padExp2_eq]
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

/-- **Totally ordered fair strong cyclic MP plan existence is 2-EXPTIME-complete.** -/
theorem complete_TO_mpFair : Cx.Complete Cx.EXPTIME2 (PlanExMPFair FClass.TO) :=
  ⟨fairMP_TO_mem, hard_TO_mpFair⟩

end TOHard2

end FOND
