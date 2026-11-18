import FondHtn.AcycHard.InstPT
import FondHtn.StrongOD.Acyc
import FondHtn.MPStrong.Acyc
import FondHtn.MPStrong.CyclicAcyc
/-!
# Acyclic problems: EXPSPACE-hardness

* **`FOND.AcycHard.hard_ACYC_strongOD`** — `PlanExFM .strongOD FClass.ACYC` is EXPSPACE-hard
  ([CB21, Thm. 4.11]);
* **`FOND.AcycHard.hard_ACYC_mpStrong`** — `PlanExMP .strong FClass.ACYC` is EXPSPACE-hard
  ([CB22, Thm. 2]);
* **`FOND.AcycHard.hard_ACYC_mpFair`** — the same for strong cyclic fair method-based policies;

with the memberships, the three problems are EXPSPACE-complete.

A language of EXPSPACE is the Savitch game of a machine `N` with space `S = 2 ^ p(|w|)`
(`FOND.ATM.expspace_savWin`); the reduction maps `w` to the description of the Savitch instance
`FOND.AcycHard.Sav.instOf N P E₁ E₂ w` with `P = p(|w|)` and polynomial exponents `E₁, E₂`.
-/

namespace FOND

namespace AcycHard

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime TM Sav

/-! ## The exponents -/

theorem le_mul_two_pow (a L : ℕ) (ha : 1 ≤ a) : a + L + 1 ≤ a * 2 ^ (L + 1) := by
  have h : L + 2 ≤ 2 ^ (L + 1) := by
    induction L with
    | zero => norm_num
    | succ L ih => rw [pow_succ]; omega
  nlinarith

/-- The constant of the supply. -/
noncomputable def cD {k : ℕ} (N : NTM (Fin k) (Option Bool)) : ℕ :=
  (allSyms k).length + (allSyms k).length * (accE N).length + (optsC N).length + 1

/-- **The bounds hold** for `E₁ = 2P + k + 4` and `E₂ = E₁ + P + L + D + 4`. -/
theorem bounds {k : ℕ} (N : NTM (Fin k) (Option Bool)) (P L E₁ E₂ : ℕ) (hE₁ : E₁ = 2 * P + k + 4)
    (hE₂ : E₂ = E₁ + P + L + cD N + 4) :
    (k + P + 2 * 2 ^ P + 2) * 2 ^ P ≤ 2 ^ E₁ ∧ E₁ ≤ E₂ ∧ 2 ^ P * 2 ^ P < 2 ^ E₂ ∧
      k + P + 2 * 2 ^ P < 2 ^ E₂ ∧
      2 ^ P * (2 * 2 ^ P + 1) + 2 ^ E₁ * ((allSyms k).length * (2 * 2 ^ P + 2) +
        ((L + 2) * ((allSyms k).length * (accE N).length) + (optsC N).length)) ≤ 2 ^ E₂ := by
  set S := 2 ^ P with hS
  have hS1 : 1 ≤ S := Nat.one_le_two_pow
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have hP : P < 2 ^ P := Nat.lt_two_pow_self
  have hkP : 2 ^ k ≤ 2 ^ (P + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPk : 2 ^ P ≤ 2 ^ (P + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hSS' : S * S = 2 ^ (2 * P) := by rw [hS, ← pow_add, two_mul]
  -- the first bound
  have hA : k + P + 2 * S + 2 ≤ 2 ^ (P + k + 4) := by
    have : 2 ^ (P + k + 4) = 16 * 2 ^ (P + k) := by rw [pow_add]; ring
    rw [this]; have : 1 ≤ 2 ^ (P + k) := Nat.one_le_two_pow; omega
  have h1 : (k + P + 2 * S + 2) * S ≤ 2 ^ E₁ := by
    have : 2 ^ E₁ = 2 ^ (P + k + 4) * S := by
      rw [hS, ← pow_add, hE₁]; congr 1; omega
    rw [this]; exact Nat.mul_le_mul_right _ hA
  have hE1 : 2 ^ E₁ ≤ 2 ^ E₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hSS : S * S < 2 ^ E₂ := by
    rw [hSS']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hKS : k + P + 2 * S < 2 ^ E₁ := by
    have : k + P + 2 * S < (k + P + 2 * S + 2) * S := by nlinarith
    omega
  refine ⟨h1, by omega, hSS, by omega, ?_⟩
  -- the size bound
  set cs := (allSyms k).length
  set ca := (accE N).length
  set cc := (optsC N).length
  set D := cD N with hDdef
  have hD : D < 2 ^ D := Nat.lt_two_pow_self
  have hcD : D = cs + cs * ca + cc + 1 := rfl
  have hX : cs * (2 * S + 2) + ((L + 2) * (cs * ca) + cc) ≤ (S + L + 1) * (2 * D) := by
    have b1 : 2 * S + 2 ≤ 2 * (S + L + 1) := by omega
    have b2 : L + 2 ≤ 2 * (S + L + 1) := by omega
    have a1 : cs * (2 * S + 2) ≤ cs * (2 * (S + L + 1)) := Nat.mul_le_mul_left _ b1
    have a2 : (L + 2) * (cs * ca) ≤ (2 * (S + L + 1)) * (cs * ca) := Nat.mul_le_mul_right _ b2
    have a3 : cc ≤ (2 * (S + L + 1)) * (cc + 1) := by nlinarith
    have e : (S + L + 1) * (2 * D) =
        cs * (2 * (S + L + 1)) + (2 * (S + L + 1)) * (cs * ca) + (2 * (S + L + 1)) * (cc + 1) := by
      rw [hcD]; ring
    omega
  have hY : S + L + 1 ≤ S * 2 ^ (L + 1) := le_mul_two_pow S L hS1
  have hZ : (S + L + 1) * (2 * D) ≤ 2 ^ (P + L + D + 2) := by
    have : 2 ^ (P + L + D + 2) = S * 2 ^ (L + 1) * (2 * 2 ^ D) := by
      rw [hS, show P + L + D + 2 = P + (L + 1) + (D + 1) by omega, pow_add, pow_add, pow_succ]
      ring
    rw [this]; exact Nat.mul_le_mul hY (by omega)
  obtain ⟨m, hm⟩ : ∃ m, E₂ = m + 2 := ⟨E₂ - 2, by omega⟩
  have hF : 2 ^ E₁ * 2 ^ (P + L + D + 2) = 2 ^ m := by
    rw [← pow_add]; congr 1; omega
  have hG : S * (2 * S + 1) ≤ 2 ^ m := by
    have h3 : 2 ^ (2 * P + 2) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (2 * P + 2) = 4 * 2 ^ (2 * P) := by rw [pow_add]; ring
    have h5 : S * (2 * S + 1) ≤ 4 * (S * S) := by nlinarith
    omega
  have hE2 : 2 ^ E₂ = 4 * 2 ^ m := by rw [hm, pow_add]; ring
  have hmul : 2 ^ E₁ * (cs * (2 * S + 2) + ((L + 2) * (cs * ca) + cc)) ≤ 2 ^ m := by
    rw [← hF]; exact Nat.mul_le_mul_left _ (hX.trans hZ)
  omega

/-! ## The reduction -/

/-- **The reduction**: an EXPSPACE language is decided by the Savitch instances. -/
theorem exists_red {L : Cx.Language} (hL : Cx.EXPSPACE L) :
    ∃ f : List Bool → FProbDesc, PT f ∧ ∀ w, (f w).Valid ∧ FClass.ACYC (f w).toProblem ∧
      (L w ↔ (f w).toProblem.StrongODSolvable) ∧ (L w ↔ (f w).toProblem.MPStrongSolvable) := by
  obtain ⟨k, N, p, hN⟩ := ATM.expspace_savWin hL
  set e₁ : Polynomial ℕ := 2 * p + Polynomial.C (k + 4)
  set e₂ : Polynomial ℕ := e₁ + p + Polynomial.X + Polynomial.C (cD N + 4)
  obtain ⟨Pl, hPl, hPlen⟩ := PolyDom.exists_pt_polyLen p
  obtain ⟨E₁l, hE₁, hE₁len⟩ := PolyDom.exists_pt_polyLen e₁
  obtain ⟨E₂l, hE₂, hE₂len⟩ := PolyDom.exists_pt_polyLen e₂
  refine ⟨fun w => (instOf N (Pl w).length (E₁l w).length (E₂l w).length w).desc,
    pt_descOf hPl hE₁ hE₂, fun w => ?_⟩
  beta_reduce
  set P := p.eval w.length
  have h1 : (E₁l w).length = 2 * P + k + 4 := by
    rw [hE₁len]; simp [e₁, P]; ring
  have h2 : (E₂l w).length = (2 * P + k + 4) + P + w.length + cD N + 4 := by
    rw [hE₂len]; simp [e₂, e₁, P]; ring
  rw [hPlen, h1, h2]
  obtain ⟨b1, b12, bSS, bK, b2⟩ := bounds N P w.length _ _ rfl rfl
  have hg := good_instOf w b1 b12 bSS bK b2
  refine ⟨Inst.valid _ (mem_allSyms none), Inst.acyc _, ?_, ?_⟩
  · rw [instOf_strongOD_iff hg, hN]
  · rw [instOf_mpStrong_iff hg, hN]

/-! ## The theorems -/

/-- **Strong OD plan existence for acyclic problems is EXPSPACE-hard** [CB21, Thm. 4.11]. -/
theorem hard_ACYC_strongOD : Cx.Hard Cx.EXPSPACE (PlanExFM .strongOD FClass.ACYC) := by
  intro L hL
  obtain ⟨f, hf, hfw⟩ := exists_red hL
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun w => ?_⟩
  show L w ↔ PlanExFM .strongOD FClass.ACYC (enc (f w))
  rw [planExFM_enc_iff]
  obtain ⟨hv, hac, hs, -⟩ := hfw w
  exact ⟨fun h => ⟨hv, hac, hs.1 h⟩, fun h => hs.2 h.2.2⟩

/-- **Strong method-based plan existence for acyclic problems is EXPSPACE-hard** [CB22, Thm. 2]. -/
theorem hard_ACYC_mpStrong : Cx.Hard Cx.EXPSPACE (PlanExMP .strong FClass.ACYC) := by
  intro L hL
  obtain ⟨f, hf, hfw⟩ := exists_red hL
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun w => ?_⟩
  show L w ↔ PlanExMP .strong FClass.ACYC (enc (f w))
  rw [planExMP_enc_iff]
  obtain ⟨hv, hac, -, hs⟩ := hfw w
  exact ⟨fun h => ⟨hv, hac, hs.1 h⟩, fun h => hs.2 h.2.2⟩

/-- **Strong cyclic fair method-based plan existence for acyclic problems is EXPSPACE-hard.** -/
theorem hard_ACYC_mpFair : Cx.Hard Cx.EXPSPACE (PlanExMPFair FClass.ACYC) := by
  rw [planExMPFair_eq_strong fun _ h => h]
  exact hard_ACYC_mpStrong

theorem complete_ACYC_strongOD : Cx.Complete Cx.EXPSPACE (PlanExFM .strongOD FClass.ACYC) :=
  ⟨strongOD_ACYC_mem, hard_ACYC_strongOD⟩

theorem complete_ACYC_mpStrong : Cx.Complete Cx.EXPSPACE (PlanExMP .strong FClass.ACYC) :=
  ⟨strongMP_ACYC_mem, hard_ACYC_mpStrong⟩

theorem complete_ACYC_mpFair : Cx.Complete Cx.EXPSPACE (PlanExMPFair FClass.ACYC) :=
  ⟨fairMP_ACYC_mem, hard_ACYC_mpFair⟩

end AcycHard

end FOND
