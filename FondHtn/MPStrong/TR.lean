import FondHtn.MPStrong.Mem
import FondHtn.Cx.Exp2
/-!
# Strong method-based plan existence for tail-recursive problems is in `2-EXPTIME`
([CB22, Thm. 5], membership, strong)

The progression game on descriptions of `FondHtn/MPStrong/Game.lean` with *exponential*
certificates and progression bounds: configurations have exponential size, so the least fixpoint
of the AND-OR game is computed in doubly exponential time
(`HTN.Syn.PolyDom.inExp2Time_codeLang_of_andOr`).

* `FOND.MPS.inExp2Time_planExMP_strong` — the generic statement (exponential analogue of
  `FOND.MPS.inExpTime_planExMP_strong`);
* **`FOND.strongMP_TR_mem`** — `PlanExMP .strong TR ∈ 2-EXPTIME` ([CB22, Thm. 5]), with the
  progression bound `k · m^h` of Lemma 4.2.15 (`h ≤ |p|`), which is exponential.

As for the other memberships, the progression restriction of the algorithm is justified by the
G8 lemma `FOND.Problem.mpStrongSolvable_iff_mpProg`.  [CB22] claims 2-EXPTIME-completeness; only
EXPSPACE-hardness is inherited (`FOND.hard_TR_mp`, for TR with a totally ordered initial network),
recorded in `FOND.strongMP_TR_bounds`.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

namespace MPS

section Main

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

theorem sz_zero_nat : sz (0 : ℕ) ≤ 5 := sz_nat_le_two (by norm_num)

/-- The node bound with an exponential progression bound is exponential. -/
theorem exp_nodeBound_le (e S : ℕ) : 2 ^ e + nodeBound (2 ^ e) S ≤ 2 ^ (3 * e + 3 * S + 12) := by
  unfold nodeBound
  have h0 := sz_zero_nat
  set X := 2 ^ (e + S) with hX
  have h1 : 2 ^ e ≤ X := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ S ≤ X := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : S < 2 ^ S := Nat.lt_two_pow_self
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have h4 : 2 ^ e + 2 * S + 1 ≤ 3 * X := by omega
  have h5 : (2 ^ e + 2 * S + 1) ^ 3 ≤ (3 * X) ^ 3 := Nat.pow_le_pow_left h4 3
  have h6 : S * (2 * S + 2) ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
  have h7 : 2 ^ (3 * e + 3 * S + 12) = 4096 * X ^ 3 := by
    rw [hX, ← pow_mul, show 3 * e + 3 * S + 12 = 12 + (e + S) * 3 by ring, pow_add]; norm_num
  rw [h7]
  have h8 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
  have h9 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by norm_num)
  have h10 : X * (2 * X) = 2 * X ^ 2 := by ring
  have h11 : (3 * X) ^ 3 = 27 * X ^ 3 := by ring
  have h12 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
  omega

/-- **Strong method-based plan existence is in `2-EXPTIME`** for classes with exponential
certificates and exponential progression bounds of the skeleton. -/
theorem inExp2Time_planExMP_strong {Y : FClass} {cB : FProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r : Polynomial ℕ)
    (hcomp : ∀ p : FProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ 2 ^ r.eval (sz p)) ∧ (skDesc p).toProblem.IsHTNProgBound (2 ^ r.eval (sz p))) :
    Cx.EXPTIME2 (PlanExMP .strong Y) := by
  obtain ⟨gr, hgr, hgrlen⟩ := HTN.Syn.PolyDom.exists_pt_polyLen r
  have hR : PT fun p : FProbDesc => 2 ^ r.eval (sz p) := by
    have h := PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
      (hgr.comp (BDec.pt_encL (α := FProbDesc))) (PT.const false)) (PT.const [true]))
    exact h.of_eq fun a => by rw [List.map_const', hgrlen, natOfBits_pow]; rfl
  let q : Polynomial ℕ := 3 * r + 3 * Polynomial.X + 12
  have hq : ∀ n, q.eval n = 3 * r.eval n + 3 * n + 12 := fun n => by simp [q]
  have hreach : ∀ p : FProbDesc, p.Valid → Y p.toProblem → ∀ b : β, sz b ≤ 2 ^ r.eval (sz p) →
      ∀ g, GReach p b g → sz g ≤ 2 ^ q.eval (sz p) := by
    intro p hp hY b hb g hg
    have := sz_le_of_gInv hp (hcomp p hp hY).2 (gInv_of_reach hp hg)
    have h2 := exp_nodeBound_le (r.eval (sz p)) (sz p)
    rw [hq]
    omega
  refine inExp2Time_codeLang_of_andOr (α := FProbDesc) (σ := β × GNode)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongSolvable)
    (pt_gInit hcB hR) pt_gAcc pt_gUni pt_gStep q fun p => ?_
  constructor
  · rintro ⟨hp, hY, hsol⟩
    obtain ⟨⟨b, hb, hbs⟩, -⟩ := hcomp p hp hY
    have hsz := hreach p hp hY b hbs
    refine ⟨(b, ((false, 0), initF p)), hsz _ .refl, ?_, ?_⟩
    · simp [gInit, (FProbDesc.validB_iff p).2 hp, hb, hbs]
    · have h := (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).1 hsol
      exact complete hp hsz h .refl rfl (init_state p) (FProbDesc.toProblem_wf hp).tnI
        (isoVia_art (isoVia_id_of_agree (agree_initF hp)))
  · rintro ⟨⟨b, g⟩, -, hi, hw⟩
    simp only [gInit, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨hv, hb⟩, hbs⟩, rfl⟩ := hi
    have hp := (FProbDesc.validB_iff p).1 hv
    have hY := hsound p b hp hb
    have hsz := hreach p hp hY b hbs
    refine ⟨hp, hY, ?_⟩
    have h := (sound hp hsz hw .refl).1 rfl
    have hinv := (gInv_init hp b).inv
    rw [← init_state] at h
    exact (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).2
      (h.isoVia hinv.wf (FProbDesc.toProblem_wf hp).tnI
        (isoVia_art (isoVia_id_of_agree (agree_initF hp).symm)))

end Main

end MPS

/-- The tail-recursion certificate and the exponential progression bound of Cor. 4.2.16, for a
deterministic description `q`. -/
theorem tr_hcomp {q : ProbDesc} (hq : q.Valid) (hY : q.toProblem.IsTailREC) :
    (∃ b, trHB (q, b) = true ∧ sz b ≤ 2 ^ (sz q ^ 2 + 2 * sz q + 6)) ∧
      q.toProblem.IsHTNProgBound (2 ^ (sz q ^ 2 + 2 * sz q + 6)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb, hsz, -⟩ := exists_trHB hq hY
    refine ⟨b, hb, hsz.trans ?_⟩
    set S := sz q
    have hS := one_le_S q
    have h1 : 2 * S + 1 ≤ 2 ^ (S + 1) := by
      have := Nat.lt_two_pow_self (n := S); rw [pow_succ]; omega
    have h2 : (2 * S + 1) ^ 2 ≤ 2 ^ (2 * S + 2) := by
      calc (2 * S + 1) ^ 2 ≤ (2 ^ (S + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 2 ^ (2 * S + 2) := by rw [← pow_mul]; ring_nf
    have h3 : 2 ^ (S ^ 2 + 2 * S + 6) = 2 ^ (S ^ 2 + 4) * 2 ^ (2 * S + 2) := by
      rw [← pow_add]; ring_nf
    have h4 : 16 ≤ 2 ^ (S ^ 2 + 4) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (S ^ 2 + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h3]
    nlinarith
  · have hh := isTailREC_h_of_isTailREC hq hY
    have hb := (q.toProblem.lem_4_2_15 (wf_toProblem q) hh (tnI_card_le q) (one_le_S q)
      (meth_card_le q)).1
    refine IsHTNProgBound.mono hb ?_
    set S := sz q
    have hK : (numsOf q).length ≤ S := length_numsOf_le q
    have hS := one_le_S q
    have h1 : S ^ (numsOf q).length ≤ S ^ S := Nat.pow_le_pow_right hS hK
    have h2 : S ^ S ≤ (2 ^ S) ^ S := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le S
    have h3 : S ≤ 2 ^ S := (Nat.lt_two_pow_self).le
    have h4 : S * S ^ S ≤ 2 ^ S * (2 ^ S) ^ S := Nat.mul_le_mul h3 h2
    have h5 : 2 ^ S * (2 ^ S) ^ S = 2 ^ (S + S * S) := by rw [← pow_mul, ← pow_add]
    have h6 : 2 ^ (S + S * S) ≤ 2 ^ (S ^ 2 + 2 * S + 6) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    calc S * S ^ (numsOf q).length ≤ S * S ^ S := Nat.mul_le_mul_left _ h1
      _ ≤ _ := h4.trans (h5 ▸ h6)

theorem skDesc_exp_le (p : FProbDesc) :
    2 ^ (sz (skDesc p) ^ 2 + 2 * sz (skDesc p) + 6) ≤ 2 ^ (4 * sz p ^ 2 + 4 * sz p + 6) := by
  have hS := sz_skDesc_le p
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have : sz (skDesc p) ^ 2 ≤ (2 * sz p) ^ 2 := Nat.pow_le_pow_left hS 2
  nlinarith

/-- **[CB22, Thm. 5], membership (strong)**: strong method-based plan existence for
tail-recursive problems is in `2-EXPTIME`. -/
theorem strongMP_TR_mem : Cx.EXPTIME2 (PlanExMP .strong FClass.TR) := by
  let r : Polynomial ℕ := 4 * Polynomial.X ^ 2 + 4 * Polynomial.X + 6
  have hr : ∀ n, r.eval n = 4 * n ^ 2 + 4 * n + 6 := fun n => by simp [r]
  refine inExp2Time_planExMP_strong (β := ℕ × (List ℕ × List (ℕ × ℕ)))
    (cB := fun x => trHB (skDesc x.1, x.2)) (pt_trHB.comp (PT.pair (pt_skDesc.comp PT.fst)
      PT.snd)) (fun p b hp hb => ?_) r fun p hp hY => ?_
  · exact (sameShape_skDesc p).isTailRecursive.2 (trHB_sound (skDesc_valid hp) hb).1
  · obtain ⟨⟨b, hb, hbs⟩, hn⟩ := tr_hcomp (skDesc_valid hp)
      ((sameShape_skDesc p).isTailRecursive.1 hY)
    have he := skDesc_exp_le p
    rw [hr]
    exact ⟨⟨b, hb, hbs.trans he⟩, IsHTNProgBound.mono hn he⟩

/-- Membership in `2-EXPTIME` together with the inherited lower bound (EXPSPACE-hardness, already
for tail-recursive problems with a totally ordered initial network). -/
theorem strongMP_TR_bounds :
    Cx.EXPTIME2 (PlanExMP .strong FClass.TR) ∧
      Cx.Hard Cx.EXPSPACE (PlanExMP .strong FClass.TR) :=
  ⟨strongMP_TR_mem, (hard_TR_mp .strong (by decide)).of_redP
    (redP_filterMP pt_fToB fun _ hp => fToB_iff hp)⟩

end FOND
