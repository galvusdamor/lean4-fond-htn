import FondHtn.Cx.Closure
import HtnComplexity.Article.AcycNExp
import HtnComplexity.Article.AcycRegNP
import HtnComplexity.Article.NExpHard
import HtnComplexity.Article.ExpSpaceHard
import HtnComplexity.Article.ProgCors
/-!
# Closure of `NEXPTIME` and `EXPSPACE` under polynomial-time reductions

Both classes are defined by nondeterministic Turing machines, and the library only gives
sufficient conditions for membership: a polynomial-time verifier of exponential certificates
(`HTN.Mach.inNExp_of_verifier`) and a nondeterministic search through exponentially long
configurations (`HTN.Mach.inExpSpace_of_search`).  We go through complete problems:

1. `nexp_of_redP_codeLang` / `expSpace_of_redP_codeLang`: if `L` reduces to a language of codes
   with a verifier (resp. a search) in the calculus, then `L` is in the class — the verifier
   (search) of the target, with the reduction prepended.
2. Every language of the class reduces to `PlanEx^{ACYC ∩ TO-tn_I}` (resp.
   `PlanEx^{TAIL-REC ∩ TO-tn_I}`) by the library's hardness theorems, and these languages have
   such verifiers (resp. searches), by the library's membership proofs (Thm. 4.2.5, Cor. 4.2.16)
   with the total-order test of `tn_I` added.
-/

namespace HTN

namespace Cx

open Syn Syn.PolyDom PTime Article

/-! ### Verifiers and searches behind a reduction -/

section Gen

variable {α β σ : Type} [BEnc α] [BDec α] [BEnc β] [BDec β] [BEnc σ] [BDec σ]

theorem nexp_of_redP_codeLang {L : Language} {Q : α → Prop} (hred : RedP L (codeLang α Q))
    {r : α × β → Bool} (hr : PT r) (p : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ b : β, (enc b).length < 2 ^ p.eval (enc a).length ∧ r (a, b) = true) :
    NEXPTIME L := by
  obtain ⟨F, hF, hFF⟩ := hred
  obtain ⟨Pf, hPf⟩ := hF.poly_length
  obtain ⟨g, hg, hglen⟩ := PolyDom.exists_pt_polyLen p
  have hF' := pt_of_polyTimeFun hF
  let h : List Bool × List Bool → Bool := fun q =>
    isCode α (F q.1) && isCode β q.2 && decide ((bitsOfNat q.2.length).length ≤ (g (F q.1)).length) &&
      r ((decR (F q.1) : α × List Bool).1, (decR q.2 : β × List Bool).1)
  have hh : PT h := PT.and (PT.and (PT.and ((pt_isCode α).comp (hF'.comp PT.fst))
    ((pt_isCode β).comp PT.snd))
    (PT.le (PT.length (PT.bits.comp (PT.length PT.snd))) (PT.length (hg.comp (hF'.comp PT.fst)))))
    (hr.comp (PT.pair (PT.fst.comp (BDec.pt_decR.comp (hF'.comp PT.fst)))
      (PT.fst.comp (BDec.pt_decR.comp PT.snd))))
  refine Mach.inNExp_of_verifier (fun args => h (args.getD 0 [], args.getD 1 [])) (cobhamB_of_pt₂ hh)
    (p.comp Pf) (fun x w hv => ?_) (fun x => ⟨?_, ?_⟩)
  · simp only [List.getD_cons_zero, List.getD_cons_succ, h, Bool.and_eq_true, decide_eq_true_eq]
      at hv
    rw [hglen, length_bitsOfNat_le_iff] at hv
    refine hv.1.2.le.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    rw [Polynomial.eval_comp]; exact poly_eval_mono p (hPf x)
  · intro hx
    obtain ⟨a, ha, hQa⟩ := (hFF x).1 hx
    obtain ⟨b, hb, hrb⟩ := (hQ a).1 hQa
    refine ⟨enc b, ?_⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, h, ← ha, Bool.and_eq_true,
      decide_eq_true_eq, (isCode_iff _).2 ⟨a, rfl⟩, (isCode_iff _).2 ⟨b, rfl⟩, decR_enc', hrb,
      hglen, length_bitsOfNat_le_iff, hb, and_self]
  · rintro ⟨w, hv⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, h, Bool.and_eq_true, decide_eq_true_eq]
      at hv
    obtain ⟨⟨⟨hx, hw'⟩, hlen⟩, hrr⟩ := hv
    obtain ⟨a, ha⟩ := (isCode_iff _).1 hx
    obtain ⟨b, rfl⟩ := (isCode_iff _).1 hw'
    rw [← ha, decR_enc', decR_enc'] at hrr
    rw [hglen, length_bitsOfNat_le_iff, ← ha] at hlen
    exact (hFF x).2 ⟨a, ha, (hQ a).2 ⟨b, hlen, hrr⟩⟩

theorem expSpace_of_redP_codeLang {L : Language} {Q : α → Prop} (hred : RedP L (codeLang α Q))
    {init : α × σ → Bool} {step : α × σ × σ → Bool} {acc : α × σ → Bool} (hi : PT init)
    (hs : PT step) (ha : PT acc) (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀ c, sz c₀ < 2 ^ q.eval (sz a) ∧ init (a, c₀) = true ∧
      Relation.ReflTransGen (fun c c' => sz c' < 2 ^ q.eval (sz a) ∧ step (a, c, c') = true) c₀ c ∧
      acc (a, c) = true) :
    EXPSPACE L := by
  obtain ⟨F, hF, hFF⟩ := hred
  obtain ⟨Pf, hPf⟩ := hF.poly_length
  have hF' := pt_of_polyTimeFun hF
  obtain ⟨g, hg, hglen⟩ := PolyDom.exists_pt_polyLen q
  let dA : List Bool → α := fun x => (decR x : α × List Bool).1
  let dS : List Bool → σ := fun x => (decR x : σ × List Bool).1
  have hdA : PT dA := PT.fst.comp BDec.pt_decR
  have hdS : PT dS := PT.fst.comp BDec.pt_decR
  let hSt : List Bool × List Bool × List Bool → Bool := fun r =>
    r.2.2.headI && isCode σ r.2.2.tail && isCode α (F r.1) &&
      decide ((bitsOfNat r.2.2.tail.length).length ≤ (g (F r.1)).length) &&
      bif r.2.1.isEmpty then init (dA (F r.1), dS r.2.2.tail)
        else r.2.1.headI && isCode σ r.2.1.tail && step (dA (F r.1), dS r.2.1.tail, dS r.2.2.tail)
  have hhSt : PT hSt := by
    have hc' : PT fun r : List Bool × List Bool × List Bool => r.2.2 := PT.snd.comp PT.snd
    have hc : PT fun r : List Bool × List Bool × List Bool => r.2.1 := PT.fst.comp PT.snd
    have hx : PT fun r : List Bool × List Bool × List Bool => F r.1 := hF'.comp PT.fst
    exact PT.and (PT.and (PT.and (PT.and (PT.headI hc') ((pt_isCode σ).comp (PT.tail hc')))
      ((pt_isCode α).comp hx)) (PT.le (PT.length (PT.bits.comp (PT.length (PT.tail hc'))))
        (PT.length (hg.comp hx))))
      (PT.cond (PT.isEmpty hc) (hi.comp (PT.pair (hdA.comp hx) (hdS.comp (PT.tail hc'))))
        (PT.and (PT.and (PT.headI hc) ((pt_isCode σ).comp (PT.tail hc)))
          (hs.comp (PT.pair (hdA.comp hx) (PT.pair (hdS.comp (PT.tail hc))
            (hdS.comp (PT.tail hc')))))))
  let hAc : List Bool × List Bool → Bool := fun r =>
    r.2.headI && isCode σ r.2.tail && isCode α (F r.1) && acc (dA (F r.1), dS r.2.tail)
  have hhAc : PT hAc := PT.and (PT.and (PT.and (PT.headI PT.snd) ((pt_isCode σ).comp
    (PT.tail PT.snd))) ((pt_isCode α).comp (hF'.comp PT.fst)))
    (ha.comp (PT.pair (hdA.comp (hF'.comp PT.fst)) (hdS.comp (PT.tail PT.snd))))
  have hcons : ∀ l : List Bool, l.headI = true → l = true :: l.tail := by
    intro l h; cases l with
    | nil => simp at h
    | cons b l => simp at h; simp [h]
  refine Mach.inExpSpace_of_search (fun args => hSt (args.getD 0 [], args.getD 1 [], args.getD 2 []))
    (fun args => hAc (args.getD 0 [], args.getD 1 [])) (cobhamB_of_pt₃ hhSt) (cobhamB_of_pt₂ hhAc)
    (q.comp Pf + 1) (fun x c c' h => ?_) (fun x => ⟨?_, ?_⟩)
  · simp only [List.getD_cons_zero, List.getD_cons_succ, hSt, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, -⟩, -⟩, h4⟩, -⟩ := h
    rw [hglen, length_bitsOfNat_le_iff] at h4
    rw [hcons c' h1, List.length_cons]
    have hm : 2 ^ q.eval (F x).length ≤ 2 ^ (q.comp Pf).eval x.length :=
      Nat.pow_le_pow_right (by norm_num) (by
        rw [Polynomial.eval_comp]; exact poly_eval_mono q (hPf x))
    have : 2 ^ ((q.comp Pf + 1).eval x.length) = 2 * 2 ^ (q.comp Pf).eval x.length := by
      simp [pow_succ]; ring
    rw [this]
    have : 1 ≤ 2 ^ (q.comp Pf).eval x.length := Nat.one_le_two_pow
    omega
  · intro hx
    obtain ⟨a, ha, hQa⟩ := (hFF x).1 hx
    obtain ⟨c₀, c, h₀, hi₀, hr, hac⟩ := (hQ a).1 hQa
    refine ⟨true :: enc c, ?_, ?_⟩
    · refine Relation.ReflTransGen.head (b := true :: enc c₀) ?_
        (Relation.ReflTransGen.lift (fun s => true :: enc s) (fun s s' hss => ?_) hr)
      · show hSt (x, [], true :: enc c₀) = true
        simp only [hSt, ← ha, List.headI_cons, List.tail_cons, (isCode_iff _).2 ⟨c₀, rfl⟩,
          (isCode_iff _).2 ⟨a, rfl⟩, Bool.true_and, hglen, length_bitsOfNat_le_iff,
          List.isEmpty_nil, cond_true, dA, dS, decR_enc', hi₀, Bool.and_true, decide_eq_true_eq]
        exact h₀
      · show hSt (x, true :: enc s, true :: enc s') = true
        simp only [hSt, ← ha, List.headI_cons, List.tail_cons, (isCode_iff _).2 ⟨s, rfl⟩,
          (isCode_iff _).2 ⟨s', rfl⟩, (isCode_iff _).2 ⟨a, rfl⟩, Bool.true_and, hglen,
          length_bitsOfNat_le_iff, List.isEmpty_cons, cond_false, dA, dS, decR_enc', hss.2,
          Bool.and_true, decide_eq_true_eq]
        exact hss.1
    · show hAc (x, true :: enc c) = true
      simp only [hAc, ← ha, List.headI_cons, List.tail_cons, (isCode_iff _).2 ⟨c, rfl⟩,
        (isCode_iff _).2 ⟨a, rfl⟩, dA, dS, decR_enc', hac, Bool.and_self]
  · rintro ⟨c, hr, hac⟩
    have hac' : hAc (x, c) = true := hac
    simp only [hAc, Bool.and_eq_true] at hac'
    obtain ⟨⟨⟨hh, -⟩, hx⟩, hacc⟩ := hac'
    obtain ⟨a, ha⟩ := (isCode_iff _).1 hx
    have key : ∀ c, Relation.ReflTransGen (fun c c' =>
        hSt (x, c, c') = true) [] c → c = [] ∨ ∃ c₀ s, sz c₀ < 2 ^ q.eval (sz a) ∧
          init (a, c₀) = true ∧ Relation.ReflTransGen (fun c c' => sz c' < 2 ^ q.eval (sz a) ∧
            step (a, c, c') = true) c₀ s ∧ c = true :: enc s := by
      intro c hc
      induction hc with
      | refl => exact Or.inl rfl
      | @tail b c' _ hbc ih =>
        simp only [hSt, Bool.and_eq_true, decide_eq_true_eq] at hbc
        obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩ := hbc
        obtain ⟨s', hs'⟩ := (isCode_iff _).1 h2
        rw [hglen, length_bitsOfNat_le_iff, ← ha] at h4
        have hc'eq : c' = true :: enc s' := by rw [hcons c' h1, hs']
        rw [← hs'] at h4
        right
        rcases ih with rfl | ⟨c₀, s, h0, hi0, hrs, rfl⟩
        · simp only [List.isEmpty_nil, cond_true, dA, dS, ← hs', ← ha, decR_enc'] at h5
          exact ⟨s', s', h4, h5, .refl, hc'eq⟩
        · simp only [List.isEmpty_cons, cond_false, List.headI_cons, List.tail_cons, Bool.true_and,
            Bool.and_eq_true, dA, dS, ← hs', ← ha, decR_enc'] at h5
          exact ⟨c₀, s', h0, hi0, hrs.tail ⟨h4, h5.2⟩, hc'eq⟩
    rcases key c hr with rfl | ⟨c₀, s, h0, hi0, hrs, rfl⟩
    · simp at hh
    · simp only [List.tail_cons, dA, dS, ← ha, decR_enc'] at hacc
      exact (hFF x).2 ⟨a, ha, (hQ a).2 ⟨c₀, s, h0, hi0, hrs, hacc⟩⟩

end Gen

/-! ### `NEXPTIME` -/

/-- The verifier of Thm. 4.2.5 with the total-order test of `tn_I`. -/
def acycTOB (x : ProbDesc × AcycTreeCert) : Bool := acycTreeB x && toB x.1.tnI

theorem pt_acycTOB : PT acycTOB :=
  (PT.and pt_acycTreeB (pt_toB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))))).of_eq fun _ => rfl

theorem NEXPTIME.of_redP {L L' : Language} (h : RedP L L') (h' : NEXPTIME L') : NEXPTIME L := by
  have hred := h.trans (thm_4_3_7_acyc L' h')
  refine nexp_of_redP_codeLang (α := ProbDesc) (β := AcycTreeCert)
    (Q := fun p => p.Valid ∧ (p.toProblem.IsACYC ∧ p.toProblem.IsTO_tnI) ∧ p.toProblem.Solvable)
    hred pt_acycTOB qAcyc fun p => ⟨fun ⟨hp, ⟨hac, hto⟩, hsol⟩ => ?_, fun ⟨b, _, hb⟩ => ?_⟩
  · obtain ⟨b, hsz, hb⟩ := exists_acycTreeB ⟨hp, hac, hsol⟩
    exact ⟨b, hsz, by simp [acycTOB, hb, (toB_iff hp.tnI).2 hto]⟩
  · simp only [acycTOB, Bool.and_eq_true] at hb
    obtain ⟨hp, hac, hsol⟩ := of_acycTreeB hb.1
    exact ⟨hp, ⟨hac, (toB_iff hp.tnI).1 hb.2⟩, hsol⟩

/-! ### `EXPSPACE` -/

/-- The certificate check of Cor. 4.2.16 with the total-order test of `tn_I`. -/
def trTOB (x : ProbDesc × (ℕ × (List ℕ × List (ℕ × ℕ)))) : Bool := trHB x && toB x.1.tnI

theorem pt_trTOB : PT trTOB :=
  (PT.and pt_trHB (pt_toB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))))).of_eq
    fun _ => rfl

/-- The certificates and progression bounds of Cor. 4.2.16. -/
theorem trTO_hcomp (p : ProbDesc) (hp : p.Valid)
    (hY : p.toProblem.IsTailREC ∧ p.toProblem.IsTO_tnI) :
    (∃ b, trTOB (p, b) = true ∧ sz b ≤ 2 ^ (sz p ^ 2 + 2 * sz p + 6)) ∧
      p.toProblem.IsHTNProgBound (2 ^ (sz p ^ 2 + 2 * sz p + 6)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb, hsz, -⟩ := exists_trHB hp hY.1
    refine ⟨b, by simp [trTOB, hb, (toB_iff hp.tnI).2 hY.2], hsz.trans ?_⟩
    set S := sz p
    have hS := one_le_S p
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
  · have hh := isTailREC_h_of_isTailREC hp hY.1
    have hb := (p.toProblem.lem_4_2_15 (wf_toProblem p) hh (tnI_card_le p) (one_le_S p)
      (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    set S := sz p
    have hK : (numsOf p).length ≤ S := length_numsOf_le p
    have hS := one_le_S p
    have h1 : S ^ (numsOf p).length ≤ S ^ S := Nat.pow_le_pow_right hS hK
    have h2 : S ^ S ≤ (2 ^ S) ^ S := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le S
    have h3 : S ≤ 2 ^ S := (Nat.lt_two_pow_self).le
    have h4 : S * S ^ S ≤ 2 ^ S * (2 ^ S) ^ S := Nat.mul_le_mul h3 h2
    have h5 : 2 ^ S * (2 ^ S) ^ S = 2 ^ (S + S * S) := by rw [← pow_mul, ← pow_add]
    have h6 : 2 ^ (S + S * S) ≤ 2 ^ (S ^ 2 + 2 * S + 6) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    calc S * S ^ (numsOf p).length ≤ S * S ^ S := Nat.mul_le_mul_left _ h1
      _ ≤ _ := h4.trans (h5 ▸ h6)

theorem EXPSPACE.of_redP {L L' : Language} (h : RedP L L') (h' : EXPSPACE L') : EXPSPACE L := by
  have hred := h.trans (thm_4_3_7_tr L' h')
  let r : Polynomial ℕ := Polynomial.X ^ 2 + 2 * Polynomial.X + 6
  have hr : ∀ n, r.eval n = n ^ 2 + 2 * n + 6 := fun n => by simp [r]
  let q : Polynomial ℕ := 3 * r + 3 * Polynomial.X + 12
  have hq : ∀ n, q.eval n = 3 * r.eval n + 3 * n + 12 := fun n => by simp [q]
  have hbound : ∀ n e : ℕ, 2 ^ e + 40 * (2 ^ e + n + 1) ^ 3 < 2 ^ (3 * e + 3 * n + 12) := by
    intro n e
    have h1 : 2 ^ e + n + 1 ≤ 3 * 2 ^ (e + n) := by
      have := Nat.lt_two_pow_self (n := n)
      have : 2 ^ n ≤ 2 ^ (e + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ e ≤ 2 ^ (e + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : (2 ^ e + n + 1) ^ 3 ≤ 27 * 2 ^ (3 * (e + n)) := by
      calc (2 ^ e + n + 1) ^ 3 ≤ (3 * 2 ^ (e + n)) ^ 3 := Nat.pow_le_pow_left h1 3
        _ = 27 * 2 ^ (3 * (e + n)) := by rw [mul_pow, ← pow_mul]; ring_nf
    have h3 : 2 ^ e ≤ 2 ^ (3 * (e + n)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (3 * e + 3 * n + 12) = 4096 * 2 ^ (3 * (e + n)) := by
      rw [show 3 * e + 3 * n + 12 = 12 + 3 * (e + n) by ring, pow_add]; norm_num
    rw [h4]
    have : 0 < 2 ^ (3 * (e + n)) := by positivity
    omega
  have hsound : ∀ p b, p.Valid → trTOB (p, b) = true →
      p.toProblem.IsTailREC ∧ p.toProblem.IsTO_tnI := fun p b hp hb => by
    simp only [trTOB, Bool.and_eq_true] at hb
    exact ⟨(trHB_sound hp hb.1).1, (toB_iff hp.tnI).1 hb.2⟩
  refine expSpace_of_redP_codeLang (α := ProbDesc) (σ := (ℕ × (List ℕ × List (ℕ × ℕ))) × PCfg)
    (Q := fun p => p.Valid ∧ (p.toProblem.IsTailREC ∧ p.toProblem.IsTO_tnI) ∧
      p.toProblem.Solvable) hred (pt_pInit pt_trTOB) pt_pStep pt_pAcc q fun p => ?_
  have e := planEx_iff_search (cB := trTOB)
    (Y := fun P => P.IsTailREC ∧ P.IsTO_tnI) hsound (fun n => 2 ^ q.eval n - 1)
    (fun p hp hY => by
      obtain ⟨⟨b, hb, hbs⟩, hn⟩ := trTO_hcomp p hp hY
      refine ⟨b, hb, _, hn, ?_⟩
      have := hbound (sz p) (r.eval (sz p))
      show _ ≤ 2 ^ q.eval (sz p) - 1
      rw [hq, ← hr] at *
      omega) p
  refine e.trans ?_
  have hlt : ∀ m, m ≤ 2 ^ q.eval (sz p) - 1 ↔ m < 2 ^ q.eval (sz p) := fun m => by
    have : 0 < 2 ^ q.eval (sz p) := by positivity
    omega
  simp only [hlt]

end Cx

end HTN
