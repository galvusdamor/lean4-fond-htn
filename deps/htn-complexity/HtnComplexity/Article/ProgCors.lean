import HtnComplexity.Article.TRCert
/-!
# Upper space bounds by progression (Cors. 4.2.16–4.2.18, 4.2.20, 4.2.22)

Each corollary instantiates `HTN.Article.inPSpace_planEx` (or `inExpSpace_planEx`): a certificate
of the class (`HTN.Article.trB` for tail recursion, `HTN.Article.acycB` for acyclicity, with the
total-order checks `HTN.Article.toB` of the initial network and of the methods of the certified
reachable names), and the progression bound of the article's lemma:

* Cor. 4.2.16 — `TAIL-REC` in `EXPSPACE` (Lem. 4.2.15: `k · m^h`, `h ≤ |p|`);
* Cor. 4.2.17 — `TAIL-REC_h` in `PSPACE` for fixed `h` (Lem. 4.2.15);
* Cor. 4.2.18 — `REG` and `REG ∩ TO` in `PSPACE` (Thm. 3.0.1: `REG = TAIL-REC_1`);
* Cor. 4.2.20 — `TAIL-REC ∩ TO` and `ACYC ∩ TO` in `PSPACE` (Lem. 4.2.19);
* Cor. 4.2.22 — `TAIL-REC ∩ TO-M` and `ACYC ∩ TO-M` in `PSPACE` (Lem. 4.2.21).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-! ### Sizes and bounds -/

theorem tnI_card_le (p : ProbDesc) : p.toProblem.tnI.T.card ≤ sz p := by
  have h1 : p.toProblem.tnI.T.card ≤ p.tnI.ids.length := List.toFinset_card_le _
  have h2 := ids_length_le_sz p.tnI
  have h3 := sz_probDesc p
  omega

theorem meth_card_le (p : ProbDesc) :
    ∀ m', p.toProblem.toPos.ReachableMethod m' → m'.subtasks.T.card ≤ sz p := by
  rintro m' ⟨⟨e, he, rfl⟩, -⟩
  exact (List.toFinset_card_le _).trans (methods_ids_le e he)

theorem IsHTNProgBound.mono {p : ProbDesc} {n n' : ℕ} (h : p.toProblem.IsHTNProgBound n)
    (hle : n ≤ n') : p.toProblem.IsHTNProgBound n' := fun nd hnd => (h nd hnd).trans hle

theorem sz_rcert_le {p : ProbDesc} {R : List ℕ} {rkL : List (ℕ × ℕ)} {H : ℕ}
    (hRN : ∀ c ∈ R, c ∈ numsOf p) (hRl : R.length ≤ (numsOf p).length)
    (hrkN : ∀ q ∈ rkL, q.1 ∈ numsOf p ∧ q.2 < H) (hrkl : rkL.length ≤ (numsOf p).length) :
    sz (R, rkL) ≤ 10 * (sz p + H + 1) ^ 2 := by
  set S := sz p
  have hK : (numsOf p).length ≤ S := length_numsOf_le p
  have hR : sz R ≤ R.length * (2 * S + 2) + 1 := sz_list_le fun a ha => sz_le_of_mem_numsOf (hRN a ha)
  have hrk : sz rkL ≤ rkL.length * (2 * (S + (2 * H + 1)) + 2) + 1 := sz_list_le fun q hq => by
    rw [sz_prod]
    have := sz_le_of_mem_numsOf (hrkN q hq).1
    have := sz_nat_le_of_lt' (hrkN q hq).2
    omega
  have e1 : R.length * (2 * S + 2) ≤ (S + H + 1) * (2 * (S + H + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : rkL.length * (2 * (S + (2 * H + 1)) + 2) ≤ (S + H + 1) * (6 * (S + H + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [sz_prod]
  nlinarith

/-- The methods of the names of `R` pass the check `g`. -/
def methodsRB (g : TnDesc → Bool) (p : ProbDesc) (R : List ℕ) : Bool :=
  p.methods.all fun e => !decide (e.1 ∈ R) || g e.2

theorem pt_methodsRB {α : Type} [BEnc α] {g : TnDesc → Bool} (hg : PT g) {f : α → ProbDesc}
    {r : α → List ℕ} (hf : PT f) (hr : PT r) : PT fun a => methodsRB g (f a) (r a) := by
  unfold methodsRB
  exact PT.all (PT.snd.comp (PT.fst.comp hf)) (PT.or (PT.not (PT.elem (hr.comp PT.fst)
    (PT.fst.comp PT.snd))) (hg.comp (PT.snd.comp PT.snd)))

theorem methodsRB_sound {p : ProbDesc} (hp : p.Valid) {R : List ℕ}
    (hcl : ∀ c, p.toProblem.toPos.ReachableName c → c ∈ R) {g : TnDesc → Bool}
    {Pm : TaskNetwork ℕ ℕ ℕ → Prop} (hg : ∀ {t : TnDesc}, TnValid p.Declared t →
      (g t = true ↔ Pm t.toTaskNetwork)) (h : methodsRB g p R = true) :
    ∀ m, p.toProblem.toPos.ReachableMethod m → Pm m.subtasks := by
  rintro m ⟨⟨e, he, rfl⟩, hr⟩
  have := List.all_eq_true.1 h e he
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
  rcases this with h1 | h1
  · exact absurd (hcl _ hr) h1
  · exact (hg (hp.methods e he)).1 h1

theorem methodsRB_complete {p : ProbDesc} (hp : p.Valid) {R : List ℕ}
    (hRr : ∀ c ∈ R, p.toProblem.toPos.ReachableName c) {g : TnDesc → Bool}
    {Pm : TaskNetwork ℕ ℕ ℕ → Prop} (hg : ∀ {t : TnDesc}, TnValid p.Declared t →
      (g t = true ↔ Pm t.toTaskNetwork))
    (h : ∀ m, p.toProblem.toPos.ReachableMethod m → Pm m.subtasks) : methodsRB g p R = true := by
  unfold methodsRB
  rw [List.all_eq_true]
  intro e he
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases hR : e.1 ∈ R
  · exact Or.inr ((hg (hp.methods e he)).2
      (h _ ⟨(⟨e, he, rfl⟩ : ∃ e' ∈ p.methods, e'.toMethod = e.toMethod), hRr _ hR⟩))
  · exact Or.inl hR

theorem trCert_closed {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} {h : ℕ} (hc : TRCert p R rk h) :
    ∀ c, p.toProblem.toPos.ReachableName c → c ∈ R := fun _ hr => hc.reach_mem hr

theorem one_le_S (p : ProbDesc) : 1 ≤ sz p := one_le_sz_probDesc p

theorem le_two_pow_self (n : ℕ) : n + 1 ≤ 2 ^ n ∨ n = 0 := by
  rcases n with _ | n
  · exact Or.inr rfl
  · left; have := Nat.lt_two_pow_self (n := n + 1); omega

/-! ### Corollary 4.2.17 -/

/-- **Corollary 4.2.17.** For a fixed `h`, `PlanEx^{TAIL-REC_h}_htn ∈ PSPACE`. -/
theorem cor_4_2_17 (h : ℕ) : Cx.PSPACE (PlanEx fun P => P.IsTailREC_h h) := by
  let r : Polynomial ℕ := 10 * (Polynomial.X + Polynomial.C h + 1) ^ 2 + (Polynomial.X + 1) ^ (h + 1)
  have hr : ∀ n, r.eval n = 10 * (n + h + 1) ^ 2 + (n + 1) ^ (h + 1) := fun n => by simp [r]
  refine inPSpace_planEx (pt_trB h) (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨R, rkL⟩ := b
    exact ((trB_iff h p R rkL).1 hb).isTailREC_h hp
  · obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -⟩ := exists_trCert hp hY
    refine ⟨(R, rkL), hb, ?_⟩
    rw [hr]
    have := sz_rcert_le hRN hRl hrkN hrkl
    omega
  · have hb := (p.toProblem.lem_4_2_15 (wf_toProblem p) hY (tnI_card_le p) (one_le_S p)
      (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
    have h1 : sz p ^ h ≤ (sz p + 1) ^ h := Nat.pow_le_pow_left (by omega) h
    have h2 : sz p * sz p ^ h ≤ (sz p + 1) * (sz p + 1) ^ h := Nat.mul_le_mul (by omega) h1
    have h3 : (sz p + 1) * (sz p + 1) ^ h = (sz p + 1) ^ (h + 1) := by ring
    omega

/-! ### Corollary 4.2.16 -/

/-- The certificate of tail recursion with the height. -/
def trHB (x : ProbDesc × (ℕ × (List ℕ × List (ℕ × ℕ)))) : Bool := trB x.2.1 (x.1, x.2.2)

theorem pt_trHB : PT trHB :=
  (pt_trBH.comp (PT.pair (PT.pair PT.fst (PT.snd.comp PT.snd)) (PT.fst.comp PT.snd))).of_eq
    fun _ => rfl

theorem trHB_sound {p : ProbDesc} (hp : p.Valid) {b : ℕ × (List ℕ × List (ℕ × ℕ))}
    (hb : trHB (p, b) = true) : p.toProblem.IsTailREC ∧
      ∀ c, p.toProblem.toPos.ReachableName c → c ∈ b.2.1 := by
  obtain ⟨h, R, rkL⟩ := b
  have hc := (trB_iff h p R rkL).1 hb
  exact ⟨HTN.Problem.IsTailRecursiveH.isTailRecursive (hc.isTailREC_h hp), trCert_closed hc⟩

/-- A certificate for a tail-recursive description, with its size. -/
theorem exists_trHB {p : ProbDesc} (hp : p.Valid) (hY : p.toProblem.IsTailREC) :
    ∃ b, trHB (p, b) = true ∧ sz b ≤ 11 * (2 * sz p + 1) ^ 2 ∧
      (∀ c ∈ b.2.1, p.toProblem.toPos.ReachableName c) := by
  obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, hRr⟩ :=
    exists_trCert hp (isTailREC_h_of_isTailREC hp hY)
  refine ⟨((numsOf p).length, R, rkL), hb, ?_, hRr⟩
  have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
  have h1 := sz_rcert_le hRN hRl hrkN hrkl
  have h2 : sz (numsOf p).length ≤ 2 * sz p + 1 :=
    sz_nat_le_of_lt (lt_of_le_of_lt hK (Nat.lt_two_pow_self))
  rw [sz_prod]
  have : (sz p + (numsOf p).length + 1) ^ 2 ≤ (2 * sz p + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

/-- **Corollary 4.2.16.** `PlanEx^{TAIL-REC}_htn ∈ EXPSPACE`. -/
theorem cor_4_2_16 : Cx.EXPSPACE (PlanEx fun P => P.IsTailREC) := by
  let r : Polynomial ℕ := Polynomial.X ^ 2 + 2 * Polynomial.X + 6
  have hr : ∀ n, r.eval n = n ^ 2 + 2 * n + 6 := fun n => by simp [r]
  refine inExpSpace_planEx pt_trHB (fun p b hp hb => (trHB_sound hp hb).1) r
    fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨b, hb, hsz, -⟩ := exists_trHB hp hY
    refine ⟨b, hb, hsz.trans ?_⟩
    rw [hr]
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
  · have hh := isTailREC_h_of_isTailREC hp hY
    have hb := (p.toProblem.lem_4_2_15 (wf_toProblem p) hh (tnI_card_le p) (one_le_S p)
      (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
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

/-! ### Corollary 4.2.18 -/

/-- **Corollary 4.2.18 (REG).** `PlanEx^{REG}_htn ∈ PSPACE`. -/
theorem cor_4_2_18 : Cx.PSPACE (PlanEx fun P => P.IsREG) := by
  let r : Polynomial ℕ := 10 * (Polynomial.X + 2) ^ 2 + (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 10 * (n + 2) ^ 2 + (n + 1) ^ 2 := fun n => by simp [r]
  refine inPSpace_planEx (pt_trB 1) (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨R, rkL⟩ := b
    exact (p.toProblem.thm_3_0_1 (wf_toProblem p)).2 (((trB_iff 1 p R rkL).1 hb).isTailREC_h hp)
  · obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -⟩ :=
      exists_trCert hp ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hY)
    refine ⟨(R, rkL), hb, ?_⟩
    rw [hr]
    have : sz (R, rkL) ≤ 10 * (sz p + 2) ^ 2 := sz_rcert_le hRN hRl hrkN hrkl
    omega
  · have hb := (p.toProblem.lem_4_2_15 (wf_toProblem p) ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hY)
      (tnI_card_le p) (one_le_S p) (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
    nlinarith

/-- The check of `REG ∩ TO`. -/
def regTOB (x : ProbDesc × (List ℕ × List (ℕ × ℕ))) : Bool :=
  trB 1 x && toB x.1.tnI && methodsRB toB x.1 x.2.1

theorem pt_regTOB : PT regTOB :=
  (PT.and (PT.and (pt_trB 1) (pt_toB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst)))))
    (pt_methodsRB pt_toB PT.fst (PT.fst.comp PT.snd))).of_eq fun _ => rfl

/-- **Corollary 4.2.18 (REG ∩ TO).** `PlanEx^{REG ∩ TO}_htn ∈ PSPACE`. -/
theorem cor_4_2_18_TO : Cx.PSPACE (PlanEx fun P => P.IsREG ∧ P.IsTO) := by
  let r : Polynomial ℕ := 10 * (Polynomial.X + 2) ^ 2 + (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 10 * (n + 2) ^ 2 + (n + 1) ^ 2 := fun n => by simp [r]
  refine inPSpace_planEx pt_regTOB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨R, rkL⟩ := b
    simp only [regTOB, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hc := (trB_iff 1 p R rkL).1 h1
    exact ⟨(p.toProblem.thm_3_0_1 (wf_toProblem p)).2 (hc.isTailREC_h hp),
      (toB_iff hp.tnI).1 h2, methodsRB_sound hp (trCert_closed hc) (fun ht => toB_iff ht) h3⟩
  · obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, hRr⟩ :=
      exists_trCert hp ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hY.1)
    refine ⟨(R, rkL), ?_, ?_⟩
    · simp only [regTOB, Bool.and_eq_true]
      exact ⟨⟨hb, (toB_iff hp.tnI).2 hY.2.1⟩,
        methodsRB_complete hp hRr (fun ht => toB_iff ht) hY.2.2⟩
    · rw [hr]
      have : sz (R, rkL) ≤ 10 * (sz p + 2) ^ 2 := sz_rcert_le hRN hRl hrkN hrkl
      omega
  · have hb := (p.toProblem.lem_4_2_19 (wf_toProblem p)
      ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hY.1) hY.2 (tnI_card_le p) (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
    have : sz p - 1 ≤ sz p := Nat.sub_le _ _
    nlinarith

/-! ### Corollary 4.2.20 -/

/-- The check of `TAIL-REC ∩ TO`. -/
def trTOB (x : ProbDesc × (ℕ × (List ℕ × List (ℕ × ℕ)))) : Bool :=
  trHB x && toB x.1.tnI && methodsRB toB x.1 x.2.2.1

theorem pt_trTOB : PT trTOB :=
  (PT.and (PT.and pt_trHB (pt_toB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst)))))
    (pt_methodsRB pt_toB PT.fst (PT.fst.comp (PT.snd.comp PT.snd)))).of_eq fun _ => rfl

/-- **Corollary 4.2.20 (TAIL-REC ∩ TO).** `PlanEx^{TAIL-REC ∩ TO}_htn ∈ PSPACE`. -/
theorem cor_4_2_20 : Cx.PSPACE (PlanEx fun P => P.IsTailREC ∧ P.IsTO) := by
  let r : Polynomial ℕ := 11 * (2 * Polynomial.X + 1) ^ 2 + Polynomial.X + Polynomial.X ^ 2
  have hr : ∀ n, r.eval n = 11 * (2 * n + 1) ^ 2 + n + n ^ 2 := fun n => by simp [r]
  refine inPSpace_planEx pt_trTOB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · simp only [trTOB, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    obtain ⟨htr, hcl⟩ := trHB_sound hp h1
    exact ⟨htr, (toB_iff hp.tnI).1 h2, methodsRB_sound hp hcl (fun ht => toB_iff ht) h3⟩
  · obtain ⟨b, hb, hsz, hRr⟩ := exists_trHB hp hY.1
    refine ⟨b, ?_, ?_⟩
    · simp only [trTOB, Bool.and_eq_true]
      exact ⟨⟨hb, (toB_iff hp.tnI).2 hY.2.1⟩, methodsRB_complete hp hRr (fun ht => toB_iff ht) hY.2.2⟩
    · rw [hr]; omega
  · have hb := (p.toProblem.lem_4_2_19 (wf_toProblem p) (isTailREC_h_of_isTailREC hp hY.1) hY.2
      (tnI_card_le p) (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
    have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
    have : (sz p - 1) * (numsOf p).length ≤ sz p * sz p := Nat.mul_le_mul (Nat.sub_le _ _) hK
    nlinarith

/-- The check of `ACYC ∩ TO`. -/
def acTOB (x : ProbDesc × (List ℕ × List (ℕ × ℕ))) : Bool :=
  acycB x.1 x.2 && toB x.1.tnI && methodsRB toB x.1 x.2.1

theorem pt_acTOB : PT acTOB :=
  (PT.and (PT.and pt_acycB (pt_toB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst)))))
    (pt_methodsRB pt_toB PT.fst (PT.fst.comp PT.snd))).of_eq fun _ => rfl

theorem isTailREC_of_isACYC {p : ProbDesc} (h : p.toProblem.IsACYC) : p.toProblem.IsTailREC :=
  HTN.Problem.IsAcyclic.isTailRecursive h

/-- **Corollary 4.2.20 (ACYC ∩ TO).** `PlanEx^{ACYC ∩ TO}_htn ∈ PSPACE`. -/
theorem cor_4_2_20_acyc : Cx.PSPACE (PlanEx fun P => P.IsACYC ∧ P.IsTO) := by
  let r : Polynomial ℕ := 10 * (2 * Polynomial.X + 2) ^ 2 + Polynomial.X + Polynomial.X ^ 2
  have hr : ∀ n, r.eval n = 10 * (2 * n + 2) ^ 2 + n + n ^ 2 := fun n => by simp [r]
  refine inPSpace_planEx pt_acTOB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨R, rkL⟩ := b
    simp only [acTOB, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hc := (acycB_iff p R rkL).1 h1
    exact ⟨hc.isACYC, (toB_iff hp.tnI).1 h2,
      methodsRB_sound hp (fun _ hr => hc.reach_mem hr) (fun ht => toB_iff ht) h3⟩
  · obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -, hRr, -⟩ := exists_acycCert hp hY.1
    refine ⟨(R, rkL), ?_, ?_⟩
    · simp only [acTOB, Bool.and_eq_true]
      exact ⟨⟨hb, (toB_iff hp.tnI).2 hY.2.1⟩, methodsRB_complete hp hRr (fun ht => toB_iff ht) hY.2.2⟩
    · rw [hr]
      have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
      have := sz_rcert_le (H := (numsOf p).length + 1) hRN hRl
        (fun q hq => ⟨(hrkN q hq).1, Nat.lt_succ_of_le (hrkN q hq).2⟩) hrkl
      have h2 : (sz p + ((numsOf p).length + 1) + 1) ^ 2 ≤ (2 * sz p + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      omega
  · have hb := (p.toProblem.lem_4_2_19 (wf_toProblem p)
      (isTailREC_h_of_isTailREC hp (isTailREC_of_isACYC hY.1)) hY.2
      (tnI_card_le p) (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
    have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
    have : (sz p - 1) * (numsOf p).length ≤ sz p * sz p := Nat.mul_le_mul (Nat.sub_le _ _) hK
    nlinarith

/-! ### Corollary 4.2.22 -/

/-- The check of `TAIL-REC ∩ TO-M`. -/
def trTOMB (x : ProbDesc × (ℕ × (List ℕ × List (ℕ × ℕ)))) : Bool :=
  trHB x && methodsRB toB x.1 x.2.2.1

theorem pt_trTOMB : PT trTOMB :=
  (PT.and pt_trHB (pt_methodsRB pt_toB PT.fst (PT.fst.comp (PT.snd.comp PT.snd)))).of_eq
    fun _ => rfl

/-- **Corollary 4.2.22 (TAIL-REC ∩ TO-M).** `PlanEx^{TAIL-REC ∩ TO-M}_htn ∈ PSPACE`. -/
theorem cor_4_2_22 : Cx.PSPACE (PlanEx fun P => P.IsTailREC ∧ P.IsTO_M) := by
  let r : Polynomial ℕ := 11 * (2 * Polynomial.X + 1) ^ 2 + Polynomial.X * (1 + Polynomial.X ^ 2)
  have hr : ∀ n, r.eval n = 11 * (2 * n + 1) ^ 2 + n * (1 + n ^ 2) := fun n => by simp [r]
  refine inPSpace_planEx pt_trTOMB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · simp only [trTOMB, Bool.and_eq_true] at hb
    obtain ⟨h1, h3⟩ := hb
    obtain ⟨htr, hcl⟩ := trHB_sound hp h1
    exact ⟨htr, methodsRB_sound hp hcl (fun ht => toB_iff ht) h3⟩
  · obtain ⟨b, hb, hsz, hRr⟩ := exists_trHB hp hY.1
    refine ⟨b, ?_, ?_⟩
    · simp only [trTOMB, Bool.and_eq_true]
      exact ⟨hb, methodsRB_complete hp hRr (fun ht => toB_iff ht) hY.2⟩
    · rw [hr]; omega
  · have hb := (p.toProblem.lem_4_2_21 (wf_toProblem p) (isTailREC_h_of_isTailREC hp hY.1) hY.2
      (tnI_card_le p) (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
    have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
    have : (sz p - 1) * (numsOf p).length ≤ sz p * sz p := Nat.mul_le_mul (Nat.sub_le _ _) hK
    have : sz p * (1 + (sz p - 1) * (numsOf p).length) ≤ sz p * (1 + sz p ^ 2) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    omega

/-- The check of `ACYC ∩ TO-M`. -/
def acTOMB (x : ProbDesc × (List ℕ × List (ℕ × ℕ))) : Bool :=
  acycB x.1 x.2 && methodsRB toB x.1 x.2.1

theorem pt_acTOMB : PT acTOMB :=
  (PT.and pt_acycB (pt_methodsRB pt_toB PT.fst (PT.fst.comp PT.snd))).of_eq fun _ => rfl

/-- **Corollary 4.2.22 (ACYC ∩ TO-M).** `PlanEx^{ACYC ∩ TO-M}_htn ∈ PSPACE`. -/
theorem cor_4_2_22_acyc : Cx.PSPACE (PlanEx fun P => P.IsACYC ∧ P.IsTO_M) := by
  let r : Polynomial ℕ := 10 * (2 * Polynomial.X + 2) ^ 2 + Polynomial.X * (1 + Polynomial.X ^ 2)
  have hr : ∀ n, r.eval n = 10 * (2 * n + 2) ^ 2 + n * (1 + n ^ 2) := fun n => by simp [r]
  refine inPSpace_planEx pt_acTOMB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨R, rkL⟩ := b
    simp only [acTOMB, Bool.and_eq_true] at hb
    obtain ⟨h1, h3⟩ := hb
    have hc := (acycB_iff p R rkL).1 h1
    exact ⟨hc.isACYC, methodsRB_sound hp (fun _ hr => hc.reach_mem hr) (fun ht => toB_iff ht) h3⟩
  · obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -, hRr, -⟩ := exists_acycCert hp hY.1
    refine ⟨(R, rkL), ?_, ?_⟩
    · simp only [acTOMB, Bool.and_eq_true]
      exact ⟨hb, methodsRB_complete hp hRr (fun ht => toB_iff ht) hY.2⟩
    · rw [hr]
      have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
      have := sz_rcert_le (H := (numsOf p).length + 1) hRN hRl
        (fun q hq => ⟨(hrkN q hq).1, Nat.lt_succ_of_le (hrkN q hq).2⟩) hrkl
      have h2 : (sz p + ((numsOf p).length + 1) + 1) ^ 2 ≤ (2 * sz p + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      omega
  · have hb := (p.toProblem.lem_4_2_21 (wf_toProblem p)
      (isTailREC_h_of_isTailREC hp (isTailREC_of_isACYC hY.1)) hY.2
      (tnI_card_le p) (meth_card_le p)).1
    refine IsHTNProgBound.mono hb ?_
    rw [hr]
    have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
    have : (sz p - 1) * (numsOf p).length ≤ sz p * sz p := Nat.mul_le_mul (Nat.sub_le _ _) hK
    have : sz p * (1 + (sz p - 1) * (numsOf p).length) ≤ sz p * (1 + sz p ^ 2) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    omega

end Article

end HTN
