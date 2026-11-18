import HtnComplexity.Article.AProgSpace
/-!
# TIHTN upper space bounds by acyclic progression (Cors. 4.2.23–4.2.25)

Each corollary instantiates `HTN.Article.inPSpace_planExTI` with a certificate of the class and
the TIHTN part of the article's progression bound (Lems. 4.2.15, 4.2.19, 4.2.21 bound acyclic
progression as well):

* Cor. 4.2.23 — `TAIL-REC ∩ TO-M` and `ACYC ∩ TO-M` (`HTN.Article.cor_4_2_23_tr`,
  `cor_4_2_23_acyc`); the unrestricted case is in `HtnComplexity/Article/TIUnres.lean`;
* Cor. 4.2.24 — `REG`, `REG ∩ TO`, `REG ∩ TO-M` and the same with `ACYC`;
* Cor. 4.2.25 — `noHTN` and `noHTN ∩ TO-tn_I`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

theorem IsTIHTNProgBound.mono {p : ProbDesc} {n n' : ℕ} (h : p.toProblem.IsTIHTNProgBound n)
    (hle : n ≤ n') : p.toProblem.IsTIHTNProgBound n' := fun nd hnd => (h nd hnd).trans hle

/-! ### Corollary 4.2.23 -/

/-- **Corollary 4.2.23 (TAIL-REC ∩ TO-M).** `PlanEx^{TAIL-REC ∩ TO-M}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_23_tr : Cx.PSPACE (PlanExTI fun P => P.IsTailREC ∧ P.IsTO_M) := by
  let r : Polynomial ℕ := 11 * (2 * Polynomial.X + 1) ^ 2 + Polynomial.X * (1 + Polynomial.X ^ 2)
  have hr : ∀ n, r.eval n = 11 * (2 * n + 1) ^ 2 + n * (1 + n ^ 2) := fun n => by simp [r]
  refine inPSpace_planExTI pt_trTOMB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
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
      (tnI_card_le p) (meth_card_le p)).2
    refine IsTIHTNProgBound.mono hb ?_
    rw [hr]
    have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
    have : (sz p - 1) * (numsOf p).length ≤ sz p * sz p := Nat.mul_le_mul (Nat.sub_le _ _) hK
    have : sz p * (1 + (sz p - 1) * (numsOf p).length) ≤ sz p * (1 + sz p ^ 2) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    omega

/-- **Corollary 4.2.23 (ACYC ∩ TO-M).** `PlanEx^{ACYC ∩ TO-M}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_23_acyc : Cx.PSPACE (PlanExTI fun P => P.IsACYC ∧ P.IsTO_M) := by
  let r : Polynomial ℕ := 10 * (2 * Polynomial.X + 2) ^ 2 + Polynomial.X * (1 + Polynomial.X ^ 2)
  have hr : ∀ n, r.eval n = 10 * (2 * n + 2) ^ 2 + n * (1 + n ^ 2) := fun n => by simp [r]
  refine inPSpace_planExTI pt_acTOMB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
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
      (tnI_card_le p) (meth_card_le p)).2
    refine IsTIHTNProgBound.mono hb ?_
    rw [hr]
    have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
    have : (sz p - 1) * (numsOf p).length ≤ sz p * sz p := Nat.mul_le_mul (Nat.sub_le _ _) hK
    have : sz p * (1 + (sz p - 1) * (numsOf p).length) ≤ sz p * (1 + sz p ^ 2) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    omega

/-! ### Corollary 4.2.24 -/

/-- The regular bound, for both progression and acyclic progression. -/
theorem regBound {p : ProbDesc} (hY : p.toProblem.IsREG) :
    p.toProblem.IsProgBound (sz p * sz p ^ 1) :=
  p.toProblem.lem_4_2_15 (wf_toProblem p) ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hY)
    (tnI_card_le p) (one_le_S p) (meth_card_le p)

/-- **Corollary 4.2.24 (REG).** `PlanEx^{REG}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_24 : Cx.PSPACE (PlanExTI fun P => P.IsREG) := by
  let r : Polynomial ℕ := 10 * (Polynomial.X + 2) ^ 2 + (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 10 * (n + 2) ^ 2 + (n + 1) ^ 2 := fun n => by simp [r]
  refine inPSpace_planExTI (pt_trB 1) (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨R, rkL⟩ := b
    exact (p.toProblem.thm_3_0_1 (wf_toProblem p)).2 (((trB_iff 1 p R rkL).1 hb).isTailREC_h hp)
  · obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, -⟩ :=
      exists_trCert hp ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hY)
    refine ⟨(R, rkL), hb, ?_⟩
    rw [hr]
    have : sz (R, rkL) ≤ 10 * (sz p + 2) ^ 2 := sz_rcert_le hRN hRl hrkN hrkl
    omega
  · refine IsTIHTNProgBound.mono (regBound hY).2 ?_
    rw [hr]
    nlinarith

/-- **Corollary 4.2.24 (REG ∩ TO).** `PlanEx^{REG ∩ TO}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_24_TO : Cx.PSPACE (PlanExTI fun P => P.IsREG ∧ P.IsTO) := by
  let r : Polynomial ℕ := 10 * (Polynomial.X + 2) ^ 2 + (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 10 * (n + 2) ^ 2 + (n + 1) ^ 2 := fun n => by simp [r]
  refine inPSpace_planExTI pt_regTOB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
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
  · refine IsTIHTNProgBound.mono (regBound hY.1).2 ?_
    rw [hr]
    nlinarith

/-- The check of `REG ∩ TO-M`. -/
def regTOMB (x : ProbDesc × (List ℕ × List (ℕ × ℕ))) : Bool :=
  trB 1 x && methodsRB toB x.1 x.2.1

theorem pt_regTOMB : PT regTOMB :=
  (PT.and (pt_trB 1) (pt_methodsRB pt_toB PT.fst (PT.fst.comp PT.snd))).of_eq fun _ => rfl

/-- **Corollary 4.2.24 (REG ∩ TO-M).** `PlanEx^{REG ∩ TO-M}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_24_TOM : Cx.PSPACE (PlanExTI fun P => P.IsREG ∧ P.IsTO_M) := by
  let r : Polynomial ℕ := 10 * (Polynomial.X + 2) ^ 2 + (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 10 * (n + 2) ^ 2 + (n + 1) ^ 2 := fun n => by simp [r]
  refine inPSpace_planExTI pt_regTOMB (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨R, rkL⟩ := b
    simp only [regTOMB, Bool.and_eq_true] at hb
    obtain ⟨h1, h3⟩ := hb
    have hc := (trB_iff 1 p R rkL).1 h1
    exact ⟨(p.toProblem.thm_3_0_1 (wf_toProblem p)).2 (hc.isTailREC_h hp),
      methodsRB_sound hp (trCert_closed hc) (fun ht => toB_iff ht) h3⟩
  · obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, hRr⟩ :=
      exists_trCert hp ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hY.1)
    refine ⟨(R, rkL), ?_, ?_⟩
    · simp only [regTOMB, Bool.and_eq_true]
      exact ⟨hb, methodsRB_complete hp hRr (fun ht => toB_iff ht) hY.2⟩
    · rw [hr]
      have : sz (R, rkL) ≤ 10 * (sz p + 2) ^ 2 := sz_rcert_le hRN hRl hrkN hrkl
      omega
  · refine IsTIHTNProgBound.mono (regBound hY.1).2 ?_
    rw [hr]
    nlinarith

/-- The certificate of `REG ∩ ACYC`: a certificate of tail recursion of height one and an
acyclicity certificate. -/
abbrev RACert : Type := (List ℕ × List (ℕ × ℕ)) × (List ℕ × List (ℕ × ℕ))

/-- The check of `REG ∩ ACYC`, with an extra check `g` of the methods of the reachable names and
`tI` of the initial network. -/
def regAcB (tI g : TnDesc → Bool) (x : ProbDesc × RACert) : Bool :=
  trB 1 (x.1, x.2.1) && acycB x.1 x.2.2 && tI x.1.tnI && methodsRB g x.1 x.2.1.1

theorem pt_regAcB {tI g : TnDesc → Bool} (htI : PT tI) (hg : PT g) : PT (regAcB tI g) := by
  have h1 := (pt_trB 1).comp (PT.pair (PT.fst (α := ProbDesc) (β := RACert)) (PT.fst.comp PT.snd))
  have h2 := pt_acycB.comp (PT.pair (PT.fst (α := ProbDesc) (β := RACert)) (PT.snd.comp PT.snd))
  have h3 : PT fun x : ProbDesc × RACert => tI x.1.tnI :=
    htI.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst)))
  have h4 : PT fun x : ProbDesc × RACert => methodsRB g x.1 x.2.1.1 :=
    pt_methodsRB hg PT.fst (PT.fst.comp (PT.fst.comp PT.snd))
  exact (PT.and (PT.and (PT.and h1 h2) h3) h4).of_eq fun _ => rfl

/-- The common part of the corollaries for `REG ∩ ACYC`. -/
theorem regAc_gen {tI g : TnDesc → Bool} (htI : PT tI) (hg : PT g) {QI : TaskNetwork ℕ ℕ ℕ → Prop}
    {Pm : TaskNetwork ℕ ℕ ℕ → Prop}
    (hQI : ∀ {p : ProbDesc}, p.Valid → (tI p.tnI = true ↔ QI p.toProblem.tnI))
    (hPm : ∀ {p : ProbDesc} {t : TnDesc}, TnValid p.Declared t → (g t = true ↔ Pm t.toTaskNetwork)) :
    Cx.PSPACE (PlanExTI fun P => P.IsREG ∧ P.IsACYC ∧ QI P.tnI ∧
      ∀ m, P.toPos.ReachableMethod m → Pm m.subtasks) := by
  let r : Polynomial ℕ := 20 * (2 * Polynomial.X + 2) ^ 2 + (Polynomial.X + 1) ^ 2
  have hr : ∀ n, r.eval n = 20 * (2 * n + 2) ^ 2 + (n + 1) ^ 2 := fun n => by simp [r]
  refine inPSpace_planExTI (pt_regAcB htI hg) (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · obtain ⟨⟨R, rkL⟩, ⟨R', rkL'⟩⟩ := b
    simp only [regAcB, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
    have hc := (trB_iff 1 p R rkL).1 h1
    exact ⟨(p.toProblem.thm_3_0_1 (wf_toProblem p)).2 (hc.isTailREC_h hp),
      ((acycB_iff p R' rkL').1 h2).isACYC, (hQI hp).1 h3,
      methodsRB_sound hp (trCert_closed hc) (fun ht => hPm ht) h4⟩
  · obtain ⟨hreg, hac, hqi, hpm⟩ := hY
    obtain ⟨R, rkL, hb, hRN, hRl, hrkN, hrkl, hRr⟩ :=
      exists_trCert hp ((p.toProblem.thm_3_0_1 (wf_toProblem p)).1 hreg)
    obtain ⟨R', rkL', hb', hRN', hRl', hrkN', hrkl', -⟩ := exists_acycCert hp hac
    refine ⟨((R, rkL), (R', rkL')), ?_, ?_⟩
    · simp only [regAcB, Bool.and_eq_true]
      exact ⟨⟨⟨hb, hb'⟩, (hQI hp).2 hqi⟩, methodsRB_complete hp hRr (fun ht => hPm ht) hpm⟩
    · rw [hr, sz_prod]
      have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
      have e1 : sz (R, rkL) ≤ 10 * (sz p + 2) ^ 2 := sz_rcert_le hRN hRl hrkN hrkl
      have e2 := sz_rcert_le (H := (numsOf p).length + 1) hRN' hRl'
        (fun q hq => ⟨(hrkN' q hq).1, Nat.lt_succ_of_le (hrkN' q hq).2⟩) hrkl'
      have e3 : (sz p + 2) ^ 2 ≤ (2 * sz p + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e4 : (sz p + ((numsOf p).length + 1) + 1) ^ 2 ≤ (2 * sz p + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      omega
  · refine IsTIHTNProgBound.mono (regBound hY.1).2 ?_
    rw [hr]
    nlinarith

/-- **Corollary 4.2.24 (REG ∩ ACYC).** `PlanEx^{REG ∩ ACYC}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_24_regAcyc : Cx.PSPACE (PlanExTI fun P => P.IsREG ∧ P.IsACYC) := by
  have h := regAc_gen (tI := fun _ => true) (g := fun _ => true) (QI := fun _ => True)
    (Pm := fun _ => True) (PT.const true) (PT.const true) (fun _ => by simp) (fun _ => by simp)
  refine (congrArg Cx.PSPACE ?_).mp h
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hv, ⟨h1, h2, -, -⟩, h3⟩; exact ⟨p, rfl, hv, ⟨h1, h2⟩, h3⟩
  · rintro ⟨p, rfl, hv, ⟨h1, h2⟩, h3⟩; exact ⟨p, rfl, hv, ⟨h1, h2, trivial, fun _ _ => trivial⟩, h3⟩

/-- **Corollary 4.2.24 (REG ∩ ACYC ∩ TO).** `PlanEx^{REG ∩ ACYC ∩ TO}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_24_regAcyc_TO : Cx.PSPACE (PlanExTI fun P => P.IsREG ∧ P.IsACYC ∧ P.IsTO) := by
  have h := regAc_gen (QI := fun tn => tn.IsTotallyOrdered) (Pm := fun tn => tn.IsTotallyOrdered)
    pt_toB pt_toB (fun hp => toB_iff hp.tnI) (fun ht => toB_iff ht)
  refine (congrArg Cx.PSPACE ?_).mp h
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hv, ⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨p, rfl, hv, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨p, rfl, hv, ⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨p, rfl, hv, ⟨h1, h2, h3, h4⟩, h5⟩

/-- **Corollary 4.2.24 (REG ∩ ACYC ∩ TO-M).** `PlanEx^{REG ∩ ACYC ∩ TO-M}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_24_regAcyc_TOM : Cx.PSPACE (PlanExTI fun P => P.IsREG ∧ P.IsACYC ∧ P.IsTO_M) := by
  have h := regAc_gen (tI := fun _ => true) (QI := fun _ => True)
    (Pm := fun tn => tn.IsTotallyOrdered) (PT.const true) pt_toB (fun _ => by simp)
    (fun ht => toB_iff ht)
  refine (congrArg Cx.PSPACE ?_).mp h
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hv, ⟨h1, h2, -, h4⟩, h5⟩; exact ⟨p, rfl, hv, ⟨h1, h2, h4⟩, h5⟩
  · rintro ⟨p, rfl, hv, ⟨h1, h2, h4⟩, h5⟩; exact ⟨p, rfl, hv, ⟨h1, h2, trivial, h4⟩, h5⟩

/-! ### Corollary 4.2.25 -/

theorem not_reachable_of_noHTN {p : ProbDesc} (h : p.toProblem.IsNoHTN) {c : ℕ}
    (hc : p.toProblem.toPos.ReachableName c) : False := by
  induction hc with
  | @tnI t c ht hc =>
    obtain ⟨a, ha⟩ := h t ht
    rw [ha] at hc; cases hc
  | method _ _ _ _ ih => exact ih

theorem isTailREC_h_zero_of_noHTN {p : ProbDesc} (h : p.toProblem.IsNoHTN) :
    p.toProblem.IsTailREC_h 0 :=
  ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ => Or.inl trivial⟩,
    fun _ ⟨_, hr⟩ _ _ _ _ _ => absurd hr (fun h' => not_reachable_of_noHTN h h'),
    fun _ ⟨_, hr⟩ _ _ _ _ _ => absurd hr (fun h' => not_reachable_of_noHTN h h')⟩,
    fun _ => 0, fun c hc => absurd hc (fun h' => not_reachable_of_noHTN h h'),
    fun c _ hc _ => absurd hc (fun h' => not_reachable_of_noHTN h h')⟩

/-- The check of `noHTN`, with an extra check of the initial network. -/
def noHTNCB (tI : TnDesc → Bool) (x : ProbDesc × List ℕ) : Bool := NoHTN.noHTNB x.1.tnI && tI x.1.tnI

theorem noHTN_gen {tI : TnDesc → Bool} (htI : PT tI) {QI : TaskNetwork ℕ ℕ ℕ → Prop}
    (hQI : ∀ {p : ProbDesc}, p.Valid → (tI p.tnI = true ↔ QI p.toProblem.tnI)) :
    Cx.PSPACE (PlanExTI fun P => P.IsNoHTN ∧ QI P.tnI) := by
  let r : Polynomial ℕ := Polynomial.X + 1
  have hr : ∀ n, r.eval n = n + 1 := fun n => by simp [r]
  have hpt : PT (noHTNCB tI) :=
    (PT.and (NoHTN.pt_noHTNB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))))
      (htI.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))))).of_eq fun _ => rfl
  refine inPSpace_planExTI hpt (fun p b hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · simp only [noHTNCB, Bool.and_eq_true] at hb
    exact ⟨(NoHTN.noHTNB_iff _).1 hb.1, (hQI hp).1 hb.2⟩
  · refine ⟨[], by simp [noHTNCB, (NoHTN.noHTNB_iff _).2 hY.1, (hQI hp).2 hY.2], ?_⟩
    rw [hr]; simp [sz_nil]
  · have hb := (p.toProblem.lem_4_2_15 (wf_toProblem p) (isTailREC_h_zero_of_noHTN hY.1)
      (tnI_card_le p) (one_le_S p) (meth_card_le p)).2
    refine IsTIHTNProgBound.mono hb ?_
    rw [hr]; simp

/-- **Corollary 4.2.25 (noHTN).** `PlanEx^{noHTN}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_25 : Cx.PSPACE (PlanExTI fun P => P.IsNoHTN) := by
  have h := noHTN_gen (tI := fun _ => true) (QI := fun _ => True) (PT.const true) (fun _ => by simp)
  refine (congrArg Cx.PSPACE ?_).mp h
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hv, ⟨h1, -⟩, h3⟩; exact ⟨p, rfl, hv, h1, h3⟩
  · rintro ⟨p, rfl, hv, h1, h3⟩; exact ⟨p, rfl, hv, ⟨h1, trivial⟩, h3⟩

/-- **Corollary 4.2.25 (noHTN ∩ TO-tn_I).** `PlanEx^{noHTN ∩ TO-tn_I}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_25_TO : Cx.PSPACE (PlanExTI fun P => P.IsNoHTN ∧ P.IsTO_tnI) :=
  noHTN_gen (QI := fun tn => tn.IsTotallyOrdered) pt_toB (fun hp => toB_iff hp.tnI)

end Article

end HTN
