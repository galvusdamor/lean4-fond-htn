import ComplexityTheory.Collapse.Search
/-!
# Eliminating the advice: `EXPTIME ⊆ PSPACE/poly ⟹ EXPTIME ⊆ PSPACE`

This file puts together the two halves of the argument:

* `ComplexityTheory/Collapse/Verify.lean` — a claimed table of acceptance values which passes
  the two local checks *is* the table of `HTN.PSpace.ASpace.accWithin`;
* `ComplexityTheory/Collapse/Search.lean` — the formula "there is a candidate advice whose
  claimed table passes the local checks and which claims that the initial configuration accepts"
  is a predicate of the polynomial-space class as soon as the advised predicate is.

The naive argument — "the machine iterates over all polynomially many advice strings" — is
**not** sound on its own: a wrong advice string can make the machine accept a word outside the
language, and a machine that accepts as soon as *some* advice string says so decides the union
of the advised languages, not the right one.  What repairs it is that the answers the advice is
asked for can be *checked*: the hypothesis is applied not to the language of the machine but to
its **configuration questions** `HTN.PSpace.ASpace.confLang`, whose answers satisfy two local
equations that pin them down (the step counter is what removes the spurious solutions of the
local rule).  A candidate advice is then accepted only after its whole claimed table has been
verified against those equations, so a wrong candidate is rejected and the search is sound.

The main results are

* `HTN.PSpace.ASpace.L_of_searchB` — **soundness**: if some candidate passes, the word is in the
  language.  No assumption at all on the advised predicate;
* `HTN.PSpace.ASpace.searchB_of_L` — **completeness**: the genuine advice passes;
* `HTN.PSpace.inPSpace_of_confLang` — a machine whose configuration questions are decided in
  polynomial space with polynomial advice has its language decided in polynomial space, with no
  advice.
-/

namespace HTN

namespace PSpace

open PTime

namespace ASpace

variable {M : ASpace} {q : Args → Bool}

/-- The table of acceptance values a candidate advice `a` claims, on input `x`. -/
def qtbl (M : ASpace) (q : Args → Bool) (x a : List Bool) : List Bool → List Bool → Bool :=
  fun c t => claim M q x a c t

/-! ### Reading the layers of the formula off an explicit argument list -/

theorem allBody_apply (c' c t' a x : List Bool) :
    allBody M q [c', c, t', a, x] = (!M.stepB [c', c, x] || qtbl M q x a c' t') := rfl

theorem exBody_apply (c' c t' a x : List Bool) :
    exBody M q [c', c, t', a, x] = (M.stepB [c', c, x] && qtbl M q x a c' t') := rfl

theorem allQ_apply (c t' a x : List Bool) :
    allQ M q [c, t', a, x] =
      allLenB (M.w x) (fun c' => !M.stepB [c', c, x] || qtbl M q x a c' t') := rfl

theorem exQ_apply (c t' a x : List Bool) :
    exQ M q [c, t', a, x] =
      anyLen (M.w x) (fun c' => M.stepB [c', c, x] && qtbl M q x a c' t') := rfl

theorem chkCT_apply (c t' a x : List Bool) :
    chkCT M q [c, t', a, x] =
      ((!decide (t' = zeros (M.w x + 1)) ||
          (qtbl M q x a c (zeros (M.w x + 1)) == M.accB [c, x])) &&
        (decide (t' = ones (M.w x + 1)) ||
          (qtbl M q x a c (succB t') == ruleV M x (qtbl M q x a) c t'))) := rfl

theorem chkT_apply (t' a x : List Bool) :
    chkT M q [t', a, x] = allLenB (M.w x) (fun c => chkCT M q [c, t', a, x]) := rfl

theorem consistentB_apply (a x : List Bool) :
    consistentB M q [a, x] = allLenB (M.w x + 1) (fun t' => chkT M q [t', a, x]) := rfl

theorem searchB_apply (a x : List Bool) :
    searchB M q [a, x] =
      (consistentB M q [a, x] &&
        claim M q x a (M.initF [x]) (ones (M.w x + 1))) := rfl

theorem answerB_apply (f : Fn) (x : List Bool) :
    answerB M q f [x] = anyLen (f [x]).length (fun a => searchB M q [a, x]) := rfl

/-! ### The check is exactly the consistency of the claimed table -/

/-- **Passing the local checks is being consistent.** -/
theorem consistentB_iff (a x : List Bool) :
    consistentB M q [a, x] = true ↔ Consistent M x (qtbl M q x a) := by
  rw [consistentB_apply, allLenB_eq_true]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro c hc
      have h1 := h (zeros (M.w x + 1)) (by simp)
      rw [chkT_apply, allLenB_eq_true] at h1
      have h2 := h1 c hc
      rw [chkCT_apply, Bool.and_eq_true_iff] at h2
      have h3 := h2.1
      simp only [decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at h3
      exact h3
    · intro t' ht' hne c hc
      have h1 := h t' ht'
      rw [chkT_apply, allLenB_eq_true] at h1
      have h2 := h1 c hc
      rw [chkCT_apply, Bool.and_eq_true_iff] at h2
      have h3 := h2.2
      rw [decide_eq_false hne] at h3
      simpa using h3
  · intro h t' ht'
    rw [chkT_apply, allLenB_eq_true]
    intro c hc
    rw [chkCT_apply, Bool.and_eq_true_iff]
    constructor
    · by_cases hz : t' = zeros (M.w x + 1)
      · subst hz
        simp [h.base c hc]
      · simp [hz]
    · by_cases ho : t' = ones (M.w x + 1)
      · simp [ho]
      · simp [ho, h.step t' ht' ho c hc]

/-! ### Soundness -/

/-- **Soundness of the brute force**: a candidate advice that passes the check and claims that
the initial configuration accepts is right — the word is in the language.  Nothing whatever is
assumed of the advised predicate. -/
theorem L_of_searchB {a x : List Bool} (h : searchB M q [a, x] = true) : M.L x := by
  rw [searchB_apply, Bool.and_eq_true_iff] at h
  obtain ⟨hcons, hinit⟩ := h
  have hC := (consistentB_iff a x).1 hcons
  have hlen : (M.initF [x]).length = M.w x := M.initF_length x
  have heq := consistent_eq hC (val (ones (M.w x + 1))) (ones (M.w x + 1)) rfl (by simp)
    (M.initF [x]) hlen
  have : M.accWithin x (val (ones (M.w x + 1))) (M.initF [x]) = true := by
    rw [← heq]; exact hinit
  rwa [val_ones] at this

/-! ### Completeness -/

/-- A table which agrees with `HTN.PSpace.ASpace.accWithin` on the well-formed arguments is
consistent. -/
theorem consistent_of_table_eq {x : List Bool} {Q : List Bool → List Bool → Bool}
    (hQ : ∀ c t, c.length = M.w x → t.length = M.w x + 1 → Q c t = M.accWithin x (val t) c) :
    Consistent M x Q := by
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hQ c _ hc (by simp), val_zeros, accWithin_zero]
  · intro t' ht' hne c hc
    have hval : val (succB t') = val t' + 1 := by
      have hlt : val t' + 1 < 2 ^ (M.w x + 1) := by
        have h1 := val_lt_two_pow t'
        rw [ht'] at h1
        have h2 : val t' ≠ 2 ^ (M.w x + 1) - 1 := by
          intro hcon
          exact hne (val_inj_of_length_eq _ _ (by simp [ht']) (by rw [hcon, val_ones]))
        omega
      rw [val_succB, ht', Nat.mod_eq_of_lt hlt]
    rw [hQ c _ hc (by simp [ht']), hval,
      accWithin_succ_eq_ruleV (M := M) (x := x) (val t') c t' rfl]
    exact ruleV_congr fun c' hc' => (hQ c' t' hc' ht').symm

/-- **Completeness of the brute force**: a candidate advice whose decoded advice is the genuine
one passes the check, on a word of the language. -/
theorem searchB_of_L {adv : ℕ → List Bool}
    (hcorr : ∀ z, M.confLang z ↔ q [z, adv z.length] = true) {a x : List Bool}
    (ha : decC a = adv (3 * M.w x + 2 + x.length)) (hx : M.L x) : searchB M q [a, x] = true := by
  have hclaim : ∀ c t, c.length = M.w x → t.length = M.w x + 1 →
      qtbl M q x a c t = M.accWithin x (val t) c := by
    intro c t hc ht
    have hz : (encS (ones (M.w x)) c t x).length = 3 * M.w x + 2 + x.length :=
      M.length_encS_conf hc ht
    rw [Bool.eq_iff_iff]
    have : qtbl M q x a c t = q [encS (ones (M.w x)) c t x,
        adv (encS (ones (M.w x)) c t x).length] := by
      rw [qtbl, claim, ha, hz]
    rw [this, ← hcorr, M.confLang_encS hc ht]
  rw [searchB_apply, Bool.and_eq_true_iff]
  refine ⟨(consistentB_iff a x).2 (consistent_of_table_eq hclaim), ?_⟩
  have hlen : (M.initF [x]).length = M.w x := M.initF_length x
  have := hclaim (M.initF [x]) (ones (M.w x + 1)) hlen (by simp)
  rw [qtbl] at this
  rw [this, val_ones]
  exact hx

end ASpace

/-! ### The collapse -/

/-- **If the configuration questions of an alternating machine are decided in polynomial space
with polynomial advice, its language is decided in polynomial space with no advice.** -/
theorem inPSpace_of_confLang (M : ASpace) (h : InPSpacePoly M.confLang) : InPSpace M.L := by
  obtain ⟨q, adv, r, hq, hadv, hcorr⟩ := h
  -- a polynomial bound on the width of a configuration
  obtain ⟨pw, hpw⟩ := M.cobham_widthF.poly_length
  have hw : ∀ x : List Bool, M.w x ≤ pw.eval x.length := by
    intro x
    simpa [ASpace.w, argSize_cons] using hpw [x]
  -- a Cobham padding long enough to hold the advice twice
  set ρ₀ : Polynomial ℕ := 3 * pw + Polynomial.C 2 + Polynomial.X with hρ₀
  obtain ⟨padF, hpad, hpadlen⟩ :=
    exists_cobham_len_ge (2 * r.comp ρ₀ + 1)
  refine ⟨ASpace.answerB M q (compFn padF [proj 0]), ASpace.psAnswerB hq hpad, fun x => ?_⟩
  have hcomp : (compFn padF [proj 0] : Fn) [x] = padF [x] := by
    simp [compFn, proj]
  rw [ASpace.answerB_apply, hcomp, anyLen_eq_true]
  -- the abbreviations
  set N : ℕ := 3 * M.w x + 2 + x.length with hN
  set l : ℕ := (adv N).length with hl
  set K : ℕ := (padF [x]).length with hK
  have hNle : N ≤ ρ₀.eval x.length := by
    have := hw x
    simp only [hρ₀, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hbig : 2 * l + 1 ≤ K := by
    have h1 : l ≤ r.eval N := hadv N
    have h2 : r.eval N ≤ r.eval (ρ₀.eval x.length) := Polynomial.eval_mono_nat r hNle
    have h3 : (2 * r.comp ρ₀ + 1).eval x.length ≤ K := hpadlen x
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_comp, Polynomial.eval_ofNat] at h3
    omega
  constructor
  · -- completeness
    intro hx
    refine ⟨encS (ones l) (adv N) (zeros (K - (2 * l + 1))) [], ?_, ?_⟩
    · rw [length_encS]
      simp only [length_ones, length_zeros, List.length_nil, ← hl]
      omega
    · refine ASpace.searchB_of_L hcorr ?_ hx
      rw [decC_encS (m := l) rfl]
  · -- soundness
    rintro ⟨a, -, hsearch⟩
    exact ASpace.L_of_searchB hsearch

end PSpace

end HTN
