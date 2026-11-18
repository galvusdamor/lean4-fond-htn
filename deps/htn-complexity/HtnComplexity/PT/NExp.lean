import HtnComplexity.PT.NP
import ComplexityTheory.Machine.NExp
/-!
# Languages of codes in NEXPTIME

* **`HTN.Syn.PolyDom.inNExp_codeLang`** — if `Q a` holds iff some value `b` whose code is shorter
  than `2 ^ p(|code of a|)` makes a polynomial-time Boolean function `r (a, b)` true, then the
  language of the codes of the values satisfying `Q` is in `NEXPTIME`.

The verifier checks that both strings are codes, that the certificate is short enough (by
comparing the number of binary digits of its length with `p(|x|)`), decodes them and runs `r`;
it is a predicate of Cobham's class (`HTN.Syn.PolyDom.cobhamB_of_pt₂`), and
`HTN.Mach.inNExp_of_verifier` turns it into a nondeterministic Turing machine.

Also: `HTN.Syn.PolyDom.exists_pt_polyLen` — a polynomial-time list of length `q(|x|)`.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

/-- For every polynomial `q` there is a polynomial-time list of length `q(|x|)`. -/
theorem exists_pt_polyLen (q : Polynomial ℕ) :
    ∃ g : List Bool → List Unit, PT g ∧ ∀ x, (g x).length = q.eval x.length := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨g₁, h₁, e₁⟩ := hp
    obtain ⟨g₂, h₂, e₂⟩ := hr
    exact ⟨fun x => g₁ x ++ g₂ x, PT.append h₁ h₂, fun x => by simp [e₁, e₂]⟩
  | monomial n a =>
    induction n with
    | zero =>
      exact ⟨fun _ => List.replicate a (), PT.const _, fun x => by simp⟩
    | succ n ih =>
      obtain ⟨g, hg, eg⟩ := ih
      refine ⟨fun x => (g x).flatMap fun _ => x.map fun _ => (), PT.flatMap hg
        (PT.map PT.fst (PT.const ())), fun x => ?_⟩
      simp only [List.length_flatMap, List.length_map, List.map_const', List.sum_replicate,
        smul_eq_mul, eg, Polynomial.eval_monomial, List.length_replicate]
      ring

/-- The number of binary digits of `n` is at most `k` iff `n < 2 ^ k`. -/
theorem length_bitsOfNat_le_iff : ∀ (k n : ℕ), (bitsOfNat n).length ≤ k ↔ n < 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro n
    rcases n with _ | n
    · simp [bitsOfNat]
    · rw [bitsOfNat]; simp
  | succ k ih =>
    intro n
    rcases n with _ | n
    · simp [bitsOfNat]
    · rw [bitsOfNat, List.length_cons, pow_succ]
      have := ih ((n + 1) / 2)
      constructor
      · intro h; have := this.1 (by omega); omega
      · intro h; have := this.2 (by omega); omega

/-- A two-argument predicate of the calculus on raw strings is a predicate of Cobham's class. -/
theorem cobhamB_of_pt₂ {h : List Bool × List Bool → Bool} (hh : PT h) :
    CobhamB fun args => h (args.getD 0 [], args.getD 1 []) := by
  obtain ⟨H, hH, hHh⟩ := hh
  have hl : ∀ i, Cobham fun args : Args => lift (args.getD i []) := fun i =>
    (cobham_c1 uc_lift (Cobham.proj i)).of_fun_eq fun args => by simp [proj, compFn]
  have hcat : Cobham fun args : Args => lift (args.getD 0 []) ++ lift (args.getD 1 []) :=
    (cobham_c2 cobham_append (hl 0) (hl 1)).of_fun_eq fun args => by simp [compFn]
  refine (cobham_c1 hH hcat).of_fun_eq fun args => ?_
  show H (lift (args.getD 0 []) ++ lift (args.getD 1 [])) = _
  exact hHh (args.getD 0 [], args.getD 1 [])

/-- **A language of codes with polynomial-time checkable, exponentially bounded certificates is
in `NEXPTIME`.** -/
theorem inNExp_codeLang {α β : Type} [BEnc α] [BDec α] [BEnc β] [BDec β] {Q : α → Prop}
    {r : α × β → Bool} (hr : PT r) (p : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ b : β, (enc b).length < 2 ^ p.eval (enc a).length ∧ r (a, b) = true) :
    Cx.NEXPTIME (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen p
  let h : List Bool × List Bool → Bool := fun q =>
    isCode α q.1 && isCode β q.2 && decide ((bitsOfNat q.2.length).length ≤ (g q.1).length) &&
      r ((decR q.1 : α × List Bool).1, (decR q.2 : β × List Bool).1)
  have hh : PT h := PT.and (PT.and (PT.and ((pt_isCode α).comp PT.fst) ((pt_isCode β).comp PT.snd))
    (PT.le (PT.length (PT.bits.comp (PT.length PT.snd))) (PT.length (hg.comp PT.fst))))
    (hr.comp (PT.pair (PT.fst.comp (BDec.pt_decR.comp PT.fst))
      (PT.fst.comp (BDec.pt_decR.comp PT.snd))))
  have hdec : ∀ {γ : Type} [BEnc γ] [BDec γ] (c : γ), (decR (enc c) : γ × List Bool).1 = c := by
    intro γ _ _ c
    rw [show enc c = enc c ++ [] by simp, BDec.decR_enc]
  refine Mach.inNExp_of_verifier (fun args => h (args.getD 0 [], args.getD 1 [])) (cobhamB_of_pt₂ hh)
    p (fun x w hv => ?_) (fun x => ⟨?_, ?_⟩)
  · simp only [List.getD_cons_zero, List.getD_cons_succ, h, Bool.and_eq_true, decide_eq_true_eq]
      at hv
    rw [hglen] at hv
    exact ((length_bitsOfNat_le_iff _ _).1 hv.1.2).le
  · rintro ⟨a, rfl, ha⟩
    obtain ⟨b, hb, hrb⟩ := (hQ a).1 ha
    refine ⟨enc b, ?_⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, h, Bool.and_eq_true, decide_eq_true_eq,
      (isCode_iff _).2 ⟨a, rfl⟩, (isCode_iff _).2 ⟨b, rfl⟩, hdec, hrb, hglen,
      length_bitsOfNat_le_iff, hb, and_self]
  · rintro ⟨w, hv⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ, h, Bool.and_eq_true, decide_eq_true_eq]
      at hv
    obtain ⟨⟨⟨hx, hw'⟩, hlen⟩, hrr⟩ := hv
    obtain ⟨a, rfl⟩ := (isCode_iff _).1 hx
    obtain ⟨b, rfl⟩ := (isCode_iff _).1 hw'
    rw [hdec, hdec] at hrr
    rw [hglen, length_bitsOfNat_le_iff] at hlen
    exact ⟨a, rfl, (hQ a).2 ⟨b, hlen, hrr⟩⟩

end PolyDom

end Syn

end HTN
