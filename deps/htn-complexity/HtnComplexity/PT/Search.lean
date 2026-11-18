import HtnComplexity.PT.NExp
import ComplexityTheory.Savitch.Uniform
import ComplexityTheory.Machine.ExpSpace
/-!
# Languages of codes decided by a nondeterministic search

* **`HTN.Syn.PolyDom.inPSpace_codeLang_of_search`** — if `Q a` holds iff, from some configuration
  `c₀` with `init (a, c₀)`, polynomial-time steps `step (a, c, c')` through configurations whose
  codes are at most `q(|code of a|)` long reach a configuration `c` with `acc (a, c)`, then the
  language of the codes of the values satisfying `Q` is in `PSPACE`.  The machine
  (`HTN.Space.NSpace`) guesses the configurations; Savitch's theorem
  (`HTN.Savitch.inPSpace_of_inNSpace`) makes it deterministic.
* **`HTN.Syn.PolyDom.inExpSpace_codeLang_of_search`** — the same with configurations shorter than
  `2 ^ q(|code of a|)`: the language is in `EXPSPACE` (`HTN.Mach.inExpSpace_of_search`).
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

/-- A three-argument predicate of the calculus on raw strings is a predicate of Cobham's class. -/
theorem cobhamB_of_pt₃ {h : List Bool × List Bool × List Bool → Bool} (hh : PT h) :
    CobhamB fun args => h (args.getD 0 [], args.getD 1 [], args.getD 2 []) := by
  obtain ⟨H, hH, hHh⟩ := hh
  have hl : ∀ i, Cobham fun args : Args => lift (args.getD i []) := fun i =>
    (cobham_c1 uc_lift (Cobham.proj i)).of_fun_eq fun args => by simp [proj, compFn]
  have h12 : Cobham fun args : Args => lift (args.getD 1 []) ++ lift (args.getD 2 []) :=
    (cobham_c2 cobham_append (hl 1) (hl 2)).of_fun_eq fun args => by simp [compFn]
  have hcat : Cobham fun args : Args =>
      lift (args.getD 0 []) ++ (lift (args.getD 1 []) ++ lift (args.getD 2 [])) :=
    (cobham_c2 cobham_append (hl 0) h12).of_fun_eq fun args => by simp [compFn]
  refine (cobham_c1 hH hcat).of_fun_eq fun args => ?_
  show H (lift (args.getD 0 []) ++ (lift (args.getD 1 []) ++ lift (args.getD 2 []))) = _
  exact hHh (args.getD 0 [], args.getD 1 [], args.getD 2 [])

theorem decR_enc' {γ : Type} [BEnc γ] [BDec γ] (c : γ) : (decR (enc c) : γ × List Bool).1 = c := by
  rw [show enc c = enc c ++ [] by simp, BDec.decR_enc]

section Search

variable {α σ : Type} [BEnc α] [BDec α] [BEnc σ] [BDec σ]

/-- **Nondeterministic polynomial-space search decides a language of codes in `PSPACE`.** -/
theorem inPSpace_codeLang_of_search {Q : α → Prop} {init : α × σ → Bool}
    {step : α × σ × σ → Bool} {acc : α × σ → Bool} (hi : PT init) (hs : PT step) (ha : PT acc)
    (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀ c, sz c₀ ≤ q.eval (sz a) ∧ init (a, c₀) = true ∧
      Relation.ReflTransGen (fun c c' => sz c' ≤ q.eval (sz a) ∧ step (a, c, c') = true) c₀ c ∧
      acc (a, c) = true) :
    Cx.PSPACE (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  let dA : List Bool → α := fun x => (decR x : α × List Bool).1
  let dS : List Bool → σ := fun x => (decR x : σ × List Bool).1
  have hdA : PT dA := PT.fst.comp BDec.pt_decR
  have hdS : PT dS := PT.fst.comp BDec.pt_decR
  let hI : List Bool × List Bool → Bool := fun r =>
    isCode σ r.1 && isCode α r.2 && decide (r.1.length ≤ (g r.2).length) && init (dA r.2, dS r.1)
  have hhI : PT hI := PT.and (PT.and (PT.and ((pt_isCode σ).comp PT.fst)
    ((pt_isCode α).comp PT.snd)) (PT.le (PT.length PT.fst) (PT.length (hg.comp PT.snd))))
    (hi.comp (PT.pair (hdA.comp PT.snd) (hdS.comp PT.fst)))
  let hS : List Bool × List Bool × List Bool → Bool := fun r =>
    isCode σ r.1 && isCode σ r.2.1 && isCode α r.2.2 && decide (r.1.length ≤ (g r.2.2).length) &&
      step (dA r.2.2, dS r.2.1, dS r.1)
  have hhS : PT hS := PT.and (PT.and (PT.and (PT.and ((pt_isCode σ).comp PT.fst)
    ((pt_isCode σ).comp (PT.fst.comp PT.snd))) ((pt_isCode α).comp (PT.snd.comp PT.snd)))
    (PT.le (PT.length PT.fst) (PT.length (hg.comp (PT.snd.comp PT.snd)))))
    (hs.comp (PT.pair (hdA.comp (PT.snd.comp PT.snd))
      (PT.pair (hdS.comp (PT.fst.comp PT.snd)) (hdS.comp PT.fst))))
  let hA : List Bool × List Bool → Bool := fun r =>
    isCode σ r.1 && isCode α r.2 && acc (dA r.2, dS r.1)
  have hhA : PT hA := PT.and (PT.and ((pt_isCode σ).comp PT.fst) ((pt_isCode α).comp PT.snd))
    (ha.comp (PT.pair (hdA.comp PT.snd) (hdS.comp PT.fst)))
  have hlen : ∀ (c x a : List Bool), c.length ≤ (g x).length →
      c.length ≤ q.eval (x.length + a.length) := fun c x a h => by
    rw [hglen] at h
    exact h.trans (Polynomial.eval_mono_nat _ (by omega))
  let M : Space.NSpace :=
    { initB := fun args => hI (args.getD 0 [], args.getD 1 [])
      stepB := fun args => hS (args.getD 0 [], args.getD 1 [], args.getD 2 [])
      accB := fun args => hA (args.getD 0 [], args.getD 1 [])
      cobham_initB := cobhamB_of_pt₂ hhI
      cobham_stepB := cobhamB_of_pt₃ hhS
      cobham_accB := cobhamB_of_pt₂ hhA
      bound := q
      initB_length := fun c x a h => by
        simp only [List.getD_cons_zero, List.getD_cons_succ, hI, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact hlen c x a h.1.2
      stepB_length := fun c' c x a h => by
        simp only [List.getD_cons_zero, List.getD_cons_succ, hS, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact hlen c' x a h.1.2 }
  refine Savitch.inPSpace_of_inNSpace ⟨M, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨a, rfl, hQa⟩
    obtain ⟨c₀, c, h₀, hi₀, hr, hac⟩ := (hQ a).1 hQa
    refine ⟨enc c₀, enc c, ?_, ?_, ?_⟩
    · simp only [M, List.getD_cons_zero, List.getD_cons_succ, hI, Bool.and_eq_true,
        decide_eq_true_eq, (isCode_iff _).2 ⟨c₀, rfl⟩, (isCode_iff _).2 ⟨a, rfl⟩, dA, dS, decR_enc',
        hglen, hi₀, and_true, true_and]
      exact h₀
    · refine Relation.ReflTransGen.lift enc (fun c c' hcc => ?_) hr
      show hS (enc c', enc c, enc a) = true
      simp only [hS, Bool.and_eq_true, decide_eq_true_eq, (isCode_iff _).2 ⟨c, rfl⟩,
        (isCode_iff _).2 ⟨c', rfl⟩, (isCode_iff _).2 ⟨a, rfl⟩, dA, dS, decR_enc', hglen, hcc.2,
        and_true, true_and]
      exact hcc.1
    · simp only [M, List.getD_cons_zero, List.getD_cons_succ, hA, Bool.and_eq_true,
        (isCode_iff _).2 ⟨c, rfl⟩, (isCode_iff _).2 ⟨a, rfl⟩, dA, dS, decR_enc', hac, and_self]
  · rintro ⟨c₀, c, hi₀, hr, hac⟩
    simp only [M, List.getD_cons_zero, List.getD_cons_succ, hI, Bool.and_eq_true,
      decide_eq_true_eq] at hi₀
    obtain ⟨⟨⟨hc₀, hx⟩, hl₀⟩, hin⟩ := hi₀
    obtain ⟨a, rfl⟩ := (isCode_iff _).1 hx
    obtain ⟨s₀, rfl⟩ := (isCode_iff _).1 hc₀
    simp only [dA, dS, decR_enc'] at hin
    have key : ∀ c, Relation.ReflTransGen (M.Step (enc a) []) (enc s₀) c → ∃ s, c = enc s ∧
        Relation.ReflTransGen (fun c c' => sz c' ≤ q.eval (sz a) ∧ step (a, c, c') = true) s₀ s := by
      intro c hc
      induction hc with
      | refl => exact ⟨s₀, rfl, .refl⟩
      | @tail b c' _ hbc ih =>
        obtain ⟨s, rfl, hrs⟩ := ih
        have hbc' : hS (c', enc s, enc a) = true := hbc
        simp only [hS, Bool.and_eq_true, decide_eq_true_eq] at hbc'
        obtain ⟨⟨⟨⟨hc', -⟩, -⟩, hl'⟩, hst⟩ := hbc'
        obtain ⟨s', rfl⟩ := (isCode_iff _).1 hc'
        simp only [dA, dS, decR_enc'] at hst
        rw [hglen] at hl'
        exact ⟨s', rfl, hrs.tail ⟨hl', hst⟩⟩
    obtain ⟨s, rfl, hrs⟩ := key c hr
    refine ⟨a, rfl, (hQ a).2 ⟨s₀, s, by rw [hglen] at hl₀; exact hl₀, hin, hrs, ?_⟩⟩
    simp only [M, List.getD_cons_zero, List.getD_cons_succ, hA, Bool.and_eq_true, dA, dS,
      decR_enc'] at hac
    exact hac.2

/-- **Nondeterministic exponential-space search decides a language of codes in `EXPSPACE`.** -/
theorem inExpSpace_codeLang_of_search {Q : α → Prop} {init : α × σ → Bool}
    {step : α × σ × σ → Bool} {acc : α × σ → Bool} (hi : PT init) (hs : PT step) (ha : PT acc)
    (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀ c, sz c₀ < 2 ^ q.eval (sz a) ∧ init (a, c₀) = true ∧
      Relation.ReflTransGen (fun c c' => sz c' < 2 ^ q.eval (sz a) ∧ step (a, c, c') = true) c₀ c ∧
      acc (a, c) = true) :
    Cx.EXPSPACE (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  let dA : List Bool → α := fun x => (decR x : α × List Bool).1
  let dS : List Bool → σ := fun x => (decR x : σ × List Bool).1
  have hdA : PT dA := PT.fst.comp BDec.pt_decR
  have hdS : PT dS := PT.fst.comp BDec.pt_decR
  -- a configuration `s` is written `true :: enc s`; `[]` is the start
  let hSt : List Bool × List Bool × List Bool → Bool := fun r =>
    r.2.2.headI && isCode σ r.2.2.tail && isCode α r.1 &&
      decide ((bitsOfNat r.2.2.tail.length).length ≤ (g r.1).length) &&
      bif r.2.1.isEmpty then init (dA r.1, dS r.2.2.tail)
        else r.2.1.headI && isCode σ r.2.1.tail && step (dA r.1, dS r.2.1.tail, dS r.2.2.tail)
  have hhSt : PT hSt := by
    have hc' : PT fun r : List Bool × List Bool × List Bool => r.2.2 := PT.snd.comp PT.snd
    have hc : PT fun r : List Bool × List Bool × List Bool => r.2.1 := PT.fst.comp PT.snd
    exact PT.and (PT.and (PT.and (PT.and (PT.headI hc') ((pt_isCode σ).comp (PT.tail hc')))
      ((pt_isCode α).comp PT.fst)) (PT.le (PT.length (PT.bits.comp (PT.length (PT.tail hc'))))
        (PT.length (hg.comp PT.fst))))
      (PT.cond (PT.isEmpty hc) (hi.comp (PT.pair (hdA.comp PT.fst) (hdS.comp (PT.tail hc'))))
        (PT.and (PT.and (PT.headI hc) ((pt_isCode σ).comp (PT.tail hc)))
          (hs.comp (PT.pair (hdA.comp PT.fst) (PT.pair (hdS.comp (PT.tail hc))
            (hdS.comp (PT.tail hc')))))))
  let hAc : List Bool × List Bool → Bool := fun r =>
    r.2.headI && isCode σ r.2.tail && isCode α r.1 && acc (dA r.1, dS r.2.tail)
  have hhAc : PT hAc := PT.and (PT.and (PT.and (PT.headI PT.snd) ((pt_isCode σ).comp
    (PT.tail PT.snd))) ((pt_isCode α).comp PT.fst))
    (ha.comp (PT.pair (hdA.comp PT.fst) (hdS.comp (PT.tail PT.snd))))
  have hcons : ∀ l : List Bool, l.headI = true → l = true :: l.tail := by
    intro l h; cases l with
    | nil => simp at h
    | cons b l => simp at h; simp [h]
  refine Mach.inExpSpace_of_search (fun args => hSt (args.getD 0 [], args.getD 1 [], args.getD 2 []))
    (fun args => hAc (args.getD 0 [], args.getD 1 [])) (cobhamB_of_pt₃ hhSt) (cobhamB_of_pt₂ hhAc)
    q (fun x c c' h => ?_) (fun x => ⟨?_, ?_⟩)
  · simp only [List.getD_cons_zero, List.getD_cons_succ, hSt, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, -⟩, -⟩, h4⟩, -⟩ := h
    rw [hglen, length_bitsOfNat_le_iff] at h4
    rw [hcons c' h1, List.length_cons]
    omega
  · rintro ⟨a, rfl, hQa⟩
    obtain ⟨c₀, c, h₀, hi₀, hr, hac⟩ := (hQ a).1 hQa
    refine ⟨true :: enc c, ?_, ?_⟩
    · refine Relation.ReflTransGen.head (b := true :: enc c₀) ?_
        (Relation.ReflTransGen.lift (fun s => true :: enc s) (fun s s' hss => ?_) hr)
      · show hSt (enc a, [], true :: enc c₀) = true
        simp only [hSt, List.headI_cons, List.tail_cons, (isCode_iff _).2 ⟨c₀, rfl⟩,
          (isCode_iff _).2 ⟨a, rfl⟩, Bool.true_and, hglen, length_bitsOfNat_le_iff, List.isEmpty_nil,
          cond_true, dA, dS, decR_enc', hi₀, Bool.and_true, decide_eq_true_eq]
        exact h₀
      · show hSt (enc a, true :: enc s, true :: enc s') = true
        simp only [hSt, List.headI_cons, List.tail_cons, (isCode_iff _).2 ⟨s, rfl⟩,
          (isCode_iff _).2 ⟨s', rfl⟩, (isCode_iff _).2 ⟨a, rfl⟩, Bool.true_and, hglen,
          length_bitsOfNat_le_iff, List.isEmpty_cons, cond_false, dA, dS, decR_enc', hss.2,
          Bool.and_true, decide_eq_true_eq]
        exact hss.1
    · show hAc (enc a, true :: enc c) = true
      simp only [hAc, List.headI_cons, List.tail_cons, (isCode_iff _).2 ⟨c, rfl⟩,
        (isCode_iff _).2 ⟨a, rfl⟩, dA, dS, decR_enc', hac, Bool.and_self]
  · rintro ⟨c, hr, hac⟩
    have hac' : hAc (x, c) = true := hac
    simp only [hAc, Bool.and_eq_true] at hac'
    obtain ⟨⟨⟨hh, hcode⟩, hx⟩, hacc⟩ := hac'
    obtain ⟨a, rfl⟩ := (isCode_iff _).1 hx
    -- the configurations reachable from the start
    have key : ∀ c, Relation.ReflTransGen (fun c c' =>
        hSt (enc a, c, c') = true) [] c → c = [] ∨ ∃ c₀ s, sz c₀ < 2 ^ q.eval (sz a) ∧
          init (a, c₀) = true ∧ Relation.ReflTransGen (fun c c' => sz c' < 2 ^ q.eval (sz a) ∧
            step (a, c, c') = true) c₀ s ∧ c = true :: enc s := by
      intro c hc
      induction hc with
      | refl => exact Or.inl rfl
      | @tail b c' _ hbc ih =>
        simp only [hSt, Bool.and_eq_true, decide_eq_true_eq] at hbc
        obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩ := hbc
        obtain ⟨s', hs'⟩ := (isCode_iff _).1 h2
        rw [hglen, length_bitsOfNat_le_iff] at h4
        have hc'eq : c' = true :: enc s' := by rw [hcons c' h1, hs']
        rw [← hs'] at h4
        right
        rcases ih with rfl | ⟨c₀, s, h0, hi0, hrs, rfl⟩
        · simp only [List.isEmpty_nil, cond_true, dA, dS, ← hs', decR_enc'] at h5
          exact ⟨s', s', h4, h5, .refl, hc'eq⟩
        · simp only [List.isEmpty_cons, cond_false, List.headI_cons, List.tail_cons, Bool.true_and,
            Bool.and_eq_true, dA, dS, ← hs', decR_enc'] at h5
          exact ⟨c₀, s', h0, hi0, hrs.tail ⟨h4, h5.2⟩, hc'eq⟩
    rcases key c hr with rfl | ⟨c₀, s, h0, hi0, hrs, rfl⟩
    · simp at hh
    · simp only [List.tail_cons, dA, dS, decR_enc'] at hacc
      exact ⟨a, rfl, (hQ a).2 ⟨c₀, s, h0, hi0, hrs, hacc⟩⟩

end Search

end PolyDom

end Syn

end HTN
