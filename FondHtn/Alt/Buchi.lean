import FondHtn.Alt.ExpTime
import FondHtn.Cx.Exp2
/-!
# Fair (Büchi-style) AND-OR games over bounded configurations

The game of `FondHtn/Alt/ExpTime.lean` decides the *least* fixpoint (reachability).  Fair strong
cyclic planning needs the nested fixpoint `νX. μZ. Attr(X, Z)` (Cimatti et al.): a configuration
is *winning* if it lies in a set `X` every element of which is in the attractor `BAttr X` of the
accepting configurations, where

* accepting configurations are in the attractor;
* an existential configuration (`uni = false`) is in the attractor if some successor is in `X`
  and in the attractor;
* a universal configuration is in the attractor if all its successors are in `X` and some
  successor is in the attractor.

All configurations have codes of length at most `B` (`HTN.Syn.PolyDom.BAttr`,
`HTN.Syn.PolyDom.BWin`).

* **`HTN.Syn.PolyDom.inExpTime_codeLang_of_buchi`** — configurations of polynomial size: the
  language is in `EXPTIME`;
* **`HTN.Syn.PolyDom.inExp2Time_codeLang_of_buchi`** — configurations of exponential size: the
  language is in `2-EXPTIME`.

Proof: the candidates (all configurations of size at most `B`) are enumerated as in
`inExpTime_codeLang_of_andOr`; the inner least fixpoint is computed by iterating
`HTN.Syn.PolyDom.attrStep` from `[]` (increasing), the outer greatest fixpoint by iterating the
inner fixpoint from the list of all candidates (decreasing); both stabilise after at most
`|All| + 1` rounds (`HTN.Syn.PolyDom.iter_up_fix`, `HTN.Syn.PolyDom.iter_down_fix`).
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

section Buchi

set_option linter.unusedSectionVars false

variable {α σ : Type} [BEnc α] [BDec α] [BEnc σ] [BDec σ] [DecidableEq σ]

/-- **The attractor** of the accepting configurations with respect to `X`. -/
inductive BAttr (B : ℕ) (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (a : α)
    (X : σ → Prop) : σ → Prop
  | acc {c : σ} : sz c ≤ B → acc (a, c) = true → BAttr B acc uni step a X c
  | ex {c c' : σ} : sz c ≤ B → uni (a, c) = false → sz c' ≤ B → step (a, c, c') = true → X c' →
      BAttr B acc uni step a X c' → BAttr B acc uni step a X c
  | univ {c c' : σ} : sz c ≤ B → uni (a, c) = true →
      (∀ c'', sz c'' ≤ B → step (a, c, c'') = true → X c'') → sz c' ≤ B →
      step (a, c, c') = true → BAttr B acc uni step a X c' → BAttr B acc uni step a X c

/-- **Winning configurations**: in a set `X` contained in its attractor. -/
def BWin (B : ℕ) (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (a : α) (c : σ) : Prop :=
  ∃ X : σ → Prop, X c ∧ ∀ c', X c' → BAttr B acc uni step a X c'

variable {B : ℕ} {acc uni : α × σ → Bool} {step : α × σ × σ → Bool} {a : α}

theorem BAttr.sz_le {X : σ → Prop} {c : σ} (h : BAttr B acc uni step a X c) : sz c ≤ B := by
  cases h <;> assumption

theorem BAttr.monoX {X Y : σ → Prop} (hXY : ∀ c, X c → Y c) {c : σ}
    (h : BAttr B acc uni step a X c) : BAttr B acc uni step a Y c := by
  induction h with
  | acc hB ha => exact .acc hB ha
  | ex hB hu hB' hs hX _ ih => exact .ex hB hu hB' hs (hXY _ hX) ih
  | univ hB hu hall hB' hs _ ih =>
    exact .univ hB hu (fun c'' h1 h2 => hXY _ (hall c'' h1 h2)) hB' hs ih

/-! ### Generic stabilisation of monotone iterations -/

section Iter

variable {All : List σ} {G : List σ → List σ}

theorem iter_up_mono (hmono : ∀ W W', (∀ x ∈ W, x ∈ W') → ∀ x ∈ G W, x ∈ G W') (k : ℕ) :
    ∀ x ∈ G^[k] [], x ∈ G^[k + 1] [] := by
  induction k with
  | zero => intro x hx; simp at hx
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx ⊢
    exact hmono _ _ ih x hx

theorem iter_down_mono (hmono : ∀ W W', (∀ x ∈ W, x ∈ W') → ∀ x ∈ G W, x ∈ G W')
    (hsub : ∀ W, ∀ x ∈ G W, x ∈ All) (k : ℕ) :
    ∀ x ∈ G^[k + 1] All, x ∈ G^[k] All := by
  induction k with
  | zero => intro x hx; exact hsub _ x hx
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx ⊢
    exact hmono _ _ ih x hx

theorem iter_sub (hsub : ∀ W, ∀ x ∈ G W, x ∈ All) (W₀ : List σ) (hW₀ : ∀ x ∈ W₀, x ∈ All) :
    ∀ k, ∀ x ∈ G^[k] W₀, x ∈ All := by
  intro k
  cases k with
  | zero => exact hW₀
  | succ k => intro x hx; rw [Function.iterate_succ_apply'] at hx; exact hsub _ x hx

/-- Stabilisation from a fixed point of the finsets, using congruence. -/
theorem iter_stable (hcongr : ∀ W W', (∀ x, x ∈ W ↔ x ∈ W') → G W = G W') (W₀ : List σ) {k : ℕ}
    (heq : (G^[k] W₀).toFinset = (G^[k + 1] W₀).toFinset) :
    ∀ j, G^[k + 1 + j] W₀ = G^[k + 1] W₀ := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show k + 1 + (j + 1) = (k + 1 + j) + 1 by omega, Function.iterate_succ_apply', ih,
      Function.iterate_succ_apply']
    exact hcongr _ _ fun x => by
      have := Finset.ext_iff.1 heq x
      rw [List.mem_toFinset, List.mem_toFinset, Function.iterate_succ_apply'] at this
      exact this.symm

theorem iter_up_stab (hmono : ∀ W W', (∀ x ∈ W, x ∈ W') → ∀ x ∈ G W, x ∈ G W')
    (hsub : ∀ W, ∀ x ∈ G W, x ∈ All) :
    ∃ k ≤ All.length, (G^[k] []).toFinset = (G^[k + 1] []).toFinset := by
  classical
  by_contra hc
  push_neg at hc
  have hss : ∀ k, (G^[k] []).toFinset ⊆ (G^[k + 1] []).toFinset := fun k x hx => by
    rw [List.mem_toFinset] at hx ⊢; exact iter_up_mono hmono k x hx
  have hcard : ∀ k ≤ All.length + 1, k ≤ (G^[k] []).toFinset.card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hss k, hc k (by omega)⟩)
      have := ih (by omega)
      omega
  have h1 := hcard (All.length + 1) le_rfl
  have h2 : (G^[All.length + 1] []).toFinset ⊆ All.toFinset := fun x hx => by
    rw [List.mem_toFinset] at hx ⊢
    exact iter_sub hsub [] (by simp) _ x hx
  have h3 := Finset.card_le_card h2
  have h4 := List.toFinset_card_le All
  omega

theorem iter_down_stab (hmono : ∀ W W', (∀ x ∈ W, x ∈ W') → ∀ x ∈ G W, x ∈ G W')
    (hsub : ∀ W, ∀ x ∈ G W, x ∈ All) :
    ∃ k ≤ All.length, (G^[k] All).toFinset = (G^[k + 1] All).toFinset := by
  classical
  by_contra hc
  push_neg at hc
  have hss : ∀ k, (G^[k + 1] All).toFinset ⊆ (G^[k] All).toFinset := fun k x hx => by
    rw [List.mem_toFinset] at hx ⊢; exact iter_down_mono hmono hsub k x hx
  have hcard : ∀ k ≤ All.length + 1, (G^[k] All).toFinset.card + k ≤ All.length := by
    intro k
    induction k with
    | zero => intro _; simpa using List.toFinset_card_le All
    | succ k ih =>
      intro hk
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hss k, (hc k (by omega)).symm⟩)
      have := ih (by omega)
      omega
  have := hcard (All.length + 1) le_rfl
  omega

theorem iter_fix_of_stab (hcongr : ∀ W W', (∀ x, x ∈ W ↔ x ∈ W') → G W = G W') (W₀ : List σ)
    (hstab : ∃ k ≤ All.length, (G^[k] W₀).toFinset = (G^[k + 1] W₀).toFinset) {N : ℕ}
    (hN : All.length + 1 ≤ N) : G (G^[N] W₀) = G^[N] W₀ ∧
      ∀ N', All.length + 1 ≤ N' → G^[N'] W₀ = G^[N] W₀ := by
  obtain ⟨k, hk, heq⟩ := hstab
  have hs := iter_stable hcongr W₀ heq
  have hconst : ∀ M, k + 1 ≤ M → G^[M] W₀ = G^[k + 1] W₀ := fun M hM => by
    obtain ⟨j, rfl⟩ : ∃ j, M = k + 1 + j := ⟨M - (k + 1), by omega⟩
    exact hs j
  refine ⟨?_, fun N' hN' => by rw [hconst N' (by omega), hconst N (by omega)]⟩
  rw [← Function.iterate_succ_apply' G, hconst (N + 1) (by omega), hconst N (by omega)]

end Iter

/-! ### The inner least fixpoint -/

/-- One round of the attractor computation on `((a, All), W)`. -/
def attrStep (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (y : (α × List σ) × List σ)
    (Z : List σ) : List σ :=
  y.1.2.filter fun c => acc (y.1.1, c) ||
    (!uni (y.1.1, c) && y.1.2.any fun c' => step (y.1.1, c, c') && decide (c' ∈ y.2) &&
      decide (c' ∈ Z)) ||
    (uni (y.1.1, c) && (y.1.2.all fun c' => !step (y.1.1, c, c') || decide (c' ∈ y.2)) &&
      y.1.2.any fun c' => step (y.1.1, c, c') && decide (c' ∈ Z))

/-- The attractor of `W`: `|code| + 1` rounds from the empty list. -/
def attrFix (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (y : (α × List σ) × List σ) :
    List σ :=
  (attrStep acc uni step y)^[1 * (sz y + 1) ^ 1] []

/-- The winning region: `|code| + 1` rounds of `attrFix` from all candidates. -/
def winFix (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (y : α × List σ) : List σ :=
  (fun W => attrFix acc uni step (y, W))^[1 * (sz y + 1) ^ 1] y.2

section Correct

variable {All : List σ} (hAll : ∀ c, c ∈ All ↔ sz c ≤ B)
include hAll

theorem attrStep_sub (W Z : List σ) : ∀ x ∈ attrStep acc uni step ((a, All), W) Z, x ∈ All :=
  fun _ hx => (List.mem_filter.1 hx).1

theorem attrStep_mono (W : List σ) : ∀ Z Z', (∀ x ∈ Z, x ∈ Z') →
    ∀ x ∈ attrStep acc uni step ((a, All), W) Z, x ∈ attrStep acc uni step ((a, All), W) Z' := by
  intro Z Z' h x hx
  unfold attrStep at hx ⊢
  simp only [List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hx ⊢
  obtain ⟨hxA, hx⟩ := hx
  refine ⟨hxA, ?_⟩
  rcases hx with (hx | ⟨hu, c', hc', ⟨hs, hW⟩, hZ⟩) | ⟨⟨hu, hall⟩, c', hc', hs, hZ⟩
  · exact Or.inl (Or.inl hx)
  · exact Or.inl (Or.inr ⟨hu, c', hc', ⟨hs, hW⟩, h c' hZ⟩)
  · exact Or.inr ⟨⟨hu, hall⟩, c', hc', hs, h c' hZ⟩

theorem attrStep_congr (W : List σ) : ∀ Z Z', (∀ x, x ∈ Z ↔ x ∈ Z') →
    attrStep acc uni step ((a, All), W) Z = attrStep acc uni step ((a, All), W) Z' := by
  intro Z Z' h
  unfold attrStep
  refine List.filter_congr fun c _ => ?_
  simp only [h]

theorem attrStep_sound (W : List σ) : ∀ k, ∀ c ∈ (attrStep acc uni step ((a, All), W))^[k] [],
    BAttr B acc uni step a (· ∈ W) c := by
  intro k
  induction k with
  | zero => intro c hc; simp at hc
  | succ k ih =>
    intro c hc
    rw [Function.iterate_succ_apply'] at hc
    unfold attrStep at hc
    simp only [List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hcA, hc⟩ := hc
    have hcB := (hAll c).1 hcA
    rcases hc with (hc | ⟨hu, c', hc', ⟨hs, hW⟩, hZ⟩) | ⟨⟨hu, hall⟩, c', hc', hs, hZ⟩
    · exact .acc hcB hc
    · exact .ex hcB hu ((hAll c').1 hc') hs hW (ih c' hZ)
    · refine .univ hcB hu (fun c'' h1 h2 => ?_) ((hAll c').1 hc') hs (ih c' hZ)
      rcases hall c'' ((hAll c'').2 h1) with h | h
      · simp [h2] at h
      · exact h

theorem mem_attrFix_iff (W : List σ) (c : σ) :
    c ∈ attrFix acc uni step ((a, All), W) ↔ BAttr B acc uni step a (· ∈ W) c := by
  set F := attrStep acc uni step ((a, All), W)
  have hN : All.length + 1 ≤ 1 * (sz ((a, All), W) + 1) ^ 1 := by
    have := length_le_sz All
    rw [sz_prod, sz_prod, pow_one, one_mul]; omega
  have hfix := (iter_fix_of_stab (All := All) (G := F) (attrStep_congr hAll W) []
    (iter_up_stab (attrStep_mono hAll W) (attrStep_sub hAll W)) hN).1
  constructor
  · exact fun h => attrStep_sound hAll W _ c h
  · intro h
    show c ∈ F^[1 * (sz ((a, All), W) + 1) ^ 1] []
    set Z := F^[1 * (sz ((a, All), W) + 1) ^ 1] []
    induction h with
    | acc hB ha =>
      rw [← hfix]; unfold F attrStep
      simp [List.mem_filter, (hAll _).2 hB, ha]
    | @ex c₁ c' hB hu hB' hs hX _ ih =>
      rw [← hfix]; unfold F attrStep
      simp only [List.mem_filter, (hAll _).2 hB, Bool.or_eq_true, Bool.and_eq_true,
        List.any_eq_true, true_and, hu, Bool.not_false, decide_eq_true_eq]
      exact Or.inl (Or.inr ⟨c', (hAll _).2 hB', ⟨hs, hX⟩, ih⟩)
    | @univ c₁ c' hB hu hall hB' hs _ ih =>
      rw [← hfix]; unfold F attrStep
      simp only [List.mem_filter, (hAll _).2 hB, Bool.or_eq_true, Bool.and_eq_true,
        List.all_eq_true, List.any_eq_true, true_and, hu, decide_eq_true_eq]
      refine Or.inr ⟨fun c'' hc'' => ?_, c', (hAll _).2 hB', hs, ih⟩
      by_cases hs'' : step (a, c₁, c'') = true
      · simp [hall c'' ((hAll _).1 hc'') hs'']
      · simp [hs'']

/-! ### The outer greatest fixpoint -/

theorem mem_winFix_iff (c : σ) :
    c ∈ winFix acc uni step (a, All) ↔ BWin B acc uni step a c := by
  set G : List σ → List σ := fun W => attrFix acc uni step ((a, All), W)
  have hG : ∀ W x, x ∈ G W ↔ BAttr B acc uni step a (· ∈ W) x := fun W x =>
    mem_attrFix_iff hAll W x
  have hsub : ∀ W, ∀ x ∈ G W, x ∈ All := fun W x hx => (hAll x).2 ((hG W x).1 hx).sz_le
  have hmono : ∀ W W', (∀ x ∈ W, x ∈ W') → ∀ x ∈ G W, x ∈ G W' := fun W W' h x hx =>
    (hG W' x).2 (((hG W x).1 hx).monoX fun c hc => h c hc)
  -- `G` only depends on membership: two iterates of the attractor computation past
  -- stabilisation agree
  have hcongr : ∀ W W', (∀ x, x ∈ W ↔ x ∈ W') → G W = G W' := by
    intro W W' h
    have hstep : attrStep acc uni step ((a, All), W) = attrStep acc uni step ((a, All), W') := by
      funext Z
      unfold attrStep
      refine List.filter_congr fun c _ => ?_
      simp only [h]
    have hN : ∀ W₁ : List σ, All.length + 1 ≤ 1 * (sz ((a, All), W₁) + 1) ^ 1 := fun W₁ => by
      have := length_le_sz All
      rw [sz_prod, sz_prod, pow_one, one_mul]; omega
    have hfix := (iter_fix_of_stab (All := All) (G := attrStep acc uni step ((a, All), W'))
      (attrStep_congr hAll W') [] (iter_up_stab (attrStep_mono hAll W') (attrStep_sub hAll W'))
      (hN W')).2
    show (attrStep acc uni step ((a, All), W))^[_] [] =
      (attrStep acc uni step ((a, All), W'))^[_] []
    rw [hstep]
    exact hfix _ (hN W)
  have hN : All.length + 1 ≤ 1 * (sz (a, All) + 1) ^ 1 := by
    have := length_le_sz All
    rw [sz_prod, pow_one, one_mul]; omega
  have hfix := (iter_fix_of_stab (All := All) (G := G) hcongr All
    (iter_down_stab hmono hsub) hN).1
  show c ∈ G^[1 * (sz (a, All) + 1) ^ 1] All ↔ _
  set W := G^[1 * (sz (a, All) + 1) ^ 1] All
  constructor
  · intro hc
    refine ⟨(· ∈ W), hc, fun c' hc' => ?_⟩
    rw [← hfix] at hc'
    exact (hG W c').1 hc'
  · rintro ⟨X, hXc, hX⟩
    have : ∀ k, ∀ c', X c' → c' ∈ G^[k] All := by
      intro k
      induction k with
      | zero => intro c' hc'; exact (hAll c').2 (hX c' hc').sz_le
      | succ k ih =>
        intro c' hc'
        rw [Function.iterate_succ_apply']
        exact (hG _ c').2 ((hX c' hc').monoX fun d hd => ih d hd)
    exact this _ c hXc

end Correct

/-! ### Polynomial time -/

theorem pt_attrStep (ha : PT acc) (hu : PT uni) (hs : PT step) :
    PT₂ fun (y : (α × List σ) × List σ) (Z : List σ) => attrStep acc uni step y Z := by
  unfold PT₂ attrStep
  -- context `z : (((α × List σ) × List σ) × List σ) × σ`
  have zA : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.1.1.1 :=
    PT.fst.comp (PT.fst.comp (PT.fst.comp PT.fst))
  have zAll : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.1.1.2 :=
    PT.snd.comp (PT.fst.comp (PT.fst.comp PT.fst))
  have zW : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.1.2 :=
    PT.snd.comp (PT.fst.comp PT.fst)
  have zZ : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.2 := PT.snd.comp PT.fst
  have zc : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.2 := PT.snd
  -- context `w : ((((α × List σ) × List σ) × List σ) × σ) × σ`
  have wst : PT fun w : ((((α × List σ) × List σ) × List σ) × σ) × σ =>
      step (w.1.1.1.1.1, w.1.2, w.2) :=
    hs.comp (PT.pair (zA.comp PT.fst) (PT.pair (zc.comp PT.fst) PT.snd))
  have wW : PT fun w : ((((α × List σ) × List σ) × List σ) × σ) × σ => decide (w.2 ∈ w.1.1.1.2) :=
    PT.elem (zW.comp PT.fst) PT.snd
  have wZ : PT fun w : ((((α × List σ) × List σ) × List σ) × σ) × σ => decide (w.2 ∈ w.1.1.2) :=
    PT.elem (zZ.comp PT.fst) PT.snd
  have hex : PT fun z : (((α × List σ) × List σ) × List σ) × σ =>
      z.1.1.1.2.any fun c' => step (z.1.1.1.1, z.2, c') && decide (c' ∈ z.1.1.2) &&
        decide (c' ∈ z.1.2) :=
    PT.any zAll (PT.and (PT.and wst wW) wZ)
  have hall : PT fun z : (((α × List σ) × List σ) × List σ) × σ =>
      z.1.1.1.2.all fun c' => !step (z.1.1.1.1, z.2, c') || decide (c' ∈ z.1.1.2) :=
    PT.all zAll (PT.or (PT.not wst) wW)
  have hany : PT fun z : (((α × List σ) × List σ) × List σ) × σ =>
      z.1.1.1.2.any fun c' => step (z.1.1.1.1, z.2, c') && decide (c' ∈ z.1.2) :=
    PT.any zAll (PT.and wst wZ)
  have hacc : PT fun z : (((α × List σ) × List σ) × List σ) × σ => acc (z.1.1.1.1, z.2) :=
    ha.comp (PT.pair zA zc)
  have huni : PT fun z : (((α × List σ) × List σ) × List σ) × σ => uni (z.1.1.1.1, z.2) :=
    hu.comp (PT.pair zA zc)
  exact PT.filter (PT.snd.comp (PT.fst.comp PT.fst))
    (PT.or (PT.or hacc (PT.and (PT.not huni) hex)) (PT.and (PT.and huni hall) hany))

theorem one_le_sz_list {β : Type} [BEnc β] (l : List β) : 1 ≤ sz l := by
  cases l with
  | nil => simp [sz_nil]
  | cons b l => rw [sz_cons]; omega

theorem sz_attrStep_le (acc uni : α × σ → Bool) (step : α × σ × σ → Bool)
    (y : (α × List σ) × List σ) (Z : List σ) : sz (attrStep acc uni step y Z) ≤ sz y.1.2 :=
  sz_filter_le _ _

theorem sz_attrStep_iterate_le' (acc uni : α × σ → Bool) (step : α × σ × σ → Bool)
    (y : (α × List σ) × List σ) (k : ℕ) :
    sz ((attrStep acc uni step y)^[k] []) ≤ sz y.1.2 := by
  cases k with
  | zero => exact one_le_sz_list _
  | succ k => rw [Function.iterate_succ_apply']; exact sz_attrStep_le _ _ _ _ _

theorem sz_attrStep_iterate_le (acc uni : α × σ → Bool) (step : α × σ × σ → Bool)
    (y : (α × List σ) × List σ) (k : ℕ) :
    sz ((attrStep acc uni step y)^[k] []) ≤ 1 * (sz y + 1) ^ 1 := by
  have h1 := sz_attrStep_iterate_le' acc uni step y k
  have h2 : sz y.1.2 ≤ sz y := by
    rw [show sz y = sz y.1 + sz y.2 from sz_prod _ _,
      show sz y.1 = sz y.1.1 + sz y.1.2 from sz_prod _ _]; omega
  simp only [pow_one, one_mul]
  omega

theorem pt_attrFix (ha : PT acc) (hu : PT uni) (hs : PT step) : PT (attrFix acc uni step) := by
  unfold attrFix
  exact PT.iterate (init := fun _ => ([] : List σ)) (PT.const _) (pt_attrStep ha hu hs)
    (fun y k => sz_attrStep_iterate_le acc uni step y k) 1 1

theorem sz_attrFix_le (y : (α × List σ) × List σ) :
    sz (attrFix acc uni step y) ≤ sz y.1.2 :=
  sz_attrStep_iterate_le' _ _ _ _ _

theorem pt_winFix (ha : PT acc) (hu : PT uni) (hs : PT step) : PT (winFix acc uni step) := by
  unfold winFix
  refine PT.iterate (init := fun y : α × List σ => y.2) (c := 1) (d := 1) PT.snd
    (step := fun (y : α × List σ) (W : List σ) => attrFix acc uni step (y, W))
    ((pt_attrFix ha hu hs).of_eq fun _ => rfl) (fun y k => ?_) 1 1
  have hy : sz y.2 ≤ sz y := by rw [show sz y = sz y.1 + sz y.2 from sz_prod _ _]; omega
  cases k with
  | zero => simp only [Function.iterate_zero, id_eq, pow_one, one_mul]; omega
  | succ k =>
    rw [Function.iterate_succ_apply']
    have : sz (attrFix acc uni step (y, (fun W => attrFix acc uni step (y, W))^[k] y.2)) ≤
        sz y.2 := sz_attrFix_le _
    simp only [pow_one, one_mul]
    omega

/-! ### The main theorems -/

/-- **Fair AND-OR games over polynomial-size configurations are in `EXPTIME`.** -/
theorem inExpTime_codeLang_of_buchi {Q : α → Prop} {init acc uni : α × σ → Bool}
    {step : α × σ × σ → Bool} (hi : PT init) (ha : PT acc) (hu : PT uni) (hs : PT step)
    (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ q.eval (sz a) ∧ init (a, c₀) = true ∧
      BWin (q.eval (sz a)) acc uni step a c₀) :
    Cx.EXPTIME (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  have hB : PT fun a : α => q.eval (sz a) :=
    (PT.length (hg.comp (BDec.pt_encL (α := α)))).of_eq fun a => by rw [hglen]; rfl
  let All : α × List Bool → List σ := fun x => aoCands σ (q.eval (sz x.1)) x.2
  have hAll : PT All := pt_aoCands (hB.comp PT.fst) PT.snd
  let r : α × List Bool → Bool := fun x =>
    (winFix acc uni step (x.1, All x)).any fun c => init (x.1, c)
  have hp : PT fun x : α × List Bool => (x.1, All x) := PT.pair PT.fst hAll
  have hr : PT r := PT.any (f := fun x => winFix acc uni step (x.1, All x))
    (p := fun x c => init (x.1, c)) ((pt_winFix ha hu hs).comp hp)
    (show PT fun z : (α × List Bool) × σ => init (z.1.1, z.2) from
      hi.comp (PT.pair (PT.fst.comp PT.fst) PT.snd))
  refine inExpTime_codeLang hr (q + 1) fun a => ?_
  have hpad : 2 ^ (q.eval (sz a) + 1) ≤
      (List.replicate (2 ^ (q + 1).eval (sz a)) true).length := by simp
  have hmem := mem_aoCands (σ := σ) hpad
  rw [hQ]
  simp only [r, List.any_eq_true]
  constructor
  · rintro ⟨c₀, -, hi₀, hw⟩
    exact ⟨c₀, (mem_winFix_iff hmem c₀).2 hw, hi₀⟩
  · rintro ⟨c₀, hc₀, hi₀⟩
    have hw := (mem_winFix_iff hmem c₀).1 hc₀
    obtain ⟨X, hX, hXa⟩ := hw
    exact ⟨c₀, (hXa c₀ hX).sz_le, hi₀, X, hX, hXa⟩

/-- **Fair AND-OR games over exponential-size configurations are in `2-EXPTIME`.** -/
theorem inExp2Time_codeLang_of_buchi {Q : α → Prop} {init acc uni : α × σ → Bool}
    {step : α × σ × σ → Bool} (hi : PT init) (ha : PT acc) (hu : PT uni) (hs : PT step)
    (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ 2 ^ q.eval (sz a) ∧ init (a, c₀) = true ∧
      BWin (2 ^ q.eval (sz a)) acc uni step a c₀) :
    Cx.EXPTIME2 (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  have hB : PT fun a : α => 2 ^ q.eval (sz a) := by
    have h := PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
      (hg.comp (BDec.pt_encL (α := α))) (PT.const false)) (PT.const [true]))
    exact h.of_eq fun a => by rw [List.map_const', hglen, natOfBits_pow]; rfl
  let All : α × List Bool → List σ := fun x => aoCands σ (2 ^ q.eval (sz x.1)) x.2
  have hAll : PT All := pt_aoCands (hB.comp PT.fst) PT.snd
  let r : α × List Bool → Bool := fun x =>
    (winFix acc uni step (x.1, All x)).any fun c => init (x.1, c)
  have hp : PT fun x : α × List Bool => (x.1, All x) := PT.pair PT.fst hAll
  have hr : PT r := PT.any (f := fun x => winFix acc uni step (x.1, All x))
    (p := fun x c => init (x.1, c)) ((pt_winFix ha hu hs).comp hp)
    (show PT fun z : (α × List Bool) × σ => init (z.1.1, z.2) from
      hi.comp (PT.pair (PT.fst.comp PT.fst) PT.snd))
  refine inExp2Time_codeLang hr (q + 1) fun a => ?_
  have hpad : 2 ^ (2 ^ q.eval (sz a) + 1) ≤
      (List.replicate (2 ^ 2 ^ (q + 1).eval (sz a)) true).length := by
    have h1 : 2 ^ q.eval (sz a) + 1 ≤ 2 ^ (q + 1).eval (sz a) := by
      rw [Polynomial.eval_add, Polynomial.eval_one, pow_succ]
      have : 1 ≤ 2 ^ q.eval (sz a) := Nat.one_le_two_pow
      omega
    rw [List.length_replicate]
    exact Nat.pow_le_pow_right (by norm_num) h1
  have hmem := mem_aoCands (σ := σ) hpad
  rw [hQ]
  simp only [r, List.any_eq_true]
  constructor
  · rintro ⟨c₀, -, hi₀, hw⟩
    exact ⟨c₀, (mem_winFix_iff hmem c₀).2 hw, hi₀⟩
  · rintro ⟨c₀, hc₀, hi₀⟩
    have hw := (mem_winFix_iff hmem c₀).1 hc₀
    obtain ⟨X, hX, hXa⟩ := hw
    exact ⟨c₀, (hXa c₀ hX).sz_le, hi₀, X, hX, hXa⟩

end Buchi

end PolyDom

end Syn

end HTN
