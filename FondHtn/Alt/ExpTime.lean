import HtnComplexity.PT.ExpTime
import HtnComplexity.PT.NExp
/-!
# AND-OR reachability games over polynomial-size configurations are in `EXPTIME`

The easy direction of Chandra–Kozen–Stockmeyer (`APSPACE ⊆ EXPTIME`), stated for an explicit
game: configurations `c : σ` whose codes have length at most `B = q(|code of a|)`;
an *accepting* configuration wins, an *existential* configuration (`uni = false`) wins if some
successor wins, a *universal* configuration (`uni = true`) wins if all its successors win
(vacuously if it has none).  The winning configurations are the least fixpoint `AOWin`.

* **`HTN.Syn.PolyDom.inExpTime_codeLang_of_andOr`** — if `Q a` holds iff some initial
  configuration of size at most `q(|code of a|)` is winning, the language of the codes of the
  values satisfying `Q` is in `EXPTIME`.

Proof: with an exponential padding, all candidate configurations are enumerated
(`HTN.Syn.PolyDom.aoCands`: the codes among the strings `(bitsOfNat i).dropLast`), and the least
fixpoint is computed by iterating the one-step operator `HTN.Syn.PolyDom.aoStep` `|All| + 1`
times (more precisely `|code of (a, All)| + 1` times).  The iterates are increasing and bounded
by `All`, hence stabilise (`HTN.Syn.PolyDom.aoStep_iterate_fix`); the stable list is closed under
the rules, so it contains every winning configuration, and every element is winning.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

section AndOr

set_option linter.unusedSectionVars false

variable {α σ : Type} [BEnc α] [BDec α] [BEnc σ] [BDec σ] [DecidableEq σ]

/-- **Winning configurations** of the AND-OR game on `a` with configurations of size at most `B`:
the least set closed under the three rules. -/
inductive AOWin (B : ℕ) (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (a : α) : σ → Prop
  | acc {c : σ} : sz c ≤ B → acc (a, c) = true → AOWin B acc uni step a c
  | ex {c c' : σ} : sz c ≤ B → uni (a, c) = false → sz c' ≤ B → step (a, c, c') = true →
      AOWin B acc uni step a c' → AOWin B acc uni step a c
  | univ {c : σ} : sz c ≤ B → uni (a, c) = true →
      (∀ c', sz c' ≤ B → step (a, c, c') = true → AOWin B acc uni step a c') →
      AOWin B acc uni step a c

/-- One round of the fixpoint computation on `y = (a, All)`: the configurations of `All` that
win given that the configurations of `W` win. -/
def aoStep (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (y : α × List σ) (W : List σ) :
    List σ :=
  y.2.filter fun c => acc (y.1, c) || (!uni (y.1, c) && W.any fun c' => step (y.1, c, c')) ||
    (uni (y.1, c) && y.2.all fun c' => !step (y.1, c, c') || decide (c' ∈ W))

/-- The fixpoint computation: `|code of y| + 1` rounds from the empty list. -/
def aoFix (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (y : α × List σ) : List σ :=
  (aoStep acc uni step y)^[1 * (sz y + 1) ^ 1] []

/-! ### Sizes -/

theorem sz_filter_le {β : Type} [BEnc β] (l : List β) (p : β → Bool) : sz (l.filter p) ≤ sz l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.filter_cons]
    split
    · rw [sz_cons, sz_cons]; omega
    · rw [sz_cons]; omega

theorem sz_aoStep_iterate_le (acc uni : α × σ → Bool) (step : α × σ × σ → Bool)
    (y : α × List σ) (k : ℕ) : sz ((aoStep acc uni step y)^[k] []) ≤ 1 * (sz y + 1) ^ 1 := by
  cases k with
  | zero => simp [sz_nil]
  | succ k =>
    rw [Function.iterate_succ_apply']
    have h1 := sz_filter_le y.2 (fun c => acc (y.1, c) ||
      (!uni (y.1, c) && ((aoStep acc uni step y)^[k] []).any fun c' => step (y.1, c, c')) ||
      (uni (y.1, c) && y.2.all fun c' => !step (y.1, c, c') ||
        decide (c' ∈ (aoStep acc uni step y)^[k] [])))
    have h2 : sz y.2 ≤ sz y := by rw [show sz y = sz y.1 + sz y.2 from sz_prod _ _]; omega
    simp only [aoStep, pow_one, one_mul]
    omega

/-! ### Polynomial time of one round and of the iteration -/

theorem pt_aoStep {acc uni : α × σ → Bool} {step : α × σ × σ → Bool}
    (ha : PT acc) (hu : PT uni) (hs : PT step) :
    PT₂ fun (y : α × List σ) (W : List σ) => aoStep acc uni step y W := by
  unfold PT₂ aoStep
  -- context `z : ((α × List σ) × List σ) × σ`
  have zA : PT fun z : ((α × List σ) × List σ) × σ => z.1.1.1 :=
    PT.fst.comp (PT.fst.comp PT.fst)
  have zAll : PT fun z : ((α × List σ) × List σ) × σ => z.1.1.2 :=
    PT.snd.comp (PT.fst.comp PT.fst)
  have zW : PT fun z : ((α × List σ) × List σ) × σ => z.1.2 := PT.snd.comp PT.fst
  have zc : PT fun z : ((α × List σ) × List σ) × σ => z.2 := PT.snd
  -- context `w : (((α × List σ) × List σ) × σ) × σ`
  have wst : PT fun w : (((α × List σ) × List σ) × σ) × σ => step (w.1.1.1.1, w.1.2, w.2) :=
    hs.comp (PT.pair (zA.comp PT.fst) (PT.pair (zc.comp PT.fst) PT.snd))
  have hany : PT fun z : ((α × List σ) × List σ) × σ => z.1.2.any fun c' => step (z.1.1.1, z.2, c') :=
    PT.any (f := fun z : ((α × List σ) × List σ) × σ => z.1.2)
      (p := fun z c' => step (z.1.1.1, z.2, c')) zW wst
  have hall : PT fun z : ((α × List σ) × List σ) × σ =>
      z.1.1.2.all fun c' => !step (z.1.1.1, z.2, c') || decide (c' ∈ z.1.2) :=
    PT.all (f := fun z : ((α × List σ) × List σ) × σ => z.1.1.2)
      (p := fun z c' => !step (z.1.1.1, z.2, c') || decide (c' ∈ z.1.2)) zAll
      (PT.or (PT.not wst) (PT.elem (zW.comp PT.fst) PT.snd))
  have hacc : PT fun z : ((α × List σ) × List σ) × σ => acc (z.1.1.1, z.2) :=
    ha.comp (PT.pair zA zc)
  have huni : PT fun z : ((α × List σ) × List σ) × σ => uni (z.1.1.1, z.2) :=
    hu.comp (PT.pair zA zc)
  exact PT.filter (f := fun p : (α × List σ) × List σ => p.1.2)
    (p := fun p c => acc (p.1.1, c) || (!uni (p.1.1, c) && p.2.any fun c' => step (p.1.1, c, c')) ||
      (uni (p.1.1, c) && p.1.2.all fun c' => !step (p.1.1, c, c') || decide (c' ∈ p.2)))
    (PT.snd.comp PT.fst) (PT.or (PT.or hacc (PT.and (PT.not huni) hany)) (PT.and huni hall))

theorem pt_aoFix {acc uni : α × σ → Bool} {step : α × σ × σ → Bool}
    (ha : PT acc) (hu : PT uni) (hs : PT step) : PT (aoFix acc uni step) := by
  unfold aoFix
  exact PT.iterate (init := fun _ => ([] : List σ)) (PT.const _) (pt_aoStep ha hu hs)
    (fun y k => sz_aoStep_iterate_le acc uni step y k) 1 1

/-! ### Correctness of the fixpoint computation -/

section Fix

variable {acc uni : α × σ → Bool} {step : α × σ × σ → Bool} {a : α} {All : List σ}

theorem aoStep_congr {W W' : List σ} (h : ∀ x, x ∈ W ↔ x ∈ W') :
    aoStep acc uni step (a, All) W = aoStep acc uni step (a, All) W' := by
  unfold aoStep
  refine List.filter_congr fun c _ => ?_
  have h1 : (W.any fun c' => step (a, c, c')) = (W'.any fun c' => step (a, c, c')) := by
    apply Bool.eq_iff_iff.2; simp [List.any_eq_true, h]
  have h2 : (All.all fun c' => !step (a, c, c') || decide (c' ∈ W)) =
      (All.all fun c' => !step (a, c, c') || decide (c' ∈ W')) := by
    apply Bool.eq_iff_iff.2; simp [List.all_eq_true, h]
  simp only [h1, h2]

theorem aoStep_mono {W W' : List σ} (h : ∀ x ∈ W, x ∈ W') :
    ∀ x ∈ aoStep acc uni step (a, All) W, x ∈ aoStep acc uni step (a, All) W' := by
  intro x hx
  unfold aoStep at hx ⊢
  simp only [List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hx ⊢
  obtain ⟨hxA, hx⟩ := hx
  refine ⟨hxA, ?_⟩
  rcases hx with (hx | ⟨hu, c', hc', hs⟩) | ⟨hu, hall⟩
  · exact Or.inl (Or.inl hx)
  · exact Or.inl (Or.inr ⟨hu, c', h c' hc', hs⟩)
  · refine Or.inr ⟨hu, fun c' hc' => ?_⟩
    rcases hall c' hc' with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h c' h')

theorem aoStep_sub (W : List σ) : ∀ x ∈ aoStep acc uni step (a, All) W, x ∈ All := by
  intro x hx; unfold aoStep at hx; exact (List.mem_filter.1 hx).1

theorem aoStep_iterate_mono (k : ℕ) :
    ∀ x ∈ (aoStep acc uni step (a, All))^[k] [], x ∈ (aoStep acc uni step (a, All))^[k + 1] [] := by
  induction k with
  | zero => intro x hx; simp at hx
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx ⊢
    exact aoStep_mono ih x hx

/-- **The iteration stabilises** after at most `|All|` rounds. -/
theorem aoStep_iterate_stab :
    ∃ k ≤ All.length, ((aoStep acc uni step (a, All))^[k] []).toFinset =
      ((aoStep acc uni step (a, All))^[k + 1] []).toFinset := by
  classical
  set F := aoStep acc uni step (a, All)
  by_contra hc
  push_neg at hc
  have hsub : ∀ k, (F^[k] []).toFinset ⊆ (F^[k + 1] []).toFinset := fun k x hx => by
    rw [List.mem_toFinset] at hx ⊢; exact aoStep_iterate_mono k x hx
  have hcard : ∀ k ≤ All.length + 1, k ≤ (F^[k] []).toFinset.card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hss : (F^[k] []).toFinset ⊂ (F^[k + 1] []).toFinset :=
        Finset.ssubset_iff_subset_ne.2 ⟨hsub k, hc k (by omega)⟩
      have := Finset.card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hcard (All.length + 1) le_rfl
  have h2 : (F^[All.length + 1] []).toFinset ⊆ All.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    rw [Function.iterate_succ_apply'] at hx
    exact aoStep_sub _ x hx
  have h3 := Finset.card_le_card h2
  have h4 := List.toFinset_card_le All
  omega

/-- **After `|All| + 1` or more rounds the list is a fixpoint.** -/
theorem aoStep_iterate_fix {N : ℕ} (hN : All.length + 1 ≤ N) :
    aoStep acc uni step (a, All) ((aoStep acc uni step (a, All))^[N] []) =
      (aoStep acc uni step (a, All))^[N] [] := by
  set F := aoStep acc uni step (a, All)
  obtain ⟨k, hk, heq⟩ := aoStep_iterate_stab (acc := acc) (uni := uni) (step := step) (a := a)
    (All := All)
  have hstable : ∀ j, F^[k + 1 + j] [] = F^[k + 1] [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show k + 1 + (j + 1) = (k + 1 + j) + 1 by omega, Function.iterate_succ_apply', ih,
        Function.iterate_succ_apply']
      exact aoStep_congr fun x => by
        have := Finset.ext_iff.1 heq x
        rw [List.mem_toFinset, List.mem_toFinset, Function.iterate_succ_apply'] at this
        exact this.symm
  obtain ⟨j, rfl⟩ : ∃ j, N = k + 1 + j := ⟨N - (k + 1), by omega⟩
  rw [← Function.iterate_succ_apply' F, show (k + 1 + j).succ = k + 1 + (j + 1) by omega,
    hstable, hstable]

variable {B : ℕ}

/-- **Soundness:** every configuration in an iterate is winning. -/
theorem aoWin_of_mem_iterate (hAll : ∀ c, c ∈ All ↔ sz c ≤ B) :
    ∀ k, ∀ c ∈ (aoStep acc uni step (a, All))^[k] [], AOWin B acc uni step a c := by
  intro k
  induction k with
  | zero => intro c hc; simp at hc
  | succ k ih =>
    intro c hc
    rw [Function.iterate_succ_apply'] at hc
    unfold aoStep at hc
    simp only [List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hcA, hc⟩ := hc
    have hcB := (hAll c).1 hcA
    rcases hc with (hc | ⟨hu, c', hc', hs⟩) | ⟨hu, hall⟩
    · exact AOWin.acc hcB hc
    · have hc'A := aoStep_iterate_mono k c' hc'
      rw [Function.iterate_succ_apply'] at hc'A
      exact AOWin.ex hcB hu ((hAll c').1 (aoStep_sub _ c' hc'A)) hs (ih c' hc')
    · refine AOWin.univ hcB hu fun c' hc'B hs => ?_
      rcases hall c' ((hAll c').2 hc'B) with h' | h'
      · simp [hs] at h'
      · exact ih c' h'

/-- **Completeness:** every winning configuration is in a stable iterate. -/
theorem mem_iterate_of_aoWin (hAll : ∀ c, c ∈ All ↔ sz c ≤ B) {N : ℕ} (hN : All.length + 1 ≤ N)
    {c : σ} (hc : AOWin B acc uni step a c) : c ∈ (aoStep acc uni step (a, All))^[N] [] := by
  have hfix := aoStep_iterate_fix (acc := acc) (uni := uni) (step := step) (a := a) hN
  set W := (aoStep acc uni step (a, All))^[N] []
  induction hc with
  | acc hB ha =>
    rw [← hfix]; unfold aoStep
    simp [List.mem_filter, (hAll _).2 hB, ha]
  | ex hB hu hB' hs _ ih =>
    rw [← hfix]; unfold aoStep
    simp only [List.mem_filter, (hAll _).2 hB, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, true_and, hu, Bool.not_false]
    exact Or.inl (Or.inr ⟨_, ih, hs⟩)
  | @univ c₁ hB hu _ ih =>
    rw [← hfix]; unfold aoStep
    simp only [List.mem_filter, (hAll _).2 hB, Bool.or_eq_true, Bool.and_eq_true,
      List.all_eq_true, true_and, hu, decide_eq_true_eq]
    refine Or.inr fun c' hc' => ?_
    by_cases hs : step (a, c₁, c') = true
    · simp [ih c' ((hAll c').1 hc') hs]
    · simp [hs]

theorem mem_aoFix_iff (hAll : ∀ c, c ∈ All ↔ sz c ≤ B) (c : σ) :
    c ∈ aoFix acc uni step (a, All) ↔ AOWin B acc uni step a c := by
  have hN : All.length + 1 ≤ 1 * (sz (a, All) + 1) ^ 1 := by
    have := length_le_sz All
    rw [sz_prod, pow_one, one_mul]; omega
  exact ⟨fun h => aoWin_of_mem_iterate hAll _ c h, fun h => mem_iterate_of_aoWin hAll hN h⟩

end Fix

/-! ### Enumerating the candidate configurations -/

/-- All configurations whose codes have length at most `B`, if `2 ^ (B + 1) ≤ |pad|`. -/
def aoCands (σ : Type) [BEnc σ] [BDec σ] (B : ℕ) (pad : List Bool) : List σ :=
  ((((List.range pad.length).map fun i => (bitsOfNat i).dropLast).filter fun w =>
    decide (w.length ≤ B) && isCode σ w)).map fun w => (decR w : σ × List Bool).1

theorem strip_append_true (w : List Bool) : strip (w ++ [true]) = w ++ [true] := by
  induction w with
  | nil => rw [List.nil_append, strip_cons]; simp [strip_nil]
  | cons b w ih =>
    rw [List.cons_append, strip_cons, ih]
    simp

theorem mem_aoCands {B : ℕ} {pad : List Bool} (hpad : 2 ^ (B + 1) ≤ pad.length) (c : σ) :
    c ∈ aoCands σ B pad ↔ sz c ≤ B := by
  unfold aoCands
  simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨-, hwB, hw⟩, rfl⟩
    obtain ⟨c', rfl⟩ := (isCode_iff _).1 hw
    rw [decR_enc']
    exact hwB
  · intro hc
    refine ⟨enc c, ⟨⟨natOfBits (enc c ++ [true]), ?_, ?_⟩, hc, (isCode_iff _).2 ⟨c, rfl⟩⟩,
      decR_enc' c⟩
    · have h1 := natOfBits_lt' (enc c ++ [true])
      have h2 : 2 ^ (enc c ++ [true]).length ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by omega)
        (by simp; exact hc)
      omega
    · rw [bitsOfNat_natOfBits, strip_append_true]; simp

theorem pt_aoCands {β : Type} [BEnc β] {B : β → ℕ} {pad : β → List Bool} (hB : PT B)
    (hpad : PT pad) : PT fun x => aoCands σ (B x) (pad x) := by
  unfold aoCands
  have hdl : PT fun q : β × ℕ => (bitsOfNat q.2).dropLast := by
    refine (PT.reverse (PT.tail (PT.reverse (PT.bits.comp PT.snd)))).of_eq fun q => ?_
    simp [List.tail_reverse]
  have hm := PT.map (g := fun (_ : β) (i : ℕ) => (bitsOfNat i).dropLast) (PT.rangeLength hpad) hdl
  have hf := PT.filter (p := fun x (w : List Bool) => decide (w.length ≤ B x) && isCode σ w) hm
    (PT.and (PT.le (PT.length PT.snd) (hB.comp PT.fst)) ((pt_isCode σ).comp PT.snd))
  exact PT.map (g := fun (_ : β) (w : List Bool) => (decR w : σ × List Bool).1) hf
    (PT.fst.comp (BDec.pt_decR.comp PT.snd))

/-! ### The main theorem -/

/-- **AND-OR reachability games over polynomial-size configurations are decidable in exponential
time.**  If `Q a` holds iff some initial configuration `c₀` (of size at most `q(|a|)`) is winning
in the game on `a` with configurations of size at most `q(|a|)`, the language of the codes of the
values satisfying `Q` is in `EXPTIME`.  Universal configurations without successors win
vacuously. -/
theorem inExpTime_codeLang_of_andOr {Q : α → Prop} {init acc uni : α × σ → Bool}
    {step : α × σ × σ → Bool} (hi : PT init) (ha : PT acc) (hu : PT uni) (hs : PT step)
    (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ q.eval (sz a) ∧ init (a, c₀) = true ∧
      AOWin (q.eval (sz a)) acc uni step a c₀) :
    Cx.EXPTIME (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  have hB : PT fun a : α => q.eval (sz a) :=
    (PT.length (hg.comp (BDec.pt_encL (α := α)))).of_eq fun a => by rw [hglen]; rfl
  let All : α × List Bool → List σ := fun x => aoCands σ (q.eval (sz x.1)) x.2
  have hAll : PT All := pt_aoCands (hB.comp PT.fst) PT.snd
  let r : α × List Bool → Bool := fun x =>
    (aoFix acc uni step (x.1, All x)).any fun c => init (x.1, c)
  have hp : PT fun x : α × List Bool => (x.1, All x) := PT.pair PT.fst hAll
  have hr : PT r := PT.any (f := fun x => aoFix acc uni step (x.1, All x))
    (p := fun x c => init (x.1, c)) ((pt_aoFix ha hu hs).comp hp)
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
    exact ⟨c₀, (mem_aoFix_iff hmem c₀).2 hw, hi₀⟩
  · rintro ⟨c₀, hc₀, hi₀⟩
    have hw := (mem_aoFix_iff hmem c₀).1 hc₀
    refine ⟨c₀, ?_, hi₀, hw⟩
    cases hw <;> assumption

end AndOr

end PolyDom

end Syn

end HTN
