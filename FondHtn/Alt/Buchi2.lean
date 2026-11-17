import FondHtn.Alt.Buchi
/-!
# Fair games with conjunctive nodes and separate safety/progress successors

A generalisation of `FondHtn/Alt/Buchi.lean` needed for the summary game of fair strong cyclic
planning on totally ordered problems (`doc/notes_to_fair_3.md`).  Every configuration has a
*kind* `kd` and two successor relations, `stepX` (successors that must be safe, i.e. in `X`) and
`stepZ` (successors used for progress, i.e. in the attractor `Z`):

* accepting configurations (`acc`) are in the attractor;
* kind `1` (**existential**): some `stepX`-successor is in `X` and in the attractor;
* kind `2` (**fair**): all `stepX`-successors are in `X`, some `stepZ`-successor is in the
  attractor;
* kind `3` (**conjunctive**): all `stepX`-successors are in `X`, all `stepZ`-successors are in
  the attractor.

`HTN.Syn.PolyDom.B2Win`: some set `X` containing the configuration is contained in its attractor
(`νX. μZ`).  As in `Buchi.lean`, the winning region over all configurations of size at most `B`
is computed by an outer decreasing and an inner increasing iteration:

* **`HTN.Syn.PolyDom.inExpTime_codeLang_of_buchi2`** — polynomial-size configurations: `EXPTIME`;
* **`HTN.Syn.PolyDom.inExp2Time_codeLang_of_buchi2`** — exponential-size configurations:
  `2-EXPTIME`.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

section Buchi2

set_option linter.unusedSectionVars false

variable {α σ : Type} [BEnc α] [BDec α] [BEnc σ] [BDec σ] [DecidableEq σ]

/-- **The attractor** with respect to `X`. -/
inductive B2Attr (B : ℕ) (acc : α × σ → Bool) (kd : α × σ → ℕ)
    (stepX stepZ : α × σ × σ → Bool) (a : α) (X : σ → Prop) : σ → Prop
  | acc {c : σ} : sz c ≤ B → acc (a, c) = true → B2Attr B acc kd stepX stepZ a X c
  | ex {c c' : σ} : sz c ≤ B → kd (a, c) = 1 → sz c' ≤ B → stepX (a, c, c') = true → X c' →
      B2Attr B acc kd stepX stepZ a X c' → B2Attr B acc kd stepX stepZ a X c
  | fair {c c' : σ} : sz c ≤ B → kd (a, c) = 2 →
      (∀ c'', sz c'' ≤ B → stepX (a, c, c'') = true → X c'') → sz c' ≤ B →
      stepZ (a, c, c') = true → B2Attr B acc kd stepX stepZ a X c' →
      B2Attr B acc kd stepX stepZ a X c
  | conj {c : σ} : sz c ≤ B → kd (a, c) = 3 →
      (∀ c'', sz c'' ≤ B → stepX (a, c, c'') = true → X c'') →
      (∀ c'', sz c'' ≤ B → stepZ (a, c, c'') = true → B2Attr B acc kd stepX stepZ a X c'') →
      B2Attr B acc kd stepX stepZ a X c

/-- **Winning configurations.** -/
def B2Win (B : ℕ) (acc : α × σ → Bool) (kd : α × σ → ℕ) (stepX stepZ : α × σ × σ → Bool)
    (a : α) (c : σ) : Prop :=
  ∃ X : σ → Prop, X c ∧ ∀ c', X c' → B2Attr B acc kd stepX stepZ a X c'

variable {B : ℕ} {acc : α × σ → Bool} {kd : α × σ → ℕ} {stepX stepZ : α × σ × σ → Bool} {a : α}

theorem B2Attr.sz_le {X : σ → Prop} {c : σ} (h : B2Attr B acc kd stepX stepZ a X c) :
    sz c ≤ B := by
  cases h <;> assumption

theorem B2Attr.monoX {X Y : σ → Prop} (hXY : ∀ c, X c → Y c) {c : σ}
    (h : B2Attr B acc kd stepX stepZ a X c) : B2Attr B acc kd stepX stepZ a Y c := by
  induction h with
  | acc hB ha => exact .acc hB ha
  | ex hB hk hB' hs hX _ ih => exact .ex hB hk hB' hs (hXY _ hX) ih
  | fair hB hk hall hB' hs _ ih =>
    exact .fair hB hk (fun c'' h1 h2 => hXY _ (hall c'' h1 h2)) hB' hs ih
  | conj hB hk hall _ ih =>
    exact .conj hB hk (fun c'' h1 h2 => hXY _ (hall c'' h1 h2)) ih

/-! ### The inner least fixpoint -/

/-- One round of the attractor computation on `((a, All), W)`. -/
def attrStep2 (acc : α × σ → Bool) (kd : α × σ → ℕ) (stepX stepZ : α × σ × σ → Bool)
    (y : (α × List σ) × List σ) (Z : List σ) : List σ :=
  y.1.2.filter fun c => acc (y.1.1, c) ||
    (kd (y.1.1, c) == 1 && y.1.2.any fun c' => stepX (y.1.1, c, c') && decide (c' ∈ y.2) &&
      decide (c' ∈ Z)) ||
    (kd (y.1.1, c) == 2 && (y.1.2.all fun c' => !stepX (y.1.1, c, c') || decide (c' ∈ y.2)) &&
      y.1.2.any fun c' => stepZ (y.1.1, c, c') && decide (c' ∈ Z)) ||
    (kd (y.1.1, c) == 3 && (y.1.2.all fun c' => !stepX (y.1.1, c, c') || decide (c' ∈ y.2)) &&
      y.1.2.all fun c' => !stepZ (y.1.1, c, c') || decide (c' ∈ Z))

/-- The attractor of `W`. -/
def attrFix2 (acc : α × σ → Bool) (kd : α × σ → ℕ) (stepX stepZ : α × σ × σ → Bool)
    (y : (α × List σ) × List σ) : List σ :=
  (attrStep2 acc kd stepX stepZ y)^[1 * (sz y + 1) ^ 1] []

/-- The winning region. -/
def winFix2 (acc : α × σ → Bool) (kd : α × σ → ℕ) (stepX stepZ : α × σ × σ → Bool)
    (y : α × List σ) : List σ :=
  (fun W => attrFix2 acc kd stepX stepZ (y, W))^[1 * (sz y + 1) ^ 1] y.2

section Correct

variable {All : List σ} (hAll : ∀ c, c ∈ All ↔ sz c ≤ B)
include hAll

theorem attrStep2_sub (W Z : List σ) :
    ∀ x ∈ attrStep2 acc kd stepX stepZ ((a, All), W) Z, x ∈ All :=
  fun _ hx => (List.mem_filter.1 hx).1

theorem attrStep2_mono (W : List σ) : ∀ Z Z', (∀ x ∈ Z, x ∈ Z') →
    ∀ x ∈ attrStep2 acc kd stepX stepZ ((a, All), W) Z,
      x ∈ attrStep2 acc kd stepX stepZ ((a, All), W) Z' := by
  intro Z Z' h x hx
  unfold attrStep2 at hx ⊢
  simp only [List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hx ⊢
  obtain ⟨hxA, hx⟩ := hx
  refine ⟨hxA, ?_⟩
  rcases hx with ((hx | ⟨hk, c', hc', ⟨hs, hW⟩, hZ⟩) | ⟨⟨hk, hall⟩, c', hc', hs, hZ⟩) |
    ⟨⟨hk, hall⟩, hallZ⟩
  · exact Or.inl (Or.inl (Or.inl hx))
  · exact Or.inl (Or.inl (Or.inr ⟨hk, c', hc', ⟨hs, hW⟩, h c' hZ⟩))
  · exact Or.inl (Or.inr ⟨⟨hk, hall⟩, c', hc', hs, h c' hZ⟩)
  · refine Or.inr ⟨⟨hk, hall⟩, fun c' hc' => ?_⟩
    rcases hallZ c' hc' with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h c' h')

theorem attrStep2_congr (W : List σ) : ∀ Z Z', (∀ x, x ∈ Z ↔ x ∈ Z') →
    attrStep2 acc kd stepX stepZ ((a, All), W) Z = attrStep2 acc kd stepX stepZ ((a, All), W) Z' := by
  intro Z Z' h
  unfold attrStep2
  refine List.filter_congr fun c _ => ?_
  simp only [h]

theorem attrStep2_sound (W : List σ) :
    ∀ k, ∀ c ∈ (attrStep2 acc kd stepX stepZ ((a, All), W))^[k] [],
      B2Attr B acc kd stepX stepZ a (· ∈ W) c := by
  intro k
  induction k with
  | zero => intro c hc; simp at hc
  | succ k ih =>
    intro c hc
    rw [Function.iterate_succ_apply'] at hc
    unfold attrStep2 at hc
    simp only [List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      List.any_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨hcA, hc⟩ := hc
    have hcB := (hAll c).1 hcA
    have hX : ∀ c'', (∀ c' ∈ All, stepX (a, c, c') = false ∨ c' ∈ W) → sz c'' ≤ B →
        stepX (a, c, c'') = true → c'' ∈ W := fun c'' hall h1 h2 => by
      rcases hall c'' ((hAll c'').2 h1) with h | h
      · simp [h2] at h
      · exact h
    rcases hc with ((hc | ⟨hk, c', hc', ⟨hs, hW⟩, hZ⟩) | ⟨⟨hk, hall⟩, c', hc', hs, hZ⟩) |
      ⟨⟨hk, hall⟩, hallZ⟩
    · exact .acc hcB hc
    · exact .ex hcB hk ((hAll c').1 hc') hs hW (ih c' hZ)
    · exact .fair hcB hk (hX · hall) ((hAll c').1 hc') hs (ih c' hZ)
    · refine .conj hcB hk (hX · hall) fun c'' h1 h2 => ?_
      rcases hallZ c'' ((hAll c'').2 h1) with h | h
      · simp [h2] at h
      · exact ih c'' h

theorem mem_attrFix2_iff (W : List σ) (c : σ) :
    c ∈ attrFix2 acc kd stepX stepZ ((a, All), W) ↔ B2Attr B acc kd stepX stepZ a (· ∈ W) c := by
  set F := attrStep2 acc kd stepX stepZ ((a, All), W)
  have hN : All.length + 1 ≤ 1 * (sz ((a, All), W) + 1) ^ 1 := by
    have := length_le_sz All
    rw [sz_prod, sz_prod, pow_one, one_mul]; omega
  have hfix := (iter_fix_of_stab (All := All) (G := F) (attrStep2_congr hAll W) []
    (iter_up_stab (attrStep2_mono hAll W) (attrStep2_sub hAll W)) hN).1
  constructor
  · exact fun h => attrStep2_sound hAll W _ c h
  · intro h
    show c ∈ F^[1 * (sz ((a, All), W) + 1) ^ 1] []
    set Z := F^[1 * (sz ((a, All), W) + 1) ^ 1] []
    have hXall : ∀ c₁, (∀ c'', sz c'' ≤ B → stepX (a, c₁, c'') = true → c'' ∈ W) →
        ∀ c' ∈ All, stepX (a, c₁, c') = false ∨ c' ∈ W := fun c₁ hall c' hc' => by
      by_cases hs'' : stepX (a, c₁, c') = true
      · exact Or.inr (hall c' ((hAll _).1 hc') hs'')
      · exact Or.inl (by simpa using hs'')
    induction h with
    | acc hB ha =>
      rw [← hfix]; unfold F attrStep2
      simp [List.mem_filter, (hAll _).2 hB, ha]
    | @ex c₁ c' hB hk hB' hs hX _ ih =>
      rw [← hfix]; unfold F attrStep2
      simp only [List.mem_filter, (hAll _).2 hB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        List.any_eq_true, List.all_eq_true, true_and, hk, decide_eq_true_eq, Bool.not_eq_true']
      exact Or.inl (Or.inl (Or.inr ⟨c', (hAll _).2 hB', ⟨hs, hX⟩, ih⟩))
    | @fair c₁ c' hB hk hall hB' hs _ ih =>
      rw [← hfix]; unfold F attrStep2
      simp only [List.mem_filter, (hAll _).2 hB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        List.any_eq_true, List.all_eq_true, true_and, hk, decide_eq_true_eq, Bool.not_eq_true']
      exact Or.inl (Or.inr ⟨hXall c₁ hall, c', (hAll _).2 hB', hs, ih⟩)
    | @conj c₁ hB hk hall _ ih =>
      rw [← hfix]; unfold F attrStep2
      simp only [List.mem_filter, (hAll _).2 hB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        List.any_eq_true, List.all_eq_true, true_and, hk, decide_eq_true_eq, Bool.not_eq_true']
      refine Or.inr ⟨hXall c₁ hall, fun c' hc' => ?_⟩
      by_cases hs'' : stepZ (a, c₁, c') = true
      · exact Or.inr (ih c' ((hAll _).1 hc') hs'')
      · exact Or.inl (by simpa using hs'')

/-! ### The outer greatest fixpoint -/

theorem mem_winFix2_iff (c : σ) :
    c ∈ winFix2 acc kd stepX stepZ (a, All) ↔ B2Win B acc kd stepX stepZ a c := by
  set G : List σ → List σ := fun W => attrFix2 acc kd stepX stepZ ((a, All), W)
  have hG : ∀ W x, x ∈ G W ↔ B2Attr B acc kd stepX stepZ a (· ∈ W) x := fun W x =>
    mem_attrFix2_iff hAll W x
  have hsub : ∀ W, ∀ x ∈ G W, x ∈ All := fun W x hx => (hAll x).2 ((hG W x).1 hx).sz_le
  have hmono : ∀ W W', (∀ x ∈ W, x ∈ W') → ∀ x ∈ G W, x ∈ G W' := fun W W' h x hx =>
    (hG W' x).2 (((hG W x).1 hx).monoX fun c hc => h c hc)
  have hcongr : ∀ W W', (∀ x, x ∈ W ↔ x ∈ W') → G W = G W' := by
    intro W W' h
    have hstep : attrStep2 acc kd stepX stepZ ((a, All), W) =
        attrStep2 acc kd stepX stepZ ((a, All), W') := by
      funext Z
      unfold attrStep2
      refine List.filter_congr fun c _ => ?_
      simp only [h]
    have hN : ∀ W₁ : List σ, All.length + 1 ≤ 1 * (sz ((a, All), W₁) + 1) ^ 1 := fun W₁ => by
      have := length_le_sz All
      rw [sz_prod, sz_prod, pow_one, one_mul]; omega
    have hfix := (iter_fix_of_stab (All := All) (G := attrStep2 acc kd stepX stepZ ((a, All), W'))
      (attrStep2_congr hAll W') [] (iter_up_stab (attrStep2_mono hAll W') (attrStep2_sub hAll W'))
      (hN W')).2
    show (attrStep2 acc kd stepX stepZ ((a, All), W))^[_] [] =
      (attrStep2 acc kd stepX stepZ ((a, All), W'))^[_] []
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

theorem pt_attrStep2 (ha : PT acc) (hk : PT kd) (hsX : PT stepX) (hsZ : PT stepZ) :
    PT₂ fun (y : (α × List σ) × List σ) (Z : List σ) => attrStep2 acc kd stepX stepZ y Z := by
  unfold PT₂ attrStep2
  have zA : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.1.1.1 :=
    PT.fst.comp (PT.fst.comp (PT.fst.comp PT.fst))
  have zAll : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.1.1.2 :=
    PT.snd.comp (PT.fst.comp (PT.fst.comp PT.fst))
  have zW : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.1.2 :=
    PT.snd.comp (PT.fst.comp PT.fst)
  have zZ : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.1.2 := PT.snd.comp PT.fst
  have zc : PT fun z : (((α × List σ) × List σ) × List σ) × σ => z.2 := PT.snd
  have wX : PT fun w : ((((α × List σ) × List σ) × List σ) × σ) × σ =>
      stepX (w.1.1.1.1.1, w.1.2, w.2) :=
    hsX.comp (PT.pair (zA.comp PT.fst) (PT.pair (zc.comp PT.fst) PT.snd))
  have wZs : PT fun w : ((((α × List σ) × List σ) × List σ) × σ) × σ =>
      stepZ (w.1.1.1.1.1, w.1.2, w.2) :=
    hsZ.comp (PT.pair (zA.comp PT.fst) (PT.pair (zc.comp PT.fst) PT.snd))
  have wW : PT fun w : ((((α × List σ) × List σ) × List σ) × σ) × σ => decide (w.2 ∈ w.1.1.1.2) :=
    PT.elem (zW.comp PT.fst) PT.snd
  have wZ : PT fun w : ((((α × List σ) × List σ) × List σ) × σ) × σ => decide (w.2 ∈ w.1.1.2) :=
    PT.elem (zZ.comp PT.fst) PT.snd
  have hacc : PT fun z : (((α × List σ) × List σ) × List σ) × σ => acc (z.1.1.1.1, z.2) :=
    ha.comp (PT.pair zA zc)
  have hkd : PT fun z : (((α × List σ) × List σ) × List σ) × σ => kd (z.1.1.1.1, z.2) :=
    hk.comp (PT.pair zA zc)
  have hallX : PT fun z : (((α × List σ) × List σ) × List σ) × σ =>
      z.1.1.1.2.all fun c' => !stepX (z.1.1.1.1, z.2, c') || decide (c' ∈ z.1.1.2) :=
    PT.all zAll (PT.or (PT.not wX) wW)
  exact PT.filter (PT.snd.comp (PT.fst.comp PT.fst))
    (PT.or (PT.or (PT.or hacc (PT.and (PT.beq hkd (PT.const 1))
      (PT.any zAll (PT.and (PT.and wX wW) wZ))))
      (PT.and (PT.and (PT.beq hkd (PT.const 2)) hallX) (PT.any zAll (PT.and wZs wZ))))
      (PT.and (PT.and (PT.beq hkd (PT.const 3)) hallX) (PT.all zAll (PT.or (PT.not wZs) wZ))))

theorem sz_attrStep2_iterate_le' (acc : α × σ → Bool) (kd : α × σ → ℕ)
    (stepX stepZ : α × σ × σ → Bool) (y : (α × List σ) × List σ) (k : ℕ) :
    sz ((attrStep2 acc kd stepX stepZ y)^[k] []) ≤ sz y.1.2 := by
  cases k with
  | zero => exact one_le_sz_list _
  | succ k => rw [Function.iterate_succ_apply']; exact sz_filter_le _ _

theorem pt_attrFix2 (ha : PT acc) (hk : PT kd) (hsX : PT stepX) (hsZ : PT stepZ) :
    PT (attrFix2 acc kd stepX stepZ) := by
  unfold attrFix2
  refine PT.iterate (init := fun _ => ([] : List σ)) (c := 1) (d := 1) (PT.const _) (pt_attrStep2 ha hk hsX hsZ)
    (fun y k => ?_) 1 1
  have h1 := sz_attrStep2_iterate_le' acc kd stepX stepZ y k
  have h2 : sz y.1.2 ≤ sz y := by
    rw [show sz y = sz y.1 + sz y.2 from sz_prod _ _,
      show sz y.1 = sz y.1.1 + sz y.1.2 from sz_prod _ _]; omega
  show sz ((attrStep2 acc kd stepX stepZ y)^[k] []) ≤ 1 * (sz y + 1) ^ 1
  simp only [pow_one, one_mul]
  omega

theorem pt_winFix2 (ha : PT acc) (hk : PT kd) (hsX : PT stepX) (hsZ : PT stepZ) :
    PT (winFix2 acc kd stepX stepZ) := by
  unfold winFix2
  refine PT.iterate (init := fun y : α × List σ => y.2) (c := 1) (d := 1) PT.snd
    (step := fun (y : α × List σ) (W : List σ) => attrFix2 acc kd stepX stepZ (y, W))
    ((pt_attrFix2 ha hk hsX hsZ).of_eq fun _ => rfl) (fun y k => ?_) 1 1
  have hy : sz y.2 ≤ sz y := by rw [show sz y = sz y.1 + sz y.2 from sz_prod _ _]; omega
  cases k with
  | zero => simp only [Function.iterate_zero, id_eq, pow_one, one_mul]; omega
  | succ k =>
    rw [Function.iterate_succ_apply']
    have : sz (attrFix2 acc kd stepX stepZ (y, (fun W => attrFix2 acc kd stepX stepZ (y, W))^[k]
        y.2)) ≤ sz y.2 := sz_attrStep2_iterate_le' _ _ _ _ _ _
    simp only [pow_one, one_mul]
    omega

/-! ### The main theorems -/

/-- **Fair games with conjunctive nodes over polynomial-size configurations are in `EXPTIME`.** -/
theorem inExpTime_codeLang_of_buchi2 {Q : α → Prop} {init acc : α × σ → Bool} {kd : α × σ → ℕ}
    {stepX stepZ : α × σ × σ → Bool} (hi : PT init) (ha : PT acc) (hk : PT kd) (hsX : PT stepX)
    (hsZ : PT stepZ) (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ q.eval (sz a) ∧ init (a, c₀) = true ∧
      B2Win (q.eval (sz a)) acc kd stepX stepZ a c₀) :
    Cx.EXPTIME (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  have hB : PT fun a : α => q.eval (sz a) :=
    (PT.length (hg.comp (BDec.pt_encL (α := α)))).of_eq fun a => by rw [hglen]; rfl
  let All : α × List Bool → List σ := fun x => aoCands σ (q.eval (sz x.1)) x.2
  have hAll : PT All := pt_aoCands (hB.comp PT.fst) PT.snd
  let r : α × List Bool → Bool := fun x =>
    (winFix2 acc kd stepX stepZ (x.1, All x)).any fun c => init (x.1, c)
  have hp : PT fun x : α × List Bool => (x.1, All x) := PT.pair PT.fst hAll
  have hr : PT r := PT.any (f := fun x => winFix2 acc kd stepX stepZ (x.1, All x))
    (p := fun x c => init (x.1, c)) ((pt_winFix2 ha hk hsX hsZ).comp hp)
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
    exact ⟨c₀, (mem_winFix2_iff hmem c₀).2 hw, hi₀⟩
  · rintro ⟨c₀, hc₀, hi₀⟩
    have hw := (mem_winFix2_iff hmem c₀).1 hc₀
    obtain ⟨X, hX, hXa⟩ := hw
    exact ⟨c₀, (hXa c₀ hX).sz_le, hi₀, X, hX, hXa⟩

/-- **Fair games with conjunctive nodes over exponential-size configurations are in
`2-EXPTIME`.** -/
theorem inExp2Time_codeLang_of_buchi2 {Q : α → Prop} {init acc : α × σ → Bool} {kd : α × σ → ℕ}
    {stepX stepZ : α × σ × σ → Bool} (hi : PT init) (ha : PT acc) (hk : PT kd) (hsX : PT stepX)
    (hsZ : PT stepZ) (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ 2 ^ q.eval (sz a) ∧ init (a, c₀) = true ∧
      B2Win (2 ^ q.eval (sz a)) acc kd stepX stepZ a c₀) :
    Cx.EXPTIME2 (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  have hB : PT fun a : α => 2 ^ q.eval (sz a) := by
    have h := PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
      (hg.comp (BDec.pt_encL (α := α))) (PT.const false)) (PT.const [true]))
    exact h.of_eq fun a => by rw [List.map_const', hglen, natOfBits_pow]; rfl
  let All : α × List Bool → List σ := fun x => aoCands σ (2 ^ q.eval (sz x.1)) x.2
  have hAll : PT All := pt_aoCands (hB.comp PT.fst) PT.snd
  let r : α × List Bool → Bool := fun x =>
    (winFix2 acc kd stepX stepZ (x.1, All x)).any fun c => init (x.1, c)
  have hp : PT fun x : α × List Bool => (x.1, All x) := PT.pair PT.fst hAll
  have hr : PT r := PT.any (f := fun x => winFix2 acc kd stepX stepZ (x.1, All x))
    (p := fun x c => init (x.1, c)) ((pt_winFix2 ha hk hsX hsZ).comp hp)
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
    exact ⟨c₀, (mem_winFix2_iff hmem c₀).2 hw, hi₀⟩
  · rintro ⟨c₀, hc₀, hi₀⟩
    have hw := (mem_winFix2_iff hmem c₀).1 hc₀
    obtain ⟨X, hX, hXa⟩ := hw
    exact ⟨c₀, (hXa c₀ hX).sz_le, hi₀, X, hX, hXa⟩

end Buchi2

end PolyDom

end Syn

end HTN
