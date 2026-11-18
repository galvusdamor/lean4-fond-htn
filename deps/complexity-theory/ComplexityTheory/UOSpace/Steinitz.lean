import Mathlib

/-!
# The Steinitz lemma, and a single-exponential zero-sum bound

The small-solution theorem for unordered HTN planning in
`HtnComplexity/UODecide/Abstract.lean` rests on a zero-sum lemma whose bound
`(2a+2)^(3^n)` is *doubly* exponential in the dimension `n`.  For the polynomial-space upper bound
of Lauer, Höller and Bercher we need a bound whose logarithm is polynomial.  This file proves it
through the **Steinitz lemma** (in the form of Grinberg and Sevastyanov):

* `HTN.Steinitz.exists_few_frac` — a point of a box `[0,1]^I` cut by linear equations into a
  space of dimension `r` can be moved, without leaving the box or violating the equations, to a
  point with at most `r` fractional coordinates;
* `HTN.Steinitz.steinitz` — a zero-sum family of integer vectors of `ℤ^D` with entries in
  `[-a, a]` can be listed so that every prefix sum has entries in `[-|D|·a, |D|·a]`;
* `HTN.Steinitz.exists_proper_zero_sum` — consequently a zero-sum family of more than
  `zsP n a = (2·n·a + 1)^n` such vectors (`n` the number of coordinates) has a proper nonempty
  zero-sum subfamily;
* `HTN.Steinitz.exists_small_zero_sum_mem` — every zero-sum family has a zero-sum subfamily of at
  most `zsP n a` members containing any prescribed member.

Vectors in the last two statements are functions `ℕ → ℤ` vanishing outside a finite set of
coordinates `A`, as in `ComplexityTheory/UODecide/ZeroSum.lean`.
-/

namespace HTN

namespace Steinitz

open Finset

/-! ### Few fractional coordinates -/

section Frac

variable {α E : Type*} [Fintype E] [DecidableEq α]

/-- The fractional coordinates of `μ` on `I`. -/
def fracSet (I : Finset α) (μ : α → ℚ) : Finset α := I.filter fun i => 0 < μ i ∧ μ i < 1

/-- One reduction step: if more than `|E|` coordinates are fractional, a point with fewer
fractional coordinates exists. -/
theorem frac_step (I : Finset α) (w : α → E → ℚ) (b : E → ℚ) (μ : α → ℚ)
    (h0 : ∀ i ∈ I, 0 ≤ μ i) (h1 : ∀ i ∈ I, μ i ≤ 1) (hb : ∑ i ∈ I, μ i • w i = b)
    (hc : Fintype.card E < (fracSet I μ).card) :
    ∃ μ', (∀ i ∈ I, 0 ≤ μ' i) ∧ (∀ i ∈ I, μ' i ≤ 1) ∧ ∑ i ∈ I, μ' i • w i = b ∧
      (fracSet I μ').card < (fracSet I μ).card := by
  classical
  set Fr := fracSet I μ with hFr
  -- a linear dependence among the fractional columns
  have hdep : ¬ LinearIndependent ℚ (fun i : Fr => w i) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    omega
  obtain ⟨g, hg, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.1 hdep
  -- normalise so that some coefficient is positive
  obtain ⟨g, hg, i₁, hi₁⟩ : ∃ g : Fr → ℚ, ∑ i, g i • w i = 0 ∧ ∃ i, 0 < g i := by
    rcases lt_or_gt_of_ne hi₁ with h | h
    · refine ⟨fun i => -g i, ?_, i₁, by simpa using h⟩
      simp only [neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
    · exact ⟨g, hg, i₁, h⟩
  let d : α → ℚ := fun i => if h : i ∈ Fr then g ⟨i, h⟩ else 0
  have hdFr : ∀ i, i ∉ Fr → d i = 0 := fun i hi => by simp [d, hi]
  have hFrI : Fr ⊆ I := Finset.filter_subset _ _
  have hdsum : ∑ i ∈ I, d i • w i = 0 := by
    rw [← Finset.sum_subset hFrI (fun i _ hi => by rw [hdFr i hi, zero_smul])]
    rw [← hg, ← Finset.sum_coe_sort Fr]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [d, i.2]
  -- the step length of each coordinate
  let tt : α → ℚ := fun i => if 0 < d i then (1 - μ i) / d i else μ i / (-d i)
  let Nz := Fr.filter fun i => d i ≠ 0
  have hNz : Nz.Nonempty := ⟨i₁.1, Finset.mem_filter.2 ⟨i₁.2, by simp [d, i₁.2, hi₁.ne']⟩⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image Nz tt hNz
  have hi₀Fr : i₀ ∈ Fr := (Finset.mem_filter.1 hi₀).1
  have hdi₀ : d i₀ ≠ 0 := (Finset.mem_filter.1 hi₀).2
  have hfrac : ∀ i ∈ Fr, 0 < μ i ∧ μ i < 1 := fun i hi => (Finset.mem_filter.1 hi).2
  have htt_pos : ∀ i ∈ Nz, 0 < tt i := by
    intro i hi
    obtain ⟨hiFr, hdi⟩ := Finset.mem_filter.1 hi
    obtain ⟨hμ0, hμ1⟩ := hfrac i hiFr
    simp only [tt]
    split_ifs with h
    · exact div_pos (by linarith) h
    · exact div_pos hμ0 (by
        have : d i < 0 := lt_of_le_of_ne (not_lt.1 h) hdi
        linarith)
  set t := tt i₀ with ht
  have htpos : 0 < t := htt_pos i₀ hi₀
  refine ⟨fun i => μ i + t * d i, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hd : d i = 0
    · simp [hd, h0 i hi]
    have hiFr : i ∈ Fr := by by_contra h; exact hd (hdFr i h)
    have hiNz : i ∈ Nz := Finset.mem_filter.2 ⟨hiFr, hd⟩
    have hle := hmin i hiNz
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · have : tt i = μ i / (-d i) := by simp [tt, not_lt.2 hneg.le]
      rw [this, le_div_iff₀ (by linarith)] at hle
      show 0 ≤ μ i + t * d i
      nlinarith
    · have := h0 i hi
      show 0 ≤ μ i + t * d i
      have : 0 < t * d i := mul_pos htpos hpos
      linarith
  · intro i hi
    by_cases hd : d i = 0
    · simp [hd, h1 i hi]
    have hiFr : i ∈ Fr := by by_contra h; exact hd (hdFr i h)
    have hiNz : i ∈ Nz := Finset.mem_filter.2 ⟨hiFr, hd⟩
    have hle := hmin i hiNz
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · have := h1 i hi
      show μ i + t * d i ≤ 1
      have : t * d i < 0 := mul_neg_of_pos_of_neg htpos hneg
      linarith
    · have : tt i = (1 - μ i) / d i := by simp [tt, hpos]
      rw [this, le_div_iff₀ hpos] at hle
      show μ i + t * d i ≤ 1
      linarith
  · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hdsum, smul_zero,
      add_zero, hb]
  · -- the fractional coordinates shrink: `i₀` is no longer fractional
    have hsub : fracSet I (fun i => μ i + t * d i) ⊆ Fr.erase i₀ := by
      intro i hi
      obtain ⟨hiI, hlo, hhi⟩ := Finset.mem_filter.1 hi
      simp only at hlo hhi
      have hiFr : i ∈ Fr := by
        by_contra hn
        have hd := hdFr i hn
        simp only [hd, mul_zero, add_zero] at hlo hhi
        exact hn (Finset.mem_filter.2 ⟨hiI, hlo, hhi⟩)
      refine Finset.mem_erase.2 ⟨?_, hiFr⟩
      rintro rfl
      rcases lt_or_gt_of_ne hdi₀ with hneg | hpos
      · have e : t = μ i / (-d i) := by simp [t, tt, not_lt.2 hneg.le]
        have : μ i + t * d i = 0 := by
          rw [e]; field_simp; ring
        rw [this] at hlo
        exact lt_irrefl _ hlo
      · have e : t = (1 - μ i) / d i := by simp [t, tt, hpos]
        have : μ i + t * d i = 1 := by
          rw [e]; field_simp; ring
        rw [this] at hhi
        exact lt_irrefl _ hhi
    calc (fracSet I (fun i => μ i + t * d i)).card ≤ (Fr.erase i₀).card := Finset.card_le_card hsub
      _ < Fr.card := Finset.card_erase_lt_of_mem hi₀Fr

/-- **Few fractional coordinates.**  A point of the box `[0,1]^I` satisfying the linear equations
`∑ μᵢ wᵢ = b` (with `wᵢ` in a space of dimension `|E|`) can be replaced by one with at most
`|E|` fractional coordinates. -/
theorem exists_few_frac (I : Finset α) (w : α → E → ℚ) (b : E → ℚ) :
    ∀ (n : ℕ) (μ : α → ℚ), (fracSet I μ).card = n → (∀ i ∈ I, 0 ≤ μ i) → (∀ i ∈ I, μ i ≤ 1) →
      ∑ i ∈ I, μ i • w i = b →
      ∃ μ', (∀ i ∈ I, 0 ≤ μ' i) ∧ (∀ i ∈ I, μ' i ≤ 1) ∧ ∑ i ∈ I, μ' i • w i = b ∧
        (fracSet I μ').card ≤ Fintype.card E := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro μ hn h0 h1 hb
    by_cases hc : (fracSet I μ).card ≤ Fintype.card E
    · exact ⟨μ, h0, h1, hb, hc⟩
    push_neg at hc
    obtain ⟨μ', h0', h1', hb', hlt⟩ := frac_step I w b μ h0 h1 hb hc
    exact ih _ (hn ▸ hlt) μ' rfl h0' h1' hb'

end Frac

/-! ### The Steinitz lemma -/

section Stz

variable {α D : Type*} [DecidableEq α] [Fintype D]

/-- The columns of the linear system of the Steinitz step: the vector and a `1`. -/
def colw (u : α → D → ℤ) (i : α) : Option D → ℚ
  | none => 1
  | some d => (u i d : ℚ)

omit [DecidableEq α] [Fintype D] in
theorem sum_smul_colw_none (J : Finset α) (u : α → D → ℤ) (μ : α → ℚ) :
    (∑ i ∈ J, μ i • colw u i) none = ∑ i ∈ J, μ i := by
  simp [Finset.sum_apply, colw]

omit [DecidableEq α] [Fintype D] in
theorem sum_smul_colw_some (J : Finset α) (u : α → D → ℤ) (μ : α → ℚ) (d : D) :
    (∑ i ∈ J, μ i • colw u i) (some d) = ∑ i ∈ J, μ i * (u i d : ℚ) := by
  simp [Finset.sum_apply, colw]

/-- **The Steinitz step**: a fractional weighting of `J` with total weight `|J| - |D|` that
balances the vectors can be traded for one of total weight `|J| - 1 - |D|` on `J` minus one
element. -/
theorem stz_step (J : Finset α) (u : α → D → ℤ) (lam : α → ℚ) (hk : Fintype.card D < J.card)
    (h0 : ∀ i ∈ J, 0 ≤ lam i) (h1 : ∀ i ∈ J, lam i ≤ 1)
    (hs : ∀ d, ∑ i ∈ J, lam i * (u i d : ℚ) = 0)
    (hsum : ∑ i ∈ J, lam i = (J.card : ℚ) - Fintype.card D) :
    ∃ j ∈ J, ∃ lam' : α → ℚ, (∀ i ∈ J.erase j, 0 ≤ lam' i) ∧ (∀ i ∈ J.erase j, lam' i ≤ 1) ∧
      (∀ d, ∑ i ∈ J.erase j, lam' i * (u i d : ℚ) = 0) ∧
      ∑ i ∈ J.erase j, lam' i = ((J.erase j).card : ℚ) - Fintype.card D := by
  classical
  set k := J.card with hkdef
  set n := Fintype.card D with hn
  have hkn : (n : ℚ) < k := by exact_mod_cast hk
  set c : ℚ := ((k : ℚ) - 1 - n) / ((k : ℚ) - n) with hc
  have hc0 : 0 ≤ c := div_nonneg (by
    have : (n : ℚ) + 1 ≤ k := by exact_mod_cast hk
    linarith) (by linarith)
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by linarith)]
    linarith
  let b : Option D → ℚ := fun e => match e with
    | none => (k : ℚ) - 1 - n
    | some _ => 0
  have hb : ∑ i ∈ J, (c * lam i) • colw u i = b := by
    funext e
    cases e with
    | none =>
      rw [sum_smul_colw_none, ← Finset.mul_sum, hsum, hc]
      show _ = (k : ℚ) - 1 - n
      field_simp [show (k : ℚ) - n ≠ 0 by linarith]
    | some d =>
      rw [sum_smul_colw_some]
      show _ = 0
      simp only [mul_assoc, ← Finset.mul_sum, hs d, mul_zero]
  obtain ⟨μ, hμ0, hμ1, hμb, hμfr⟩ := exists_few_frac J (colw u) b _ (fun i => c * lam i) rfl
    (fun i hi => mul_nonneg hc0 (h0 i hi))
    (fun i hi => by have := h1 i hi; have := h0 i hi; nlinarith) hb
  have hμsum : ∑ i ∈ J, μ i = (k : ℚ) - 1 - n := by
    have := congrFun hμb none
    rwa [sum_smul_colw_none] at this
  have hμs : ∀ d, ∑ i ∈ J, μ i * (u i d : ℚ) = 0 := by
    intro d
    have := congrFun hμb (some d)
    rwa [sum_smul_colw_some] at this
  rw [Fintype.card_option] at hμfr
  -- some coordinate vanishes
  obtain ⟨j, hj, hμj⟩ : ∃ j ∈ J, μ j = 0 := by
    by_contra hno
    push_neg at hno
    have hpos : ∀ i ∈ J, 0 < μ i := fun i hi => lt_of_le_of_ne (hμ0 i hi) (hno i hi).symm
    set Fr := fracSet J μ with hFr
    have hFrJ : Fr ⊆ J := Finset.filter_subset _ _
    have hone : ∀ i ∈ J \ Fr, μ i = 1 := by
      intro i hi
      obtain ⟨hiJ, hiFr⟩ := Finset.mem_sdiff.1 hi
      by_contra hne
      exact hiFr (Finset.mem_filter.2 ⟨hiJ, hpos i hiJ, lt_of_le_of_ne (hμ1 i hiJ) hne⟩)
    have hsplit : ∑ i ∈ J, μ i = ∑ i ∈ Fr, μ i + ((J \ Fr).card : ℚ) := by
      rw [← Finset.sum_sdiff hFrJ, add_comm, Finset.sum_congr rfl hone]
      simp
    have hcard : ((J \ Fr).card : ℚ) = k - Fr.card := by
      rw [Finset.card_sdiff_of_subset hFrJ]
      push_cast [Finset.card_le_card hFrJ]
      ring
    rcases Finset.eq_empty_or_nonempty Fr with hE | hNE
    · rw [hsplit, hcard, hE] at hμsum
      simp at hμsum
      linarith
    · have : 0 < ∑ i ∈ Fr, μ i := Finset.sum_pos (fun i hi => hpos i (hFrJ hi)) hNE
      have hfr : (Fr.card : ℚ) ≤ n + 1 := by exact_mod_cast hμfr
      rw [hsplit, hcard] at hμsum
      linarith
  refine ⟨j, hj, μ, fun i hi => hμ0 i (Finset.mem_of_mem_erase hi),
    fun i hi => hμ1 i (Finset.mem_of_mem_erase hi), fun d => ?_, ?_⟩
  · rw [← hμs d, ← Finset.add_sum_erase J _ hj, hμj, zero_mul, zero_add]
  · rw [Finset.card_erase_of_mem hj]
    have hk1 : 1 ≤ k := by omega
    rw [← Finset.add_sum_erase J _ hj, hμj, zero_add] at hμsum
    rw [hμsum, ← hkdef]
    push_cast [hk1]
    ring

omit [DecidableEq α] in
/-- The bound on the full sum carried by a balancing weighting. -/
theorem abs_sum_le_of_weight (J : Finset α) (u : α → D → ℤ) (a : ℕ) (lam : α → ℚ)
    (hb : ∀ i ∈ J, ∀ d, |u i d| ≤ a) (h1 : ∀ i ∈ J, lam i ≤ 1)
    (hs : ∀ d, ∑ i ∈ J, lam i * (u i d : ℚ) = 0)
    (hsum : ∑ i ∈ J, lam i = (J.card : ℚ) - Fintype.card D) (d : D) :
    |∑ i ∈ J, u i d| ≤ Fintype.card D * a := by
  have key : ((∑ i ∈ J, u i d : ℤ) : ℚ) = ∑ i ∈ J, (1 - lam i) * (u i d : ℚ) := by
    push_cast
    have : ∑ i ∈ J, (1 - lam i) * (u i d : ℚ) =
        ∑ i ∈ J, (u i d : ℚ) - ∑ i ∈ J, lam i * (u i d : ℚ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, hs d, sub_zero]
  have hq : |((∑ i ∈ J, u i d : ℤ) : ℚ)| ≤ (Fintype.card D : ℚ) * a := by
    rw [key]
    calc |∑ i ∈ J, (1 - lam i) * (u i d : ℚ)| ≤ ∑ i ∈ J, |(1 - lam i) * (u i d : ℚ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ J, (1 - lam i) * (a : ℚ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_of_nonneg (by linarith [h1 i hi])]
          refine mul_le_mul_of_nonneg_left ?_ (by linarith [h1 i hi])
          exact_mod_cast hb i hi d
      _ = (Fintype.card D : ℚ) * a := by
          rw [← Finset.sum_mul, Finset.sum_sub_distrib, hsum]
          simp
  exact_mod_cast hq

/-- The sum over a duplicate-free list is the sum over its set of elements. -/
theorem list_sum_eq_finset_sum {β : Type*} [AddCommMonoid β] (f : α → β) {L : List α}
    (h : L.Nodup) : (L.map f).sum = ∑ i ∈ L.toFinset, f i := by
  rw [List.sum_toFinset _ h]

/-- **The Steinitz lemma**, inductive form. -/
theorem stz_aux (u : α → D → ℤ) (a : ℕ) : ∀ (k : ℕ) (J : Finset α), J.card = k →
    (∀ i ∈ J, ∀ d, |u i d| ≤ a) →
    (Fintype.card D < k → ∃ lam : α → ℚ, (∀ i ∈ J, 0 ≤ lam i) ∧ (∀ i ∈ J, lam i ≤ 1) ∧
      (∀ d, ∑ i ∈ J, lam i * (u i d : ℚ) = 0) ∧
      ∑ i ∈ J, lam i = (J.card : ℚ) - Fintype.card D) →
    ∃ L : List α, L.Nodup ∧ L.toFinset = J ∧
      ∀ m, ∀ d, |((L.take m).map (fun i => u i d)).sum| ≤ Fintype.card D * a := by
  classical
  intro k
  induction k with
  | zero =>
    intro J hJ _ _
    refine ⟨[], List.nodup_nil, by simpa using (Finset.card_eq_zero.1 hJ).symm, ?_⟩
    intro m d
    simp only [List.take_nil, List.map_nil, List.sum_nil, abs_zero]
    positivity
  | succ k ih =>
    intro J hJ hb hlam
    -- the full sum is bounded
    have hfull : ∀ d, |∑ i ∈ J, u i d| ≤ Fintype.card D * a := by
      intro d
      by_cases hk : Fintype.card D < k + 1
      · obtain ⟨lam, -, h1, hs, hsum⟩ := hlam hk
        exact abs_sum_le_of_weight J u a lam hb h1 hs hsum d
      · push_neg at hk
        calc |∑ i ∈ J, u i d| ≤ ∑ i ∈ J, |u i d| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ J, (a : ℤ) := Finset.sum_le_sum fun i hi => hb i hi d
          _ = J.card * a := by simp
          _ ≤ Fintype.card D * a := by
              rw [hJ]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
    -- remove one element
    obtain ⟨j, hj, hrest⟩ : ∃ j ∈ J, (Fintype.card D < k → ∃ lam : α → ℚ,
        (∀ i ∈ J.erase j, 0 ≤ lam i) ∧ (∀ i ∈ J.erase j, lam i ≤ 1) ∧
        (∀ d, ∑ i ∈ J.erase j, lam i * (u i d : ℚ) = 0) ∧
        ∑ i ∈ J.erase j, lam i = ((J.erase j).card : ℚ) - Fintype.card D) := by
      by_cases hk : Fintype.card D < k + 1
      · obtain ⟨lam, h0, h1, hs, hsum⟩ := hlam hk
        obtain ⟨j, hj, lam', h0', h1', hs', hsum'⟩ :=
          stz_step J u lam (by omega) h0 h1 hs hsum
        exact ⟨j, hj, fun _ => ⟨lam', h0', h1', hs', hsum'⟩⟩
      · have hne : J.Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨j, hj⟩ := hne
        exact ⟨j, hj, fun h => by omega⟩
    obtain ⟨L', hnd', hset', hpre'⟩ := ih (J.erase j) (by rw [Finset.card_erase_of_mem hj]; omega)
      (fun i hi => hb i (Finset.mem_of_mem_erase hi)) hrest
    have hjL' : j ∉ L' := by
      intro h
      have : j ∈ L'.toFinset := List.mem_toFinset.2 h
      rw [hset'] at this
      simp at this
    have hlen' : L'.length = k := by
      rw [← List.toFinset_card_of_nodup hnd', hset', Finset.card_erase_of_mem hj]
      omega
    refine ⟨L' ++ [j], ?_, ?_, ?_⟩
    · exact List.nodup_append.2 ⟨hnd', List.nodup_singleton j, by simpa using fun x hx (h : x = j) => hjL' (h ▸ hx)⟩
    · rw [List.toFinset_append, hset']
      simp [Finset.insert_erase hj]
    · intro m d
      by_cases hm : m ≤ k
      · rw [List.take_append_of_le_length (by omega)]
        exact hpre' m d
      · push_neg at hm
        rw [List.take_of_length_le (by simp; omega)]
        have hnd : (L' ++ [j]).Nodup :=
          List.nodup_append.2 ⟨hnd', List.nodup_singleton j, by simpa using fun x hx (h : x = j) => hjL' (h ▸ hx)⟩
        rw [list_sum_eq_finset_sum (fun i => u i d) hnd]
        have : (L' ++ [j]).toFinset = J := by
          rw [List.toFinset_append, hset']
          simp [Finset.insert_erase hj]
        rw [this]
        exact hfull d

/-- **The Steinitz lemma** (Grinberg–Sevastyanov form): a zero-sum family of integer vectors
of `ℤ^D` with entries in `[-a, a]` can be listed so that every prefix sum has entries in
`[-|D|·a, |D|·a]`. -/
theorem steinitz (J : Finset α) (u : α → D → ℤ) (a : ℕ) (hb : ∀ i ∈ J, ∀ d, |u i d| ≤ a)
    (hz : ∀ d, ∑ i ∈ J, u i d = 0) :
    ∃ L : List α, L.Nodup ∧ L.toFinset = J ∧
      ∀ m, ∀ d, |((L.take m).map (fun i => u i d)).sum| ≤ Fintype.card D * a := by
  refine stz_aux u a J.card J rfl hb fun hk => ?_
  have hJ : (0 : ℚ) < J.card := by exact_mod_cast (show 0 < J.card by omega)
  refine ⟨fun _ => ((J.card : ℚ) - Fintype.card D) / J.card, fun i _ => ?_, fun i _ => ?_,
    fun d => ?_, ?_⟩
  · have : (Fintype.card D : ℚ) < J.card := by exact_mod_cast hk
    exact div_nonneg (by linarith) hJ.le
  · rw [div_le_one hJ]
    have : (0 : ℚ) ≤ Fintype.card D := by positivity
    linarith
  · rw [← Finset.mul_sum]
    have : ∑ i ∈ J, (u i d : ℚ) = 0 := by exact_mod_cast hz d
    rw [this, mul_zero]
  · rw [Finset.sum_const, nsmul_eq_mul]
    field_simp

/-! ### The zero-sum lemma -/

/-- **The single-exponential zero-sum bound.** -/
def zsP (n a : ℕ) : ℕ := (2 * n * a + 1) ^ n

/-- **Proper zero-sum subsets**, index form: a zero-sum set of more than `zsP |D| a` vectors with
entries in `[-a, a]` has a proper nonempty zero-sum subset. -/
theorem exists_proper_zero_sum_finset (J : Finset α) (u : α → D → ℤ) (a : ℕ)
    (hb : ∀ i ∈ J, ∀ d, |u i d| ≤ a) (hz : ∀ d, ∑ i ∈ J, u i d = 0)
    (hc : zsP (Fintype.card D) a < J.card) :
    ∃ K ⊆ J, K.Nonempty ∧ K ≠ J ∧ ∀ d, ∑ i ∈ K, u i d = 0 := by
  classical
  obtain ⟨L, hnd, hset, hpre⟩ := steinitz J u a hb hz
  have hlen : L.length = J.card := by rw [← List.toFinset_card_of_nodup hnd, hset]
  set B : ℤ := Fintype.card D * a with hB
  let P : ℕ → D → ℤ := fun m d => ((L.take m).map (fun i => u i d)).sum
  let box : Finset (D → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-B) B
  have hmaps : ∀ m ∈ Finset.range J.card, P m ∈ box := by
    intro m _
    refine Fintype.mem_piFinset.2 fun d => Finset.mem_Icc.2 ?_
    have := hpre m d
    rw [abs_le] at this
    exact this
  have hboxcard : box.card = zsP (Fintype.card D) a := by
    simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, zsP]
    congr 1
    rw [hB, show (Fintype.card D : ℤ) * a = ((Fintype.card D * a : ℕ) : ℤ) by push_cast; ring,
      mul_assoc]
    omega
  obtain ⟨m₁, hm₁, m₂, hm₂, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := box) (show box.card < (Finset.range J.card).card by
      rw [hboxcard, Finset.card_range]; exact hc) (f := P) (fun m hm => hmaps m hm)
  -- order the two indices
  have main : ∀ i j, i < j → j < J.card → P i = P j →
      ∃ K ⊆ J, K.Nonempty ∧ K ≠ J ∧ ∀ d, ∑ i ∈ K, u i d = 0 := by
    intro i j hij hj hP
    let M := (L.drop i).take (j - i)
    have hMsub : M.Sublist L := (List.take_sublist _ _).trans (List.drop_sublist _ _)
    have hMnd : M.Nodup := hMsub.nodup hnd
    have hMlen : M.length = j - i := by simp [M, hlen]; omega
    refine ⟨M.toFinset, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [← hset]
      exact List.mem_toFinset.2 (hMsub.subset (List.mem_toFinset.1 hx))
    · refine ⟨M.head (List.ne_nil_of_length_pos (by omega)), List.mem_toFinset.2 (List.head_mem _)⟩
    · intro hEq
      have : M.toFinset.card = J.card := by rw [hEq]
      rw [List.toFinset_card_of_nodup hMnd, hMlen] at this
      omega
    · intro d
      rw [← list_sum_eq_finset_sum (fun i => u i d) hMnd]
      have hsplit : L.take j = L.take i ++ M := by
        simp only [M]
        have e : j = i + (j - i) := by omega
        conv_lhs => rw [e]
        rw [List.take_add]
      have := congrFun hP d
      simp only [P, hsplit, List.map_append, List.sum_append] at this
      omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact main m₁ m₂ h (Finset.mem_range.1 hm₂) heq
  · exact main m₂ m₁ h (Finset.mem_range.1 hm₁) heq.symm

end Stz

/-! ### Multiset form -/

open Multiset in
/-- **The single-exponential zero-sum lemma.**  Let `g` map a family `S` to integer vectors
supported on the finite coordinate set `A`, with entries in `[-a, a]`, summing to zero.  If `S`
has more than `zsP |A| a` members, it has a proper nonempty subfamily that also sums to zero. -/
theorem exists_proper_zero_sum (A : Finset ℕ) (a : ℕ) {β : Type} (S : Multiset β)
    (g : β → ℕ → ℤ) (hsupp : ∀ x ∈ S, ∀ i, i ∉ A → g x i = 0) (hb : ∀ x ∈ S, ∀ i, |g x i| ≤ a)
    (hs : (S.map g).sum = 0) (hc : zsP A.card a < card S) :
    ∃ T ≤ S, T ≠ 0 ∧ T ≠ S ∧ (T.map g).sum = 0 := by
  classical
  set l := S.toList with hl
  have hS : (l : Multiset β) = S := Multiset.coe_toList S
  let u : Fin l.length → A → ℤ := fun i d => g (l.get i) d
  have hmemS : ∀ i : Fin l.length, l.get i ∈ S := fun i => by
    rw [← hS]; exact Multiset.mem_coe.2 (List.get_mem _ _)
  have hmapS : (Finset.univ.val.map fun i : Fin l.length => l.get i) = S := by
    rw [← hS]
    have : (Finset.univ.val.map fun i : Fin l.length => l.get i) = ((List.finRange l.length).map
        fun i => l.get i : List β) := by
      rw [← Multiset.map_coe]
      congr 1
    rw [this, List.map_get_finRange]
  have hsumcoord : ∀ (K : Finset (Fin l.length)) (i : ℕ),
      ((K.val.map fun j => l.get j).map g).sum i = ∑ j ∈ K, g (l.get j) i := by
    intro K i
    rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum, Finset.sum_apply]
    rfl
  have hz : ∀ d : A, ∑ j ∈ (Finset.univ : Finset (Fin l.length)), u j d = 0 := by
    intro d
    have := congrFun hs d
    rw [← hmapS, hsumcoord] at this
    exact this
  have hcard : zsP (Fintype.card A) a < (Finset.univ : Finset (Fin l.length)).card := by
    rw [Fintype.card_coe, Finset.card_univ, Fintype.card_fin, Multiset.length_toList]
    exact hc
  obtain ⟨K, -, hKne, hKJ, hKz⟩ := exists_proper_zero_sum_finset Finset.univ u a
    (fun j _ d => hb _ (hmemS j) d) hz hcard
  refine ⟨K.val.map fun j => l.get j, ?_, ?_, ?_, ?_⟩
  · rw [← hmapS]
    exact Multiset.map_le_map (Finset.val_le_iff.2 (Finset.subset_univ K))
  · simpa using hKne.ne_empty
  · intro h
    have h1 : card (K.val.map fun j => l.get j) = K.card := by simp
    rw [h] at h1
    have h2 : K.card < (Finset.univ : Finset (Fin l.length)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ K, hKJ⟩)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have : l.length = card S := Multiset.length_toList S
    omega
  · funext i
    rw [hsumcoord]
    by_cases hi : i ∈ A
    · exact hKz ⟨i, hi⟩
    · simp only [Pi.zero_apply]
      exact Finset.sum_eq_zero fun j _ => hsupp _ (hmemS j) i hi

open Multiset in
/-- **Small zero-sum subfamilies through a prescribed member**, with the single-exponential
bound. -/
theorem exists_small_zero_sum_mem (A : Finset ℕ) (a : ℕ) {β : Type} (g : β → ℕ → ℤ) (x₀ : β) :
    ∀ (n : ℕ) (S : Multiset β), card S = n → x₀ ∈ S →
      (∀ x ∈ S, ∀ i, i ∉ A → g x i = 0) → (∀ x ∈ S, ∀ i, |g x i| ≤ a) →
      (S.map g).sum = 0 →
      ∃ T ≤ S, x₀ ∈ T ∧ card T ≤ zsP A.card a ∧ (T.map g).sum = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hx₀ hsupp hb hs
    by_cases hsmall : card S ≤ zsP A.card a
    · exact ⟨S, le_rfl, hx₀, hsmall, hs⟩
    push_neg at hsmall
    obtain ⟨T, hT, hT0, hTS, hTs⟩ := exists_proper_zero_sum A a S g hsupp hb hs hsmall
    obtain ⟨U, rfl⟩ := Multiset.le_iff_exists_add.1 hT
    have hU0 : U ≠ 0 := by
      rintro rfl
      exact hTS (by simp)
    have hUs : (U.map g).sum = 0 := by
      rw [Multiset.map_add, Multiset.sum_add, hTs, zero_add] at hs
      exact hs
    have hTc : card T < n := by
      rw [← hn, Multiset.card_add]
      have : 0 < card U := Multiset.card_pos.2 hU0
      omega
    have hUc : card U < n := by
      rw [← hn, Multiset.card_add]
      have : 0 < card T := Multiset.card_pos.2 hT0
      omega
    rcases Multiset.mem_add.1 hx₀ with h | h
    · obtain ⟨T', hT', h1, h2, h3⟩ := ih _ hTc T rfl h
        (fun x hx => hsupp x (Multiset.mem_add.2 (Or.inl hx)))
        (fun x hx => hb x (Multiset.mem_add.2 (Or.inl hx))) hTs
      exact ⟨T', hT'.trans (Multiset.le_add_right _ _), h1, h2, h3⟩
    · obtain ⟨T', hT', h1, h2, h3⟩ := ih _ hUc U rfl h
        (fun x hx => hsupp x (Multiset.mem_add.2 (Or.inr hx)))
        (fun x hx => hb x (Multiset.mem_add.2 (Or.inr hx))) hUs
      exact ⟨T', hT'.trans (Multiset.le_add_left _ _), h1, h2, h3⟩

end Steinitz

end HTN
