import HtnComplexity.Article.TOHardSound
/-!
# The tableau-checking problem: completeness, and plan existence

* `HTN.Article.TabData.refT_chk` — from every state `(t, i)` the check of the code of the entry
  `(t, i)` has a refinement that restores the state (induction on `t`);
* **`HTN.Article.TabData.solvable_iff`** — the problem has a solution iff some cell `i < 2 ^ B`
  holds an accepting entry at time `2 ^ B - 1`.
-/

namespace HTN

namespace Article

open Syn PTime

namespace TabData

variable {d : TabData} {tabC : ℕ → ℕ → ℕ}

/-- A method whose labels refine one after the other refines its name. -/
theorem refT_meth {c : ℕ} {body : List (Bool × ℕ)} (he : meth c body ∈ d.methods) {s s' : Set ℕ}
    (h : ChainL (RefT d.desc) (body.map toLab) s s') : RefT d.desc (Sum.inr c) s s' :=
  refT_of_chain (p := d.desc) (e := meth c body) he (seqTn_isTO body)
    (chainT_iff_chainR.2 (chainR_seqTn_iff.2 h))

theorem mem_ctr' {j : ℕ} (hj : j < d.B) {e : MethodDesc}
    (h : e = meth (cIncT j) [(false, setN (tF j))] ∨
      e = meth (cIncT j) [(false, clrN (tF j)), (true, cIncT (j + 1))] ∨
      e = meth (cDecT j) [(false, clrN (tF j))] ∨
      e = meth (cDecT j) [(false, setN (tF j)), (true, cDecT (j + 1))] ∨
      e = meth (cIncI j) [(false, setN (iF j))] ∨
      e = meth (cIncI j) [(false, clrN (iF j)), (true, cIncI (j + 1))] ∨
      e = meth (cDecI j) [(false, clrN (iF j))] ∨
      e = meth (cDecI j) [(false, setN (iF j)), (true, cDecI (j + 1))] ∨
      e = meth (cGuess j) [(false, noopN)] ∨
      e = meth (cGuess j) [(false, setN (iF j))]) : e ∈ d.methods :=
  (d.mem_methods).2 (Or.inl ⟨j, hj, h⟩)

theorem lt_of_two_pow_lt {j B t : ℕ} (h : t + 2 ^ j < 2 ^ B) : j < B := by
  by_contra hn
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show B ≤ j by omega)
  omega

/-! ### The counters -/

theorem refT_incT : ∀ n j, d.B - j = n → ∀ t i, t + 2 ^ j < 2 ^ d.B →
    RefT d.desc (Sum.inr (cIncT j)) (cntS d.B t i) (cntS d.B (t + 2 ^ j) i) := by
  intro n
  induction n with
  | zero => intro j hn t i h; exact absurd (lt_of_two_pow_lt h) (by omega)
  | succ n ih =>
    intro j hn t i h
    have hj := lt_of_two_pow_lt h
    rcases hb : t.testBit j
    · refine refT_meth (mem_ctr' hj (Or.inl rfl)) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false]
      exact .cons ((d.refT_setT hj).2 ⟨hb, rfl⟩) (.nil _)
    · have hge := Nat.ge_two_pow_of_testBit hb
      refine refT_meth (mem_ctr' hj (Or.inr (Or.inl rfl))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false, if_true]
      refine .cons ((d.refT_clrT hj).2 ⟨hb, rfl⟩) (.cons ?_ (.nil _))
      have := ih (j + 1) (by omega) (t - 2 ^ j) i (by rw [two_pow_succ_sub hge]; exact h)
      rwa [two_pow_succ_sub hge] at this

theorem refT_decT : ∀ n j, d.B - j = n → ∀ t i, t < 2 ^ d.B → 2 ^ j ≤ t →
    RefT d.desc (Sum.inr (cDecT j)) (cntS d.B t i) (cntS d.B (t - 2 ^ j) i) := by
  intro n
  induction n with
  | zero =>
    intro j hn t i ht h
    exact absurd (lt_of_two_pow_lt (t := 0) (j := j) (B := d.B) (by omega)) (by omega)
  | succ n ih =>
    intro j hn t i ht h
    have hj : j < d.B := lt_of_two_pow_lt (t := 0) (by omega)
    rcases hb : t.testBit j
    · refine refT_meth (mem_ctr' hj (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false, if_true]
      refine .cons ((d.refT_setT hj).2 ⟨hb, rfl⟩) (.cons ?_ (.nil _))
      have := ih (j + 1) (by omega) (t + 2 ^ j) i (add_two_pow_lt ht hj hb)
        (show 2 ^ (j + 1) ≤ t + 2 ^ j by rw [pow_succ]; omega)
      rwa [pow_succ, show t + 2 ^ j - 2 ^ j * 2 = t - 2 ^ j by omega] at this
    · refine refT_meth (mem_ctr' hj (Or.inr (Or.inr (Or.inl rfl)))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false]
      exact .cons ((d.refT_clrT hj).2 ⟨hb, rfl⟩) (.nil _)

theorem refT_incI : ∀ n j, d.B - j = n → ∀ t i, i + 2 ^ j < 2 ^ d.B →
    RefT d.desc (Sum.inr (cIncI j)) (cntS d.B t i) (cntS d.B t (i + 2 ^ j)) := by
  intro n
  induction n with
  | zero => intro j hn t i h; exact absurd (lt_of_two_pow_lt h) (by omega)
  | succ n ih =>
    intro j hn t i h
    have hj := lt_of_two_pow_lt h
    rcases hb : i.testBit j
    · refine refT_meth (mem_ctr' hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false]
      exact .cons ((d.refT_setI hj).2 ⟨hb, rfl⟩) (.nil _)
    · have hge := Nat.ge_two_pow_of_testBit hb
      refine refT_meth (mem_ctr' hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false, if_true]
      refine .cons ((d.refT_clrI hj).2 ⟨hb, rfl⟩) (.cons ?_ (.nil _))
      have := ih (j + 1) (by omega) t (i - 2 ^ j) (by rw [two_pow_succ_sub hge]; exact h)
      rwa [two_pow_succ_sub hge] at this

theorem refT_decI : ∀ n j, d.B - j = n → ∀ t i, i < 2 ^ d.B → 2 ^ j ≤ i →
    RefT d.desc (Sum.inr (cDecI j)) (cntS d.B t i) (cntS d.B t (i - 2 ^ j)) := by
  intro n
  induction n with
  | zero =>
    intro j hn t i hi h
    exact absurd (lt_of_two_pow_lt (t := 0) (j := j) (B := d.B) (by omega)) (by omega)
  | succ n ih =>
    intro j hn t i hi h
    have hj : j < d.B := lt_of_two_pow_lt (t := 0) (by omega)
    rcases hb : i.testBit j
    · refine refT_meth (mem_ctr' hj
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false, if_true]
      refine .cons ((d.refT_setI hj).2 ⟨hb, rfl⟩) (.cons ?_ (.nil _))
      have := ih (j + 1) (by omega) t (i + 2 ^ j) (add_two_pow_lt hi hj hb)
        (show 2 ^ (j + 1) ≤ i + 2 ^ j by rw [pow_succ]; omega)
      rwa [pow_succ, show i + 2 ^ j - 2 ^ j * 2 = i - 2 ^ j by omega] at this
    · refine refT_meth (mem_ctr' hj
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false]
      exact .cons ((d.refT_clrI hj).2 ⟨hb, rfl⟩) (.nil _)

theorem incT0 {t i : ℕ} (h : t + 1 < 2 ^ d.B) :
    RefT d.desc (Sum.inr (cIncT 0)) (cntS d.B t i) (cntS d.B (t + 1) i) := by
  have := refT_incT (d := d) _ 0 rfl t i (by simpa using h)
  simpa using this

theorem decT0 {t i : ℕ} (h : t < 2 ^ d.B) (h1 : 1 ≤ t) :
    RefT d.desc (Sum.inr (cDecT 0)) (cntS d.B t i) (cntS d.B (t - 1) i) := by
  have := refT_decT (d := d) _ 0 rfl t i h (by simpa using h1)
  simpa using this

theorem incI0 {t i : ℕ} (h : i + 1 < 2 ^ d.B) :
    RefT d.desc (Sum.inr (cIncI 0)) (cntS d.B t i) (cntS d.B t (i + 1)) := by
  have := refT_incI (d := d) _ 0 rfl t i (by simpa using h)
  simpa using this

theorem decI0 {t i : ℕ} (h : i < 2 ^ d.B) (h1 : 1 ≤ i) :
    RefT d.desc (Sum.inr (cDecI 0)) (cntS d.B t i) (cntS d.B t (i - 1)) := by
  have := refT_decI (d := d) _ 0 rfl t i h (by simpa using h1)
  simpa using this

/-! ### The checks -/

theorem mem_geNames {B c i : ℕ} {gN : ℕ → ℕ} (hc : c < 2 ^ B) (hi : i < 2 ^ B) (h : c ≤ i) :
    ∃ X ∈ geNames B c gN, X = eqN c ∧ i = c ∨
      ∃ j < B, X = gN j ∧ i.testBit j = true ∧ ∀ m, j < m → m < B → i.testBit m = c.testBit m := by
  rcases h.lt_or_eq with h | rfl
  · obtain ⟨j, hj, hcj, hij, hab⟩ := (lt_iff_testBit hc hi).1 h
    refine ⟨gN j, ?_, Or.inr ⟨j, hj, rfl, hij, hab⟩⟩
    simp only [geNames, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range, bit_eq]
    exact Or.inr ⟨j, ⟨hj, by simp [hcj]⟩, rfl⟩
  · exact ⟨eqN c, by simp [geNames], Or.inl ⟨rfl, rfl⟩⟩

/-- **Completeness**: the check of the entry `(t, i)` refines from the state `(t, i)` back to it. -/
theorem refT_chk (hg : Good d tabC) : ∀ t, t < 2 ^ d.B → ∀ i, i < 2 ^ d.B →
    RefT d.desc (Sum.inr (cChk (tabC t i))) (cntS d.B t i) (cntS d.B t i) := by
  have hB := hg.hB
  have hmx := hg.hmx
  have h2B : 2 ≤ 2 ^ d.B := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d.B := Nat.pow_le_pow_right (by norm_num) hB
  have hc₂ := hg.hc₂
  have hc₁₂ := hg.hc₁₂
  intro t
  induction t with
  | zero =>
    intro _ i hi
    by_cases h1 : i < d.c₁
    · rw [hg.base i h1]
      refine refT_meth ((d.mem_methods).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨i, h1, rfl⟩)))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false]
      exact .cons ((d.refT_tz (Nat.two_pow_pos _)).2 ⟨rfl, rfl⟩)
        (.cons ((d.refT_eq (by omega) hi (Or.inl h1)).2 ⟨rfl, rfl⟩) (.nil _))
    by_cases h2 : i < d.c₂
    · rw [hg.tru i (by omega) h2]
      obtain ⟨X, hX, hXc⟩ := mem_geNames (gN := gt1N) (B := d.B) (by omega) hi (show d.c₁ ≤ i by omega)
      obtain ⟨j, hj, hij, hcj, hab⟩ := (lt_iff_testBit hi hc₂).1 h2
      have hY : lt2N j ∈ ltNames d.B d.c₂ := by
        simp only [ltNames, List.mem_map, List.mem_filter, List.mem_range, bit_eq]
        exact ⟨j, ⟨hj, hcj⟩, rfl⟩
      refine refT_meth ((d.mem_methods).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨X, hX, _, hY, rfl⟩))))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false]
      refine .cons ((d.refT_tz (Nat.two_pow_pos _)).2 ⟨rfl, rfl⟩) (.cons ?_
        (.cons ((d.refT_lt2 hj).2 ⟨⟨hij, fun m h1 h2 => (hab m h1 h2).symm⟩, rfl⟩) (.nil _)))
      rcases hXc with ⟨rfl, rfl⟩ | ⟨j', hj', rfl, hij', hab'⟩
      · exact (d.refT_eq (by omega) hi (Or.inr (Or.inl rfl))).2 ⟨rfl, rfl⟩
      · exact (d.refT_gt1 hj').2 ⟨⟨hij', hab'⟩, rfl⟩
    · rw [hg.non i (by omega) hi]
      obtain ⟨X, hX, hXc⟩ := mem_geNames (gN := gt2N) (B := d.B) hc₂ hi (show d.c₂ ≤ i by omega)
      refine refT_meth ((d.mem_methods).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨X, hX, rfl⟩)))))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false]
      refine .cons ((d.refT_tz (Nat.two_pow_pos _)).2 ⟨rfl, rfl⟩) (.cons ?_ (.nil _))
      rcases hXc with ⟨rfl, rfl⟩ | ⟨j', hj', rfl, hij', hab'⟩
      · exact (d.refT_eq hc₂ hi (Or.inr (Or.inr (Or.inl rfl)))).2 ⟨rfl, rfl⟩
      · exact (d.refT_gt2 hj').2 ⟨⟨hij', hab'⟩, rfl⟩
  | succ t ih =>
    intro ht i hi
    have ht' : t < 2 ^ d.B := by omega
    by_cases h0 : i = 0
    · subst h0
      have hq := hg.lft_c t ht
      refine refT_meth ((d.mem_methods).2 (Or.inr (Or.inr (Or.inl ⟨_, hq, rfl⟩)))) ?_
      simp only [lftBody, List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
        if_true]
      refine .cons ((d.refT_eq (Nat.two_pow_pos _) hi (Or.inl hg.hc₁)).2 ⟨rfl, rfl⟩) ?_
      refine .cons (by simpa using decT0 (d := d) (i := 0) ht (by omega)) ?_
      refine .cons (ih ht' 0 hi) ?_
      refine .cons (incI0 (by omega)) ?_
      refine .cons (ih ht' 1 (by omega)) ?_
      refine .cons (by simpa using decI0 (d := d) (t := t) (i := 1) (by omega) le_rfl) ?_
      exact .cons (incT0 ht) (.nil _)
    by_cases hm : i = d.mx
    · subst hm
      have hq := hg.rgt_c t ht
      refine refT_meth ((d.mem_methods).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hq, rfl⟩))))) ?_
      simp only [rgtBody, List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
        if_true]
      refine .cons ((d.refT_eq hi hi (Or.inr (Or.inr (Or.inr rfl)))).2 ⟨rfl, rfl⟩) ?_
      refine .cons (by simpa using decT0 (d := d) (i := d.mx) ht (by omega)) ?_
      refine .cons (decI0 hi (by omega)) ?_
      refine .cons (ih ht' (d.mx - 1) (by omega)) ?_
      refine .cons (s₁ := cntS d.B t d.mx) ?_ ?_
      · have := incI0 (d := d) (t := t) (i := d.mx - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ d.mx)] at this
      refine .cons (ih ht' d.mx hi) ?_
      exact .cons (incT0 ht) (.nil _)
    · have hi1 : i + 1 < 2 ^ d.B := by omega
      have hq := hg.mid_c t i (by omega) hi1 ht
      refine refT_meth ((d.mem_methods).2 (Or.inr (Or.inl ⟨_, hq, rfl⟩))) ?_
      simp only [midBody, List.map_cons, List.map_nil, toLab, if_true]
      refine .cons (by simpa using decT0 (d := d) (i := i) ht (by omega)) ?_
      refine .cons (decI0 hi (by omega)) ?_
      refine .cons (ih ht' (i - 1) (by omega)) ?_
      refine .cons (s₁ := cntS d.B t i) ?_ ?_
      · have := incI0 (d := d) (t := t) (i := i - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at this
      refine .cons (ih ht' i hi) ?_
      refine .cons (incI0 hi1) ?_
      refine .cons (ih ht' (i + 1) hi1) ?_
      refine .cons (by simpa using decI0 (d := d) (t := t) (i := i + 1) hi1 (by omega)) ?_
      exact .cons (incT0 ht) (.nil _)

/-! ### Guessing the cell -/

theorem mod_two_pow_succ_eq (i j : ℕ) :
    i % 2 ^ (j + 1) = i % 2 ^ j + if i.testBit j then 2 ^ j else 0 := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with h | h <;> simp [h]

theorem guesses_complete (hT : T < 2 ^ d.B) (i : ℕ) : ∀ j ≤ d.B,
    ChainL (RefT d.desc) ((List.range j).map fun j => Sum.inr (cGuess j)) (cntS d.B T 0)
      (cntS d.B T (i % 2 ^ j)) := by
  intro j
  induction j with
  | zero => intro _; rw [pow_zero, Nat.mod_one]; exact .nil _
  | succ j ih =>
    intro hj
    rw [List.range_succ, List.map_append, chainL_append_iff]
    refine ⟨_, ih (by omega), .cons ?_ (.nil _)⟩
    rw [mod_two_pow_succ_eq]
    have hlt : i % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos _)
    rcases hb : i.testBit j
    · refine refT_meth (mem_ctr' (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl rfl)))))))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false, add_zero]
      exact .cons ((d.refT_noop).2 rfl) (.nil _)
    · refine refT_meth (mem_ctr' (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr rfl)))))))))) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false, if_true]
      exact .cons ((d.refT_setI (by omega)).2 ⟨Nat.testBit_lt_two_pow hlt, rfl⟩) (.nil _)

theorem guesses_sound (hg : Good d tabC) {T : ℕ} : ∀ j ≤ d.B, ∀ {s : Set ℕ},
    ChainL (RefT d.desc) ((List.range j).map fun j => Sum.inr (cGuess j)) (cntS d.B T 0) s →
      ∃ i < 2 ^ j, s = cntS d.B T i := by
  intro j
  induction j with
  | zero => intro _ s h; rw [List.range_zero, List.map_nil, chainL_nil_iff] at h; exact ⟨0, by simp, h⟩
  | succ j ih =>
    intro hj s h
    rw [List.range_succ, List.map_append, chainL_append_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    obtain ⟨i, hi, rfl⟩ := ih (by omega) h₁
    rw [List.map_cons, List.map_nil, chainL_cons_iff] at h₂
    obtain ⟨s₂, h₃, h₄⟩ := h₂
    rw [chainL_nil_iff] at h₄
    subst h₄
    exact sem_guess (sem_of_refT hg h₃) hi (by omega) rfl

/-! ### Plan existence -/

theorem init_eq (hg : Good d tabC) : d.desc.toProblem.init = cntS d.B d.mx 0 := by
  ext f
  show f ∈ (List.range d.B).map tF ↔ _
  rw [hg.hmx]
  rcases tF_or_iF f with hf | hf <;> rw [hf]
  · rw [mem_cntS_tF, Nat.testBit_two_pow_sub_one]
    simp only [List.mem_map, List.mem_range, decide_eq_true_eq]
    exact ⟨fun ⟨j, hj, e⟩ => by rw [← tF_inj e]; exact ⟨hj, hj⟩, fun ⟨h, _⟩ => ⟨_, h, rfl⟩⟩
  · rw [mem_cntS_iF]
    simp only [List.mem_map, List.mem_range, Nat.zero_testBit, Bool.false_eq_true, and_false,
      iff_false, not_exists, not_and]
    exact fun j _ e => tF_ne_iF _ _ e

theorem cN_inj {k p k' p' : ℕ} (hk : k < 8) (hk' : k' < 8) (h : cN k p = cN k' p') :
    k = k' ∧ p = p' := by
  unfold cN at h; omega

/-- The methods of the root. -/
theorem root_methods {e : MethodDesc} (he : e ∈ d.methods) (h : e.1 = rootN) :
    ∃ a ∈ d.acc, e = meth rootN (rootBody d.B a) := by
  have nr : ∀ k p, k < 6 → cN k p ≠ rootN := fun k p hk e => by
    have := (cN_inj (by omega) (by norm_num) e).1; omega
  rcases (d.mem_methods).1 he with ⟨j, -, hh⟩ | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ |
      ⟨c, -, rfl⟩ | ⟨X, -, Y, -, rfl⟩ | ⟨X, -, rfl⟩ | ⟨a, ha, rfl⟩
  · rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact absurd h (nr _ _ (by norm_num))
  all_goals first
    | exact absurd h (nr 5 _ (by norm_num))
    | exact ⟨a, ha, rfl⟩

/-- **Plan existence**: the problem has a solution iff some cell holds an accepting entry at time
`2 ^ B - 1`. -/
theorem solvable_iff (hg : Good d tabC) :
    d.desc.toProblem.Solvable ↔ ∃ i < 2 ^ d.B, tabC d.mx i ∈ d.acc := by
  have hv := d.desc_valid (by have := hg.hc₁; omega)
  have hmx := hg.hmx
  have hmxB : d.mx < 2 ^ d.B := by have := Nat.two_pow_pos d.B; omega
  rw [solvable_iff_chain hv (seqTn_isTO _)]
  have hgoal : ∀ s, d.desc.toProblem.GoalState s := fun s =>
    ⟨fun f hf => absurd hf (by simp [ProbDesc.toProblem, TabData.desc, ProbDesc.goalPos]),
      Set.disjoint_left.2 fun f hf => absurd hf (by simp [ProbDesc.toProblem, TabData.desc,
        ProbDesc.goalNeg])⟩
  have htnI : d.desc.tnI = seqTn [(true, rootN)] := rfl
  rw [init_eq hg]
  simp only [htnI, chainT_iff_chainR, chainR_seqTn_iff, List.map_cons, List.map_nil, toLab, if_true,
    chainL_cons_iff, chainL_nil_iff]
  constructor
  · rintro ⟨s', ⟨s₁, hr, rfl⟩, -⟩
    obtain ⟨e, he, he1, hch⟩ := chain_of_refT hr fun e he _ => d.methods_isTO he
    obtain ⟨a, ha, rfl⟩ := root_methods he he1
    rw [chainT_iff_chainR] at hch
    have hch' := chainR_seqTn_iff.1 hch
    rw [rootBody, List.map_append, List.map_map, chainL_append_iff] at hch'
    clear hch
    have hch := hch'
    obtain ⟨s₂, hgs, hc⟩ := hch
    have hgs' : ChainL (RefT d.desc) ((List.range d.B).map fun j => Sum.inr (cGuess j))
        (cntS d.B d.mx 0) s₂ := by
      simpa [Function.comp_def, toLab] using hgs
    obtain ⟨i, hi, rfl⟩ := guesses_sound hg d.B le_rfl hgs'
    simp only [List.map_cons, List.map_nil, toLab, if_true, chainL_cons_iff, chainL_nil_iff] at hc
    obtain ⟨s₃, hr₃, rfl⟩ := hc
    obtain ⟨-, hta⟩ := sem_chk (sem_of_refT hg hr₃) hmxB hi rfl
    exact ⟨i, hi, hta ▸ ha⟩
  · rintro ⟨i, hi, ha⟩
    refine ⟨_, ⟨cntS d.B d.mx i, ?_, rfl⟩, hgoal _⟩
    refine refT_meth ((d.mem_methods).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨_, ha, rfl⟩)))))))) ?_
    rw [rootBody, List.map_append, chainL_append_iff]
    refine ⟨cntS d.B d.mx i, ?_, ?_⟩
    · have := guesses_complete (d := d) hmxB i d.B le_rfl
      rw [Nat.mod_eq_of_lt hi] at this
      simpa [Function.comp_def, toLab] using this
    · simp only [List.map_cons, List.map_nil, toLab, if_true]
      exact .cons (refT_chk hg d.mx hmxB i hi) (.nil _)

end TabData

end Article

end HTN
