import HtnComplexity.Article.TOInd
/-!
# Binary counters in states

Two `B`-bit counters `t` and `i` are kept in a state as the facts `2 j` (bit `j` of `t`) and
`2 j + 1` (bit `j` of `i`) (`HTN.Article.cntS`).  This file has the arithmetic of the bits:

* `HTN.Article.testBit_add_two_pow`, `HTN.Article.testBit_sub_two_pow` — setting and clearing a
  bit adds and subtracts its power of two;
* `HTN.Article.lt_iff_testBit` — comparison with a constant through the highest differing bit;
* `HTN.Article.cntS_inj` — the state determines the counters;
* `HTN.Article.getI_bitsOfNat` — the binary digits of `HTN.PTime.bitsOfNat` are the bits.
-/

namespace HTN

namespace Article

open PTime

theorem testBit_add_two_pow : ∀ {j t : ℕ}, t.testBit j = false → ∀ m,
    (t + 2 ^ j).testBit m = (decide (m = j) || t.testBit m) := by
  intro j
  induction j with
  | zero =>
    intro t h m
    rw [Nat.testBit_zero] at h
    have h2 : t % 2 = 0 := by simpa using h
    cases m with
    | zero => simp; omega
    | succ m =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one, show (t + 2 ^ 0) / 2 = t / 2 by simp; omega]
      simp
  | succ j ih =>
    intro t h m
    rw [Nat.testBit_add_one] at h
    cases m with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_zero, pow_succ]
      simp only [Nat.add_mul_mod_self_right, Bool.false_or, show (0 = j + 1) = False by simp,
        decide_false]
    | succ m =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one, show (t + 2 ^ (j + 1)) / 2 = t / 2 + 2 ^ j by
        rw [pow_succ]; omega, ih h m]
      simp

theorem testBit_sub_two_pow : ∀ {j t : ℕ}, t.testBit j = true → ∀ m,
    (t - 2 ^ j).testBit m = (decide (m ≠ j) && t.testBit m) := by
  intro j
  induction j with
  | zero =>
    intro t h m
    rw [Nat.testBit_zero] at h
    have h2 : t % 2 = 1 := by simpa using h
    cases m with
    | zero => simp; omega
    | succ m =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one, show (t - 2 ^ 0) / 2 = t / 2 by simp; omega]
      simp
  | succ j ih =>
    intro t h m
    have hge := Nat.ge_two_pow_of_testBit h
    rw [Nat.testBit_add_one] at h
    cases m with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_zero]
      have : (t - 2 ^ (j + 1)) % 2 = t % 2 := by
        rw [pow_succ] at hge ⊢
        obtain ⟨a, ha⟩ : ∃ a, t = a + 2 ^ j * 2 := ⟨t - 2 ^ j * 2, by omega⟩
        subst ha
        rw [Nat.add_sub_cancel, Nat.add_mul_mod_self_right]
      simp [this]
    | succ m =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one, show (t - 2 ^ (j + 1)) / 2 = t / 2 - 2 ^ j by
        rw [pow_succ] at hge ⊢; omega, ih h m]
      simp

theorem testBit_ge {t B m : ℕ} (ht : t < 2 ^ B) (hm : B ≤ m) : t.testBit m = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) hm))

theorem lt_two_pow_of_bits {t B : ℕ} (h : ∀ m, B ≤ m → t.testBit m = false) : t < 2 ^ B :=
  Nat.lt_pow_two_of_testBit t h

/-- Setting an unset bit below `B` keeps a number below `2 ^ B`. -/
theorem add_two_pow_lt {t j B : ℕ} (ht : t < 2 ^ B) (hj : j < B) (h : t.testBit j = false) :
    t + 2 ^ j < 2 ^ B :=
  lt_two_pow_of_bits fun m hm => by
    rw [testBit_add_two_pow h, testBit_ge ht hm]; simp; omega

theorem eq_of_bits {t t' B : ℕ} (ht : t < 2 ^ B) (ht' : t' < 2 ^ B)
    (h : ∀ m < B, t.testBit m = t'.testBit m) : t = t' := by
  refine Nat.eq_of_testBit_eq fun m => ?_
  by_cases hm : m < B
  · exact h m hm
  · rw [testBit_ge ht (by omega), testBit_ge ht' (by omega)]

/-- **Comparison through the highest differing bit.** -/
theorem lt_iff_testBit {c i B : ℕ} (hc : c < 2 ^ B) (hi : i < 2 ^ B) :
    c < i ↔ ∃ j < B, c.testBit j = false ∧ i.testBit j = true ∧
      ∀ m, j < m → m < B → i.testBit m = c.testBit m := by
  constructor
  · intro hlt
    set D := (Finset.range B).filter fun j => c.testBit j ≠ i.testBit j
    have hD : D.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty] at hn
      have : c = i := eq_of_bits hc hi fun m hm => by
        by_contra hne
        have : m ∈ D := Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, hne⟩
        rw [hn] at this; simp at this
      omega
    set j := D.max' hD
    have hjD : j ∈ D := D.max'_mem hD
    obtain ⟨hjB, hne⟩ := Finset.mem_filter.1 hjD
    have hjB' : j < B := Finset.mem_range.1 hjB
    have habove : ∀ m, j < m → m < B → i.testBit m = c.testBit m := by
      intro m hm hmB
      by_contra hn
      have : m ∈ D := Finset.mem_filter.2 ⟨Finset.mem_range.2 hmB, fun e => hn e.symm⟩
      have := D.le_max' m this
      omega
    refine ⟨j, hjB', ?_⟩
    rcases hcj : c.testBit j with _ | _ <;> rcases hij : i.testBit j with _ | _
    · rw [hcj, hij] at hne; exact absurd rfl hne
    · exact ⟨rfl, rfl, habove⟩
    · exfalso
      have := Nat.lt_of_testBit j hij hcj fun m hm => by
        by_cases hmB : m < B
        · exact habove m hm hmB
        · rw [testBit_ge hc (by omega), testBit_ge hi (by omega)]
      omega
    · rw [hcj, hij] at hne; exact absurd rfl hne
  · rintro ⟨j, hjB, hcj, hij, habove⟩
    exact Nat.lt_of_testBit j hcj hij fun m hm => by
      by_cases hmB : m < B
      · exact (habove m hm hmB).symm
      · rw [testBit_ge hc (by omega), testBit_ge hi (by omega)]

theorem getI_bitsOfNat : ∀ (c m : ℕ), (bitsOfNat c).getI m = c.testBit m := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro m
    rcases c with _ | c
    · simp [List.getI]
    · rw [bitsOfNat_succ]
      cases m with
      | zero => simp [List.getI, Nat.testBit_zero]
      | succ m =>
        rw [List.getI_cons_succ, ih _ (Nat.div_lt_self (Nat.succ_pos c) (by norm_num)),
          Nat.testBit_add_one]

/-! ### Counters in states -/

/-- The state with the counters `t` (even facts) and `i` (odd facts) of `B` bits. -/
def cntS (B t i : ℕ) : Set ℕ :=
  {f | f / 2 < B ∧ (if f % 2 = 0 then t.testBit (f / 2) else i.testBit (f / 2)) = true}

/-- The fact of bit `j` of `t`. -/
def tF (j : ℕ) : ℕ := 2 * j

/-- The fact of bit `j` of `i`. -/
def iF (j : ℕ) : ℕ := 2 * j + 1

theorem mem_cntS_tF {B t i j : ℕ} : tF j ∈ cntS B t i ↔ j < B ∧ t.testBit j = true := by
  simp [cntS, tF]

theorem mem_cntS_iF {B t i j : ℕ} : iF j ∈ cntS B t i ↔ j < B ∧ i.testBit j = true := by
  simp only [cntS, iF, Set.mem_setOf_eq]
  rw [show (2 * j + 1) / 2 = j by omega, if_neg (by omega)]

theorem tF_or_iF (f : ℕ) : f = tF (f / 2) ∨ f = iF (f / 2) := by
  unfold tF iF; omega

theorem tF_ne_iF (j m : ℕ) : tF j ≠ iF m := by unfold tF iF; omega

theorem tF_inj {j m : ℕ} (h : tF j = tF m) : j = m := by unfold tF at h; omega

theorem iF_inj {j m : ℕ} (h : iF j = iF m) : j = m := by unfold iF at h; omega

theorem cntS_ext {B t i t' i' : ℕ} (h1 : ∀ j < B, t.testBit j = t'.testBit j)
    (h2 : ∀ j < B, i.testBit j = i'.testBit j) : cntS B t i = cntS B t' i' := by
  ext f
  rcases tF_or_iF f with hf | hf <;> rw [hf]
  · rw [mem_cntS_tF, mem_cntS_tF]
    exact ⟨fun ⟨a, b⟩ => ⟨a, (h1 _ a) ▸ b⟩, fun ⟨a, b⟩ => ⟨a, (h1 _ a).symm ▸ b⟩⟩
  · rw [mem_cntS_iF, mem_cntS_iF]
    exact ⟨fun ⟨a, b⟩ => ⟨a, (h2 _ a) ▸ b⟩, fun ⟨a, b⟩ => ⟨a, (h2 _ a).symm ▸ b⟩⟩

/-- **The state determines the counters.** -/
theorem cntS_inj {B t i t' i' : ℕ} (ht : t < 2 ^ B) (hi : i < 2 ^ B) (ht' : t' < 2 ^ B)
    (hi' : i' < 2 ^ B) (h : cntS B t i = cntS B t' i') : t = t' ∧ i = i' := by
  constructor
  · refine eq_of_bits ht ht' fun m hm => ?_
    have := congrArg (tF m ∈ ·) h
    simp only [mem_cntS_tF, eq_iff_iff] at this
    rcases h1 : t.testBit m <;> rcases h2 : t'.testBit m <;> simp_all
  · refine eq_of_bits hi hi' fun m hm => ?_
    have := congrArg (iF m ∈ ·) h
    simp only [mem_cntS_iF, eq_iff_iff] at this
    rcases h1 : i.testBit m <;> rcases h2 : i'.testBit m <;> simp_all

/-- Setting bit `j` of `t`. -/
theorem cntS_insert_tF {B t i j : ℕ} (hj : j < B) (h : t.testBit j = false) :
    cntS B t i ∪ {tF j} = cntS B (t + 2 ^ j) i := by
  ext f
  rcases tF_or_iF f with hf | hf <;> rw [hf]
  · rw [Set.mem_union, mem_cntS_tF, mem_cntS_tF, Set.mem_singleton_iff, testBit_add_two_pow h]
    constructor
    · rintro (⟨a, b⟩ | e)
      · exact ⟨a, by simp [b]⟩
      · rw [tF_inj e]; exact ⟨hj, by simp⟩
    · rintro ⟨a, b⟩
      by_cases e : f / 2 = j
      · exact Or.inr (by rw [e])
      · exact Or.inl ⟨a, by simpa [e] using b⟩
  · rw [Set.mem_union, mem_cntS_iF, mem_cntS_iF, Set.mem_singleton_iff]
    simp [(tF_ne_iF _ _).symm]

/-- Clearing bit `j` of `t`. -/
theorem cntS_diff_tF {B t i j : ℕ} (h : t.testBit j = true) :
    cntS B t i \ {tF j} = cntS B (t - 2 ^ j) i := by
  ext f
  rcases tF_or_iF f with hf | hf <;> rw [hf]
  · rw [Set.mem_diff, mem_cntS_tF, mem_cntS_tF, Set.mem_singleton_iff, testBit_sub_two_pow h]
    constructor
    · rintro ⟨⟨a, b⟩, e⟩
      have : f / 2 ≠ j := fun e' => e (by rw [e'])
      exact ⟨a, by simp [this, b]⟩
    · rintro ⟨a, b⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at b
      exact ⟨⟨a, b.2⟩, fun e => b.1 (tF_inj e)⟩
  · rw [Set.mem_diff, mem_cntS_iF, mem_cntS_iF, Set.mem_singleton_iff]
    simp [(tF_ne_iF _ _).symm]

/-- Setting bit `j` of `i`. -/
theorem cntS_insert_iF {B t i j : ℕ} (hj : j < B) (h : i.testBit j = false) :
    cntS B t i ∪ {iF j} = cntS B t (i + 2 ^ j) := by
  ext f
  rcases tF_or_iF f with hf | hf <;> rw [hf]
  · rw [Set.mem_union, mem_cntS_tF, mem_cntS_tF, Set.mem_singleton_iff]
    simp [tF_ne_iF]
  · rw [Set.mem_union, mem_cntS_iF, mem_cntS_iF, Set.mem_singleton_iff, testBit_add_two_pow h]
    constructor
    · rintro (⟨a, b⟩ | e)
      · exact ⟨a, by simp [b]⟩
      · rw [iF_inj e]; exact ⟨hj, by simp⟩
    · rintro ⟨a, b⟩
      by_cases e : f / 2 = j
      · exact Or.inr (by rw [e])
      · exact Or.inl ⟨a, by simpa [e] using b⟩

/-- Clearing bit `j` of `i`. -/
theorem cntS_diff_iF {B t i j : ℕ} (h : i.testBit j = true) :
    cntS B t i \ {iF j} = cntS B t (i - 2 ^ j) := by
  ext f
  rcases tF_or_iF f with hf | hf <;> rw [hf]
  · rw [Set.mem_diff, mem_cntS_tF, mem_cntS_tF, Set.mem_singleton_iff]
    simp [tF_ne_iF]
  · rw [Set.mem_diff, mem_cntS_iF, mem_cntS_iF, Set.mem_singleton_iff, testBit_sub_two_pow h]
    constructor
    · rintro ⟨⟨a, b⟩, e⟩
      have : f / 2 ≠ j := fun e' => e (by rw [e'])
      exact ⟨a, by simp [this, b]⟩
    · rintro ⟨a, b⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at b
      exact ⟨⟨a, b.2⟩, fun e => b.1 (iF_inj e)⟩

end Article

end HTN
