import HtnComplexity.Article.TOHardAct
/-!
# The tableau-checking problem: soundness

`HTN.Article.TabData.Good d tabC`: the data `d` describe the table `tabC` (the codes of the
entries of a tableau): its first row, its local rule (complete and sound), its accepting entries,
and the constants are in range.

`HTN.Article.TabData.sem_of_refT`: every refinement of a compound name has its meaning
(`HTN.Article.TabData.Sem`): `cIncT j` adds `2 ^ j` to `t`, `cDecT j` subtracts it, likewise
`cIncI j`, `cDecI j` for `i`; `cGuess j` sets bit `j` of `i` or not; and `cChk a` from the state
`(t, i)` restores it, and the entry `(t, i)` has the code `a`.
-/

namespace HTN

namespace Article

open Syn PTime

namespace TabData

/-- **The data describe the table `tabC`.** -/
structure Good (d : TabData) (tabC : ℕ → ℕ → ℕ) : Prop where
  hB : 1 ≤ d.B
  hmx : d.mx = 2 ^ d.B - 1
  hc₁ : 1 ≤ d.c₁
  hc₂ : d.c₂ < 2 ^ d.B
  hc₁₂ : d.c₁ ≤ d.c₂
  base : ∀ c < d.c₁, tabC 0 c = d.baseU.getI c
  tru : ∀ i, d.c₁ ≤ i → i < d.c₂ → tabC 0 i = d.codeTrue
  non : ∀ i, d.c₂ ≤ i → i < 2 ^ d.B → tabC 0 i = d.codeNone
  mid_s : ∀ q ∈ d.mid, ∀ t i, 0 < i → i + 1 < 2 ^ d.B → tabC t (i - 1) = q.2.1 →
    tabC t i = q.2.2.1 → tabC t (i + 1) = q.2.2.2 → tabC (t + 1) i = q.1
  mid_c : ∀ t i, 0 < i → i + 1 < 2 ^ d.B → t + 1 < 2 ^ d.B →
    (tabC (t + 1) i, tabC t (i - 1), tabC t i, tabC t (i + 1)) ∈ d.mid
  lft_s : ∀ q ∈ d.lft, ∀ t, tabC t 0 = q.2.1 → tabC t 1 = q.2.2 → tabC (t + 1) 0 = q.1
  lft_c : ∀ t, t + 1 < 2 ^ d.B → (tabC (t + 1) 0, tabC t 0, tabC t 1) ∈ d.lft
  rgt_s : ∀ q ∈ d.rgt, ∀ t, t + 1 < 2 ^ d.B → tabC t (d.mx - 1) = q.2.1 → tabC t d.mx = q.2.2 →
    tabC (t + 1) d.mx = q.1
  rgt_c : ∀ t, t + 1 < 2 ^ d.B → (tabC (t + 1) d.mx, tabC t (d.mx - 1), tabC t d.mx) ∈ d.rgt

/-- The meaning of the compound name of kind `k` and parameter `p`. -/
def SemK (B : ℕ) (tabC : ℕ → ℕ → ℕ) (k p : ℕ) (s s' : Set ℕ) : Prop :=
  if k = 0 then ∀ t i, t < 2 ^ B → s = cntS B t i → t + 2 ^ p < 2 ^ B ∧ s' = cntS B (t + 2 ^ p) i
  else if k = 1 then ∀ t i, t < 2 ^ B → s = cntS B t i → 2 ^ p ≤ t ∧ s' = cntS B (t - 2 ^ p) i
  else if k = 2 then ∀ t i, i < 2 ^ B → s = cntS B t i → i + 2 ^ p < 2 ^ B ∧ s' = cntS B t (i + 2 ^ p)
  else if k = 3 then ∀ t i, i < 2 ^ B → s = cntS B t i → 2 ^ p ≤ i ∧ s' = cntS B t (i - 2 ^ p)
  else if k = 4 then ∀ t i, i < 2 ^ p → p < B → s = cntS B t i → ∃ i' < 2 ^ (p + 1), s' = cntS B t i'
  else if k = 5 then ∀ t i, t < 2 ^ B → i < 2 ^ B → s = cntS B t i → s' = s ∧ tabC t i = p
  else True

/-- The meaning of a task name. -/
def Sem (B : ℕ) (tabC : ℕ → ℕ → ℕ) : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop
  | .inl _, _, _ => True
  | .inr n, s, s' => SemK B tabC (n % 8) (n / 8) s s'

theorem sem_cN {B : ℕ} {tabC : ℕ → ℕ → ℕ} {k p : ℕ} (hk : k < 8) {s s' : Set ℕ} :
    Sem B tabC (Sum.inr (cN k p)) s s' ↔ SemK B tabC k p s s' := by
  simp only [Sem, cN_mod hk, cN_div hk]

section Uses

variable {B : ℕ} {tabC : ℕ → ℕ → ℕ} {s s' : Set ℕ} {t i : ℕ}

theorem sem_incT {p : ℕ} (h : Sem B tabC (Sum.inr (cIncT p)) s s') (ht : t < 2 ^ B)
    (hs : s = cntS B t i) : t + 2 ^ p < 2 ^ B ∧ s' = cntS B (t + 2 ^ p) i := by
  rw [cIncT, sem_cN (by norm_num)] at h
  simp only [SemK, if_true] at h
  exact h t i ht hs

theorem sem_decT {p : ℕ} (h : Sem B tabC (Sum.inr (cDecT p)) s s') (ht : t < 2 ^ B)
    (hs : s = cntS B t i) : 2 ^ p ≤ t ∧ s' = cntS B (t - 2 ^ p) i := by
  rw [cDecT, sem_cN (by norm_num)] at h
  simp only [SemK, show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true] at h
  exact h t i ht hs

theorem sem_incI {p : ℕ} (h : Sem B tabC (Sum.inr (cIncI p)) s s') (hi : i < 2 ^ B)
    (hs : s = cntS B t i) : i + 2 ^ p < 2 ^ B ∧ s' = cntS B t (i + 2 ^ p) := by
  rw [cIncI, sem_cN (by norm_num)] at h
  simp only [SemK, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false,
    if_true] at h
  exact h t i hi hs

theorem sem_decI {p : ℕ} (h : Sem B tabC (Sum.inr (cDecI p)) s s') (hi : i < 2 ^ B)
    (hs : s = cntS B t i) : 2 ^ p ≤ i ∧ s' = cntS B t (i - 2 ^ p) := by
  rw [cDecI, sem_cN (by norm_num)] at h
  simp only [SemK, show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
    show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true] at h
  exact h t i hi hs

theorem sem_guess {p : ℕ} (h : Sem B tabC (Sum.inr (cGuess p)) s s') (hi : i < 2 ^ p)
    (hp : p < B) (hs : s = cntS B t i) : ∃ i' < 2 ^ (p + 1), s' = cntS B t i' := by
  rw [cGuess, sem_cN (by norm_num)] at h
  simp only [SemK, show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num,
    show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num, if_false, if_true] at h
  exact h t i hi hp hs

theorem sem_chk {a : ℕ} (h : Sem B tabC (Sum.inr (cChk a)) s s') (ht : t < 2 ^ B)
    (hi : i < 2 ^ B) (hs : s = cntS B t i) : s' = s ∧ tabC t i = a := by
  rw [cChk, sem_cN (by norm_num)] at h
  simp only [SemK, show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
    show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num,
    if_false, if_true] at h
  exact h t i ht hi hs

end Uses

/-! ### Soundness -/

variable {d : TabData} {tabC : ℕ → ℕ → ℕ}

/-- The chain of a sequence method, as a chain of its labels. -/
theorem chain_meth {c : ℕ} {body : List (Bool × ℕ)} {s s' : Set ℕ}
    (h : ChainR (fun n s s' => RefT d.desc n s s' ∧ Sem d.B tabC n s s') (meth c body).2.label
      (TnDesc.lin (meth c body).2) s s') :
    ChainL (fun n s s' => RefT d.desc n s s' ∧ Sem d.B tabC n s s') (body.map toLab) s s' :=
  chainR_seqTn_iff.1 h

theorem two_pow_succ_sub {t j : ℕ} (h : 2 ^ j ≤ t) : t - 2 ^ j + 2 ^ (j + 1) = t + 2 ^ j := by
  rw [pow_succ]; omega

/-- The meaning of every method. -/
theorem sem_meth (hg : Good d tabC) {e : MethodDesc} (he : e ∈ d.methods) {s s' : Set ℕ}
    (hch : ChainR (fun n s s' => RefT d.desc n s s' ∧ Sem d.B tabC n s s') e.2.label
      (TnDesc.lin e.2) s s') : Sem d.B tabC (Sum.inr e.1) s s' := by
  rcases (d.mem_methods).1 he with ⟨j, hj, h⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ |
      ⟨c, hc, rfl⟩ | ⟨X, hX, Y, hY, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨a, -, rfl⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      have hc := chain_meth hch <;>
      simp only [List.map_cons, List.map_nil, toLab, if_true, Bool.false_eq_true, if_false,
        chainL_cons_iff, chainL_nil_iff] at hc
    -- incT, set
    · obtain ⟨s₁, ⟨h₁, -⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 0 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, if_true]
      rintro t i ht rfl
      obtain ⟨hb, rfl⟩ := (d.refT_setT hj).1 h₁
      exact ⟨add_two_pow_lt ht hj hb, rfl⟩
    -- incT, clear and carry
    · obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨-, h₂⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 0 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, if_true]
      rintro t i ht rfl
      obtain ⟨hb, rfl⟩ := (d.refT_clrT hj).1 h₁
      have hge := Nat.ge_two_pow_of_testBit hb
      obtain ⟨h3, rfl⟩ := sem_incT h₂ (lt_of_le_of_lt (Nat.sub_le _ _) ht) rfl
      rw [two_pow_succ_sub hge] at h3 ⊢
      exact ⟨h3, rfl⟩
    -- decT, clear
    · obtain ⟨s₁, ⟨h₁, -⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 1 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true]
      rintro t i ht rfl
      obtain ⟨hb, rfl⟩ := (d.refT_clrT hj).1 h₁
      exact ⟨Nat.ge_two_pow_of_testBit hb, rfl⟩
    -- decT, set and borrow
    · obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨-, h₂⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 1 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true]
      rintro t i ht rfl
      obtain ⟨hb, rfl⟩ := (d.refT_setT hj).1 h₁
      obtain ⟨h3, rfl⟩ := sem_decT h₂ (add_two_pow_lt ht hj hb) rfl
      rw [pow_succ] at h3
      refine ⟨by omega, ?_⟩
      rw [pow_succ, show t + 2 ^ j - 2 ^ j * 2 = t - 2 ^ j by omega]
    -- incI, set
    · obtain ⟨s₁, ⟨h₁, -⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 2 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false,
        if_true]
      rintro t i hi rfl
      obtain ⟨hb, rfl⟩ := (d.refT_setI hj).1 h₁
      exact ⟨add_two_pow_lt hi hj hb, rfl⟩
    -- incI, clear and carry
    · obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨-, h₂⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 2 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false,
        if_true]
      rintro t i hi rfl
      obtain ⟨hb, rfl⟩ := (d.refT_clrI hj).1 h₁
      have hge := Nat.ge_two_pow_of_testBit hb
      obtain ⟨h3, rfl⟩ := sem_incI h₂ (lt_of_le_of_lt (Nat.sub_le _ _) hi) rfl
      rw [two_pow_succ_sub hge] at h3 ⊢
      exact ⟨h3, rfl⟩
    -- decI, clear
    · obtain ⟨s₁, ⟨h₁, -⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 3 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
        show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true]
      rintro t i hi rfl
      obtain ⟨hb, rfl⟩ := (d.refT_clrI hj).1 h₁
      exact ⟨Nat.ge_two_pow_of_testBit hb, rfl⟩
    -- decI, set and borrow
    · obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨-, h₂⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 3 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
        show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true]
      rintro t i hi rfl
      obtain ⟨hb, rfl⟩ := (d.refT_setI hj).1 h₁
      obtain ⟨h3, rfl⟩ := sem_decI h₂ (add_two_pow_lt hi hj hb) rfl
      rw [pow_succ] at h3
      refine ⟨by omega, ?_⟩
      rw [pow_succ, show i + 2 ^ j - 2 ^ j * 2 = i - 2 ^ j by omega]
    -- guess, no
    · obtain ⟨s₁, ⟨h₁, -⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 4 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num,
        show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num, if_false, if_true]
      rintro t i hi - rfl
      rw [(d.refT_noop).1 h₁]
      exact ⟨i, by rw [pow_succ]; omega, rfl⟩
    -- guess, yes
    · obtain ⟨s₁, ⟨h₁, -⟩, rfl⟩ := hc
      show Sem _ _ (Sum.inr (cN 4 j)) _ _
      rw [sem_cN (by norm_num)]
      simp only [SemK, show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num,
        show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num, if_false, if_true]
      rintro t i hi - rfl
      obtain ⟨-, rfl⟩ := (d.refT_setI hj).1 h₁
      exact ⟨i + 2 ^ j, by rw [pow_succ]; omega, rfl⟩
  -- the middle step
  · have hc := chain_meth hch
    simp only [midBody, List.map_cons, List.map_nil, toLab, if_true, chainL_cons_iff,
      chainL_nil_iff] at hc
    obtain ⟨s₁, ⟨-, h₁⟩, s₂, ⟨-, h₂⟩, s₃, ⟨-, h₃⟩, s₄, ⟨-, h₄⟩, s₅, ⟨-, h₅⟩, s₆, ⟨-, h₆⟩,
      s₇, ⟨-, h₇⟩, s₈, ⟨-, h₈⟩, s₉, ⟨-, h₉⟩, rfl⟩ := hc
    show Sem _ _ (Sum.inr (cN 5 q.1)) _ _
    rw [sem_cN (by norm_num)]
    simp only [SemK, show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
      show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num,
      if_false, if_true]
    rintro t i ht hi rfl
    obtain ⟨ht1, rfl⟩ := sem_decT h₁ ht rfl
    rw [pow_zero] at ht1
    obtain ⟨hi1, rfl⟩ := sem_decI h₂ hi rfl
    rw [pow_zero] at hi1
    obtain ⟨rfl, hl⟩ := sem_chk h₃ (by omega) (by omega) rfl
    obtain ⟨hi2, rfl⟩ := sem_incI h₄ (by omega) rfl
    rw [pow_zero, Nat.sub_add_cancel hi1] at hi2
    rw [pow_zero, Nat.sub_add_cancel hi1] at h₅
    obtain ⟨rfl, hcc⟩ := sem_chk h₅ (by omega) hi rfl
    obtain ⟨hi3, rfl⟩ := sem_incI h₆ hi rfl
    rw [pow_zero] at hi3 h₇
    obtain ⟨rfl, hr⟩ := sem_chk h₇ (by omega) hi3 rfl
    obtain ⟨-, rfl⟩ := sem_decI h₈ hi3 rfl
    rw [pow_zero, Nat.add_sub_cancel] at h₉
    obtain ⟨-, rfl⟩ := sem_incT h₉ (by omega) rfl
    rw [pow_zero, Nat.sub_add_cancel ht1]
    refine ⟨rfl, ?_⟩
    have := hg.mid_s q hq (t - 1) i (by omega) hi3 hl hcc hr
    rwa [Nat.sub_add_cancel ht1] at this
  -- the step at cell 0
  · have hc := chain_meth hch
    simp only [lftBody, List.map_cons, List.map_nil, toLab, if_true, Bool.false_eq_true, if_false,
      chainL_cons_iff, chainL_nil_iff] at hc
    obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨-, h₂⟩, s₃, ⟨-, h₃⟩, s₄, ⟨-, h₄⟩, s₅, ⟨-, h₅⟩, s₆, ⟨-, h₆⟩,
      s₇, ⟨-, h₇⟩, rfl⟩ := hc
    show Sem _ _ (Sum.inr (cN 5 q.1)) _ _
    rw [sem_cN (by norm_num)]
    simp only [SemK, show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
      show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num,
      if_false, if_true]
    rintro t i ht hi rfl
    obtain ⟨rfl, rfl⟩ := (d.refT_eq (Nat.two_pow_pos _) hi (Or.inl hg.hc₁)).1 h₁
    obtain ⟨ht1, rfl⟩ := sem_decT h₂ ht rfl
    rw [pow_zero] at ht1
    obtain ⟨rfl, hcc⟩ := sem_chk h₃ (by omega) hi rfl
    obtain ⟨hi3, rfl⟩ := sem_incI h₄ hi rfl
    rw [pow_zero, zero_add] at hi3 h₅
    obtain ⟨rfl, hr⟩ := sem_chk h₅ (by omega) hi3 rfl
    obtain ⟨-, rfl⟩ := sem_decI h₆ hi3 rfl
    rw [pow_zero, Nat.sub_self] at h₇
    obtain ⟨-, rfl⟩ := sem_incT h₇ (by omega) rfl
    rw [pow_zero, Nat.sub_add_cancel ht1]
    refine ⟨rfl, ?_⟩
    have := hg.lft_s q hq (t - 1) hcc hr
    rwa [Nat.sub_add_cancel ht1] at this
  -- the step at the last cell
  · have hc := chain_meth hch
    simp only [rgtBody, List.map_cons, List.map_nil, toLab, if_true, Bool.false_eq_true, if_false,
      chainL_cons_iff, chainL_nil_iff] at hc
    obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨-, h₂⟩, s₃, ⟨-, h₃⟩, s₄, ⟨-, h₄⟩, s₅, ⟨-, h₅⟩, s₆, ⟨-, h₆⟩,
      s₇, ⟨-, h₇⟩, rfl⟩ := hc
    show Sem _ _ (Sum.inr (cN 5 q.1)) _ _
    rw [sem_cN (by norm_num)]
    simp only [SemK, show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
      show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num,
      if_false, if_true]
    rintro t i ht hi rfl
    have hmx := hg.hmx
    have hB := hg.hB
    have h2B : 2 ≤ 2 ^ d.B := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d.B := Nat.pow_le_pow_right (by norm_num) hB
    obtain ⟨rfl, rfl⟩ := (d.refT_eq (by omega) hi (Or.inr (Or.inr (Or.inr rfl)))).1 h₁
    obtain ⟨ht1, rfl⟩ := sem_decT h₂ ht rfl
    rw [pow_zero] at ht1
    obtain ⟨-, rfl⟩ := sem_decI h₃ hi rfl
    rw [pow_zero] at h₄
    obtain ⟨rfl, hl⟩ := sem_chk h₄ (by omega) (by omega) rfl
    obtain ⟨-, rfl⟩ := sem_incI h₅ (by omega) rfl
    rw [pow_zero, Nat.sub_add_cancel (by omega : 1 ≤ d.mx)] at h₆
    obtain ⟨rfl, hcc⟩ := sem_chk h₆ (by omega) hi rfl
    obtain ⟨-, rfl⟩ := sem_incT h₇ (by omega) rfl
    rw [pow_zero, Nat.sub_add_cancel ht1]
    refine ⟨rfl, ?_⟩
    have := hg.rgt_s q hq (t - 1) (by omega) hl hcc
    rwa [Nat.sub_add_cancel ht1] at this
  -- the first row, the prefix
  · have hc := chain_meth hch
    simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
      chainL_cons_iff, chainL_nil_iff] at hc
    obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨h₂, -⟩, rfl⟩ := hc
    show Sem _ _ (Sum.inr (cN 5 _)) _ _
    rw [sem_cN (by norm_num)]
    simp only [SemK, show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
      show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num,
      if_false, if_true]
    rintro t i ht hi rfl
    obtain ⟨rfl, rfl⟩ := (d.refT_tz ht).1 h₁
    obtain ⟨rfl, rfl⟩ := (d.refT_eq (by have := hg.hc₂; have := hg.hc₁₂; omega) hi (Or.inl hc)).1 h₂
    exact ⟨rfl, hg.base i hc⟩
  -- the first row, the cells holding `1`
  · have hc := chain_meth hch
    simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
      chainL_cons_iff, chainL_nil_iff] at hc
    obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨h₂, -⟩, s₃, ⟨h₃, -⟩, rfl⟩ := hc
    show Sem _ _ (Sum.inr (cN 5 _)) _ _
    rw [sem_cN (by norm_num)]
    simp only [SemK, show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
      show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num,
      if_false, if_true]
    rintro t i ht hi rfl
    have hc₂ := hg.hc₂
    have hc₁₂ := hg.hc₁₂
    obtain ⟨rfl, rfl⟩ := (d.refT_tz ht).1 h₁
    have hge : d.c₁ ≤ i := by
      simp only [geNames, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range,
        Bool.not_eq_true', bit_eq] at hX
      rcases hX with rfl | ⟨j, ⟨hj, hcj⟩, rfl⟩
      · obtain ⟨rfl, -⟩ := (d.refT_eq (by omega) hi (Or.inr (Or.inl rfl))).1 h₂
        exact le_rfl
      · obtain ⟨⟨hij, hab⟩, -⟩ := (d.refT_gt1 hj).1 h₂
        exact ((lt_iff_testBit (by omega) hi).2 ⟨j, hj, hcj, hij, hab⟩).le
    have hs₂ : s₂ = cntS d.B 0 i := by
      simp only [geNames, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range] at hX
      rcases hX with rfl | ⟨j, ⟨hj, -⟩, rfl⟩
      · exact ((d.refT_eq (by omega) hi (Or.inr (Or.inl rfl))).1 h₂).2
      · exact ((d.refT_gt1 hj).1 h₂).2
    subst hs₂
    simp only [ltNames, List.mem_map, List.mem_filter, List.mem_range, bit_eq] at hY
    obtain ⟨j, ⟨hj, hcj⟩, rfl⟩ := hY
    obtain ⟨⟨hij, hab⟩, rfl⟩ := (d.refT_lt2 hj).1 h₃
    have hlt : i < d.c₂ := (lt_iff_testBit hi hc₂).2 ⟨j, hj, hij, hcj, fun m h1 h2 => (hab m h1 h2).symm⟩
    exact ⟨rfl, hg.tru i hge hlt⟩
  -- the first row, the blank cells
  · have hc := chain_meth hch
    simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
      chainL_cons_iff, chainL_nil_iff] at hc
    obtain ⟨s₁, ⟨h₁, -⟩, s₂, ⟨h₂, -⟩, rfl⟩ := hc
    show Sem _ _ (Sum.inr (cN 5 _)) _ _
    rw [sem_cN (by norm_num)]
    simp only [SemK, show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
      show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num,
      if_false, if_true]
    rintro t i ht hi rfl
    have hc₂ := hg.hc₂
    obtain ⟨rfl, rfl⟩ := (d.refT_tz ht).1 h₁
    simp only [geNames, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range,
      Bool.not_eq_true', bit_eq] at hX
    rcases hX with rfl | ⟨j, ⟨hj, hcj⟩, rfl⟩
    · obtain ⟨rfl, rfl⟩ := (d.refT_eq hc₂ hi (Or.inr (Or.inr (Or.inl rfl)))).1 h₂
      exact ⟨rfl, hg.non _ le_rfl hi⟩
    · obtain ⟨⟨hij, hab⟩, rfl⟩ := (d.refT_gt2 hj).1 h₂
      exact ⟨rfl, hg.non i ((lt_iff_testBit hc₂ hi).2 ⟨j, hj, hcj, hij, hab⟩).le hi⟩
  -- the root
  · show Sem _ _ (Sum.inr (cN 6 0)) _ _
    rw [sem_cN (by norm_num)]
    simp [SemK]

/-- **Soundness**: every refinement has its meaning. -/
theorem sem_of_refT (hg : Good d tabC) {n : ℕ ⊕ ℕ} {s s' : Set ℕ} (h : RefT d.desc n s s') :
    Sem d.B tabC n s s' :=
  refT_induction (p := d.desc) (Sem d.B tabC) (fun e he => d.methods_isTO (show e ∈ d.methods from he)) (fun _ _ _ => trivial)
    (fun e he s s' hch => sem_meth hg (show e ∈ d.methods from he) hch) h

end TabData

end Article

end HTN
