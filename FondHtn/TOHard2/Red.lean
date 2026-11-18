import FondHtn.TOHard2.Correct
import HtnComplexity.Article.TOHard
import HtnComplexity.Article.BinCount
/-!
# The parameters of the reduction

For a deterministic single-tape machine `M`, the counter width `b` (numbers with `D = 2 ^ b`
digits), the exponent `E` of the padding (`N = 2 ^ E` padding cells) and the input `x`,
`FOND.TOHard2.parOf M b E x` are the parameters of the description.

* `FOND.TOHard2.hyp_parOf` — they describe the tableau of `M` on the padded word
  `Cx.padExp (C E) x` (`HTN.Article.dOf`, `HTN.Article.good_dOf` with the counter width `D`);
* `FOND.TOHard2.mpStrong_parOf_iff` — the description is MP strongly solvable iff `M` accepts the
  padded word within `2 ^ D - 1` steps.

The constants are given by their set digits (`FOND.TOHard2.onesL`); the end `c₂ = c₁ + 1 + 2 ^ E`
of the cells holding `1` has the set digits of `c₁ + 1` and `E` (`FOND.TOHard2.onesPow`).
-/

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn PTime TM

/-! ## Set digits -/

/-- The set digits of `c`. -/
def onesL (c : ℕ) : List ℕ := (List.range (bitsOfNat c).length).filter fun j => (bitsOfNat c).getI j

theorem mem_onesL {c j : ℕ} : j ∈ onesL c ↔ c.testBit j = true := by
  simp only [onesL, List.mem_filter, List.mem_range, getI_bitsOfNat]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hj
  push_neg at hj
  have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (HTN.Syn.PolyDom.lt_two_pow_length_bits c)
    (Nat.pow_le_pow_right (by norm_num) hj))
  rw [this] at h; cases h

/-- The set digits of `A + 2 ^ E`. -/
def onesPow (A E : ℕ) : List ℕ :=
  if (bitsOfNat A).length ≤ E then onesL A ++ [E] else onesL (A + 2 ^ min E (bitsOfNat A).length)

theorem mem_onesPow {A E j : ℕ} : j ∈ onesPow A E ↔ (A + 2 ^ E).testBit j = true := by
  unfold onesPow
  split_ifs with h
  · have hA : A < 2 ^ E := lt_of_lt_of_le (HTN.Syn.PolyDom.lt_two_pow_length_bits A) (Nat.pow_le_pow_right (by norm_num) h)
    rw [List.mem_append, mem_onesL, List.mem_singleton, add_comm]
    rcases lt_trichotomy j E with hj | rfl | hj
    · rw [Nat.testBit_two_pow_add_gt hj]; simp [Nat.ne_of_lt hj]
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hA]; simp
    · have h1 : 2 ^ E + A < 2 ^ j := by
        have : 2 ^ (E + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        rw [pow_succ] at this; omega
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow (lt_trans (by omega) h1)]
      simp [Nat.ne_of_gt hj]
  · rw [min_eq_left (by omega), mem_onesL]

/-- A list of digits describes the number with these set digits. -/
theorem ofB_kDig {cs : List (List ℕ)} {k c n : ℕ} (h : ∀ j, j ∈ cs.getI k ↔ c.testBit j = true)
    (hc : c < 2 ^ n) : ofB (kDig cs k) n = c :=
  (ofB_eq_iff hc).2 fun r _ => by
    simp only [kDig]
    cases hb : c.testBit r
    · simp only [decide_eq_false_iff_not]; rw [h]; simp [hb]
    · simp only [decide_eq_true_eq]; rw [h, hb]

theorem lt_of_testBit {c n j : ℕ} (hc : c < 2 ^ 2 ^ n) (h : c.testBit j = true) : j < 2 ^ n := by
  have := Nat.ge_two_pow_of_testBit h
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt this hc)

/-! ## The parameters -/

variable {k : ℕ} (M : NTM (Fin k) (Option Bool))

/-- The constants: `c₁`, `c₂ = c₁ + 1 + 2 ^ E` and the prefix cells. -/
def csOf (E : ℕ) (x : List Bool) : List (List ℕ) :=
  [onesL (prefW x).length, onesPow ((prefW x).length + 1) E] ++ (List.range (prefW x).length).map onesL

/-- **The parameters of the description.** -/
noncomputable def parOf (b E : ℕ) (x : List Bool) : Par where
  b := b
  cs := csOf E x
  mid := midL M
  lft := lftL M
  rgt := rgtL M
  acc := accL M
  baseU := (List.range (prefW x).length).map (baseCode M.init.val x)
  codeTrue := symC ((none, some true) : Option (Fin k) × Option Bool)
  codeNone := symC ((none, none) : Option (Fin k) × Option Bool)

/-- The tableau data of the run. -/
noncomputable def dataOf (b E : ℕ) (x : List Bool) : TabData :=
  dOf M (List.replicate (2 ^ b) ()) x (2 ^ E)

/-- The table of the run on the padded word. -/
noncomputable def tabOf (E : ℕ) (x : List Bool) : ℕ → ℕ → ℕ :=
  fun t i => symC (M.tab ((Cx.padExp (Polynomial.C E) x).map some) t i)

theorem csOf_getI (E : ℕ) (x : List Bool) (j : ℕ) :
    (csOf E x).getI j = if j = 0 then onesL (prefW x).length
      else if j = 1 then onesPow ((prefW x).length + 1) E
      else if j - 2 < (prefW x).length then onesL (j - 2) else [] := by
  unfold csOf
  rcases j with _ | _ | j
  · rfl
  · rfl
  · simp only [List.cons_append, List.nil_append, List.getI_cons_succ]
    rw [if_neg (by omega), if_neg (by omega), show j + 1 + 1 - 2 = j by omega,
      ← List.getD_default_eq_getI]
    split_ifs with h
    · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]; rfl

/-- **The parameters describe the tableau.** -/
theorem hyp_parOf (hdet : ∀ q γ, (M.step q γ).Subsingleton) (hblank : M.blank = none) {b E : ℕ}
    {x : List Bool} (hc₂ : (prefW x).length + 1 + 2 ^ E < 2 ^ 2 ^ b) :
    Hyp (parOf M b E x) (dataOf M b E x) (tabOf M E x) := by
  have hB1 : 1 ≤ (List.replicate (2 ^ b) ()).length := by simp; exact Nat.one_le_two_pow
  have hc₂' : (prefW x).length + 1 + 2 ^ (Polynomial.C E).eval x.length <
      2 ^ (List.replicate (2 ^ b) ()).length := by simpa using hc₂
  have hg := good_dOf M hdet hblank (q := Polynomial.C E) hB1 hc₂'
  simp only [Polynomial.eval_C] at hg
  have hL := length_prefW x
  have hE := Nat.two_pow_pos E
  refine ⟨hg, by simp [dataOf, dOf, parOf], rfl, rfl, rfl, rfl, rfl, by simp [dataOf, dOf, parOf],
    rfl, rfl, by simp [parOf, csOf]; omega, ?_, ?_, ?_, ?_⟩
  · intro j e he
    show e < 2 ^ b
    simp only [parOf, csOf_getI] at he
    split_ifs at he with h0 h1 h2
    · exact lt_of_testBit (by omega) (mem_onesL.1 he)
    · exact lt_of_testBit hc₂ (mem_onesPow.1 he)
    · exact lt_of_testBit (by omega) (mem_onesL.1 he)
    · simp at he
  · simp only [parOf, dataOf, dOf]
    exact ofB_kDig (fun j => by rw [csOf_getI, if_pos rfl, mem_onesL]) (by omega)
  · simp only [parOf, dataOf, dOf]
    exact ofB_kDig (fun j => by rw [csOf_getI, if_neg (by norm_num), if_pos rfl, mem_onesPow]) hc₂
  · intro c hc
    simp only [parOf, List.length_map, List.length_range] at hc ⊢
    exact ofB_kDig (fun j => by
      rw [csOf_getI, if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 + c - 2 = c by omega,
        mem_onesL]) (by omega)

/-- **Correctness of the reduction.** -/
theorem mpStrong_parOf_iff (hdet : ∀ q γ, (M.step q γ).Subsingleton) (hblank : M.blank = none)
    {b E : ℕ} {x : List Bool} (hc₂ : (prefW x).length + 1 + 2 ^ E < 2 ^ 2 ^ b) :
    (desc (parOf M b E x)).toProblem.MPStrongSolvable ↔
      M.AcceptsWithin ((Cx.padExp (Polynomial.C E) x).map some) (2 ^ 2 ^ b - 1) := by
  have H := hyp_parOf M hdet hblank hc₂
  rw [mpStrong_desc_iff H]
  have hB1 : 1 ≤ (List.replicate (2 ^ b) ()).length := by simp; exact Nat.one_le_two_pow
  have hc₂' : (prefW x).length + 1 + 2 ^ (Polynomial.C E).eval x.length <
      2 ^ (List.replicate (2 ^ b) ()).length := by simpa using hc₂
  have h1 := solvable_dOf_iff M hdet hblank hB1 hc₂'
  rw [TabData.solvable_iff (good_dOf M hdet hblank hB1 hc₂')] at h1
  simp only [Polynomial.eval_C, List.length_replicate] at h1
  have hmx : (dataOf M b E x).mx = 2 ^ (dataOf M b E x).B - 1 := H.good.hmx
  rw [← hmx]
  exact h1

end TOHard2

end FOND
