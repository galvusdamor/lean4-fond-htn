import ComplexityTheory.Complexity.PrimDiag.Defs
import ComplexityTheory.Complexity.PolyExp
/-!
# A primitive recursive language outside every `N·k-EXPTIME/poly`

**Main results.**

* `HTN.PrimDiag.InNTowPoly j L` — `L` has a nondeterministic verifier of Cobham's class with
  polynomial advice and certificates of length at most `tow j (p |x|)` (an iterated exponential
  of a polynomial).  Level `1` is `NEXPTIME/poly` (`HTN.Space.InNExpPoly`), level `2` is
  `N2EXPTIME/poly`, which contains `EXPSPACE/poly`.
* `HTN.PrimDiag.not_inNTowPoly_dg` — the diagonal language `dg` is in none of these classes;
* `HTN.PrimDiag.exists_primrec_not_inNTowPoly` — **some language with a primitive recursive
  decision procedure is in no `InNTowPoly j`**, with no hypothesis.

This is the unconditional separation that replaces `EXPSPACE ⊄ NEXPTIME/poly` once the source
class is hard for all primitive recursive languages: a plain diagonalisation (every candidate
verifier is defeated at a length reserved for it), made primitive recursive by the universal
evaluator of `ComplexityTheory/Complexity/PrimDiag/Universal.lean`.
-/

namespace HTN.PrimDiag

open HTN.PTime HTN.PTime.CobhamTM HTN.PTime.CobhamTM.Prog

/-! ### Words -/

theorem mem_words {m : ℕ} {w : List Bool} : w ∈ words m ↔ w.length = m := by
  induction m generalizing w with
  | zero => simp [words]
  | succ m ih =>
    simp only [words, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨y, hy, rfl | rfl⟩ <;> simp [ih.1 hy]
    · intro h
      obtain _ | ⟨b, y⟩ := w
      · simp at h
      · refine ⟨y, ih.2 (by simpa using h), ?_⟩
        cases b <;> simp

theorem length_words (m : ℕ) : (words m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [words, List.length_flatMap, List.length_cons, List.length_nil]
    rw [List.map_const', List.sum_replicate, ih]
    simp [pow_succ]

theorem mem_upTo {B : ℕ} {w : List Bool} : w ∈ upTo B ↔ w.length ≤ B := by
  simp only [upTo, List.mem_flatMap, List.mem_range, mem_words]
  constructor
  · rintro ⟨l, hl, rfl⟩; omega
  · intro h; exact ⟨w.length, by omega, rfl⟩

theorem length_upTo (B : ℕ) : (upTo B).length + 1 = 2 ^ (B + 1) := by
  induction B with
  | zero => rfl
  | succ B ih =>
    have : upTo (B + 1) = upTo B ++ words (B + 1) := by
      simp [upTo, List.range_succ, List.flatMap_append]
    rw [this, List.length_append, length_words]
    rw [pow_succ 2 (B + 1)]
    omega

/-! ### Binary words and bits -/

theorem length_padW (n i : ℕ) : (padW n i).length = n := by simp [padW]

theorem bitB_succ (i k : ℕ) : bitB i (k + 1) = bitB (i / 2) k := by
  simp only [bitB, pow_succ', Nat.div_div_eq_div_mul]

theorem nob_padW (n i : ℕ) : nob (padW n i) = i % 2 ^ n := by
  induction n generalizing i with
  | zero => simp [padW, nob, Nat.mod_one]
  | succ n ih =>
    have hp : padW (n + 1) i = bitB i 0 :: padW n (i / 2) := by
      simp only [padW, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      exact List.map_congr_left fun k _ => bitB_succ i k
    have hn : nob (padW (n + 1) i) = (if bitB i 0 then 1 else 0) + 2 * nob (padW n (i / 2)) := by
      rw [hp]; rfl
    rw [hn, ih, pow_succ', Nat.mod_mul]
    congr 1
    simp only [bitB, pow_zero, Nat.div_one]
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

theorem bitB_eq_testBit (f i : ℕ) : bitB f i = f.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, bitB]
  by_cases h : f / 2 ^ i % 2 = 1 <;> simp [h]

theorem eq_of_bitB {K f f' : ℕ} (hf : f < 2 ^ K) (hf' : f' < 2 ^ K)
    (h : ∀ i < K, bitB f i = bitB f' i) : f = f' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [← bitB_eq_testBit, ← bitB_eq_testBit, h i hi]
  · push_neg at hi
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hf (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hf' (Nat.pow_le_pow_right (by norm_num) hi))]

theorem cond_not_eq_true {b g : Bool} : cond b g (!g) = true ↔ b = g := by
  cases b <;> cases g <;> simp

/-! ### Counting: some table is not produced -/

/-- **Some table is produced by no advice**: there are fewer than `2 ^ (R + 1)` advice strings
of length at most `R`. -/
theorem exists_not_realized (c : Cand) (n : ℕ) :
    ∃ f ∈ List.range (2 ^ (Rc c n + 1)), realizedB c n f = false := by
  classical
  by_contra hcon
  push_neg at hcon
  set K := Rc c n + 1
  have hreal : ∀ f < 2 ^ K, ∃ a ∈ upTo (Rc c n), ∀ i < K, bitB f i = gc c n a (padW n i) := by
    intro f hf
    have h := hcon f (List.mem_range.2 hf)
    rw [ne_eq, Bool.not_eq_false, realizedB, anyB_eq_true] at h
    obtain ⟨a, ha, hall⟩ := h
    exact ⟨a, ha, fun i hi => cond_not_eq_true.1 (allB_eq_true.1 hall i (List.mem_range.2 hi))⟩
  let φ : ℕ → List Bool := fun f =>
    if h : ∃ a ∈ upTo (Rc c n), ∀ i < K, bitB f i = gc c n a (padW n i) then h.choose else []
  have hφ : ∀ f < 2 ^ K, φ f ∈ upTo (Rc c n) ∧ ∀ i < K, bitB f i = gc c n (φ f) (padW n i) := by
    intro f hf
    have h := hreal f hf
    simp only [φ, dif_pos h]
    exact h.choose_spec
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range (2 ^ K))
    (t := (upTo (Rc c n)).toFinset) φ
    (fun f hf => by
      rw [Finset.coe_range, Set.mem_Iio] at hf
      simpa using (hφ f hf).1)
    (fun f hf f' hf' he => by
      rw [Finset.coe_range, Set.mem_Iio] at hf hf'
      refine eq_of_bitB hf hf' fun i hi => ?_
      rw [(hφ f hf).2 i hi, (hφ f' hf').2 i hi, he])
  have h1 := List.toFinset_card_le (upTo (Rc c n))
  have h2 := length_upTo (Rc c n)
  simp only [Finset.card_range] at hcard
  have h3 : 2 ^ K = 2 ^ (Rc c n + 1) := rfl
  omega

/-! ### Polynomials as coefficient lists -/

theorem polyL_append (l : List ℕ) (a n : ℕ) :
    polyL (l ++ [a]) n = polyL l n + n ^ l.length * a := by
  induction l with
  | nil => simp [polyL]
  | cons b l ih =>
    simp only [polyL, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem polyL_map_range (f : ℕ → ℕ) (k n : ℕ) :
    polyL ((List.range k).map f) n = ∑ i ∈ Finset.range k, f i * n ^ i := by
  induction k with
  | zero => simp [polyL]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, polyL_append, ih,
      Finset.sum_range_succ]
    simp [mul_comm]

theorem exists_polyL (p : Polynomial ℕ) : ∃ pc : List ℕ, ∀ n, polyL pc n = p.eval n :=
  ⟨(List.range (p.natDegree + 1)).map p.coeff, fun n => by
    rw [polyL_map_range, Polynomial.eval_eq_sum_range]⟩

/-! ### Large lengths -/

theorem exists_large (m : ℕ) : ∃ N, ∀ n ≥ N, (n + m) ^ m + 1 ≤ 2 ^ n := by
  obtain ⟨N₀, hN₀⟩ := HTN.exists_poly_lt_two_pow (2 ^ m + 1) m
  refine ⟨max N₀ m, fun n hn => ?_⟩
  have h := hN₀ n (le_of_max_le_left hn)
  have h1 : (n + m) ^ m ≤ 2 ^ m * (n + 1) ^ m := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h2 : 1 ≤ (n + 1) ^ m := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-! ### The separation -/

/-- **Nondeterministic iterated-exponential time with polynomial advice**: certificates of
length at most `tow j (p |x|)`, checked by a predicate of Cobham's class that also reads an
advice string of polynomial length depending on `|x|` only.  Level `1` is `NEXPTIME/poly`. -/
def InNTowPoly (j : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (V : Args → Bool) (p r : Polynomial ℕ) (adv : ℕ → List Bool), CobhamB V ∧
    (∀ n, (adv n).length ≤ r.eval n) ∧
    ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ tow j (p.eval x.length) ∧
      V [x, adv x.length, w] = true

/-- **The diagonal language is in no `InNTowPoly j`.** -/
theorem not_inNTowPoly_dg (j : ℕ) : ¬ InNTowPoly j (fun x => dg x = true) := by
  rintro ⟨V, p, r, adv, hV, hadv, hcorr⟩
  have hcorr' : ∀ x, dg x = true ↔ ∃ w : List Bool, w.length ≤ tow j (p.eval x.length) ∧
      V [x, adv x.length, w] = true := hcorr
  obtain ⟨C, M, A, m₁, hm₁, hU⟩ := exists_uevalB hV
  obtain ⟨m₂, hm₂, hr⟩ := exists_powSelf_bound r
  obtain ⟨pc, hpc⟩ := exists_polyL p
  let c : Cand := ((C, M, A), (m₁ + m₂, j, pc))
  obtain ⟨N, hN⟩ := exists_large (m₁ + m₂)
  let n := Nat.pair (Encodable.encode c) N
  have hn : N ≤ n := Nat.right_le_pair _ _
  have hcand : cand n = c := by simp [cand, n, Nat.unpair_pair, Encodable.encodek]
  have hK : Rc c n + 1 ≤ 2 ^ n := hN n hn
  have hVc : ∀ args, Vc c args = V args := fun args =>
    hU args _ (pow_bound_mono (m' := m₁ + m₂) hm₁ (by omega))
  have hBc : Bc c n = tow j (p.eval n) := by simp [Bc, c, hpc]
  have hg : ∀ y : List Bool, y.length = n → (gc c n (adv n) y = true ↔ dg y = true) := by
    intro y hy
    rw [gc, anyB_eq_true, hcorr' y, hy]
    constructor
    · rintro ⟨w, hw, hwV⟩
      exact ⟨w, by rw [← hBc]; exact mem_upTo.1 hw, by rw [← hVc]; exact hwV⟩
    · rintro ⟨w, hw, hwV⟩
      exact ⟨w, mem_upTo.2 (by rw [hBc]; exact hw), by rw [hVc]; exact hwV⟩
  have hdg : ∀ i < Rc c n + 1, dg (padW n i) = bitB (fstar c n) i := by
    intro i hi
    have hi' : i < 2 ^ n := lt_of_lt_of_le hi hK
    simp [dg, length_padW, hcand, nob_padW, Nat.mod_eq_of_lt hi', hi]
  obtain ⟨-, hfalse⟩ := findF_spec (exists_not_realized c n)
  have hadvR : (adv n).length ≤ Rc c n :=
    calc (adv n).length ≤ r.eval n := hadv n
      _ ≤ (n + m₂) ^ m₂ := hr n
      _ ≤ (n + (m₁ + m₂)) ^ (m₁ + m₂) := pow_bound_mono hm₂ (by omega)
  have htrue : realizedB c n (fstar c n) = true := by
    rw [realizedB, anyB_eq_true]
    refine ⟨adv n, mem_upTo.2 hadvR, allB_eq_true.2 fun i hi => ?_⟩
    rw [List.mem_range] at hi
    rw [cond_not_eq_true, ← hdg i hi]
    exact Bool.eq_iff_iff.2 (hg _ (length_padW n i)).symm
  rw [fstar] at htrue
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

/-- **A primitive recursive language in no `N·k-EXPTIME/poly`.**  The language `dg` has a
primitive recursive decision procedure and, for every level `j`, is not decided by a
nondeterministic verifier of Cobham's class with polynomial advice and certificates of length
`tow j (poly)`.  No hypothesis. -/
theorem exists_primrec_not_inNTowPoly :
    ∃ d : List Bool → Bool, Primrec d ∧ ∀ j, ¬ InNTowPoly j (fun x => d x = true) :=
  ⟨dg, primrec_dg, not_inNTowPoly_dg⟩

end HTN.PrimDiag
