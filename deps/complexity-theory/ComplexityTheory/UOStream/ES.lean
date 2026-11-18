import Mathlib

/-!
# Few generators suffice (Eisenbrand–Shmonin)

`HTN.UOStream.es_reduce`: let `x j : ι → ℤ` be integer vectors with entries bounded by `M`, and
let `K` be such that `(2 s M + 1) ^ |ι| < 2 ^ s` for every `s > K`.  Every non-negative integer
combination `Σ_j k_j x_j` is also a combination `Σ_j k'_j x_j` with at most `K` non-zero
coefficients, and `k'` is supported inside the support of `k`.

The proof (Eisenbrand and Shmonin, Oper. Res. Lett. 34, 2006): if the support `S` has more than
`K` elements, two different subsets of `S` have the same sum (there are `2^|S|` subsets and at
most `(2|S|M+1)^|ι|` sums); removing their intersection gives disjoint `P ≠ ∅` and `Q` with equal
sums.  Moving the smallest coefficient `μ` on `P` to `Q` keeps the combination and empties one
coefficient.
-/

namespace HTN

namespace UOStream

open Finset

variable {ι J : Type} [Fintype ι] [DecidableEq ι] [DecidableEq J]

/-- The combination of the generators `x` with coefficients `k` over `T`. -/
def comb (T : Finset J) (x : J → ι → ℤ) (k : J → ℕ) (i : ι) : ℤ := ∑ j ∈ T, (k j : ℤ) * x j i

/-- The support of `k` inside `T`. -/
def supp (T : Finset J) (k : J → ℕ) : Finset J := T.filter fun j => k j ≠ 0

/-- Two disjoint subsets of `S`, the first non-empty, with the same sum. -/
theorem exists_balanced {S : Finset J} {x : J → ι → ℤ} {M : ℕ} (hM : ∀ j ∈ S, ∀ i, |x j i| ≤ M)
    (hlt : (2 * S.card * M + 1) ^ Fintype.card ι < 2 ^ S.card) :
    ∃ P ⊆ S, ∃ Q ⊆ S, Disjoint P Q ∧ P.Nonempty ∧ ∀ i, ∑ j ∈ P, x j i = ∑ j ∈ Q, x j i := by
  set m := S.card
  set box : Finset (ι → ℤ) :=
    Fintype.piFinset fun _ => Icc (-((m * M : ℕ) : ℤ)) ((m * M : ℕ) : ℤ)
  have hbox : box.card = (2 * m * M + 1) ^ Fintype.card ι := by
    have hI : (Icc (-((m * M : ℕ) : ℤ)) ((m * M : ℕ) : ℤ)).card = 2 * m * M + 1 := by
      rw [Int.card_Icc]
      have e : ((m * M : ℕ) : ℤ) + 1 - -((m * M : ℕ) : ℤ) = ((2 * m * M + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [e, Int.toNat_natCast]
    simp only [box, Fintype.card_piFinset, hI, prod_const, card_univ]
  have hmaps : ∀ A ∈ S.powerset, (fun i => ∑ j ∈ A, x j i) ∈ box := by
    intro A hA
    rw [mem_powerset] at hA
    simp only [box, Fintype.mem_piFinset, mem_Icc]
    intro i
    have h1 : |∑ j ∈ A, x j i| ≤ ((m * M : ℕ) : ℤ) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ A, |x j i| ≤ ∑ _j ∈ A, (M : ℤ) := sum_le_sum fun j hj => hM j (hA hj) i
        _ = A.card * M := by simp
        _ ≤ m * M := by
          have := card_le_card hA
          exact_mod_cast Nat.mul_le_mul_right _ this
        _ = ((m * M : ℕ) : ℤ) := by push_cast; ring
    exact ⟨by linarith [neg_abs_le (∑ j ∈ A, x j i)], (le_abs_self _).trans h1⟩
  have hcard : box.card < S.powerset.card := by rw [hbox, card_powerset]; exact hlt
  obtain ⟨A, hA, B, hB, hAB, hsum⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [mem_powerset] at hA hB
  have hsplit : ∀ (U W : Finset J) (i : ι), ∑ j ∈ U, x j i = ∑ j ∈ U ∩ W, x j i + ∑ j ∈ U \ W, x j i :=
    fun U W i => (sum_inter_add_sum_diff U W _).symm
  have heq : ∀ i, ∑ j ∈ A \ B, x j i = ∑ j ∈ B \ A, x j i := by
    intro i
    have h := congrFun hsum i
    simp only at h
    rw [hsplit A B i, hsplit B A i, inter_comm B A] at h
    linarith
  by_cases hne : (A \ B).Nonempty
  · exact ⟨A \ B, sdiff_subset.trans hA, B \ A, sdiff_subset.trans hB, disjoint_sdiff_sdiff,
      hne, heq⟩
  · have hAB' : A \ B = ∅ := not_nonempty_iff_eq_empty.1 hne
    have hBA : (B \ A).Nonempty := by
      by_contra h
      have hBA' : B \ A = ∅ := not_nonempty_iff_eq_empty.1 h
      apply hAB
      have h1 : A ⊆ B := sdiff_eq_empty_iff_subset.1 hAB'
      have h2 : B ⊆ A := sdiff_eq_empty_iff_subset.1 hBA'
      exact Subset.antisymm h1 h2
    exact ⟨B \ A, sdiff_subset.trans hB, A \ B, sdiff_subset.trans hA, disjoint_sdiff_sdiff,
      hBA, fun i => (heq i).symm⟩

/-- **Eisenbrand–Shmonin.** -/
theorem es_reduce (x : J → ι → ℤ) (M K : ℕ)
    (hK : ∀ s, K < s → (2 * s * M + 1) ^ Fintype.card ι < 2 ^ s) :
    ∀ (T : Finset J) (k : J → ℕ), (∀ j ∈ T, ∀ i, |x j i| ≤ M) →
      ∃ k' : J → ℕ, (∀ j, k' j ≠ 0 → k j ≠ 0) ∧ (supp T k').card ≤ K ∧
        ∀ i, comb T x k' i = comb T x k i := by
  intro T
  suffices H : ∀ m (k : J → ℕ), (supp T k).card = m → (∀ j ∈ T, ∀ i, |x j i| ≤ M) →
      ∃ k' : J → ℕ, (∀ j, k' j ≠ 0 → k j ≠ 0) ∧ (supp T k').card ≤ K ∧
        ∀ i, comb T x k' i = comb T x k i from fun k hM => H _ k rfl hM
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm hM
    by_cases hle : m ≤ K
    · exact ⟨k, fun _ h => h, hm ▸ hle, fun _ => rfl⟩
    · set S := supp T k
      have hST : S ⊆ T := filter_subset _ _
      obtain ⟨P, hPS, Q, hQS, hPQ, hPne, hPQsum⟩ :=
        exists_balanced (S := S) (x := x) (M := M) (fun j hj => hM j (hST hj))
          (hm ▸ hK m (by omega))
      -- the smallest coefficient on `P`
      obtain ⟨j₀, hj₀P, hj₀⟩ := P.exists_min_image k hPne
      set μ := k j₀
      let k₂ : J → ℕ := fun j => if j ∈ P then k j - μ else if j ∈ Q then k j + μ else k j
      have hk₂P : ∀ j ∈ P, (k₂ j : ℤ) = k j - μ := by
        intro j hj
        simp only [k₂, if_pos hj]
        have : μ ≤ k j := hj₀ j hj
        push_cast [this]; ring
      have hk₂Q : ∀ j ∈ Q, (k₂ j : ℤ) = k j + μ := by
        intro j hj
        have hjP : j ∉ P := fun h => disjoint_left.1 hPQ h hj
        simp only [k₂, if_neg hjP, if_pos hj]; push_cast; ring
      have hk₂O : ∀ j, j ∉ P → j ∉ Q → k₂ j = k j := by
        intro j h1 h2; simp only [k₂, if_neg h1, if_neg h2]
      -- the combination does not change
      have hcomb : ∀ i, comb T x k₂ i = comb T x k i := by
        intro i
        have hP : P ⊆ T := hPS.trans hST
        have hQ : Q ⊆ T := hQS.trans hST
        have hdec : ∀ (f : J → ℤ), ∑ j ∈ T, f j =
            ∑ j ∈ P, f j + ∑ j ∈ Q, f j + ∑ j ∈ T \ (P ∪ Q), f j := by
          intro f
          rw [← sum_union hPQ, ← sum_union disjoint_sdiff, union_sdiff_of_subset (union_subset hP hQ)]
        unfold comb
        rw [hdec, hdec (fun j => (k j : ℤ) * x j i)]
        have e1 : ∑ j ∈ P, (k₂ j : ℤ) * x j i = ∑ j ∈ P, (k j : ℤ) * x j i - μ * ∑ j ∈ P, x j i := by
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun j hj => by rw [hk₂P j hj]; ring
        have e2 : ∑ j ∈ Q, (k₂ j : ℤ) * x j i = ∑ j ∈ Q, (k j : ℤ) * x j i + μ * ∑ j ∈ Q, x j i := by
          rw [mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun j hj => by rw [hk₂Q j hj]; ring
        have e3 : ∑ j ∈ T \ (P ∪ Q), (k₂ j : ℤ) * x j i = ∑ j ∈ T \ (P ∪ Q), (k j : ℤ) * x j i := by
          refine sum_congr rfl fun j hj => ?_
          rw [mem_sdiff, mem_union, not_or] at hj
          rw [hk₂O j hj.2.1 hj.2.2]
        rw [e1, e2, e3, hPQsum i]
        ring
      -- the support shrinks
      have hsupp₂ : ∀ j, k₂ j ≠ 0 → k j ≠ 0 := by
        intro j hj
        by_cases h1 : j ∈ P
        · intro h0; apply hj; simp only [k₂, if_pos h1, h0, Nat.zero_sub]
        · by_cases h2 : j ∈ Q
          · exact (mem_filter.1 (hQS h2)).2
          · rwa [hk₂O j h1 h2] at hj
      have hsub : supp T k₂ ⊆ S.erase j₀ := by
        intro j hj
        rw [supp, mem_filter] at hj
        refine mem_erase.2 ⟨fun h => ?_, mem_filter.2 ⟨hj.1, hsupp₂ j hj.2⟩⟩
        subst h
        apply hj.2
        simp only [k₂, if_pos hj₀P, μ, Nat.sub_self]
      have hlt : (supp T k₂).card < m := by
        have h1 := card_le_card hsub
        rw [card_erase_of_mem (hPS hj₀P)] at h1
        have : 0 < S.card := card_pos.2 ⟨j₀, hPS hj₀P⟩
        omega
      obtain ⟨k', hk', hcard, hc⟩ := ih _ hlt k₂ rfl hM
      exact ⟨k', fun j h => hsupp₂ j (hk' j h), hcard, fun i => (hc i).trans (hcomb i)⟩

end UOStream

end HTN
