import Mathlib

/-!
# The covering lemma of Fortnow and Santhanam

The combinatorial core of the theorem of Fortnow and Santhanam (2008): *if OR-SAT has a
polynomial compression, then `NP ⊆ coNP/poly`*.  Let `U` be a finite set (the unsatisfiable
formulas of one size), and `f` a map on `t`-tuples over `U` whose values lie in a set `T` with at
most `2 ^ ℓ` elements, where `ℓ ≤ t` (the compressed outputs).  Then a set `S ⊆ T` with
`2 ^ |S| ≤ 2 |U|` — so of size about `log₂ |U| + 1` — **covers** `U`: every `x ∈ U` occurs in
some tuple over `U` whose value lies in `S`.

With `S` as advice, the complement of the compressed language is in `NP/poly`: to certify that
`x` is unsatisfiable, guess a tuple over the formulas of the same size that contains `x` and whose
compressed value lies in `S`.  A tuple containing a satisfiable formula is a yes-instance of
OR-SAT, and yes- and no-instances never share a compressed value, so no satisfiable `x` has such
a certificate.

* `HTN.Syn.Compress.exists_half_cover` — one greedy step: some value covers half of `W`;
* `HTN.Syn.Compress.fs_cover` — the covering lemma.
-/

namespace HTN

namespace Syn

namespace Compress

open Finset

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- The elements of `W` that occur in a tuple over `W` mapped to `y`. -/
def coverSet {t : ℕ} (f : (Fin t → X) → Y) (W : Finset X) (y : Y) : Finset X :=
  W.filter fun x => ∃ tup ∈ Fintype.piFinset (fun _ : Fin t => W), (∃ i, tup i = x) ∧ f tup = y

/-- **One greedy step**: if the tuples over `W` take at most `2 ^ ℓ ≤ 2 ^ t` values, one of the
values covers at least half of `W`. -/
theorem exists_half_cover {t ℓ : ℕ} (f : (Fin t → X) → Y) (W : Finset X) (hW : W.Nonempty)
    (T : Finset Y) (hT : T.card ≤ 2 ^ ℓ) (hℓ : ℓ ≤ t) (ht : 0 < t)
    (hmap : ∀ tup ∈ Fintype.piFinset (fun _ : Fin t => W), f tup ∈ T) :
    ∃ y ∈ T, W.card ≤ 2 * (coverSet f W y).card := by
  by_contra hcon
  push_neg at hcon
  set P := Fintype.piFinset (fun _ : Fin t => W) with hP
  have hPcard : P.card = W.card ^ t := by simp [hP]
  have hfib : ∀ y ∈ T, (P.filter fun tup => f tup = y).card ≤ (coverSet f W y).card ^ t := by
    intro y _
    have hsub : P.filter (fun tup => f tup = y) ⊆
        Fintype.piFinset (fun _ : Fin t => coverSet f W y) := by
      intro tup htup
      rw [mem_filter] at htup
      rw [Fintype.mem_piFinset]
      intro i
      have hi : tup i ∈ W := (Fintype.mem_piFinset.1 htup.1) i
      simp only [coverSet, mem_filter]
      exact ⟨hi, tup, htup.1, ⟨i, rfl⟩, htup.2⟩
    calc _ ≤ _ := card_le_card hsub
      _ = _ := by simp
  have hsum : P.card = ∑ y ∈ T, (P.filter fun tup => f tup = y).card :=
    card_eq_sum_card_fiberwise hmap
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hW
    exact ⟨f (fun _ => x), hmap _ (by simp [hP, hx])⟩
  have hsmall : ∀ y ∈ T, 2 ^ ℓ * (coverSet f W y).card ^ t < W.card ^ t := by
    intro y hy
    have h1 : 2 * (coverSet f W y).card < W.card := hcon y hy
    calc 2 ^ ℓ * (coverSet f W y).card ^ t ≤ 2 ^ t * (coverSet f W y).card ^ t :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hℓ)
      _ = (2 * (coverSet f W y).card) ^ t := by rw [mul_pow]
      _ < W.card ^ t := Nat.pow_lt_pow_left h1 (by omega)
  have : 2 ^ ℓ * W.card ^ t < 2 ^ ℓ * W.card ^ t := by
    calc 2 ^ ℓ * W.card ^ t = 2 ^ ℓ * ∑ y ∈ T, (P.filter fun tup => f tup = y).card := by
          rw [← hsum, hPcard]
      _ ≤ 2 ^ ℓ * ∑ y ∈ T, (coverSet f W y).card ^ t :=
          Nat.mul_le_mul_left _ (sum_le_sum hfib)
      _ = ∑ y ∈ T, 2 ^ ℓ * (coverSet f W y).card ^ t := by rw [mul_sum]
      _ < ∑ y ∈ T, W.card ^ t := sum_lt_sum_of_nonempty hTne hsmall
      _ = T.card * W.card ^ t := by simp
      _ ≤ 2 ^ ℓ * W.card ^ t := Nat.mul_le_mul_right _ hT
  exact lt_irrefl _ this

/-- **The covering lemma of Fortnow and Santhanam.**  If the `t`-tuples over the finite set `U`
are mapped into a set of at most `2 ^ ℓ` values, with `ℓ ≤ t`, then a set `S` of values with
`2 ^ |S| ≤ 2 |U|` covers `U`: every element of `U` occurs in a tuple over `U` whose value lies
in `S`. -/
theorem fs_cover {t ℓ : ℕ} (f : (Fin t → X) → Y) (U : Finset X) (hU : U.Nonempty)
    (T : Finset Y) (hT : T.card ≤ 2 ^ ℓ) (hℓ : ℓ ≤ t) (ht : 0 < t)
    (hmap : ∀ tup ∈ Fintype.piFinset (fun _ : Fin t => U), f tup ∈ T) :
    ∃ S ⊆ T, 2 ^ S.card ≤ 2 * U.card ∧
      ∀ x ∈ U, ∃ tup ∈ Fintype.piFinset (fun _ : Fin t => U), (∃ i, tup i = x) ∧ f tup ∈ S := by
  suffices key : ∀ m, ∀ W ⊆ U, W.card = m → W.Nonempty → ∃ S ⊆ T, 2 ^ S.card ≤ 2 * W.card ∧
      ∀ x ∈ W, ∃ tup ∈ Fintype.piFinset (fun _ : Fin t => U), (∃ i, tup i = x) ∧ f tup ∈ S from
    key _ U subset_rfl rfl hU
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W hWU hWm hW
  have hmapW : ∀ tup ∈ Fintype.piFinset (fun _ : Fin t => W), f tup ∈ T := fun tup htup =>
    hmap tup (Fintype.mem_piFinset.2 fun i => hWU ((Fintype.mem_piFinset.1 htup) i))
  obtain ⟨y, hyT, hy⟩ := exists_half_cover f W hW T hT hℓ ht hmapW
  set C := coverSet f W y with hC
  have hCW : C ⊆ W := filter_subset _ _
  have hcovC : ∀ x ∈ C, ∃ tup ∈ Fintype.piFinset (fun _ : Fin t => U), (∃ i, tup i = x) ∧
      f tup = y := by
    intro x hx
    simp only [hC, coverSet, mem_filter] at hx
    obtain ⟨-, tup, htup, hi, hf⟩ := hx
    exact ⟨tup, Fintype.mem_piFinset.2 fun i => hWU ((Fintype.mem_piFinset.1 htup) i), hi, hf⟩
  set W' := W \ C with hW'
  have hW'card : W'.card = W.card - C.card := card_sdiff_of_subset hCW
  have hCle : C.card ≤ W.card := card_le_card hCW
  rcases W'.eq_empty_or_nonempty with h0 | hne
  · refine ⟨{y}, by simpa using hyT, ?_, ?_⟩
    · have : 1 ≤ W.card := hW.card_pos
      simp; omega
    · intro x hx
      have hxC : x ∈ C := by
        by_contra hxC
        have : x ∈ W' := mem_sdiff.2 ⟨hx, hxC⟩
        rw [h0] at this; simp at this
      obtain ⟨tup, htup, hi, hf⟩ := hcovC x hxC
      exact ⟨tup, htup, hi, by simp [hf]⟩
  · have hlt : W'.card < m := by
      have : 1 ≤ W.card := hW.card_pos
      omega
    obtain ⟨S', hS'T, hS'card, hS'cov⟩ :=
      ih _ hlt W' (fun x hx => hWU (mem_sdiff.1 hx).1) rfl hne
    refine ⟨insert y S', insert_subset hyT hS'T, ?_, ?_⟩
    · calc 2 ^ (insert y S').card ≤ 2 ^ (S'.card + 1) :=
            Nat.pow_le_pow_right (by norm_num) (card_insert_le _ _)
        _ = 2 * 2 ^ S'.card := by ring
        _ ≤ 2 * (2 * W'.card) := by omega
        _ ≤ 2 * W.card := by omega
    · intro x hx
      by_cases hxC : x ∈ C
      · obtain ⟨tup, htup, hi, hf⟩ := hcovC x hxC
        exact ⟨tup, htup, hi, by simp [hf]⟩
      · obtain ⟨tup, htup, hi, hf⟩ := hS'cov x (mem_sdiff.2 ⟨hx, hxC⟩)
        exact ⟨tup, htup, hi, mem_insert_of_mem hf⟩

end Compress

end Syn

end HTN
