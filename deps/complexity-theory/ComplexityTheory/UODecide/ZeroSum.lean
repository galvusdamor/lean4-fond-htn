import Mathlib

/-!
# Zero-sum sub-multisets of bounded integer vectors

The combinatorial core of the small-solution bound for unordered HTN planning
(`HtnComplexity/UODecide/Abstract.lean`).

* `HTN.ZeroSum.exists_proper_zero_sum_1d` — a zero-sum multiset of at least `2a+2` integers in
  `[-a, a]` has a proper, nonempty zero-sum sub-multiset (greedy ordering + pigeonhole on the
  prefix sums);
* `HTN.ZeroSum.exists_proper_zero_sum` — the same in dimension `n`: a zero-sum multiset of
  more than `zsB n a = (2a+2)^(3^n)` vectors of `ℤⁿ` with entries in `[-a, a]` has a proper,
  nonempty zero-sum sub-multiset (induction on the dimension: split along one coordinate into
  short zero-sum pieces, then apply the induction hypothesis to the piece sums);
* `HTN.ZeroSum.exists_small_zero_sum_mem` — consequently every zero-sum multiset has a zero-sum
  sub-multiset of at most `zsB n a` elements containing any prescribed element.

Vectors are functions `ℕ → ℤ` vanishing outside a finite set of coordinates `A`.
-/

namespace HTN

namespace ZeroSum

open Multiset

variable {α : Type*}

/-! ### Dimension one -/

theorem list_sum_neg_of_forall {f : α → ℤ} :
    ∀ {l : List α}, l ≠ [] → (∀ x ∈ l, f x < 0) → (l.map f).sum < 0
  | [], h, _ => absurd rfl h
  | [x], _, hf => by simpa using hf x (by simp)
  | x :: y :: l, _, hf => by
    have h1 := hf x (by simp)
    have h2 : ((y :: l).map f).sum < 0 :=
      list_sum_neg_of_forall (by simp) (fun z hz => hf z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons, List.sum_cons] at h2 ⊢
    omega

theorem list_sum_nonneg_of_forall {f : α → ℤ} :
    ∀ {l : List α}, (∀ x ∈ l, 0 ≤ f x) → 0 ≤ (l.map f).sum
  | [], _ => by simp
  | x :: l, hf => by
    have h1 := hf x (by simp)
    have h2 : 0 ≤ (l.map f).sum :=
      list_sum_nonneg_of_forall (fun z hz => hf z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- **Greedy ordering**: a zero-sum family of integers in `[-a, a]` can be listed so that every
prefix sum (shifted by the current offset `σ`) stays in `[-a, a]`. -/
theorem greedy [DecidableEq α] (f : α → ℤ) (a : ℕ) :
    ∀ (n : ℕ) (R : List α) (σ : ℤ), R.length = n → (∀ x ∈ R, |f x| ≤ a) →
      σ + (R.map f).sum = 0 → |σ| ≤ a →
      ∃ l : List α, l.Perm R ∧ ∀ i, |σ + ((l.take i).map f).sum| ≤ a := by
  intro n
  induction n with
  | zero =>
    intro R σ hR _ _ hσ
    refine ⟨[], by rw [List.length_eq_zero_iff.1 hR], fun i => by simpa using hσ⟩
  | succ n ih =>
    intro R σ hR hb hsum hσ
    have hne : R ≠ [] := by rintro rfl; simp at hR
    -- choose the next element
    obtain ⟨x, hxR, hxσ⟩ : ∃ x ∈ R, |σ + f x| ≤ a := by
      by_cases hs : σ ≤ 0
      · by_contra hno
        push_neg at hno
        have hneg : ∀ x ∈ R, f x < 0 := by
          intro x hx
          by_contra hfx
          push_neg at hfx
          have h1 := hno x hx
          have h2 := hb x hx
          rw [abs_le] at h2 hσ
          rw [lt_abs] at h1
          omega
        have := list_sum_neg_of_forall hne hneg
        omega
      · push_neg at hs
        by_contra hno
        push_neg at hno
        have hpos : ∀ x ∈ R, 0 ≤ f x := by
          intro x hx
          by_contra hfx
          push_neg at hfx
          have h1 := hno x hx
          have h2 := hb x hx
          rw [abs_le] at h2 hσ
          rw [lt_abs] at h1
          omega
        have := list_sum_nonneg_of_forall hpos
        omega
    have hperm : R.Perm (x :: R.erase x) := List.perm_cons_erase hxR
    have hsum' : (σ + f x) + ((R.erase x).map f).sum = 0 := by
      have := (hperm.map f).sum_eq
      simp only [List.map_cons, List.sum_cons] at this
      omega
    have hlen : (R.erase x).length = n := by
      have := List.length_erase_of_mem hxR
      omega
    obtain ⟨l', hl', hpre⟩ := ih (R.erase x) (σ + f x) hlen
      (fun y hy => hb y (List.mem_of_mem_erase hy)) hsum' hxσ
    refine ⟨x :: l', ((hl'.cons x).trans hperm.symm), ?_⟩
    intro i
    cases i with
    | zero => simpa using hσ
    | succ i =>
      have := hpre i
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      rwa [← add_assoc]

/-- **Dimension one.**  A zero-sum family of at least `2a+2` integers in `[-a, a]` has a proper
nonempty zero-sum subfamily. -/
theorem exists_proper_zero_sum_1d (f : α → ℤ) (a : ℕ) (S : Multiset α)
    (hb : ∀ x ∈ S, |f x| ≤ a) (hs : (S.map f).sum = 0) (hc : 2 * a + 2 ≤ card S) :
    ∃ T ≤ S, T ≠ 0 ∧ T ≠ S ∧ (T.map f).sum = 0 := by
  classical
  induction S using Quotient.inductionOn with
  | h R =>
  simp only [Multiset.quot_mk_to_coe, Multiset.mem_coe, Multiset.map_coe, Multiset.sum_coe,
    Multiset.coe_card] at hb hs hc
  obtain ⟨l, hl, hpre⟩ := greedy f a R.length R 0 rfl hb (by simpa using hs) (by simp)
  have hlen : l.length = R.length := hl.length_eq
  -- pigeonhole on the prefix sums `0, …, l.length - 1`
  set P : ℕ → ℤ := fun i => ((l.take i).map f).sum with hP
  have hmaps : ∀ i ∈ Finset.range l.length, P i ∈ Finset.Icc (-(a : ℤ)) a := by
    intro i _
    have := hpre i
    rw [zero_add, abs_le] at this
    exact Finset.mem_Icc.2 this
  have hcard : (Finset.Icc (-(a : ℤ)) a).card < (Finset.range l.length).card := by
    rw [Int.card_Icc, Finset.card_range]
    omega
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have key : ∀ i j, i < j → j < l.length → P i = P j →
      ∃ T ≤ (↑R : Multiset α), T ≠ 0 ∧ T ≠ ↑R ∧ (T.map f).sum = 0 := by
    intro i j hij hj hPij
    refine ⟨↑((l.take j).drop i), ?_, ?_, ?_, ?_⟩
    · rw [← Multiset.coe_eq_coe.2 hl]
      exact Multiset.coe_le.2 ((List.drop_sublist _ _).trans (List.take_sublist _ _)).subperm
    · simp only [ne_eq, Multiset.coe_eq_zero, List.drop_eq_nil_iff, List.length_take]
      omega
    · intro h
      have := congrArg Multiset.card h
      simp only [Multiset.coe_card, List.length_drop, List.length_take] at this
      omega
    · have hsplit : (l.take j) = l.take i ++ (l.take j).drop i := by
        conv_lhs => rw [← List.take_append_drop i (l.take j)]
        rw [List.take_take, min_eq_left hij.le]
      have : P j = P i + (((l.take j).drop i).map f).sum := by
        simp only [hP]
        conv_lhs => rw [hsplit]
        simp
      simp only [Multiset.map_coe, Multiset.sum_coe]
      omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h (Finset.mem_range.1 hj) heq
  · exact key j i h (Finset.mem_range.1 hi) heq.symm

/-! ### Arbitrary dimension -/

theorem vsum_apply {β : Type*} (S : Multiset β) (g : β → ℕ → ℤ) (i : ℕ) :
    (S.map g).sum i = (S.map (fun x => g x i)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons x S ih => simp [ih]

/-- The length bound of the zero-sum lemma in dimension `n` for entries in `[-a, a]`. -/
def zsB (n a : ℕ) : ℕ := (2 * a + 2) ^ (3 ^ n)

theorem zsB_step (n a : ℕ) : (2 * a + 1) * zsB n ((2 * a + 1) * a) ≤ zsB (n + 1) a := by
  unfold zsB
  have hb : 2 * ((2 * a + 1) * a) + 2 ≤ (2 * a + 2) ^ 2 := by nlinarith
  have h1 : (2 * ((2 * a + 1) * a) + 2) ^ 3 ^ n ≤ ((2 * a + 2) ^ 2) ^ 3 ^ n :=
    Nat.pow_le_pow_left hb _
  have h2 : 2 * a + 1 ≤ 2 * a + 2 := by omega
  have hpos : 0 < 2 * a + 2 := by omega
  calc (2 * a + 1) * (2 * ((2 * a + 1) * a) + 2) ^ 3 ^ n
      ≤ (2 * a + 2) * ((2 * a + 2) ^ 2) ^ 3 ^ n := Nat.mul_le_mul h2 h1
    _ = (2 * a + 2) ^ (2 * 3 ^ n + 1) := by rw [← pow_mul, pow_succ, mul_comm]
    _ ≤ (2 * a + 2) ^ 3 ^ (n + 1) := by
        apply Nat.pow_le_pow_right hpos
        have : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
        rw [pow_succ]
        omega

theorem one_le_zsB (n a : ℕ) : 1 ≤ zsB n a := Nat.one_le_pow _ _ (by omega)

/-- Splitting a family that sums to zero in one coordinate into short pieces, each summing to
zero in that coordinate. -/
theorem exists_pieces (f : α → ℤ) (a : ℕ) :
    ∀ (n : ℕ) (S : Multiset α), card S = n → (∀ x ∈ S, |f x| ≤ a) → (S.map f).sum = 0 →
      ∃ P : Multiset (Multiset α), P.join = S ∧
        ∀ p ∈ P, p ≠ 0 ∧ card p ≤ 2 * a + 1 ∧ (p.map f).sum = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hb hs
    by_cases hsmall : card S ≤ 2 * a + 1
    · by_cases h0 : S = 0
      · exact ⟨0, by simp [h0], by simp⟩
      · exact ⟨{S}, by simp, by
          intro p hp
          rw [Multiset.mem_singleton] at hp
          subst hp
          exact ⟨h0, hsmall, hs⟩⟩
    · push_neg at hsmall
      obtain ⟨T, hT, hT0, hTS, hTsum⟩ := exists_proper_zero_sum_1d f a S hb hs (by omega)
      obtain ⟨U, rfl⟩ := Multiset.le_iff_exists_add.1 hT
      have hU0 : U ≠ 0 := by
        rintro rfl
        exact hTS (by simp)
      have hTc : card T < n := by
        rw [← hn, Multiset.card_add]
        have : 0 < card U := Multiset.card_pos.2 hU0
        omega
      have hUc : card U < n := by
        rw [← hn, Multiset.card_add]
        have : 0 < card T := Multiset.card_pos.2 hT0
        omega
      have hUsum : (U.map f).sum = 0 := by
        rw [Multiset.map_add, Multiset.sum_add, hTsum, zero_add] at hs
        exact hs
      obtain ⟨P₁, hP₁, hP₁ok⟩ := ih _ hTc T rfl (fun x hx => hb x (Multiset.mem_add.2 (Or.inl hx)))
        hTsum
      obtain ⟨P₂, hP₂, hP₂ok⟩ := ih _ hUc U rfl (fun x hx => hb x (Multiset.mem_add.2 (Or.inr hx)))
        hUsum
      refine ⟨P₁ + P₂, by rw [Multiset.join_add, hP₁, hP₂], ?_⟩
      intro p hp
      rcases Multiset.mem_add.1 hp with h | h
      · exact hP₁ok p h
      · exact hP₂ok p h

theorem join_le_join {P Q : Multiset (Multiset α)} (h : P ≤ Q) : P.join ≤ Q.join := by
  obtain ⟨U, rfl⟩ := Multiset.le_iff_exists_add.1 h
  rw [Multiset.join_add]
  exact Multiset.le_add_right _ _

theorem abs_sum_le_card_mul {s : Multiset α} {g : α → ℤ} {b : ℕ} (h : ∀ x ∈ s, |g x| ≤ b) :
    |(s.map g).sum| ≤ (card s * b : ℕ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have h1 := h x (Multiset.mem_cons_self _ _)
    have h2 := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    calc |g x + (s.map g).sum| ≤ |g x| + |(s.map g).sum| := abs_add_le _ _
      _ ≤ b + (card s * b : ℕ) := add_le_add h1 h2
      _ = ((card s + 1) * b : ℕ) := by push_cast; ring

/-- **The zero-sum lemma.**  Let `g` map a family `S` to integer vectors supported on the finite
coordinate set `A`, with entries in `[-a, a]`, summing to zero.  If `S` has more than
`zsB A.card a` members, it has a proper nonempty subfamily that also sums to zero. -/
theorem exists_proper_zero_sum (A : Finset ℕ) :
    ∀ (a : ℕ) {β : Type} (S : Multiset β) (g : β → ℕ → ℤ),
      (∀ x ∈ S, ∀ i, i ∉ A → g x i = 0) → (∀ x ∈ S, ∀ i, |g x i| ≤ a) →
      (S.map g).sum = 0 → zsB A.card a < card S →
      ∃ T ≤ S, T ≠ 0 ∧ T ≠ S ∧ (T.map g).sum = 0 := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro a β S g hsupp _ _ hc
    have hS : S ≠ 0 := by
      rintro rfl
      simp at hc
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hS
    refine ⟨{x}, Multiset.singleton_le.2 hx, by simp, ?_, ?_⟩
    · intro h
      have := congrArg Multiset.card h
      have h1 := one_le_zsB 0 a
      simp only [Finset.card_empty, Multiset.card_singleton] at this hc
      omega
    · funext i
      simp [hsupp x hx i (Finset.notMem_empty i)]
  | insert i A hi ih =>
    intro a β S g hsupp hb hs hc
    -- split along the coordinate `i`
    have hsi : (S.map (fun x => g x i)).sum = 0 := by
      have := congrFun hs i
      rwa [vsum_apply] at this
    obtain ⟨P, hPS, hPok⟩ := exists_pieces (fun x => g x i) a (card S) S rfl
      (fun x hx => hb x hx i) hsi
    -- the piece sums
    let G : Multiset β → ℕ → ℤ := fun p => (p.map g).sum
    have hmemP : ∀ p ∈ P, ∀ x ∈ p, x ∈ S := by
      intro p hp x hx
      rw [← hPS]
      exact Multiset.mem_join.2 ⟨p, hp, hx⟩
    have hGsupp : ∀ p ∈ P, ∀ j, j ∉ A → G p j = 0 := by
      intro p hp j hj
      by_cases hji : j = i
      · subst hji
        have := (hPok p hp).2.2
        simp only [G, vsum_apply]
        exact this
      · have hj' : j ∉ insert i A := by simp [hji, hj]
        simp only [G, vsum_apply]
        rw [Multiset.sum_eq_zero]
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
        exact hsupp x (hmemP p hp x hx) j hj'
    have hGb : ∀ p ∈ P, ∀ j, |G p j| ≤ ((2 * a + 1) * a : ℕ) := by
      intro p hp j
      simp only [G, vsum_apply]
      calc |(p.map (fun x => g x j)).sum| ≤ (card p * a : ℕ) :=
            abs_sum_le_card_mul (fun x hx => hb x (hmemP p hp x hx) j)
        _ ≤ ((2 * a + 1) * a : ℕ) := by
            exact_mod_cast Nat.mul_le_mul_right a (hPok p hp).2.1
    have hGs : (P.map G).sum = 0 := by
      have : (P.map G).sum = (P.join.map g).sum := by
        rw [Multiset.map_join, Multiset.sum_join, Multiset.map_map]
        rfl
      rw [this, hPS, hs]
    by_cases hbig : zsB A.card ((2 * a + 1) * a) < card P
    · obtain ⟨TP, hTP, hTP0, hTPP, hTPs⟩ := ih ((2 * a + 1) * a) P G hGsupp hGb hGs hbig
      obtain ⟨U, hU⟩ := Multiset.le_iff_exists_add.1 hTP
      refine ⟨TP.join, hPS ▸ join_le_join hTP, ?_, ?_, ?_⟩
      · obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hTP0
        have hp0 := (hPok p (Multiset.mem_of_le hTP hp)).1
        obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hp0
        intro h
        have : x ∈ TP.join := Multiset.mem_join.2 ⟨p, hp, hx⟩
        rw [h] at this
        simp at this
      · intro h
        have hU0 : U ≠ 0 := by
          rintro rfl
          exact hTPP (by simp [hU])
        obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hU0
        have hpP : p ∈ P := by rw [hU]; exact Multiset.mem_add.2 (Or.inr hp)
        have hp0 := (hPok p hpP).1
        have hcardp : 0 < card p := Multiset.card_pos.2 hp0
        have hjU : 0 < card U.join := by
          rw [Multiset.card_join]
          obtain ⟨V, rfl⟩ := Multiset.exists_cons_of_mem hp
          simp only [Multiset.map_cons, Multiset.sum_cons]
          omega
        have hc1 : card S = card TP.join + card U.join := by
          rw [← hPS, hU, Multiset.join_add, Multiset.card_add]
        rw [h] at hc1
        omega
      · have : (TP.join.map g).sum = (TP.map G).sum := by
          rw [Multiset.map_join, Multiset.sum_join, Multiset.map_map]
          rfl
        rw [this, hTPs]
    · push_neg at hbig
      exfalso
      have hcS : card S ≤ (2 * a + 1) * card P := by
        rw [← hPS, Multiset.card_join]
        calc (P.map card).sum ≤ (P.map (fun _ => 2 * a + 1)).sum :=
              Multiset.sum_map_le_sum_map _ _ (fun p hp => (hPok p hp).2.1)
          _ = (2 * a + 1) * card P := by
              rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_comm]
      have := zsB_step A.card a
      rw [Finset.card_insert_of_notMem hi] at hc
      have h2 : (2 * a + 1) * card P ≤ (2 * a + 1) * zsB A.card ((2 * a + 1) * a) :=
        Nat.mul_le_mul_left _ hbig
      omega

/-- **Small zero-sum subfamilies through a prescribed member.**  A zero-sum family as in
`exists_proper_zero_sum` has a zero-sum subfamily with at most `zsB A.card a` members that
contains the prescribed member `x₀`. -/
theorem exists_small_zero_sum_mem (A : Finset ℕ) (a : ℕ) {β : Type} (g : β → ℕ → ℤ) (x₀ : β) :
    ∀ (n : ℕ) (S : Multiset β), card S = n → x₀ ∈ S →
      (∀ x ∈ S, ∀ i, i ∉ A → g x i = 0) → (∀ x ∈ S, ∀ i, |g x i| ≤ a) →
      (S.map g).sum = 0 →
      ∃ T ≤ S, x₀ ∈ T ∧ card T ≤ zsB A.card a ∧ (T.map g).sum = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hx₀ hsupp hb hs
    by_cases hsmall : card S ≤ zsB A.card a
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

end ZeroSum

end HTN
