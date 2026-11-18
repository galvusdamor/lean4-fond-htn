import Mathlib

/-!
# Commutative grammars: a vector of rule multiplicities is realisable iff it balances and every
# used head is reachable

A finite list `R` of rules `(c, β)` rewrites one copy of the compound label `(true, c)` of a
multiset into the multiset `β` (`DecR`).  For a vector `x` of rule multiplicities let `T x` be the
sum of the bodies and `H x` the sum of the heads.

* `HTN.UOFlow.decR_iff` — `M` rewrites to a primitive multiset `P` iff there is `x` with
  `M + T x = H x + P` and every head of a rule used by `x` is reachable from a compound label of
  `M` along rules used by `x` (Esparza's characterisation for communication-free Petri nets).
-/

namespace HTN

namespace UOFlow

variable (R : List (ℕ × Multiset (Bool × ℕ)))

/-- Rewriting with the rules of `R`. -/
inductive DecR : Multiset (Bool × ℕ) → Multiset (Bool × ℕ) → Prop
  | refl (M : Multiset (Bool × ℕ)) : DecR M M
  | step {M M' : Multiset (Bool × ℕ)} {c : ℕ} {β : Multiset (Bool × ℕ)} :
      (true, c) ∈ M → (c, β) ∈ R → DecR (M.erase (true, c) + β) M' → DecR M M'

/-- Primitive multisets. -/
def PrimM (P : Multiset (Bool × ℕ)) : Prop := ∀ l ∈ P, l.1 = false

/-- The sum of the bodies. -/
def T (x : Fin R.length → ℕ) : Multiset (Bool × ℕ) := ∑ i, x i • (R.get i).2

/-- The sum of the heads. -/
def H (x : Fin R.length → ℕ) : Multiset (Bool × ℕ) := ∑ i, x i • {(true, (R.get i).1)}

/-- An edge `u → v`: a used rule with head `u` has `v` in its body. -/
def Edge (x : Fin R.length → ℕ) (u v : ℕ) : Prop :=
  ∃ i, 0 < x i ∧ (R.get i).1 = u ∧ (true, v) ∈ (R.get i).2

/-- `v` is reachable from a compound label of `M`. -/
def Reach (x : Fin R.length → ℕ) (M : Multiset (Bool × ℕ)) (v : ℕ) : Prop :=
  ∃ u, (true, u) ∈ M ∧ Relation.ReflTransGen (Edge R x) u v

/-- Every head of a used rule is reachable. -/
def Conn (x : Fin R.length → ℕ) (M : Multiset (Bool × ℕ)) : Prop :=
  ∀ i, 0 < x i → Reach R x M (R.get i).1

variable {R}

/-! ### Rewriting gives a balanced, connected vector -/

theorem T_add_single (x : Fin R.length → ℕ) (i : Fin R.length) :
    T R (x + Pi.single i 1) = T R x + (R.get i).2 := by
  simp only [T, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

theorem H_add_single (x : Fin R.length → ℕ) (i : Fin R.length) :
    H R (x + Pi.single i 1) = H R x + {(true, (R.get i).1)} := by
  simp only [H, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

theorem decR_flow {M P : Multiset (Bool × ℕ)} (h : DecR R M P) :
    ∃ x, M + T R x = H R x + P ∧ Conn R x M := by
  induction h with
  | refl M => exact ⟨0, by simp [T, H], fun i hi => absurd hi (by simp)⟩
  | @step M M' c β hc hr _ ih =>
    obtain ⟨x, heq, hconn⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hr
    refine ⟨x + Pi.single i 1, ?_, ?_⟩
    · rw [T_add_single, H_add_single, hi]
      have e : M = M.erase (true, c) + {(true, c)} := by
        rw [add_comm, Multiset.singleton_add, Multiset.cons_erase hc]
      calc M + (T R x + β) = (M.erase (true, c) + β + T R x) + {(true, c)} := by
            conv_lhs => rw [e]
            abel
        _ = H R x + {(true, c)} + M' := by rw [heq]; abel
    · -- edges of `x` are edges of the new vector; the new rule is an edge from `c`
      have hmono : ∀ u v, Edge R x u v → Edge R (x + Pi.single i 1) u v := by
        rintro u v ⟨j, hj, h1, h2⟩
        exact ⟨j, by simp only [Pi.add_apply]; omega, h1, h2⟩
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact ⟨c, hc, by rw [hi]⟩
      · have hj' : 0 < x j := by
          simpa [Pi.add_apply, Pi.single_apply, hji] using hj
        obtain ⟨u, hu, hp⟩ := hconn j hj'
        have hp' := hp.mono hmono
        rcases Multiset.mem_add.1 hu with hu | hu
        · exact ⟨u, Multiset.mem_of_mem_erase hu, hp'⟩
        · refine ⟨c, hc, Relation.ReflTransGen.head ?_ hp'⟩
          exact ⟨i, by simp, by rw [hi], by rw [hi]; exact hu⟩

/-! ### Paths avoiding a node -/

section Avoid

variable {α : Type} {E : α → α → Prop} {c : α}

theorem rtg_avoid_to {s : α} (h : Relation.ReflTransGen E s c) :
    Relation.ReflTransGen (fun u v => E u v ∧ u ≠ c) s c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hE _ ih =>
    by_cases hac : a = c
    · subst hac; exact .refl
    · exact .head ⟨hE, hac⟩ ih

theorem rtg_avoid_or {p u : α} (h : Relation.ReflTransGen E p u) :
    Relation.ReflTransGen (fun a b => E a b ∧ a ≠ c) p u ∨ Relation.ReflTransGen E c u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl .refl
  | @head a b hE hrest ih =>
    by_cases hac : a = c
    · subst hac; exact Or.inr (.head hE hrest)
    · rcases ih with ih | ih
      · exact Or.inl (.head ⟨hE, hac⟩ ih)
      · exact Or.inr ih

theorem rtg_avoid_from {u : α} (h : Relation.ReflTransGen (fun a b => E a b ∧ a ≠ c) c u) : u = c := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, ⟨_, hne⟩, _⟩
  · rfl
  · exact absurd rfl hne

end Avoid

/-! ### One firing step -/

section Step

variable {x : Fin R.length → ℕ} {M P : Multiset (Bool × ℕ)} {i : Fin R.length}

/-- The vector after firing rule `i` once. -/
def dec1 (x : Fin R.length → ℕ) (i : Fin R.length) : Fin R.length → ℕ := Function.update x i (x i - 1)

/-- The multiset after firing rule `i` once. -/
def fire (M : Multiset (Bool × ℕ)) (i : Fin R.length) : Multiset (Bool × ℕ) :=
  M.erase (true, (R.get i).1) + (R.get i).2

theorem dec1_add (hi : 0 < x i) : dec1 x i + Pi.single i 1 = x := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [dec1]; omega
  · simp [dec1, Function.update_of_ne hj, Pi.single_apply, hj]

theorem dec1_le (j : Fin R.length) : dec1 x i j ≤ x j := by
  by_cases hj : j = i
  · subst hj; simp [dec1]
  · simp [dec1, Function.update_of_ne hj]

theorem dec1_ne {j : Fin R.length} (hj : j ≠ i) : dec1 x i j = x j := by
  simp [dec1, Function.update_of_ne hj]

theorem fire_eq (hi : 0 < x i) (hc : (true, (R.get i).1) ∈ M) (heq : M + T R x = H R x + P) :
    fire M i + T R (dec1 x i) = H R (dec1 x i) + P := by
  have h1 := T_add_single (dec1 x i) i
  have h2 := H_add_single (dec1 x i) i
  rw [dec1_add hi] at h1 h2
  rw [h1, h2] at heq
  have e : M = M.erase (true, (R.get i).1) + {(true, (R.get i).1)} := by
    rw [add_comm, Multiset.singleton_add, Multiset.cons_erase hc]
  rw [e] at heq
  have : (fire M i + T R (dec1 x i)) + {(true, (R.get i).1)} =
      (H R (dec1 x i) + P) + {(true, (R.get i).1)} := by
    simp only [fire]
    calc M.erase (true, (R.get i).1) + (R.get i).2 + T R (dec1 x i) + {(true, (R.get i).1)}
        = M.erase (true, (R.get i).1) + {(true, (R.get i).1)} + (T R (dec1 x i) + (R.get i).2) := by abel
      _ = H R (dec1 x i) + {(true, (R.get i).1)} + P := heq
      _ = H R (dec1 x i) + P + {(true, (R.get i).1)} := by abel
  exact add_right_cancel this

/-- **Transfer of connectivity** through one firing step, given that the fired head stays
reachable (or marked, or unused). -/
theorem conn_fire (hi : 0 < x i) (hconn : Conn R x M)
    (hK : (true, (R.get i).1) ∈ fire M i ∨ Reach R (dec1 x i) (fire M i) (R.get i).1 ∨
      ∀ j, 0 < dec1 x i j → (R.get j).1 ≠ (R.get i).1) :
    Conn R (dec1 x i) (fire M i) := by
  set c := (R.get i).1
  -- every node reachable before is reachable from `fire M i` plus `c`
  have lift : ∀ u v, (true, u) ∈ M → Relation.ReflTransGen (Edge R x) u v →
      ∃ w, ((true, w) ∈ fire M i ∨ w = c) ∧ Relation.ReflTransGen (Edge R (dec1 x i)) w v := by
    intro u v hu hp
    induction hp with
    | refl =>
      by_cases huc : u = c
      · exact ⟨u, Or.inr huc, .refl⟩
      · refine ⟨u, Or.inl ?_, .refl⟩
        simp only [fire]
        exact Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne (by simpa using huc)).2 hu))
    | @tail b v' _ hE ih =>
      obtain ⟨w, hw, hp'⟩ := ih
      obtain ⟨k, hk, hk1, hk2⟩ := hE
      by_cases hki : k = i ∧ dec1 x i i = 0
      · obtain ⟨rfl, -⟩ := hki
        refine ⟨v', Or.inl ?_, .refl⟩
        simp only [fire]
        exact Multiset.mem_add.2 (Or.inr hk2)
      · have hk' : 0 < dec1 x i k := by
          by_cases hkie : k = i
          · subst hkie; push_neg at hki; exact Nat.pos_of_ne_zero (hki rfl)
          · rw [dec1_ne hkie]; exact hk
        exact ⟨w, hw, hp'.tail ⟨k, hk', hk1, hk2⟩⟩
  intro j hj
  obtain ⟨u, hu, hp⟩ := hconn j (lt_of_lt_of_le hj (dec1_le j))
  obtain ⟨w, hw, hp'⟩ := lift u _ hu hp
  rcases hw with hw | rfl
  · exact ⟨w, hw, hp'⟩
  · rcases hK with hK | ⟨w', hw', hp''⟩ | hK
    · exact ⟨c, hK, hp'⟩
    · exact ⟨w', hw', hp''.trans hp'⟩
    · exfalso
      rcases Relation.ReflTransGen.cases_head hp' with h0 | ⟨b, ⟨k, hk, hk1, -⟩, -⟩
      · exact hK j hj h0.symm
      · exact hK k hk hk1

end Step

/-! ### Choosing the rule to fire -/

section Choose

variable {x : Fin R.length → ℕ} {M P : Multiset (Bool × ℕ)}

theorem count_H (x : Fin R.length → ℕ) (c : ℕ) :
    (H R x).count (true, c) = ∑ k, if (R.get k).1 = c then x k else 0 := by
  simp only [H, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (R.get k).1 = c
  · rw [if_pos h, if_pos (by rw [h])]; simp
  · rw [if_neg h, if_neg (fun e => h (by rw [Prod.mk.injEq] at e; exact e.2.symm))]; simp

theorem count_T (x : Fin R.length → ℕ) (l : Bool × ℕ) :
    (T R x).count l = ∑ k, x k * ((R.get k).2.count l) := by
  simp only [T, Multiset.count_sum', Multiset.count_nsmul]

theorem edge_dec1 {i : Fin R.length} {u v : ℕ} (h : Edge R x u v) (hu : u ≠ (R.get i).1) :
    Edge R (dec1 x i) u v := by
  obtain ⟨k, hk, hk1, hk2⟩ := h
  have hki : k ≠ i := fun e => hu (by rw [← hk1, e])
  exact ⟨k, by rw [dec1_ne hki]; exact hk, hk1, hk2⟩

theorem mem_fire_of_ne {i : Fin R.length} {p : ℕ} (hp : (true, p) ∈ M) (hne : p ≠ (R.get i).1) :
    (true, p) ∈ fire M i := by
  simp only [fire]
  exact Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne (by simpa using hne)).2 hp))

/-- **The choice**: some used rule with a marked head can be fired keeping connectivity. -/
theorem choose_step (heq : M + T R x = H R x + P) (hP : PrimM P) (hconn : Conn R x M)
    (hx : ∃ i, 0 < x i) :
    ∃ i, 0 < x i ∧ (true, (R.get i).1) ∈ M ∧ Conn R (dec1 x i) (fire M i) := by
  -- a marked head
  obtain ⟨i0, hi0⟩ := hx
  have hmarked : ∃ i1, 0 < x i1 ∧ (true, (R.get i1).1) ∈ M := by
    obtain ⟨u, hu, hp⟩ := hconn i0 hi0
    rcases Relation.ReflTransGen.cases_head hp with h | ⟨b, ⟨k, hk, hk1, -⟩, -⟩
    · exact ⟨i0, hi0, h ▸ hu⟩
    · exact ⟨k, hk, hk1 ▸ hu⟩
  obtain ⟨i1, hi1, hm1⟩ := hmarked
  obtain ⟨c, hc⟩ : ∃ c, (R.get i1).1 = c := ⟨_, rfl⟩
  rw [hc] at hm1
  by_cases hA : 2 ≤ M.count (true, c)
  · -- two tokens: one stays
    refine ⟨i1, hi1, hc ▸ hm1, conn_fire hi1 hconn (Or.inl ?_)⟩
    simp only [fire, hc]
    refine Multiset.mem_add.2 (Or.inl (Multiset.count_pos.1 ?_))
    rw [Multiset.count_erase_self]; omega
  by_cases hB : ∃ j, 0 < x j ∧ (R.get j).1 = c ∧ ∃ s, (true, s) ∈ (R.get j).2 ∧
      Relation.ReflTransGen (Edge R x) s c
  · -- a used rule of `c` leads back to `c`
    obtain ⟨j, hj, hjc, s, hs, hp⟩ := hB
    refine ⟨j, hj, hjc ▸ hm1, conn_fire hj hconn (Or.inr (Or.inl ?_))⟩
    refine ⟨s, by simp only [fire]; exact Multiset.mem_add.2 (Or.inr hs), ?_⟩
    rw [hjc]
    exact (rtg_avoid_to hp).mono fun u v ⟨hE, hu⟩ => edge_dec1 hE (by rw [hjc]; exact hu)
  by_cases hC : ∃ j, 0 < x j ∧ (true, c) ∈ (R.get j).2
  · -- `c` is produced by a rule of another head
    obtain ⟨j, hj, hjc⟩ := hC
    refine ⟨i1, hi1, hc ▸ hm1, conn_fire hi1 hconn (Or.inr (Or.inl ?_))⟩
    rw [hc]
    have hu : (R.get j).1 ≠ c := fun e => hB ⟨j, hj, e, c, hjc, .refl⟩
    obtain ⟨p, hp, hpath⟩ := hconn j hj
    rcases rtg_avoid_or (c := c) hpath with hav | hfrom
    · have hpc : p ≠ c := fun e => by
        subst e; exact hu (rtg_avoid_from hav)
      refine ⟨p, mem_fire_of_ne hp (by rw [hc]; exact hpc), ?_⟩
      refine ((hav.mono fun u v ⟨hE, hu'⟩ => edge_dec1 hE (by rw [hc]; exact hu')).tail ?_)
      have hji : j ≠ i1 := fun e => hu (by rw [e, hc])
      exact ⟨j, by rw [dec1_ne hji]; exact hj, rfl, hjc⟩
    · exfalso
      rcases Relation.ReflTransGen.cases_head hfrom with h | ⟨b, ⟨k, hk, hk1, hk2⟩, hbu⟩
      · exact hu h.symm
      · exact hB ⟨k, hk, hk1, b, hk2, hbu.tail ⟨j, hj, rfl, hjc⟩⟩
  · -- `c` is not produced: its only token is consumed by the only use of a rule of `c`
    refine ⟨i1, hi1, hc ▸ hm1, conn_fire hi1 hconn (Or.inr (Or.inr ?_))⟩
    rw [hc]
    push_neg at hA hC
    have hM1 : M.count (true, c) = 1 := by
      have := Multiset.count_pos.2 hm1; omega
    have hT0 : (T R x).count (true, c) = 0 := by
      rw [count_T]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases Nat.eq_zero_or_pos (x k) with h | h
      · rw [h, zero_mul]
      · rw [Multiset.count_eq_zero.2 (hC k h), mul_zero]
    have hP0 : P.count (true, c) = 0 := Multiset.count_eq_zero.2 fun h => by simpa using hP _ h
    have hH : (H R x).count (true, c) = 1 := by
      have := congrArg (Multiset.count (true, c)) heq
      rw [Multiset.count_add, Multiset.count_add, hM1, hT0, hP0] at this
      omega
    rw [count_H] at hH
    have hf1 : (if (R.get i1).1 = c then x i1 else 0) = x i1 := if_pos hc
    intro k hk hkc
    by_cases hki : k = i1
    · subst hki
      have h2 : 2 ≤ x k := by simp only [dec1, Function.update_self] at hk; omega
      have := Finset.single_le_sum (f := fun k => if (R.get k).1 = c then x k else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      simp only at this
      rw [hf1] at this
      omega
    · have hxk : 0 < x k := by rw [dec1_ne hki] at hk; exact hk
      have hfk : (if (R.get k).1 = c then x k else 0) = x k := if_pos hkc
      have := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun k => if (R.get k).1 = c then x k else 0) (Finset.subset_univ {k, i1})
        (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair hki] at this
      simp only at this
      rw [hf1, hfk] at this
      omega

end Choose

/-! ### Realisation -/

theorem sum_dec1 {x : Fin R.length → ℕ} {i : Fin R.length} (hi : 0 < x i) :
    ∑ j, dec1 x i j + 1 = ∑ j, x j := by
  conv_rhs => rw [← dec1_add hi]
  simp [Finset.sum_add_distrib]

theorem flow_decR {P : Multiset (Bool × ℕ)} (hP : PrimM P) :
    ∀ (n : ℕ) (M : Multiset (Bool × ℕ)) (x : Fin R.length → ℕ), ∑ j, x j = n →
      M + T R x = H R x + P → Conn R x M → DecR R M P
  | 0, M, x, hn, heq, _ => by
    have hx : x = 0 := funext fun j => by
      have := Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      simp only [Pi.zero_apply]; omega
    subst hx
    simp only [T, H, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, zero_add] at heq
    subst heq
    exact .refl _
  | n + 1, M, x, hn, heq, hconn => by
    have hx : ∃ i, 0 < x i := by
      by_contra h
      push_neg at h
      have : ∑ j, x j = 0 := Finset.sum_eq_zero fun j _ => by have := h j; omega
      omega
    obtain ⟨i, hi, hm, hconn'⟩ := choose_step heq hP hconn hx
    refine .step hm (List.get_mem R i) ?_
    have := sum_dec1 hi
    exact flow_decR hP n (fire M i) (dec1 x i) (by omega) (fire_eq hi hm heq) hconn'

/-- **Esparza's characterisation.** -/
theorem decR_iff {M P : Multiset (Bool × ℕ)} (hP : PrimM P) :
    DecR R M P ↔ ∃ x, M + T R x = H R x + P ∧ Conn R x M :=
  ⟨decR_flow, fun ⟨x, heq, hconn⟩ => flow_decR hP _ M x rfl heq hconn⟩

end UOFlow

end HTN
