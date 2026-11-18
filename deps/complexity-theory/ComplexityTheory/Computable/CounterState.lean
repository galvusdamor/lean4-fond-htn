import ComplexityTheory.Computable.BitCount
/-!
# The states of the binary counter, as sets of facts

This file turns the bit lists of `ComplexityTheory/Computable/BitCount.lean` into planning
states — sets of facts — and writes down the two kinds of action the counting family of
`HtnComplexity/Computable/CounterFamily.lean` uses.

* `HTN.Syn.bitF k b` — the fact "the bit at position `k` is `b`"; the two facts of a position
  are complementary, which is what lets a *positive* precondition test a zero bit;
* `HTN.Syn.gF r` — the goal fact, outside the range of the counter facts;
* `HTN.Syn.stList l` — the facts of the bit list `l`, one per position;
* `HTN.Syn.stateAt r t mk` — the state after `t` increments of the `r`-bit counter, with the
  goal fact present exactly when `mk` is `true`;
* `HTN.Syn.incPrec j`, `HTN.Syn.incAdd j` — the precondition (= delete list) and add list of
  the action *increment at the lowest zero bit `j`*: it demands ones below `j` and a zero at
  `j`, and flips them.  `HTN.Syn.incPrec_subset_iff` and `HTN.Syn.inc_state` are its
  applicability and its effect: **a step of the counter**;
* `HTN.Syn.markPrec_subset_iff` and `HTN.Syn.mark_state` — the same for the *marking* action,
  which demands the whole bit pattern of a fixed value `i`, hence fires exactly at time `i`,
  and adds the goal fact.
-/

namespace HTN

namespace Syn

open Bits

/-! ### Facts -/

/-- The fact "the bit at position `k` has the value `b`". -/
def bitF (k : ℕ) (b : Bool) : ℕ := 2 * k + (if b then 1 else 0)

/-- The goal fact of the counting family, outside the range of the `r` counter positions. -/
def gF (r : ℕ) : ℕ := 2 * r

theorem bitF_lt {k : ℕ} {b : Bool} {r : ℕ} (h : k < r) : bitF k b < gF r := by
  have : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
  unfold bitF gF
  omega

theorem bitF_ne_gF {k : ℕ} {b : Bool} {r : ℕ} (h : k < r) : bitF k b ≠ gF r :=
  Nat.ne_of_lt (bitF_lt h)

theorem bitF_inj {k k' : ℕ} {b b' : Bool} (h : bitF k b = bitF k' b') : k = k' ∧ b = b' := by
  have hb : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
  have hb' : (if b' then 1 else 0) ≤ 1 := by cases b' <;> simp
  have hk : k = k' := by unfold bitF at h; omega
  subst hk
  refine ⟨rfl, ?_⟩
  cases b <;> cases b' <;> simp_all [bitF]

/-- The facts of a bit list: one per position. -/
def stList (l : List Bool) : List ℕ := (List.range l.length).map fun k => bitF k (l.getI k)

theorem mem_stList {l : List Bool} {f : ℕ} :
    f ∈ stList l ↔ ∃ k, k < l.length ∧ f = bitF k (l.getI k) := by
  constructor
  · intro h
    obtain ⟨k, hk, hfk⟩ := List.mem_map.1 h
    exact ⟨k, List.mem_range.1 hk, hfk.symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

theorem bitF_mem_stList {l : List Bool} {k : ℕ} {b : Bool} (hk : k < l.length) :
    bitF k b ∈ stList l ↔ l.getI k = b := by
  constructor
  · intro h
    obtain ⟨k', hk', he⟩ := mem_stList.1 h
    obtain ⟨rfl, hb⟩ := bitF_inj he
    exact hb.symm
  · intro h
    exact mem_stList.2 ⟨k, hk, by rw [h]⟩

/-- Two bit lists of the same length with the same bits are equal. -/
theorem eq_of_getI {l l' : List Bool} (hlen : l.length = l'.length)
    (h : ∀ k < l.length, l.getI k = l'.getI k) : l = l' := by
  refine List.ext_getElem hlen (fun k h1 h2 => ?_)
  have := h k h1
  rwa [List.getI_eq_getElem _ h1, List.getI_eq_getElem _ h2] at this

/-! ### The states of the counter -/

/-- **The state after `t` increments** of the `r`-bit counter, marked or not. -/
def stateAt (r t : ℕ) (mk : Bool) : Set ℕ :=
  {f | f ∈ stList (cnt r t)} ∪ (if mk then {gF r} else ∅)

theorem mem_stateAt {r t : ℕ} {mk : Bool} {f : ℕ} :
    f ∈ stateAt r t mk ↔
      (∃ k, k < r ∧ f = bitF k ((cnt r t).getI k)) ∨ (mk = true ∧ f = gF r) := by
  constructor
  · rintro (h | h)
    · obtain ⟨k, hk, hf⟩ := mem_stList.1 h
      rw [length_cnt] at hk
      exact Or.inl ⟨k, hk, hf⟩
    · cases mk with
      | false => simp at h
      | true =>
        simp only [if_true, Set.mem_singleton_iff] at h
        exact Or.inr ⟨rfl, h⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl (mem_stList.2 ⟨k, by rw [length_cnt]; exact hk, rfl⟩)
    · exact Or.inr (by simp)

theorem bitF_mem_stateAt {r t k : ℕ} {b : Bool} {mk : Bool} (hk : k < r) :
    bitF k b ∈ stateAt r t mk ↔ (cnt r t).getI k = b := by
  rw [mem_stateAt]
  constructor
  · rintro (⟨k', hk', he⟩ | ⟨-, he⟩)
    · obtain ⟨rfl, hb⟩ := bitF_inj he
      exact hb.symm
    · exact absurd he (bitF_ne_gF hk)
  · intro h
    exact Or.inl ⟨k, hk, by rw [h]⟩

theorem gF_mem_stateAt {r t : ℕ} {mk : Bool} : gF r ∈ stateAt r t mk ↔ mk = true := by
  rw [mem_stateAt]
  constructor
  · rintro (⟨k, hk, he⟩ | ⟨h, -⟩)
    · exact absurd he.symm (bitF_ne_gF hk)
    · exact h
  · intro h
    exact Or.inr ⟨h, rfl⟩

/-! ### The increment action -/

/-- The precondition — and delete list — of the increment at the lowest zero bit `j`. -/
def incPrec (j : ℕ) : List ℕ := (List.range j).map (fun k => bitF k true) ++ [bitF j false]

/-- The add list of the increment at the lowest zero bit `j`. -/
def incAdd (j : ℕ) : List ℕ := (List.range j).map (fun k => bitF k false) ++ [bitF j true]

theorem mem_incPrec {j f : ℕ} :
    f ∈ incPrec j ↔ (∃ k, k < j ∧ f = bitF k true) ∨ f = bitF j false := by
  simp only [incPrec, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro (⟨k, hk, rfl⟩ | h)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr h
  · rintro (⟨k, hk, rfl⟩ | rfl)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr rfl

theorem mem_incAdd {j f : ℕ} :
    f ∈ incAdd j ↔ (∃ k, k < j ∧ f = bitF k false) ∨ f = bitF j true := by
  simp only [incAdd, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro (⟨k, hk, rfl⟩ | h)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr h
  · rintro (⟨k, hk, rfl⟩ | rfl)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr rfl

theorem gF_not_mem_incPrec {r j : ℕ} (hj : j < r) : gF r ∉ incPrec j := by
  intro h
  rcases mem_incPrec.1 h with ⟨k, hk, he⟩ | he
  · exact absurd he.symm (bitF_ne_gF (show k < r by omega))
  · exact absurd he.symm (bitF_ne_gF hj)

/-- **When the increment at `j` is applicable**: the bits below `j` are ones and the bit at `j`
is a zero. -/
theorem incPrec_subset_iff {r t j : ℕ} {mk : Bool} (hj : j < r) :
    {f | f ∈ incPrec j} ⊆ stateAt r t mk ↔
      (∀ k < j, (cnt r t).getI k = true) ∧ (cnt r t).getI j = false := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have hmem : bitF k true ∈ stateAt r t mk :=
        h (mem_incPrec.2 (Or.inl ⟨k, hk, rfl⟩))
      exact (bitF_mem_stateAt (show k < r by omega)).1 hmem
    · have hmem : bitF j false ∈ stateAt r t mk := h (mem_incPrec.2 (Or.inr rfl))
      exact (bitF_mem_stateAt hj).1 hmem
  · rintro ⟨h1, h2⟩ f hf
    rcases mem_incPrec.1 hf with ⟨k, hk, rfl⟩ | rfl
    · exact (bitF_mem_stateAt (show k < r by omega)).2 (h1 k hk)
    · exact (bitF_mem_stateAt hj).2 h2

/-- **The effect of the increment at `j`**: the counter advances by one. -/
theorem inc_state {r t j : ℕ} {mk : Bool} (hj : j < r)
    (h1 : ∀ k < j, (cnt r t).getI k = true) (h2 : (cnt r t).getI j = false) :
    (stateAt r t mk \ {f | f ∈ incPrec j}) ∪ {f | f ∈ incAdd j} = stateAt r (t + 1) mk := by
  have hjl : j < (cnt r t).length := by rw [length_cnt]; exact hj
  have hbits : ∀ k, (cnt r (t + 1)).getI k =
      if k < j then false else if k = j then true else (cnt r t).getI k := by
    intro k
    rw [cnt_succ]
    exact getI_binInc hjl h1 h2 k
  ext f
  constructor
  · rintro (⟨hf, hnot⟩ | hadd)
    · rcases mem_stateAt.1 hf with ⟨k, hk, rfl⟩ | ⟨hmk, rfl⟩
      · have hkj : j < k := by
          by_contra hc
          push_neg at hc
          rcases Nat.lt_or_ge k j with h | h
          · exact hnot (mem_incPrec.2 (Or.inl ⟨k, h, by rw [h1 k h]⟩))
          · have : k = j := by omega
            subst this
            exact hnot (mem_incPrec.2 (Or.inr (by rw [h2])))
        refine mem_stateAt.2 (Or.inl ⟨k, hk, ?_⟩)
        rw [hbits k, if_neg (by omega), if_neg (by omega)]
      · exact mem_stateAt.2 (Or.inr ⟨hmk, rfl⟩)
    · rcases mem_incAdd.1 hadd with ⟨k, hk, rfl⟩ | rfl
      · refine mem_stateAt.2 (Or.inl ⟨k, by omega, ?_⟩)
        rw [hbits k, if_pos hk]
      · refine mem_stateAt.2 (Or.inl ⟨j, hj, ?_⟩)
        rw [hbits j, if_neg (by omega), if_pos rfl]
  · intro hf
    rcases mem_stateAt.1 hf with ⟨k, hk, rfl⟩ | ⟨hmk, rfl⟩
    · rcases Nat.lt_trichotomy k j with h | h | h
      · refine Or.inr (mem_incAdd.2 (Or.inl ⟨k, h, ?_⟩))
        rw [hbits k, if_pos h]
      · subst h
        refine Or.inr (mem_incAdd.2 (Or.inr ?_))
        rw [hbits k, if_neg (by omega), if_pos rfl]
      · refine Or.inl ⟨mem_stateAt.2 (Or.inl ⟨k, hk, ?_⟩), ?_⟩
        · rw [hbits k, if_neg (by omega), if_neg (by omega)]
        · intro hc
          rcases mem_incPrec.1 hc with ⟨k', hk', he⟩ | he
          · obtain ⟨rfl, -⟩ := bitF_inj he
            omega
          · obtain ⟨rfl, -⟩ := bitF_inj he
            omega
    · exact Or.inl ⟨mem_stateAt.2 (Or.inr ⟨hmk, rfl⟩), gF_not_mem_incPrec hj⟩

/-! ### The marking action -/

/-- **When the marking action of the value `i` is applicable**: exactly at time `i`. -/
theorem markPrec_subset_iff {r t i : ℕ} {mk : Bool} :
    {f | f ∈ stList (cnt r i)} ⊆ stateAt r t mk ↔ cnt r i = cnt r t := by
  constructor
  · intro h
    refine eq_of_getI (by simp) (fun k hk => ?_)
    rw [length_cnt] at hk
    have hmem : bitF k ((cnt r i).getI k) ∈ stateAt r t mk :=
      h (mem_stList.2 ⟨k, by rw [length_cnt]; exact hk, rfl⟩)
    exact ((bitF_mem_stateAt hk).1 hmem).symm
  · intro heq f hf
    rw [heq] at hf
    obtain ⟨k, hk, rfl⟩ := mem_stList.1 hf
    rw [length_cnt] at hk
    exact (bitF_mem_stateAt hk).2 rfl

/-- **The effect of the marking action**: the counter advances by one and the goal fact is
added. -/
theorem mark_state {r t i : ℕ} {mk : Bool} (h : cnt r i = cnt r t) :
    (stateAt r t mk \ {f | f ∈ stList (cnt r i)}) ∪ {f | f ∈ gF r :: stList (cnt r (i + 1))} =
      stateAt r (t + 1) true := by
  have hsucc : cnt r (i + 1) = cnt r (t + 1) := by rw [cnt_succ, cnt_succ, h]
  rw [h, hsucc]
  ext f
  constructor
  · rintro (⟨hf, hnot⟩ | hadd)
    · rcases mem_stateAt.1 hf with ⟨k, hk, rfl⟩ | ⟨-, rfl⟩
      · exact absurd (mem_stList.2 ⟨k, by rw [length_cnt]; exact hk, rfl⟩) hnot
      · exact mem_stateAt.2 (Or.inr ⟨rfl, rfl⟩)
    · rcases List.mem_cons.1 hadd with rfl | hmem
      · exact mem_stateAt.2 (Or.inr ⟨rfl, rfl⟩)
      · obtain ⟨k, hk, rfl⟩ := mem_stList.1 hmem
        rw [length_cnt] at hk
        exact mem_stateAt.2 (Or.inl ⟨k, hk, rfl⟩)
  · intro hf
    rcases mem_stateAt.1 hf with ⟨k, hk, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr (List.mem_cons.2 (Or.inr (mem_stList.2
        ⟨k, by rw [length_cnt]; exact hk, rfl⟩)))
    · exact Or.inr (List.mem_cons.2 (Or.inl rfl))

theorem gF_not_mem_stList {r t : ℕ} : gF r ∉ stList (cnt r t) := by
  intro h
  obtain ⟨k, hk, he⟩ := mem_stList.1 h
  rw [length_cnt] at hk
  exact absurd he.symm (bitF_ne_gF hk)

end Syn

end HTN
