import HtnComplexity.UOSpace.Table
/-!
# Representing abstract configurations by table states

A state of the action table `HTN.UOTbl.uoTbl d W` *represents* an abstract configuration
`(σ, M)` of `HTN.Syn.uoSys d q` (`HTN.UOTbl.Rep`) when its facts are exactly

* `fSt v` for `v ∈ σ`;
* the facts singled out by a control predicate `C` (in practice: one control fact);
* for every label `l` of the domain and every `i < W`, the bit fact "bit `i` of the counter of
  `l` is `(M.count l).testBit i`".

This file proves the bookkeeping lemmas: membership of the various fact shapes in a represented
state, and the effect of a counter decrement / increment on the bit facts.
-/

namespace HTN

namespace UOTbl

open Syn Space

/-! ### Fact shapes -/

@[simp] theorem fI_eq_bitF_iff {k : ℕ} {l : Bool × ℕ} {i : ℕ} {v : Bool} :
    fI k = bitF l i v ↔ k = kBit l i v := by unfold bitF; exact fI_inj
@[simp] theorem bitF_eq_fI_iff {k : ℕ} {l : Bool × ℕ} {i : ℕ} {v : Bool} :
    bitF l i v = fI k ↔ kBit l i v = k := by unfold bitF; exact fI_inj
@[simp] theorem bitF_ne_fSt (l : Bool × ℕ) (i : ℕ) (v : Bool) (w : ℕ) : bitF l i v ≠ fSt w :=
  fI_ne_fSt _ _
@[simp] theorem fSt_ne_bitF (l : Bool × ℕ) (i : ℕ) (v : Bool) (w : ℕ) : fSt w ≠ bitF l i v :=
  fSt_ne_fI _ _
@[simp] theorem bitF_ne_fRoot (l : Bool × ℕ) (i : ℕ) (v : Bool) (c : ℕ) : bitF l i v ≠ fRoot c :=
  fI_ne_fRoot _ _
@[simp] theorem fRoot_ne_bitF (l : Bool × ℕ) (i : ℕ) (v : Bool) (c : ℕ) : fRoot c ≠ bitF l i v :=
  fRoot_ne_fI _ _
@[simp] theorem bitF_ne_fDone (l : Bool × ℕ) (i : ℕ) (v : Bool) : bitF l i v ≠ fDone :=
  fI_ne_fDone _
@[simp] theorem fDone_ne_bitF (l : Bool × ℕ) (i : ℕ) (v : Bool) : fDone ≠ bitF l i v :=
  fDone_ne_fI _

/-- Every number is a state fact, a bit fact, or neither. -/
theorem fact_cases (f : ℕ) :
    (∃ v, f = fSt v) ∨ (∃ l i b, f = bitF l i b) ∨
      ((∀ v, f ≠ fSt v) ∧ ∀ l i b, f ≠ bitF l i b) := by
  by_cases h1 : ∃ v, f = fSt v
  · exact Or.inl h1
  by_cases h2 : ∃ l i b, f = bitF l i b
  · exact Or.inr (Or.inl h2)
  push_neg at h1 h2
  exact Or.inr (Or.inr ⟨h1, h2⟩)

/-! ### Representation -/

/-- The state facts of a planning state. -/
def StP (σ : Finset ℕ) (f : ℕ) : Prop := ∃ v ∈ σ, f = fSt v

/-- The bit facts of the counters of a multiset of labels. -/
def BitP (L : List (Bool × ℕ)) (W : ℕ) (M : Multiset (Bool × ℕ)) (f : ℕ) : Prop :=
  ∃ l ∈ L, ∃ i < W, f = bitF l i ((M.count l).testBit i)

/-- **A table state represents an abstract configuration**, with control facts `C`. -/
def Rep (L : List (Bool × ℕ)) (W : ℕ) (σ : Finset ℕ) (M : Multiset (Bool × ℕ)) (C : ℕ → Prop)
    (s : List ℕ) : Prop :=
  (∀ x ∈ M, x ∈ L) ∧ (∀ l, M.count l < 2 ^ W) ∧ ∀ f, f ∈ s ↔ StP σ f ∨ C f ∨ BitP L W M f

/-- A control predicate that never holds of state facts or bit facts. -/
def CtlOK (C : ℕ → Prop) : Prop := (∀ v, ¬ C (fSt v)) ∧ ∀ l i b, ¬ C (bitF l i b)

theorem ctlOK_fI {k : ℕ} (hk : ∀ l i b, k ≠ kBit l i b) : CtlOK (· = fI k) :=
  ⟨fun v h => fSt_ne_fI _ _ h, fun l i b h => hk l i b (fI_eq_bitF_iff.1 h.symm)⟩

theorem ctlOK_idle : CtlOK (· = fI kIdle) := ctlOK_fI fun l i b => kIdle_ne_kBit l i b

theorem ctlOK_ctl (k p : ℕ) : CtlOK (· = fI (kCtl k p)) := ctlOK_fI fun l i b => kCtl_ne_kBit k p l i b

theorem ctlOK_done : CtlOK (· = fDone) :=
  ⟨fun v h => fSt_ne_fDone _ h, fun l i b h => bitF_ne_fDone l i b h⟩

@[simp] theorem stP_fSt {σ : Finset ℕ} {v : ℕ} : StP σ (fSt v) ↔ v ∈ σ := by
  simp [StP]

@[simp] theorem stP_bitF {σ : Finset ℕ} {l i b} : ¬ StP σ (bitF l i b) := by
  simp [StP]

theorem not_stP {σ : Finset ℕ} {f : ℕ} (hf : ∀ v, f ≠ fSt v) : ¬ StP σ f := by
  rintro ⟨v, -, rfl⟩; exact hf v rfl

@[simp] theorem bitP_fSt {L W M} {v : ℕ} : ¬ BitP L W M (fSt v) := by
  simp [BitP]

theorem bitP_bitF {L W M} {l i b} :
    BitP L W M (bitF l i b) ↔ l ∈ L ∧ i < W ∧ b = (M.count l).testBit i := by
  simp only [BitP, bitF_inj]
  constructor
  · rintro ⟨l', hl', i', hi', rfl, rfl, rfl⟩; exact ⟨hl', hi', rfl⟩
  · rintro ⟨hl, hi, rfl⟩; exact ⟨l, hl, i, hi, rfl, rfl, rfl⟩

theorem not_bitP {L W M} {f : ℕ} (hf : ∀ l i b, f ≠ bitF l i b) : ¬ BitP L W M f := by
  rintro ⟨l, -, i, -, rfl⟩; exact hf _ _ _ rfl

section Mem

variable {L : List (Bool × ℕ)} {W : ℕ} {σ : Finset ℕ} {M : Multiset (Bool × ℕ)} {C : ℕ → Prop}
  {s : List ℕ}

theorem Rep.mem_fSt (h : Rep L W σ M C s) (hC : CtlOK C) (v : ℕ) : fSt v ∈ s ↔ v ∈ σ := by
  rw [h.2.2]; simp [hC.1 v]

theorem Rep.mem_bitF (h : Rep L W σ M C s) (hC : CtlOK C) (l : Bool × ℕ) (i : ℕ) (b : Bool) :
    bitF l i b ∈ s ↔ l ∈ L ∧ i < W ∧ b = (M.count l).testBit i := by
  rw [h.2.2, bitP_bitF]; simp [hC.2 l i b]

theorem Rep.mem_other (h : Rep L W σ M C s) {f : ℕ} (hf1 : ∀ v, f ≠ fSt v)
    (hf2 : ∀ l i b, f ≠ bitF l i b) : f ∈ s ↔ C f := by
  rw [h.2.2]; simp [not_stP hf1, not_bitP hf2]

/-- **Building a representation** from the three fact shapes. -/
theorem rep_of (hsupp : ∀ x ∈ M, x ∈ L) (hcnt : ∀ l, M.count l < 2 ^ W) (hC : CtlOK C)
    (h1 : ∀ v, fSt v ∈ s ↔ v ∈ σ)
    (h2 : ∀ l i b, bitF l i b ∈ s ↔ l ∈ L ∧ i < W ∧ b = (M.count l).testBit i)
    (h3 : ∀ f, (∀ v, f ≠ fSt v) → (∀ l i b, f ≠ bitF l i b) → (f ∈ s ↔ C f)) :
    Rep L W σ M C s := by
  refine ⟨hsupp, hcnt, fun f => ?_⟩
  rcases fact_cases f with ⟨v, rfl⟩ | ⟨l, i, b, rfl⟩ | ⟨hf1, hf2⟩
  · rw [h1]; simp [hC.1 v]
  · rw [h2, bitP_bitF]; simp [hC.2 l i b]
  · rw [h3 f hf1 hf2]; simp [not_stP hf1, not_bitP hf2]

end Mem

/-! ### Bit patterns -/

theorem mem_lowF {l : Bool × ℕ} {i : ℕ} {v : Bool} {f : ℕ} :
    f ∈ lowF l i v ↔ ∃ j < i, f = bitF l j v := by
  simp [lowF, eq_comm]

theorem bitF_mem_lowF {l l' : Bool × ℕ} {i j : ℕ} {v v' : Bool} :
    bitF l' j v' ∈ lowF l i v ↔ l' = l ∧ j < i ∧ v' = v := by
  rw [mem_lowF]
  constructor
  · rintro ⟨j', hj', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := bitF_inj.1 h
    exact ⟨rfl, hj', rfl⟩
  · rintro ⟨rfl, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem bitF_mem_decPre {l l' : Bool × ℕ} {i j : ℕ} {v' : Bool} :
    bitF l' j v' ∈ decPre l i ↔ l' = l ∧ ((j = i ∧ v' = true) ∨ (j < i ∧ v' = false)) := by
  simp only [decPre, List.mem_cons, bitF_inj, bitF_mem_lowF]
  tauto

theorem bitF_mem_decAdd {l l' : Bool × ℕ} {i j : ℕ} {v' : Bool} :
    bitF l' j v' ∈ decAdd l i ↔ l' = l ∧ ((j = i ∧ v' = false) ∨ (j < i ∧ v' = true)) := by
  simp only [decAdd, List.mem_cons, bitF_inj, bitF_mem_lowF]
  tauto

theorem mem_decPre_shape {l : Bool × ℕ} {i f : ℕ} (h : f ∈ decPre l i) :
    ∃ j b, f = bitF l j b := by
  simp only [decPre, List.mem_cons, mem_lowF] at h
  rcases h with rfl | ⟨j, -, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem mem_decAdd_shape {l : Bool × ℕ} {i f : ℕ} (h : f ∈ decAdd l i) :
    ∃ j b, f = bitF l j b := by
  simp only [decAdd, List.mem_cons, mem_lowF] at h
  rcases h with rfl | ⟨j, -, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem not_mem_decPre_of {l : Bool × ℕ} {i f : ℕ} (hf : ∀ j b, f ≠ bitF l j b) :
    f ∉ decPre l i := fun h => by
  obtain ⟨j, b, rfl⟩ := mem_decPre_shape h; exact hf j b rfl

theorem not_mem_decAdd_of {l : Bool × ℕ} {i f : ℕ} (hf : ∀ j b, f ≠ bitF l j b) :
    f ∉ decAdd l i := fun h => by
  obtain ⟨j, b, rfl⟩ := mem_decAdd_shape h; exact hf j b rfl

/-- The pattern `decPre l i` is present iff `i` is the lowest one bit of the counter of `l`. -/
theorem decPre_sub_iff {L W σ M C s} (h : Rep L W σ M C s) (hC : CtlOK C) (l : Bool × ℕ)
    (i : ℕ) :
    (∀ f ∈ decPre l i, f ∈ s) ↔ l ∈ L ∧ i < W ∧ (∀ j < i, (M.count l).testBit j = false) ∧
      (M.count l).testBit i = true := by
  constructor
  · intro H
    have h0 := (h.mem_bitF hC l i true).1 (H _ (by simp [decPre]))
    refine ⟨h0.1, h0.2.1, fun j hj => ?_, h0.2.2.symm⟩
    have := (h.mem_bitF hC l j false).1 (H _ (by simp only [decPre, List.mem_cons, mem_lowF]; exact Or.inr ⟨j, hj, rfl⟩))
    exact this.2.2.symm
  · rintro ⟨hl, hi, hlow, hb⟩ f hf
    simp only [decPre, List.mem_cons, mem_lowF] at hf
    rcases hf with rfl | ⟨j, hj, rfl⟩
    · exact (h.mem_bitF hC _ _ _).2 ⟨hl, hi, hb.symm⟩
    · exact (h.mem_bitF hC _ _ _).2 ⟨hl, by omega, (hlow j hj).symm⟩

/-- The pattern `decAdd l i` is present iff `i` is the lowest zero bit of the counter of `l`. -/
theorem decAdd_sub_iff {L W σ M C s} (h : Rep L W σ M C s) (hC : CtlOK C) (l : Bool × ℕ)
    (i : ℕ) :
    (∀ f ∈ decAdd l i, f ∈ s) ↔ l ∈ L ∧ i < W ∧ (∀ j < i, (M.count l).testBit j = true) ∧
      (M.count l).testBit i = false := by
  constructor
  · intro H
    have h0 := (h.mem_bitF hC l i false).1 (H _ (by simp [decAdd]))
    refine ⟨h0.1, h0.2.1, fun j hj => ?_, h0.2.2.symm⟩
    have := (h.mem_bitF hC l j true).1 (H _ (by simp only [decAdd, List.mem_cons, mem_lowF]; exact Or.inr ⟨j, hj, rfl⟩))
    exact this.2.2.symm
  · rintro ⟨hl, hi, hlow, hb⟩ f hf
    simp only [decAdd, List.mem_cons, mem_lowF] at hf
    rcases hf with rfl | ⟨j, hj, rfl⟩
    · exact (h.mem_bitF hC _ _ _).2 ⟨hl, hi, hb.symm⟩
    · exact (h.mem_bitF hC _ _ _).2 ⟨hl, by omega, (hlow j hj).symm⟩

/-- **Decrement, on bit facts.** -/
theorem bit_dec_iff {L : List (Bool × ℕ)} {W : ℕ} {M : Multiset (Bool × ℕ)} {l : Bool × ℕ}
    {i : ℕ} (hl : l ∈ L) (hi : i < W) (hlow : ∀ j < i, (M.count l).testBit j = false)
    (hb : (M.count l).testBit i = true) (l' : Bool × ℕ) (j : ℕ) (b : Bool) :
    (bitF l' j b ∈ decAdd l i ∨
        ((l' ∈ L ∧ j < W ∧ b = (M.count l').testBit j) ∧ bitF l' j b ∉ decPre l i)) ↔
      (l' ∈ L ∧ j < W ∧ b = ((M.erase l).count l').testBit j) := by
  rw [bitF_mem_decAdd, bitF_mem_decPre]
  by_cases hl' : l' = l
  · subst hl'
    rw [Multiset.count_erase_self, Counter.testBit_pred_of_low_one i _ hlow hb j]
    rcases lt_trichotomy j i with hj | rfl | hj
    · have := hlow j hj
      cases b <;> simp [hj, hl, this, show j < W by omega, show j ≠ i by omega]
    · cases b <;> simp [hl, hi, hb]
    · cases b <;> simp [show ¬ j < i by omega, show j ≠ i by omega]
  · rw [Multiset.count_erase_of_ne hl']
    simp [hl']

/-- **Increment, on bit facts.** -/
theorem bit_inc_iff {L : List (Bool × ℕ)} {W : ℕ} {M : Multiset (Bool × ℕ)} {l : Bool × ℕ}
    {i : ℕ} (hl : l ∈ L) (hi : i < W) (hlow : ∀ j < i, (M.count l).testBit j = true)
    (hb : (M.count l).testBit i = false) (l' : Bool × ℕ) (j : ℕ) (b : Bool) :
    (bitF l' j b ∈ decPre l i ∨
        ((l' ∈ L ∧ j < W ∧ b = (M.count l').testBit j) ∧ bitF l' j b ∉ decAdd l i)) ↔
      (l' ∈ L ∧ j < W ∧ b = ((l ::ₘ M).count l').testBit j) := by
  rw [bitF_mem_decAdd, bitF_mem_decPre]
  by_cases hl' : l' = l
  · subst hl'
    rw [Multiset.count_cons_self, Counter.testBit_succ_of_low_zero i _ hlow hb j]
    rcases lt_trichotomy j i with hj | rfl | hj
    · have := hlow j hj
      cases b <;> simp [hj, hl, this, show j < W by omega, show j ≠ i by omega]
    · cases b <;> simp [hl, hi, hb]
    · cases b <;> simp [show ¬ j < i by omega, show j ≠ i by omega]
  · rw [Multiset.count_cons_of_ne hl']
    simp [hl']

/-- An increment at the lowest zero bit below `W` stays below `2 ^ W`. -/
theorem succ_lt_of_low_zero {n W i : ℕ} (hn : n < 2 ^ W) (hi : i < W)
    (hlow : ∀ j < i, n.testBit j = true) (hb : n.testBit i = false) : n + 1 < 2 ^ W := by
  refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
  rw [Counter.testBit_succ_of_low_zero i n hlow hb j]
  simp [show ¬ j < i by omega, show j ≠ i by omega, Counter.testBit_eq_false_of_lt_pow hn hj]

end UOTbl

end HTN
