import HtnComplexity.UOSpace.TblRep
/-!
# The rows of the unordered-HTN action table, one by one

For every kind of row of `HTN.UOTbl.uoTbl d W` we prove

* when it is applicable in a represented state (`*_pre`), and
* which configuration the successor state represents (`*_post`).

These lemmas serve both directions of the simulation (`HtnComplexity/UOSpace/TblSim.lean`).
-/

namespace HTN

namespace UOTbl

open Syn Space

/-! ### Applying a row -/

/-- The canonical successor of a state under a row. -/
def applyRow (r : Row) (s : List ℕ) : List ℕ := r.2.1 ++ s.filter (fun f => decide (f ∉ r.2.2))

theorem mem_applyRow {r : Row} {s : List ℕ} {f : ℕ} :
    f ∈ applyRow r s ↔ f ∈ r.2.1 ∨ (f ∈ s ∧ f ∉ r.2.2) := by
  simp [applyRow]

theorem stepTbl_applyRow {tbl : List Row} {r : Row} {s : List ℕ} (hr : r ∈ tbl)
    (hpre : ∀ f ∈ r.1, f ∈ s) : StepTbl tbl s (applyRow r s) :=
  ⟨r, hr, hpre, fun _ => mem_applyRow⟩

/-! ### Control facts in a represented state -/

section Ctl

variable {L : List (Bool × ℕ)} {W : ℕ} {σ : Finset ℕ} {M : Multiset (Bool × ℕ)} {C : ℕ → Prop}
  {s : List ℕ}

theorem Rep.mem_fI (h : Rep L W σ M C s) {k : ℕ} (hk : ∀ l i b, k ≠ kBit l i b) :
    fI k ∈ s ↔ C (fI k) :=
  h.mem_other (fun v => fI_ne_fSt _ _) (fun l i b he => hk l i b (fI_eq_bitF_iff.1 he))

theorem Rep.mem_idle (h : Rep L W σ M C s) : fI kIdle ∈ s ↔ C (fI kIdle) :=
  h.mem_fI (kIdle_ne_kBit)

theorem Rep.mem_ctl (h : Rep L W σ M C s) (k p : ℕ) : fI (kCtl k p) ∈ s ↔ C (fI (kCtl k p)) :=
  h.mem_fI (kCtl_ne_kBit k p)

theorem Rep.mem_root (h : Rep L W σ M C s) (c : ℕ) : fRoot c ∈ s ↔ C (fRoot c) :=
  h.mem_other (fun v => fRoot_ne_fSt _ _) (fun l i b => fRoot_ne_bitF l i b c)

theorem Rep.mem_done (h : Rep L W σ M C s) : fDone ∈ s ↔ C fDone :=
  h.mem_other (fun v => fDone_ne_fSt _) (fun l i b => fDone_ne_bitF l i b)

end Ctl

theorem fSt_not_mem_decPre {l : Bool × ℕ} {i v : ℕ} : fSt v ∉ decPre l i :=
  not_mem_decPre_of fun j b => fSt_ne_bitF _ _ _ _

theorem fSt_not_mem_decAdd {l : Bool × ℕ} {i v : ℕ} : fSt v ∉ decAdd l i :=
  not_mem_decAdd_of fun j b => fSt_ne_bitF _ _ _ _

theorem fI_not_mem_decPre {l : Bool × ℕ} {i k : ℕ} (hk : ∀ l i b, k ≠ kBit l i b) :
    fI k ∉ decPre l i :=
  not_mem_decPre_of fun j b he => hk _ _ _ (fI_eq_bitF_iff.1 he)

theorem fI_not_mem_decAdd {l : Bool × ℕ} {i k : ℕ} (hk : ∀ l i b, k ≠ kBit l i b) :
    fI k ∉ decAdd l i :=
  not_mem_decAdd_of fun j b he => hk _ _ _ (fI_eq_bitF_iff.1 he)

theorem bitF_not_mem_map_fSt {l : Bool × ℕ} {i : ℕ} {b : Bool} {xs : List ℕ} :
    bitF l i b ∉ xs.map fSt := by
  simp

theorem mem_map_fSt {v : ℕ} {xs : List ℕ} : fSt v ∈ xs.map fSt ↔ v ∈ xs := by
  simp

theorem not_mem_map_fSt {f : ℕ} {xs : List ℕ} (hf : ∀ v, f ≠ fSt v) : f ∉ xs.map fSt := by
  simp only [List.mem_map, not_exists, not_and]
  exact fun v _ he => hf v he.symm

/-! ### Execute -/

/-- The successor planning state of `HTN.Syn.uoSys`. -/
def nxtSt (d : DomDesc) (σ : Finset ℕ) (a : ℕ) : Finset ℕ :=
  σ.filter (fun f => f ∉ (actOf d a).2.2) ∪ (actOf d a).2.1.toFinset

theorem exe_pre {L W σ M C s} (h : Rep L W σ M C s) (hC : CtlOK C) (d : DomDesc)
    (l : Bool × ℕ) (i : ℕ) :
    (∀ f ∈ (exeRow d l i).1, f ∈ s) ↔ C (fI kIdle) ∧
      (l ∈ L ∧ i < W ∧ (∀ j < i, (M.count l).testBit j = false) ∧ (M.count l).testBit i = true) ∧
      ∀ f ∈ (actOf d l.2).1, f ∈ σ := by
  simp only [exeRow, List.mem_cons, List.mem_append, forall_eq_or_imp, or_imp, forall_and,
    h.mem_idle, List.mem_map, forall_exists_index, and_imp]
  rw [decPre_sub_iff h hC]
  simp only [forall_apply_eq_imp_iff₂, h.mem_fSt hC, forall_eq, h.mem_idle]
  tauto

theorem exe_post {L W σ M s s'} (h : Rep L W σ M (· = fI kIdle) s) (d : DomDesc)
    {l : Bool × ℕ} {i : ℕ} (hl : l ∈ L) (hi : i < W)
    (hlow : ∀ j < i, (M.count l).testBit j = false) (hb : (M.count l).testBit i = true)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (exeRow d l i).2.1 ∨ (f ∈ s ∧ f ∉ (exeRow d l i).2.2)) :
    Rep L W (nxtSt d σ l.2) (M.erase l) (· = fI kIdle) s' := by
  refine rep_of (fun x hx => h.1 x (Multiset.mem_of_mem_erase hx))
    (fun l' => lt_of_le_of_lt (Multiset.count_le_of_le _ (Multiset.erase_le _ _)) (h.2.1 l'))
    ctlOK_idle (fun v => ?_) (fun l' j b => ?_) (fun f hf1 hf2 => ?_)
  · rw [hs']
    simp only [exeRow, List.mem_append, fSt_not_mem_decAdd, fSt_not_mem_decPre, false_or,
      mem_map_fSt, h.mem_fSt ctlOK_idle, nxtSt, Finset.mem_union, Finset.mem_filter,
      List.mem_toFinset]
    tauto
  · rw [hs']
    simp only [exeRow, List.mem_append, bitF_not_mem_map_fSt, or_false,
      h.mem_bitF ctlOK_idle]
    exact bit_dec_iff hl hi hlow hb l' j b
  · rw [hs']
    simp only [exeRow, List.mem_append, not_mem_decAdd_of (fun j b => hf2 l j b),
      not_mem_decPre_of (fun j b => hf2 l j b), not_mem_map_fSt hf1, or_self, false_or,
      not_false_eq_true, and_true, h.mem_other hf1 hf2]

/-! ### Decompose: start -/

theorem dec_pre {L W σ M C s} (h : Rep L W σ M C s) (hC : CtlOK C) (k : ℕ) (e : MethodDesc)
    (i : ℕ) :
    (∀ f ∈ (decRow k e i).1, f ∈ s) ↔ C (fI kIdle) ∧
      ((true, e.1) ∈ L ∧ i < W ∧ (∀ j < i, (M.count (true, e.1)).testBit j = false) ∧
        (M.count (true, e.1)).testBit i = true) := by
  simp only [decRow, List.mem_cons, forall_eq_or_imp, h.mem_idle]
  rw [← decPre_sub_iff h hC]

theorem dec_post {L W σ M s s'} (h : Rep L W σ M (· = fI kIdle) s) (k : ℕ) (e : MethodDesc)
    {i : ℕ} (hl : (true, e.1) ∈ L) (hi : i < W)
    (hlow : ∀ j < i, (M.count (true, e.1)).testBit j = false)
    (hb : (M.count (true, e.1)).testBit i = true)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (decRow k e i).2.1 ∨ (f ∈ s ∧ f ∉ (decRow k e i).2.2)) :
    Rep L W σ (M.erase (true, e.1)) (· = fI (kCtl k 0)) s' := by
  refine rep_of (fun x hx => h.1 x (Multiset.mem_of_mem_erase hx))
    (fun l' => lt_of_le_of_lt (Multiset.count_le_of_le _ (Multiset.erase_le _ _)) (h.2.1 l'))
    (ctlOK_ctl k 0) (fun v => ?_) (fun l' j b => ?_) (fun f hf1 hf2 => ?_)
  · rw [hs']
    simp [decRow, fSt_not_mem_decAdd, fSt_not_mem_decPre, h.mem_fSt ctlOK_idle]
  · rw [hs']
    simp only [decRow, List.mem_cons, bitF_eq_fI_iff, kBit_ne_kCtl, kBit_ne_kIdle, false_or,
      h.mem_bitF ctlOK_idle, not_or, true_and]
    exact bit_dec_iff hl hi hlow hb l' j b
  · rw [hs']
    simp only [decRow, List.mem_cons, not_mem_decAdd_of (fun j b => hf2 _ j b),
      not_mem_decPre_of (fun j b => hf2 _ j b), or_false, h.mem_other hf1 hf2, not_or]
    tauto

/-! ### Decompose: add a subtask -/

theorem add_pre {L W σ M C s} (h : Rep L W σ M C s) (hC : CtlOK C) (k p : ℕ) (l : Bool × ℕ)
    (i : ℕ) :
    (∀ f ∈ (addRow k p l i).1, f ∈ s) ↔ C (fI (kCtl k p)) ∧
      (l ∈ L ∧ i < W ∧ (∀ j < i, (M.count l).testBit j = true) ∧
        (M.count l).testBit i = false) := by
  simp only [addRow, List.mem_cons, forall_eq_or_imp, h.mem_ctl]
  rw [← decAdd_sub_iff h hC]

theorem add_post {L W σ M s s'} {k p : ℕ} (h : Rep L W σ M (· = fI (kCtl k p)) s)
    {l : Bool × ℕ} {i : ℕ} (hl : l ∈ L) (hi : i < W)
    (hlow : ∀ j < i, (M.count l).testBit j = true) (hb : (M.count l).testBit i = false)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (addRow k p l i).2.1 ∨ (f ∈ s ∧ f ∉ (addRow k p l i).2.2)) :
    Rep L W σ (l ::ₘ M) (· = fI (kCtl k (p + 1))) s' := by
  refine rep_of (fun x hx => ?_) (fun l' => ?_)
    (ctlOK_ctl k (p + 1)) (fun v => ?_) (fun l' j b => ?_) (fun f hf1 hf2 => ?_)
  · rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact hl
    · exact h.1 x hx
  · by_cases hl' : l' = l
    · subst hl'
      rw [Multiset.count_cons_self]
      exact succ_lt_of_low_zero (h.2.1 _) hi hlow hb
    · rw [Multiset.count_cons_of_ne hl']; exact h.2.1 l'
  · rw [hs']
    simp [addRow, fSt_not_mem_decAdd, fSt_not_mem_decPre, h.mem_fSt (ctlOK_ctl k p)]
  · rw [hs']
    simp only [addRow, List.mem_cons, bitF_eq_fI_iff, kBit_ne_kCtl, false_or,
      h.mem_bitF (ctlOK_ctl k p), not_or, true_and]
    exact bit_inc_iff hl hi hlow hb l' j b
  · rw [hs']
    simp only [addRow, List.mem_cons, not_mem_decAdd_of (fun j b => hf2 _ j b),
      not_mem_decPre_of (fun j b => hf2 _ j b), or_false, h.mem_other hf1 hf2, not_or]
    tauto

/-! ### Decompose: end -/

theorem end_pre {L W σ M C s} (h : Rep L W σ M C s) (k n : ℕ) :
    (∀ f ∈ (endRow k n).1, f ∈ s) ↔ C (fI (kCtl k n)) := by
  simp [endRow, h.mem_ctl]

theorem end_post {L W σ M s s'} {k n : ℕ} (h : Rep L W σ M (· = fI (kCtl k n)) s)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (endRow k n).2.1 ∨ (f ∈ s ∧ f ∉ (endRow k n).2.2)) :
    Rep L W σ M (· = fI kIdle) s' := by
  refine rep_of h.1 h.2.1 ctlOK_idle (fun v => ?_) (fun l' j b => ?_) (fun f hf1 hf2 => ?_)
  · rw [hs']; simp [endRow, h.mem_fSt (ctlOK_ctl k n)]
  · rw [hs']; simp [endRow, h.mem_bitF (ctlOK_ctl k n)]
  · rw [hs']
    simp only [endRow, List.mem_cons, List.not_mem_nil, or_false, h.mem_other hf1 hf2]
    tauto

/-! ### Finish -/

theorem mem_zerosAll {L : List (Bool × ℕ)} {W : ℕ} {l : Bool × ℕ} {j : ℕ} {b : Bool} :
    bitF l j b ∈ zerosAll L W ↔ l ∈ L ∧ j < W ∧ b = false := by
  simp only [zerosAll, List.mem_flatMap, List.mem_map, List.mem_range, bitF_inj]
  constructor
  · rintro ⟨l', hl', j', hj', rfl, rfl, rfl⟩; exact ⟨hl', hj', rfl⟩
  · rintro ⟨hl, hj, rfl⟩; exact ⟨l, hl, j, hj, rfl, rfl, rfl⟩

theorem mem_zerosAll_shape {L : List (Bool × ℕ)} {W f : ℕ} (h : f ∈ zerosAll L W) :
    ∃ l j b, f = bitF l j b := by
  simp only [zerosAll, List.mem_flatMap, List.mem_map] at h
  obtain ⟨l, -, j, -, rfl⟩ := h
  exact ⟨_, _, _, rfl⟩

theorem fin_pre {L W σ M C s} (h : Rep L W σ M C s) (hC : CtlOK C) :
    (∀ f ∈ (finRow L W).1, f ∈ s) ↔ C (fI kIdle) ∧ ∀ l ∈ L, M.count l = 0 := by
  simp only [finRow, List.mem_cons, forall_eq_or_imp, h.mem_idle]
  apply and_congr Iff.rfl
  constructor
  · intro H l hl
    refine Counter.eq_of_testBit_lt (h.2.1 l) (by positivity) fun j hj => ?_
    have := (h.mem_bitF hC l j false).1 (H _ (mem_zerosAll.2 ⟨hl, hj, rfl⟩))
    simpa using this.2.2.symm
  · intro H f hf
    obtain ⟨l, j, b, rfl⟩ := mem_zerosAll_shape hf
    obtain ⟨hl, hj, rfl⟩ := mem_zerosAll.1 hf
    exact (h.mem_bitF hC l j false).2 ⟨hl, hj, by simp [H l hl]⟩

theorem fin_post {L W σ M s s'} (h : Rep L W σ M (· = fI kIdle) s)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (finRow L W).2.1 ∨ (f ∈ s ∧ f ∉ (finRow L W).2.2)) :
    Rep L W σ M (· = fDone) s' := by
  refine rep_of h.1 h.2.1 ctlOK_done (fun v => ?_) (fun l' j b => ?_) (fun f hf1 hf2 => ?_)
  · rw [hs']; simp [finRow, h.mem_fSt ctlOK_idle]
  · rw [hs']; simp [finRow, h.mem_bitF ctlOK_idle]
  · rw [hs']
    simp only [finRow, List.mem_cons, List.not_mem_nil, or_false, h.mem_other hf1 hf2]
    tauto

/-! ### Start -/

theorem start_pre {s : List ℕ} {σ : Finset ℕ} {c₀ : ℕ}
    (hs : ∀ f, f ∈ s ↔ StP σ f ∨ f = fRoot c₀) (L : List (Bool × ℕ)) (W c : ℕ) :
    (∀ f ∈ (startRow L W c).1, f ∈ s) ↔ c = c₀ := by
  simp [startRow, hs, StP]

theorem start_post {s s' : List ℕ} {σ : Finset ℕ} {L : List (Bool × ℕ)} {W c : ℕ}
    (hs : ∀ f, f ∈ s ↔ StP σ f ∨ f = fRoot c) (hL : (true, c) ∈ L) (hW : 0 < W)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (startRow L W c).2.1 ∨ (f ∈ s ∧ f ∉ (startRow L W c).2.2)) :
    Rep L W σ {(true, c)} (· = fI kIdle) s' := by
  refine rep_of (fun x hx => ?_) (fun l' => ?_) ctlOK_idle (fun v => ?_) (fun l' j b => ?_)
    (fun f hf1 hf2 => ?_)
  · rw [Multiset.mem_singleton.1 hx]; exact hL
  · rw [Multiset.count_singleton]
    split_ifs
    · exact Nat.one_lt_two_pow (by omega)
    · positivity
  · rw [hs']
    simp only [startRow, List.mem_cons, List.mem_filter, fSt_ne_fI, fSt_ne_bitF, false_or, hs,
      stP_fSt, fSt_ne_fRoot, or_false, List.not_mem_nil, not_false_eq_true, and_true]
    constructor
    · rintro (⟨hz, -⟩ | h)
      · obtain ⟨l, j, b, he⟩ := mem_zerosAll_shape hz
        exact absurd he (fSt_ne_bitF _ _ _ _)
      · exact h
    · exact Or.inr
  · rw [hs']
    simp only [startRow, List.mem_cons, List.mem_filter, bitF_eq_fI_iff, kBit_ne_kIdle,
      bitF_inj, false_or, hs, stP_bitF, bitF_ne_fRoot, or_false, false_and, decide_eq_true_eq,
      ne_eq, mem_zerosAll, Multiset.count_singleton]
    by_cases hl : l' = (true, c)
    · subst hl
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · cases b <;> simp [hL, hW]
      · have h1 : Nat.testBit 1 j = false :=
          Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))
        cases b <;> simp [hL, show j ≠ 0 by omega, h1]
    · cases b <;> simp [hl]
  · rw [hs']
    have hz : f ∉ zerosAll L W := fun hz => by
      obtain ⟨l, j, b, rfl⟩ := mem_zerosAll_shape hz; exact hf2 l j b rfl
    simp only [startRow, List.mem_cons, List.mem_filter, hz, false_and, or_false, hs,
      not_stP hf1, false_or, List.not_mem_nil]
    have := hf2 (true, c) 0 true
    tauto

end UOTbl

end HTN
