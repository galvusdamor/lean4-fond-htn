import HtnComplexity.Article.TOHardDesc
/-!
# The tableau-checking problem: the actions on counter states

What each action of `HTN.Article.TabData.desc` does in a state `HTN.Article.cntS B t i`, as a
refinement of its name (`HTN.Article.RefT`): setting and clearing bits (adding and subtracting
powers of two), testing `t = 0`, `i = c`, and the comparisons of `i` with a constant through a
bit `j` (`i` agrees with the constant above `j` and has bit `j` set, resp. unset).
-/

namespace HTN

namespace Article

open Syn PTime

theorem applicable_iff (a : ActDesc) (s : Set ℕ) :
    a.toAction.Applicable s ↔ (∀ f ∈ a.2.1, f ∈ s) ∧ ∀ f ∈ a.2.2.1, f ∉ s := by
  simp only [Action.Applicable, ActDesc.toAction, Set.subset_def, Set.mem_setOf_eq,
    Set.disjoint_left]

theorem apply_eq (a : ActDesc) (s : Set ℕ) :
    a.toAction.apply s = (s \ {f | f ∈ a.2.2.2.2}) ∪ {f | f ∈ a.2.2.2.1} := rfl

theorem actOf_aN (B c₁ c₂ : ℕ) {k : ℕ} (hk : k < 16) (p : ℕ) : actOf B c₁ c₂ (aN k p) =
    if k = 0 then (aN k p, [], [p], [p], [])
    else if k = 1 then (aN k p, [p], [], [], [p])
    else if k = 3 then (aN k p, eqPos B p, eqNeg B p, [], [])
    else if k = 4 then (aN k p, [], (List.range B).map tF, [], [])
    else if k = 5 then (aN k p, iF p :: abPos B c₁ p, abNeg B c₁ p, [], [])
    else if k = 6 then (aN k p, iF p :: abPos B c₂ p, abNeg B c₂ p, [], [])
    else if k = 7 then (aN k p, abPos B c₂ p, iF p :: abNeg B c₂ p, [], [])
    else (aN k p, [], [], [], []) := by
  unfold actOf
  rw [aN_mod hk, aN_div hk]

theorem mem_eqPos {B c f : ℕ} : f ∈ eqPos B c ↔ ∃ m < B, c.testBit m = true ∧ f = iF m := by
  simp only [eqPos, List.mem_map, List.mem_filter, List.mem_range, bit_eq]
  constructor
  · rintro ⟨m, ⟨hm, hb⟩, rfl⟩; exact ⟨m, hm, hb, rfl⟩
  · rintro ⟨m, hm, hb, rfl⟩; exact ⟨m, ⟨hm, hb⟩, rfl⟩

theorem mem_eqNeg {B c f : ℕ} : f ∈ eqNeg B c ↔ ∃ m < B, c.testBit m = false ∧ f = iF m := by
  simp only [eqNeg, List.mem_map, List.mem_filter, List.mem_range, bit_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨m, ⟨hm, hb⟩, rfl⟩; exact ⟨m, hm, hb, rfl⟩
  · rintro ⟨m, hm, hb, rfl⟩; exact ⟨m, ⟨hm, hb⟩, rfl⟩

theorem mem_abPos {B c j f : ℕ} :
    f ∈ abPos B c j ↔ ∃ m < B, j < m ∧ c.testBit m = true ∧ f = iF m := by
  simp only [abPos, List.mem_map, List.mem_filter, List.mem_range, bit_eq, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨m, ⟨hm, hj, hb⟩, rfl⟩; exact ⟨m, hm, hj, hb, rfl⟩
  · rintro ⟨m, hm, hj, hb, rfl⟩; exact ⟨m, ⟨hm, hj, hb⟩, rfl⟩

theorem mem_abNeg {B c j f : ℕ} :
    f ∈ abNeg B c j ↔ ∃ m < B, j < m ∧ c.testBit m = false ∧ f = iF m := by
  simp only [abNeg, List.mem_map, List.mem_filter, List.mem_range, bit_eq, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨m, ⟨hm, hj, hb⟩, rfl⟩; exact ⟨m, hm, hj, hb, rfl⟩
  · rintro ⟨m, hm, hj, hb, rfl⟩; exact ⟨m, ⟨hm, hj, hb⟩, rfl⟩

/-- Agreement with `c` above `j`, as the preconditions `abPos`, `abNeg`. -/
theorem above_iff {B c j t i : ℕ} :
    ((∀ f ∈ abPos B c j, f ∈ cntS B t i) ∧ ∀ f ∈ abNeg B c j, f ∉ cntS B t i) ↔
      ∀ m, j < m → m < B → i.testBit m = c.testBit m := by
  simp only [mem_abPos, mem_abNeg]
  constructor
  · rintro ⟨h1, h2⟩ m hjm hm
    rcases hc : c.testBit m
    · have := h2 _ ⟨m, hm, hjm, hc, rfl⟩
      rw [mem_cntS_iF] at this
      simpa [hm] using this
    · exact ((mem_cntS_iF).1 (h1 _ ⟨m, hm, hjm, hc, rfl⟩)).2
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨m, hm, hjm, hc, rfl⟩
      exact (mem_cntS_iF).2 ⟨hm, (h m hjm hm).trans hc⟩
    · rintro _ ⟨m, hm, hjm, hc, rfl⟩ hmem
      have := ((mem_cntS_iF).1 hmem).2
      rw [h m hjm hm, hc] at this
      exact absurd this (by simp)

namespace TabData

variable (d : TabData)

theorem refT_act {n : ℕ} (hn : n ∈ actNames d.B d.c₁ d.c₂ d.mx) {s s' : Set ℕ} :
    RefT d.desc (Sum.inl n) s s' ↔
      (actOf d.B d.c₁ d.c₂ n).toAction.Applicable s ∧ s' = (actOf d.B d.c₁ d.c₂ n).toAction.apply s := by
  rw [refT_inl_iff, d.δ_desc hn]

theorem refT_setT {j t i : ℕ} (hj : j < d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (setN (tF j))) (cntS d.B t i) s' ↔
      t.testBit j = false ∧ s' = cntS d.B (t + 2 ^ j) i := by
  rw [d.refT_act (d.setN_mem (tF_lt hj)), applicable_iff, apply_eq, setN, actOf_aN _ _ _ (by norm_num)]
  simp only [if_true, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.mem_singleton,
    forall_eq, true_and, Set.setOf_false, Set.diff_empty, Set.setOf_eq_eq_singleton, mem_cntS_tF,
    hj, not_and, Bool.not_eq_true, forall_const]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, cntS_insert_tF hj h⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, (cntS_insert_tF hj h).symm⟩

theorem refT_clrT {j t i : ℕ} (hj : j < d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (clrN (tF j))) (cntS d.B t i) s' ↔
      t.testBit j = true ∧ s' = cntS d.B (t - 2 ^ j) i := by
  rw [d.refT_act (d.clrN_mem (tF_lt hj)), applicable_iff, apply_eq, clrN, actOf_aN _ _ _ (by norm_num)]
  simp only [show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true, List.mem_singleton, forall_eq,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Set.setOf_eq_eq_singleton,
    Set.setOf_false, Set.union_empty, mem_cntS_tF, hj, true_and]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, cntS_diff_tF h⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, (cntS_diff_tF h).symm⟩

theorem refT_setI {j t i : ℕ} (hj : j < d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (setN (iF j))) (cntS d.B t i) s' ↔
      i.testBit j = false ∧ s' = cntS d.B t (i + 2 ^ j) := by
  rw [d.refT_act (d.setN_mem (iF_lt hj)), applicable_iff, apply_eq, setN, actOf_aN _ _ _ (by norm_num)]
  simp only [if_true, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.mem_singleton,
    forall_eq, true_and, Set.setOf_false, Set.diff_empty, Set.setOf_eq_eq_singleton, mem_cntS_iF,
    hj, not_and, Bool.not_eq_true, forall_const]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, cntS_insert_iF hj h⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, (cntS_insert_iF hj h).symm⟩

theorem refT_clrI {j t i : ℕ} (hj : j < d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (clrN (iF j))) (cntS d.B t i) s' ↔
      i.testBit j = true ∧ s' = cntS d.B t (i - 2 ^ j) := by
  rw [d.refT_act (d.clrN_mem (iF_lt hj)), applicable_iff, apply_eq, clrN, actOf_aN _ _ _ (by norm_num)]
  simp only [show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true, List.mem_singleton, forall_eq,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Set.setOf_eq_eq_singleton,
    Set.setOf_false, Set.union_empty, mem_cntS_iF, hj, true_and]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, cntS_diff_iF h⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, (cntS_diff_iF h).symm⟩

theorem refT_noop {s s' : Set ℕ} : RefT d.desc (Sum.inl noopN) s s' ↔ s' = s := by
  rw [d.refT_act d.noopN_mem, applicable_iff, apply_eq, noopN, actOf_aN _ _ _ (by norm_num)]
  simp

theorem refT_tz {t i : ℕ} (ht : t < 2 ^ d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl tzN) (cntS d.B t i) s' ↔ t = 0 ∧ s' = cntS d.B t i := by
  rw [d.refT_act d.tzN_mem, applicable_iff, apply_eq, tzN, actOf_aN _ _ _ (by norm_num)]
  simp only [show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num,
    show (4 : ℕ) ≠ 3 by norm_num, if_false, if_true, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, true_and, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_cntS_tF, not_and, Bool.not_eq_true, Set.setOf_false,
    Set.diff_empty, Set.union_empty]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨eq_of_bits ht (Nat.two_pow_pos _) fun m hm => by simp [h m hm hm], rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨fun m _ _ => by simp, rfl⟩

theorem refT_eq {c t i : ℕ} (hc : c < 2 ^ d.B) (hi : i < 2 ^ d.B)
    (hcm : c < d.c₁ ∨ c = d.c₁ ∨ c = d.c₂ ∨ c = d.mx) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (eqN c)) (cntS d.B t i) s' ↔ i = c ∧ s' = cntS d.B t i := by
  rw [d.refT_act (d.eqN_mem hcm), applicable_iff, apply_eq, eqN, actOf_aN _ _ _ (by norm_num)]
  simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, if_false, if_true,
    List.not_mem_nil, Set.setOf_false, Set.diff_empty, Set.union_empty]
  have key : ((∀ f ∈ eqPos d.B c, f ∈ cntS d.B t i) ∧ ∀ f ∈ eqNeg d.B c, f ∉ cntS d.B t i) ↔
      i = c := by
    simp only [mem_eqPos, mem_eqNeg]
    constructor
    · rintro ⟨h1, h2⟩
      refine eq_of_bits hi hc fun m hm => ?_
      rcases hcb : c.testBit m
      · have := h2 _ ⟨m, hm, hcb, rfl⟩
        rw [mem_cntS_iF] at this
        simpa [hm] using this
      · exact ((mem_cntS_iF).1 (h1 _ ⟨m, hm, hcb, rfl⟩)).2
    · rintro rfl
      refine ⟨?_, ?_⟩
      · rintro _ ⟨m, hm, hb, rfl⟩; exact (mem_cntS_iF).2 ⟨hm, hb⟩
      · rintro _ ⟨m, hm, hb, rfl⟩ h
        rw [mem_cntS_iF, hb] at h
        exact absurd h.2 (by simp)
  rw [key]

/-- The comparison actions: kind `5` (`> c₁` through bit `j`), `6` (`> c₂`), `7` (`< c₂`). -/
theorem refT_gt1 {j t i : ℕ} (hj : j < d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (gt1N j)) (cntS d.B t i) s' ↔
      (i.testBit j = true ∧ ∀ m, j < m → m < d.B → i.testBit m = d.c₁.testBit m) ∧
        s' = cntS d.B t i := by
  rw [d.refT_act (d.gtlt_mem hj).1, applicable_iff, apply_eq, gt1N, actOf_aN _ _ _ (by norm_num)]
  simp only [show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
    show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num, if_false, if_true,
    List.not_mem_nil, Set.setOf_false, Set.diff_empty, Set.union_empty, List.mem_cons,
    forall_eq_or_imp]
  rw [← above_iff (t := t), mem_cntS_iF]
  simp only [hj, true_and, and_assoc]

theorem refT_gt2 {j t i : ℕ} (hj : j < d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (gt2N j)) (cntS d.B t i) s' ↔
      (i.testBit j = true ∧ ∀ m, j < m → m < d.B → i.testBit m = d.c₂.testBit m) ∧
        s' = cntS d.B t i := by
  rw [d.refT_act (d.gtlt_mem hj).2.1, applicable_iff, apply_eq, gt2N, actOf_aN _ _ _ (by norm_num)]
  simp only [show (6 : ℕ) ≠ 0 by norm_num, show (6 : ℕ) ≠ 1 by norm_num,
    show (6 : ℕ) ≠ 3 by norm_num, show (6 : ℕ) ≠ 4 by norm_num, show (6 : ℕ) ≠ 5 by norm_num,
    if_false, if_true, List.not_mem_nil, Set.setOf_false, Set.diff_empty, Set.union_empty,
    List.mem_cons, forall_eq_or_imp]
  rw [← above_iff (t := t), mem_cntS_iF]
  simp only [hj, true_and, and_assoc]

theorem refT_lt2 {j t i : ℕ} (hj : j < d.B) {s' : Set ℕ} :
    RefT d.desc (Sum.inl (lt2N j)) (cntS d.B t i) s' ↔
      (i.testBit j = false ∧ ∀ m, j < m → m < d.B → i.testBit m = d.c₂.testBit m) ∧
        s' = cntS d.B t i := by
  rw [d.refT_act (d.gtlt_mem hj).2.2, applicable_iff, apply_eq, lt2N, actOf_aN _ _ _ (by norm_num)]
  simp only [show (7 : ℕ) ≠ 0 by norm_num, show (7 : ℕ) ≠ 1 by norm_num,
    show (7 : ℕ) ≠ 3 by norm_num, show (7 : ℕ) ≠ 4 by norm_num, show (7 : ℕ) ≠ 5 by norm_num,
    show (7 : ℕ) ≠ 6 by norm_num, if_false, if_true, List.not_mem_nil, Set.setOf_false,
    Set.diff_empty, Set.union_empty, List.mem_cons, forall_eq_or_imp]
  rw [mem_cntS_iF]
  constructor
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    refine ⟨⟨by simpa [hj] using h2.1, (above_iff).1 ⟨h1, h2.2⟩⟩, rfl⟩
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    have := (above_iff (t := t)).2 h2
    exact ⟨⟨this.1, by simp [h1], this.2⟩, rfl⟩

end TabData

end Article

end HTN
