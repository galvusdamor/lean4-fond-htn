import HtnComplexity.PolyInst.Enum
import HtnComplexity.PolyInst.Affine
/-!
# Comparing numerals in polynomial time

The totalisation of a task network orders its identifiers by `<`, so emitting it needs the
comparison of two numerals as a predicate of Cobham's class.  For bit strings `u`, `v` read least
significant bit first:

* if `u` is shorter than `v` (and both are numerals, i.e. without trailing zeros) then `u < v`;
* if they have the same length, `u < v` iff at the most significant position where they differ
  `u` has `0` and `v` has `1`: some suffix of `u` is `0 :: s` and the suffix of `v` of the same
  length is `1 :: s` (`HTN.Syn.PolyInst.ltEqLen`).

* `HTN.Syn.PolyInst.ltBits_bitsOfNat` — `ltBits (bitsOfNat a) (bitsOfNat b) = decide (a < b)`;
* `HTN.Syn.PolyInst.cobhamB_ltBits` — `ltBits` is a predicate of Cobham's class;
* `HTN.Syn.PolyInst.undbl_serNat` — the bits of a self-delimiting numeral are read off by `undbl`.
-/

namespace HTN

namespace Syn

namespace PolyInst

open PTime Compress TOPlan

/-- Comparison of two bit strings of the same length (least significant bit first). -/
def ltEqLen (u v : List Bool) : Bool :=
  u.tails.any fun s =>
    (!decide (s = []) && !s.headD false) && decide (v.drop (v.drop s.length).length = true :: s.tail)

/-- Comparison of two numerals (least significant bit first, no trailing zeros). -/
def ltBits (u v : List Bool) : Bool :=
  decide (u.length < v.length) || (decide (u.length = v.length) && ltEqLen u v)

/-- The proposition behind `ltEqLen`. -/
def LtEq (u v : List Bool) : Prop :=
  ∃ s ∈ u.tails, (s ≠ [] ∧ s.headD false = false) ∧ v.drop (v.length - s.length) = true :: s.tail

theorem ltEqLen_iff (u v : List Bool) : ltEqLen u v = true ↔ LtEq u v := by
  simp only [ltEqLen, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, List.length_drop, LtEq]

theorem ltEq_cons {x y : Bool} {u v : List Bool} (h : u.length = v.length) :
    LtEq (x :: u) (y :: v) ↔ (x = false ∧ y = true ∧ v = u) ∨ LtEq u v := by
  simp only [LtEq, List.tails_cons, List.mem_cons, exists_eq_or_imp]
  apply or_congr
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.headD_cons, true_and, List.length_cons,
      h, Nat.sub_self, List.drop_zero, List.cons.injEq, List.tail_cons]
  · refine exists_congr fun s => and_congr_right fun hs => ?_
    have hle : s.length ≤ v.length := h ▸ ((List.mem_tails _ _).1 hs).length_le
    rw [List.length_cons, show v.length + 1 - s.length = (v.length - s.length) + 1 by omega,
      List.drop_succ_cons]

theorem natOfBits_inj_of_length : ∀ {u v : List Bool}, u.length = v.length →
    natOfBits u = natOfBits v → u = v
  | [], [], _, _ => rfl
  | x :: u, y :: v, h, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [natOfBits_cons] at he
    have : x = y ∧ natOfBits u = natOfBits v := by
      cases x <;> cases y <;> simp at he ⊢ <;> omega
    rw [this.1, natOfBits_inj_of_length h this.2]

theorem ltEq_iff : ∀ {u v : List Bool}, u.length = v.length →
    (LtEq u v ↔ natOfBits u < natOfBits v)
  | [], [], _ => by simp [LtEq]
  | x :: u, y :: v, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [ltEq_cons h, ltEq_iff h, natOfBits_cons, natOfBits_cons]
    constructor
    · rintro (⟨rfl, rfl, rfl⟩ | hlt)
      · simp
      · cases x <;> cases y <;> simp <;> omega
    · intro hlt
      by_cases hl : natOfBits u < natOfBits v
      · exact Or.inr hl
      · left
        have hge : natOfBits v ≤ natOfBits u := by omega
        cases x <;> cases y <;> simp at hlt ⊢
        all_goals first
          | omega
          | exact (natOfBits_inj_of_length h (by omega)).symm

theorem length_bitsOfNat_mono : ∀ {a b : ℕ}, a ≤ b → (bitsOfNat a).length ≤ (bitsOfNat b).length := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    intro hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have hb : 0 < b := by omega
      rw [bitsOfNat_pos ha, bitsOfNat_pos hb, List.length_cons, List.length_cons]
      have := ih (b / 2) (Nat.div_lt_self hb (by norm_num)) (Nat.div_le_div_right hab)
      omega

/-- **The comparison of numerals.** -/
theorem ltBits_bitsOfNat (a b : ℕ) : ltBits (bitsOfNat a) (bitsOfNat b) = decide (a < b) := by
  rcases lt_trichotomy (bitsOfNat a).length (bitsOfNat b).length with hl | hl | hl
  · have hab : a < b := by
      by_contra hc
      have := length_bitsOfNat_mono (not_lt.1 hc)
      omega
    simp [ltBits, hl, hab]
  · have h := ltEq_iff hl
    rw [natOfBits_bitsOfNat, natOfBits_bitsOfNat] at h
    simp only [ltBits, hl, lt_self_iff_false, decide_false, decide_true, Bool.true_and,
      Bool.false_or]
    by_cases hab : a < b
    · simp [hab, (ltEqLen_iff _ _).2 (h.2 hab)]
    · have : ltEqLen (bitsOfNat a) (bitsOfNat b) = false := by
        rcases hx : ltEqLen (bitsOfNat a) (bitsOfNat b)
        · rfl
        · exact absurd (h.1 ((ltEqLen_iff _ _).1 hx)) hab
      simp [hab, this]
  · have hab : ¬ a < b := fun h => by have := length_bitsOfNat_mono h.le; omega
    have h1 : ¬ (bitsOfNat a).length < (bitsOfNat b).length := by omega
    have h2 : (bitsOfNat a).length ≠ (bitsOfNat b).length := by omega
    simp [ltBits, h1, h2, hab]

/-! ### As a predicate of Cobham's class -/

theorem cobhamB_ltEqLen {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => ltEqLen (a args) (b args) := by
  have hp : CobhamB fun args =>
      (!decide (args.getD 0 [] = []) && !(args.getD 0 []).headD false) &&
        decide ((b args.tail).drop ((b args.tail).drop (args.getD 0 []).length).length =
          true :: (args.getD 0 []).tail) :=
    ((cobhamB_null cobham_var0).not.and (cobhamB_head cobham_var0).not).and
      (cobhamB_eqStr (cobham_drop (cobham_drop cobham_var0 (cobham_tailArgs hb))
        (cobham_tailArgs hb)) (cobham_consTrue (Syn.cobham_tail cobham_var0)))
  exact (cobhamB_anyTailsC hp ha).of_eq fun args => by simp [anyTailsB, ltEqLen]

/-- **The comparison of numerals is a predicate of Cobham's class.** -/
theorem cobhamB_ltBits {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => ltBits (a args) (b args) :=
  ((cobhamB_lenLE (cobham_consTrue ha) hb).or
    (((cobhamB_lenLE ha hb).and (cobhamB_lenLE hb ha)).and (cobhamB_ltEqLen ha hb))).of_eq
    fun args => by
      simp only [ltBits, List.length_cons]
      congr 1
      congr 1
      rw [← Bool.decide_and]
      simp only [decide_eq_decide]; omega

/-! ### The bits of a self-delimiting numeral -/

theorem undblM_outs_dbl (w : List Bool) (z : List Bool) :
    undblM.outs false (dbl w ++ z) = w ++ undblM.outs false z := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [dbl_cons, List.cons_append, Mealy.outs_cons,
      show ∀ s b, undblM.step s b = !s from fun _ _ => rfl,
      show ∀ b, undblM.out true b = [b] from fun _ => rfl,
      show ∀ b, undblM.out false b = [] from fun _ => rfl, Bool.not_false, Bool.not_true, ih]
    rfl

/-- `undbl` reads the bits off a self-delimiting numeral. -/
theorem undbl_bstr (w : List Bool) : undbl (bstr w) = w := by
  rw [undbl, bstr_eq_dbl, undblM_outs_dbl]
  exact List.append_nil w

theorem undbl_serNat (a : ℕ) : undbl (serNat a) = bitsOfNat a := undbl_bstr _

end PolyInst

end Syn

end HTN
