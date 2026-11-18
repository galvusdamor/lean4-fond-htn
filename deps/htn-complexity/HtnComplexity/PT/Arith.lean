import HtnComplexity.PT.Derived
/-!
# Arithmetic in the polynomial-time calculus

* `HTN.Syn.PolyDom.PT.bits`, `HTN.Syn.PolyDom.PT.ofBits` — the conversions between a number and
  the list of its binary digits (two transducers, and the removal of trailing zeros);
* `HTN.Syn.PolyDom.PT.add` — addition, by the school method on the zipped digits;
* `HTN.Syn.PolyDom.PT.mul` — multiplication, by shift-and-add;
* `HTN.Syn.PolyDom.PT.natPair` — Cantor's pairing `Nat.pair`.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime Compress TOPlan PolyInst

variable {α β γ δ σ : Type} [BEnc α] [BEnc β] [BEnc γ] [BEnc δ] [BEnc σ]

/-! ### More combinators -/

theorem PT.all {f : α → List β} {p : α → β → Bool} (hf : PT f) (hp : PT₂ p) :
    PT fun a => (f a).all (p a) := by
  have h := PT.isEmpty (PT.filter (p := fun a b => !p a b) hf (PT.not hp))
  refine h.of_eq fun a => ?_
  rw [Bool.eq_iff_iff, List.isEmpty_iff, List.filter_eq_nil_iff, List.all_eq_true]
  simp

theorem PT.any {f : α → List β} {p : α → β → Bool} (hf : PT f) (hp : PT₂ p) :
    PT fun a => (f a).any (p a) := by
  have h := PT.not (PT.all (p := fun a b => !p a b) hf (PT.not hp))
  refine h.of_eq fun a => ?_
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true, List.all_eq_true]

theorem PT.xor {c d : α → Bool} (hc : PT c) (hd : PT d) : PT fun a => xor (c a) (d a) :=
  (PT.cond hc (PT.not hd) hd).of_eq fun a => by cases c a <;> cases d a <;> rfl

/-! ### Digits -/

/-- From a self-delimiting numeral to the encoded list of its digits. -/
def toBitsM : Mealy ℕ where
  step s b := if s = 0 then (if b then 1 else 2) else if s = 1 then 0 else 2
  out s b := if s = 1 then [true, true, b, false] else if s = 0 ∧ b = false then [false] else []

theorem toBitsM_outs_two (r : List Bool) : toBitsM.outs 2 r = [] := by
  induction r with
  | nil => exact Mealy.outs_nil _ _
  | cons b r ih => simpa [toBitsM] using ih

theorem toBitsM_outs (w r : List Bool) : toBitsM.outs 0 (bstr w ++ r) = enc w := by
  induction w with
  | nil =>
    show toBitsM.outs 0 (false :: r) = [false]
    rw [Mealy.outs_cons, show toBitsM.step 0 false = 2 from rfl, toBitsM_outs_two]; rfl
  | cons b w ih =>
    simp only [bstr, List.foldr_cons, List.cons_append, Mealy.outs_cons] at ih ⊢
    simp only [toBitsM, if_true] at ih ⊢
    simp only [show ((1 : ℕ) = 0) = False from by simp, if_false, true_and]
    rw [ih]
    simp [enc_cons, enc_bool, bstr]

/-- From the encoded list of the digits to the self-delimiting numeral. -/
def ofBitsM : Mealy ℕ where
  step s b := if s = 0 then (if b then 1 else 4) else if s = 1 then 2 else if s = 2 then 3
    else if s = 3 then 0 else 4
  out s b := if s = 2 then [true, b] else if s = 0 ∧ b = false then [false] else []

theorem ofBitsM_outs_four (r : List Bool) : ofBitsM.outs 4 r = [] := by
  induction r with
  | nil => exact Mealy.outs_nil _ _
  | cons b r ih => simpa [ofBitsM] using ih

theorem ofBitsM_outs (w r : List Bool) : ofBitsM.outs 0 (enc w ++ r) = bstr w := by
  induction w with
  | nil =>
    show ofBitsM.outs 0 (false :: r) = [false]
    rw [Mealy.outs_cons, show ofBitsM.step 0 false = 4 from rfl, ofBitsM_outs_four]; rfl
  | cons b w ih =>
    simp only [enc_cons, enc_bool, bstr, List.foldr_cons, List.foldr_nil, List.cons_append,
      List.nil_append, Mealy.outs_cons] at ih ⊢
    simp only [ofBitsM] at ih ⊢
    simp [ih]

theorem PT.bits : PT fun n : ℕ => bitsOfNat n := by
  refine ⟨fun x => toBitsM.outs 0 x ++ [], (toBitsM.cobham_mealy [0, 1, 2] 0 (fun _ => [])
    (by simp) (by intro s b _; simp [toBitsM]; split_ifs <;> simp) cobham_var0), fun n => ?_⟩
  simpa [enc_nat, serNat] using toBitsM_outs (bitsOfNat n) []

/-- The digits without trailing zeros. -/
def strip (w : List Bool) : List Bool :=
  (splits w).flatMap fun p => if (p.2.1 :: p.2.2).all (fun b => !b) then [] else [p.2.1]

theorem strip_nil : strip [] = [] := rfl

theorem strip_cons' (b : Bool) (w : List Bool) :
    strip (b :: w) = (if (b :: w).all (fun b => !b) then [] else [b]) ++ strip w := by
  simp only [strip, splits, List.flatMap_cons, List.flatMap_map]

theorem strip_eq_nil_iff (w : List Bool) : strip w = [] ↔ w.all (fun b => !b) = true := by
  induction w with
  | nil => simp [strip_nil]
  | cons b w ih =>
    rw [strip_cons']
    by_cases h : (b :: w).all (fun b => !b) = true
    · simp only [h, if_true, List.nil_append, iff_true]
      rw [ih]
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact h.2
    · simp [h]

theorem strip_cons (b : Bool) (w : List Bool) :
    strip (b :: w) = if (b :: w).all (fun b => !b) then [] else b :: strip w := by
  rw [strip_cons']
  by_cases h : (b :: w).all (fun b => !b) = true
  · have hw : w.all (fun b => !b) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2
    simp [h, (strip_eq_nil_iff w).2 hw]
  · simp [h]

theorem bitsOfNat_natOfBits (w : List Bool) : bitsOfNat (natOfBits w) = strip w := by
  induction w with
  | nil => simp [strip_nil]
  | cons b w ih =>
    rw [natOfBits_cons, strip_cons]
    cases b
    · simp only [Bool.false_eq_true, if_false, zero_add]
      rcases Nat.eq_zero_or_pos (natOfBits w) with h0 | hpos
      · rw [h0] at ih ⊢
        have : w.all (fun b => !b) = true := (strip_eq_nil_iff w).1 (by rw [← ih]; simp)
        simp [this]
      · rw [bitsOfNat_pos (by omega), show 2 * natOfBits w / 2 = natOfBits w by omega, ih]
        have hne : strip w ≠ [] := by
          rw [← ih]; intro h
          have := natOfBits_bitsOfNat (natOfBits w)
          rw [h] at this; simp at this; omega
        have : w.all (fun b => !b) = false := by
          by_contra hc; exact hne ((strip_eq_nil_iff w).2 (by simpa using hc))
        simp [this]
    · simp only [if_true]
      rw [bitsOfNat_pos (by omega), show (1 + 2 * natOfBits w) / 2 = natOfBits w by omega, ih]
      simp

theorem PT.strip {f : α → List Bool} (hf : PT f) : PT fun a => PolyDom.strip (f a) :=
  PT.flatMapSplits (g := fun _ _ b l₂ => if (b :: l₂).all (fun b => !b) then [] else [b]) hf
    (PT.ite (PT.eq (PT.all (PT.cons (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.snd.comp (PT.snd.comp PT.snd))) (PT.not PT.snd)) (PT.const true))
      PT.nil (PT.single (PT.fst.comp (PT.snd.comp PT.snd))))

theorem PT.ofBits {f : α → List Bool} (hf : PT f) : PT fun a => natOfBits (f a) := by
  obtain ⟨F, hF, hFf⟩ := PT.strip hf
  refine ⟨fun x => ofBitsM.outs 0 (F x) ++ [], ofBitsM.cobham_mealy [0, 1, 2, 3, 4] 0
    (fun _ => []) (by simp) (by intro s b _; simp [ofBitsM]; split_ifs <;> simp) hF, fun a => ?_⟩
  simp only [hFf, List.append_nil]
  rw [enc_nat, serNat, bitsOfNat_natOfBits]
  simpa using ofBitsM_outs (PolyDom.strip (f a)) []

/-! ### Addition -/

theorem natOfBits_append (u v : List Bool) :
    natOfBits (u ++ v) = natOfBits u + 2 ^ u.length * natOfBits v := by
  induction u with
  | nil => simp
  | cons b u ih => rw [List.cons_append, natOfBits_cons, natOfBits_cons, ih]; simp [pow_succ]; ring

theorem natOfBits_replicate_false (k : ℕ) : natOfBits (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, natOfBits_cons, ih]

/-- The digits of two numbers, zipped and padded with zeros. -/
def zipBits (u v : List Bool) : List (Bool × Bool) :=
  (List.range (if u.length < v.length then v else u).length).map fun i => (u.getI i, v.getI i)

theorem range_map_getI (u : List Bool) {n : ℕ} (h : u.length ≤ n) :
    (List.range n).map u.getI = u ++ List.replicate (n - u.length) false := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < u.length
  · rw [List.getElem_append_left hi, List.getI_eq_getElem _ hi]
  · rw [List.getElem_append_right (by omega), List.getElem_replicate,
      List.getI_eq_default _ (by omega)]
    rfl

theorem natOfBits_zipBits_fst (u v : List Bool) :
    natOfBits ((zipBits u v).map Prod.fst) = natOfBits u := by
  rw [zipBits, List.map_map]
  have h : u.length ≤ (if u.length < v.length then v else u).length := by split_ifs <;> omega
  rw [show (Prod.fst ∘ fun i => (u.getI i, v.getI i)) = u.getI from rfl, range_map_getI u h,
    natOfBits_append, natOfBits_replicate_false]
  simp

theorem natOfBits_zipBits_snd (u v : List Bool) :
    natOfBits ((zipBits u v).map Prod.snd) = natOfBits v := by
  rw [zipBits, List.map_map]
  have h : v.length ≤ (if u.length < v.length then v else u).length := by split_ifs <;> omega
  rw [show (Prod.snd ∘ fun i => (u.getI i, v.getI i)) = v.getI from rfl, range_map_getI v h,
    natOfBits_append, natOfBits_replicate_false]
  simp

/-- The step of the school addition: carry and digits so far. -/
def addStep (s : Bool × List Bool) (p : Bool × Bool) : Bool × List Bool :=
  ((p.1 && p.2) || (p.1 && s.1) || (p.2 && s.1), s.2 ++ [xor (xor p.1 p.2) s.1])

/-- The value of a Boolean. -/
def bv (b : Bool) : ℕ := if b then 1 else 0

theorem natOfBits_cons' (b : Bool) (x : List Bool) : natOfBits (b :: x) = bv b + 2 * natOfBits x :=
  rfl

theorem foldl_addStep (zs : List (Bool × Bool)) (c : Bool) (acc : List Bool) :
    natOfBits ((zs.foldl addStep (c, acc)).2 ++ [(zs.foldl addStep (c, acc)).1]) =
      natOfBits acc + 2 ^ acc.length *
        (bv c + natOfBits (zs.map Prod.fst) + natOfBits (zs.map Prod.snd)) := by
  induction zs generalizing c acc with
  | nil => cases c <;> simp [natOfBits_append, bv, natOfBits]
  | cons p zs ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨x, y⟩ := p
    simp only [addStep, List.map_cons, natOfBits_cons', natOfBits_append, List.length_append,
      List.length_cons, List.length_nil, pow_succ]
    cases x <;> cases y <;> cases c <;> simp [bv, natOfBits] <;> ring

theorem length_foldl_addStep (zs : List (Bool × Bool)) (c : Bool) (acc : List Bool) :
    (zs.foldl addStep (c, acc)).2.length = acc.length + zs.length := by
  induction zs generalizing c acc with
  | nil => simp
  | cons p zs ih => rw [List.foldl_cons, ih]; simp [addStep]; omega

theorem natOfBits_lt' (x : List Bool) : natOfBits x < 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [natOfBits_cons, List.length_cons, pow_succ]
    cases b <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

theorem sz_bits_list (w : List Bool) : sz w = 4 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [sz_cons, ih]; simp [sz, enc_bool]; ring

theorem sz_nat (n : ℕ) : sz n = 2 * (bitsOfNat n).length + 1 := by
  simp [sz, enc_nat, serNat, length_bstr]

/-- The school addition of two digit lists. -/
def addBits (u v : List Bool) : List Bool :=
  ((zipBits u v).foldl addStep (false, [])).2 ++ [((zipBits u v).foldl addStep (false, [])).1]

theorem natOfBits_addBits (u v : List Bool) :
    natOfBits (addBits u v) = natOfBits u + natOfBits v := by
  rw [addBits, foldl_addStep, natOfBits_zipBits_fst, natOfBits_zipBits_snd]
  simp [bv]

theorem PT.zipBits {f g : α → List Bool} (hf : PT f) (hg : PT g) :
    PT fun a => PolyDom.zipBits (f a) (g a) := by
  unfold PolyDom.zipBits
  exact PT.map (PT.rangeLength (PT.ite (PT.lt (PT.length hf) (PT.length hg)) hg hf))
    (PT.pair (PT.getI (hf.comp PT.fst) PT.snd) (PT.getI (hg.comp PT.fst) PT.snd))

theorem length_zipBits (u v : List Bool) :
    (PolyDom.zipBits u v).length ≤ u.length + v.length := by
  simp only [PolyDom.zipBits, List.length_map, List.length_range]
  split_ifs <;> omega

theorem PT.addBits : PT fun p : List Bool × List Bool => PolyDom.addBits p.1 p.2 := by
  have hz : PT fun p : List Bool × List Bool => PolyDom.zipBits p.1 p.2 := PT.zipBits PT.fst PT.snd
  have hstep : PT fun q : (List Bool × List Bool) × (Bool × List Bool) × (Bool × Bool) =>
      addStep q.2.1 q.2.2 := by
    unfold addStep
    have hx : PT fun q : (List Bool × List Bool) × (Bool × List Bool) × (Bool × Bool) => q.2.2.1 :=
      PT.fst.comp (PT.snd.comp PT.snd)
    have hy : PT fun q : (List Bool × List Bool) × (Bool × List Bool) × (Bool × Bool) => q.2.2.2 :=
      PT.snd.comp (PT.snd.comp PT.snd)
    have hc : PT fun q : (List Bool × List Bool) × (Bool × List Bool) × (Bool × Bool) => q.2.1.1 :=
      PT.fst.comp (PT.fst.comp PT.snd)
    exact PT.pair (PT.or (PT.or (PT.and hx hy) (PT.and hx hc)) (PT.and hy hc))
      (PT.append (PT.snd.comp (PT.fst.comp PT.snd)) (PT.single (PT.xor (PT.xor hx hy) hc)))
  have hfold := PT.foldl' (g := fun _ s p => addStep s p) hz (PT.const (false, ([] : List Bool)))
    hstep (c := 1) (d := 1) fun a j hj => by
      rw [sz_prod, sz_bits_list, length_foldl_addStep, List.length_take]
      have h1 := length_zipBits a.1 a.2
      have h2 : sz a = 4 * a.1.length + 1 + (4 * a.2.length + 1) := by
        rw [show a = (a.1, a.2) from rfl, sz_prod, sz_bits_list, sz_bits_list]
      simp only [List.length_nil, zero_add, pow_one, one_mul]
      have : ∀ b : Bool, sz b = 1 := fun _ => rfl
      rw [this]
      omega
  have h := PT.append (PT.snd.comp hfold) (PT.single (PT.fst.comp hfold))
  exact h.of_eq fun p => rfl

/-- **Addition is polynomial time.** -/
theorem PT.add {f g : α → ℕ} (hf : PT f) (hg : PT g) : PT fun a => f a + g a := by
  have h := PT.ofBits (PT.addBits.comp (PT.pair (PT.bits.comp hf) (PT.bits.comp hg)))
  exact h.of_eq fun a => by simp [natOfBits_addBits, natOfBits_bitsOfNat]

/-! ### Multiplication -/

theorem lt_two_pow_length_bits (n : ℕ) : n < 2 ^ (bitsOfNat n).length := by
  have := natOfBits_lt' (bitsOfNat n)
  rwa [natOfBits_bitsOfNat] at this

/-- The step of shift-and-add: the shifted multiplicand and the partial product. -/
def mulStep (s : ℕ × ℕ) (b : Bool) : ℕ × ℕ := (2 * s.1, bif b then s.2 + s.1 else s.2)

theorem foldl_mulStep (w : List Bool) (s acc : ℕ) :
    w.foldl mulStep (s, acc) = (s * 2 ^ w.length, acc + s * natOfBits w) := by
  induction w generalizing s acc with
  | nil => simp
  | cons b w ih =>
    rw [List.foldl_cons, ih]
    cases b <;> simp only [mulStep, cond_true, cond_false, natOfBits_cons, Prod.mk.injEq,
      pow_succ, List.length_cons, if_true, if_false, Bool.false_eq_true] <;> constructor <;> ring

theorem length_bits_le_of_lt {n k : ℕ} (h : n < 2 ^ k) : (bitsOfNat n).length ≤ k := by
  induction k generalizing n with
  | zero => simp at h; subst h; simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [bitsOfNat_pos hn, List.length_cons]
      have : n / 2 < 2 ^ k := by rw [pow_succ] at h; omega
      have := ih this; omega

theorem PT.mul {f g : α → ℕ} (hf : PT f) (hg : PT g) : PT fun a => f a * g a := by
  have hstep : PT fun q : (ℕ × ℕ) × (ℕ × ℕ) × Bool => mulStep q.2.1 q.2.2 := by
    unfold mulStep
    exact PT.pair (PT.affine 2 0 (PT.fst.comp (PT.fst.comp PT.snd)) |>.of_eq fun _ => by ring)
      (PT.cond (PT.snd.comp PT.snd) (PT.add (PT.snd.comp (PT.fst.comp PT.snd))
        (PT.fst.comp (PT.fst.comp PT.snd))) (PT.snd.comp (PT.fst.comp PT.snd)))
  have hfold := PT.foldl' (l := fun p : ℕ × ℕ => bitsOfNat p.2) (init := fun p => (p.1, 0))
    (g := fun _ s b => mulStep s b) (PT.bits.comp PT.snd) (PT.pair PT.fst (PT.const 0)) hstep
    (c := 1) (d := 4) fun p j hj => by
      rw [foldl_mulStep, sz_prod, sz_nat, sz_nat, List.length_take]
      have hp : sz p = 2 * (bitsOfNat p.1).length + 1 + (2 * (bitsOfNat p.2).length + 1) := by
        rw [show p = (p.1, p.2) from rfl, sz_prod, sz_nat, sz_nat]
      set k := min j (bitsOfNat p.2).length
      have hk : k ≤ (bitsOfNat p.2).length := min_le_right _ _
      have ha := lt_two_pow_length_bits p.1
      have hw := natOfBits_lt' ((bitsOfNat p.2).take j)
      rw [List.length_take] at hw
      have e1 : (bitsOfNat (p.1 * 2 ^ k)).length ≤ (bitsOfNat p.1).length + k :=
        length_bits_le_of_lt (by rw [pow_add]; exact Nat.mul_lt_mul_of_pos_right ha (by positivity))
      have e2 : (bitsOfNat (0 + p.1 * natOfBits ((bitsOfNat p.2).take j))).length ≤
          (bitsOfNat p.1).length + k := by
        refine length_bits_le_of_lt ?_
        rw [zero_add, pow_add]
        rcases Nat.eq_zero_or_pos p.1 with h0 | hpos
        · rw [h0]; simp
        · exact Nat.mul_lt_mul_of_lt_of_le ha hw.le (by positivity)
      simp only [pow_one]
      nlinarith
  have hm : PT fun p : ℕ × ℕ => p.1 * p.2 :=
    (PT.snd.comp hfold).of_eq fun p => by simp [foldl_mulStep, natOfBits_bitsOfNat]
  exact hm.comp (hf.pair hg)

/-- **Cantor's pairing is polynomial time.** -/
theorem PT.natPair {f g : α → ℕ} (hf : PT f) (hg : PT g) : PT fun a => Nat.pair (f a) (g a) := by
  unfold Nat.pair
  exact PT.ite (PT.lt hf hg) (PT.add (PT.mul hg hg) hf) (PT.add (PT.add (PT.mul hf hf) hf) hg)

end PolyDom

end Syn

end HTN
