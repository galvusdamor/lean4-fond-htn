import HtnComplexity.Hypotheses.Partition
/-!
# From 3-dimensional matching to the equal-sum partition problem in unary

The numerical half of the classical proof that 3-Partition is NP-hard in the strong sense
(Garey and Johnson): a 3-dimensional matching instance is turned into a list of numbers of
polynomial *value*, to be split into groups of equal sum.

An instance of 3-dimensional matching is a number `q` and a list `M` of triples with coordinates
below `q`; it has a matching (`HTN.NPHard.Has3DM`) when a sub-multiset of `M` covers every
coordinate value exactly once in each of the three coordinates.

The numbers are written in base `r = 4q + 100` with five digits.  Every triple contributes one
item, every coordinate value `e` one *actual* item and, for every further occurrence of `e` in
`M`, one *dummy* item.  The digits are chosen so that a group of target sum is exactly one triple
together with one item for each of its three coordinate values, all three actual or all three
dummies.  The main result is `HTN.NPHard.esp_numInst_iff`.
-/

namespace HTN.NPHard

open Merge

/-- **3-dimensional matching**: some sub-multiset of the triples covers every value below `q`
exactly once in each coordinate. -/
def Has3DM (q : ℕ) (M : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ S : Multiset (ℕ × ℕ × ℕ), S ≤ (M : Multiset (ℕ × ℕ × ℕ)) ∧
    S.map (fun t => t.1) = Multiset.range q ∧ S.map (fun t => t.2.1) = Multiset.range q ∧
    S.map (fun t => t.2.2) = Multiset.range q

/-! ### Five-digit numbers -/

/-- A five-digit number in base `r`, least significant digit first. -/
def hor (r a0 a1 a2 a3 a4 : ℕ) : ℕ := a0 + r * (a1 + r * (a2 + r * (a3 + r * a4)))

theorem hor_add (r a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ) :
    hor r a0 a1 a2 a3 a4 + hor r b0 b1 b2 b3 b4 =
      hor r (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) := by
  unfold hor; ring

theorem digit_step {r a b x y : ℕ} (ha : a < r) (hb : b < r) (h : a + r * x = b + r * y) :
    a = b ∧ x = y := by
  have h1 : (a + r * x) % r = (b + r * y) % r := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] at h1
  subst h1
  refine ⟨rfl, ?_⟩
  have hr : 0 < r := by omega
  exact Nat.eq_of_mul_eq_mul_left hr (by omega)

theorem hor_inj {r a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ} (ha0 : a0 < r) (hb0 : b0 < r)
    (ha1 : a1 < r) (hb1 : b1 < r) (ha2 : a2 < r) (hb2 : b2 < r) (ha3 : a3 < r) (hb3 : b3 < r)
    (h : hor r a0 a1 a2 a3 a4 = hor r b0 b1 b2 b3 b4) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 := by
  unfold hor at h
  obtain ⟨e0, h⟩ := digit_step ha0 hb0 h
  obtain ⟨e1, h⟩ := digit_step ha1 hb1 h
  obtain ⟨e2, h⟩ := digit_step ha2 hb2 h
  obtain ⟨e3, h⟩ := digit_step ha3 hb3 h
  exact ⟨e0, e1, e2, e3, h⟩

theorem step_lt {r a b k : ℕ} (ha : a < r) (hb : b < r ^ k) : a + r * b < r ^ (k + 1) := by
  have : r * (b + 1) ≤ r * r ^ k := Nat.mul_le_mul_left _ hb
  rw [pow_succ]; nlinarith

/-- The four low digits stay below `r ^ 4`. -/
theorem hor_split {r a0 a1 a2 a3 a4 : ℕ} (ha0 : a0 < r) (ha1 : a1 < r) (ha2 : a2 < r)
    (ha3 : a3 < r) : ∃ L, L < r ^ 4 ∧ hor r a0 a1 a2 a3 a4 = L + r ^ 4 * a4 := by
  refine ⟨a0 + r * (a1 + r * (a2 + r * a3)), ?_, by unfold hor; ring⟩
  have h3 : a3 < r ^ 1 := by simpa using ha3
  exact step_lt ha0 (step_lt ha1 (step_lt ha2 h3))

/-! ### The items -/

/-- The items of the numerical instance: one per triple, and the actual (`d = false`) and dummy
(`d = true`) items of the three coordinates. -/
inductive Item
  | trip (t : ℕ × ℕ × ℕ)
  | w (d : Bool) (e : ℕ)
  | x (d : Bool) (e : ℕ)
  | y (d : Bool) (e : ℕ)
  deriving DecidableEq

/-- The base. -/
def radix (q : ℕ) : ℕ := 4 * q + 100

namespace Item

/-- The lowest digit: the kind of the item. -/
def d0 : Item → ℕ
  | trip _ => 8
  | w _ _ => 1
  | x _ _ => 2
  | y _ _ => 4

/-- The digit matching the first coordinate. -/
def d1 (q : ℕ) : Item → ℕ
  | trip t => q - t.1
  | w _ e => e
  | _ => 0

/-- The digit matching the second coordinate. -/
def d2 (q : ℕ) : Item → ℕ
  | trip t => q - t.2.1
  | x _ e => e
  | _ => 0

/-- The digit matching the third coordinate. -/
def d3 (q : ℕ) : Item → ℕ
  | trip t => q - t.2.2
  | y _ e => e
  | _ => 0

/-- The leading digit: actual or dummy. -/
def d4 : Item → ℕ
  | trip _ => 20
  | w d _ => if d then 21 else 20
  | x d _ => if d then 21 else 20
  | y d _ => if d then 18 else 20

/-- The value of an item. -/
def val (q : ℕ) (it : Item) : ℕ := hor (radix q) it.d0 (it.d1 q) (it.d2 q) (it.d3 q) it.d4

/-- The coordinates of an item are below `q`. -/
def Valid (q : ℕ) : Item → Prop
  | trip t => t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q
  | w _ e => e < q
  | x _ e => e < q
  | y _ e => e < q

theorem d0_lt (it : Item) : it.d0 ≤ 8 := by cases it <;> simp [d0]

theorem d1_le {q : ℕ} {it : Item} (h : it.Valid q) : it.d1 q ≤ q := by
  cases it <;> simp [d1, Valid] at * <;> omega

theorem d2_le {q : ℕ} {it : Item} (h : it.Valid q) : it.d2 q ≤ q := by
  cases it <;> simp [d2, Valid] at * <;> omega

theorem d3_le {q : ℕ} {it : Item} (h : it.Valid q) : it.d3 q ≤ q := by
  cases it <;> simp [d3, Valid] at * <;> omega

theorem d4_mem (it : Item) : it.d4 = 18 ∨ it.d4 = 20 ∨ it.d4 = 21 := by
  cases it with
  | trip => simp [d4]
  | w d _ => cases d <;> simp [d4]
  | x d _ => cases d <;> simp [d4]
  | y d _ => cases d <;> simp [d4]

end Item

/-- The target sum. -/
def bigB (q : ℕ) : ℕ := hor (radix q) 15 q q q 80

/-- The items of one coordinate: one actual item per value below `q`, and one dummy for every
further occurrence of the value among the coordinates `cs`. -/
def elemItems (mk : Bool → ℕ → Item) (cs : List ℕ) (q : ℕ) : List Item :=
  (List.range q).flatMap fun e => mk false e :: List.replicate (cs.count e - 1) (mk true e)

/-- All items of the instance. -/
def items (q : ℕ) (M : List (ℕ × ℕ × ℕ)) : List Item :=
  M.map Item.trip ++ elemItems Item.w (M.map fun t => t.1) q ++
    elemItems Item.x (M.map fun t => t.2.1) q ++ elemItems Item.y (M.map fun t => t.2.2) q

/-- **The numerical instance.** -/
def numInst (q : ℕ) (M : List (ℕ × ℕ × ℕ)) : List ℕ := (items q M).map (Item.val q)

/-! ### Sums of items -/

/-- Digit sums of a list of items. -/
theorem sum_val (q : ℕ) (g : List Item) :
    (g.map (Item.val q)).sum = hor (radix q) (g.map Item.d0).sum (g.map (Item.d1 q)).sum
      (g.map (Item.d2 q)).sum (g.map (Item.d3 q)).sum (g.map Item.d4).sum := by
  induction g with
  | nil => simp [hor]
  | cons a g ih =>
    simp only [List.map_cons, List.sum_cons, ih, Item.val, hor_add]

theorem sum_le_of {l : List Item} {f : Item → ℕ} {c : ℕ} (h : ∀ a ∈ l, f a ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp)
    have := ih fun b hb => h b (by simp [hb])
    nlinarith

/-- An item is more than a fifth and less than a third of the target. -/
theorem val_bounds {q : ℕ} {it : Item} (h : it.Valid q) :
    bigB q < 5 * it.val q ∧ 3 * it.val q < bigB q := by
  have hr : radix q = 4 * q + 100 := rfl
  have c0 := it.d0_lt
  have c1 := Item.d1_le h
  have c2 := Item.d2_le h
  have c3 := Item.d3_le h
  obtain ⟨L, hL, hv⟩ := hor_split (r := radix q) (a0 := it.d0) (a1 := it.d1 q) (a2 := it.d2 q)
    (a3 := it.d3 q) (a4 := it.d4) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨LB, hLB, hB⟩ := hor_split (r := radix q) (a0 := 15) (a1 := q) (a2 := q) (a3 := q)
    (a4 := 80) (by omega) (by omega) (by omega) (by omega)
  unfold Item.val at *
  rw [bigB, hB, hv]
  generalize radix q ^ 4 = P at *
  rcases it.d4_mem with h4 | h4 | h4 <;> rw [h4] <;> omega

theorem sum_lt_of_le_three {q : ℕ} {g : List Item} (hv : ∀ it ∈ g, it.Valid q)
    (hl : g.length ≤ 3) : (g.map (Item.val q)).sum < bigB q := by
  have hB : 0 < bigB q := by unfold bigB hor; omega
  rcases Nat.eq_zero_or_pos g.length with h0 | h0
  · rw [List.length_eq_zero_iff] at h0; subst h0; simpa using hB
  have key : ∀ l : List Item, (∀ it ∈ l, it.Valid q) → 0 < l.length →
      3 * (l.map (Item.val q)).sum < l.length * bigB q := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl _
      have ha := (val_bounds (hl a (by simp))).2
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rcases Nat.eq_zero_or_pos l.length with h | h
      · rw [List.length_eq_zero_iff] at h; subst h; simp; omega
      · have := ih (fun b hb => hl b (by simp [hb])) h
        nlinarith
  have := key g hv h0
  nlinarith

theorem sum_gt_of_ge_five {q : ℕ} {g : List Item} (hv : ∀ it ∈ g, it.Valid q)
    (hl : 5 ≤ g.length) : bigB q < (g.map (Item.val q)).sum := by
  have key : ∀ l : List Item, (∀ it ∈ l, it.Valid q) → 0 < l.length →
      l.length * bigB q < 5 * (l.map (Item.val q)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl _
      have ha := (val_bounds (hl a (by simp))).1
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rcases Nat.eq_zero_or_pos l.length with h | h
      · rw [List.length_eq_zero_iff] at h; subst h; simp; omega
      · have := ih (fun b hb => hl b (by simp [hb])) h
        nlinarith
  have := key g hv (by omega)
  nlinarith

/-! ### The shape of a group -/

/-- The kind of an item. -/
def Item.kind : Item → Fin 4
  | trip _ => 0
  | w _ _ => 1
  | x _ _ => 2
  | y _ _ => 3

theorem sum_d0_eq (g : List Item) :
    (g.map Item.d0).sum = 8 * (g.filter fun a => a.kind = 0).length +
      (g.filter fun a => a.kind = 1).length + 2 * (g.filter fun a => a.kind = 2).length +
      4 * (g.filter fun a => a.kind = 3).length := by
  induction g with
  | nil => simp
  | cons a g ih =>
    cases a <;> simp [Item.d0, Item.kind, ih] <;> ring

theorem length_eq_kinds (g : List Item) :
    g.length = (g.filter fun a => a.kind = 0).length + (g.filter fun a => a.kind = 1).length +
      (g.filter fun a => a.kind = 2).length + (g.filter fun a => a.kind = 3).length := by
  induction g with
  | nil => simp
  | cons a g ih =>
    cases a <;> simp [Item.kind, ih] <;> ring

theorem count_filter_ite {α : Type} [DecidableEq α] (p : α → Bool) (a : α) (l : List α) :
    (l.filter p).count a = if p a then l.count a else 0 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases hb : p b <;> by_cases hab : b = a <;> simp_all

theorem perm_kinds (g : List Item) :
    g.Perm ((g.filter fun a => a.kind = 0) ++ (g.filter fun a => a.kind = 1) ++
      (g.filter fun a => a.kind = 2) ++ (g.filter fun a => a.kind = 3)) := by
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append]
  rcases a with _ | _ | _ | _ <;> simp [count_filter_ite, Item.kind]

/-- The shape of a group: a triple and its three coordinate items, all actual or all dummy. -/
def shape (t : ℕ × ℕ × ℕ) (d : Bool) : List Item :=
  [Item.trip t, Item.w d t.1, Item.x d t.2.1, Item.y d t.2.2]

theorem singleton_of_kind0 {l : List Item} (hk : ∀ a ∈ l, a.kind = 0) (hl : l.length = 1) :
    ∃ t, l = [Item.trip t] := by
  match l, hl with
  | [a], _ =>
    cases a with
    | trip t => exact ⟨t, rfl⟩
    | _ => simp [Item.kind] at hk

theorem singleton_of_kind1 {l : List Item} (hk : ∀ a ∈ l, a.kind = 1) (hl : l.length = 1) :
    ∃ d e, l = [Item.w d e] := by
  match l, hl with
  | [a], _ =>
    cases a with
    | w d e => exact ⟨d, e, rfl⟩
    | _ => simp [Item.kind] at hk

theorem singleton_of_kind2 {l : List Item} (hk : ∀ a ∈ l, a.kind = 2) (hl : l.length = 1) :
    ∃ d e, l = [Item.x d e] := by
  match l, hl with
  | [a], _ =>
    cases a with
    | x d e => exact ⟨d, e, rfl⟩
    | _ => simp [Item.kind] at hk

theorem singleton_of_kind3 {l : List Item} (hk : ∀ a ∈ l, a.kind = 3) (hl : l.length = 1) :
    ∃ d e, l = [Item.y d e] := by
  match l, hl with
  | [a], _ =>
    cases a with
    | y d e => exact ⟨d, e, rfl⟩
    | _ => simp [Item.kind] at hk

/-- **A group of target sum is a triple with its three coordinate items, all actual or all
dummy.** -/
theorem group_shape {q : ℕ} {g : List Item} (hv : ∀ it ∈ g, it.Valid q)
    (hs : (g.map (Item.val q)).sum = bigB q) :
    ∃ t d, (Item.trip t).Valid q ∧ g.Perm (shape t d) := by
  have hlen : g.length = 4 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := sum_lt_of_le_three hv (by omega); omega
    · have := sum_gt_of_ge_five hv (by omega); omega
  -- digit sums
  have hr : radix q = 4 * q + 100 := rfl
  have b0 : (g.map Item.d0).sum ≤ 4 * 8 := by
    have := sum_le_of (l := g) (f := Item.d0) (c := 8) fun a _ => a.d0_lt
    rw [hlen] at this; exact this
  have b1 : (g.map (Item.d1 q)).sum ≤ 4 * q := by
    have := sum_le_of (l := g) (f := Item.d1 q) (c := q) fun a ha => Item.d1_le (hv a ha)
    rw [hlen] at this; exact this
  have b2 : (g.map (Item.d2 q)).sum ≤ 4 * q := by
    have := sum_le_of (l := g) (f := Item.d2 q) (c := q) fun a ha => Item.d2_le (hv a ha)
    rw [hlen] at this; exact this
  have b3 : (g.map (Item.d3 q)).sum ≤ 4 * q := by
    have := sum_le_of (l := g) (f := Item.d3 q) (c := q) fun a ha => Item.d3_le (hv a ha)
    rw [hlen] at this; exact this
  rw [sum_val, bigB] at hs
  obtain ⟨e0, -, -, -, -⟩ := hor_inj (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hs
  -- the kinds
  have hk := sum_d0_eq g
  have hl := length_eq_kinds g
  set n0 := (g.filter fun a => a.kind = 0).length with hn0
  set n1 := (g.filter fun a => a.kind = 1).length with hn1
  set n2 := (g.filter fun a => a.kind = 2).length with hn2
  set n3 := (g.filter fun a => a.kind = 3).length with hn3
  have h0 : n0 = 1 := by omega
  have h1 : n1 = 1 := by omega
  have h2 : n2 = 1 := by omega
  have h3 : n3 = 1 := by omega
  obtain ⟨t, ht⟩ := singleton_of_kind0 (l := g.filter fun a => a.kind = 0)
    (fun a ha => by simpa using (List.mem_filter.1 ha).2) h0
  obtain ⟨d1, e1, he1⟩ := singleton_of_kind1 (l := g.filter fun a => a.kind = 1)
    (fun a ha => by simpa using (List.mem_filter.1 ha).2) h1
  obtain ⟨d2, e2, he2⟩ := singleton_of_kind2 (l := g.filter fun a => a.kind = 2)
    (fun a ha => by simpa using (List.mem_filter.1 ha).2) h2
  obtain ⟨d3, e3, he3⟩ := singleton_of_kind3 (l := g.filter fun a => a.kind = 3)
    (fun a ha => by simpa using (List.mem_filter.1 ha).2) h3
  have hp := perm_kinds g
  rw [ht, he1, he2, he3] at hp
  have hvt : (Item.trip t).Valid q := hv _ (hp.symm.subset (by simp))
  have hv1 : (Item.w d1 e1).Valid q := hv _ (hp.symm.subset (by simp))
  have hv2 : (Item.x d2 e2).Valid q := hv _ (hp.symm.subset (by simp))
  have hv3 : (Item.y d3 e3).Valid q := hv _ (hp.symm.subset (by simp))
  simp only [Item.Valid] at hvt hv1 hv2 hv3
  have hs' := hs
  rw [(hp.map _).sum_eq, (hp.map _).sum_eq, (hp.map _).sum_eq, (hp.map _).sum_eq,
    (hp.map _).sum_eq] at hs'
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Item.d0, Item.d1, Item.d2, Item.d3, Item.d4] at hs'
  obtain ⟨-, f1, f2, f3, f4⟩ := hor_inj (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hs'
  have ee1 : e1 = t.1 := by omega
  have ee2 : e2 = t.2.1 := by omega
  have ee3 : e3 = t.2.2 := by omega
  subst ee1 ee2 ee3
  have hd : d2 = d1 ∧ d3 = d1 := by
    cases d1 <;> cases d2 <;> cases d3 <;> simp at f4 ⊢
  obtain ⟨h2', h3'⟩ := hd
  rw [h2', h3'] at hp
  refine ⟨t, d1, hvt, hp.trans ?_⟩
  simp [shape]

/-! ### Values determine items -/

theorem val_injective {q : ℕ} {a b : Item} (ha : a.Valid q) (hb : b.Valid q)
    (h : a.val q = b.val q) : a = b := by
  have hr : radix q = 4 * q + 100 := rfl
  have := Item.d1_le ha; have := Item.d2_le ha; have := Item.d3_le ha
  have := Item.d1_le hb; have := Item.d2_le hb; have := Item.d3_le hb
  have := a.d0_lt; have := b.d0_lt
  obtain ⟨e0, e1, e2, e3, e4⟩ := hor_inj (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) h
  cases a with
  | trip t =>
    cases b with
    | trip t' =>
      obtain ⟨a1, a2, a3⟩ := t
      obtain ⟨b1, b2, b3⟩ := t'
      simp only [Item.d1, Item.d2, Item.d3, Item.Valid] at e1 e2 e3 ha hb
      have : a1 = b1 := by omega
      have : a2 = b2 := by omega
      have : a3 = b3 := by omega
      subst_vars; rfl
    | _ => simp [Item.d0] at e0
  | w d e =>
    cases b with
    | w d' e' =>
      simp only [Item.d1, Item.d4] at e1 e4
      subst e1; cases d <;> cases d' <;> simp_all
    | _ => simp [Item.d0] at e0
  | x d e =>
    cases b with
    | x d' e' =>
      simp only [Item.d2, Item.d4] at e2 e4
      subst e2; cases d <;> cases d' <;> simp_all
    | _ => simp [Item.d0] at e0
  | y d e =>
    cases b with
    | y d' e' =>
      simp only [Item.d3, Item.d4] at e3 e4
      subst e3; cases d <;> cases d' <;> simp_all
    | _ => simp [Item.d0] at e0

open Classical in
/-- Reading an item off its value. -/
noncomputable def dec (q v : ℕ) : Item :=
  if h : ∃ it : Item, it.Valid q ∧ it.val q = v then h.choose else Item.w false 0

theorem dec_val {q : ℕ} {a : Item} (ha : a.Valid q) : dec q (a.val q) = a := by
  have h : ∃ it : Item, it.Valid q ∧ it.val q = a.val q := ⟨a, ha, rfl⟩
  rw [dec, dif_pos h]
  exact val_injective h.choose_spec.1 ha h.choose_spec.2

/-! ### Multisets of items -/

theorem count_range_ite (q c : ℕ) : (Multiset.range q).count c = if c < q then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup (Multiset.nodup_range q)]; simp [Multiset.mem_range]

theorem bind_replicate_eq (q : ℕ) (cs : Multiset ℕ) (hcs : ∀ c ∈ cs, c < q) :
    (Multiset.range q).bind (fun e => Multiset.replicate (cs.count e - 1) e) =
      cs - Multiset.range q := by
  ext c
  rw [Multiset.count_bind, Multiset.count_sub, count_range_ite]
  have : (Multiset.map (fun b => Multiset.count c (Multiset.replicate (cs.count b - 1) b))
      (Multiset.range q)) = (Multiset.range q).map (fun b => if b = c then cs.count c - 1 else 0) := by
    apply Multiset.map_congr rfl
    intro b _
    rw [Multiset.count_replicate]
    by_cases h : b = c <;> simp [h]
  rw [this]
  by_cases hc : c < q
  · rw [Multiset.sum_map_eq_nsmul_single c]
    · simp [hc, count_range_ite]
    · intro b hne _; simp [hne]
  · have h0 : cs.count c = 0 := Multiset.count_eq_zero.2 (fun h => hc (hcs c h))
    simp [h0, hc]

theorem elemItems_coe (mk : Bool → ℕ → Item) (cs : List ℕ)
    (q : ℕ) (hcs : ∀ c ∈ cs, c < q) :
    (elemItems mk cs q : Multiset Item) = (Multiset.range q).map (mk false) +
      ((cs : Multiset ℕ) - Multiset.range q).map (mk true) := by
  have h1 : (elemItems mk cs q : Multiset Item) = (Multiset.range q).bind
      (fun e => mk false e ::ₘ Multiset.replicate (cs.count e - 1) (mk true e)) := by
    unfold elemItems
    rw [← Multiset.coe_bind, Multiset.range]
    congr 1
  rw [h1, Multiset.bind_cons, ← bind_replicate_eq q cs hcs, Multiset.map_bind]
  congr 1
  refine congrArg _ (funext fun e => ?_)
  rw [Multiset.map_replicate, Multiset.coe_count]

theorem coe_shape (t : ℕ × ℕ × ℕ) (d : Bool) :
    (shape t d : Multiset Item) =
      Item.trip t ::ₘ Item.w d t.1 ::ₘ Item.x d t.2.1 ::ₘ Item.y d t.2.2 ::ₘ 0 := rfl

theorem bind_shape (S : Multiset (ℕ × ℕ × ℕ)) (d : Bool) :
    S.bind (fun t => (shape t d : Multiset Item)) = S.map Item.trip +
      ((S.map fun t => t.1).map (Item.w d) + ((S.map fun t => t.2.1).map (Item.x d) +
        ((S.map fun t => t.2.2).map (Item.y d) + 0))) := by
  simp only [coe_shape, Multiset.bind_cons, Multiset.map_map, Function.comp_def,
    Multiset.bind_zero]

theorem sum_shape {q : ℕ} {t : ℕ × ℕ × ℕ} (ht : (Item.trip t).Valid q) (d : Bool) :
    ((shape t d).map (Item.val q)).sum = bigB q := by
  simp only [Item.Valid] at ht
  rw [sum_val, bigB]
  simp only [shape, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Item.d0, Item.d1,
    Item.d2, Item.d3, Item.d4]
  have e1 : q - t.1 + (t.1 + (0 + (0 + 0))) = q := by omega
  have e2 : q - t.2.1 + (0 + (t.2.1 + (0 + 0))) = q := by omega
  have e3 : q - t.2.2 + (0 + (0 + (t.2.2 + 0))) = q := by omega
  rw [e1, e2, e3]
  cases d <;> rfl

theorem items_valid {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) : ∀ it ∈ items q M, it.Valid q := by
  intro it hit
  simp only [items, elemItems, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_replicate] at hit
  rcases hit with ((⟨t, ht, rfl⟩ | ⟨e, he, rfl | ⟨-, rfl⟩⟩) | ⟨e, he, rfl | ⟨-, rfl⟩⟩) |
      ⟨e, he, rfl | ⟨-, rfl⟩⟩
  · exact hM t ht
  all_goals simp_all [Item.Valid]

theorem coe_items {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) :
    (items q M : Multiset Item) = (M : Multiset _).map Item.trip +
      ((Multiset.range q).map (Item.w false) +
        (((M.map fun t => t.1 : List ℕ) : Multiset ℕ) - Multiset.range q).map (Item.w true)) +
      ((Multiset.range q).map (Item.x false) +
        (((M.map fun t => t.2.1 : List ℕ) : Multiset ℕ) - Multiset.range q).map (Item.x true)) +
      ((Multiset.range q).map (Item.y false) +
        (((M.map fun t => t.2.2 : List ℕ) : Multiset ℕ) - Multiset.range q).map (Item.y true)) := by
  rw [items, ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add,
    elemItems_coe _ _ _ (by simp only [List.mem_map]; rintro _ ⟨t, ht, rfl⟩; exact (hM t ht).1),
    elemItems_coe _ _ _ (by simp only [List.mem_map]; rintro _ ⟨t, ht, rfl⟩; exact (hM t ht).2.1),
    elemItems_coe _ _ _ (by simp only [List.mem_map]; rintro _ ⟨t, ht, rfl⟩; exact (hM t ht).2.2)]
  rfl

theorem map_sub_of_le {α β : Type} [DecidableEq α] [DecidableEq β] {S T : Multiset α} (h : S ≤ T)
    (f : α → β) : (T - S).map f = T.map f - S.map f := by
  obtain ⟨U, rfl⟩ := Multiset.le_iff_exists_add.1 h
  simp [Multiset.map_add]

/-! ### From a matching to a partition -/

theorem esp_of_has3DM {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (h : Has3DM q M) :
    EqualSumPartition (numInst q M) (bigB q) M.length := by
  obtain ⟨S, hSM, h1, h2, h3⟩ := h
  set R : Multiset (ℕ × ℕ × ℕ) := (M : Multiset _) - S with hR
  have hSR : S + R = M := by rw [hR]; exact add_tsub_cancel_of_le hSM
  have hvS : ∀ t ∈ S.toList, (Item.trip t).Valid q := fun t ht =>
    hM t (by rw [← Multiset.mem_coe]; exact Multiset.mem_of_le hSM (Multiset.mem_toList.1 ht))
  have hvR : ∀ t ∈ R.toList, (Item.trip t).Valid q := fun t ht =>
    hM t (by
      rw [← Multiset.mem_coe]
      exact Multiset.mem_of_le (Multiset.sub_le_self _ _) (Multiset.mem_toList.1 ht))
  refine ⟨(S.toList.map fun t => (shape t false).map (Item.val q)) ++
    (R.toList.map fun t => (shape t true).map (Item.val q)), ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_map, Multiset.length_toList]
    rw [← Multiset.card_add, hSR, Multiset.coe_card]
  · rw [← Multiset.coe_eq_coe, numInst, ← Multiset.map_coe, coe_items hM]
    rw [List.flatten_append, ← Multiset.coe_add]
    have hb : ∀ (L : List (ℕ × ℕ × ℕ)) (d : Bool),
        ((L.map fun t => (shape t d).map (Item.val q)).flatten : Multiset ℕ) =
          ((L : Multiset _).bind fun t => (shape t d : Multiset Item)).map (Item.val q) := by
      intro L d
      induction L with
      | nil => simp
      | cons a L ih =>
        rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, ← Multiset.cons_coe,
          Multiset.cons_bind, Multiset.map_add, Multiset.map_coe]
    rw [hb, hb, Multiset.coe_toList, Multiset.coe_toList, ← Multiset.map_add]
    congr 1
    rw [bind_shape, bind_shape, h1, h2, h3]
    have e1 : R.map (fun t => t.1) = ((M.map fun t => t.1 : List ℕ) : Multiset ℕ) - Multiset.range q := by
      rw [hR, map_sub_of_le hSM, h1, Multiset.map_coe]
    have e2 : R.map (fun t => t.2.1) = ((M.map fun t => t.2.1 : List ℕ) : Multiset ℕ) - Multiset.range q := by
      rw [hR, map_sub_of_le hSM, h2, Multiset.map_coe]
    have e3 : R.map (fun t => t.2.2) = ((M.map fun t => t.2.2 : List ℕ) : Multiset ℕ) - Multiset.range q := by
      rw [hR, map_sub_of_le hSM, h3, Multiset.map_coe]
    rw [e1, e2, e3, ← hSR, Multiset.map_add]
    abel
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact sum_shape (hvS t ht) false
    · exact sum_shape (hvR t ht) true

/-! ### From a partition to a matching -/

theorem count_eq_sum_ite {α : Type} [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    l.count a = (l.map fun x => if x == a then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons b l ih => by_cases h : b = a <;> simp [h, ih]; omega

theorem sum_map_filter_ite {α : Type} (l : List α) (c : α → Bool) (h : α → ℕ) :
    ((l.filter c).map h).sum = (l.map fun x => if c x then h x else 0).sum := by
  induction l with
  | nil => simp
  | cons b l ih => by_cases hb : c b <;> simp [hb, ih]

theorem perm_shape_data {q : ℕ} : ∀ gs : List (List ℕ),
    (∀ g ∈ gs, ∃ t d, (Item.trip t).Valid q ∧ (g.map (dec q)).Perm (shape t d)) →
    ∃ P : List ((ℕ × ℕ × ℕ) × Bool),
      ((gs.map (List.map (dec q))).flatten).Perm (P.flatMap fun p => shape p.1 p.2) ∧
        ∀ p ∈ P, (Item.trip p.1).Valid q
  | [], _ => ⟨[], by simp, by simp⟩
  | g :: gs, h => by
    obtain ⟨t, d, ht, hp⟩ := h g (by simp)
    obtain ⟨P, hP, hv⟩ := perm_shape_data gs fun g' hg' => h g' (by simp [hg'])
    refine ⟨(t, d) :: P, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, List.flatMap_cons]
      exact hp.append hP
    · intro p hp'
      rcases List.mem_cons.1 hp' with rfl | hp'
      · exact ht
      · exact hv p hp'

theorem count_trip_items {q : ℕ} {M : List (ℕ × ℕ × ℕ)} (t : ℕ × ℕ × ℕ) :
    (items q M).count (Item.trip t) = M.count t := by
  have hz : ∀ (mk : Bool → ℕ → Item) (cs : List ℕ), (∀ d e, mk d e ≠ Item.trip t) →
      (elemItems mk cs q).count (Item.trip t) = 0 := by
    intro mk cs hmk
    apply List.count_eq_zero_of_not_mem
    simp only [elemItems, List.mem_flatMap, List.mem_cons, List.mem_replicate, not_exists,
      not_and]
    intro e _ h
    rcases h with h | ⟨-, h⟩
    · exact hmk _ _ h.symm
    · exact hmk _ _ h.symm
  simp only [items, List.count_append]
  rw [hz _ _ (fun _ _ => Item.noConfusion), hz _ _ (fun _ _ => Item.noConfusion),
    hz _ _ (fun _ _ => Item.noConfusion)]
  rw [List.count_map_of_injective _ _ (fun a b h => by cases h; rfl)]
  simp

theorem count_map_eq_zero {α : Type} (s : Multiset α) (f : α → Item) (a : Item)
    (hf : ∀ x, f x ≠ a) : (s.map f).count a = 0 :=
  Multiset.count_eq_zero.2 fun h => by
    obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 h; exact hf x hx

theorem count_w_items {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (e : ℕ) :
    (items q M).count (Item.w false e) = if e < q then 1 else 0 := by
  rw [← Multiset.coe_count, coe_items hM]
  have iw : Function.Injective (Item.w false) := fun a b h => by cases h; rfl
  simp only [Multiset.count_add]
  rw [Multiset.count_map_eq_count' _ _ iw, count_range_ite,
    count_map_eq_zero (f := Item.trip) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.w true) _ _ (fun _ h => by cases h),
    count_map_eq_zero (f := Item.x false) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.x true) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.y false) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.y true) _ _ (fun _ => Item.noConfusion)]
  simp

theorem count_x_items {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (e : ℕ) :
    (items q M).count (Item.x false e) = if e < q then 1 else 0 := by
  rw [← Multiset.coe_count, coe_items hM]
  have ix : Function.Injective (Item.x false) := fun a b h => by cases h; rfl
  simp only [Multiset.count_add]
  rw [Multiset.count_map_eq_count' _ _ ix, count_range_ite,
    count_map_eq_zero (f := Item.trip) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.w false) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.w true) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.x true) _ _ (fun _ h => by cases h),
    count_map_eq_zero (f := Item.y false) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.y true) _ _ (fun _ => Item.noConfusion)]
  simp

theorem count_y_items {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (e : ℕ) :
    (items q M).count (Item.y false e) = if e < q then 1 else 0 := by
  rw [← Multiset.coe_count, coe_items hM]
  have iy : Function.Injective (Item.y false) := fun a b h => by cases h; rfl
  simp only [Multiset.count_add]
  rw [Multiset.count_map_eq_count' _ _ iy, count_range_ite,
    count_map_eq_zero (f := Item.trip) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.w false) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.w true) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.x false) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.x true) _ _ (fun _ => Item.noConfusion),
    count_map_eq_zero (f := Item.y true) _ _ (fun _ h => by cases h)]
  simp

theorem count_flatMap_shape (P : List ((ℕ × ℕ × ℕ) × Bool)) (a : Item) :
    (P.flatMap fun p => shape p.1 p.2).count a = (P.map fun p => (shape p.1 p.2).count a).sum :=
  by rw [List.count_flatMap]; rfl

/-- **From a partition to a matching.** -/
theorem has3DM_of_esp {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q)
    (h : EqualSumPartition (numInst q M) (bigB q) M.length) : Has3DM q M := by
  obtain ⟨gs, -, hperm, hsum⟩ := h
  have hval := items_valid hM
  have hmem : ∀ v ∈ gs.flatten, ∃ it ∈ items q M, it.val q = v := fun v hv => by
    have := hperm.subset hv
    simpa [numInst] using this
  have hdv : ∀ v ∈ gs.flatten, Item.val q (dec q v) = v ∧ (dec q v).Valid q := by
    intro v hv
    obtain ⟨it, hit, rfl⟩ := hmem v hv
    rw [dec_val (hval _ hit)]
    exact ⟨rfl, hval _ hit⟩
  have hgs : ∀ g ∈ gs, ∃ t d, (Item.trip t).Valid q ∧ (g.map (dec q)).Perm (shape t d) := by
    intro g hg
    have hg' : ∀ v ∈ g, v ∈ gs.flatten := fun v hv => List.mem_flatten.2 ⟨g, hg, hv⟩
    apply group_shape
    · intro it hit
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hit
      exact (hdv v (hg' v hv)).2
    · rw [List.map_map]
      have : g.map (Item.val q ∘ dec q) = g := by
        conv_rhs => rw [← List.map_id g]
        exact List.map_congr_left fun v hv => (hdv v (hg' v hv)).1
      rw [this, hsum g hg]
  obtain ⟨P, hP, -⟩ := perm_shape_data gs hgs
  have hI : (items q M).Perm (P.flatMap fun p => shape p.1 p.2) := by
    have h1 : (gs.map (List.map (dec q))).flatten = gs.flatten.map (dec q) :=
      List.map_flatten.symm
    have h3 : (numInst q M).map (dec q) = items q M := by
      rw [numInst, List.map_map]
      conv_rhs => rw [← List.map_id (items q M)]
      exact List.map_congr_left fun it hit => dec_val (hval it hit)
    rw [← h3]
    exact (hperm.map (dec q)).symm.trans (h1 ▸ hP)
  have hc := List.perm_iff_count.1 hI
  -- the selected triples
  have key : ∀ (f : ℕ × ℕ × ℕ → ℕ) (mk : ℕ → Item),
      (∀ t d, (shape t d).count (mk (f t)) = if d = false then 1 else 0) →
      (∀ t d e, f t ≠ e → (shape t d).count (mk e) = 0) →
      (∀ e, (items q M).count (mk e) = if e < q then 1 else 0) →
      ((((P.filter fun p => !p.2).map Prod.fst).map f : List ℕ) : Multiset ℕ) =
        Multiset.range q := by
    intro f mk h1 h0 hcnt
    ext e
    rw [Multiset.coe_count, count_range_ite, ← hcnt e, hc, count_flatMap_shape, List.map_map,
      count_eq_sum_ite, List.map_map, sum_map_filter_ite]
    congr 1
    apply List.map_congr_left
    rintro ⟨t, d⟩ -
    simp only [Function.comp_apply]
    by_cases hfe : f t = e
    · subst hfe; rw [h1]; cases d <;> simp
    · rw [h0 t d e hfe]; cases d <;> simp [hfe]
  refine ⟨((P.filter fun p => !p.2).map Prod.fst : List _), ?_, ?_, ?_, ?_⟩
  · have hPM : ((P.map Prod.fst : List (ℕ × ℕ × ℕ)) : Multiset (ℕ × ℕ × ℕ)) = (M : Multiset (ℕ × ℕ × ℕ)) := by
      rw [Multiset.coe_eq_coe, List.perm_iff_count]
      intro t
      have := hc (Item.trip t)
      rw [count_trip_items, count_flatMap_shape] at this
      rw [this, count_eq_sum_ite, List.map_map]
      congr 1
      apply List.map_congr_left
      rintro ⟨t', d⟩ -
      by_cases h : t' = t
      · subst h; simp [shape]
      · simp [shape, h]
    rw [← hPM]
    exact Multiset.coe_le.mpr ((List.filter_sublist).map _).subperm
  · rw [Multiset.map_coe]
    exact key (fun t => t.1) (Item.w false)
      (fun t d => by cases d <;> simp [shape])
      (fun t d e h => by cases d <;> simp [shape, h])
      (count_w_items hM)
  · rw [Multiset.map_coe]
    exact key (fun t => t.2.1) (Item.x false)
      (fun t d => by cases d <;> simp [shape])
      (fun t d e h => by cases d <;> simp [shape, h])
      (count_x_items hM)
  · rw [Multiset.map_coe]
    exact key (fun t => t.2.2) (Item.y false)
      (fun t d => by cases d <;> simp [shape])
      (fun t d e h => by cases d <;> simp [shape, h])
      (count_y_items hM)

/-- The items of the numerical instance are positive. -/
theorem numInst_pos (q : ℕ) (M : List (ℕ × ℕ × ℕ)) : ∀ a ∈ numInst q M, 0 < a := by
  intro a ha
  obtain ⟨it, -, rfl⟩ := List.mem_map.1 ha
  unfold Item.val hor
  have : 0 < it.d0 := by cases it <;> simp [Item.d0]
  omega

/-- **3-dimensional matching reduces to the equal-sum partition problem in unary.** -/
theorem esp_numInst_iff {q : ℕ} {M : List (ℕ × ℕ × ℕ)}
    (hM : ∀ t ∈ M, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) :
    EqualSumPartition (numInst q M) (bigB q) M.length ↔ Has3DM q M :=
  ⟨has3DM_of_esp hM, esp_of_has3DM hM⟩

end HTN.NPHard
