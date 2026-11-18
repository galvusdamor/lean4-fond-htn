import HtnComplexity.NPHard.GJ
/-!
# Satisfiability to unary equal-sum partition, with explicit items

The numerical instance `numInst q (gj n φ)` of `FourPart.lean`/`GJ.lean` counts the occurrences
of every coordinate value.  For the instances `gj n φ` these counts are known in closed form, and
the items can be listed without counting (`numsOf`); the two lists are permutations of each other
(`perm_numInst_numsOf`), so they have the same equal-sum partitions:

* `HTN.NPHard.esp_numsOf_iff` — for `n ≥ 1` variables, variables below `n` and nonempty clauses,
  `numsOf n φ` splits into `|gj n φ|` groups of sum `bigB (gjq n φ)` exactly when `φ` is
  satisfiable.
-/

namespace HTN.NPHard

open Merge

/-! ### Perm and count helpers -/

theorem perm_flatMap_append {α β : Type} [DecidableEq β] (l : List α) (f g : α → List β) :
    (l.flatMap fun a => f a ++ g a).Perm (l.flatMap f ++ l.flatMap g) := by
  rw [List.perm_iff_count]
  intro b
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.count_append] at ih ⊢; omega

theorem count_flatMap_range_single {β : Type} [DecidableEq β] (q : ℕ) (f : ℕ → List β) (b : β)
    (e0 : ℕ) (hf : ∀ e, e ≠ e0 → (f e).count b = 0) :
    ((List.range q).flatMap f).count b = if e0 < q then (f e0).count b else 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases h : q = e0
    · subst h; simp
    · rw [hf q h]
      by_cases h' : e0 < q
      · simp [h', show e0 < q + 1 by omega]
      · simp [h', show ¬ e0 < q + 1 by omega]

/-- The items of a coordinate, when the coordinates are the values below `q` plus extra
occurrences `E`. -/
theorem elemItems_perm (mk : Bool → ℕ → Item)
    (hmk : ∀ d e d' e', mk d e = mk d' e' → d = d' ∧ e = e') {cs E : List ℕ} {q : ℕ}
    (hcs : cs.Perm (List.range q ++ E)) (hE : ∀ e ∈ E, e < q) :
    (elemItems mk cs q).Perm ((List.range q).map (mk false) ++ E.map (mk true)) := by
  rw [List.perm_iff_count]
  intro a
  have hcnt : ∀ e, cs.count e = (if e < q then 1 else 0) + E.count e := by
    intro e
    rw [hcs.count_eq, List.count_append, List.nodup_range.count]
    simp
  have hmapc : ∀ (d : Bool) (l : List ℕ) (e : ℕ), (l.map (mk d)).count (mk d e) = l.count e := by
    intro d l e
    rw [List.count_map_of_injective]
    intro x y h; exact (hmk d x d y h).2
  by_cases ha : ∃ d e, a = mk d e
  · obtain ⟨d, e, rfl⟩ := ha
    unfold elemItems
    rw [count_flatMap_range_single q _ _ e (fun e' he' => by
      simp only [List.count_cons, List.count_replicate]
      have h1 : ¬ (mk false e' == mk d e) = true := by
        simp only [beq_iff_eq]; intro h; exact he' (hmk _ _ _ _ h).2
      have h2 : ¬ (mk true e' == mk d e) = true := by
        simp only [beq_iff_eq]; intro h; exact he' (hmk _ _ _ _ h).2
      simp [h1, h2])]
    rw [List.count_append]
    cases d
    · rw [hmapc]
      have : (E.map (mk true)).count (mk false e) = 0 := by
        rw [List.count_eq_zero]; simp only [List.mem_map, not_exists, not_and]
        intro x _ h; exact absurd (hmk _ _ _ _ h).1 (by simp)
      rw [this, List.nodup_range.count]
      simp only [List.count_cons, List.count_replicate, beq_self_eq_true, ↓reduceIte, List.mem_range]
      have : ¬ (mk true e == mk false e) = true := by
        simp only [beq_iff_eq]; intro h; exact absurd (hmk _ _ _ _ h).1 (by simp)
      split_ifs <;> simp_all
    · rw [hmapc]
      have : ((List.range q).map (mk false)).count (mk true e) = 0 := by
        rw [List.count_eq_zero]; simp only [List.mem_map, not_exists, not_and]
        intro x _ h; exact absurd (hmk _ _ _ _ h).1 (by simp)
      rw [this]
      simp only [List.count_cons, List.count_replicate, beq_self_eq_true, ↓reduceIte]
      have h1 : ¬ (mk false e == mk true e) = true := by
        simp only [beq_iff_eq]; intro h; exact absurd (hmk _ _ _ _ h).1 (by simp)
      simp only [h1, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      rw [hcnt]
      by_cases hq : e < q
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        exact (List.count_eq_zero.2 fun h => hq (hE e h)).symm
  · push_neg at ha
    rw [List.count_append]
    have h1 : (elemItems mk cs q).count a = 0 := by
      rw [List.count_eq_zero]; unfold elemItems
      simp only [List.mem_flatMap, List.mem_cons, List.mem_replicate, not_exists, not_and]
      intro e _ h; rcases h with h | ⟨_, h⟩ <;> exact ha _ _ h
    have h2 : ((List.range q).map (mk false)).count a = 0 := by
      rw [List.count_eq_zero]; simp only [List.mem_map, not_exists, not_and]
      intro e _ h; exact ha _ _ h.symm
    have h3 : (E.map (mk true)).count a = 0 := by
      rw [List.count_eq_zero]; simp only [List.mem_map, not_exists, not_and]
      intro e _ h; exact ha _ _ h.symm
    rw [h1, h2, h3]

/-! ### The explicit items -/

section Explicit

variable (n : ℕ) (φ : CNF)

/-- The second coordinates of the `tF` triples. -/
def tFsec (n m : ℕ) : List ℕ := (List.range n).flatMap fun i => (List.range m).map fun j =>
  i * m + (j + 1) % m

/-- The third coordinates of the `tF` triples. -/
def tFthird (n m : ℕ) : List ℕ := (List.range n).flatMap fun i => (List.range m).map fun j =>
  i * m + j

/-- The further occurrences of the clause elements. -/
def clRest : List ℕ := (List.range φ.length).flatMap fun j =>
  List.replicate ((φ.getD j []).length - 1) (n * φ.length + j)

/-- The further occurrences of the garbage elements. -/
def gcRest (n m : ℕ) : List ℕ := (List.range (m * (n - 1))).flatMap fun k =>
  List.replicate (2 * n * m - 1) (n * m + m + k)

/-- The further occurrences of the first coordinates. -/
def E1 : List ℕ := (clTrip n φ).map (fun t => t.1) ++ (gcTrip n φ.length).map (fun t => t.1)

/-- The further occurrences of the second coordinates. -/
def E2 : List ℕ := tFsec n φ.length ++ clRest n φ ++ gcRest n φ.length

/-- The further occurrences of the third coordinates. -/
def E3 : List ℕ := tFthird n φ.length ++ clRest n φ ++ gcRest n φ.length

/-- The items, listed explicitly. -/
def itemsAlt : List Item :=
  (gj n φ).map Item.trip ++ (List.range (gjq n φ)).map (Item.w false) ++
    (List.range (gjq n φ)).map (Item.x false) ++ (List.range (gjq n φ)).map (Item.y false) ++
    (E1 n φ).map (Item.w true) ++ (E2 n φ).map (Item.x true) ++ (E3 n φ).map (Item.y true)

/-- **The numbers, listed explicitly.** -/
def numsOf : List ℕ := (itemsAlt n φ).map (Item.val (gjq n φ))

end Explicit

/-! ### The coordinates of `gj` -/

theorem gjq_split {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    2 * n * m = n * m + (m + m * (n - 1)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

theorem range_gjq {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    List.range (2 * n * m) = List.range (n * m) ++ (List.range m).map (n * m + ·) ++
      (List.range (m * (n - 1))).map (n * m + m + ·) := by
  rw [gjq_split hn, List.range_add, List.range_add, List.map_append, List.map_map]
  simp only [List.append_assoc]
  congr 3
  funext k; simp only [Function.comp]; ring

theorem flatMap_const_replicate {α : Type} (a c : ℕ) (x : α) :
    (List.range a).flatMap (fun _ => List.replicate c x) = List.replicate (a * c) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.replicate_add]
    simp

theorem ts_fst (n m : ℕ) : ((tsTrip n m).map fun t => t.1).Perm (List.range (2 * n * m)) := by
  have e : (tsTrip n m).map (fun t => t.1) =
      (List.range (n * m)).flatMap fun x => [2 * x + 1, 2 * x] := by
    rw [← flatMap_pairs]
    simp [tsTrip, List.map_flatMap, tT, tF, lit]
  rw [e, show 2 * n * m = 2 * (n * m) by ring, ← flatMap_double]
  exact List.Perm.flatMap_left _ fun x _ => List.Perm.swap _ _ _

theorem ts_snd (n m : ℕ) :
    ((tsTrip n m).map fun t => t.2.1).Perm (List.range (n * m) ++ tFsec n m) := by
  have e : (tsTrip n m).map (fun t => t.2.1) = (List.range n).flatMap fun i =>
      (List.range m).flatMap fun j => [i * m + j] ++ [i * m + (j + 1) % m] := by
    simp [tsTrip, List.map_flatMap, tT, tF]
  have hr : List.range (n * m) = (List.range n).flatMap (fun i => (List.range m).map fun j =>
      i * m + j) := by simpa using (map_pairs n m id).symm
  rw [e, tFsec, hr]
  refine (List.Perm.flatMap_left _ fun i _ => perm_flatMap_append _ _ _).trans ?_
  refine (perm_flatMap_append _ _ _).trans ?_
  simp [List.map_eq_flatMap]

theorem ts_thd (n m : ℕ) :
    ((tsTrip n m).map fun t => t.2.2).Perm (List.range (n * m) ++ tFthird n m) := by
  have e : (tsTrip n m).map (fun t => t.2.2) = (List.range n).flatMap fun i =>
      (List.range m).flatMap fun j => [i * m + j] ++ [i * m + j] := by
    simp [tsTrip, List.map_flatMap, tT, tF]
  have hr : List.range (n * m) = (List.range n).flatMap (fun i => (List.range m).map fun j =>
      i * m + j) := by simpa using (map_pairs n m id).symm
  rw [e, tFthird, hr]
  refine (List.Perm.flatMap_left _ fun i _ => perm_flatMap_append _ _ _).trans ?_
  refine (perm_flatMap_append _ _ _).trans ?_
  simp [List.map_eq_flatMap]

theorem cl_snd (n : ℕ) {φ : CNF} (hne : ∀ c ∈ φ, c ≠ []) :
    ((clTrip n φ).map fun t => t.2.1).Perm
      ((List.range φ.length).map (n * φ.length + ·) ++ clRest n φ) := by
  have e : (clTrip n φ).map (fun t => t.2.1) = (List.range φ.length).flatMap fun j =>
      [n * φ.length + j] ++ List.replicate ((φ.getD j []).length - 1) (n * φ.length + j) := by
    simp only [clTrip, List.map_flatMap, List.map_map]
    refine List.flatMap_congr fun j hj => ?_
    rw [List.mem_range] at hj
    have hpos : 0 < (φ.getD j []).length :=
      List.length_pos_iff.2 (hne _ (getD_mem hj))
    rw [show (Function.comp (fun t : ℕ × ℕ × ℕ => t.2.1) fun l : ℕ × Bool =>
        (lit φ.length l.1 j l.2, n * φ.length + j, n * φ.length + j)) =
        fun _ => n * φ.length + j from rfl, List.map_const', List.singleton_append,
      ← List.replicate_succ, Nat.sub_add_cancel hpos]
  rw [e, clRest]
  refine (perm_flatMap_append _ _ _).trans ?_
  simp [List.map_eq_flatMap]

theorem cl_thd (n : ℕ) (φ : CNF) :
    ((clTrip n φ).map fun t => t.2.2) = (clTrip n φ).map fun t => t.2.1 := by
  simp only [clTrip, List.map_flatMap, List.map_map]; rfl

theorem gc_snd {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ((gcTrip n m).map fun t => t.2.1).Perm
      ((List.range (m * (n - 1))).map (n * m + m + ·) ++ gcRest n m) := by
  have e : (gcTrip n m).map (fun t => t.2.1) = (List.range (m * (n - 1))).flatMap fun k =>
      [n * m + m + k] ++ List.replicate (2 * n * m - 1) (n * m + m + k) := by
    simp only [gcTrip, List.map_flatMap]
    refine List.flatMap_congr fun k hk => ?_
    rw [List.mem_range] at hk
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hk
      · exact h
    have h1 : (List.range n).flatMap (fun i => (List.range m).flatMap fun j =>
        List.map (fun t : ℕ × ℕ × ℕ => t.2.1)
          [(lit m i j true, n * m + m + k, n * m + m + k),
            (lit m i j false, n * m + m + k, n * m + m + k)]) =
        List.replicate (n * (m * 2)) (n * m + m + k) := by
      simp only [List.map_cons, List.map_nil]
      rw [← flatMap_const_replicate n (m * 2), ← flatMap_const_replicate m 2]
      rfl
    rw [h1, List.singleton_append, ← List.replicate_succ]
    congr 1
    have : 1 ≤ n * m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [show 2 * n * m = 2 * (n * m) by ring]
    rw [show n * (m * 2) = 2 * (n * m) by ring]; omega
  rw [e, gcRest]
  refine (perm_flatMap_append _ _ _).trans ?_
  simp [List.map_eq_flatMap]

theorem gc_thd (n m : ℕ) :
    ((gcTrip n m).map fun t => t.2.2) = (gcTrip n m).map fun t => t.2.1 := by
  simp [gcTrip, List.map_flatMap]

theorem perm_cs1 (n : ℕ) (φ : CNF) :
    ((gj n φ).map fun t => t.1).Perm (List.range (gjq n φ) ++ E1 n φ) := by
  simp only [gj, List.map_append, E1, gjq]
  rw [List.append_assoc]
  exact (ts_fst n φ.length).append_right _

theorem perm_shuffle3 {α : Type} [DecidableEq α] (a b c d e f : List α) :
    ((a ++ b) ++ (c ++ d) ++ (e ++ f)).Perm ((a ++ c ++ e) ++ (b ++ d ++ f)) := by
  rw [List.perm_iff_count]; intro x; simp only [List.count_append]; omega

theorem perm_cs2 {n : ℕ} (hn : 1 ≤ n) {φ : CNF} (hne : ∀ c ∈ φ, c ≠ []) :
    ((gj n φ).map fun t => t.2.1).Perm (List.range (gjq n φ) ++ E2 n φ) := by
  simp only [gj, List.map_append, E2, gjq]
  rw [range_gjq hn]
  exact (((ts_snd n φ.length).append (cl_snd n hne)).append (gc_snd hn φ.length)).trans
    (perm_shuffle3 _ _ _ _ _ _)

theorem perm_cs3 {n : ℕ} (hn : 1 ≤ n) {φ : CNF} (hne : ∀ c ∈ φ, c ≠ []) :
    ((gj n φ).map fun t => t.2.2).Perm (List.range (gjq n φ) ++ E3 n φ) := by
  simp only [gj, List.map_append, E3, gjq]
  rw [range_gjq hn, cl_thd, gc_thd]
  exact (((ts_thd n φ.length).append (cl_snd n hne)).append (gc_snd hn φ.length)).trans
    (perm_shuffle3 _ _ _ _ _ _)

theorem perm_items {n : ℕ} (hn : 1 ≤ n) {φ : CNF} (hv : ∀ c ∈ φ, ∀ l ∈ c, l.1 < n)
    (hne : ∀ c ∈ φ, c ≠ []) : (items (gjq n φ) (gj n φ)).Perm (itemsAlt n φ) := by
  have hlt := gj_lt hn hv
  have hE : ∀ (f : ℕ × ℕ × ℕ → ℕ) (E : List ℕ), (∀ t ∈ gj n φ, f t < gjq n φ) →
      ((gj n φ).map f).Perm (List.range (gjq n φ) ++ E) → ∀ e ∈ E, e < gjq n φ := by
    intro f E hf hp e he
    have : e ∈ (gj n φ).map f := hp.symm.subset (List.mem_append_right _ he)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 this
    exact hf t ht
  have p1 := perm_cs1 n φ
  have p2 := perm_cs2 hn hne
  have p3 := perm_cs3 hn hne
  have q1 := elemItems_perm Item.w (fun d e d' e' h => by cases h; exact ⟨rfl, rfl⟩) p1
    (hE _ _ (fun t ht => (hlt t ht).1) p1)
  have q2 := elemItems_perm Item.x (fun d e d' e' h => by cases h; exact ⟨rfl, rfl⟩) p2
    (hE _ _ (fun t ht => (hlt t ht).2.1) p2)
  have q3 := elemItems_perm Item.y (fun d e d' e' h => by cases h; exact ⟨rfl, rfl⟩) p3
    (hE _ _ (fun t ht => (hlt t ht).2.2) p3)
  unfold items itemsAlt
  refine ((((List.Perm.refl _).append q1).append q2).append q3).trans ?_
  rw [List.perm_iff_count]; intro x; simp only [List.count_append]; omega

theorem perm_numInst_numsOf {n : ℕ} (hn : 1 ≤ n) {φ : CNF} (hv : ∀ c ∈ φ, ∀ l ∈ c, l.1 < n)
    (hne : ∀ c ∈ φ, c ≠ []) : (numInst (gjq n φ) (gj n φ)).Perm (numsOf n φ) :=
  (perm_items hn hv hne).map _

theorem esp_perm {as as' : List ℕ} {B m : ℕ} (h : as.Perm as') :
    EqualSumPartition as B m ↔ EqualSumPartition as' B m := by
  constructor
  · rintro ⟨gs, h1, h2, h3⟩; exact ⟨gs, h1, h2.trans h, h3⟩
  · rintro ⟨gs, h1, h2, h3⟩; exact ⟨gs, h1, h2.trans h.symm, h3⟩

/-- **Satisfiability reduces to the explicit numerical instance.** -/
theorem esp_numsOf_iff {n : ℕ} (hn : 1 ≤ n) {φ : CNF} (hv : ∀ c ∈ φ, ∀ l ∈ c, l.1 < n)
    (hne : ∀ c ∈ φ, c ≠ []) :
    EqualSumPartition (numsOf n φ) (bigB (gjq n φ)) (gj n φ).length ↔ Satisfiable φ := by
  rw [← esp_perm (perm_numInst_numsOf hn hv hne), esp_numInst_iff (gj_lt hn hv),
    has3DM_gj_iff hn hv]

theorem numsOf_pos (n : ℕ) (φ : CNF) : ∀ a ∈ numsOf n φ, 0 < a := by
  intro a ha
  obtain ⟨it, -, rfl⟩ := List.mem_map.1 ha
  unfold Item.val hor
  have : 0 < it.d0 := by cases it <;> simp [Item.d0]
  omega

end HTN.NPHard
