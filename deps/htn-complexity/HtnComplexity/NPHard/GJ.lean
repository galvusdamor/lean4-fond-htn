import HtnComplexity.NPHard.FourPart
/-!
# From satisfiability to 3-dimensional matching

The classical reduction of Garey and Johnson from satisfiability of formulas in conjunctive
normal form to 3-dimensional matching, for formulas with `n ≥ 1` variables `0, …, n - 1` and
`m` clauses (of any length).

The three coordinates are numbered as follows (`i < n`, `j < m`):

* first coordinate: the literal elements `lit m i j b = 2 (i m + j) + [b = false]`;
* second and third coordinates: the ring elements `i m + j`, the clause elements `n m + j`, and
  the garbage elements `n m + m + k` for `k < m (n - 1)`.

The triples are the truth-setting rings, one triple per literal occurrence of a clause, and the
garbage collection triples.  The main result is `HTN.NPHard.has3DM_gj_iff`.
-/

namespace HTN.NPHard

/-- A formula in conjunctive normal form: a list of clauses, each a list of literals
`(variable, sign)`. -/
abbrev CNF : Type := List (List (ℕ × Bool))

/-- The assignment `σ` satisfies the formula. -/
def Sat (σ : ℕ → Bool) (φ : CNF) : Prop := ∀ c ∈ φ, ∃ l ∈ c, σ l.1 = l.2

/-- The formula is satisfiable. -/
def Satisfiable (φ : CNF) : Prop := ∃ σ, Sat σ φ

/-- The literal element of the variable `i` in the column `j`. -/
def lit (m i j : ℕ) (b : Bool) : ℕ := 2 * (i * m + j) + if b then 0 else 1

/-- The truth-setting triple of the variable `i` in the column `j` chosen when `i` is true
(it covers the negative literal element). -/
def tT (m i j : ℕ) : ℕ × ℕ × ℕ := (lit m i j false, i * m + j, i * m + j)

/-- The truth-setting triple of the variable `i` in the column `j` chosen when `i` is false. -/
def tF (m i j : ℕ) : ℕ × ℕ × ℕ := (lit m i j true, i * m + (j + 1) % m, i * m + j)

/-- The truth-setting rings. -/
def tsTrip (n m : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range m).flatMap fun j => [tT m i j, tF m i j]

/-- The clause triples: one for every literal of every clause. -/
def clTrip (n : ℕ) (φ : CNF) : List (ℕ × ℕ × ℕ) :=
  (List.range φ.length).flatMap fun j =>
    (φ.getD j []).map fun l => (lit φ.length l.1 j l.2, n * φ.length + j, n * φ.length + j)

/-- The garbage collection triples. -/
def gcTrip (n m : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (m * (n - 1))).flatMap fun k => (List.range n).flatMap fun i =>
    (List.range m).flatMap fun j =>
      [(lit m i j true, n * m + m + k, n * m + m + k), (lit m i j false, n * m + m + k, n * m + m + k)]

/-- **The 3-dimensional matching instance of a formula.** -/
def gj (n : ℕ) (φ : CNF) : List (ℕ × ℕ × ℕ) :=
  tsTrip n φ.length ++ clTrip n φ ++ gcTrip n φ.length

/-- The size of the instance. -/
def gjq (n : ℕ) (φ : CNF) : ℕ := 2 * n * φ.length

/-! ### Arithmetic of the numbering -/

theorem pair_inj {m i j i' j' : ℕ} (hj : j < m) (hj' : j' < m) (h : i * m + j = i' * m + j') :
    i = i' ∧ j = j' := by
  have hm : 0 < m := by omega
  have h1 : (i * m + j) / m = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (i' * m + j') / m = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj', Nat.zero_add]
  have hi : i = i' := by rw [← h1, ← h2, h]
  subst hi
  exact ⟨rfl, by omega⟩

theorem pair_lt {n m i j : ℕ} (hi : i < n) (hj : j < m) : i * m + j < n * m := by
  have : (i + 1) * m ≤ n * m := Nat.mul_le_mul_right _ hi
  nlinarith

theorem lit_inj {m i j i' j' : ℕ} {b b' : Bool} (hj : j < m) (hj' : j' < m)
    (h : lit m i j b = lit m i' j' b') : i = i' ∧ j = j' ∧ b = b' := by
  unfold lit at h
  have hb : b = b' := by
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> first | rfl | omega
  subst hb
  have : i * m + j = i' * m + j' := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> omega
  obtain ⟨rfl, rfl⟩ := pair_inj hj hj' this
  exact ⟨rfl, rfl, rfl⟩

theorem lit_lt {n m i j : ℕ} (b : Bool) (hi : i < n) (hj : j < m) : lit m i j b < 2 * n * m := by
  have := pair_lt hi hj
  have e : 2 * n * m = 2 * (n * m) := by ring
  rw [e]
  unfold lit; split <;> omega

theorem getD_mem {φ : CNF} {j : ℕ} (hj : j < φ.length) : φ.getD j [] ∈ φ := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

theorem mem_gj {n : ℕ} {φ : CNF} {t : ℕ × ℕ × ℕ} :
    t ∈ gj n φ ↔
      (∃ i < n, ∃ j < φ.length, t = tT φ.length i j ∨ t = tF φ.length i j) ∨
      (∃ j < φ.length, ∃ l ∈ φ.getD j [],
        t = (lit φ.length l.1 j l.2, n * φ.length + j, n * φ.length + j)) ∨
      (∃ k < φ.length * (n - 1), ∃ i < n, ∃ j < φ.length, ∃ b,
        t = (lit φ.length i j b, n * φ.length + φ.length + k, n * φ.length + φ.length + k)) := by
  simp only [gj, tsTrip, clTrip, gcTrip, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_map, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨i, hi, j, hj, h⟩ | ⟨j, hj, l, hl, rfl⟩) | ⟨k, hk, i, hi, j, hj, h⟩)
    · exact Or.inl ⟨i, hi, j, hj, h⟩
    · exact Or.inr (Or.inl ⟨j, hj, l, hl, rfl⟩)
    · rcases h with h | h
      · exact Or.inr (Or.inr ⟨k, hk, i, hi, j, hj, true, h⟩)
      · exact Or.inr (Or.inr ⟨k, hk, i, hi, j, hj, false, h⟩)
  · rintro (⟨i, hi, j, hj, h⟩ | ⟨j, hj, l, hl, rfl⟩ | ⟨k, hk, i, hi, j, hj, b, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, hi, j, hj, h⟩)
    · exact Or.inl (Or.inr ⟨j, hj, l, hl, rfl⟩)
    · cases b
      · exact Or.inr ⟨k, hk, i, hi, j, hj, Or.inr rfl⟩
      · exact Or.inr ⟨k, hk, i, hi, j, hj, Or.inl rfl⟩

/-- **The coordinates of the instance are below its size.** -/
theorem gj_lt {n : ℕ} {φ : CNF} (hn : 1 ≤ n) (hv : ∀ c ∈ φ, ∀ l ∈ c, l.1 < n) :
    ∀ t ∈ gj n φ, t.1 < gjq n φ ∧ t.2.1 < gjq n φ ∧ t.2.2 < gjq n φ := by
  intro t ht
  have e : gjq n φ = n * φ.length + φ.length + φ.length * (n - 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [gjq, Nat.add_sub_cancel]; ring
  have e' : 2 * n * φ.length = n * φ.length + φ.length + φ.length * (n - 1) := e
  rw [e]
  rcases mem_gj.1 ht with ⟨i, hi, j, hj, rfl | rfl⟩ | ⟨j, hj, l, hl, rfl⟩ |
      ⟨k, hk, i, hi, j, hj, b, rfl⟩
  · have := pair_lt hi hj
    have := lit_lt false hi hj
    simp only [tT]; omega
  · have := pair_lt hi hj
    have : (j + 1) % φ.length < φ.length := Nat.mod_lt _ (by omega)
    have := pair_lt hi this
    have := lit_lt true hi hj
    simp only [tF]; omega
  · have hl1 : l.1 < n := hv _ (getD_mem hj) l hl
    have := lit_lt l.2 hl1 hj
    simp only; omega
  · have := lit_lt b hi hj
    simp only; omega

/-! ### List lemmas -/

theorem flatMap_pairs {α : Type} (n m : ℕ) (F : ℕ → List α) :
    (List.range n).flatMap (fun i => (List.range m).flatMap fun j => F (i * m + j)) =
      (List.range (n * m)).flatMap F := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add,
      List.flatMap_append]
    simp [List.flatMap_map, Nat.add_comm]

theorem map_pairs {α : Type} (n m : ℕ) (F : ℕ → α) :
    (List.range n).flatMap (fun i => (List.range m).map fun j => F (i * m + j)) =
      (List.range (n * m)).map F := by
  have := flatMap_pairs n m (fun x => [F x])
  simpa [List.flatMap_singleton', List.map_eq_flatMap] using this

theorem flatMap_double (N : ℕ) :
    (List.range N).flatMap (fun x => [2 * x, 2 * x + 1]) = List.range (2 * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
      List.range_succ, List.range_succ]
    simp

theorem rot_perm (m : ℕ) : ((List.range m).map fun j => (j + 1) % m).Perm (List.range m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hinj : ∀ a ∈ List.range m, ∀ b ∈ List.range m, (a + 1) % m = (b + 1) % m → a = b := by
    intro a ha b hb h
    simp only [List.mem_range] at ha hb
    rcases Nat.lt_or_ge (a + 1) m with h1 | h1 <;> rcases Nat.lt_or_ge (b + 1) m with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
    · rw [Nat.mod_eq_of_lt h1, show b + 1 = m by omega, Nat.mod_self] at h; omega
    · rw [Nat.mod_eq_of_lt h2, show a + 1 = m by omega, Nat.mod_self] at h; omega
    · omega
  rw [List.perm_ext_iff_of_nodup ((List.nodup_range).map_on hinj) List.nodup_range]
  intro x
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, -, rfl⟩; exact Nat.mod_lt _ hm
  · intro hx
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · exact ⟨m - 1, by omega, by rw [show m - 1 + 1 = m by omega, Nat.mod_self]⟩
    · exact ⟨x - 1, by omega, by rw [show x - 1 + 1 = x by omega, Nat.mod_eq_of_lt hx]⟩

theorem filter_ne_length {n v : ℕ} (hv : v < n) :
    ((List.range n).filter fun i => i ≠ v).length = n - 1 := by
  have h := List.Nodup.erase_eq_filter (List.nodup_range (n := n)) v
  have : ((List.range n).filter fun i => i ≠ v) = (List.range n).filter fun i => i != v := by
    congr 1; funext i; by_cases h : i = v <;> simp [h]
  rw [this, ← h, List.length_erase_of_mem (List.mem_range.2 hv), List.length_range]

theorem sum_map_const_range (n c : ℕ) : ((List.range n).map fun _ => c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; ring

theorem map_range_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun k => f (l.getD k d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

/-! ### From a satisfying assignment to a matching -/

theorem has3DM_of_sat {n : ℕ} {φ : CNF} (hn : 1 ≤ n) (hv : ∀ c ∈ φ, ∀ l ∈ c, l.1 < n)
    (σ : ℕ → Bool) (hσ : Sat σ φ) : Has3DM (gjq n φ) (gj n φ) := by
  classical
  have hq : gjq n φ = n * φ.length + φ.length + φ.length * (n - 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [gjq, Nat.add_sub_cancel]; ring
  rw [hq]
  have hmem : ∀ t, t ∈ gj n φ ↔ _ := fun t => mem_gj (n := n) (φ := φ) (t := t)
  generalize hm : φ.length = m at hmem
  -- the chosen literals
  let pick : ℕ → ℕ × Bool := fun j =>
    if h : ∃ l ∈ φ.getD j [], σ l.1 = l.2 then h.choose else (0, true)
  have hpick : ∀ j < m, pick j ∈ φ.getD j [] ∧ σ (pick j).1 = (pick j).2 := fun j hj => by
    have h : ∃ l ∈ φ.getD j [], σ l.1 = l.2 := hσ _ (getD_mem (by omega))
    simp only [pick, dif_pos h]; exact h.choose_spec
  have hpn : ∀ j < m, (pick j).1 < n := fun j hj =>
    hv _ (getD_mem (by omega)) _ (hpick j hj).1
  -- the free literal elements not used by the clauses
  let R : List (ℕ × ℕ) := (List.range m).flatMap fun j =>
    ((List.range n).filter fun i => i ≠ (pick j).1).map fun i => (i, j)
  have hRlen : R.length = m * (n - 1) := by
    simp only [R, List.length_flatMap, List.length_map]
    rw [List.map_congr_left (g := fun _ => n - 1) (fun j hj =>
      filter_ne_length (hpn j (List.mem_range.1 hj)))]
    simp
  have hRmem : ∀ p, p ∈ R ↔ p.1 < n ∧ p.2 < m ∧ p.1 ≠ (pick p.2).1 := by
    rintro ⟨i, j⟩
    simp only [R, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
      decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨j', hj', i', ⟨hi', hne⟩, rfl, rfl⟩; exact ⟨hi', hj', hne⟩
    · rintro ⟨hi, hj, hne⟩; exact ⟨j, hj, i, ⟨hi, hne⟩, rfl, rfl⟩
  -- the matching
  let Lts : List (ℕ × ℕ × ℕ) := (List.range n).flatMap fun i =>
    (List.range m).map fun j => if σ i then tT m i j else tF m i j
  let Lcl : List (ℕ × ℕ × ℕ) :=
    (List.range m).map fun j => (lit m (pick j).1 j (pick j).2, n * m + j, n * m + j)
  let Lgc : List (ℕ × ℕ × ℕ) := (List.range (m * (n - 1))).map fun k =>
    (lit m (R.getD k (0, 0)).1 (R.getD k (0, 0)).2 (σ (R.getD k (0, 0)).1),
      n * m + m + k, n * m + m + k)
  let L := Lts ++ Lcl ++ Lgc
  -- the third coordinates
  have hY : L.map (fun t => t.2.2) = List.range (n * m + m + m * (n - 1)) := by
    rw [List.range_add, List.range_add]
    simp only [L, Lts, Lcl, Lgc, List.map_append, List.map_flatMap, List.map_map]
    congr 2
    · conv_rhs => rw [← List.map_id (List.range (n * m)), ← map_pairs n m id]
      congr 1; funext i; congr 1; funext j
      simp only [Function.comp_apply, id]
      split <;> rfl
  -- the second coordinates
  have hX : (L.map (fun t => t.2.1)).Perm (List.range (n * m + m + m * (n - 1))) := by
    rw [List.range_add, List.range_add]
    simp only [L, Lts, Lcl, Lgc, List.map_append, List.map_flatMap, List.map_map]
    refine (List.Perm.append (List.Perm.append ?_ (by rfl)) ?_)
    · conv_rhs => rw [← List.map_id (List.range (n * m)), ← map_pairs n m id]
      refine List.Perm.flatMap_left _ fun i _ => ?_
      by_cases h : σ i
      · simp [h, tT, Function.comp_def]
      · simp only [h, Function.comp_def, tF, id, Bool.false_eq_true, if_false]
        have := (rot_perm m).map (fun j => i * m + j)
        simpa [List.map_map, Function.comp_def] using this
    · apply List.Perm.of_eq
      congr 1
  -- the first coordinates
  have hW : (L.map (fun t => t.1)).Perm (List.range (n * m + m + m * (n - 1))) := by
    let g : ℕ × ℕ × Bool → ℕ := fun p => lit m p.1 p.2.1 p.2.2
    let A : List (ℕ × ℕ × Bool) :=
      ((List.range n).flatMap fun i => (List.range m).map fun j => (i, j, !σ i)) ++
        ((List.range m).map fun j => ((pick j).1, j, σ (pick j).1)) ++
        R.map fun p => (p.1, p.2, σ p.1)
    let All : List (ℕ × ℕ × Bool) := (List.range n).flatMap fun i =>
      (List.range m).flatMap fun j => [(i, j, true), (i, j, false)]
    have hLA : L.map (fun t => t.1) = A.map g := by
      simp only [L, Lts, Lcl, Lgc, A, List.map_append, List.map_flatMap, List.map_map]
      refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
      · congr 1; funext i; congr 1; funext j
        simp only [Function.comp_apply, g]
        cases σ i <;> rfl
      · refine List.map_congr_left fun j hj => ?_
        simp only [Function.comp_apply, g, (hpick j (List.mem_range.1 hj)).2]
      · rw [← hRlen, ← map_range_getD R (0, 0)]
        rfl
    have hAll : All.map g = List.range (2 * (n * m)) := by
      rw [← flatMap_double]
      simp only [All, List.map_flatMap]
      rw [← flatMap_pairs n m]
      congr 1
    have hAllnd : All.Nodup := List.Nodup.of_map g (hAll ▸ List.nodup_range)
    have hsub : All ⊆ A := by
      intro p hp
      obtain ⟨i, j, b⟩ := p
      simp only [All, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false, Prod.mk.injEq] at hp
      obtain ⟨i', hi, j', hj, h⟩ := hp
      have hij : i = i' ∧ j = j' := by rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> exact ⟨h1, h2⟩
      obtain ⟨rfl, rfl⟩ := hij
      simp only [A, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
        Prod.mk.injEq]
      by_cases hb : b = !σ i
      · exact Or.inl (Or.inl ⟨i, hi, j, hj, rfl, rfl, hb.symm⟩)
      · have hb' : b = σ i := by cases b <;> cases h' : σ i <;> simp_all
        by_cases hp : i = (pick j).1
        · exact Or.inl (Or.inr ⟨j, hj, hp.symm, rfl, by rw [hb', hp]⟩)
        · exact Or.inr ⟨(i, j), (hRmem _).2 ⟨hi, hj, hp⟩, rfl, rfl, hb'.symm⟩
    have hAlen : A.length = n * m + m + m * (n - 1) := by
      simp only [A, List.length_append, List.length_flatMap, List.length_map, List.length_range,
        hRlen, sum_map_const_range]
    have hAlllen : All.length = 2 * (n * m) := by
      rw [← List.length_map (f := g), hAll, List.length_range]
    have hperm : All.Perm A :=
      (hAllnd.subperm hsub).perm_of_length_le (by
        rw [hAlen, hAlllen]; obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; nlinarith)
    rw [hLA]
    refine (hperm.map g).symm.trans ?_
    rw [hAll]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show 2 * ((n' + 1) * m) = (n' + 1) * m + m + m * n' by ring]
  -- the matching is a sub-multiset of the triples
  have hnd : L.Nodup := List.Nodup.of_map _ (hY ▸ List.nodup_range)
  have hLM : L ⊆ gj n φ := by
    intro t ht
    rw [hmem]
    simp only [L, Lts, Lcl, Lgc, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_range] at ht
    rcases ht with (⟨i, hi, j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨k, hk, rfl⟩
    · refine Or.inl ⟨i, hi, j, hj, ?_⟩
      cases σ i <;> simp
    · exact Or.inr (Or.inl ⟨j, hj, pick j, (hpick j hj).1, rfl⟩)
    · have hkR : R.getD k (0, 0) ∈ R := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      obtain ⟨hi, hj, -⟩ := (hRmem _).1 hkR
      exact Or.inr (Or.inr ⟨k, hk, _, hi, _, hj, _, rfl⟩)
  refine ⟨L, Multiset.coe_le.mpr (hnd.subperm hLM), ?_, ?_, ?_⟩
  · rw [Multiset.map_coe, ← Multiset.coe_range, Multiset.coe_eq_coe]; exact hW
  · rw [Multiset.map_coe, ← Multiset.coe_range, Multiset.coe_eq_coe]; exact hX
  · rw [Multiset.map_coe, ← Multiset.coe_range, hY]

/-! ### From a matching to a satisfying assignment -/

theorem two_le_count_map {S : Multiset (ℕ × ℕ × ℕ)} {f : ℕ × ℕ × ℕ → ℕ} {a b : ℕ × ℕ × ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) (hf : f a = f b) : 2 ≤ (S.map f).count (f a) := by
  have hle : ({a, b} : Multiset _) ≤ S := by
    rw [Multiset.le_iff_subset (by simp [hne])]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have := Multiset.count_le_of_le (f a) (Multiset.map_le_map (f := f) hle)
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.count_cons_self, Multiset.count_singleton, hf] at this
  simpa [hf] using this

theorem exactly_one {S M : Multiset (ℕ × ℕ × ℕ)} {f : ℕ × ℕ × ℕ → ℕ} {y : ℕ}
    (hSM : S ≤ M) (hc : (S.map f).count y = 1) {u1 u2 : ℕ × ℕ × ℕ} (hne : u1 ≠ u2)
    (hf1 : f u1 = y) (hf2 : f u2 = y) (honly : ∀ t ∈ M, f t = y → t = u1 ∨ t = u2) :
    u1 ∈ S ↔ u2 ∉ S := by
  constructor
  · intro h1 h2
    have := two_le_count_map h1 h2 hne (hf1.trans hf2.symm)
    rw [hf1] at this; omega
  · intro h2
    by_contra h1
    have hpos : 0 < (S.map f).count y := by omega
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 (Multiset.count_pos.1 hpos)
    rcases honly t (Multiset.mem_of_le hSM ht) rfl with rfl | rfl
    · exact h1 ht
    · exact h2 ht

theorem count_range_one {q y : ℕ} (hy : y < q) : (Multiset.range q).count y = 1 := by
  rw [count_range_ite, if_pos hy]

theorem sat_of_has3DM {n : ℕ} {φ : CNF} (hn : 1 ≤ n) (hv : ∀ c ∈ φ, ∀ l ∈ c, l.1 < n)
    (h : Has3DM (gjq n φ) (gj n φ)) : Satisfiable φ := by
  classical
  obtain ⟨S, hSM, h1, h2, h3⟩ := h
  have hq : gjq n φ = n * φ.length + φ.length + φ.length * (n - 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [gjq, Nat.add_sub_cancel]; ring
  have hq2 : gjq n φ = 2 * n * φ.length := rfl
  have hmem : ∀ t, t ∈ gj n φ ↔ _ := fun t => mem_gj (n := n) (φ := φ) (t := t)
  have hgd : ∀ j < φ.length, ∀ l ∈ φ.getD j [], l.1 < n := fun j hj l hl =>
    hv _ (getD_mem hj) l hl
  generalize hm : φ.length = m at hmem hq hq2 hgd
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine ⟨fun _ => true, fun c hc => ?_⟩
    rw [List.length_eq_zero_iff] at hm; subst hm; simp at hc
  have hnmq : n * m + m ≤ gjq n φ := by rw [hq]; omega
  set M : Multiset (ℕ × ℕ × ℕ) := ((gj n φ : List (ℕ × ℕ × ℕ)) : Multiset (ℕ × ℕ × ℕ)) with hM
  have hMm : ∀ t ∈ M, t ∈ gj n φ := fun t ht => Multiset.mem_coe.1 ht
  -- decoding the coordinates
  have decY : ∀ i < n, ∀ j < m, ∀ t ∈ M, t.2.2 = i * m + j → t = tT m i j ∨ t = tF m i j := by
    intro i hi j hj t ht hy
    have hlt := pair_lt hi hj
    rcases (hmem t).1 (hMm t ht) with ⟨i', hi', j', hj', rfl | rfl⟩ | ⟨j', hj', l, hl, rfl⟩ |
        ⟨k, hk, i', hi', j', hj', b, rfl⟩
    · obtain ⟨rfl, rfl⟩ := pair_inj hj' hj hy; exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := pair_inj hj' hj hy; exact Or.inr rfl
    · simp only at hy; omega
    · simp only at hy; omega
  have decX : ∀ i < n, ∀ j < m, ∀ t ∈ M, t.2.1 = i * m + j →
      t = tT m i j ∨ t = tF m i ((j + m - 1) % m) := by
    intro i hi j hj t ht hx
    have hlt := pair_lt hi hj
    rcases (hmem t).1 (hMm t ht) with ⟨i', hi', j', hj', rfl | rfl⟩ | ⟨j', hj', l, hl, rfl⟩ |
        ⟨k, hk, i', hi', j', hj', b, rfl⟩
    · obtain ⟨rfl, rfl⟩ := pair_inj hj' hj hx; exact Or.inl rfl
    · obtain ⟨rfl, hj2⟩ := pair_inj (Nat.mod_lt _ hm0) hj hx
      right
      have : j' = (j + m - 1) % m := by
        rcases Nat.lt_or_ge (j' + 1) m with h' | h'
        · rw [Nat.mod_eq_of_lt h'] at hj2
          rw [show j + m - 1 = j' + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj']
        · rw [show j' + 1 = m by omega, Nat.mod_self] at hj2
          subst hj2
          rw [show 0 + m - 1 = m - 1 by omega, Nat.mod_eq_of_lt (by omega)]; omega
      rw [← this]
    · simp only at hx; omega
    · simp only at hx; omega
  have decS : ∀ j < m, ∀ t ∈ M, t.2.1 = n * m + j →
      ∃ l ∈ φ.getD j [], t = (lit m l.1 j l.2, n * m + j, n * m + j) := by
    intro j hj t ht hx
    rcases (hmem t).1 (hMm t ht) with ⟨i', hi', j', hj', rfl | rfl⟩ | ⟨j', hj', l, hl, rfl⟩ |
        ⟨k, hk, i', hi', j', hj', b, rfl⟩
    · have := pair_lt hi' hj'; simp only [tT] at hx; omega
    · have := pair_lt hi' (Nat.mod_lt (j' + 1) hm0); simp only [tF] at hx; omega
    · simp only at hx
      obtain rfl : j' = j := by omega
      exact ⟨l, hl, rfl⟩
    · simp only at hx; omega
  -- the coordinate counts
  have cnt : ∀ (f : ℕ × ℕ × ℕ → ℕ), S.map f = Multiset.range (gjq n φ) →
      ∀ y < gjq n φ, (S.map f).count y = 1 := fun f hf y hy => by
    rw [hf]; exact count_range_one hy
  have hTF : ∀ i < n, ∀ j < m, tT m i j ≠ tF m i j := by
    intro i hi j hj h
    have := congrArg (fun t => t.1) h
    simp [tT, tF, lit] at this
  -- truth-setting: exactly one of the two triples in every column
  have colY : ∀ i < n, ∀ j < m, (tT m i j ∈ S ↔ tF m i j ∉ S) := by
    intro i hi j hj
    have hlt := pair_lt hi hj
    exact exactly_one (f := fun t => t.2.2) (y := i * m + j) hSM
      (cnt _ h3 (i * m + j) (by omega)) (hTF i hi j hj) rfl rfl (decY i hi j hj)
  have colX : ∀ i < n, ∀ j < m, (tT m i j ∈ S ↔ tF m i ((j + m - 1) % m) ∉ S) := by
    intro i hi j hj
    have hlt := pair_lt hi hj
    have hpj : (j + m - 1) % m < m := Nat.mod_lt _ hm0
    have hne : tT m i j ≠ tF m i ((j + m - 1) % m) := by
      intro h
      have := congrArg (fun t => t.1) h
      simp [tT, tF, lit] at this; omega
    have hx2 : (tF m i ((j + m - 1) % m)).2.1 = i * m + j := by
      simp only [tF]
      suffices h : ((j + m - 1) % m + 1) % m = j by rw [h]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [show 0 + m - 1 = m - 1 by omega, Nat.mod_eq_of_lt (show m - 1 < m by omega),
          show m - 1 + 1 = m by omega, Nat.mod_self]
      · rw [show j + m - 1 = (j - 1) + m by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show j - 1 < m by omega), show j - 1 + 1 = j by omega,
          Nat.mod_eq_of_lt hj]
    exact exactly_one (f := fun t => t.2.1) (y := i * m + j) hSM
      (cnt _ h2 (i * m + j) (by omega)) hne rfl hx2 (decX i hi j hj)
  -- the ring: all columns agree
  have ring : ∀ i < n, ∀ j < m, (tT m i j ∈ S ↔ tT m i 0 ∈ S) := by
    intro i hi j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih (by omega), colX i hi (j + 1) hj,
        show (j + 1 + m - 1) % m = j by rw [show j + 1 + m - 1 = j + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)], colY i hi j (by omega)]
  -- the assignment
  refine ⟨fun i => decide (tT m i 0 ∈ S), fun c hc => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  rw [hm] at hj
  have hcj : φ[j] = φ.getD j [] := (List.getD_eq_getElem _ _ (by omega)).symm
  rw [hcj]
  have hlt : n * m + j < gjq n φ := by rw [hq]; omega
  have hpos : 0 < (S.map fun t => t.2.1).count (n * m + j) := by
    rw [cnt _ h2 _ hlt]; omega
  obtain ⟨t, ht, htx⟩ := Multiset.mem_map.1 (Multiset.count_pos.1 hpos)
  obtain ⟨l, hl, rfl⟩ := decS j hj t (Multiset.mem_of_le hSM ht) htx
  refine ⟨l, hl, ?_⟩
  have hl1 : l.1 < n := hgd j hj l hl
  have hW1 : (S.map fun t => t.1).count (lit m l.1 j l.2) = 1 :=
    cnt _ h1 _ (by have := lit_lt l.2 hl1 hj; rw [hq2]; exact this)
  have hlt' := pair_lt hl1 hj
  simp only [decide_eq_decide]
  cases hb : l.2
  · -- a negative literal: the truth-setting triple covering it is not chosen
    have hnot : tT m l.1 j ∉ S := by
      intro hT
      have hne : tT m l.1 j ≠ (lit m l.1 j l.2, n * m + j, n * m + j) := by
        intro h; have := congrArg (fun t => t.2.1) h; simp only [tT] at this; omega
      have := two_le_count_map (f := fun t => t.1) hT ht hne (by simp [tT, hb])
      simp only [tT] at this
      rw [← hb] at this; omega
    simp only [Bool.false_eq_true, decide_eq_false_iff_not, iff_false]
    rw [← ring l.1 hl1 j hj]; exact hnot
  · have hnot : tF m l.1 j ∉ S := by
      intro hF
      have hne : tF m l.1 j ≠ (lit m l.1 j l.2, n * m + j, n * m + j) := by
        intro h; have := congrArg (fun t => t.2.1) h; simp only [tF] at this
        have := Nat.mod_lt (j + 1) hm0
        have := pair_lt hl1 this
        omega
      have := two_le_count_map (f := fun t => t.1) hF ht hne (by simp [tF, hb])
      simp only [tF] at this
      rw [← hb] at this; omega
    simp only [decide_eq_true_eq, iff_true]
    rw [← ring l.1 hl1 j hj, colY l.1 hl1 j hj]; exact hnot

/-- **Satisfiability reduces to 3-dimensional matching.** -/
theorem has3DM_gj_iff {n : ℕ} {φ : CNF} (hn : 1 ≤ n) (hv : ∀ c ∈ φ, ∀ l ∈ c, l.1 < n) :
    Has3DM (gjq n φ) (gj n φ) ↔ Satisfiable φ :=
  ⟨sat_of_has3DM hn hv, fun ⟨σ, hσ⟩ => has3DM_of_sat hn hv σ hσ⟩

end HTN.NPHard
