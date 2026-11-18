import ComplexityTheory.UOSpace.Steinitz
/-!
# Small solutions of integer linear systems

A system of linear equations with integer coefficients, in non-negative integer unknowns
`x 0, x 1, …`, is a list of pairs `(c, r)` standing for `∑ v, c[v] * x v = r`
(`HTN.Petri.ILP.LSat`).  **If it has a solution, it has one whose entries are at most
`zsP m a`** (`HTN.Petri.ILP.small_sol`), `m` the number of equations and `a` a bound on the
absolute values of the coefficients and right-hand sides.  This is the consequence of the Steinitz
lemma `HTN.Steinitz.exists_small_zero_sum_mem`: the columns of a solution, with the negated
right-hand side added once, form a zero-sum family; a small zero-sum subfamily containing the
right-hand side is again a solution.

Consequently feasibility is a bounded search (`HTN.Petri.ILP.lsat_iff_bounded`).
-/

namespace HTN

namespace Petri

namespace ILP

open Finset

/-- One equation `∑ v, c[v] * x v = r`. -/
def EqSat (e : List ℤ × ℤ) (x : ℕ → ℕ) : Prop :=
  ∑ v ∈ range e.1.length, e.1.getD v 0 * (x v : ℤ) = e.2

/-- A solution of a system. -/
def LSat (es : List (List ℤ × ℤ)) (x : ℕ → ℕ) : Prop := ∀ e ∈ es, EqSat e x

/-- The number of unknowns a system mentions. -/
def nVar (es : List (List ℤ × ℤ)) : ℕ := (es.map fun e => e.1.length).foldr max 0

/-- A bound on the absolute values of the coefficients and right-hand sides. -/
def amax (es : List (List ℤ × ℤ)) : ℕ :=
  (es.map fun e => e.2.natAbs + (e.1.map Int.natAbs).sum).sum

/-- The bound on the entries of a small solution. -/
def solBnd (es : List (List ℤ × ℤ)) : ℕ := Steinitz.zsP es.length (amax es)

theorem length_le_nVar {es : List (List ℤ × ℤ)} {e : List ℤ × ℤ} (he : e ∈ es) :
    e.1.length ≤ nVar es := by
  unfold nVar
  induction es with
  | nil => simp at he
  | cons e' es ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 he with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem natAbs_getD_le (c : List ℤ) (v : ℕ) : (c.getD v 0).natAbs ≤ (c.map Int.natAbs).sum := by
  induction c generalizing v with
  | nil => simp
  | cons z c ih =>
    cases v with
    | zero => simp
    | succ v =>
      simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
      have := ih v
      omega

theorem le_amax {es : List (List ℤ × ℤ)} {e : List ℤ × ℤ} (he : e ∈ es) :
    e.2.natAbs + (e.1.map Int.natAbs).sum ≤ amax es := by
  unfold amax
  exact List.le_sum_of_mem (List.mem_map.2 ⟨e, he, rfl⟩)

theorem eqSat_congr {e : List ℤ × ℤ} {x y : ℕ → ℕ} (h : ∀ v < e.1.length, x v = y v) :
    EqSat e x ↔ EqSat e y := by
  unfold EqSat
  rw [Finset.sum_congr rfl fun v hv => by rw [h v (Finset.mem_range.1 hv)]]

/-- The coordinates of the zero-sum family: row `i` of the system. -/
def gcol (es : List (List ℤ × ℤ)) : Option ℕ → ℕ → ℤ
  | none, i => -(es.getD i ([], 0)).2
  | some v, i => (es.getD i ([], 0)).1.getD v 0

/-- The family of columns of a solution `x` on the unknowns `< n`. -/
def colFam (n : ℕ) (x : ℕ → ℕ) : Multiset (Option ℕ) :=
  none ::ₘ ∑ v ∈ range n, Multiset.replicate (x v) (some v)

theorem sum_colFam (es : List (List ℤ × ℤ)) (n : ℕ) (x : ℕ → ℕ) (i : ℕ) :
    ((colFam n x).map (gcol es)).sum i =
      -(es.getD i ([], 0)).2 + ∑ v ∈ range n, (x v : ℤ) * (es.getD i ([], 0)).1.getD v 0 := by
  unfold colFam
  rw [Multiset.map_cons, Multiset.sum_cons, Pi.add_apply]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Multiset.map_add, Multiset.sum_add, Pi.add_apply, ih,
      Finset.sum_range_succ, Multiset.map_replicate, Multiset.sum_replicate, Pi.smul_apply,
      nsmul_eq_mul]
    rfl

theorem eqSat_iff_row {es : List (List ℤ × ℤ)} {n : ℕ} (hn : nVar es ≤ n) (x : ℕ → ℕ) {i : ℕ}
    (hi : i < es.length) :
    EqSat es[i] x ↔ ((colFam n x).map (gcol es)).sum i = 0 := by
  rw [sum_colFam, List.getD_eq_getElem _ _ hi]
  have hlen : es[i].1.length ≤ n := (length_le_nVar (List.getElem_mem hi)).trans hn
  unfold EqSat
  have : ∑ v ∈ range n, (x v : ℤ) * es[i].1.getD v 0 =
      ∑ v ∈ range es[i].1.length, es[i].1.getD v 0 * (x v : ℤ) := by
    rw [← Finset.sum_range_add_sum_Ico _ hlen]
    rw [Finset.sum_eq_zero (s := Ico _ _) fun v hv => by
      rw [List.getD_eq_default _ _ (Finset.mem_Ico.1 hv).1, mul_zero]]
    rw [add_zero]
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [this]
  omega

theorem gcol_bound (es : List (List ℤ × ℤ)) (s : Option ℕ) (i : ℕ) :
    |gcol es s i| ≤ amax es := by
  rcases lt_or_ge i es.length with hi | hi
  · have hm := le_amax (List.getElem_mem hi)
    cases s with
    | none =>
      simp only [gcol, List.getD_eq_getElem _ _ hi, abs_neg]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (Nat.le_add_right _ _).trans hm
    | some v =>
      simp only [gcol, List.getD_eq_getElem _ _ hi]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (natAbs_getD_le _ v).trans ((Nat.le_add_left _ _).trans hm)
  · cases s <;> simp only [gcol] <;> rw [List.getD_eq_default _ _ hi] <;> simp

theorem gcol_supp (es : List (List ℤ × ℤ)) (s : Option ℕ) (i : ℕ) (hi : i ∉ range es.length) :
    gcol es s i = 0 := by
  have hi' : es.length ≤ i := by simpa using hi
  cases s <;> simp only [gcol] <;> rw [List.getD_eq_default _ _ hi'] <;> simp

theorem lsat_iff_zero {es : List (List ℤ × ℤ)} {n : ℕ} (hn : nVar es ≤ n) (x : ℕ → ℕ) :
    LSat es x ↔ ((colFam n x).map (gcol es)).sum = 0 := by
  constructor
  · intro h
    funext i
    rcases lt_or_ge i es.length with hi | hi
    · exact (eqSat_iff_row hn x hi).1 (h _ (List.getElem_mem hi))
    · rw [sum_colFam, List.getD_eq_default _ _ hi]
      simp
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact (eqSat_iff_row hn x hi).2 (by rw [h]; rfl)

theorem count_colFam_none (n : ℕ) (x : ℕ → ℕ) : (colFam n x).count none = 1 := by
  unfold colFam
  rw [Multiset.count_cons_self, Multiset.count_sum']
  simp [Multiset.count_replicate]

theorem count_colFam_some (n : ℕ) (x : ℕ → ℕ) (w : ℕ) :
    (colFam n x).count (some w) = if w < n then x w else 0 := by
  unfold colFam
  rw [Multiset.count_cons_of_ne (by simp), Multiset.count_sum']
  simp [Multiset.count_replicate]

/-- **Small solutions**: a solvable system has a solution with entries at most `solBnd es`,
vanishing beyond the unknowns the system mentions. -/
theorem small_sol {es : List (List ℤ × ℤ)} {x : ℕ → ℕ} (h : LSat es x) :
    ∃ y, LSat es y ∧ (∀ v, y v ≤ solBnd es) ∧ ∀ v, nVar es ≤ v → y v = 0 := by
  classical
  set n := nVar es
  have hS := (lsat_iff_zero le_rfl x).1 h
  obtain ⟨T, hTS, hT0, hTc, hTs⟩ := Steinitz.exists_small_zero_sum_mem (range es.length)
    (amax es) (gcol es) none _ (colFam n x) rfl (by simp [colFam])
    (fun s _ i hi => gcol_supp es s i hi) (fun s _ i => gcol_bound es s i) hS
  rw [Finset.card_range] at hTc
  let y : ℕ → ℕ := fun v => if v < n then T.count (some v) else 0
  have hT : colFam n y = T := by
    ext s
    cases s with
    | none =>
      rw [count_colFam_none]
      have h1 := Multiset.count_le_of_le none hTS
      rw [count_colFam_none] at h1
      have h2 := Multiset.count_pos.2 hT0
      omega
    | some w =>
      rw [count_colFam_some]
      by_cases hw : w < n
      · simp [hw, y]
      · have h1 := Multiset.count_le_of_le (some w) hTS
        rw [count_colFam_some, if_neg hw] at h1
        rw [if_neg hw]
        omega
  refine ⟨y, (lsat_iff_zero le_rfl y).2 (by rw [hT]; exact hTs), fun v => ?_, fun v hv => ?_⟩
  · simp only [y]
    split_ifs
    · exact (Multiset.count_le_card _ _).trans hTc
    · exact Nat.zero_le _
  · simp [y, not_lt.2 hv]

/-- **Feasibility is a bounded search.** -/
theorem lsat_iff_bounded (es : List (List ℤ × ℤ)) :
    (∃ x, LSat es x) ↔ ∃ x, LSat es x ∧ (∀ v, x v ≤ solBnd es) ∧ ∀ v, nVar es ≤ v → x v = 0 :=
  ⟨fun ⟨_, h⟩ => small_sol h, fun ⟨x, h, _⟩ => ⟨x, h⟩⟩

end ILP

end Petri

end HTN
