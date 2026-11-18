import HtnComplexity.Space.Norm
import HtnComplexity.Space.InstBound
import HtnComplexity.Complexity.SerialSize
/-!
# The advice: an action table, written out as a serialised list

The advice of the target-side machine carries the action table.  A row is *not* written as one
entry — an entry is wrapped in `HTN.Syn.bstr`, and the machine cannot scan inside it — so the
table is flattened: the advice is

    blist (idEnts tbl) ++ blist (factEnts tbl) ++ [b]

where

* `HTN.Space.idEnts tbl` lists a **name** `HTN.Space.rowId i = true^i ++ [false]` for each row;
  the names are pairwise distinct and none is a prefix of another, which is what makes the rows
  of the flattened list separable by a prefix test;
* `HTN.Space.factEnts tbl` lists one entry `rowId i ++ tag ++ bitsOfNat f` per fact `f` of row
  `i`, the two-bit `tag` saying whether `f` is in the precondition, the add or the delete list;
* the last bit `b` is the one bit of the answer that depends on the domain description alone.

`HTN.Space.mem_factEnts_prec`, `HTN.Space.mem_factEnts_add` and `HTN.Space.mem_factEnts_del`
are the decoding lemmas: an entry of that shape occurs exactly when the fact is in the
corresponding list of the row.  `HTN.Space.length_tblAdv_le` bounds the length of the advice by
a polynomial in the number of symbols of the table and in the length of the longest numeral it
mentions.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### The entries -/

/-- The name of the `i`-th row: `i` ones followed by a zero.  No name is a prefix of another. -/
def rowId (i : ℕ) : List Bool := List.replicate i true ++ [false]

@[simp] theorem length_rowId (i : ℕ) : (rowId i).length = i + 1 := by simp [rowId]

/-- The tag of a precondition fact. -/
def tagPrec : List Bool := [false, false]

/-- The tag of an add fact. -/
def tagAdd : List Bool := [false, true]

/-- The tag of a delete fact. -/
def tagDel : List Bool := [true, false]

/-- The entry recording that `f` occurs in the list of row `i` marked by `t`. -/
def factEnt (i : ℕ) (t : List Bool) (f : ℕ) : List Bool := rowId i ++ t ++ bitsOfNat f

/-- The row at a position of the table. -/
def rowOf (tbl : List Row) (i : ℕ) : Row := tbl.getD i ([], [], [])

theorem rowOf_mem {tbl : List Row} {i : ℕ} (hi : i < tbl.length) : rowOf tbl i ∈ tbl := by
  rw [rowOf, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem exists_rowOf {tbl : List Row} {r : Row} (hr : r ∈ tbl) :
    ∃ i < tbl.length, rowOf tbl i = r := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  exact ⟨i, hi, by rw [rowOf, List.getD_eq_getElem _ _ hi]⟩

/-- The table is the list of its rows, read off by position. -/
theorem map_rowOf_range (tbl : List Row) :
    (List.range tbl.length).map (rowOf tbl) = tbl := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, rowOf]
  rw [List.getD_eq_getElem _ _ h₂]

/-- The entries of one row. -/
def rowEnts (i : ℕ) (r : Row) : List (List Bool) :=
  r.1.map (factEnt i tagPrec) ++ r.2.1.map (factEnt i tagAdd) ++ r.2.2.map (factEnt i tagDel)

@[simp] theorem length_rowEnts (i : ℕ) (r : Row) :
    (rowEnts i r).length = r.1.length + r.2.1.length + r.2.2.length := by
  simp only [rowEnts, List.length_append, List.length_map]

/-- The fact entries of the table. -/
def factEnts (tbl : List Row) : List (List Bool) :=
  (List.range tbl.length).flatMap fun i => rowEnts i (rowOf tbl i)

/-- The names of the rows of the table. -/
def idEnts (tbl : List Row) : List (List Bool) := (List.range tbl.length).map rowId

/-- **The advice**: the names of the rows, the fact entries, and one flag bit. -/
def tblAdv (b : Bool) (tbl : List Row) : List Bool :=
  blist (idEnts tbl) ++ blist (factEnts tbl) ++ [b]

/-! ### The names are prefix-free -/

theorem rowId_prefix_append (i j : ℕ) (r : List Bool) : rowId i <+: rowId j ++ r ↔ i = j := by
  induction i generalizing j r with
  | zero =>
    cases j with
    | zero => simpa [rowId] using ⟨fun _ => rfl, fun _ => List.prefix_append _ _⟩
    | succ j =>
      constructor
      · intro h
        rw [rowId, rowId] at h
        simp only [List.replicate_succ, List.cons_append] at h
        exact absurd (List.cons_prefix_cons.1 h).1 (by simp)
      · intro h; exact absurd h (by simp)
  | succ i ih =>
    cases j with
    | zero =>
      constructor
      · intro h
        rw [rowId, rowId] at h
        simp only [List.replicate_succ, List.cons_append, List.replicate_zero,
          List.nil_append] at h
        exact absurd (List.cons_prefix_cons.1 h).1 (by simp)
      · intro h; exact absurd h (by simp)
    | succ j =>
      rw [rowId, rowId]
      simp only [List.replicate_succ, List.cons_append, List.cons_prefix_cons, true_and,
        Nat.succ.injEq]
      exact ih j r

theorem rowId_prefix_rowId_iff (i j : ℕ) : rowId i <+: rowId j ↔ i = j := by
  simpa using rowId_prefix_append i j []

theorem rowId_prefix_factEnt_iff (i j : ℕ) (t : List Bool) (f : ℕ) :
    rowId i <+: factEnt j t f ↔ i = j := by
  rw [factEnt, List.append_assoc]
  exact rowId_prefix_append i j _

theorem factEnt_injective {i j : ℕ} {t t' : List Bool} {f f' : ℕ} (ht : t.length = 2)
    (ht' : t'.length = 2) (h : factEnt i t f = factEnt j t' f') : i = j ∧ t = t' ∧ f = f' := by
  have hij : i = j := by
    refine (rowId_prefix_factEnt_iff i j t' f').1 ?_
    rw [← h, factEnt, List.append_assoc]
    exact List.prefix_append _ _
  subst hij
  rw [factEnt, factEnt, List.append_assoc, List.append_assoc] at h
  have h2 : t ++ bitsOfNat f = t' ++ bitsOfNat f' := List.append_cancel_left h
  obtain ⟨htt, hff⟩ := List.append_inj h2 (by rw [ht, ht'])
  exact ⟨rfl, htt, bitsOfNat_injective hff⟩

/-! ### Decoding -/

theorem mem_factEnts_iff {tbl : List Row} {w : List Bool} :
    w ∈ factEnts tbl ↔ ∃ i < tbl.length, w ∈ rowEnts i (rowOf tbl i) := by
  simp [factEnts, List.mem_flatMap, List.mem_range]

private theorem mem_rowEnts_cases {i j : ℕ} {t : List Bool} {f : ℕ} {r : Row}
    (ht : t.length = 2) (h : factEnt i t f ∈ rowEnts j r) :
    i = j ∧ ((t = tagPrec ∧ f ∈ r.1) ∨ (t = tagAdd ∧ f ∈ r.2.1) ∨ (t = tagDel ∧ f ∈ r.2.2)) := by
  simp only [rowEnts, List.mem_append, List.mem_map] at h
  rcases h with (⟨a, ha, he⟩ | ⟨a, ha, he⟩) | ⟨a, ha, he⟩
  · obtain ⟨hij, htt, hff⟩ := factEnt_injective ht (by rfl) he.symm
    exact ⟨hij, Or.inl ⟨htt, hff ▸ ha⟩⟩
  · obtain ⟨hij, htt, hff⟩ := factEnt_injective ht (by rfl) he.symm
    exact ⟨hij, Or.inr (Or.inl ⟨htt, hff ▸ ha⟩)⟩
  · obtain ⟨hij, htt, hff⟩ := factEnt_injective ht (by rfl) he.symm
    exact ⟨hij, Or.inr (Or.inr ⟨htt, hff ▸ ha⟩)⟩

theorem mem_factEnts_shape {tbl : List Row} {w : List Bool} (hw : w ∈ factEnts tbl) :
    ∃ j t f, j < tbl.length ∧ t.length = 2 ∧ w = factEnt j t f := by
  obtain ⟨j, hj, hjw⟩ := mem_factEnts_iff.1 hw
  simp only [rowEnts, List.mem_append, List.mem_map] at hjw
  rcases hjw with (⟨f, -, rfl⟩ | ⟨f, -, rfl⟩) | ⟨f, -, rfl⟩
  · exact ⟨j, tagPrec, f, hj, rfl, rfl⟩
  · exact ⟨j, tagAdd, f, hj, rfl, rfl⟩
  · exact ⟨j, tagDel, f, hj, rfl, rfl⟩

theorem mem_factEnts_prec {tbl : List Row} {i f : ℕ} (hi : i < tbl.length) :
    factEnt i tagPrec f ∈ factEnts tbl ↔ f ∈ (rowOf tbl i).1 := by
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := mem_factEnts_iff.1 h
    obtain ⟨rfl, hcase⟩ := mem_rowEnts_cases (by rfl) hj
    rcases hcase with ⟨-, hf⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    · exact hf
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
  · intro h
    exact mem_factEnts_iff.2 ⟨i, hi, by
      simp only [rowEnts, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨f, h, rfl⟩)⟩

theorem mem_factEnts_add {tbl : List Row} {i f : ℕ} (hi : i < tbl.length) :
    factEnt i tagAdd f ∈ factEnts tbl ↔ f ∈ (rowOf tbl i).2.1 := by
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := mem_factEnts_iff.1 h
    obtain ⟨rfl, hcase⟩ := mem_rowEnts_cases (by rfl) hj
    rcases hcase with ⟨hc, -⟩ | ⟨-, hf⟩ | ⟨hc, -⟩
    · exact absurd hc (by decide)
    · exact hf
    · exact absurd hc (by decide)
  · intro h
    exact mem_factEnts_iff.2 ⟨i, hi, by
      simp only [rowEnts, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨f, h, rfl⟩)⟩

theorem mem_factEnts_del {tbl : List Row} {i f : ℕ} (hi : i < tbl.length) :
    factEnt i tagDel f ∈ factEnts tbl ↔ f ∈ (rowOf tbl i).2.2 := by
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := mem_factEnts_iff.1 h
    obtain ⟨rfl, hcase⟩ := mem_rowEnts_cases (by rfl) hj
    rcases hcase with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨-, hf⟩
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact hf
  · intro h
    exact mem_factEnts_iff.2 ⟨i, hi, by
      simp only [rowEnts, List.mem_append, List.mem_map]
      exact Or.inr ⟨f, h, rfl⟩⟩

theorem mem_idEnts_iff {tbl : List Row} {u : List Bool} :
    u ∈ idEnts tbl ↔ ∃ i < tbl.length, u = rowId i := by
  simp [idEnts, List.mem_map, List.mem_range, eq_comm]

/-! ### Counting -/

theorem length_factEnts (tbl : List Row) :
    (factEnts tbl).length + tbl.length = tblSize tbl := by
  have h : (factEnts tbl).length
      = ((List.range tbl.length).map fun i =>
          (rowOf tbl i).1.length + (rowOf tbl i).2.1.length + (rowOf tbl i).2.2.length).sum := by
    rw [factEnts, List.length_flatMap]
    congr 1
    exact List.map_congr_left fun i _ => length_rowEnts _ _
  rw [h, tblSize]
  have h2 : (tbl.map fun r => r.1.length + r.2.1.length + r.2.2.length)
      = (List.range tbl.length).map fun i =>
          (rowOf tbl i).1.length + (rowOf tbl i).2.1.length + (rowOf tbl i).2.2.length := by
    conv_lhs => rw [← map_rowOf_range tbl]
    rw [List.map_map]
    rfl
  rw [h2]
  omega

theorem length_factEnts_le (tbl : List Row) : (factEnts tbl).length ≤ tblSize tbl := by
  have := length_factEnts tbl
  omega

theorem length_idEnts (tbl : List Row) : (idEnts tbl).length = tbl.length := by
  simp [idEnts]

theorem length_le_tblSize (tbl : List Row) : tbl.length ≤ tblSize tbl := by
  have := length_factEnts tbl
  omega

/-! ### The length of the advice -/

theorem length_blist_le {l : List (List Bool)} {N K : ℕ} (hN : l.length ≤ N)
    (hK : ∀ y ∈ l, y.length ≤ K) : (blist l).length ≤ N * (2 * K + 2) + 1 := by
  induction l generalizing N with
  | nil => simp [blist]
  | cons x l ih =>
    cases N with
    | zero => simp at hN
    | succ N =>
      have hx : x.length ≤ K := hK x (by simp)
      have hrest := ih (N := N) (by simpa using hN) fun y hy => hK y (by simp [hy])
      rw [blist_cons]
      simp only [List.length_cons, List.length_append, length_bstr]
      nlinarith [hrest, hx]

/-- **The advice is polynomially long** in the number of symbols of the table and in the length
of the longest numeral the table mentions. -/
theorem length_tblAdv_le (b : Bool) (tbl : List Row) (m : ℕ)
    (hm : ∀ f ∈ tblFacts tbl, (bitsOfNat f).length ≤ m) :
    (tblAdv b tbl).length ≤ 8 * (tblSize tbl + m + 3) ^ 3 := by
  set T := tblSize tbl with hT
  have hn : tbl.length ≤ T := length_le_tblSize tbl
  have hid : (blist (idEnts tbl)).length ≤ T * (2 * T + 2) + 1 := by
    refine length_blist_le (by rw [length_idEnts]; exact hn) fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := mem_idEnts_iff.1 hy
    rw [length_rowId]
    omega
  have hfe : (blist (factEnts tbl)).length ≤ T * (2 * (T + 2 + m) + 2) + 1 := by
    refine length_blist_le (length_factEnts_le tbl) fun y hy => ?_
    obtain ⟨i, hi, hy⟩ := mem_factEnts_iff.1 hy
    have hmem : rowOf tbl i ∈ tbl := rowOf_mem hi
    simp only [rowEnts, List.mem_append, List.mem_map] at hy
    have hlen : ∀ f, f ∈ tblFacts tbl → ∀ t : List Bool, t.length = 2 →
        (factEnt i t f).length ≤ T + 2 + m := by
      intro f hf t ht
      have := hm f hf
      simp only [factEnt, List.length_append, length_rowId, ht]
      omega
    rcases hy with (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) | ⟨f, hf, rfl⟩
    · exact hlen f (mem_tblFacts_of_prec hmem hf) _ rfl
    · exact hlen f (mem_tblFacts_of_add hmem hf) _ rfl
    · exact hlen f (mem_tblFacts_of_del hmem hf) _ rfl
  have htot : (tblAdv b tbl).length
      = (blist (idEnts tbl)).length + (blist (factEnts tbl)).length + 1 := by
    simp [tblAdv]
    omega
  rw [htot]
  nlinarith [hid, hfe, Nat.zero_le T, Nat.zero_le m, sq_nonneg (T + m)]

/-! ### What the advice makes available to the machine -/

theorem length_bitsOfNat_le_tblAdv {b : Bool} {tbl : List Row} {f : ℕ} (hf : f ∈ addFacts tbl) :
    (bitsOfNat f).length ≤ (tblAdv b tbl).length := by
  obtain ⟨r, hr, hfr⟩ := List.mem_flatMap.1 hf
  obtain ⟨i, hi, rfl⟩ := exists_rowOf hr
  have hmem : factEnt i tagAdd f ∈ factEnts tbl := (mem_factEnts_add hi).2 hfr
  have h1 := le_length_blist_of_mem hmem
  have h2 : (bitsOfNat f).length ≤ (factEnt i tagAdd f).length := by
    simp only [factEnt, List.length_append, length_rowId]
    omega
  have h3 : (blist (factEnts tbl)).length ≤ (tblAdv b tbl).length := by
    simp [tblAdv]
    omega
  omega

theorem length_addFacts_le_tblAdv {b : Bool} {tbl : List Row} :
    (addFacts tbl).length ≤ (tblAdv b tbl).length := by
  have h1 : (addFacts tbl).length ≤ (factEnts tbl).length := by
    have hA : (addFacts tbl).length
        = ((List.range tbl.length).map fun i => (rowOf tbl i).2.1.length).sum := by
      rw [addFacts, List.length_flatMap]
      conv_lhs => rw [← map_rowOf_range tbl]
      rw [List.map_map]
      rfl
    have hF : (factEnts tbl).length
        = ((List.range tbl.length).map fun i =>
            (rowOf tbl i).1.length + (rowOf tbl i).2.1.length + (rowOf tbl i).2.2.length).sum := by
      rw [factEnts, List.length_flatMap]
      congr 1
      exact List.map_congr_left fun i _ => length_rowEnts _ _
    rw [hA, hF]
    refine List.sum_le_sum ?_
    intro i _
    omega
  have h2 := length_le_length_blist (factEnts tbl)
  have h3 : (blist (factEnts tbl)).length ≤ (tblAdv b tbl).length := by
    simp [tblAdv]
    omega
  omega

theorem length_bitsOfNat_le_encState {s : List ℕ} {f : ℕ} (hf : f ∈ s) :
    (bitsOfNat f).length ≤ (encState s).length := by
  have := le_length_blist_of_mem (x := bitsOfNat f) (l := s.map bitsOfNat)
    (List.mem_map_of_mem hf)
  rw [encState]
  omega

theorem length_le_encState (s : List ℕ) : s.length ≤ (encState s).length := by
  have := length_le_length_blist (s.map bitsOfNat)
  rw [encState]
  simpa using this

end Space

end HTN
