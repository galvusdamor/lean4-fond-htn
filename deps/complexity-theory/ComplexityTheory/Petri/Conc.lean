import ComplexityTheory.Petri.Refute
import ComplexityTheory.Petri.ILP
/-!
# Concrete generalised problems

The decomposition theory of `ComplexityTheory/Petri/*.lean` works with blocks over a finite
type `ι` of coordinates, whose vectors are functions.  To *check* refutations by a primitive
recursive procedure we need first-order data.  A concrete block is a tuple of lists
(`HTN.Petri.KLM.CB`): integer vectors are `List ℤ`, `ω`-vectors are `List (Option ℕ)` (`none` is
`ω`), labels are a list indexed by the node, edges are triples.  `decB d` decodes a concrete block
into a block over `Fin d`; entries beyond the list are `0` (integer vectors) or `ω`.

This file also provides linear equations given by lists of terms (`TEq`), which the
characteristic system is built from.
-/

namespace HTN

namespace Petri

namespace KLM

open Finset

/-! ### Concrete data -/

/-- A concrete integer vector. -/
abbrev CV : Type := List ℤ

/-- A concrete `ω`-vector (`none` = `ω`). -/
abbrev CW : Type := List (Option ℕ)

/-- A concrete edge. -/
abbrev CE : Type := ℕ × CV × ℕ

/-- A concrete component: nodes, labels (indexed by node), edges, entry, exit. -/
abbrev CC : Type := List ℕ × List CW × List CE × ℕ × ℕ

/-- A concrete block: link vector, input, component, output. -/
abbrev CB : Type := CV × CW × CC × CW

/-- Accessors. -/
def cPre (b : CB) : CV := b.1
def cInp (b : CB) : CW := b.2.1
def cComp (b : CB) : CC := b.2.2.1
def cOut (b : CB) : CW := b.2.2.2
def cNodes (c : CC) : List ℕ := c.1
def cLabs (c : CC) : List CW := c.2.1
def cEdges (c : CC) : List CE := c.2.2.1
def cEntry (c : CC) : ℕ := c.2.2.2.1
def cExit (c : CC) : ℕ := c.2.2.2.2

/-! ### Decoding -/

/-- Decoding an integer vector. -/
def decV (d : ℕ) (v : CV) : Fin d → ℤ := fun j => v.getD j 0

/-- Decoding an optional number. -/
def decO : Option ℕ → ℕ∞
  | none => ⊤
  | some n => (n : ℕ∞)

/-- Decoding an `ω`-vector. -/
def decW (d : ℕ) (w : CW) : Fin d → ℕ∞ := fun j => decO (w.getD j none)

/-- Decoding an edge. -/
def decE (d : ℕ) (e : CE) : Edge (Fin d) := (e.1, decV d e.2.1, e.2.2)

/-- Decoding a component. -/
def decC (d : ℕ) (c : CC) : Comp (Fin d) :=
  ⟨cNodes c, fun u => decW d ((cLabs c).getD u []), (cEdges c).map (decE d), cEntry c, cExit c⟩

/-- **Decoding a block.** -/
def decB (d : ℕ) (b : CB) : Block (Fin d) :=
  ⟨decV d (cPre b), decW d (cInp b), decC d (cComp b), decW d (cOut b)⟩

@[simp] theorem decO_ne_top {o : Option ℕ} : decO o ≠ ⊤ ↔ o.isSome := by
  cases o <;> simp [decO]

theorem decO_toNat (n : ℕ) : (decO (some n)).toNat = n := by simp [decO]

@[simp] theorem decB_pre (d : ℕ) (b : CB) : (decB d b).pre = decV d (cPre b) := rfl
@[simp] theorem decB_inp (d : ℕ) (b : CB) : (decB d b).inp = decW d (cInp b) := rfl
@[simp] theorem decB_out (d : ℕ) (b : CB) : (decB d b).out = decW d (cOut b) := rfl
@[simp] theorem decB_comp (d : ℕ) (b : CB) : (decB d b).comp = decC d (cComp b) := rfl
@[simp] theorem decC_nodes (d : ℕ) (c : CC) : (decC d c).nodes = cNodes c := rfl
@[simp] theorem decC_edges (d : ℕ) (c : CC) : (decC d c).edges = (cEdges c).map (decE d) := rfl
@[simp] theorem decC_entry (d : ℕ) (c : CC) : (decC d c).entry = cEntry c := rfl
@[simp] theorem decC_exit (d : ℕ) (c : CC) : (decC d c).exit = cExit c := rfl
@[simp] theorem decC_lab (d : ℕ) (c : CC) (u : ℕ) :
    (decC d c).lab u = decW d ((cLabs c).getD u []) := rfl

theorem decE_default (d : ℕ) : decE d (0, [], 0) = ((0, 0, 0) : Edge (Fin d)) := by
  simp only [decE, Prod.mk.injEq, true_and, and_true]
  funext j; simp [decV]

theorem getD_map_decE (d : ℕ) (l : List CE) (k : ℕ) :
    (l.map (decE d)).getD k (0, 0, 0) = decE d (l.getD k (0, [], 0)) := by
  rw [← decE_default d, List.getD_map]

theorem vec_decC (d : ℕ) (c : CC) (k : ℕ) :
    (decC d c).vec k = decV d ((cEdges c).getD k (0, [], 0)).2.1 := by
  simp only [Comp.vec, decC_edges, getD_map_decE]
  rfl

/-! ### Linear equations as lists of terms -/

/-- A linear equation `∑ (v, c) ∈ terms, c * x v = r`. -/
abbrev TEq : Type := List (ℕ × ℤ) × ℤ

/-- The value of a list of terms. -/
def tval (ts : List (ℕ × ℤ)) (x : ℕ → ℕ) : ℤ := (ts.map fun p => p.2 * (x p.1 : ℤ)).sum

/-- An equation holds. -/
def TSat (e : TEq) (x : ℕ → ℕ) : Prop := tval e.1 x = e.2

/-- A system holds. -/
def TSatL (es : List TEq) (x : ℕ → ℕ) : Prop := ∀ e ∈ es, TSat e x

@[simp] theorem tval_nil (x : ℕ → ℕ) : tval [] x = 0 := rfl
@[simp] theorem tval_cons (p : ℕ × ℤ) (ts : List (ℕ × ℤ)) (x : ℕ → ℕ) :
    tval (p :: ts) x = p.2 * (x p.1 : ℤ) + tval ts x := by simp [tval]
theorem tval_append (ts ts' : List (ℕ × ℤ)) (x : ℕ → ℕ) :
    tval (ts ++ ts') x = tval ts x + tval ts' x := by simp [tval]

theorem tval_map_range (n : ℕ) (f : ℕ → ℕ) (c : ℕ → ℤ) (x : ℕ → ℕ) :
    tval ((List.range n).map fun k => (f k, c k)) x = ∑ k ∈ range n, c k * (x (f k) : ℤ) := by
  simp only [tval, List.map_map, Function.comp_def]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem tval_congr {ts : List (ℕ × ℤ)} {x y : ℕ → ℕ} (h : ∀ p ∈ ts, x p.1 = y p.1) :
    tval ts x = tval ts y := by
  induction ts with
  | nil => rfl
  | cons p ts ih =>
    rw [tval_cons, tval_cons, h p (by simp), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem tSatL_append {es es' : List TEq} {x : ℕ → ℕ} :
    TSatL (es ++ es') x ↔ TSatL es x ∧ TSatL es' x := by
  simp only [TSatL, List.mem_append]
  constructor
  · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
  · rintro ⟨h, h'⟩ e (he | he)
    · exact h e he
    · exact h' e he

/-- The variables mentioned by a system are below `n`. -/
def VarsBelow (es : List TEq) (n : ℕ) : Prop := ∀ e ∈ es, ∀ p ∈ e.1, p.1 < n

theorem tSatL_congr {es : List TEq} {n : ℕ} (hv : VarsBelow es n) {x y : ℕ → ℕ}
    (h : ∀ v < n, x v = y v) : TSatL es x ↔ TSatL es y := by
  have : ∀ e ∈ es, tval e.1 x = tval e.1 y := fun e he =>
    tval_congr fun p hp => h _ (hv e he p hp)
  simp only [TSatL, TSat]
  exact ⟨fun H e he => (this e he) ▸ H e he, fun H e he => (this e he).symm ▸ H e he⟩

/-! ### From terms to dense coefficient lists -/

/-- The coefficient of the unknown `v` in a list of terms. -/
def tcoef (ts : List (ℕ × ℤ)) (v : ℕ) : ℤ := ((ts.filter fun p => p.1 = v).map Prod.snd).sum

/-- The number of unknowns of a list of terms. -/
def tlen (ts : List (ℕ × ℤ)) : ℕ := (ts.map fun p => p.1 + 1).foldr max 0

/-- The dense form of an equation. -/
def dense (e : TEq) : List ℤ × ℤ := ((List.range (tlen e.1)).map (tcoef e.1), e.2)

theorem lt_tlen {ts : List (ℕ × ℤ)} {p : ℕ × ℤ} (hp : p ∈ ts) : p.1 < tlen ts := by
  unfold tlen
  induction ts with
  | nil => simp at hp
  | cons q ts ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hp with rfl | h
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih h) (le_max_right _ _)

theorem tval_eq_sum_coef (ts : List (ℕ × ℤ)) (x : ℕ → ℕ) {n : ℕ} (hn : ∀ p ∈ ts, p.1 < n) :
    tval ts x = ∑ v ∈ range n, tcoef ts v * (x v : ℤ) := by
  induction ts with
  | nil => simp [tcoef]
  | cons p ts ih =>
    rw [tval_cons, ih fun q hq => hn q (List.mem_cons_of_mem _ hq)]
    have hp : p.1 ∈ range n := Finset.mem_range.2 (hn p (by simp))
    have : ∀ v, tcoef (p :: ts) v = (if p.1 = v then p.2 else 0) + tcoef ts v := by
      intro v
      unfold tcoef
      by_cases h : p.1 = v <;> simp [h]
    simp only [this, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, if_pos hp]

theorem eqSat_dense (e : TEq) (x : ℕ → ℕ) : ILP.EqSat (dense e) x ↔ TSat e x := by
  unfold ILP.EqSat dense TSat
  simp only [List.length_map, List.length_range]
  rw [tval_eq_sum_coef e.1 x fun p hp => lt_tlen hp]
  refine Eq.congr_left (Finset.sum_congr rfl fun v hv => ?_)
  rw [List.getD_eq_getElem _ _ (by simpa using hv)]
  simp

theorem lsat_dense (es : List TEq) (x : ℕ → ℕ) : ILP.LSat (es.map dense) x ↔ TSatL es x := by
  simp only [ILP.LSat, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    eqSat_dense, TSatL]

end KLM

end Petri

end HTN
