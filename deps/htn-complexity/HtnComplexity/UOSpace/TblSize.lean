import HtnComplexity.UOSpace.Table
import HtnComplexity.Space.RegSize
/-!
# The size of the unordered-HTN action table

`HTN.UOTbl.tblSize_uoTbl_le`: the action table `uoTbl d W` has at most `40 (d.size + W + 1) ^ 4`
symbols.
-/

namespace HTN

namespace UOTbl

open Syn Space

/-! ### Sizes of the domain data -/

theorem size_le_of_mem_methods' {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    e.size ≤ d.size := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := MethodDesc.size) he)
  unfold DomDesc.size
  omega

theorem length_body_le (e : MethodDesc) : (body e).length + 1 ≤ e.size := by
  have h1 : (body e).length ≤ e.2.ids.length := by
    simp only [body, List.length_map]
    exact (List.dedup_sublist _).length_le
  simp only [MethodDesc.size, TnDesc.size]
  omega

theorem length_methods_le' (d : DomDesc) : d.methods.length ≤ d.size := by
  have h : ∀ x ∈ d.methods.map MethodDesc.size, 1 ≤ x := by
    intro x hx
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    simp [MethodDesc.size]
  have := List.card_nsmul_le_sum _ 1 h
  simp only [List.length_map, smul_eq_mul, mul_one] at this
  unfold DomDesc.size
  omega

theorem length_flatMap_body_le (d : DomDesc) :
    (d.methods.flatMap body).length + d.methods.length ≤ d.size := by
  rw [List.length_flatMap]
  have : ((d.methods.map fun e => (body e).length).sum + d.methods.length) ≤
      (d.methods.map MethodDesc.size).sum := by
    clear * -
    induction d.methods with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := length_body_le e
      omega
  unfold DomDesc.size
  omega

theorem length_labs_le (d : DomDesc) : (labs d).length ≤ d.size := by
  have := length_flatMap_body_le d
  simp only [labs, List.length_append, List.length_map]
  omega

/-! ### Row sizes -/

/-- The number of facts a row lists. -/
def rowSzU (r : Row) : ℕ := r.1.length + r.2.1.length + r.2.2.length

theorem tblSize_le_of_rowSzU {tbl : List Row} {B : ℕ} (h : ∀ r ∈ tbl, rowSzU r ≤ B) :
    tblSize tbl ≤ tbl.length * (B + 1) := by
  have hs := List.sum_le_card_nsmul (tbl.map fun r => r.1.length + r.2.1.length + r.2.2.length) B
    (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      exact h r hr)
  simp only [List.length_map, smul_eq_mul] at hs
  rw [tblSize, Nat.mul_succ]
  omega

@[simp] theorem length_lowF (l : Bool × ℕ) (i : ℕ) (v : Bool) : (lowF l i v).length = i := by
  simp [lowF]

@[simp] theorem length_decPre (l : Bool × ℕ) (i : ℕ) : (decPre l i).length = i + 1 := by
  simp [decPre]

@[simp] theorem length_decAdd (l : Bool × ℕ) (i : ℕ) : (decAdd l i).length = i + 1 := by
  simp [decAdd]

theorem length_zerosAll (L : List (Bool × ℕ)) (W : ℕ) : (zerosAll L W).length = L.length * W := by
  simp only [zerosAll, List.length_flatMap, List.length_map, List.length_range]
  simp

theorem rowSzU_le {d : DomDesc} {W : ℕ} {r : Row} (hr : r ∈ uoTbl d W) :
    rowSzU r ≤ 4 + 3 * W + d.size + d.size * W := by
  have hA := length_labs_le d
  have hAW : (labs d).length * W ≤ d.size * W := Nat.mul_le_mul_right _ hA
  simp only [uoTbl, methRows, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
    List.mem_range, List.mem_singleton] at hr
  rcases hr with (((⟨e, -, rfl⟩ | ⟨l, -, i, hi, rfl⟩) | ⟨x, -, ((⟨i, hi, rfl⟩ |
    ⟨y, -, i, hi, rfl⟩) | rfl)⟩) | rfl)
  · have := List.length_filter_le (fun f => decide (f ≠ bitF (true, e.1) 0 false))
      (zerosAll (labs d) W)
    simp only [rowSzU, startRow, List.length_cons, List.length_nil, length_zerosAll] at this ⊢
    omega
  · have := rowSize_actOf_le d l.2
    simp only [rowSzU, exeRow, List.length_cons, List.length_append, List.length_map,
      length_decPre, length_decAdd]
    omega
  · simp only [rowSzU, decRow, List.length_cons, length_decPre, length_decAdd]
    omega
  · simp only [rowSzU, addRow, List.length_cons, length_decPre, length_decAdd]
    omega
  · simp only [rowSzU, endRow, List.length_singleton]
    omega
  · simp only [rowSzU, finRow, List.length_cons, List.length_nil, length_zerosAll]
    omega

theorem length_flatMap_zipIdx {α β : Type*} (l : List α) (F : α × ℕ → List β) (g : α → ℕ)
    (h : ∀ x, (F x).length = g x.1) : (l.zipIdx.flatMap F).length = (l.map g).sum := by
  rw [List.length_flatMap]
  have : (l.zipIdx.map fun x => (F x).length) = (l.zipIdx.map Prod.fst).map g := by
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => h x)
  rw [this, List.zipIdx_map_fst 0 l]

theorem length_uoTbl_le (d : DomDesc) (W : ℕ) :
    (uoTbl d W).length ≤ 1 + 2 * d.size + 2 * d.size * W := by
  have hA := length_labs_le d
  have hM := length_methods_le' d
  have hB := length_flatMap_body_le d
  have h1 : ((labs d).filter (fun l => l.1 = false)).length ≤ (labs d).length :=
    List.length_filter_le _ _
  have h2 : (((labs d).filter (fun l => l.1 = false)).flatMap
      (fun l => (List.range W).map (exeRow d l))).length =
      ((labs d).filter (fun l => l.1 = false)).length * W := by
    simp [List.length_flatMap]
  have h3 : (d.methods.zipIdx.flatMap (methRows W)).length =
      d.methods.length * W + (d.methods.flatMap body).length * W + d.methods.length := by
    rw [length_flatMap_zipIdx d.methods (methRows W) (fun e => W + (body e).length * W + 1)
      (fun x => by
        simp only [methRows, List.length_append, List.length_map, List.length_range,
          List.length_singleton]
        rw [length_flatMap_zipIdx (body x.1) _ (fun _ => W) (fun y => by simp)]
        simp)]
    rw [List.length_flatMap]
    clear * -
    induction d.methods with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring
  simp only [uoTbl, List.length_append, List.length_map, List.length_singleton, h2, h3]
  have h4 : ((labs d).filter (fun l => l.1 = false)).length * W ≤ d.size * W :=
    Nat.mul_le_mul_right _ (h1.trans hA)
  have h5 : d.methods.length * W + (d.methods.flatMap body).length * W ≤ d.size * W := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **The action table has polynomially many symbols.** -/
theorem tblSize_uoTbl_le (d : DomDesc) (W : ℕ) :
    tblSize (uoTbl d W) ≤ 40 * (d.size + W + 1) ^ 4 := by
  have h := tblSize_le_of_rowSzU (fun r hr => rowSzU_le (d := d) (W := W) hr)
  have hl := length_uoTbl_le d W
  calc tblSize (uoTbl d W) ≤ (uoTbl d W).length * (4 + 3 * W + d.size + d.size * W + 1) := h
    _ ≤ (1 + 2 * d.size + 2 * d.size * W) * (4 + 3 * W + d.size + d.size * W + 1) :=
        Nat.mul_le_mul_right _ hl
    _ ≤ 40 * (d.size + W + 1) ^ 4 := by
        have h1 : 1 + 2 * d.size + 2 * d.size * W ≤ 8 * (d.size + W + 1) ^ 2 := by nlinarith
        have h2 : 4 + 3 * W + d.size + d.size * W + 1 ≤ 5 * (d.size + W + 1) ^ 2 := by nlinarith
        calc _ ≤ 8 * (d.size + W + 1) ^ 2 * (5 * (d.size + W + 1) ^ 2) := Nat.mul_le_mul h1 h2
          _ = 40 * (d.size + W + 1) ^ 4 := by ring

end UOTbl

end HTN
