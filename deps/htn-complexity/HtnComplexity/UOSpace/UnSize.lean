import HtnComplexity.UOSpace.UnTable
import HtnComplexity.UOSpace.TblSize
import HtnComplexity.Space.SeqSize
/-!
# The size of the unrooted unordered-HTN action table

`HTN.UOTbl.tblSize_unTbl_le`: the table `unTbl d W N` has at most `80 (d.size + W + N + 1) ^ 5`
symbols.
-/

namespace HTN

namespace UOTbl

open Syn Space

theorem length_labsU_le (d : DomDesc) : (labsU d).length ≤ 2 * d.size := by
  have h1 := length_labs_le d
  have h2 := SeqM.length_vocA_le d
  simp only [labsU, List.length_append, List.length_map]
  omega

theorem rowSzU_unTbl_le {d : DomDesc} {W N : ℕ} {r : Row} (hr : r ∈ unTbl d W N) :
    rowSzU r ≤ 7 + 3 * W + d.size + 2 * d.size * W := by
  have hA := length_labsU_le d
  have hAW : (labsU d).length * W ≤ 2 * d.size * W := Nat.mul_le_mul_right _ hA
  rcases mem_unTbl.1 hr with rfl | ⟨p, -, rfl⟩ | ⟨p, -, l, -, i, hi, rfl⟩ | ⟨p, -, rfl⟩ |
    ⟨l, -, -, i, hi, rfl⟩ | ⟨k, e, -, (⟨i, hi, rfl⟩ | ⟨p, l, -, i, hi, rfl⟩ | rfl)⟩ | rfl
  · simp only [rowSzU, zeroRow, List.length_cons, List.length_nil, length_zerosAll]
    omega
  · simp only [rowSzU, nopRow, List.length_cons, List.length_nil]
    omega
  · simp only [rowSzU, labRow, addRow, List.length_cons, length_decPre, length_decAdd]
    omega
  · simp only [rowSzU, doneRow, List.length_cons, List.length_nil]
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

theorem length_unTbl_le (d : DomDesc) (W N : ℕ) :
    (unTbl d W N).length ≤ 3 + 2 * N + 2 * d.size * W * N + 4 * d.size * W + d.size := by
  have hA := length_labsU_le d
  have hM := length_methods_le' d
  have hB := length_flatMap_body_le d
  have h0 : (initRows d W N).length = 1 + N * (1 + (labsU d).length * W) + (N + 1) := by
    simp only [initRows, List.length_cons, List.length_append, List.length_map,
      List.length_range, List.length_flatMap]
    simp only [List.length_range, List.map_const', List.sum_replicate, smul_eq_mul]
    ring
  have h1 : ((labsU d).filter (fun l => l.1 = false)).length ≤ (labsU d).length :=
    List.length_filter_le _ _
  have h2 : (((labsU d).filter (fun l => l.1 = false)).flatMap
      (fun l => (List.range W).map (exeRow d l))).length =
      ((labsU d).filter (fun l => l.1 = false)).length * W := by
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
  simp only [unTbl, List.length_append, List.length_singleton, h0, h2, h3]
  have h4 : ((labsU d).filter (fun l => l.1 = false)).length * W ≤ 2 * d.size * W :=
    Nat.mul_le_mul_right _ (h1.trans hA)
  have h5 : d.methods.length * W + (d.methods.flatMap body).length * W ≤ d.size * W := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have h6 : N * ((labsU d).length * W) ≤ N * (2 * d.size * W) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA)
  nlinarith

/-- **The unrooted table has polynomially many symbols.** -/
theorem tblSize_unTbl_le (d : DomDesc) (W N : ℕ) :
    tblSize (unTbl d W N) ≤ 80 * (d.size + W + N + 1) ^ 5 := by
  have h := tblSize_le_of_rowSzU (fun r hr => rowSzU_unTbl_le (d := d) (W := W) (N := N) hr)
  have hl := length_unTbl_le d W N
  set X := d.size + W + N + 1 with hX
  calc tblSize (unTbl d W N) ≤ (unTbl d W N).length * (7 + 3 * W + d.size + 2 * d.size * W + 1) := h
    _ ≤ (3 + 2 * N + 2 * d.size * W * N + 4 * d.size * W + d.size) *
          (7 + 3 * W + d.size + 2 * d.size * W + 1) := Nat.mul_le_mul_right _ hl
    _ ≤ 80 * X ^ 5 := by
        have hx1 : 1 ≤ X := by omega
        have hs : d.size ≤ X := by omega
        have hW : W ≤ X := by omega
        have hN : N ≤ X := by omega
        have hsW : d.size * W ≤ X * X := Nat.mul_le_mul hs hW
        have hsWN : d.size * W * N ≤ X * X * X := Nat.mul_le_mul hsW hN
        have hX2 : X ≤ X * X := Nat.le_mul_of_pos_right _ hx1
        have hX3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ hx1
        have h1 : 3 + 2 * N + 2 * d.size * W * N + 4 * d.size * W + d.size ≤ 10 * (X * X * X) := by
          nlinarith
        have h2 : 7 + 3 * W + d.size + 2 * d.size * W + 1 ≤ 8 * (X * X) := by nlinarith
        calc _ ≤ 10 * (X * X * X) * (8 * (X * X)) := Nat.mul_le_mul h1 h2
          _ = 80 * X ^ 5 := by ring

end UOTbl

end HTN
