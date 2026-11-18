import HtnComplexity.Space.ThrMachine
import HtnComplexity.Space.SeqSize
/-!
# The size of the thread table

`HTN.Space.Thr.tblSize_thrTbl_le`: the numbered thread table `(thrTbl d N).map (encRow enc)` has
at most `64 · (N + d.size + 1)^4` symbols (rows plus entries of their three lists).  Only lengths
are counted here; the numerals themselves are renamed away by `tblNorm` in the advice.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM

/-! ### Generic bounds -/

theorem length_flatMap_le' {α β : Type} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

/-- The number of entries of a row over `TF`. -/
def rs (r : Rw) : ℕ := r.1.length + r.2.1.length + r.2.2.length

theorem tblSize_map_encRow_le (tbl : List Rw) (M : ℕ) (h : ∀ r ∈ tbl, rs r ≤ M) :
    tblSize (tbl.map (encRow enc)) ≤ tbl.length * (M + 1) := by
  induction tbl with
  | nil => simp
  | cons r tbl ih =>
    have h1 := h r (List.mem_cons_self ..)
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [tblSize, List.map_cons, List.length_cons, List.sum_cons] at h2 ⊢
    simp only [encRow, List.length_map, rs] at h1 h2 ⊢
    rw [Nat.succ_mul]
    omega

/-! ### Lengths read off the domain description -/

theorem length_actOf_le (d : DomDesc) (a : ℕ) :
    (actOf d a).1.length + (actOf d a).2.1.length + (actOf d a).2.2.length ≤ d.size := by
  rw [actOf_eq]
  rcases h : d.actions.lookup a with _ | x
  · simp
  · have hmem : (a, x) ∈ d.actions := mem_of_lookup_eq_some h
    have hle : ActionDesc.size (a, x) ≤ (d.actions.map ActionDesc.size).sum :=
      DomDesc.mem_le_sum ActionDesc.size hmem
    have he : ActionDesc.size (a, x) = 1 + x.1.length + x.2.1.length + x.2.2.length := rfl
    have hs : d.size = (d.actions.map ActionDesc.size).sum +
      (d.methods.map MethodDesc.size).sum := rfl
    simp only [Option.elim, id]
    omega

theorem length_body_ids_le (d : DomDesc) (μ : ℕ) : (body d μ).ids.length ≤ d.size := by
  unfold body mth
  by_cases hμ : μ < d.methods.length
  · rw [List.getD_eq_getElem _ _ hμ]
    have hmem := List.getElem_mem hμ
    have hle := DomDesc.mem_le_sum MethodDesc.size hmem
    have hs : d.size = (d.actions.map ActionDesc.size).sum +
      (d.methods.map MethodDesc.size).sum := rfl
    have he : MethodDesc.size d.methods[μ] = 1 + (d.methods[μ]).2.size := rfl
    have ht : (d.methods[μ]).2.size = (d.methods[μ]).2.ids.length +
      (d.methods[μ]).2.ordList.length + (d.methods[μ]).2.lbl.length := rfl
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [TnDesc.nil, TnDesc.ids]

theorem length_primsL_le (d : DomDesc) (μ : ℕ) : (primsL d μ).length ≤ d.size :=
  (List.length_filter_le _ _).trans (length_body_ids_le d μ)

theorem length_predsL_le (d : DomDesc) (μ x : ℕ) : (predsL d μ x).length ≤ d.size := by
  unfold predsL
  exact (List.length_filter_le _ _).trans (length_body_ids_le d μ)

theorem length_oks_le (N j : ℕ) : (oks N j).length ≤ N := by
  unfold oks
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-! ### The rows -/

section Rows

variable (d : DomDesc) (N : ℕ)

theorem rs_rExpP (j μ : ℕ) : rs (rExpP d N j μ) ≤ N + 2 * d.size + 3 := by
  have := length_oks_le N j
  have := length_primsL_le d μ
  simp only [rs, rExpP, startL, List.length_cons, List.length_map, List.length_nil]
  omega

theorem rs_rExpC (j μ : ℕ) : rs (rExpC d j μ) ≤ N + 2 * d.size + 3 := by
  have := length_primsL_le d μ
  simp only [rs, rExpC, startL, List.length_cons, List.length_map, List.length_nil]
  omega

theorem rs_rClose (j μ : ℕ) : rs (rClose d j μ) ≤ N + 2 * d.size + 3 := by
  have := length_primsL_le d μ
  simp only [rs, rClose, doneL, List.length_cons, List.length_map, List.length_nil]
  omega

theorem rs_rExecs {j μ x : ℕ} {r : Rw} (hr : r ∈ rExecs d j μ x) :
    rs r ≤ N + 2 * d.size + 3 := by
  unfold rExecs at hr
  split at hr
  · rename_i a _
    simp only [List.mem_singleton] at hr
    subst hr
    have := length_actOf_le d a
    have := length_predsL_le d μ x
    simp only [rs, rExec, List.length_cons, List.length_append, List.length_map]
    omega
  · simp at hr

theorem rs_rExecP (j a : ℕ) : rs (rExecP d N j a) ≤ N + 2 * d.size + 3 := by
  have := length_actOf_le d a
  have := length_oks_le N j
  simp only [rs, rExecP, List.length_cons, List.length_append, List.length_map]
  omega

theorem rs_rNop (j : ℕ) : rs (rNop N j) ≤ N + 2 * d.size + 3 := by
  have := length_oks_le N j
  simp only [rs, rNop, List.length_cons, List.length_nil]
  omega

theorem rs_rZok {i j μ : ℕ} {r : Rw} (hr : r ∈ rZok d i j μ) : rs r ≤ N + 2 * d.size + 3 := by
  unfold rZok at hr
  split at hr
  · simp at hr
  · simp only [List.mem_singleton] at hr
    subst hr
    have := length_primsL_le d μ
    simp only [rs, doneL, List.length_cons, List.length_map, List.length_nil]
    omega

theorem rs_small {r : Rw} (hr : r ∈ rOks i j ∨ r ∈ rRch x y z ∨ r ∈ rCnt p) :
    rs r ≤ N + 2 * d.size + 3 := by
  simp only [rOks, rRch, rCnt, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
    simp [rs]

/-- **Every row of the thread table has at most `N + 2·d.size + 3` entries.** -/
theorem rs_thrTbl {r : Rw} (hr : r ∈ thrTbl d N) : rs r ≤ N + 2 * d.size + 3 := by
  simp only [thrTbl, List.mem_append, List.mem_flatMap, List.mem_range] at hr
  rcases hr with (((⟨j, -, μ, -, hr⟩ | ⟨j, -, hr⟩) | ⟨i, -, j, -, hr⟩) | ⟨x, -, y, -, z, -, hr⟩) |
      ⟨p, -, hr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | ⟨x, -, hr⟩
    · exact rs_rExpP d N j μ
    · exact rs_rExpC d N j μ
    · exact rs_rClose d N j μ
    · exact rs_rExecs d N hr
  · simp only [List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨a, -, rfl⟩ | rfl
    · exact rs_rExecP d N j a
    · exact rs_rNop d N j
  · rcases hr with hr | ⟨μ, -, hr⟩
    · exact rs_small d N (i := i) (j := j) (x := 0) (y := 0) (z := 0) (p := 0) (Or.inl hr)
    · exact rs_rZok d N hr
  · exact rs_small d N (i := 0) (j := 0) (p := 0) (Or.inr (Or.inl hr))
  · exact rs_small d N (i := 0) (j := 0) (x := 0) (y := 0) (z := 0) (Or.inr (Or.inr hr))

/-- **The thread table has at most `16 · (N + d.size + 1)^3` rows.** -/
theorem length_thrTbl_le : (thrTbl d N).length ≤ 16 * (N + d.size + 1) ^ 3 := by
  set s := d.size
  have hm : d.methods.length ≤ s := length_methods_le_size d
  have hv : (vocA d).length ≤ s := SeqM.length_vocA_le d
  have h1 : ((List.range N).flatMap fun j => (List.range d.methods.length).flatMap fun μ =>
      [rExpP d N j μ, rExpC d j μ, rClose d j μ] ++ (primsL d μ).flatMap (rExecs d j μ)).length
      ≤ N * (s * (3 + s)) := by
    refine (length_flatMap_le' _ _ (s * (3 + s)) fun j _ => ?_).trans (by simp)
    refine (length_flatMap_le' _ _ (3 + s) fun μ _ => ?_).trans
      (by simp only [List.length_range]; exact Nat.mul_le_mul_right _ hm)
    rw [List.length_append]
    have := length_flatMap_le' (primsL d μ) (rExecs d j μ) 1 fun x _ => by
      unfold rExecs; split <;> simp
    have := length_primsL_le d μ
    simp only [List.length_cons, List.length_nil]
    omega
  have h2 : ((List.range N).flatMap fun j => (vocA d).map (rExecP d N j) ++ [rNop N j]).length
      ≤ N * (s + 1) := by
    refine (length_flatMap_le' _ _ (s + 1) fun j _ => ?_).trans (by simp)
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  have h3 : ((List.range N).flatMap fun i => (List.range N).flatMap fun j =>
      rOks i j ++ (List.range d.methods.length).flatMap (rZok d i j)).length
      ≤ N * (N * (4 + s)) := by
    refine (length_flatMap_le' _ _ (N * (4 + s)) fun i _ => ?_).trans (by simp)
    refine (length_flatMap_le' _ _ (4 + s) fun j _ => ?_).trans (by simp)
    rw [List.length_append]
    have := length_flatMap_le' (List.range d.methods.length) (rZok d i j) 1 fun μ _ => by
      unfold rZok; split <;> simp
    simp only [List.length_range] at this
    simp only [rOks, List.length_cons, List.length_nil]
    omega
  have h4 : ((List.range N).flatMap fun x => (List.range N).flatMap fun y =>
      (List.range N).flatMap (rRch x y)).length ≤ N * (N * (N * 2)) := by
    refine (length_flatMap_le' _ _ (N * (N * 2)) fun x _ => ?_).trans (by simp)
    refine (length_flatMap_le' _ _ (N * 2) fun y _ => ?_).trans (by simp)
    refine (length_flatMap_le' _ _ 2 fun z _ => ?_).trans (by simp)
    simp [rRch]
  have h5 : ((List.range N).flatMap rCnt).length ≤ N * 4 := by
    refine (length_flatMap_le' _ _ 4 fun p _ => ?_).trans (by simp)
    simp [rCnt]
  unfold thrTbl
  simp only [List.length_append]
  have e1 : N * (s * (3 + s)) ≤ 4 * (N + s + 1) ^ 3 := by
    have : N * (s * (3 + s)) ≤ (N + s + 1) * ((N + s + 1) * (3 * (N + s + 1))) := by
      apply Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    nlinarith
  have e2 : N * (s + 1) ≤ (N + s + 1) ^ 3 := by
    have : N * (s + 1) ≤ (N + s + 1) * (N + s + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have e3 : N * (N * (4 + s)) ≤ 4 * (N + s + 1) ^ 3 := by
    have : N * (N * (4 + s)) ≤ (N + s + 1) * ((N + s + 1) * (4 * (N + s + 1))) := by
      apply Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    nlinarith
  have e4 : N * (N * (N * 2)) ≤ 2 * (N + s + 1) ^ 3 := by
    have : N * (N * (N * 2)) ≤ (N + s + 1) * ((N + s + 1) * ((N + s + 1) * 2)) := by
      apply Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    nlinarith
  have e5 : N * 4 ≤ 4 * (N + s + 1) ^ 3 := by
    have : N ≤ (N + s + 1) ^ 3 := by
      calc N ≤ N + s + 1 := by omega
        _ ≤ (N + s + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  omega

end Rows

/-- **The numbered thread table has at most `64 · (N + d.size + 1)^4` symbols.** -/
theorem tblSize_thrTbl_le (d : DomDesc) (N : ℕ) :
    tblSize ((thrTbl d N).map (encRow enc)) ≤ 64 * (N + d.size + 1) ^ 4 := by
  have h := tblSize_map_encRow_le (thrTbl d N) (N + 2 * d.size + 3) fun r hr => rs_thrTbl d N hr
  have h2 := length_thrTbl_le d N
  calc _ ≤ (thrTbl d N).length * (N + 2 * d.size + 3 + 1) := h
    _ ≤ 16 * (N + d.size + 1) ^ 3 * (4 * (N + d.size + 1)) :=
      Nat.mul_le_mul h2 (by omega)
    _ = 64 * (N + d.size + 1) ^ 4 := by ring

end Thr

end Space

end HTN
