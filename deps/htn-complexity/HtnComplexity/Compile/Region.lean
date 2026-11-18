import HtnComplexity.Compile.Block
import ComplexityTheory.Compile.Enc
/-!
# Writing a region of the memory

Besides the circuits and the guesses, the compiled program only ever writes a **region** of the
memory: it gathers a list of cells into a contiguous block (`HTN.Compile.gatherProg`), or writes
the cell encoding of the input word (`HTN.Compile.encInpProg`).  Both are assignment blocks in
the sense of `HtnComplexity/Compile/Block.lean`, so what they compute is read off
`HTN.Compile.runInstrs_assign` with no induction.

Writing `false` needs no instruction of its own: the program keeps a cell that is always
`false`, and a copy from it is a clear.
-/

namespace HTN

namespace Compile

open Syn

/-! ### Gathering cells into a region -/

/-- Copy the cells `src 0, …, src (len - 1)` into the region at `dst`. -/
def gatherProg (dst : ℕ) (src : ℕ → ℕ) (len : ℕ) : List Instr :=
  (List.range len).map fun i => iCopy (src i) (dst + i)

@[simp] theorem length_gatherProg (dst : ℕ) (src : ℕ → ℕ) (len : ℕ) :
    (gatherProg dst src len).length = len := by simp [gatherProg]

theorem simple_gatherProg {dst : ℕ} {src : ℕ → ℕ} {len : ℕ} :
    ∀ I ∈ gatherProg dst src len, Simple I := by
  intro I hI
  rw [gatherProg, List.mem_map] at hI
  obtain ⟨i, -, rfl⟩ := hI
  exact simple_iCopy _ _

theorem getI_gatherProg {dst : ℕ} {src : ℕ → ℕ} {len i : ℕ} (hi : i < len) :
    (gatherProg dst src len).getI i = iCopy (src i) (dst + i) := by
  rw [gatherProg, List.getI_eq_getElem _ (by simpa using hi)]
  simp

/-- A cell outside the region keeps its value. -/
theorem runInstrs_gatherProg_of_ne {W : List Bool} {μ : ℕ → Bool} {dst : ℕ} {src : ℕ → ℕ}
    {len a : ℕ} (ha : ∀ i < len, a ≠ dst + i) :
    runInstrs W μ (gatherProg dst src len) a = μ a := by
  refine runInstrs_of_forall_ne ?_
  intro I hI
  rw [gatherProg, List.mem_map] at hI
  obtain ⟨i, hi, rfl⟩ := hI
  rw [List.mem_range] at hi
  exact ha i hi

/-- **The region carries the gathered cells.** -/
theorem runInstrs_gatherProg {W : List Bool} {μ : ℕ → Bool} {dst : ℕ} {src : ℕ → ℕ} {len : ℕ}
    (hsrc : ∀ i < len, ∀ i' < len, src i ≠ dst + i') {i : ℕ} (hi : i < len) :
    runInstrs W μ (gatherProg dst src len) (dst + i) = μ (src i) := by
  have hmem : iCopy (src i) (dst + i) ∈ gatherProg dst src len := by
    rw [gatherProg, List.mem_map]
    exact ⟨i, List.mem_range.2 hi, rfl⟩
  have := runInstrs_assign (W := W) (μ := μ) (Is := gatherProg dst src len) ?_ ?_ _ hmem
  · simpa using this
  · intro I hI J hJ
    rw [gatherProg, List.mem_map] at hI hJ
    obtain ⟨a, ha, rfl⟩ := hI
    obtain ⟨b, hb, rfl⟩ := hJ
    rw [List.mem_range] at ha hb
    simp only [wrIdx, rdIdx_iCopy, List.mem_cons, List.not_mem_nil, or_false]
    exact fun hc => hsrc b hb a ha hc.symm
  · rw [gatherProg]
    refine List.pairwise_map.2 (List.Pairwise.imp ?_ List.pairwise_lt_range)
    intro a b hab
    simp only [wrIdx_iCopy]
    omega

/-! ### The cell encoding of the input word -/

/-- Write the cell encoding of the input word, at the bound `m`, into the region at `dst`. -/
def encInpProg (dst m n : ℕ) : List Instr :=
  (List.range m).flatMap fun i =>
    if i < n then [iSet1 (dst + 2 * i), iRdIn (n - 1 - i) (dst + 2 * i + 1)]
    else [iSet0 (dst + 2 * i), iSet0 (dst + 2 * i + 1)]

@[simp] theorem length_encInpProg (dst m n : ℕ) : (encInpProg dst m n).length = 2 * m := by
  rw [encInpProg, List.length_flatMap]
  have h : ((List.range m).map fun i =>
      (if i < n then [iSet1 (dst + 2 * i), iRdIn (n - 1 - i) (dst + 2 * i + 1)]
        else [iSet0 (dst + 2 * i), iSet0 (dst + 2 * i + 1)]).length)
      = (List.range m).map fun _ => 2 := by
    refine List.map_congr_left ?_
    intro i _
    split_ifs <;> rfl
  rw [h]
  simp [mul_comm]

theorem simple_encInpProg {dst m n : ℕ} : ∀ I ∈ encInpProg dst m n, Simple I := by
  intro I hI
  rw [encInpProg, List.mem_flatMap] at hI
  obtain ⟨i, -, hI⟩ := hI
  split_ifs at hI <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI <;>
    rcases hI with rfl | rfl <;> simp

theorem getI_encInpProg {dst m n i : ℕ} (hi : i < m) :
    (encInpProg dst m n).getI (2 * i) =
      (if i < n then iSet1 (dst + 2 * i) else iSet0 (dst + 2 * i)) ∧
    (encInpProg dst m n).getI (2 * i + 1) =
      (if i < n then iRdIn (n - 1 - i) (dst + 2 * i + 1) else iSet0 (dst + 2 * i + 1)) := by
  have hlen : ∀ j : ℕ, ((if j < n then [iSet1 (dst + 2 * j), iRdIn (n - 1 - j) (dst + 2 * j + 1)]
      else [iSet0 (dst + 2 * j), iSet0 (dst + 2 * j + 1)] : List Instr)).length = 2 := by
    intro j; split_ifs <;> rfl
  constructor
  · have h := getI_flatMap_range (α := Instr) (m := 2) (k := m)
      (f := fun j => if j < n then [iSet1 (dst + 2 * j), iRdIn (n - 1 - j) (dst + 2 * j + 1)]
        else [iSet0 (dst + 2 * j), iSet0 (dst + 2 * j + 1)]) hlen hi (r := 0) (by omega)
    rw [encInpProg, show 2 * i = 2 * i + 0 from rfl, h]
    dsimp only
    split_ifs <;> simp
  · have h := getI_flatMap_range (α := Instr) (m := 2) (k := m)
      (f := fun j => if j < n then [iSet1 (dst + 2 * j), iRdIn (n - 1 - j) (dst + 2 * j + 1)]
        else [iSet0 (dst + 2 * j), iSet0 (dst + 2 * j + 1)]) hlen hi (r := 1) (by omega)
    rw [encInpProg, h]
    dsimp only
    split_ifs <;> simp

/-- A cell outside the region keeps its value. -/
theorem runInstrs_encInpProg_of_ne {W : List Bool} {μ : ℕ → Bool} {dst m n a : ℕ}
    (ha : ∀ r < 2 * m, a ≠ dst + r) :
    runInstrs W μ (encInpProg dst m n) a = μ a := by
  refine runInstrs_of_forall_ne ?_
  intro I hI
  rw [encInpProg, List.mem_flatMap] at hI
  obtain ⟨i, hi, hI⟩ := hI
  rw [List.mem_range] at hi
  split_ifs at hI <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI <;>
    rcases hI with rfl | rfl <;>
    simp only [wrIdx] <;>
    first
      | exact ha (2 * i) (by omega)
      | exact (show dst + 2 * i + 1 = dst + (2 * i + 1) by omega) ▸ ha (2 * i + 1) (by omega)

/-- The bit of the word at a position, counted from the left. -/
theorem inBit_rev {W : List Bool} {i : ℕ} (hi : i < W.length) :
    inBit W (W.length - 1 - i) = W.getI i := by
  rw [inBit, List.getI_eq_getElem _ (by simp; omega), List.getI_eq_getElem _ hi]
  simp only [List.getElem_reverse]
  congr 1
  omega

/-- **The region carries the cell encoding of the input word.** -/
theorem runInstrs_encInpProg {W : List Bool} {μ : ℕ → Bool} {dst m n : ℕ} (hW : W.length = n)
    {r : ℕ} (hr : r < 2 * m) :
    runInstrs W μ (encInpProg dst m n) (dst + r) = (encStr m W).getI r := by
  have hdisj : ∀ I ∈ encInpProg dst m n, ∀ J ∈ encInpProg dst m n, wrIdx I ∉ rdIdx J := by
    intro I hI J hJ
    rw [encInpProg, List.mem_flatMap] at hJ
    obtain ⟨i, -, hJ⟩ := hJ
    split_ifs at hJ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ <;>
      rcases hJ with rfl | rfl <;> simp
  have hpw : List.Pairwise (fun I J => wrIdx I ≠ wrIdx J) (encInpProg dst m n) := by
    rw [encInpProg]
    refine List.pairwise_flatMap.2 ⟨?_, ?_⟩
    · intro i _
      split_ifs <;> simp
    · refine List.Pairwise.imp ?_ List.pairwise_lt_range
      intro i j hij I hI J hJ
      have hI' : wrIdx I = dst + 2 * i ∨ wrIdx I = dst + 2 * i + 1 := by
        split_ifs at hI <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hI <;>
          rcases hI with rfl | rfl <;> simp
      have hJ' : wrIdx J = dst + 2 * j ∨ wrIdx J = dst + 2 * j + 1 := by
        split_ifs at hJ <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ <;>
          rcases hJ with rfl | rfl <;> simp
      rcases hI' with h | h <;> rcases hJ' with h' | h' <;> rw [h, h'] <;> omega
  -- the cell and the half of it the position `r` is
  obtain ⟨i, s, hs, rfl⟩ : ∃ i s, s < 2 ∧ r = 2 * i + s :=
    ⟨r / 2, r % 2, by omega, by omega⟩
  have hi : i < m := by omega
  obtain ⟨hI0, hI1⟩ := getI_encInpProg (dst := dst) (n := n) hi
  interval_cases s
  · -- the presence bit
    have hmem : (if i < n then iSet1 (dst + 2 * i) else iSet0 (dst + 2 * i))
        ∈ encInpProg dst m n := by
      rw [← hI0]
      exact getI_mem (by simp; omega)
    have := runInstrs_assign (W := W) (μ := μ) hdisj hpw _ hmem
    rw [show 2 * i + 0 = 2 * i by omega, getI_encStr_pres _ hi, hW]
    by_cases h : i < n
    · rw [if_pos h] at this
      simpa [h] using this
    · rw [if_neg h] at this
      simpa [h] using this
  · -- the value bit
    have hmem : (if i < n then iRdIn (n - 1 - i) (dst + 2 * i + 1) else iSet0 (dst + 2 * i + 1))
        ∈ encInpProg dst m n := by
      rw [← hI1]
      exact getI_mem (by simp; omega)
    have := runInstrs_assign (W := W) (μ := μ) hdisj hpw _ hmem
    rw [show dst + (2 * i + 1) = dst + 2 * i + 1 by omega, getI_encStr_val _ hi]
    by_cases h : i < n
    · rw [if_pos h] at this
      simp only [wrVal, iRdIn, wrIdx] at this
      norm_num at this
      rw [this, show n - 1 - i = W.length - 1 - i by omega, inBit_rev (by omega)]
    · rw [if_neg h] at this
      simp only [wrIdx, wrVal, iSet0] at this
      rw [this, getI_of_le_length (by omega)]
      norm_num

/-! ### Well-formedness -/

theorem wf_gatherProg {dst : ℕ} {src : ℕ → ℕ} {len mm n : ℕ} (hd : dst + len ≤ mm)
    (hs : ∀ i < len, src i < mm) :
    ∀ I ∈ gatherProg dst src len, instrWf I mm n ∧ instrCanon I := by
  intro I hI
  rw [gatherProg, List.mem_map] at hI
  obtain ⟨i, hi, rfl⟩ := hI
  rw [List.mem_range] at hi
  refine ⟨?_, ?_⟩
  · simp only [instrWf, iCopy]
    norm_num
    exact ⟨hs i hi, by omega⟩
  · simp [instrCanon, iCopy]

theorem wf_encInpProg {dst m n mm : ℕ} (hd : dst + 2 * m ≤ mm) :
    ∀ I ∈ encInpProg dst m n, instrWf I mm n ∧ instrCanon I := by
  intro I hI
  rw [encInpProg, List.mem_flatMap] at hI
  obtain ⟨i, hi, hI⟩ := hI
  rw [List.mem_range] at hi
  split_ifs at hI with hin <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI <;>
    rcases hI with rfl | rfl <;>
    exact ⟨by simp [instrWf, iSet1, iSet0, iRdIn]; omega,
      by simp [instrCanon, iSet1, iSet0, iRdIn]⟩

end Compile

end HTN
