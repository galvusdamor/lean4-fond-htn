import ComplexityTheory.Compile.Circ
/-!
# Bit strings of a bounded length, as fixed-width bit vectors

A circuit has a fixed number of input and output wires, while the functions of Cobham's class
(`ComplexityTheory/Complexity/Cobham.lean`) map bit strings of varying length to bit strings of
varying length.  The two are reconciled by the **cell encoding**: a string `s` with `|s| ≤ B` is
written as `B` cells of two bits each,

    cell i  =  (i < |s| , s.getI i)   —   the *presence* bit and the *value* bit,

so that its width is `2 * B` whatever `s` is.  A list of `k` arguments is the concatenation of
`k` such blocks (`HTN.Compile.encArgs`).

The file proves what the constructions need of the encoding: its width, how to read a cell off
it, that it determines the string it encodes, and that widening the bound only appends empty
cells.
-/

namespace HTN

namespace Compile

/-! ### Reading a concatenation of blocks of one width -/

/-- Reading a position of a concatenation of blocks, all of the same width. -/
theorem getI_flatMap_range {α : Type*} [Inhabited α] {m k : ℕ} {f : ℕ → List α}
    (hf : ∀ i, (f i).length = m)
    {j r : ℕ} (hj : j < k) (hr : r < m) :
    ((List.range k).flatMap f).getI (m * j + r) = (f j).getI r := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range k).flatMap f).length = m * k := by
      rw [List.length_flatMap]
      simp [hf, mul_comm]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getI_append _ _ _ (by rw [hlen]; nlinarith)]
      exact ih hj'
    · have h1 : ((List.range j).flatMap f).length ≤ m * j + r := by rw [hlen]; omega
      rw [List.getI_eq_getElem _ (by
        rw [List.length_append, hlen]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hf]
        omega)]
      rw [List.getElem_append_right (by rw [hlen]; omega)]
      rw [List.getI_eq_getElem _ (by
        simp only [hf]
        exact hr)]
      simp only [hlen, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      congr 1
      omega

/-! ### The cell encoding of a string -/

/-- The **cell encoding** of a string, at the bound `B`: `B` cells of two bits, the presence bit
and the value bit. -/
def encStr (B : ℕ) (s : List Bool) : List Bool :=
  (List.range B).flatMap fun i => [decide (i < s.length), s.getI i]

@[simp] theorem length_encStr (B : ℕ) (s : List Bool) : (encStr B s).length = 2 * B := by
  rw [encStr, List.length_flatMap]
  simp [mul_comm]

/-- The presence bit of the `i`-th cell. -/
theorem getI_encStr_pres {B i : ℕ} (s : List Bool) (hi : i < B) :
    (encStr B s).getI (2 * i) = decide (i < s.length) := by
  have := getI_flatMap_range (m := 2) (k := B)
    (f := fun i => [decide (i < s.length), s.getI i]) (fun _ => rfl) hi (r := 0) (by omega)
  simpa using this

/-- The value bit of the `i`-th cell. -/
theorem getI_encStr_val {B i : ℕ} (s : List Bool) (hi : i < B) :
    (encStr B s).getI (2 * i + 1) = s.getI i := by
  have := getI_flatMap_range (m := 2) (k := B)
    (f := fun i => [decide (i < s.length), s.getI i]) (fun _ => rfl) hi (r := 1) (by omega)
  simpa using this

/-- Two strings within the bound with the same encoding are equal. -/
theorem encStr_injOn {B : ℕ} {s t : List Bool} (hs : s.length ≤ B) (ht : t.length ≤ B)
    (h : encStr B s = encStr B t) : s = t := by
  have hlen : s.length = t.length := by
    by_contra hne
    rcases Nat.lt_or_ge s.length t.length with hlt | hge
    · have h1 := getI_encStr_pres (B := B) s (i := s.length) (by omega)
      have h2 := getI_encStr_pres (B := B) t (i := s.length) (by omega)
      rw [h] at h1
      rw [h1] at h2
      simp at h2
      omega
    · have hlt : t.length < s.length := by omega
      have h1 := getI_encStr_pres (B := B) s (i := t.length) (by omega)
      have h2 := getI_encStr_pres (B := B) t (i := t.length) (by omega)
      rw [h] at h1
      rw [h1] at h2
      simp at h2
      omega
  refine List.ext_getElem hlen ?_
  intro i hi hi'
  have h1 := getI_encStr_val (B := B) s (i := i) (by omega)
  have h2 := getI_encStr_val (B := B) t (i := i) (by omega)
  rw [h] at h1
  rw [h1] at h2
  rwa [List.getI_eq_getElem _ hi, List.getI_eq_getElem _ hi'] at h2

/-- The empty cells appended by a wider bound. -/
theorem encStr_widen {B B' : ℕ} {s : List Bool} (hs : s.length ≤ B) (h : B ≤ B') :
    encStr B' s = encStr B s ++ (List.range (B' - B)).flatMap fun _ => [false, false] := by
  conv_lhs => rw [show B' = B + (B' - B) by omega]
  rw [encStr, encStr, List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  refine List.flatMap_congr ?_
  intro i _
  have h1 : ¬ (B + i < s.length) := by omega
  have h2 : s.getI (B + i) = false := getI_of_le_length (by omega)
  simp [h1, h2]

/-! ### The encoding of an argument list -/

/-- The **cell encoding of an argument list**: `k` blocks of `n` cells. -/
def encArgs (k n : ℕ) (args : List (List Bool)) : List Bool :=
  (List.range k).flatMap fun i => encStr n (args.getD i [])

@[simp] theorem length_encArgs (k n : ℕ) (args : List (List Bool)) :
    (encArgs k n args).length = 2 * n * k := by
  rw [encArgs, List.length_flatMap]
  simp [mul_comm]

/-- Reading the block of the `j`-th argument. -/
theorem getI_encArgs {k n j r : ℕ} {args : List (List Bool)} (hj : j < k) (hr : r < 2 * n) :
    (encArgs k n args).getI (2 * n * j + r) = (encStr n (args.getD j [])).getI r :=
  getI_flatMap_range (m := 2 * n) (fun i => length_encStr n (args.getD i [])) hj hr

end Compile

end HTN
