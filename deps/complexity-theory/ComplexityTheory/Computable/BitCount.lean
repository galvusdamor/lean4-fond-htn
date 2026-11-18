import Mathlib

/-!
# A binary counter on little-endian bit lists

The counting family of `HtnComplexity/Computable/CounterFamily.lean` needs a counter with
`2 ^ r` values over `O(r)` facts, and a domain description can only mention *positions*, so the
counter is a list of bits.  This file is the arithmetic of that counter, kept separate from the
planning constructions:

* `HTN.Bits.binInc` — the little-endian binary increment;
* `HTN.Bits.binVal` — the value of a bit list;
* `HTN.Bits.cnt r t` — the bit list reached from `r` zero bits after `t` increments;
* `HTN.Bits.binVal_cnt` — its value is `t` as long as `t < 2 ^ r`, hence `HTN.Bits.cnt_inj`:
  the first `2 ^ r` counter states are pairwise distinct;
* `HTN.Bits.getI_binInc` — the bits of `binInc l` when the lowest zero bit of `l` is at
  position `j`, which is the shape a planning action can have;
* `HTN.Bits.exists_low_zero` — such a position exists as soon as some bit is zero.
-/

namespace HTN

namespace Bits

/-- The **little-endian binary increment** of a bit list. -/
def binInc : List Bool → List Bool
  | [] => []
  | false :: t => true :: t
  | true :: t => false :: binInc t

/-- The **value** of a little-endian bit list. -/
def binVal : List Bool → ℕ
  | [] => 0
  | false :: t => 2 * binVal t
  | true :: t => 1 + 2 * binVal t

@[simp] theorem binInc_nil : binInc [] = [] := rfl

@[simp] theorem binInc_false_cons (t : List Bool) : binInc (false :: t) = true :: t := rfl

@[simp] theorem binInc_true_cons (t : List Bool) : binInc (true :: t) = false :: binInc t := rfl

@[simp] theorem binVal_nil : binVal [] = 0 := rfl

@[simp] theorem binVal_false_cons (t : List Bool) : binVal (false :: t) = 2 * binVal t := rfl

@[simp] theorem binVal_true_cons (t : List Bool) : binVal (true :: t) = 1 + 2 * binVal t := rfl

/-! ### Indexing -/

theorem getI_cons_zero (b : Bool) (t : List Bool) : (b :: t).getI 0 = b := rfl

theorem getI_cons_succ (b : Bool) (t : List Bool) (k : ℕ) : (b :: t).getI (k + 1) = t.getI k := rfl

/-! ### The increment -/

/-- The increment keeps the length. -/
@[simp] theorem length_binInc (l : List Bool) : (binInc l).length = l.length := by
  induction l with
  | nil => rfl
  | cons b t ih => cases b <;> simp [ih]

/-- A bit list of length `n` has a value below `2 ^ n`. -/
theorem binVal_lt (l : List Bool) : binVal l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    have hp : (2 : ℕ) ^ (t.length + 1) = 2 ^ t.length * 2 := pow_succ 2 t.length
    cases b <;> simp only [binVal_false_cons, binVal_true_cons, List.length_cons] <;> omega

/-- An all-ones bit list of length `n` has the value `2 ^ n - 1`. -/
theorem binVal_of_all_true {l : List Bool} (h : ∀ b ∈ l, b = true) :
    binVal l + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    have hb : b = true := h b (by simp)
    have ht : ∀ c ∈ t, c = true := fun c hc => h c (by simp [hc])
    have hih := ih ht
    have hp : (2 : ℕ) ^ (t.length + 1) = 2 ^ t.length * 2 := pow_succ 2 t.length
    subst hb
    simp only [binVal_true_cons, List.length_cons]
    omega

/-- A bit list whose value is not maximal has a zero bit. -/
theorem false_mem_of_binVal_lt {l : List Bool} (h : binVal l + 1 < 2 ^ l.length) :
    false ∈ l := by
  by_contra hc
  have hall : ∀ b ∈ l, b = true := by
    intro b hb
    cases b with
    | false => exact absurd hb hc
    | true => rfl
  have := binVal_of_all_true hall
  omega

/-- Incrementing a bit list with a zero bit adds one to its value. -/
theorem binVal_binInc {l : List Bool} (h : false ∈ l) : binVal (binInc l) = binVal l + 1 := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    cases b with
    | false => simp only [binInc_false_cons, binVal_true_cons, binVal_false_cons]; omega
    | true =>
      have ht : false ∈ t := by simpa using h
      simp only [binInc_true_cons, binVal_false_cons, binVal_true_cons, ih ht]
      omega

/-- **The lowest zero bit.** -/
theorem exists_low_zero {l : List Bool} (h : false ∈ l) :
    ∃ j, j < l.length ∧ (∀ k < j, l.getI k = true) ∧ l.getI j = false := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    cases b with
    | false => exact ⟨0, by simp, by omega, rfl⟩
    | true =>
      have ht : false ∈ t := by simpa using h
      obtain ⟨j, hj, hlow, hzero⟩ := ih ht
      refine ⟨j + 1, by simpa using hj, ?_, by rw [getI_cons_succ]; exact hzero⟩
      intro k hk
      cases k with
      | zero => rfl
      | succ k' =>
        rw [getI_cons_succ]
        exact hlow k' (by omega)

/-- **The bits of an increment** when the lowest zero bit sits at position `j`. -/
theorem getI_binInc {l : List Bool} {j : ℕ} (hj : j < l.length)
    (hlow : ∀ k < j, l.getI k = true) (hzero : l.getI j = false) (k : ℕ) :
    (binInc l).getI k = if k < j then false else if k = j then true else l.getI k := by
  induction l generalizing j k with
  | nil => simp at hj
  | cons b t ih =>
    cases j with
    | zero =>
      have hb : b = false := by rw [← getI_cons_zero b t]; exact hzero
      subst hb
      cases k with
      | zero => simp [binInc_false_cons]
      | succ k' => simp [binInc_false_cons]
    | succ j' =>
      have hb : b = true := hlow 0 (by omega)
      subst hb
      have hj' : j' < t.length := by simpa using hj
      have hlow' : ∀ k < j', t.getI k = true := by
        intro k hk
        rw [← getI_cons_succ true t k]
        exact hlow (k + 1) (by omega)
      have hzero' : t.getI j' = false := by rw [← getI_cons_succ true t j']; exact hzero
      cases k with
      | zero => simp [binInc_true_cons]
      | succ k' =>
        rw [binInc_true_cons, getI_cons_succ, ih hj' hlow' hzero' k', getI_cons_succ]
        by_cases h1 : k' < j'
        · rw [if_pos h1, if_pos (by omega)]
        · by_cases h2 : k' = j'
          · subst h2
            rw [if_neg h1, if_pos rfl, if_neg (by omega), if_pos rfl]
          · rw [if_neg h1, if_neg h2, if_neg (by omega), if_neg (by omega)]

/-! ### The counter -/

/-- The bit list of `r` zeros. -/
def zeros (r : ℕ) : List Bool := List.replicate r false

@[simp] theorem length_zeros (r : ℕ) : (zeros r).length = r := by simp [zeros]

@[simp] theorem binVal_zeros (r : ℕ) : binVal (zeros r) = 0 := by
  induction r with
  | zero => rfl
  | succ n ih => simpa [zeros, List.replicate_succ] using ih

/-- **The counter state after `t` increments** of the all-zero bit list of length `r`. -/
def cnt (r t : ℕ) : List Bool := binInc^[t] (zeros r)

@[simp] theorem cnt_zero (r : ℕ) : cnt r 0 = zeros r := rfl

theorem cnt_succ (r t : ℕ) : cnt r (t + 1) = binInc (cnt r t) := by
  simp [cnt, Function.iterate_succ_apply']

@[simp] theorem length_cnt (r t : ℕ) : (cnt r t).length = r := by
  induction t with
  | zero => simp
  | succ n ih => rw [cnt_succ, length_binInc, ih]

/-- **The counter counts**: after `t` increments its value is `t`, as long as `t < 2 ^ r`. -/
theorem binVal_cnt {r t : ℕ} (h : t < 2 ^ r) : binVal (cnt r t) = t := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hn : n < 2 ^ r := by omega
    have hval : binVal (cnt r n) = n := ih hn
    have hfalse : false ∈ cnt r n := by
      refine false_mem_of_binVal_lt ?_
      rw [hval, length_cnt]
      omega
    rw [cnt_succ, binVal_binInc hfalse, hval]

/-- **The first `2 ^ r` counter states are pairwise distinct.** -/
theorem cnt_inj {r t u : ℕ} (ht : t < 2 ^ r) (hu : u < 2 ^ r) (h : cnt r t = cnt r u) : t = u := by
  have := congrArg binVal h
  rwa [binVal_cnt ht, binVal_cnt hu] at this

/-- A counter state below the maximum has a zero bit. -/
theorem false_mem_cnt {r t : ℕ} (h : t + 1 < 2 ^ r) : false ∈ cnt r t := by
  refine false_mem_of_binVal_lt ?_
  rw [binVal_cnt (by omega), length_cnt]
  omega

end Bits

end HTN
