import HtnComplexity.Article.ExpSpacePT
/-!
# The halving closure as a list

`HTN.halvingClosure k` — the numbers reached from `k` by halving even numbers and decrementing
odd ones — is contained in the list `HTN.Article.hcL k` of the numbers `k / 2 ^ j` and
`k / 2 ^ j - 1` for `j ≤ |bits k|` (`HTN.Article.mem_hcL_of_mem`), which is computed in polynomial
time from `k` in binary (`HTN.Article.pt_hcL`).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime

/-- **The halving closure as a list** (a superset of it). -/
def hcL (k : ℕ) : List ℕ :=
  (List.range ((bitsOfNat k).length + 1)).flatMap fun j => [k / 2 ^ j, k / 2 ^ j - 1]

theorem exists_of_mem_halvingClosure : ∀ (k x : ℕ), x ∈ halvingClosure k →
    ∃ j, x = k / 2 ^ j ∨ x = k / 2 ^ j - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    match k, hx with
    | 0, hx => exact ⟨0, Or.inl (by simpa using hx)⟩
    | 1, hx => exact ⟨0, Or.inl (by simpa using hx)⟩
    | k + 2, hx =>
      rw [halvingClosure_succ_succ, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ⟨0, Or.inl (by simp)⟩
      split_ifs at hx with he
      · obtain ⟨j, hj⟩ := ih ((k + 2) / 2) (by omega) x hx
        refine ⟨j + 1, ?_⟩
        have e : (k + 2) / 2 / 2 ^ j = (k + 2) / 2 ^ (j + 1) := by
          rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
        rw [← e]; exact hj
      · -- `k + 2` is odd, so `k + 1 ≥ 2` is even
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [show k' + 1 + 1 = k' + 2 by ring, halvingClosure_succ_succ, Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact ⟨0, Or.inr (by simp)⟩
        rw [if_pos (by omega)] at hx
        obtain ⟨j, hj⟩ := ih ((k' + 2) / 2) (by omega) x hx
        refine ⟨j + 1, ?_⟩
        have hh : (k' + 1 + 2) / 2 = (k' + 2) / 2 := by omega
        have e : (k' + 2) / 2 / 2 ^ j = (k' + 1 + 2) / 2 ^ (j + 1) := by
          rw [← hh, Nat.div_div_eq_div_mul, pow_succ, mul_comm]
        rw [← e]; exact hj

theorem lt_two_pow_length_bitsOfNat (k : ℕ) : k < 2 ^ (bitsOfNat k).length := by
  have := natOfBits_lt' (bitsOfNat k)
  rwa [natOfBits_bitsOfNat] at this

/-- **The halving closure is contained in the list.** -/
theorem mem_hcL_of_mem {k x : ℕ} (h : x ∈ halvingClosure k) : x ∈ hcL k := by
  obtain ⟨j, hj⟩ := exists_of_mem_halvingClosure k x h
  set L := (bitsOfNat k).length
  have hk : k < 2 ^ L := lt_two_pow_length_bitsOfNat k
  simp only [hcL, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false]
  by_cases hjL : j ≤ L
  · exact ⟨j, by omega, hj⟩
  · have h1 : k / 2 ^ j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hk
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : k / 2 ^ L = 0 := Nat.div_eq_of_lt hk
    exact ⟨L, by omega, by rw [h2]; rw [h1] at hj; omega⟩

/-! ### Polynomial time -/

theorem div_two_pow_eq_natOfBits (k j : ℕ) : k / 2 ^ j = natOfBits ((bitsOfNat k).drop j) := by
  induction j generalizing k with
  | zero => simp [natOfBits_bitsOfNat]
  | succ j ih =>
    rw [pow_succ, mul_comm, ← Nat.div_div_eq_div_mul]
    rcases k with _ | k
    · simp [ih]
    · rw [bitsOfNat_succ, List.drop_succ_cons, ← ih]

theorem drop_eq_map_range {β : Type} [Inhabited β] (l : List β) (j : ℕ) :
    l.drop j = (List.range (l.length - j)).map fun i => l.getI (i + j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ (by simp at h1; omega)]
    congr 1
    omega

variable {α : Type} [BEnc α]

theorem range_filter_ge (j : ℕ) : ∀ n : ℕ,
    (List.range n).filter (fun i => decide (j ≤ i)) = (List.range (n - j)).map (· + j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : j ≤ n
    · rw [show n + 1 - j = (n - j) + 1 by omega, List.range_succ, List.map_append]
      simp [h]
    · simp [h, show n + 1 - j = 0 by omega, show n - j = 0 by omega]

theorem drop_eq_filter {β : Type} [Inhabited β] (l : List β) (j : ℕ) :
    l.drop j = ((List.range l.length).filter fun i => decide (j ≤ i)).map l.getI := by
  rw [range_filter_ge, List.map_map, drop_eq_map_range]
  rfl

theorem pt_divPow {k j : α → ℕ} (hk : PT k) (hj : PT j) : PT fun a => k a / 2 ^ j a := by
  have hb : PT fun a => bitsOfNat (k a) := PT.bits.comp hk
  refine (PT.ofBits (PT.map (g := fun a (i : ℕ) => (bitsOfNat (k a)).getI i)
    (PT.filter (p := fun a (i : ℕ) => decide (j a ≤ i)) (PT.rangeLength hb)
    (PT.le (hj.comp PT.fst) PT.snd))
    (PT.getI (hb.comp PT.fst) PT.snd))).of_eq fun a => ?_
  rw [div_two_pow_eq_natOfBits, drop_eq_filter]

theorem pt_hcL {k : α → ℕ} (hk : PT k) : PT fun a => hcL (k a) := by
  unfold hcL
  have hR : PT fun a => List.range ((bitsOfNat (k a)).length + 1) :=
    PT.rangeLength (PT.append (PT.bits.comp hk) (PT.const [false])) |>.of_eq fun a => by simp
  exact PT.flatMap hR (PT.cons (pt_divPow (hk.comp PT.fst) PT.snd)
    (PT.single (PT.pred (pt_divPow (hk.comp PT.fst) PT.snd))))

end Article

end HTN
