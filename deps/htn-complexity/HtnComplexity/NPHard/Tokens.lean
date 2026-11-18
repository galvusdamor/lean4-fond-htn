import HtnComplexity.NPHard.Nums
/-!
# Formulas as token lists

A formula in conjunctive normal form is written as a flat list of numbers (`toks`): every clause
is a separator `0` followed by its literals, the literal `(v, b)` written `2 v + 1` (negative) or
`2 v + 2` (positive).  Loops over the literals of the formula, with the index of their clause and
whether they are the last literal of it, are loops over the positions of the token list
(`tokLoop_toks`).
-/

namespace HTN.NPHard

/-- The token of a literal. -/
def litTok (l : ℕ × Bool) : ℕ := 2 * l.1 + if l.2 then 2 else 1

/-- The literal of a token. -/
def decLit (t : ℕ) : ℕ × Bool := ((t - 1) / 2, decide ((t - 1) % 2 = 1))

theorem decLit_litTok (l : ℕ × Bool) : decLit (litTok l) = l := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [decLit, litTok] <;> omega

theorem litTok_ne_zero (l : ℕ × Bool) : litTok l ≠ 0 := by
  unfold litTok; split <;> omega

/-- **The token list of a formula.** -/
def toks (φ : CNF) : List ℕ := φ.flatMap fun c => 0 :: c.map litTok

/-- The number of separators before position `i`. -/
def zerosBefore (T : List ℕ) (i : ℕ) : ℕ := ((List.range i).filter fun i' => T.getD i' 0 = 0).length

/-- The number of separators. -/
def nZeros (T : List ℕ) : ℕ := zerosBefore T T.length

/-- **A loop over the literals of a token list**: the chunk sees the index of the clause (counted
from `z`), the literal and whether it is the last one of its clause. -/
def tokLoop {α : Type} (F : ℕ → ℕ × Bool → Bool → List α) (T : List ℕ) (z : ℕ) : List α :=
  (List.range T.length).flatMap fun i => if T.getD i 0 = 0 then [] else
    F (z + zerosBefore T i - 1) (decLit (T.getD i 0)) (decide (T.getD (i + 1) 0 = 0))

/-- The loop over the literals of a formula, clause by clause. -/
def litLoop {α : Type} (F : ℕ → ℕ × Bool → Bool → List α) (φ : CNF) (z : ℕ) : List α :=
  (List.range φ.length).flatMap fun j => (List.range (φ.getD j []).length).flatMap fun r =>
    F (z + j) ((φ.getD j []).getD r (0, false)) (decide (r + 1 = (φ.getD j []).length))

theorem zerosBefore_append_left {A B : List ℕ} {i : ℕ} (hi : i ≤ A.length) :
    zerosBefore (A ++ B) i = zerosBefore A i := by
  unfold zerosBefore
  congr 1
  refine List.filter_congr fun i' hi' => ?_
  rw [List.mem_range] at hi'
  rw [List.getD_append _ _ _ _ (by omega)]

theorem zerosBefore_append_right (A B : List ℕ) (i : ℕ) :
    zerosBefore (A ++ B) (A.length + i) = nZeros A + zerosBefore B i := by
  unfold nZeros zerosBefore
  rw [List.range_add, List.filter_append, List.length_append]
  congr 1
  · congr 1
    refine List.filter_congr fun i' hi' => ?_
    rw [List.mem_range] at hi'
    rw [List.getD_append _ _ _ _ hi']
  · rw [List.filter_map, List.length_map]
    congr 2
    funext i'
    simp only [Function.comp]
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem toks_cons (c : List (ℕ × Bool)) (φ : CNF) :
    toks (c :: φ) = (0 :: c.map litTok) ++ toks φ := rfl

theorem getD_toks_zero (φ : CNF) : (toks φ).getD 0 0 = 0 := by
  cases φ <;> simp [toks]

theorem zerosBefore_head (c : List (ℕ × Bool)) {r : ℕ} (hr : r ≤ c.length) :
    zerosBefore (0 :: c.map litTok) (r + 1) = 1 := by
  unfold zerosBefore
  rw [List.range_succ_eq_map, List.filter_cons]
  simp only [List.getD_cons_zero, decide_true, ↓reduceIte, List.length_cons]
  have key : ∀ x : ℕ, x = 0 → x + 1 = 1 := by omega
  apply key
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
  rw [List.mem_range] at hs'
  simp only [Nat.succ_eq_add_one, List.getD_cons_succ, decide_eq_true_eq]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
  exact litTok_ne_zero _

theorem nZeros_head (c : List (ℕ × Bool)) : nZeros (0 :: c.map litTok) = 1 := by
  unfold nZeros; rw [List.length_cons, List.length_map]; exact zerosBefore_head c le_rfl

theorem tokLoop_toks {α : Type} (F : ℕ → ℕ × Bool → Bool → List α) (φ : CNF) (z : ℕ) :
    tokLoop F (toks φ) z = litLoop F φ z := by
  induction φ generalizing z with
  | nil => simp [tokLoop, litLoop, toks]
  | cons c φ ih =>
    set A := 0 :: c.map litTok with hA
    have hlenA : A.length = c.length + 1 := by simp [hA]
    unfold tokLoop
    rw [toks_cons, ← hA, List.length_append, List.range_add, List.flatMap_append, List.flatMap_map]
    have h2 : ((List.range (toks φ).length).flatMap fun i =>
        if (A ++ toks φ).getD (A.length + i) 0 = 0 then [] else
          F (z + zerosBefore (A ++ toks φ) (A.length + i) - 1)
            (decLit ((A ++ toks φ).getD (A.length + i) 0))
            (decide ((A ++ toks φ).getD (A.length + i + 1) 0 = 0))) = tokLoop F (toks φ) (z + 1) := by
      unfold tokLoop
      refine List.flatMap_congr fun i _ => ?_
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
        zerosBefore_append_right, hA, nZeros_head, ← hA, Nat.add_assoc,
        List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      congr 2
      omega
    have h1 : ((List.range A.length).flatMap fun i =>
        if (A ++ toks φ).getD i 0 = 0 then [] else
          F (z + zerosBefore (A ++ toks φ) i - 1) (decLit ((A ++ toks φ).getD i 0))
            (decide ((A ++ toks φ).getD (i + 1) 0 = 0))) =
        (List.range c.length).flatMap fun r => F z (c.getD r (0, false)) (decide (r + 1 = c.length)) := by
      rw [hlenA, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [hA, List.cons_append, List.getD_cons_zero, ↓reduceIte, List.nil_append]
      refine List.flatMap_congr fun r hr => ?_
      rw [List.mem_range] at hr
      have hget : (List.map litTok c ++ toks φ).getD r 0 = litTok (c.getD r (0, false)) := by
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_map, List.getD_eq_getElem _ _ hr]
      simp only [Nat.succ_eq_add_one, List.getD_cons_succ, hget, litTok_ne_zero, ↓reduceIte,
        decLit_litTok]
      rw [show zerosBefore (0 :: (List.map litTok c ++ toks φ)) (r + 1) = 1 by
        rw [← List.cons_append, zerosBefore_append_left (by simp; omega)]
        exact zerosBefore_head c (by omega)]
      congr 2
      rcases Nat.lt_or_ge (r + 1) c.length with h | h
      · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_map]
        simp [litTok_ne_zero]; omega
      · rw [List.getD_append_right _ _ _ _ (by simp; omega),
          show r + 1 - (List.map litTok c).length = 0 by simp; omega, getD_toks_zero]
        simp; omega
    rw [h1, h2, ih]
    unfold litLoop
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    congr 1
    refine List.flatMap_congr fun j _ => ?_
    congr 1
    funext r
    congr 1
    omega

theorem nZeros_toks (φ : CNF) : nZeros (toks φ) = φ.length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [toks_cons]
    unfold nZeros
    rw [List.length_append, zerosBefore_append_right]
    unfold nZeros at ih
    rw [ih, nZeros_head, List.length_cons, Nat.add_comm]

end HTN.NPHard
