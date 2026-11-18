import HtnPlanning.Interleave.InterleaveList
/-!
# Consuming interleavings one element at a time

The soundness proof of the encoding of `HtnComplexity/SpaceEnc/` reads a plan action by
action and keeps track of which *words* (refinements of the parallel subtasks) have been
consumed how far.  This file provides the bookkeeping, for an arbitrary alphabet:

* `HTN.SpaceEnc.CS bls z` — `z` is the concatenation of interleavings of the blocks `bls`
  (the refinement of a loop, one block per iteration);
* `HTN.SpaceEnc.Gen bA bB φ z` — `z` interleaves a `CS` of `bA`, a `CS` of `bB` and the word `φ`;
* the step lemmas `HTN.SpaceEnc.interleaveList_cons`, `HTN.SpaceEnc.cs_cons`,
  `HTN.SpaceEnc.gen_cons`: the first element of `z` is the head of one of the words, which is then
  shortened;
* `HTN.SpaceEnc.msOf` — the multiset of the non-empty words of a block, and how it changes.
-/

namespace HTN

namespace SpaceEnc

variable {α : Type*}

/-! ### Interleavings of many words -/

/-- All words of a block are empty. -/
def AllEmpty (bl : List (List α)) : Prop := ∀ w ∈ bl, w = []

theorem interleaveList_nil_iff {bl : List (List α)} : InterleaveList bl [] ↔ AllEmpty bl := by
  constructor
  · intro h
    generalize hz : ([] : List α) = z at h
    induction h with
    | nil => intro w hw; simp at hw
    | @cons as bs cs ls h hint ih =>
      subst hz
      obtain ⟨rfl, rfl⟩ := hint.eq_nil_of_left
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · rfl
      · exact ih rfl w hw
  · exact fun h => InterleaveList.of_forall_nil h

/-- **The first element of an interleaving is the head of one of the words.** -/
theorem interleaveList_cons {bl : List (List α)} {a : α} {z : List α}
    (h : InterleaveList bl (a :: z)) :
    ∃ (i : ℕ) (t : List α), bl[i]? = some (a :: t) ∧ InterleaveList (bl.set i t) z := by
  generalize hz : a :: z = z' at h
  induction h generalizing z with
  | nil => simp at hz
  | @cons as bs cs ls h hint ih =>
    subst hz
    cases hint with
    | left _ hint' =>
      exact ⟨0, _, rfl, InterleaveList.cons h hint'⟩
    | right _ hint' =>
      obtain ⟨i, t, hi, hrest⟩ := ih rfl
      exact ⟨i + 1, t, by simpa using hi, by simpa using InterleaveList.cons hrest hint'⟩

/-- The converse step. -/
theorem interleaveList_cons_of {bl : List (List α)} {a : α} {z : List α} {i : ℕ} {t : List α}
    (hi : bl[i]? = some (a :: t)) (h : InterleaveList (bl.set i t) z) :
    InterleaveList bl (a :: z) := by
  induction bl generalizing i z with
  | nil => simp at hi
  | cons w ws ih =>
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.set_cons_zero] at h
      cases h with
      | cons h hint => exact InterleaveList.cons h (Interleave.left a hint)
    · simp only [List.getElem?_cons_succ] at hi
      simp only [List.set_cons_succ] at h
      cases h with
      | cons h hint =>
        -- `z` interleaves `w` with an interleaving of the rest; push `a` into the rest
        exact InterleaveList.cons (ih hi h) (Interleave.right a hint)

/-! ### Concatenations of interleavings -/

/-- `CS bls z`: `z` is the concatenation of interleavings of the blocks of `bls`. -/
def CS : List (List (List α)) → List α → Prop
  | [], z => z = []
  | bl :: bls, z => ∃ z₁ z₂, InterleaveList bl z₁ ∧ CS bls z₂ ∧ z = z₁ ++ z₂

theorem cs_nil {bls : List (List (List α))} (h : CS bls []) : ∀ bl ∈ bls, AllEmpty bl := by
  induction bls with
  | nil => simp
  | cons bl bls ih =>
    obtain ⟨z₁, z₂, h₁, h₂, hz⟩ := h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hz.symm
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact interleaveList_nil_iff.1 h₁
    · exact ih h₂ b hb

/-- **The first element of a concatenation of interleavings is the head of a word of the first
block that is not entirely consumed.** -/
theorem cs_cons {bls : List (List (List α))} {a : α} {z : List α} (h : CS bls (a :: z)) :
    ∃ (e : List (List (List α))) (bl : List (List α)) (rest : List (List (List α))) (i : ℕ)
      (t : List α), bls = e ++ bl :: rest ∧ (∀ b ∈ e, AllEmpty b) ∧ bl[i]? = some (a :: t) ∧
      CS (bl.set i t :: rest) z := by
  induction bls with
  | nil => simp [CS] at h
  | cons bl bls ih =>
    obtain ⟨z₁, z₂, h₁, h₂, hz⟩ := h
    rcases z₁ with _ | ⟨b, z₁⟩
    · simp only [List.nil_append] at hz
      subst hz
      obtain ⟨e, bl', rest, i, t, rfl, he, hi, hcs⟩ := ih h₂
      refine ⟨bl :: e, bl', rest, i, t, rfl, ?_, hi, hcs⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact interleaveList_nil_iff.1 h₁
      · exact he b hb
    · simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      obtain ⟨i, t, hi, h₁'⟩ := interleaveList_cons h₁
      exact ⟨[], bl, bls, i, t, rfl, by simp, hi, z₁, z₂, h₁', h₂, rfl⟩

/-! ### Three processes -/

/-- `Gen bA bB φ z`: `z` interleaves a concatenation of interleavings of `bA`, one of `bB`, and
the word `φ`. -/
def Gen (bA bB : List (List (List α))) (φ : List α) (z : List α) : Prop :=
  ∃ zA zB zBF, CS bA zA ∧ CS bB zB ∧ Interleave zB φ zBF ∧ Interleave zA zBF z

theorem gen_nil {bA bB : List (List (List α))} {φ : List α} (h : Gen bA bB φ []) : φ = [] := by
  obtain ⟨zA, zB, zBF, -, -, h₃, h₄⟩ := h
  obtain ⟨-, rfl⟩ := h₄.eq_nil_of_left
  exact h₃.eq_nil_of_left.2

/-- **The first element of a three-process interleaving** comes from one of the processes. -/
theorem gen_cons {bA bB : List (List (List α))} {φ : List α} {a : α} {z : List α}
    (h : Gen bA bB φ (a :: z)) :
    (∃ e bl rest i t, bA = e ++ bl :: rest ∧ (∀ b ∈ e, AllEmpty b) ∧ bl[i]? = some (a :: t) ∧
        Gen (bl.set i t :: rest) bB φ z) ∨
      (∃ e bl rest i t, bB = e ++ bl :: rest ∧ (∀ b ∈ e, AllEmpty b) ∧
        bl[i]? = some (a :: t) ∧ Gen bA (bl.set i t :: rest) φ z) ∨
      (∃ φ', φ = a :: φ' ∧ Gen bA bB φ' z) := by
  obtain ⟨zA, zB, zBF, hA, hB, h₃, h₄⟩ := h
  cases h₄ with
  | left _ h₄ =>
    obtain ⟨e, bl, rest, i, t, rfl, he, hi, hcs⟩ := cs_cons hA
    exact Or.inl ⟨e, bl, rest, i, t, rfl, he, hi, _, zB, zBF, hcs, hB, h₃, h₄⟩
  | right _ h₄ =>
    cases h₃ with
    | left _ h₃ =>
      obtain ⟨e, bl, rest, i, t, rfl, he, hi, hcs⟩ := cs_cons hB
      exact Or.inr (Or.inl ⟨e, bl, rest, i, t, rfl, he, hi, zA, _, _, hA, hcs, h₃, h₄⟩)
    | right _ h₃ =>
      exact Or.inr (Or.inr ⟨_, rfl, zA, zB, _, hA, hB, h₃, h₄⟩)

/-! ### The multiset of the remaining words of a block -/

variable [DecidableEq α]

/-- The non-empty words of a block, as a multiset. -/
def msOf (bl : List (List α)) : Multiset (List α) := Multiset.filter (· ≠ []) (bl : Multiset (List α))

omit [DecidableEq α] in
theorem mem_msOf {bl : List (List α)} {w : List α} : w ∈ msOf bl ↔ w ∈ bl ∧ w ≠ [] := by
  simp [msOf]

omit [DecidableEq α] in
theorem allEmpty_iff_msOf {bl : List (List α)} : AllEmpty bl ↔ msOf bl = 0 := by
  simp only [AllEmpty, msOf, Multiset.filter_eq_nil, Multiset.mem_coe, not_not]

theorem msOf_set {bl : List (List α)} {i : ℕ} {w t : List α} (hi : bl[i]? = some w)
    (hw : w ≠ []) :
    msOf (bl.set i t) = (msOf bl).erase w + Multiset.filter (· ≠ []) {t} := by
  have hlt : i < bl.length := by
    rcases Nat.lt_or_ge i bl.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hi
  have hget : bl[i] = w := by simpa [List.getElem?_eq_getElem hlt] using hi
  -- `bl` is `w` together with the other words, `bl.set i t` is `t` together with them
  have h1 : (bl : Multiset (List α)) = w ::ₘ (bl.eraseIdx i : Multiset (List α)) := by
    rw [Multiset.cons_coe]
    refine Multiset.coe_eq_coe.2 ?_
    rw [← hget]
    exact (List.getElem_cons_eraseIdx_perm hlt).symm
  have h2 : ((bl.set i t : List (List α)) : Multiset (List α)) =
      t ::ₘ (bl.eraseIdx i : Multiset (List α)) := by
    rw [Multiset.cons_coe]
    refine Multiset.coe_eq_coe.2 ?_
    have hlt' : i < (bl.set i t).length := by simpa using hlt
    have := (List.getElem_cons_eraseIdx_perm hlt').symm
    simp only [List.getElem_set_self] at this
    rwa [List.eraseIdx_set_eq] at this
  unfold msOf
  rw [h1, h2, Multiset.filter_cons_of_pos (p := fun x => x ≠ []) _ hw, Multiset.erase_cons_head,
    Multiset.filter_cons, Multiset.filter_singleton, add_comm]
  rfl

end SpaceEnc

end HTN
