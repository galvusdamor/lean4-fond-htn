import HtnPlanning.Interleave.InterleaveGrow
/-!
# Splitting an interleaving at a cut of the interleaved word

`HtnPlanning/Interleave/InterleaveList.lean` proves that every *prefix* of an interleaving is an
interleaving of prefixes of the components.  The analysis of a block-structured interleaving —
the one the reduction of `HtnComplexity/Core/MergePartition.lean` needs — wants slightly more:
the components are cut into a first and a second half, and the two halves interleave the two
halves of the word *simultaneously*.

* `HTN.Interleave.exists_split` — the binary version: an interleaving of `u ++ v` cuts both
  components in two, the first parts interleaving `u` and the second parts interleaving `v`;
* `HTN.InterleaveList.exists_split` — the version for many components, the cut being recorded as
  a list of pairs;
* `HTN.InterleaveList.eq_nil_of_interleave_nil`, `HTN.InterleaveList.nil_cons`,
  `HTN.InterleaveList.of_append_replicate_nil` — empty components may be added or dropped freely,
  which is what makes the bookkeeping of the reduction possible.
-/

namespace HTN

universe u

variable {α : Type u}

namespace Interleave

/-- **An interleaving of a concatenation cuts both components.** -/
lemma exists_split : ∀ {u v xs ys : List α}, Interleave xs ys (u ++ v) →
    ∃ x₁ x₂ y₁ y₂ : List α, xs = x₁ ++ x₂ ∧ ys = y₁ ++ y₂ ∧
      Interleave x₁ y₁ u ∧ Interleave x₂ y₂ v := by
  intro u
  induction u with
  | nil =>
      intro v xs ys h
      exact ⟨[], xs, [], ys, rfl, rfl, Interleave.nil, by simpa using h⟩
  | cons a u ih =>
      intro v xs ys h
      rw [List.cons_append] at h
      cases h
      · rename_i xs' hh
        obtain ⟨x₁, x₂, y₁, y₂, hx, hy, h₁, h₂⟩ := ih hh
        exact ⟨a :: x₁, x₂, y₁, y₂, by rw [hx]; rfl, hy, Interleave.left a h₁, h₂⟩
      · rename_i ys' hh
        obtain ⟨x₁, x₂, y₁, y₂, hx, hy, h₁, h₂⟩ := ih hh
        exact ⟨x₁, x₂, a :: y₁, y₂, hx, by rw [hy]; rfl, Interleave.right a h₁, h₂⟩

end Interleave

namespace InterleaveList

/-- Inversion at a component: an interleaving of `a :: ls` interleaves `a` with an interleaving
of `ls`. -/
lemma cons_inv {a : List α} {ls : List (List α)} {z : List α} (h : InterleaveList (a :: ls) z) :
    ∃ bs : List α, InterleaveList ls bs ∧ Interleave a bs z := by
  generalize hL : (a :: ls) = L at h
  induction h with
  | nil => simp at hL
  | @cons as bs cs ls' hrest hint _ =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hL.symm
      exact ⟨bs, hrest, hint⟩

/-- An interleaving of no components at all is the empty word. -/
lemma eq_nil_of_nil_components {z : List α} (h : InterleaveList ([] : List (List α)) z) :
    z = [] := by
  generalize hL : ([] : List (List α)) = L at h
  cases h with
  | nil => rfl
  | cons hrest hint => simp at hL

/-- **An interleaving of a concatenation cuts every component.**  The cut is recorded as a list
of pairs: each component is the concatenation of its two parts, the first parts interleave `u`
and the second parts interleave `v`. -/
lemma exists_split : ∀ {ls : List (List α)} {u v : List α}, InterleaveList ls (u ++ v) →
    ∃ prs : List (List α × List α), ls = prs.map (fun p => p.1 ++ p.2) ∧
      InterleaveList (prs.map Prod.fst) u ∧ InterleaveList (prs.map Prod.snd) v := by
  intro ls
  induction ls with
  | nil =>
      intro u v h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 (eq_nil_of_nil_components h)
      exact ⟨[], rfl, InterleaveList.nil, InterleaveList.nil⟩
  | cons a ls ih =>
      intro u v h
      obtain ⟨bs, hrest, hint⟩ := cons_inv h
      obtain ⟨x₁, x₂, y₁, y₂, hx, hy, h₁, h₂⟩ := hint.exists_split
      subst hy
      obtain ⟨prs, hprs, hu, hv⟩ := ih hrest
      refine ⟨(x₁, x₂) :: prs, ?_, ?_, ?_⟩
      · simp [hx, hprs]
      · exact InterleaveList.cons hu h₁
      · exact InterleaveList.cons hv h₂

/-- An interleaving of the empty word has only empty components. -/
lemma eq_nil_of_interleave_nil {ls : List (List α)} {z : List α} (h : InterleaveList ls z) :
    z = [] → ∀ l ∈ ls, l = [] := by
  induction h with
  | nil => intro _ l hl; simp at hl
  | @cons as bs cs ls hrest hint ih =>
      intro hcs l hl
      subst hcs
      obtain ⟨ha, hb⟩ := hint.eq_nil_of_left
      subst ha
      rcases List.mem_cons.1 hl with rfl | hl
      · rfl
      · exact ih hb l hl

/-- An empty component may be dropped. -/
lemma of_nil_cons {ls : List (List α)} {z : List α} (h : InterleaveList ([] :: ls) z) :
    InterleaveList ls z := by
  obtain ⟨bs, hrest, hint⟩ := cons_inv h
  rw [hint.eq_of_nil_left]
  exact hrest

/-- An empty component may be added. -/
lemma nil_cons {ls : List (List α)} {z : List α} (h : InterleaveList ls z) :
    InterleaveList ([] :: ls) z :=
  InterleaveList.cons h (Interleave.nil_left z)

/-- Trailing empty components may be dropped. -/
lemma of_append_replicate_nil {ls : List (List α)} {z : List α} :
    ∀ {k : ℕ}, InterleaveList (ls ++ List.replicate k []) z → InterleaveList ls z := by
  intro k
  induction k with
  | zero => intro h; simpa using h
  | succ k ih =>
      intro h
      refine ih ?_
      have hperm : (ls ++ List.replicate (k + 1) ([] : List α)).Perm
          ([] :: (ls ++ List.replicate k [])) := by
        rw [List.replicate_succ]
        exact List.perm_middle
      exact of_nil_cons (h.perm hperm)

end InterleaveList

end HTN
