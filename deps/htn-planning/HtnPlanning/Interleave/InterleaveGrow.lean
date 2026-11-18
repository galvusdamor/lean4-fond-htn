import HtnPlanning.Interleave.SchedPeel
/-!
# Growing an interleaving of many components

The plan of the compiled problem of `HtnComplexity/ToHtnAc/ToHtnAc.lean` is built block by block,
and each block *extends* the interleaving built so far: it continues the run of one of the
components (a memory cell answering a read request) or starts a new one (a memory cell being
filled).  This file provides the three corresponding operations on `HTN.InterleaveList`, plus
the invariance under permuting the components that lets one always work at the head of the
component list.

* `HTN.InterleaveList.perm` — the components may be reordered;
* `HTN.InterleaveList.extend_head` — actions appended at the end of the interleaving may be
  attributed to the first component;
* `HTN.InterleaveList.cons_new` — they may also be attributed to a new component;
* `HTN.InterleaveList.append_replicate` — hence `w` new copies of one and the same component
  may be started at the end.
-/

namespace HTN

universe u

variable {α : Type u}

namespace InterleaveList

/-- **An interleaving does not depend on the order of the components.** -/
theorem perm {ls ls' : List (List α)} {z : List α} (h : InterleaveList ls z)
    (hp : ls.Perm ls') : InterleaveList ls' z :=
  sched_iff_interleaveList.1 ((sched_iff_interleaveList.2 h).perm hp)

/-- **Actions appended at the end of an interleaving continue its first component.** -/
theorem extend_head {a : List α} {ls : List (List α)} {z y : List α}
    (h : InterleaveList (a :: ls) z) : InterleaveList ((a ++ y) :: ls) (z ++ y) := by
  cases h with
  | @cons as bs cs ls h hint =>
      refine InterleaveList.cons h ?_
      have := hint.append_append (Interleave.nil_right y)
      simpa using this

/-- **Actions appended at the end of an interleaving may start a new component.** -/
theorem cons_new {ls : List (List α)} {z y : List α} (h : InterleaveList ls z) :
    InterleaveList (y :: ls) (z ++ y) :=
  InterleaveList.cons h (Interleave.append z y).symm

/-- **`w` copies of one new component may be started at the end of an interleaving.** -/
theorem append_replicate {ls : List (List α)} {z y : List α} (h : InterleaveList ls z) :
    ∀ w : ℕ, InterleaveList (List.replicate w y ++ ls) (z ++ (List.replicate w y).flatten) := by
  intro w
  induction w with
  | zero => simpa using h
  | succ w ih =>
      have h' := ih.cons_new (y := y)
      have hy : (y :: List.replicate w y).flatten = (List.replicate w y).flatten ++ y := by
        have : (List.replicate (w + 1) y).flatten = (List.replicate w y).flatten ++ y := by
          rw [List.replicate_succ']; simp
        rwa [List.replicate_succ] at this
      rw [List.replicate_succ, List.cons_append, hy, ← List.append_assoc]
      exact h'

end InterleaveList

/-! ## Interleaving an unordered family of components

Since the order of the components does not matter, it is convenient to keep them as a
*multiset*: growing the interleaving is then stated without any reordering bookkeeping. -/

/-- `InterleaveMS s z`: the list `z` is an interleaving of the family of components `s`. -/
def InterleaveMS (s : Multiset (List α)) (z : List α) : Prop :=
  ∃ l : List (List α), (l : Multiset (List α)) = s ∧ InterleaveList l z

namespace InterleaveMS

lemma nil : InterleaveMS (0 : Multiset (List α)) ([] : List α) :=
  ⟨[], rfl, InterleaveList.nil⟩

lemma of_interleaveList {ls : List (List α)} {z : List α} (h : InterleaveList ls z) :
    InterleaveMS (ls : Multiset (List α)) z := ⟨ls, rfl, h⟩

lemma exists_interleaveList {s : Multiset (List α)} {z : List α} (h : InterleaveMS s z) :
    ∃ l : List (List α), (l : Multiset (List α)) = s ∧ InterleaveList l z := h

/-- **A component of the family may be continued by actions appended at the end.** -/
lemma extend {y u : List α} {s : Multiset (List α)} {z : List α}
    (h : InterleaveMS (y ::ₘ s) z) : InterleaveMS ((y ++ u) ::ₘ s) (z ++ u) := by
  obtain ⟨l, hl, hint⟩ := h
  have hy : y ∈ l := by
    have : y ∈ (l : Multiset (List α)) := by rw [hl]; exact Multiset.mem_cons_self _ _
    simpa using this
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hy
  have hperm : (pre ++ y :: post).Perm (y :: (pre ++ post)) := List.perm_middle
  have hs : ((pre ++ post : List (List α)) : Multiset (List α)) = s := by
    have h1 : ((pre ++ y :: post : List (List α)) : Multiset (List α)) =
        y ::ₘ ((pre ++ post : List (List α)) : Multiset (List α)) :=
      Quot.sound hperm
    rw [h1] at hl
    exact (Multiset.cons_inj_right y).1 hl
  exact ⟨(y ++ u) :: (pre ++ post), by rw [← Multiset.cons_coe, hs], (hint.perm hperm).extend_head⟩

/-- **A new component may be started by actions appended at the end.** -/
lemma cons_new {y : List α} {s : Multiset (List α)} {z : List α} (h : InterleaveMS s z) :
    InterleaveMS (y ::ₘ s) (z ++ y) := by
  obtain ⟨l, hl, hint⟩ := h
  exact ⟨y :: l, by rw [← Multiset.cons_coe, hl], hint.cons_new⟩

/-- **`w` copies of a new component may be started at the end.** -/
lemma append_replicate {y : List α} {s : Multiset (List α)} {z : List α} (h : InterleaveMS s z)
    (w : ℕ) : InterleaveMS (Multiset.replicate w y + s)
      (z ++ (List.replicate w y).flatten) := by
  obtain ⟨l, hl, hint⟩ := h
  refine ⟨List.replicate w y ++ l, ?_, hint.append_replicate w⟩
  rw [← hl, ← Multiset.coe_replicate]
  rfl

end InterleaveMS

end HTN
