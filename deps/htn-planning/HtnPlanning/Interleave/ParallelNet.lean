import HtnPlanning.Interleave.Interleave
import HtnPlanning.Core.DecompositionIso
/-!
# Parallel and sequential composition of task networks

The initial task network of the HTN-AC compilation (`HtnComplexity/ToHtnAc/ToHtnAc.lean`) is a
*parallel* composition of two subnetworks, and the bodies of its methods are grids, i.e.
parallel compositions of chains.  Reasoning about such networks requires two structural
notions, formalised here:

* `HTN.TaskNetwork.IsPar tn tn₁ tn₂` — `tn` is the parallel composition `tn₁ ∥ tn₂`: its tasks
  are the disjoint union of the tasks of the parts, the labels agree, and two tasks are ordered
  exactly when they lie in the same part and are ordered there;
* `HTN.TaskNetwork.IsSeries tn tn₁ tn₂` — `tn` is the sequential composition `tn₁ ; tn₂`: as
  above, but in addition every task of `tn₁` precedes every task of `tn₂`.

For both notions we prove

* well-formedness (`IsPar.wf`, `IsSeries.wf`);
* the description of the linearizations: those of a parallel composition are the interleavings
  of the linearizations of the parts (`IsPar.isLinearization_iff`), those of a sequential
  composition are their concatenations (`IsSeries.isLinearization_iff`);
* that decomposition respects the composition: a decomposition step of `tn` is a step of one of
  the two parts (`IsPar.decompStep`, `IsSeries.decompStep`) and conversely (`IsPar.decompStep_left`
  and friends).

Together with `HTN.DecomposesTo.iso_avoiding` — a version of the replay theorem
`HTN.DecomposesTo.iso` in which the identifiers created by the replayed derivation avoid a
prescribed finite set — these are the tools used in `HtnPlanning/Interleave/NetYield.lean` to
describe the action sequences that a composed task network can be refined into.
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

namespace TaskNetwork

/-! ### Parallel composition -/

/-- `IsPar tn tn₁ tn₂`: the task network `tn` is the parallel composition of `tn₁` and `tn₂`. -/
structure IsPar (tn tn₁ tn₂ : TaskNetwork I A C) : Prop where
  /-- The two parts have disjoint task identifiers. -/
  disjoint : Disjoint tn₁.T tn₂.T
  /-- The tasks of the composition are those of the two parts. -/
  memT : ∀ t, t ∈ tn.T ↔ t ∈ tn₁.T ∨ t ∈ tn₂.T
  /-- The labelling agrees with the first part. -/
  α₁ : ∀ t ∈ tn₁.T, tn.α t = tn₁.α t
  /-- The labelling agrees with the second part. -/
  α₂ : ∀ t ∈ tn₂.T, tn.α t = tn₂.α t
  /-- Two tasks are ordered exactly when they are ordered inside one of the parts. -/
  ord : ∀ a b, tn.ord a b ↔ (tn₁.ord a b ∨ tn₂.ord a b)

/-- `IsSeries tn tn₁ tn₂`: the task network `tn` is the sequential composition of `tn₁`
and `tn₂`, i.e. `tn₁` followed by `tn₂`. -/
structure IsSeries (tn tn₁ tn₂ : TaskNetwork I A C) : Prop where
  /-- The two parts have disjoint task identifiers. -/
  disjoint : Disjoint tn₁.T tn₂.T
  /-- The tasks of the composition are those of the two parts. -/
  memT : ∀ t, t ∈ tn.T ↔ t ∈ tn₁.T ∨ t ∈ tn₂.T
  /-- The labelling agrees with the first part. -/
  α₁ : ∀ t ∈ tn₁.T, tn.α t = tn₁.α t
  /-- The labelling agrees with the second part. -/
  α₂ : ∀ t ∈ tn₂.T, tn.α t = tn₂.α t
  /-- Two tasks are ordered when they are ordered inside one of the parts, or when the first
  belongs to `tn₁` and the second to `tn₂`. -/
  ord : ∀ a b, tn.ord a b ↔
    (tn₁.ord a b ∨ tn₂.ord a b ∨ (a ∈ tn₁.T ∧ b ∈ tn₂.T))

/-- **Splitting a linearization along a decomposition of the tasks into two parts.**  If the
tasks of `tn` are the disjoint union of those of `tn₁` and `tn₂` and the orderings of the two
parts are contained in the ordering of `tn`, then a linearization of `tn` restricts to
linearizations of the two parts. -/
lemma isLinearization_filter_parts [DecidableEq I] {tn tn₁ tn₂ : TaskNetwork I A C}
    (hdisj : Disjoint tn₁.T tn₂.T) (hmemT : ∀ t, t ∈ tn.T ↔ t ∈ tn₁.T ∨ t ∈ tn₂.T)
    (hord₁ : ∀ a b, tn₁.ord a b → tn.ord a b) (hord₂ : ∀ a b, tn₂.ord a b → tn.ord a b)
    {l : List I} (hl : tn.IsLinearization l) :
    tn₁.IsLinearization (l.filter (fun t => decide (t ∈ tn₁.T))) ∧
      tn₂.IsLinearization (l.filter (fun t => ! decide (t ∈ tn₁.T))) := by
  classical
  obtain ⟨hn, hm, hp⟩ := hl
  refine ⟨⟨hn.filter _, ?_, ?_⟩, ⟨hn.filter _, ?_, ?_⟩⟩
  · intro t
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ht => ht.2, fun ht => ⟨(hm t).2 ((hmemT t).2 (Or.inl ht)), ht⟩⟩
  · refine (List.Pairwise.sublist List.filter_sublist hp).imp ?_
    intro a b hab hcon
    exact hab (hord₁ b a hcon)
  · intro t
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨ht, ht₁⟩
      rcases (hmemT t).1 ((hm t).1 ht) with h' | h'
      · exact absurd h' ht₁
      · exact h'
    · intro ht
      exact ⟨(hm t).2 ((hmemT t).2 (Or.inr ht)), Finset.disjoint_right.1 hdisj ht⟩
  · refine (List.Pairwise.sublist List.filter_sublist hp).imp ?_
    intro a b hab hcon
    exact hab (hord₂ b a hcon)

namespace IsPar

variable {tn tn₁ tn₂ : TaskNetwork I A C}

lemma symm (h : IsPar tn tn₁ tn₂) : IsPar tn tn₂ tn₁ where
  disjoint := h.disjoint.symm
  memT := fun t => (h.memT t).trans or_comm
  α₁ := h.α₂
  α₂ := h.α₁
  ord := fun a b => (h.ord a b).trans or_comm

lemma not_mem_right (h : IsPar tn tn₁ tn₂) {t : I} (ht : t ∈ tn₁.T) : t ∉ tn₂.T :=
  Finset.disjoint_left.1 h.disjoint ht

lemma not_mem_left (h : IsPar tn tn₁ tn₂) {t : I} (ht : t ∈ tn₂.T) : t ∉ tn₁.T :=
  Finset.disjoint_right.1 h.disjoint ht

/-- The parallel composition of two well-formed networks is well formed. -/
lemma wf (h : IsPar tn tn₁ tn₂) (h₁ : tn₁.WF) (h₂ : tn₂.WF) : tn.WF where
  mem_left := by
    intro a b hab
    rcases (h.ord a b).1 hab with hh | hh
    · exact (h.memT a).2 (Or.inl (h₁.mem_left hh))
    · exact (h.memT a).2 (Or.inr (h₂.mem_left hh))
  mem_right := by
    intro a b hab
    rcases (h.ord a b).1 hab with hh | hh
    · exact (h.memT b).2 (Or.inl (h₁.mem_right hh))
    · exact (h.memT b).2 (Or.inr (h₂.mem_right hh))
  irrefl := by
    intro a ha
    rcases (h.ord a a).1 ha with hh | hh
    · exact h₁.irrefl a hh
    · exact h₂.irrefl a hh
  trans := by
    intro a b c hab hbc
    rcases (h.ord a b).1 hab with hab' | hab' <;> rcases (h.ord b c).1 hbc with hbc' | hbc'
    · exact (h.ord a c).2 (Or.inl (h₁.trans hab' hbc'))
    · exact absurd (h₂.mem_left hbc') (h.not_mem_right (h₁.mem_right hab'))
    · exact absurd (h₁.mem_left hbc') (h.not_mem_left (h₂.mem_right hab'))
    · exact (h.ord a c).2 (Or.inr (h₂.trans hab' hbc'))

/-- The composition is primitive iff both parts are. -/
lemma isPrimitive_iff (h : IsPar tn tn₁ tn₂) :
    tn.IsPrimitive ↔ tn₁.IsPrimitive ∧ tn₂.IsPrimitive := by
  constructor
  · intro hp
    constructor
    · intro t ht
      obtain ⟨a, ha⟩ := hp t ((h.memT t).2 (Or.inl ht))
      exact ⟨a, by rw [← h.α₁ t ht]; exact ha⟩
    · intro t ht
      obtain ⟨a, ha⟩ := hp t ((h.memT t).2 (Or.inr ht))
      exact ⟨a, by rw [← h.α₂ t ht]; exact ha⟩
  · rintro ⟨hp₁, hp₂⟩ t ht
    rcases (h.memT t).1 ht with ht' | ht'
    · obtain ⟨a, ha⟩ := hp₁ t ht'
      exact ⟨a, by rw [h.α₁ t ht']; exact ha⟩
    · obtain ⟨a, ha⟩ := hp₂ t ht'
      exact ⟨a, by rw [h.α₂ t ht']; exact ha⟩

/-! #### Linearizations of a parallel composition -/

/-- Two tasks lying in different parts of a parallel composition are never ordered. -/
lemma not_ord_cross (h : IsPar tn tn₁ tn₂) (h₁ : tn₁.WF) (h₂ : tn₂.WF) {a b : I}
    (ha : a ∈ tn₁.T) (hb : b ∈ tn₂.T) : ¬ tn.ord a b ∧ ¬ tn.ord b a := by
  constructor
  · intro hcon
    rcases (h.ord a b).1 hcon with hh | hh
    · exact h.not_mem_left hb (h₁.mem_right hh)
    · exact h.not_mem_right ha (h₂.mem_left hh)
  · intro hcon
    rcases (h.ord b a).1 hcon with hh | hh
    · exact h.not_mem_left hb (h₁.mem_left hh)
    · exact h.not_mem_right ha (h₂.mem_right hh)

/-- **An interleaving of linearizations of the parts is a linearization of the parallel
composition.** -/
lemma isLinearization_of_interleave (h : IsPar tn tn₁ tn₂) (hw₁ : tn₁.WF) (hw₂ : tn₂.WF)
    {l l₁ l₂ : List I} (hint : Interleave l₁ l₂ l) (h₁ : tn₁.IsLinearization l₁)
    (h₂ : tn₂.IsLinearization l₂) : tn.IsLinearization l := by
  obtain ⟨hn₁, hm₁, hp₁⟩ := h₁
  obtain ⟨hn₂, hm₂, hp₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · refine hint.perm.nodup_iff.2 ?_
    refine List.Nodup.append hn₁ hn₂ ?_
    intro a ha ha'
    exact h.not_mem_right ((hm₁ a).1 ha) ((hm₂ a).1 ha')
  · intro t
    rw [hint.mem_iff, hm₁ t, hm₂ t, h.memT t]
  · have hp₁' : l₁.Pairwise (fun a b => ¬ tn.ord b a) := by
      refine (List.Pairwise.and_mem.1 hp₁).imp ?_
      rintro a b ⟨ha, hb, hab⟩ hcon
      rcases (h.ord b a).1 hcon with hh | hh
      · exact hab hh
      · exact h.not_mem_right ((hm₁ a).1 ha) (hw₂.mem_right hh)
    have hp₂' : l₂.Pairwise (fun a b => ¬ tn.ord b a) := by
      refine (List.Pairwise.and_mem.1 hp₂).imp ?_
      rintro a b ⟨ha, hb, hab⟩ hcon
      rcases (h.ord b a).1 hcon with hh | hh
      · exact h.not_mem_right (hw₁.mem_right hh) ((hm₂ a).1 ha)
      · exact hab hh
    refine hint.pairwise hp₁' hp₂' ?_
    intro a ha b hb
    have hcross := h.not_ord_cross hw₁ hw₂ ((hm₁ a).1 ha) ((hm₂ b).1 hb)
    exact ⟨hcross.2, hcross.1⟩

/-- **Every linearization of a parallel composition is an interleaving of linearizations of the
parts.** -/
lemma exists_interleave_of_isLinearization [DecidableEq I] (h : IsPar tn tn₁ tn₂) {l : List I}
    (hl : tn.IsLinearization l) :
    ∃ l₁ l₂, Interleave l₁ l₂ l ∧ tn₁.IsLinearization l₁ ∧ tn₂.IsLinearization l₂ := by
  classical
  obtain ⟨h₁, h₂⟩ := isLinearization_filter_parts h.disjoint h.memT
    (fun a b hab => (h.ord a b).2 (Or.inl hab)) (fun a b hab => (h.ord a b).2 (Or.inr hab)) hl
  exact ⟨_, _, interleave_filter _ l, h₁, h₂⟩

end IsPar

namespace IsSeries

variable {tn tn₁ tn₂ : TaskNetwork I A C}

lemma not_mem_right (h : IsSeries tn tn₁ tn₂) {t : I} (ht : t ∈ tn₁.T) : t ∉ tn₂.T :=
  Finset.disjoint_left.1 h.disjoint ht

lemma not_mem_left (h : IsSeries tn tn₁ tn₂) {t : I} (ht : t ∈ tn₂.T) : t ∉ tn₁.T :=
  Finset.disjoint_right.1 h.disjoint ht

/-- The sequential composition of two well-formed networks is well formed. -/
lemma wf (h : IsSeries tn tn₁ tn₂) (h₁ : tn₁.WF) (h₂ : tn₂.WF) : tn.WF where
  mem_left := by
    intro a b hab
    rcases (h.ord a b).1 hab with hh | hh | ⟨hh, -⟩
    · exact (h.memT a).2 (Or.inl (h₁.mem_left hh))
    · exact (h.memT a).2 (Or.inr (h₂.mem_left hh))
    · exact (h.memT a).2 (Or.inl hh)
  mem_right := by
    intro a b hab
    rcases (h.ord a b).1 hab with hh | hh | ⟨-, hh⟩
    · exact (h.memT b).2 (Or.inl (h₁.mem_right hh))
    · exact (h.memT b).2 (Or.inr (h₂.mem_right hh))
    · exact (h.memT b).2 (Or.inr hh)
  irrefl := by
    intro a ha
    rcases (h.ord a a).1 ha with hh | hh | ⟨h1, h2⟩
    · exact h₁.irrefl a hh
    · exact h₂.irrefl a hh
    · exact h.not_mem_right h1 h2
  trans := by
    intro a b c hab hbc
    rcases (h.ord a b).1 hab with hab' | hab' | ⟨ha₁, hb₂⟩ <;>
      rcases (h.ord b c).1 hbc with hbc' | hbc' | ⟨hb₁, hc₂⟩
    · exact (h.ord a c).2 (Or.inl (h₁.trans hab' hbc'))
    · exact absurd (h₂.mem_left hbc') (h.not_mem_right (h₁.mem_right hab'))
    · exact (h.ord a c).2 (Or.inr (Or.inr ⟨h₁.mem_left hab', hc₂⟩))
    · exact absurd (h₁.mem_left hbc') (h.not_mem_left (h₂.mem_right hab'))
    · exact (h.ord a c).2 (Or.inr (Or.inl (h₂.trans hab' hbc')))
    · exact absurd hb₁ (h.not_mem_left (h₂.mem_right hab'))
    · exact absurd (h₁.mem_left hbc') (h.not_mem_left hb₂)
    · exact (h.ord a c).2 (Or.inr (Or.inr ⟨ha₁, h₂.mem_right hbc'⟩))
    · exact absurd hb₁ (h.not_mem_left hb₂)

/-- The composition is primitive iff both parts are. -/
lemma isPrimitive_iff (h : IsSeries tn tn₁ tn₂) :
    tn.IsPrimitive ↔ tn₁.IsPrimitive ∧ tn₂.IsPrimitive := by
  constructor
  · intro hp
    constructor
    · intro t ht
      obtain ⟨a, ha⟩ := hp t ((h.memT t).2 (Or.inl ht))
      exact ⟨a, by rw [← h.α₁ t ht]; exact ha⟩
    · intro t ht
      obtain ⟨a, ha⟩ := hp t ((h.memT t).2 (Or.inr ht))
      exact ⟨a, by rw [← h.α₂ t ht]; exact ha⟩
  · rintro ⟨hp₁, hp₂⟩ t ht
    rcases (h.memT t).1 ht with ht' | ht'
    · obtain ⟨a, ha⟩ := hp₁ t ht'
      exact ⟨a, by rw [h.α₁ t ht']; exact ha⟩
    · obtain ⟨a, ha⟩ := hp₂ t ht'
      exact ⟨a, by rw [h.α₂ t ht']; exact ha⟩

/-! #### Linearizations of a sequential composition -/

/-- **The concatenation of linearizations of the parts is a linearization of the sequential
composition.** -/
lemma isLinearization_append (h : IsSeries tn tn₁ tn₂) (hw₁ : tn₁.WF) (hw₂ : tn₂.WF)
    {l₁ l₂ : List I} (h₁ : tn₁.IsLinearization l₁) (h₂ : tn₂.IsLinearization l₂) :
    tn.IsLinearization (l₁ ++ l₂) := by
  obtain ⟨hn₁, hm₁, hp₁⟩ := h₁
  obtain ⟨hn₂, hm₂, hp₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.append hn₁ hn₂ ?_
    intro a ha ha'
    exact h.not_mem_right ((hm₁ a).1 ha) ((hm₂ a).1 ha')
  · intro t
    rw [List.mem_append, hm₁ t, hm₂ t, h.memT t]
  · refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
    · refine (List.Pairwise.and_mem.1 hp₁).imp ?_
      rintro a b ⟨ha, -, hab⟩ hcon
      rcases (h.ord b a).1 hcon with hh | hh | ⟨hb₁, ha₂⟩
      · exact hab hh
      · exact h.not_mem_right ((hm₁ a).1 ha) (hw₂.mem_right hh)
      · exact h.not_mem_right ((hm₁ a).1 ha) ha₂
    · refine (List.Pairwise.and_mem.1 hp₂).imp ?_
      rintro a b ⟨ha, hb, hab⟩ hcon
      rcases (h.ord b a).1 hcon with hh | hh | ⟨hb₁, -⟩
      · exact h.not_mem_right (hw₁.mem_right hh) ((hm₂ a).1 ha)
      · exact hab hh
      · exact h.not_mem_right hb₁ ((hm₂ b).1 hb)
    · intro a ha b hb hcon
      have ha₁ : a ∈ tn₁.T := (hm₁ a).1 ha
      have hb₂ : b ∈ tn₂.T := (hm₂ b).1 hb
      rcases (h.ord b a).1 hcon with hh | hh | ⟨hb₁, -⟩
      · exact h.not_mem_left hb₂ (hw₁.mem_left hh)
      · exact h.not_mem_right ha₁ (hw₂.mem_right hh)
      · exact h.not_mem_left hb₂ hb₁

/-- **Every linearization of a sequential composition is a concatenation of linearizations of
the parts.** -/
lemma exists_append_of_isLinearization [DecidableEq I] (h : IsSeries tn tn₁ tn₂) {l : List I}
    (hl : tn.IsLinearization l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ tn₁.IsLinearization l₁ ∧ tn₂.IsLinearization l₂ := by
  classical
  obtain ⟨h₁, h₂⟩ := isLinearization_filter_parts h.disjoint h.memT
    (fun a b hab => (h.ord a b).2 (Or.inl hab))
    (fun a b hab => (h.ord a b).2 (Or.inr (Or.inl hab))) hl
  refine ⟨_, _, ?_, h₁, h₂⟩
  refine eq_filter_append_filter ?_
  obtain ⟨-, hm, hp⟩ := hl
  refine (List.Pairwise.and_mem.1 hp).imp ?_
  rintro a b ⟨ha, hb, hab⟩ hpb
  simp only [decide_eq_true_eq] at hpb ⊢
  by_contra ha₁
  have ha₂ : a ∈ tn₂.T := by
    rcases (h.memT a).1 ((hm a).1 ha) with h' | h'
    · exact absurd h' ha₁
    · exact h'
  exact hab ((h.ord b a).2 (Or.inr (Or.inr ⟨hpb, ha₂⟩)))

end IsSeries

/-! ### Action sequences of composed networks -/

/-- The action sequence of an interleaving splits into action sequences of the two parts. -/
lemma exists_interleave_actionSeq {tn tn₁ tn₂ : TaskNetwork I A C} {l l₁ l₂ : List I}
    (hint : Interleave l₁ l₂ l) (hα₁ : ∀ t ∈ l₁, tn.α t = tn₁.α t)
    (hα₂ : ∀ t ∈ l₂, tn.α t = tn₂.α t) {as : List A} (has : tn.IsActionSeq l as) :
    ∃ as₁ as₂, Interleave as₁ as₂ as ∧ tn₁.IsActionSeq l₁ as₁ ∧ tn₂.IsActionSeq l₂ as₂ := by
  induction hint generalizing as with
  | nil =>
      cases as with
      | nil => exact ⟨[], [], Interleave.nil, rfl, rfl⟩
      | cons a as => simp [TaskNetwork.IsActionSeq] at has
  | @left xs ys zs a hint ih =>
      cases as with
      | nil => simp [TaskNetwork.IsActionSeq] at has
      | cons b as =>
          simp only [TaskNetwork.IsActionSeq, List.map_cons, List.cons.injEq] at has
          obtain ⟨hab, hrest⟩ := has
          obtain ⟨as₁, as₂, hI, hs₁, hs₂⟩ := ih (fun t ht => hα₁ t (by simp [ht])) hα₂ hrest
          refine ⟨b :: as₁, as₂, Interleave.left b hI, ?_, hs₂⟩
          simp only [TaskNetwork.IsActionSeq, List.map_cons]
          rw [← hα₁ a (by simp), hab]
          exact congrArg _ hs₁
  | @right xs ys zs a hint ih =>
      cases as with
      | nil => simp [TaskNetwork.IsActionSeq] at has
      | cons b as =>
          simp only [TaskNetwork.IsActionSeq, List.map_cons, List.cons.injEq] at has
          obtain ⟨hab, hrest⟩ := has
          obtain ⟨as₁, as₂, hI, hs₁, hs₂⟩ := ih hα₁ (fun t ht => hα₂ t (by simp [ht])) hrest
          refine ⟨as₁, b :: as₂, Interleave.right b hI, hs₁, ?_⟩
          simp only [TaskNetwork.IsActionSeq, List.map_cons]
          rw [← hα₂ a (by simp), hab]
          exact congrArg _ hs₂

/-- Conversely, given an interleaving of the action sequences of the two parts, the identifier
lists can be interleaved in the same pattern, giving an action sequence of the composition. -/
lemma exists_interleave_ids {tn tn₁ tn₂ : TaskNetwork I A C} {l₁ l₂ : List I}
    {as₁ as₂ as : List A} (hint : Interleave as₁ as₂ as)
    (hα₁ : ∀ t ∈ l₁, tn.α t = tn₁.α t) (hα₂ : ∀ t ∈ l₂, tn.α t = tn₂.α t)
    (hs₁ : tn₁.IsActionSeq l₁ as₁) (hs₂ : tn₂.IsActionSeq l₂ as₂) :
    ∃ l : List I, Interleave l₁ l₂ l ∧ tn.IsActionSeq l as := by
  induction hint generalizing l₁ l₂ with
  | nil =>
      have h1 : l₁ = [] := by
        cases l₁ with
        | nil => rfl
        | cons t l => simp [TaskNetwork.IsActionSeq] at hs₁
      have h2 : l₂ = [] := by
        cases l₂ with
        | nil => rfl
        | cons t l => simp [TaskNetwork.IsActionSeq] at hs₂
      subst h1; subst h2
      exact ⟨[], Interleave.nil, rfl⟩
  | @left xs ys zs a hint ih =>
      cases l₁ with
      | nil => simp [TaskNetwork.IsActionSeq] at hs₁
      | cons t l₁ =>
          simp only [TaskNetwork.IsActionSeq, List.map_cons, List.cons.injEq] at hs₁
          obtain ⟨hta, hrest⟩ := hs₁
          obtain ⟨l, hI, hasl⟩ := ih (fun z hz => hα₁ z (by simp [hz])) hα₂ hrest hs₂
          refine ⟨t :: l, Interleave.left t hI, ?_⟩
          simp only [TaskNetwork.IsActionSeq, List.map_cons]
          rw [hα₁ t (by simp), hta]
          exact congrArg _ hasl
  | @right xs ys zs a hint ih =>
      cases l₂ with
      | nil => simp [TaskNetwork.IsActionSeq] at hs₂
      | cons t l₂ =>
          simp only [TaskNetwork.IsActionSeq, List.map_cons, List.cons.injEq] at hs₂
          obtain ⟨hta, hrest⟩ := hs₂
          obtain ⟨l, hI, hasl⟩ := ih hα₁ (fun z hz => hα₂ z (by simp [hz])) hs₁ hrest
          refine ⟨t :: l, Interleave.right t hI, ?_⟩
          simp only [TaskNetwork.IsActionSeq, List.map_cons]
          rw [hα₂ t (by simp), hta]
          exact congrArg _ hasl

/-- The action sequence of a concatenation splits into action sequences of the two parts. -/
lemma exists_append_actionSeq {tn tn₁ tn₂ : TaskNetwork I A C} {l₁ l₂ : List I} {as : List A}
    (hα₁ : ∀ t ∈ l₁, tn.α t = tn₁.α t) (hα₂ : ∀ t ∈ l₂, tn.α t = tn₂.α t)
    (has : tn.IsActionSeq (l₁ ++ l₂) as) :
    ∃ as₁ as₂, as = as₁ ++ as₂ ∧ tn₁.IsActionSeq l₁ as₁ ∧ tn₂.IsActionSeq l₂ as₂ := by
  induction l₁ generalizing as with
  | nil =>
      refine ⟨[], as, rfl, rfl, ?_⟩
      simpa only [TaskNetwork.IsActionSeq, List.nil_append] using
        (by
          simpa only [TaskNetwork.IsActionSeq, List.nil_append,
            List.map_congr_left (fun t ht => hα₂ t ht)] using has)
  | cons t l₁ ih =>
      cases as with
      | nil => simp [TaskNetwork.IsActionSeq] at has
      | cons b as =>
          simp only [TaskNetwork.IsActionSeq, List.cons_append, List.map_cons,
            List.cons.injEq] at has
          obtain ⟨htb, hrest⟩ := has
          obtain ⟨as₁, as₂, rfl, hs₁, hs₂⟩ :=
            ih (fun z hz => hα₁ z (by simp [hz])) hrest
          refine ⟨b :: as₁, as₂, rfl, ?_, hs₂⟩
          simp only [TaskNetwork.IsActionSeq, List.map_cons]
          rw [← hα₁ t (by simp), htb]
          exact congrArg _ hs₁

/-- Concatenating the action sequences of two parts gives the action sequence of the
concatenated identifier lists. -/
lemma append_actionSeq {tn tn₁ tn₂ : TaskNetwork I A C} {l₁ l₂ : List I} {as₁ as₂ : List A}
    (hα₁ : ∀ t ∈ l₁, tn.α t = tn₁.α t) (hα₂ : ∀ t ∈ l₂, tn.α t = tn₂.α t)
    (hs₁ : tn₁.IsActionSeq l₁ as₁) (hs₂ : tn₂.IsActionSeq l₂ as₂) :
    tn.IsActionSeq (l₁ ++ l₂) (as₁ ++ as₂) := by
  have e₁ : l₁.map tn.α = l₁.map tn₁.α := List.map_congr_left hα₁
  have e₂ : l₂.map tn.α = l₂.map tn₂.α := List.map_congr_left hα₂
  have h₁ : l₁.map tn₁.α = as₁.map Sum.inl := hs₁
  have h₂ : l₂.map tn₂.α = as₂.map Sum.inl := hs₂
  simp only [TaskNetwork.IsActionSeq, List.map_append, e₁, e₂, h₁, h₂]

/-! ### Networks with a single task -/

/-- `tn` consists of the single, unordered task `t`. -/
structure IsSingle (tn : TaskNetwork I A C) (t : I) : Prop where
  /-- `t` is the only task of the network. -/
  memT : ∀ x, x ∈ tn.T ↔ x = t
  /-- The ordering is empty. -/
  ord : ∀ a b, ¬ tn.ord a b

namespace IsSingle

variable {tn : TaskNetwork I A C} {t : I}

lemma mem (h : IsSingle tn t) : t ∈ tn.T := (h.memT t).2 rfl

lemma wf (h : IsSingle tn t) : tn.WF where
  mem_left := fun hab => absurd hab (h.ord _ _)
  mem_right := fun hab => absurd hab (h.ord _ _)
  irrefl := fun a => h.ord a a
  trans := fun hab => absurd hab (h.ord _ _)

/-- The only linearization of a one-task network is the singleton list. -/
lemma isLinearization_iff (h : IsSingle tn t) {l : List I} :
    tn.IsLinearization l ↔ l = [t] := by
  constructor
  · rintro ⟨hnodup, hmem, -⟩
    have hall : ∀ x ∈ l, x = t := fun x hx => (h.memT x).1 ((hmem x).1 hx)
    have ht : t ∈ l := (hmem t).2 h.mem
    cases l with
    | nil => simp at ht
    | cons a l =>
        have ha : a = t := hall a (by simp)
        subst ha
        cases l with
        | nil => rfl
        | cons b l =>
            have hb : b = a := hall b (by simp)
            subst hb
            simp at hnodup
  · rintro rfl
    refine ⟨by simp, ?_, by simp⟩
    intro x
    simp [h.memT x]

end IsSingle

end TaskNetwork

end HTN
