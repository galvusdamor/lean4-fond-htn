import HtnComplexity.Computable.TokTarget
/-!
# The token gadget: the states of the compiled description

This file computes the action model of the compiled description
(`HtnComplexity/Computable/TokDom.lean`) and simulates the execution of one block.

While the block of the source method number `i` is being executed the compiled state is
`HTN.Syn.midState d q i s ys`: the encoded source state reached by the subtasks `ys` executed so
far, a token for every primitive subtask not yet executed, and a done-mark for every subtask
already executed.  The three kinds of compiled action move through these states:

* `HTN.Syn.transition_strtA` — `strt i` turns the clean state `stateF '' s` into `midState … []`;
* `HTN.Syn.applicable_doA`, `HTN.Syn.transition_doA` — `doA (i,x)` is applicable exactly when
  `x` has not been executed, all subtasks ordered before it have been, and the source action is
  applicable, and it moves to `midState … (ys ++ [x])`;
* `HTN.Syn.applicable_finA`, `HTN.Syn.transition_finA` — `fin i` is applicable exactly when
  every primitive subtask has been executed, and returns to a clean state.

`HTN.Syn.seqApplicable_doList` puts the middle part together: the executable sequences of
`doA` actions are exactly the enumerations of the primitive part that respect the ordering and
whose source action sequence is applicable.
-/

namespace HTN

namespace Syn

variable {d : DomDesc} {q q' : InstDesc}

/-! ### Looking up a compiled action -/

/-- A lookup succeeds at a key that occurs, with a value that is unique for that key. -/
theorem lookup_eq_of_mem_of_unique {β : Type} {l : List (ℕ × β)} {a : ℕ} {b : β}
    (hmem : (a, b) ∈ l) (huniq : ∀ b', (a, b') ∈ l → b' = b) : l.lookup a = some b := by
  induction l with
  | nil => simp at hmem
  | cons p ps ih =>
      rw [show p = (p.1, p.2) from rfl, List.lookup_cons]
      by_cases hk : a = p.1
      · have hv : p.2 = b := by
          refine huniq p.2 ?_
          rw [hk]
          simp
        simp [hk, hv]
      · have hb : (a == p.1) = false := by simp [hk]
        rw [hb]
        refine ih ?_ ?_
        · rcases List.mem_cons.1 hmem with h | h
          · exact absurd (congrArg Prod.fst h) hk
          · exact h
        · exact fun b' hb' => huniq b' (List.mem_cons_of_mem _ hb')

theorem mem_tokActions_iff {p : ActionDesc} :
    p ∈ (tokDom d).actions ↔ ∃ j, j < d.methods.length ∧ p ∈ tokActionsOf d j := by
  simp only [tokDom, DomDesc.actions, List.mem_flatMap, List.mem_range]

theorem mem_tokActionsOf_iff {j : ℕ} {p : ActionDesc} :
    p ∈ tokActionsOf d j ↔
      p = (strtA j, [], (pOf d j).map (tokF j), []) ∨
      (∃ x ∈ pOf d j, p = (doA j x, doPre d j x, doAdd d j x, doDel d j x)) ∨
      p = (finA j, (pOf d j).map (donF j), [], (pOf d j).map (donF j)) := by
  simp only [tokActionsOf, List.mem_cons, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false]
  constructor
  · rintro ((h | ⟨x, hx, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨x, hx, h.symm⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨x, hx, h⟩ | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨x, hx, h.symm⟩)
    · exact Or.inr h

theorem lookup_strtA {i : ℕ} (hi : i < d.methods.length) :
    (tokDom d).actions.lookup (strtA i) = some ([], (pOf d i).map (tokF i), []) := by
  refine lookup_eq_of_mem_of_unique
    (mem_tokActions_iff.2 ⟨i, hi, mem_tokActionsOf_iff.2 (Or.inl rfl)⟩) ?_
  intro b' hb'
  obtain ⟨j, -, hmem⟩ := mem_tokActions_iff.1 hb'
  rcases mem_tokActionsOf_iff.1 hmem with h | ⟨x, -, h⟩ | h <;>
    simp only [Prod.mk.injEq] at h
  · obtain ⟨h1, h2⟩ := h
    rw [strtA_inj.1 h1]
    exact h2
  · exact absurd h.1 strtA_ne_doA
  · exact absurd h.1 strtA_ne_finA

theorem lookup_doA {i x : ℕ} (hi : i < d.methods.length) (hx : x ∈ pOf d i) :
    (tokDom d).actions.lookup (doA i x) = some (doPre d i x, doAdd d i x, doDel d i x) := by
  refine lookup_eq_of_mem_of_unique
    (mem_tokActions_iff.2 ⟨i, hi, mem_tokActionsOf_iff.2 (Or.inr (Or.inl ⟨x, hx, rfl⟩))⟩) ?_
  intro b' hb'
  obtain ⟨j, -, hmem⟩ := mem_tokActions_iff.1 hb'
  rcases mem_tokActionsOf_iff.1 hmem with h | ⟨y, -, h⟩ | h <;>
    simp only [Prod.mk.injEq] at h
  · exact absurd h.1.symm strtA_ne_doA
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, rfl⟩ := doA_inj.1 h1
    exact h2
  · exact absurd h.1 doA_ne_finA

theorem lookup_finA {i : ℕ} (hi : i < d.methods.length) :
    (tokDom d).actions.lookup (finA i) =
      some ((pOf d i).map (donF i), [], (pOf d i).map (donF i)) := by
  refine lookup_eq_of_mem_of_unique
    (mem_tokActions_iff.2 ⟨i, hi, mem_tokActionsOf_iff.2 (Or.inr (Or.inr rfl))⟩) ?_
  intro b' hb'
  obtain ⟨j, -, hmem⟩ := mem_tokActions_iff.1 hb'
  rcases mem_tokActionsOf_iff.1 hmem with h | ⟨y, -, h⟩ | h <;>
    simp only [Prod.mk.injEq] at h
  · exact absurd h.1.symm strtA_ne_finA
  · exact absurd h.1.symm doA_ne_finA
  · obtain ⟨h1, h2⟩ := h
    rw [finA_inj.1 h1]
    exact h2

/-! ### The compiled precondition, add and delete lists -/

theorem prec_strtA {i : ℕ} (hi : i < d.methods.length) :
    (problem (tokDom d) q').prec (strtA i) = {f | f ∈ ([] : List ℕ)} := by
  simp [DomDesc.prec, lookup_strtA hi]

theorem add_strtA {i : ℕ} (hi : i < d.methods.length) :
    (problem (tokDom d) q').add (strtA i) = {f | f ∈ (pOf d i).map (tokF i)} := by
  simp [DomDesc.add, lookup_strtA hi]

theorem del_strtA {i : ℕ} (hi : i < d.methods.length) :
    (problem (tokDom d) q').del (strtA i) = {f | f ∈ ([] : List ℕ)} := by
  simp [DomDesc.del, lookup_strtA hi]

theorem prec_doA {i x : ℕ} (hi : i < d.methods.length) (hx : x ∈ pOf d i) :
    (problem (tokDom d) q').prec (doA i x) = {f | f ∈ doPre d i x} := by
  simp [DomDesc.prec, lookup_doA hi hx]

theorem add_doA {i x : ℕ} (hi : i < d.methods.length) (hx : x ∈ pOf d i) :
    (problem (tokDom d) q').add (doA i x) = {f | f ∈ doAdd d i x} := by
  simp [DomDesc.add, lookup_doA hi hx]

theorem del_doA {i x : ℕ} (hi : i < d.methods.length) (hx : x ∈ pOf d i) :
    (problem (tokDom d) q').del (doA i x) = {f | f ∈ doDel d i x} := by
  simp [DomDesc.del, lookup_doA hi hx]

theorem prec_finA {i : ℕ} (hi : i < d.methods.length) :
    (problem (tokDom d) q').prec (finA i) = {f | f ∈ (pOf d i).map (donF i)} := by
  simp [DomDesc.prec, lookup_finA hi]

theorem add_finA {i : ℕ} (hi : i < d.methods.length) :
    (problem (tokDom d) q').add (finA i) = {f | f ∈ ([] : List ℕ)} := by
  simp [DomDesc.add, lookup_finA hi]

theorem del_finA {i : ℕ} (hi : i < d.methods.length) :
    (problem (tokDom d) q').del (finA i) = {f | f ∈ (pOf d i).map (donF i)} := by
  simp [DomDesc.del, lookup_finA hi]

/-! ### The states of the compiled problem -/

/-- The source state reached by executing the subtasks `ys` of the method number `i`. -/
def srcRun (d : DomDesc) (q : InstDesc) (i : ℕ) (s : Set ℕ) (ys : List ℕ) : Set ℕ :=
  (problem d q).transitionSeq (ys.map (TnDesc.actOf (tOf d i))) s

/-- The compiled state while the block of the method number `i` is being executed. -/
def midState (d : DomDesc) (q : InstDesc) (i : ℕ) (s : Set ℕ) (ys : List ℕ) : Set ℕ :=
  stateF '' srcRun d q i s ys ∪ tokF i '' {x | x ∈ pOf d i ∧ x ∉ ys} ∪ donF i '' {x | x ∈ ys}

@[simp] theorem srcRun_nil (i : ℕ) (s : Set ℕ) : srcRun d q i s [] = s := rfl

theorem srcRun_append (i : ℕ) (s : Set ℕ) (ys : List ℕ) (x : ℕ) :
    srcRun d q i s (ys ++ [x]) =
      (problem d q).transition (TnDesc.actOf (tOf d i) x) (srcRun d q i s ys) := by
  simp only [srcRun, List.map_append, List.map_cons, List.map_nil]
  rw [ActionModel.transitionSeq_append]
  rfl

@[simp] theorem stateF_mem_midState {i v : ℕ} {s : Set ℕ} {ys : List ℕ} :
    stateF v ∈ midState d q i s ys ↔ v ∈ srcRun d q i s ys := by
  simp [midState]

@[simp] theorem tokF_mem_midState {i j x : ℕ} {s : Set ℕ} {ys : List ℕ} :
    tokF j x ∈ midState d q i s ys ↔ (j = i ∧ x ∈ pOf d i ∧ x ∉ ys) := by
  constructor
  · intro h
    rcases h with (h | h) | h
    · obtain ⟨v, -, hv⟩ := h
      exact absurd hv.symm tokF_ne_stateF
    · obtain ⟨y, hy, hv⟩ := h
      obtain ⟨rfl, rfl⟩ := tokF_inj.1 hv.symm
      exact ⟨rfl, hy⟩
    · obtain ⟨y, -, hv⟩ := h
      exact absurd hv donF_ne_tokF
  · rintro ⟨rfl, hx⟩
    exact Or.inl (Or.inr ⟨x, hx, rfl⟩)

@[simp] theorem donF_mem_midState {i j x : ℕ} {s : Set ℕ} {ys : List ℕ} :
    donF j x ∈ midState d q i s ys ↔ (j = i ∧ x ∈ ys) := by
  constructor
  · intro h
    rcases h with (h | h) | h
    · obtain ⟨v, -, hv⟩ := h
      exact absurd hv.symm donF_ne_stateF
    · obtain ⟨y, -, hv⟩ := h
      exact absurd hv.symm donF_ne_tokF
    · obtain ⟨y, hy, hv⟩ := h
      obtain ⟨rfl, rfl⟩ := donF_inj.1 hv.symm
      exact ⟨rfl, hy⟩
  · rintro ⟨rfl, hx⟩
    exact Or.inr ⟨x, hx, rfl⟩

@[simp] theorem stateF_mem_image {v : ℕ} {s : Set ℕ} : stateF v ∈ stateF '' s ↔ v ∈ s := by
  simp

@[simp] theorem tokF_not_mem_image {i x : ℕ} {s : Set ℕ} : tokF i x ∉ stateF '' s := by
  rintro ⟨v, -, hv⟩
  exact tokF_ne_stateF hv.symm

@[simp] theorem donF_not_mem_image {i x : ℕ} {s : Set ℕ} : donF i x ∉ stateF '' s := by
  rintro ⟨v, -, hv⟩
  exact donF_ne_stateF hv.symm

/-! ### The three kinds of compiled action -/

theorem applicable_strtA {i : ℕ} (hi : i < d.methods.length) (S : Set ℕ) :
    (problem (tokDom d) q').Applicable (strtA i) S := by
  rw [ActionModel.Applicable, prec_strtA hi]
  intro f hf
  simp at hf

theorem transition_strtA {i : ℕ} (hi : i < d.methods.length) (s : Set ℕ) :
    (problem (tokDom d) q').transition (strtA i) (stateF '' s) = midState d q i s [] := by
  rw [ActionModel.transition, del_strtA hi, add_strtA hi]
  ext f
  rcases fact_cases f with ⟨v, rfl⟩ | ⟨j, x, rfl⟩ | ⟨j, x, rfl⟩ <;>
    simp [midState, srcRun]

theorem applicable_doA {i x : ℕ} (hi : i < d.methods.length) (hx : x ∈ pOf d i)
    (s : Set ℕ) (ys : List ℕ) :
    (problem (tokDom d) q').Applicable (doA i x) (midState d q i s ys) ↔
      (x ∉ ys ∧ (∀ y ∈ TnDesc.predsOf (tOf d i) x, y ∈ ys) ∧
        (problem d q).Applicable (TnDesc.actOf (tOf d i) x) (srcRun d q i s ys)) := by
  rw [ActionModel.Applicable, prec_doA hi hx, doPre]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h (a := tokF i x) (by simp)
      simpa using (tokF_mem_midState.1 this).2.2
    · intro y hy
      have := h (a := donF i y) (by simp [hy])
      simpa using (donF_mem_midState.1 this).2
    · intro v hv
      have := h (a := stateF v) (by
        simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map, List.mem_cons]
        exact Or.inr (Or.inr ⟨v, hv, rfl⟩))
      simpa using this
  · rintro ⟨h1, h2, h3⟩ f hf
    simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map, List.mem_cons] at hf
    rcases hf with ⟨y, hy, rfl⟩ | rfl | ⟨v, hv, rfl⟩
    · exact donF_mem_midState.2 ⟨rfl, h2 y hy⟩
    · exact tokF_mem_midState.2 ⟨rfl, hx, h1⟩
    · exact stateF_mem_midState.2 (h3 hv)

theorem transition_doA {i x : ℕ} (hi : i < d.methods.length) (hx : x ∈ pOf d i)
    (s : Set ℕ) (ys : List ℕ) :
    (problem (tokDom d) q').transition (doA i x) (midState d q i s ys) =
      midState d q i s (ys ++ [x]) := by
  rw [ActionModel.transition, del_doA hi hx, add_doA hi hx, doAdd, doDel]
  ext f
  rcases fact_cases f with ⟨v, rfl⟩ | ⟨j, y, rfl⟩ | ⟨j, y, rfl⟩ <;>
    simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.mem_cons, List.mem_map,
      List.mem_append, stateF_mem_midState, tokF_mem_midState,
      donF_mem_midState, srcRun_append, ActionModel.transition, problem_del, problem_add,
      DomDesc.del_eq, DomDesc.add_eq, stateF_ne_tokF, stateF_ne_donF,
      tokF_ne_donF, donF_ne_tokF, stateF_inj, tokF_inj, donF_inj,
      exists_eq_right, false_or, or_false, and_false, exists_false] <;>
    tauto

theorem applicable_finA {i : ℕ} (hi : i < d.methods.length) (s : Set ℕ) (ys : List ℕ) :
    (problem (tokDom d) q').Applicable (finA i) (midState d q i s ys) ↔
      ∀ x ∈ pOf d i, x ∈ ys := by
  rw [ActionModel.Applicable, prec_finA hi]
  constructor
  · intro h x hx
    have := h (a := donF i x) (by simp [hx])
    simpa using (donF_mem_midState.1 this).2
  · rintro h f hf
    simp only [Set.mem_setOf_eq, List.mem_map] at hf
    obtain ⟨x, hx, rfl⟩ := hf
    exact donF_mem_midState.2 ⟨rfl, h x hx⟩

theorem transition_finA {i : ℕ} (hi : i < d.methods.length) (s : Set ℕ) (ys : List ℕ)
    (h : ∀ x ∈ pOf d i, x ∈ ys) (hsub : ∀ y ∈ ys, y ∈ pOf d i) :
    (problem (tokDom d) q').transition (finA i) (midState d q i s ys) =
      stateF '' srcRun d q i s ys := by
  rw [ActionModel.transition, del_finA hi, add_finA hi]
  ext f
  rcases fact_cases f with ⟨v, rfl⟩ | ⟨j, y, rfl⟩ | ⟨j, y, rfl⟩
  · simp
  · simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.mem_map, tokF_mem_midState,
      List.not_mem_nil, or_false, tokF_not_mem_image]
    constructor
    · rintro ⟨⟨rfl, hy1, hy2⟩, -⟩
      exact absurd (h y hy1) hy2
    · intro hc
      exact absurd hc (by simp)
  · simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.mem_map, donF_mem_midState,
      List.not_mem_nil, or_false, donF_not_mem_image]
    constructor
    · rintro ⟨⟨rfl, hy⟩, hnd⟩
      exact absurd ⟨y, by simpa using hsub y hy, rfl⟩ hnd
    · intro hc
      exact absurd hc (by simp)

end Syn

end HTN
