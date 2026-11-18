import HtnComplexity.Computable.MergeRun
/-!
# The instance problem of the merge domain is the merge problem

`HtnComplexity/Computable/MergeDom.lean` describes the solutions of the instance
`HTN.Merge.mergeInst ws z` as the interleavings of the write chains of the words `ws` against
the read chain of the word `z`, and `HtnComplexity/Computable/MergeRun.lean` describes the
executable sequences of the fixed domain as the alternations of writes and matching reads.  This
file puts the two together:

    HTN.Merge.solvable_mergeInst_iff :
      HTN.Syn.Solvable mergeDom (mergeInst ws z) ↔ HTN.InterleaveList ws z

— the instance problem of the *single* domain description `mergeDom` is exactly the **merge
problem**: is the word `z` an interleaving (a shuffle) of the words `ws`?

The first half of the file collects the list lemmas the argument needs: an interleaving is
filtered and mapped branchwise, an element of an interleaving comes from a branch, an empty
branch may be dropped, and a single non-empty branch is the whole interleaving.
-/

namespace HTN

namespace Merge

open Syn

/-! ### Interleavings, branchwise -/

universe u

variable {α β : Type u}

/-- Filtering an interleaving filters the two parts. -/
theorem interleave_filter_map {p : α → Bool} {xs ys zs : List α} (h : Interleave xs ys zs) :
    Interleave (xs.filter p) (ys.filter p) (zs.filter p) := by
  induction h with
  | nil => exact Interleave.nil
  | @left xs ys zs a _ ih =>
      by_cases ha : p a
      · simpa [List.filter_cons, ha] using Interleave.left a ih
      · simpa [List.filter_cons, ha] using ih
  | @right xs ys zs a _ ih =>
      by_cases ha : p a
      · simpa [List.filter_cons, ha] using Interleave.right a ih
      · simpa [List.filter_cons, ha] using ih

/-- Inversion for an interleaving of a non-empty list of branches. -/
theorem interleaveList_cons_iff {l : List α} {ls : List (List α)} {z : List α} :
    InterleaveList (l :: ls) z ↔ ∃ bs, InterleaveList ls bs ∧ Interleave l bs z := by
  constructor
  · intro h
    cases h with
    | cons h hint => exact ⟨_, h, hint⟩
  · rintro ⟨bs, h, hint⟩
    exact InterleaveList.cons h hint

/-- **Filtering an interleaving filters every branch.** -/
theorem interleaveList_filter {p : α → Bool} : ∀ {ls : List (List α)} {z : List α},
    InterleaveList ls z → InterleaveList (ls.map (List.filter p)) (z.filter p) := by
  intro ls
  induction ls with
  | nil =>
      intro z h
      cases h
      exact InterleaveList.nil
  | cons l ls ih =>
      intro z h
      obtain ⟨bs, hbs, hint⟩ := interleaveList_cons_iff.1 h
      exact InterleaveList.cons (ih hbs) (interleave_filter_map hint)

/-- **Mapping an interleaving maps every branch.** -/
theorem interleaveList_map {f : α → β} : ∀ {ls : List (List α)} {z : List α},
    InterleaveList ls z → InterleaveList (ls.map (List.map f)) (z.map f) := by
  intro ls
  induction ls with
  | nil =>
      intro z h
      cases h
      exact InterleaveList.nil
  | cons l ls ih =>
      intro z h
      obtain ⟨bs, hbs, hint⟩ := interleaveList_cons_iff.1 h
      exact InterleaveList.cons (ih hbs) (hint.map f)

/-- **An element of an interleaving lies in one of the branches.** -/
theorem interleaveList_mem : ∀ {ls : List (List α)} {z : List α} {a : α},
    InterleaveList ls z → a ∈ z → ∃ l ∈ ls, a ∈ l := by
  intro ls
  induction ls with
  | nil =>
      intro z a h ha
      cases h
      simp at ha
  | cons l ls ih =>
      intro z a h ha
      obtain ⟨bs, hbs, hint⟩ := interleaveList_cons_iff.1 h
      rcases hint.mem_iff.1 ha with hl | hb
      · exact ⟨l, by simp, hl⟩
      · obtain ⟨l', hl', ha'⟩ := ih hbs hb
        exact ⟨l', by simp [hl'], ha'⟩

/-- **An empty branch may be dropped.** -/
theorem interleaveList_append_nil : ∀ {ls : List (List α)} {z : List α},
    InterleaveList (ls ++ [[]]) z → InterleaveList ls z := by
  intro ls
  induction ls with
  | nil =>
      intro z h
      obtain ⟨bs, hbs, hint⟩ := interleaveList_cons_iff.1 h
      cases hbs
      rw [hint.eq_of_nil_left]
      exact InterleaveList.nil
  | cons l ls ih =>
      intro z h
      obtain ⟨bs, hbs, hint⟩ := interleaveList_cons_iff.1 h
      exact InterleaveList.cons (ih hbs) hint

/-- **An interleaving of empty branches and one further branch is that branch.** -/
theorem interleaveList_nils_append : ∀ {ls : List (List α)} {u z : List α},
    (∀ l ∈ ls, l = []) → InterleaveList (ls ++ [u]) z → z = u := by
  intro ls
  induction ls with
  | nil =>
      intro u z _ h
      obtain ⟨bs, hbs, hint⟩ := interleaveList_cons_iff.1 h
      cases hbs
      exact hint.eq_of_nil_right
  | cons l ls ih =>
      intro u z hnil h
      obtain ⟨bs, hbs, hint⟩ := interleaveList_cons_iff.1 h
      rw [hnil l (by simp)] at hint
      rw [hint.eq_of_nil_left]
      exact ih (fun l' hl' => hnil l' (by simp [hl'])) hbs

/-! ### Decoding the alphabet -/

/-- The bit an action carries: both the write and the read of the bit `b` decode to `b`. -/
def dec (x : ℕ) : Bool := decide (x % 2 = 1)

@[simp] theorem dec_aName (b : Bool) : dec (aName b) = b := by cases b <;> simp [dec, aName]

@[simp] theorem dec_bName (b : Bool) : dec (bName b) = b := by cases b <;> simp [dec, bName]

@[simp] theorem map_dec_aWord (w : List Bool) : (aWord w).map dec = w := by
  simp [aWord, List.map_map, Function.comp_def]

@[simp] theorem map_dec_bWord (w : List Bool) : (bWord w).map dec = w := by
  simp [bWord, List.map_map, Function.comp_def]

/-- The predicate that distinguishes a write from a read. -/
def isWrite (x : ℕ) : Bool := decide (x < 2)

@[simp] theorem isWrite_aName (b : Bool) : isWrite (aName b) = true := by
  simp [isWrite, aName_lt_two]

@[simp] theorem isWrite_bName (b : Bool) : isWrite (bName b) = false := by
  have := two_le_bName b
  simp [isWrite]
  omega

@[simp] theorem filter_isWrite_aWord (w : List Bool) : (aWord w).filter isWrite = aWord w := by
  refine List.filter_eq_self.2 fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  simp

@[simp] theorem filter_isWrite_bWord (w : List Bool) : (bWord w).filter isWrite = [] := by
  refine List.filter_eq_nil_iff.2 fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  simp

@[simp] theorem filter_not_isWrite_aWord (w : List Bool) :
    (aWord w).filter (fun x => !isWrite x) = [] := by
  refine List.filter_eq_nil_iff.2 fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  simp

@[simp] theorem filter_not_isWrite_bWord (w : List Bool) :
    (bWord w).filter (fun x => !isWrite x) = bWord w := by
  refine List.filter_eq_self.2 fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  simp

@[simp] theorem filter_isWrite_pairsOf (cs : List Bool) :
    (pairsOf cs).filter isWrite = aWord cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [pairsOf_cons, ih, aWord]

@[simp] theorem filter_not_isWrite_pairsOf (cs : List Bool) :
    (pairsOf cs).filter (fun x => !isWrite x) = bWord cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [pairsOf_cons, ih, bWord]

/-! ### The actions occurring in a plan -/

theorem lt_four_of_mem_letters {ws : List (List Bool)} {z : List Bool} {x : ℕ}
    (h : ∃ l ∈ letters ws z, x ∈ l) : x < 4 := by
  obtain ⟨l, hl, hx⟩ := h
  rw [letters, List.mem_append] at hl
  rcases hl with hl | hl
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    have := aName_lt_two b
    omega
  · rw [List.mem_singleton] at hl
    subst hl
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    cases b <;> simp [bName]

/-- The plan of the backward direction: the writes of `z` interleaved with its reads. -/
theorem interleave_aWord_bWord (z : List Bool) :
    Interleave (aWord z) (bWord z) (pairsOf z) := by
  induction z with
  | nil => exact Interleave.nil
  | cons c cs ih => exact Interleave.left (aName c) (Interleave.right (bName c) ih)

/-! ### The theorem -/

theorem map_filter_isWrite_letters (ws : List (List Bool)) (z : List Bool) :
    (letters ws z).map (List.filter isWrite) = ws.map aWord ++ [[]] := by
  simp [letters, List.map_append, List.map_map, Function.comp_def]

theorem map_filter_not_isWrite_letters (ws : List (List Bool)) (z : List Bool) :
    (letters ws z).map (List.filter fun x => !isWrite x) =
      ws.map (fun _ => []) ++ [bWord z] := by
  simp [letters, List.map_append, List.map_map, Function.comp_def]

/-- **The instance problem of the fixed domain description `mergeDom` is the merge problem.**
The instance `mergeInst ws z` is solvable exactly when the word `z` is an interleaving — a
shuffle — of the words `ws`. -/
theorem solvable_mergeInst_iff (ws : List (List Bool)) (z : List Bool) :
    Syn.Solvable mergeDom (mergeInst ws z) ↔ InterleaveList ws z := by
  rw [solvable_mergeInst_iff_interleave]
  constructor
  · rintro ⟨as, hint, happ, hgoal⟩
    rw [sE_eq] at happ hgoal
    have hmem4 : ∀ x ∈ as, x < 4 := fun x hx =>
      lt_four_of_mem_letters (interleaveList_mem hint hx)
    obtain ⟨cs, rfl⟩ := exists_pairsOf_of_exec hmem4 happ hgoal
    -- the writes: `cs` is an interleaving of the `ws`
    have hA : InterleaveList (ws.map aWord) (aWord cs) := by
      have := interleaveList_filter (p := isWrite) hint
      rw [map_filter_isWrite_letters, filter_isWrite_pairsOf] at this
      exact interleaveList_append_nil this
    have hA' : InterleaveList ws cs := by
      have := interleaveList_map (f := dec) hA
      simpa [List.map_map, Function.comp_def] using this
    -- the reads: `z` is `cs`
    have hB : bWord cs = bWord z := by
      have := interleaveList_filter (p := fun x => !isWrite x) hint
      rw [map_filter_not_isWrite_letters, filter_not_isWrite_pairsOf] at this
      exact interleaveList_nils_append (by simp) this
    have hz : z = cs := by
      have := congrArg (List.map dec) hB
      simpa using this.symm
    rwa [hz]
  · intro h
    refine ⟨pairsOf z, ?_, ?_, ?_⟩
    · -- the plan is an interleaving of the branches
      have hA : InterleaveList (ws.map aWord) (aWord z) := by
        have := interleaveList_map (f := aName) h
        simpa [aWord] using this
      have hlast : InterleaveList [bWord z] (bWord z) :=
        InterleaveList.cons InterleaveList.nil (Interleave.nil_right _)
      exact InterleaveList.append hA hlast (interleave_aWord_bWord z)
    · rw [sE_eq]
      exact (exec_pairsOf z).1
    · rw [sE_eq, (exec_pairsOf z).2]

/-! ### The family is not degenerate

Both answers occur: `[true, false]` is a shuffle of `[true]` and `[false]`, and `[false]` is not
a shuffle of `[true]`. -/

example : Syn.Solvable mergeDom (mergeInst [[true], [false]] [true, false]) := by
  rw [solvable_mergeInst_iff]
  exact InterleaveList.cons
    (InterleaveList.cons InterleaveList.nil (Interleave.left false Interleave.nil))
    (Interleave.left true (Interleave.right false Interleave.nil))

example : ¬ Syn.Solvable mergeDom (mergeInst [[true]] [false]) := by
  rw [solvable_mergeInst_iff]
  intro h
  cases h with
  | cons h hint =>
      cases hint with
      | right _ h' => cases h'

end Merge

end HTN
