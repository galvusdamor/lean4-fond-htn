import HtnPlanning.Interleave.InterleaveList
/-!
# Interleavings as schedules

`HTN.InterleaveList ls z` describes an interleaving of the lists `ls` declaratively.  For an
*operational* analysis of a plan of the HTN-AC compilation — an induction along the run in which
one asks, at each action, which component performed it and what the component's remaining run is
— the following equivalent formulation is much more convenient:

`HTN.Sched ls z` — the run `z` is obtained by repeatedly taking the first remaining action of
one of the components `ls`, until all components are exhausted.

`HTN.sched_iff_interleaveList` proves the two descriptions equivalent, so the results about
interleavings (counting, prefixes, prefix sums) and the operational analysis can be combined
freely.
-/

namespace HTN

universe u

variable {α : Type u}

/-- `Sched ls z`: the list `z` is a *schedule* of the components `ls` — at each step the first
remaining action of one component is executed, and at the end every component is exhausted. -/
inductive Sched : List (List α) → List α → Prop
  /-- All components are exhausted. -/
  | nil {ls : List (List α)} (h : ∀ l ∈ ls, l = []) : Sched ls []
  /-- One component performs its first remaining action. -/
  | step {pre post : List (List α)} {a : α} {t : List α} {z : List α}
      (h : Sched (pre ++ t :: post) z) : Sched (pre ++ (a :: t) :: post) (a :: z)

namespace Sched

/-- Inversion: if a schedule is empty, every component is exhausted. -/
lemma forall_nil {ls : List (List α)} (h : Sched ls ([] : List α)) : ∀ l ∈ ls, l = [] := by
  cases h with
  | nil h => exact h

/-- Inversion: the first action of a schedule is the first action of one of the components. -/
lemma exists_of_cons {ls : List (List α)} {a : α} {z : List α} (h : Sched ls (a :: z)) :
    ∃ (pre post : List (List α)) (t : List α),
      ls = pre ++ (a :: t) :: post ∧ Sched (pre ++ t :: post) z := by
  cases h with
  | @step pre post b t z h => exact ⟨pre, post, t, rfl, h⟩

end Sched

/-- Inserting an action at the head of one component inserts it at the head of the
interleaving. -/
lemma InterleaveList.cons_component :
    ∀ {pre : List (List α)} {post : List (List α)} {t : List α} {a : α} {z : List α},
      InterleaveList (pre ++ t :: post) z → InterleaveList (pre ++ (a :: t) :: post) (a :: z) := by
  intro pre
  induction pre with
  | nil =>
      intro post t a z h
      simp only [List.nil_append] at h ⊢
      cases h with
      | cons hrest hint => exact InterleaveList.cons hrest (Interleave.left a hint)
  | cons l pre ih =>
      intro post t a z h
      simp only [List.cons_append] at h ⊢
      cases h with
      | cons hrest hint =>
          exact InterleaveList.cons (ih hrest) (Interleave.right a hint)

/-- **Schedules and interleavings describe the same runs.** -/
theorem sched_iff_interleaveList {ls : List (List α)} {z : List α} :
    Sched ls z ↔ InterleaveList ls z := by
  constructor
  · intro h
    induction h with
    | nil h => exact InterleaveList.of_forall_nil h
    | step _ ih => exact InterleaveList.cons_component ih
  · intro h
    induction h with
    | nil => exact Sched.nil (by simp)
    | @cons as bs cs ls hrest hint ih =>
        -- `ih : Sched ls bs`; insert the actions of `as` into the schedule
        clear hrest
        induction hint generalizing ls with
        | nil => exact Sched.nil (fun l hl => by
            rcases List.mem_cons.1 hl with rfl | hl
            · rfl
            · exact ih.forall_nil l hl)
        | @left xs ys zs a _ ihint =>
            exact Sched.step (pre := []) (ihint ih)
        | @right xs ys zs a _ ihint =>
            obtain ⟨pre, post, t, rfl, hs⟩ := ih.exists_of_cons
            exact Sched.step (pre := xs :: pre) (ihint hs)

/-! ### Cutting a schedule in two -/

/-- **A point of a schedule cuts every component in two.**  If the run `p ++ z` is a schedule of
the components `ls`, then each component `l` splits as `l = u ++ v` into the part `u` executed
before the cut and the part `v` executed after it, the executed parts interleave to `p` and the
remaining parts schedule `z`. -/
theorem Sched.split : ∀ {ls : List (List α)} {p z : List α}, Sched ls (p ++ z) →
    ∃ ws : List (List α × List α),
      ls = ws.map (fun w => w.1 ++ w.2) ∧
        InterleaveList (ws.map Prod.fst) p ∧ Sched (ws.map Prod.snd) z := by
  intro ls p
  induction p generalizing ls with
  | nil =>
      intro z h
      refine ⟨ls.map (fun l => ([], l)), by simp [List.map_map, Function.comp_def], ?_,
        by simpa using h⟩
      refine InterleaveList.of_forall_nil ?_
      intro l hl
      simp only [List.map_map, List.mem_map, Function.comp_apply] at hl
      obtain ⟨l', -, rfl⟩ := hl
      rfl
  | cons a p ih =>
      intro z h
      rw [List.cons_append] at h
      obtain ⟨pre, post, t, hls, hs⟩ := h.exists_of_cons
      obtain ⟨ws, hws, hint, hsch⟩ := ih hs
      -- split `ws` at the component that performed `a`
      obtain ⟨w₁, w', hw, hw₁, hw'⟩ := List.map_eq_append_iff.1 hws.symm
      obtain ⟨⟨u, v⟩, w₂, hw'eq, huv, hw₂⟩ := List.map_eq_cons_iff.1 hw'
      subst hw
      subst hw'eq
      refine ⟨w₁ ++ (a :: u, v) :: w₂, ?_, ?_, ?_⟩
      · rw [hls]
        simp only [List.map_append, List.map_cons, hw₁, hw₂]
        simp [← huv]
      · simp only [List.map_append, List.map_cons] at hint ⊢
        exact InterleaveList.cons_component hint
      · simpa using hsch

/-- The same cut, stated for interleavings. -/
theorem InterleaveList.split {ls : List (List α)} {p z : List α}
    (h : InterleaveList ls (p ++ z)) :
    ∃ ws : List (List α × List α),
      ls = ws.map (fun w => w.1 ++ w.2) ∧
        InterleaveList (ws.map Prod.fst) p ∧ InterleaveList (ws.map Prod.snd) z := by
  obtain ⟨ws, hws, hint, hsch⟩ := (sched_iff_interleaveList.2 h).split
  exact ⟨ws, hws, hint, sched_iff_interleaveList.1 hsch⟩

end HTN
