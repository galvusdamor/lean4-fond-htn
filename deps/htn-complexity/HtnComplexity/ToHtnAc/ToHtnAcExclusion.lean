import HtnComplexity.ToHtnAc.ToHtnAcQuiescent
import HtnPlanning.Interleave.Sched
/-!
# At a quiescent point the plan continues with the active proof step

This is the *exclusion lemma* of the soundness half of the correctness of the TO-HTN ⟶ HTN-AC
compilation.  Consider a plan of the compiled problem — an interleaving of the runs of its
memory cells with the runs of its proof steps — and a point `p` of it that is *quiescent*
(`HtnComplexity/ToHtnAc/ToHtnAcQuiescent.lean`): a proof step holds the lock and no handshake is in
progress.  Then the next action of the plan is performed by that proof step:

* no other proof step can move, because it has not started and `lock` needs `key₀`, which the
  active step holds;
* no memory cell can move, because — by the lock-step theorem, through the quiescence
  assumption — every cell stands at a phase boundary, so its next action is an `accept_X`, which
  needs `key₁^X`, and no request is open.

`HTN.ToAc.quiescent_next_action_of_active_step` states this: the next action `a` of the plan is
the next action of a proof step that has taken the lock and not yet released it.

Together with the positioning results of `HtnComplexity/ToHtnAc/ToHtnAcStepSeg.lean` this is what
turns a plan into a sequence of blocks, each of which is one proof step with the memory phases
it talks to spliced in.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {Q : Instance F A C I} {vars : List F}
  {bound : ℕ} {tI0 : C}

open Domain

/-- **At a quiescent point of a plan the next action belongs to the proof step holding the
lock.** -/
theorem quiescent_next_action_of_active_step (hnd : vars.Nodup)
    {γs σs : List (List (AcAct F A C))} {as as₁ as₂ p r : List (AcAct F A C)}
    {a : AcAct F A C}
    (hγ : ∀ γ ∈ γs, (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] γ)
    (hσ : ∀ σ ∈ σs, (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] σ)
    (hcells : InterleaveList γs as₁) (hsteps : InterleaveList σs as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hp : as = p ++ a :: r)
    (hquiet : Quiescent p) :
    ∃ σ ∈ σs, ∃ u t : List (AcAct F A C),
      σ = u ++ a :: t ∧ 1 ≤ u.countP isLock ∧ u.countP isUnlock = 0 := by
  classical
  -- the action `a` is applicable at the point `p`
  have happp : (problem D Q vars bound tI0).SeqApplicable (a :: r)
      ((problem D Q vars bound tI0).transitionSeq p (problem D Q vars bound tI0).init) := by
    rw [hp] at happ
    exact ((ActionModel.seqApplicable_append _ p (a :: r) _).1 happ).2
  have happa : (domain D vars bound).Applicable a
      ((problem D Q vars bound tI0).transitionSeq p (problem D Q vars bound tI0).init) :=
    happp.1
  have happ' : (problem D Q vars bound tI0).SeqApplicable p
      (problem D Q vars bound tI0).init := by
    rw [hp] at happ
    exact ((ActionModel.seqApplicable_append _ p (a :: r) _).1 happ).1
  obtain ⟨hnolock, hnokey⟩ := not_applicable_of_quiescent hquiet happ'
  -- cut the plan at `p`
  have hflat : InterleaveList (γs ++ σs) (p ++ a :: r) := by
    rw [← hp]; exact hcells.append hsteps hint
  obtain ⟨ws, hws, hfst, hsnd⟩ := hflat.split
  -- which component performs `a`?
  obtain ⟨pre, post, t, hmap, -⟩ := (sched_iff_interleaveList.2 hsnd).exists_of_cons
  obtain ⟨ws₁, w', hwseq, -, hw'⟩ := List.map_eq_append_iff.1 hmap
  obtain ⟨w, ws₂, hw'eq, hw2, -⟩ := List.map_eq_cons_iff.1 hw'
  subst hwseq
  subst hw'eq
  have hwmem : w ∈ ws₁ ++ w :: ws₂ := by simp
  -- every component is a memory cell or a proof step
  have hcomp : ∀ w' ∈ ws₁ ++ w :: ws₂,
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] (w'.1 ++ w'.2) ∨
        (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)]
          (w'.1 ++ w'.2) := by
    intro w' hw'
    have hm : w'.1 ++ w'.2 ∈ γs ++ σs := by
      rw [hws]; exact List.mem_map_of_mem hw'
    rcases List.mem_append.1 hm with h | h
    · exact Or.inl (hγ _ h)
    · exact Or.inr (hσ _ h)
  -- counting is additive over the executed parts
  have hsum : ∀ q : AcAct F A C → Bool,
      p.countP q = ((ws₁ ++ w :: ws₂).map (fun w' => w'.1.countP q)).sum := by
    intro q
    rw [hfst.countP q, List.map_map]
    rfl
  -- no cell is inside a phase
  have hmono : ∀ x : RW, ∀ w' ∈ ws₁ ++ w :: ws₂,
      w'.1.countP (isDone x) ≤ w'.1.countP (isAccept x) := by
    intro x w' hw'
    rcases hcomp w' hw' with h | h
    · have h0 := ((psumNonneg_cellW hnd x h).of_prefix ⟨w'.2, rfl⟩).total
      rw [wsum_cellW] at h0
      omega
    · obtain ⟨r₀, w₀, -, -, -, e⟩ := countP_yieldSeq_TUPLE h
      have h₁ : (w'.1 ++ w'.2).countP (isDone x) = 0 := by
        rw [e _ (handshakePred_isDone x)]; rcases x with _ | _ <;> simp [isDone]
      have c₁ : w'.1.countP (isDone x) ≤ (w'.1 ++ w'.2).countP (isDone x) :=
        (List.IsPrefix.sublist ⟨w'.2, rfl⟩).countP_le
      omega
  have hcellwise : ∀ x : RW, ∀ w' ∈ ws₁ ++ w :: ws₂,
      w'.1.countP (isAccept x) = w'.1.countP (isDone x) := by
    intro x
    refine eq_of_sum_le_sum (fun w' : List (AcAct F A C) × List (AcAct F A C) =>
        w'.1.countP (isAccept x))
      (fun w' : List (AcAct F A C) × List (AcAct F A C) => w'.1.countP (isDone x))
      (ws₁ ++ w :: ws₂) (hmono x) ?_
    have h1 := hsum (isAccept x)
    have h2 := hsum (isDone x)
    have h3 := (hquiet.2 x).2.1
    omega
  -- the component that performs `a`
  have hmemw : w.1 ++ w.2 ∈ γs ++ σs := by
    rw [hws]; exact List.mem_map_of_mem hwmem
  rcases List.mem_append.1 hmemw with hcell | hstep
  · -- a memory cell: it stands at a phase boundary, so its next action is an `accept`
    exfalso
    obtain ⟨S, S', tt, hphases⟩ := yieldSeq_MEM_phases hnd (hγ _ hcell)
    have hpre : w.1 <+: memWrite S S' tt vars ++ memRead S S' tt vars := by
      rw [← hphases]; exact ⟨w.2, rfl⟩
    have hW := hcellwise RW.write w hwmem
    have hR := hcellwise RW.read w hwmem
    by_cases hw0 : w.1.countP (isAccept RW.write) = 0
    · -- the cell has not moved: its next action is `accept_W`
      have hnil : w.1 = [] := cell_eq_nil_of_countP_accept_write hpre hw0
      have hrest : a :: t = memWrite S S' tt vars ++ memRead S S' tt vars := by
        rw [← hw2, ← hphases, hnil]; simp
      have ha : a = AcAct.accept RW.write := by
        rw [memWrite, List.cons_append] at hrest
        exact (List.cons_eq_cons.1 hrest).1
      exact (hnokey RW.write).1 (ha ▸ happa)
    · by_cases hr0 : w.1.countP (isAccept RW.read) = 0
      · -- the cell has latched its triple: its next action is `accept_R`
        have hu : w.1 = memWrite S S' tt vars :=
          cell_eq_memWrite_of_counts hpre (by omega) hr0
        have h2 : w.2 = memRead S S' tt vars := by
          have h := hphases
          rw [hu] at h
          exact List.append_cancel_left h
        rw [hw2] at h2
        have ha : a = AcAct.accept RW.read := by
          rw [memRead] at h2
          exact (List.cons_eq_cons.1 h2).1
        exact (hnokey RW.read).1 (ha ▸ happa)
      · -- the cell has finished: it has no next action
        have hu : w.1 = memWrite S S' tt vars ++ memRead S S' tt vars :=
          cell_eq_run_of_countP_done_read hpre (by omega)
        have h2 : w.2 = [] := by
          have h := hphases
          rw [hu] at h
          have h' : (memWrite S S' tt vars ++ memRead S S' tt vars) ++ w.2 =
              (memWrite S S' tt vars ++ memRead S S' tt vars) ++ [] := by simpa using h
          exact List.append_cancel_left h'
        rw [hw2] at h2
        simp at h2
  · -- a proof step: it has taken the lock and not released it
    have hne : w.1 ≠ [] := by
      intro hnil
      obtain ⟨t', ht'⟩ := yieldSeq_TUPLE_head (hσ _ hstep)
      rw [hnil, List.nil_append, hw2] at ht'
      have ha : a = AcAct.lock := (List.cons_eq_cons.1 ht').1
      exact hnolock (ha ▸ happa)
    have hlt : w.1 ≠ w.1 ++ w.2 := by
      intro hc
      have h2 : w.2 = [] := by
        have hcc : w.1 ++ [] = w.1 ++ w.2 := by simpa using hc
        exact (List.append_cancel_left hcc).symm
      rw [hw2] at h2
      simp at h2
    obtain ⟨h₁, h₂⟩ := step_countP_lock_pos_of_ne_nil (hσ _ hstep) ⟨w.2, rfl⟩ hne hlt
    exact ⟨w.1 ++ w.2, hstep, w.1, t, by rw [hw2], h₁, h₂⟩

end ToAc

end HTN
