import HtnPlanning.Interleave.InterleaveList
import HtnComplexity.ToHtnAc.ToHtnAcSyncCount
import HtnComplexity.ToHtnAc.ToHtnAcTupleShape
/-!
# The proof steps of a plan of the HTN-AC compilation are mutually exclusive

A plan of the compiled problem of `HtnComplexity/ToHtnAc/ToHtnAc.lean` is an arbitrary interleaving
of the runs of the parallel memory cells with the runs of the parallel proof steps
(`HTN.ToAc.netYield_tnI_iff`).  For the *soundness* half of the correctness of the compilation —
from a plan build a derivation of the proof-tuple calculus — the first thing that has to be
established is that this freedom is only apparent: the `lock` at the beginning and the `unlock`
at the end of a proof step, together with the semaphore invariant for `key₀`
(`HTN.ToAc.countP_lock_le_countP_unlock_succ`), force the proof steps to run one after the other.

This file proves exactly that, in the form that the global argument needs:

`HTN.ToAc.at_most_one_tuple_in_progress` — at every point of an executable plan, at most one
proof step has begun and not yet ended.

The ingredients are the prefix decomposition of an interleaving
(`HTN.InterleaveList.exists_prefix`), which lets the counting invariants be evaluated part by
part, and the fact that a memory cell contains no `lock` and no `unlock` while a proof step
contains exactly one of each, at its very beginning and at its very end.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### Parallel copies as an interleaving of a list of runs -/

/-- **A refinement of `m` parallel copies of a sequential task is an interleaving of `m`
refinements of it.** -/
theorem exists_interleaveList_of_gridYield_replicate {c : AcTask F A C} (hc : IsSeqTask c) :
    ∀ (m : ℕ) {as : List (AcAct F A C)},
      (domain D vars bound).GridYield (List.replicate m [Sum.inr c]) as →
      ∃ ls : List (List (AcAct F A C)), ls.length = m ∧
        (∀ l ∈ ls, (domain D vars bound).YieldSeq [Sum.inr c] l) ∧ InterleaveList ls as := by
  intro m
  induction m with
  | zero =>
      intro as h
      rw [gridYield_replicate_zero] at h
      exact ⟨[], rfl, by simp, h ▸ InterleaveList.nil⟩
  | succ m ih =>
      intro as h
      obtain ⟨u, v, hu, hv, hint⟩ := (gridYield_replicate_succ hc).1 h
      obtain ⟨ls, hlen, hall, hIL⟩ := ih hv
      refine ⟨u :: ls, by simp [hlen], ?_, InterleaveList.cons hIL hint⟩
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hu
      · exact hall l hl

/-! ### Locks and unlocks in the two kinds of run -/

/-- A memory cell neither takes nor releases the lock. -/
lemma countP_isLock_yieldSeq_MEM {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] as) : as.countP isLock = 0 := by
  rw [countP_yieldSeq_MEM handshakePred_isLock h]
  simp [isLock]

/-- A memory cell neither takes nor releases the lock. -/
lemma countP_isUnlock_yieldSeq_MEM {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] as) : as.countP isUnlock = 0 := by
  rw [countP_yieldSeq_MEM handshakePred_isUnlock h]
  simp [isUnlock]

/-- A proof step takes the lock exactly once. -/
lemma countP_isLock_yieldSeq_TUPLE {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] as) : as.countP isLock = 1 := by
  obtain ⟨r, w, -, -, -, e⟩ := countP_yieldSeq_TUPLE h
  rw [e isLock handshakePred_isLock]
  simp [isLock]

/-- A proof step releases the lock exactly once. -/
lemma countP_isUnlock_yieldSeq_TUPLE {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] as) : as.countP isUnlock = 1 := by
  obtain ⟨r, w, -, -, -, e⟩ := countP_yieldSeq_TUPLE h
  rw [e isUnlock handshakePred_isUnlock]
  simp [isUnlock]

/-- A proof step begins with the `lock`. -/
lemma yieldSeq_TUPLE_head {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] as) :
    ∃ t : List (AcAct F A C), as = AcAct.lock :: t := by
  rcases yieldSeq_TUPLE_shape h with
    ⟨c, x, y, g₁, g₂, g₃, e₁, e₂, e₃, e₄, w, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨o, g₁, g₂, g₃, e₁, e₂, w, -, -, -, -, -, -, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **In a part of a proof step that has begun, the lock has been taken and released at most
once, and it has been taken at least as often as it has been released.** -/
lemma countP_prefix_TUPLE {σ q : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] σ) (hq : q <+: σ) :
    q.countP isUnlock ≤ q.countP isLock ∧ q.countP isLock ≤ 1 := by
  have hsub : q.Sublist σ := hq.sublist
  have hle₁ : q.countP isLock ≤ σ.countP isLock := hsub.countP_le
  have hle₂ : q.countP isUnlock ≤ σ.countP isUnlock := hsub.countP_le
  rw [countP_isLock_yieldSeq_TUPLE h] at hle₁
  rw [countP_isUnlock_yieldSeq_TUPLE h] at hle₂
  refine ⟨?_, hle₁⟩
  cases q with
  | nil => simp
  | cons a q =>
      obtain ⟨t, rfl⟩ := yieldSeq_TUPLE_head h
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hq
      have : (AcAct.lock :: q).countP (isLock : AcAct F A C → Bool) = 1 + q.countP isLock := by
        simp [isLock, Nat.add_comm]
      omega

/-! ### The counting argument -/

/-- If every element of a list is counted at least as often by `f` as by `g`, then the number of
elements counted *strictly* more often is bounded by the difference of the two sums. -/
lemma length_filter_add_sum_le {β : Type*} (f g : β → ℕ) :
    ∀ l : List β, (∀ x ∈ l, g x ≤ f x) →
      (l.filter (fun x => decide (g x < f x))).length + (l.map g).sum ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
      intro h
      have hx := h x (by simp)
      have hrest := ih fun y hy => h y (by simp [hy])
      by_cases hlt : g x < f x
      · simp only [List.filter_cons, hlt, decide_true, if_true, List.length_cons,
          List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_neg (by simpa using hlt)]
        simp only [List.map_cons, List.sum_cons]
        omega

/-- Prefixes of a list of runs inherit the properties of the runs. -/
lemma forall_mem_of_forall₂_prefix {β : Type*} {P : List β → Prop} :
    ∀ {ps ls : List (List β)}, List.Forall₂ (· <+: ·) ps ls →
      (∀ l ∈ ls, ∀ q, q <+: l → P q) → ∀ q ∈ ps, P q := by
  intro ps ls h
  induction h with
  | nil => intro _ q hq; simp at hq
  | @cons a b as bs hab _ ih =>
      intro hall q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hall b (by simp) q hab
      · exact ih (fun l hl => hall l (by simp [hl])) q hq

/-- **At most one proof step is in progress at a time.**  Let a plan of the compiled problem be
an interleaving of the runs `γs` of its memory cells with the runs `σs` of its proof steps, and
let `p` be a prefix of the plan — a point of its execution.  Then `p` decomposes into prefixes
of the cell runs and prefixes `qs` of the proof steps, and at most one of the latter has taken
the lock without releasing it again: the proof steps do not overlap. -/
theorem at_most_one_tuple_in_progress {γs σs : List (List (AcAct F A C))}
    {as as₁ as₂ p : List (AcAct F A C)} {Q : Instance F A C I} {tI0 : C}
    (hγ : ∀ γ ∈ γs, (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] γ)
    (hσ : ∀ σ ∈ σs, (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] σ)
    (hcells : InterleaveList γs as₁) (hsteps : InterleaveList σs as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init)
    (hp : p <+: as) :
    ∃ (ps qs : List (List (AcAct F A C))) (p₁ p₂ : List (AcAct F A C)),
      Interleave p₁ p₂ p ∧ InterleaveList ps p₁ ∧ InterleaveList qs p₂ ∧
      List.Forall₂ (· <+: ·) ps γs ∧ List.Forall₂ (· <+: ·) qs σs ∧
      (qs.filter (fun q => decide (q.countP isUnlock < q.countP isLock))).length ≤ 1 := by
  classical
  obtain ⟨p₁, p₂, hp₁, hp₂, hintp⟩ := hint.exists_prefix hp
  obtain ⟨ps, hps, hallp⟩ := hcells.exists_prefix hp₁
  obtain ⟨qs, hqs, hallq⟩ := hsteps.exists_prefix hp₂
  refine ⟨ps, qs, p₁, p₂, hintp, hps, hqs, hallp, hallq, ?_⟩
  -- the semaphore invariant, evaluated at the prefix `p`
  obtain ⟨r, rfl⟩ := hp
  have happp : (problem D Q vars bound tI0).SeqApplicable p (problem D Q vars bound tI0).init :=
    (((ActionModel.seqApplicable_append _ _ _ _).1 happ).1)
  have hsem : p.countP isLock ≤ p.countP isUnlock + 1 :=
    countP_lock_le_countP_unlock_succ (Q := Q) (tI0 := tI0) happp
  -- the cells contribute nothing
  have hcell0 : ∀ q ∈ ps, q.countP (isLock : AcAct F A C → Bool) = 0 := by
    refine forall_mem_of_forall₂_prefix hallp (fun l hl q hq => ?_)
    have : q.countP (isLock : AcAct F A C → Bool) ≤ l.countP isLock := (hq.sublist).countP_le
    rw [countP_isLock_yieldSeq_MEM (hγ l hl)] at this
    omega
  have hcell1 : ∀ q ∈ ps, q.countP (isUnlock : AcAct F A C → Bool) = 0 := by
    refine forall_mem_of_forall₂_prefix hallp (fun l hl q hq => ?_)
    have : q.countP (isUnlock : AcAct F A C → Bool) ≤ l.countP isUnlock := (hq.sublist).countP_le
    rw [countP_isUnlock_yieldSeq_MEM (hγ l hl)] at this
    omega
  have hsum₁ : (ps.map (fun l => l.countP (isLock : AcAct F A C → Bool))).sum = 0 :=
    List.sum_eq_zero (by simpa using hcell0)
  have hsum₂ : (ps.map (fun l => l.countP (isUnlock : AcAct F A C → Bool))).sum = 0 :=
    List.sum_eq_zero (by simpa using hcell1)
  -- the steps: each of them has released the lock at most as often as it has taken it
  have hmono : ∀ q ∈ qs, q.countP (isUnlock : AcAct F A C → Bool) ≤
      q.countP (isLock : AcAct F A C → Bool) := by
    refine forall_mem_of_forall₂_prefix hallq (fun l hl q hq => ?_)
    exact (countP_prefix_TUPLE (hσ l hl) hq).1
  have hkey : (qs.filter (fun q => decide (q.countP isUnlock < q.countP isLock))).length +
      (qs.map (fun l => l.countP (isUnlock : AcAct F A C → Bool))).sum ≤
      (qs.map (fun l => l.countP (isLock : AcAct F A C → Bool))).sum :=
    length_filter_add_sum_le (fun q : List (AcAct F A C) => q.countP isLock)
      (fun q : List (AcAct F A C) => q.countP isUnlock) qs hmono
  have hlock : p.countP (isLock : AcAct F A C → Bool) =
      (qs.map (fun l => l.countP (isLock : AcAct F A C → Bool))).sum := by
    rw [hintp.countP, hps.countP, hqs.countP, hsum₁, Nat.zero_add]
  have hunlock : p.countP (isUnlock : AcAct F A C → Bool) =
      (qs.map (fun l => l.countP (isUnlock : AcAct F A C → Bool))).sum := by
    rw [hintp.countP, hps.countP, hqs.countP, hsum₂, Nat.zero_add]
  rw [hlock, hunlock] at hsem
  omega

end ToAc

end HTN
