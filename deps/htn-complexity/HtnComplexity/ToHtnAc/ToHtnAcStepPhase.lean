import HtnComplexity.ToHtnAc.ToHtnAcCellPhase
import HtnComplexity.ToHtnAc.ToHtnAcMutex
/-!
# How far a proof step has got is determined by the lock

The companion of `HtnComplexity/ToHtnAc/ToHtnAcCellPhase.lean` for the other kind of component of a
plan of the HTN-AC compilation.  A proof step begins with `lock` and ends with `unlock`, and
performs neither in between (`HTN.ToAc.countP_isLock_yieldSeq_TUPLE`), so the two extreme
positions of a step are recognised by counting alone:

* `HTN.ToAc.step_eq_nil_of_countP_lock` — a proof step that has not taken the lock has not
  moved;
* `HTN.ToAc.step_eq_run_of_countP_unlock` — a proof step that has released the lock has
  finished.

Together with `HTN.ToAc.at_most_one_tuple_in_progress` this says that, at any point of a plan,
all proof steps but at most one are either untouched or complete, and the exceptional one is the
step that currently holds the lock.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-- A proof step ends with `unlock`. -/
lemma yieldSeq_TUPLE_last {σ : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] σ) :
    ∃ t : List (AcAct F A C), σ = t ++ [AcAct.unlock] := by
  rcases yieldSeq_TUPLE_shape h with
    ⟨c, x, y, g₁, g₂, g₃, e₁, e₂, e₃, e₄, w, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨o, g₁, g₂, g₃, e₁, e₂, w, -, -, -, -, -, -, rfl⟩
  · exact ⟨AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++
      [AcAct.ask RW.read, AcAct.waitA RW.read] ++ e₁ ++ e₂ ++ [AcAct.preC x] ++
      [AcAct.ask RW.read, AcAct.waitA RW.read] ++ e₃ ++ e₄ ++
      [AcAct.preC y, AcAct.setC (Sum.inr c)] ++
      (List.replicate w
        ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten), rfl⟩
  · exact ⟨AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++
      [AcAct.setC (Sum.inl o)] ++
      (List.replicate w
        ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten), rfl⟩

/-- **A proof step that has not taken the lock has not moved.** -/
theorem step_eq_nil_of_countP_lock {σ q : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] σ)
    (hq : q <+: σ) (h0 : q.countP isLock = 0) : q = [] := by
  obtain ⟨t, rfl⟩ := yieldSeq_TUPLE_head h
  exact prefix_eq_nil_of_countP_head rfl (by simp [isLock]) hq h0

/-- **A proof step that has released the lock has finished.** -/
theorem step_eq_run_of_countP_unlock {σ q : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] σ)
    (hq : q <+: σ) (h1 : 1 ≤ q.countP isUnlock) : q = σ := by
  obtain ⟨t, hσ⟩ := yieldSeq_TUPLE_last h
  exact prefix_eq_of_countP_last hσ (by simp [isUnlock])
    (countP_isUnlock_yieldSeq_TUPLE h) hq h1

/-- **A proof step that is neither untouched nor complete holds the lock.**  Equivalently: at a
point at which a step has taken the lock but not released it, it is the step in progress. -/
theorem step_countP_lock_pos_of_ne_nil {σ q : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] σ)
    (hq : q <+: σ) (hne : q ≠ []) (hlt : q ≠ σ) :
    1 ≤ q.countP isLock ∧ q.countP isUnlock = 0 := by
  constructor
  · by_contra hc
    exact hne (step_eq_nil_of_countP_lock h hq (by omega))
  · by_contra hc
    exact hlt (step_eq_run_of_countP_unlock h hq (by omega))

end ToAc

end HTN
