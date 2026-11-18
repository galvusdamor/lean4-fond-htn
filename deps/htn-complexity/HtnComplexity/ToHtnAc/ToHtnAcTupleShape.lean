import HtnComplexity.ToHtnAc.ToHtnAcSyncCount
/-!
# The shape of a proof step

The compound task `TUPLE` of the HTN-AC compilation (`HtnComplexity/ToHtnAc/ToHtnAc.lean`) is one
step of the proof-tuple derivation that a plan of the compiled problem represents.  This file
determines exactly which action sequences it refines into.

There are two families of methods, and correspondingly two shapes:

* a **compound step**, for a method `c ↦ x y` of the source domain: take the lock, guess three
  states into the copies `1`, `2`, `3`, request a memory cell (`ask_R ; wait_R`) and check that
  it delivered the triple `(copy 1, x, copy 2)`, request a second one and check that it
  delivered `(copy 2, y, copy 3)`, store the task name `c`, offer the triple
  `(copy 1, c, copy 3)` to `w ≤ bound` memory cells (`ask_W ; wait_W`), release the lock;
* a **primitive step**, for an operator `o` of the source domain: take the lock, guess three
  states, check that the first two agree, apply `o` to the second copy, check that the second
  and the third agree, store the task name `o`, offer the triple to `w ≤ bound` memory cells,
  release the lock.

`HTN.ToAc.yieldSeq_TUPLE_shape` states this, and `HTN.ToAc.yieldSeq_TUPLE_of_shape` is the
converse: every choice of a source method (resp. operator), of refinements of the guessing and
comparing gadgets and of a number `w ≤ bound` of write requests gives a refinement of `TUPLE`.

Together with the memory-cell specification of `HtnComplexity/ToHtnAc/ToHtnAcMemPhase.lean` this is
the complete gadget inventory of a plan of the compiled problem: a plan interleaves memory
cells, each of which latches a triple between its two phases, with proof steps of the two shapes
above.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-- The action sequence of a compound proof step for the method `c ↦ x y`, built from
refinements `g₁ g₂ g₃` of the three state guesses, refinements `e₁ e₂ e₃ e₄` of the four
comparisons, and `w` write requests. -/
def tupleCompoundSeq (c : C) (x y : A ⊕ C) (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C))
    (w : ℕ) : List (AcAct F A C) :=
  AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++
    [AcAct.ask RW.read, AcAct.waitA RW.read] ++ e₁ ++ e₂ ++ [AcAct.preC x] ++
    [AcAct.ask RW.read, AcAct.waitA RW.read] ++ e₃ ++ e₄ ++
    [AcAct.preC y, AcAct.setC (Sum.inr c)] ++
    (List.replicate w
      ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten ++
    [AcAct.unlock])

/-- The action sequence of a primitive proof step for the operator `o`. -/
def tuplePrimitiveSeq (o : A) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)) (w : ℕ) :
    List (AcAct F A C) :=
  AcAct.lock :: (g₁ ++ g₂ ++ g₃ ++ e₁ ++ [AcAct.op2 o] ++ e₂ ++
    [AcAct.setC (Sum.inl o)] ++
    (List.replicate w
      ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten ++
    [AcAct.unlock])

/-- **The shape of a proof step.**  Every refinement of `TUPLE` is either a compound step for a
method `c ↦ x y` of the source domain or a primitive step for an operator `o`. -/
theorem yieldSeq_TUPLE_shape {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] as) :
    (∃ (c : C) (x y : A ⊕ C) (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)) (w : ℕ),
      D.SeqBody c [x, y] ∧ w ≤ bound ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄ ∧
      as = tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w) ∨
    (∃ (o : A) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)) (w : ℕ),
      w ≤ bound ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂ ∧
      as = tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w) := by
  obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
  rw [seqBody_TUPLE_iff] at hb
  rcases hb with ⟨c, x, y, hmethod, rfl⟩ | ⟨o, rfl⟩
  · obtain ⟨b₁, s₁, rfl, h₁, y₁⟩ := yieldSeq_cons_split hy
    obtain ⟨b₂, s₂, rfl, h₂, y₂⟩ := yieldSeq_cons_split y₁
    obtain ⟨b₃, s₃, rfl, h₃, y₃⟩ := yieldSeq_cons_split y₂
    obtain ⟨b₄, s₄, rfl, h₄, y₄⟩ := yieldSeq_cons_split y₃
    obtain ⟨b₅, s₅, rfl, h₅, y₅⟩ := yieldSeq_cons_split y₄
    obtain ⟨b₆, s₆, rfl, h₆, y₆⟩ := yieldSeq_cons_split y₅
    obtain ⟨b₇, s₇, rfl, h₇, y₇⟩ := yieldSeq_cons_split y₆
    obtain ⟨b₈, s₈, rfl, h₈, y₈⟩ := yieldSeq_cons_split y₇
    obtain ⟨b₉, s₉, rfl, h₉, y₉⟩ := yieldSeq_cons_split y₈
    obtain ⟨b₁₀, s₁₀, rfl, h₁₀, y₁₀⟩ := yieldSeq_cons_split y₉
    obtain ⟨b₁₁, s₁₁, rfl, h₁₁, y₁₁⟩ := yieldSeq_cons_split y₁₀
    obtain ⟨b₁₂, s₁₂, rfl, h₁₂, y₁₂⟩ := yieldSeq_cons_split y₁₁
    obtain ⟨b₁₃, s₁₃, rfl, h₁₃, y₁₃⟩ := yieldSeq_cons_split y₁₂
    obtain ⟨b₁₄, s₁₄, rfl, h₁₄, y₁₄⟩ := yieldSeq_cons_split y₁₃
    obtain ⟨b₁₅, s₁₅, rfl, h₁₅, y₁₅⟩ := yieldSeq_cons_split y₁₄
    rw [yieldSeq_nil_iff] at y₁₅
    rw [yieldSeq_singleton_inl_iff] at h₁ h₈ h₁₂ h₁₃ h₁₅
    subst h₁; subst h₈; subst h₁₂; subst h₁₃; subst h₁₅; subst y₁₅
    rw [yieldSeq_READ_iff] at h₅ h₉
    subst h₅; subst h₉
    obtain ⟨w, hw, rfl⟩ := yieldSeq_cnt_WRITE h₁₄
    exact Or.inl ⟨c, x, y, b₂, b₃, b₄, b₆, b₇, b₁₀, b₁₁, w, hmethod, hw, h₂, h₃, h₄, h₆, h₇,
      h₁₀, h₁₁, by simp [tupleCompoundSeq, List.append_assoc]⟩
  · obtain ⟨b₁, s₁, rfl, h₁, y₁⟩ := yieldSeq_cons_split hy
    obtain ⟨b₂, s₂, rfl, h₂, y₂⟩ := yieldSeq_cons_split y₁
    obtain ⟨b₃, s₃, rfl, h₃, y₃⟩ := yieldSeq_cons_split y₂
    obtain ⟨b₄, s₄, rfl, h₄, y₄⟩ := yieldSeq_cons_split y₃
    obtain ⟨b₅, s₅, rfl, h₅, y₅⟩ := yieldSeq_cons_split y₄
    obtain ⟨b₆, s₆, rfl, h₆, y₆⟩ := yieldSeq_cons_split y₅
    obtain ⟨b₇, s₇, rfl, h₇, y₇⟩ := yieldSeq_cons_split y₆
    obtain ⟨b₈, s₈, rfl, h₈, y₈⟩ := yieldSeq_cons_split y₇
    obtain ⟨b₉, s₉, rfl, h₉, y₉⟩ := yieldSeq_cons_split y₈
    obtain ⟨b₁₀, s₁₀, rfl, h₁₀, y₁₀⟩ := yieldSeq_cons_split y₉
    rw [yieldSeq_nil_iff] at y₁₀
    rw [yieldSeq_singleton_inl_iff] at h₁ h₆ h₈ h₁₀
    subst h₁; subst h₆; subst h₈; subst h₁₀; subst y₁₀
    obtain ⟨w, hw, rfl⟩ := yieldSeq_cnt_WRITE h₉
    exact Or.inr ⟨o, b₂, b₃, b₄, b₅, b₇, w, hw, h₂, h₃, h₄, h₅, h₇,
      by simp [tuplePrimitiveSeq, List.append_assoc]⟩

/-- **Conversely, every compound step is a refinement of `TUPLE`.** -/
theorem yieldSeq_TUPLE_of_compound {c : C} {x y : A ⊕ C}
    {g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)} {w : ℕ}
    (hmethod : D.SeqBody c [x, y]) (hw : w ≤ bound)
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂)
    (he₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃)
    (he₄ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄) :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)]
      (tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w) := by
  have hprim : ∀ a : AcAct F A C, (domain D vars bound).YieldSeq [Sum.inl a] [a] :=
    fun a => Domain.YieldSeq.prim Domain.YieldSeq.nil
  have hread : (domain D vars bound).YieldSeq [Sum.inr (AcTask.READ : AcTask F A C)]
      [AcAct.ask RW.read, AcAct.waitA RW.read] := yieldSeq_READ_iff.2 rfl
  have hwrite : (domain D vars bound).YieldSeq [Sum.inr (AcTask.cnt AcTask.WRITE bound)]
      ((List.replicate w
        ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten) := by
    refine (yieldSeq_cnt_iff bound).2 ⟨w, hw, ?_⟩
    clear hw
    induction w with
    | zero => simp
    | succ w ih =>
        rw [List.replicate_succ, List.replicate_succ, List.flatten_cons]
        exact (yieldSeq_WRITE_iff.2 rfl).append ih
  rw [yieldSeq_singleton_inr_iff]
  refine ⟨_, seqBody_TUPLE_iff.2 (Or.inl ⟨c, x, y, hmethod, rfl⟩), ?_⟩
  have := (hprim AcAct.lock).append (hg₁.append (hg₂.append (hg₃.append (hread.append
    (he₁.append (he₂.append ((hprim (AcAct.preC x)).append (hread.append (he₃.append
      (he₄.append ((hprim (AcAct.preC y)).append
        ((hprim (AcAct.setC (Sum.inr c))).append
          (hwrite.append (hprim AcAct.unlock))))))))))))))
  simpa [tupleCompoundSeq, List.append_assoc] using this

/-- **Conversely, every primitive step is a refinement of `TUPLE`.** -/
theorem yieldSeq_TUPLE_of_primitive {o : A} {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)} {w : ℕ}
    (hw : w ≤ bound)
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂) :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)]
      (tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w) := by
  have hprim : ∀ a : AcAct F A C, (domain D vars bound).YieldSeq [Sum.inl a] [a] :=
    fun a => Domain.YieldSeq.prim Domain.YieldSeq.nil
  have hwrite : (domain D vars bound).YieldSeq [Sum.inr (AcTask.cnt AcTask.WRITE bound)]
      ((List.replicate w
        ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten) := by
    refine (yieldSeq_cnt_iff bound).2 ⟨w, hw, ?_⟩
    clear hw
    induction w with
    | zero => simp
    | succ w ih =>
        rw [List.replicate_succ, List.replicate_succ, List.flatten_cons]
        exact (yieldSeq_WRITE_iff.2 rfl).append ih
  rw [yieldSeq_singleton_inr_iff]
  refine ⟨_, seqBody_TUPLE_iff.2 (Or.inr ⟨o, rfl⟩), ?_⟩
  have := (hprim AcAct.lock).append (hg₁.append (hg₂.append (hg₃.append (he₁.append
    ((hprim (AcAct.op2 o)).append (he₂.append ((hprim (AcAct.setC (Sum.inl o))).append
      (hwrite.append (hprim AcAct.unlock)))))))))
  simpa [tuplePrimitiveSeq, List.append_assoc] using this

end ToAc

end HTN
