import HtnComplexity.Computable.TokState
/-!
# The token gadget: one block of the compiled description

This file executes the compiled counterpart of one source method: the action sequence

    strt i ;  doA (i,x₁) … doA (i,xₙ) ;  fin i

`HTN.Syn.DoListOK` is the invariant of the middle part — the subtasks picked so far are
distinct, new, allowed by the ordering, and their source actions are executable — and
`HTN.Syn.seqApplicable_doList` shows that it is *exactly* the condition under which the middle
part is executable.  Closing the block with `fin i` forces every primitive subtask to have been
picked, so the executable blocks are exactly the enumerations of the primitive part
(`HTN.Syn.TnDesc.PrimLin`) whose source action sequence is executable
(`HTN.Syn.seqApplicable_block`), and the block has the same effect on the encoded state as the
source action sequence has on the source state (`HTN.Syn.transitionSeq_block`).
-/

namespace HTN

namespace Syn

variable {d : DomDesc} {q q' : InstDesc}

/-! ### The middle part of a block -/

/-- **The invariant of the middle part of a block.**  The subtasks `xs`, executed after the
subtasks `ys`, are pairwise distinct, none of them has been executed yet, every subtask ordered
before one of them is among `ys` and `xs`, the order of `xs` respects the ordering of the
method, and the corresponding source actions are executable. -/
structure DoListOK (d : DomDesc) (q : InstDesc) (i : ℕ) (s : Set ℕ) (ys xs : List ℕ) : Prop where
  /-- No subtask is picked twice. -/
  nodup : xs.Nodup
  /-- No subtask has been executed before. -/
  fresh : ∀ x ∈ xs, x ∉ ys
  /-- Every subtask ordered before a picked one is executed at some point. -/
  preds : ∀ x ∈ xs, ∀ y ∈ TnDesc.predsOf (tOf d i) x, y ∈ ys ∨ y ∈ xs
  /-- The picks respect the ordering of the method. -/
  ordered : xs.Pairwise (fun a b => ¬ (tOf d i).toTaskNetwork.ord b a)
  /-- The source actions are executable. -/
  src : (problem d q).SeqApplicable (xs.map (TnDesc.actOf (tOf d i))) (srcRun d q i s ys)

/-- Executing the compiled subtask actions of `xs` marks exactly `xs` as done. -/
theorem transitionSeq_doList {i : ℕ} (hi : i < d.methods.length) :
    ∀ (xs ys : List ℕ) (s : Set ℕ), (∀ x ∈ xs, x ∈ pOf d i) →
      (problem (tokDom d) q').transitionSeq (xs.map (doA i)) (midState d q i s ys) =
        midState d q i s (ys ++ xs) := by
  intro xs
  induction xs with
  | nil => intro ys s _; simp
  | cons x xs ih =>
      intro ys s hmem
      rw [List.map_cons, ActionModel.transitionSeq_cons,
        transition_doA hi (hmem x (by simp)) s ys,
        ih (ys ++ [x]) s (fun y hy => hmem y (by simp [hy]))]
      simp

/-- **The middle part of a block is executable exactly under the invariant.** -/
theorem seqApplicable_doList {i : ℕ} (hi : i < d.methods.length) :
    ∀ (xs ys : List ℕ) (s : Set ℕ), (∀ x ∈ xs, x ∈ pOf d i) →
      ((problem (tokDom d) q').SeqApplicable (xs.map (doA i)) (midState d q i s ys) ↔
        DoListOK d q i s ys xs) := by
  intro xs
  induction xs with
  | nil =>
      intro ys s _
      simp only [List.map_nil, ActionModel.seqApplicable_nil, true_iff]
      exact ⟨List.nodup_nil, by simp, by simp, List.Pairwise.nil, by simp⟩
  | cons x xs ih =>
      intro ys s hmem
      have hx : x ∈ pOf d i := hmem x (by simp)
      have hmem' : ∀ y ∈ xs, y ∈ pOf d i := fun y hy => hmem y (by simp [hy])
      rw [List.map_cons, ActionModel.seqApplicable_cons, applicable_doA hi hx,
        transition_doA hi hx, ih (ys ++ [x]) s hmem']
      constructor
      · rintro ⟨⟨hxys, hpre, hsrc⟩, hok⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact List.nodup_cons.2 ⟨fun hc => hok.fresh x hc (by simp), hok.nodup⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hxys
          · exact fun hc => hok.fresh y hy (by simp [hc])
        · intro y hy z hz
          rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inl (hpre z hz)
          · rcases hok.preds y hy z hz with h | h
            · rcases List.mem_append.1 h with h | h
              · exact Or.inl h
              · simp only [List.mem_singleton] at h
                exact Or.inr (by simp [h])
            · exact Or.inr (by simp [h])
        · refine List.pairwise_cons.2 ⟨?_, hok.ordered⟩
          intro b hb hord
          have hbp : b ∈ TnDesc.predsOf (tOf d i) x :=
            TnDesc.mem_predsOf.2 ⟨hmem' b hb, hord⟩
          exact hok.fresh b hb (by simp [hpre b hbp])
        · rw [List.map_cons, ActionModel.seqApplicable_cons]
          refine ⟨hsrc, ?_⟩
          have hs := hok.src
          rwa [srcRun_append] at hs
      · rintro ⟨hnd, hfresh, hpreds, hord, hsrc⟩
        obtain ⟨hxxs, hnd'⟩ := List.nodup_cons.1 hnd
        obtain ⟨hordx, hord'⟩ := List.pairwise_cons.1 hord
        obtain ⟨hsrcx, hsrc'⟩ := by
          rw [List.map_cons, ActionModel.seqApplicable_cons] at hsrc
          exact hsrc
        have hpre : ∀ y ∈ TnDesc.predsOf (tOf d i) x, y ∈ ys := by
          intro y hy
          obtain ⟨hyp, hyord⟩ := TnDesc.mem_predsOf.1 hy
          rcases hpreds x (by simp) y hy with h | h
          · exact h
          · rcases List.mem_cons.1 h with rfl | h
            · exact absurd hyord ((tOf d i).toTaskNetwork_wf.irrefl y)
            · exact absurd hyord (hordx y h)
        refine ⟨⟨hfresh x (by simp), hpre, hsrcx⟩, ?_, ?_, ?_, hord', ?_⟩
        · exact hnd'
        · intro y hy hc
          rcases List.mem_append.1 hc with h | h
          · exact hfresh y (by simp [hy]) h
          · simp only [List.mem_singleton] at h
            exact hxxs (h ▸ hy)
        · intro y hy z hz
          rcases hpreds y (by simp [hy]) z hz with h | h
          · exact Or.inl (by simp [h])
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl (by simp)
            · exact Or.inr h
        · rw [srcRun_append]
          exact hsrc'

/-! ### A whole block -/

/-- **The executable blocks of the compiled description are exactly the enumerations of the
primitive part of the source method whose source action sequence is executable.** -/
theorem seqApplicable_block {i : ℕ} (hi : i < d.methods.length) (s : Set ℕ) (xs : List ℕ)
    (hmem : ∀ x ∈ xs, x ∈ pOf d i) :
    (problem (tokDom d) q').SeqApplicable (strtA i :: (xs.map (doA i) ++ [finA i]))
        (stateF '' s) ↔
      (TnDesc.PrimLin (tOf d i) xs ∧
        (problem d q).SeqApplicable (xs.map (TnDesc.actOf (tOf d i))) s) := by
  rw [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_append,
    transition_strtA hi s, transitionSeq_doList (q := q) hi xs [] s hmem,
    seqApplicable_doList (q := q) hi xs [] s hmem]
  simp only [List.nil_append, ActionModel.seqApplicable_cons, ActionModel.seqApplicable_nil,
    and_true, applicable_finA hi, applicable_strtA hi, true_and]
  constructor
  · rintro ⟨hok, hcomp⟩
    refine ⟨⟨hok.nodup, ?_, hok.ordered⟩, ?_⟩
    · intro y
      exact ⟨fun hy => hmem y hy, fun hy => hcomp y hy⟩
    · have := hok.src
      rwa [srcRun_nil] at this
  · rintro ⟨⟨hnd, hiff, hord⟩, hsrc⟩
    refine ⟨⟨hnd, by simp, ?_, hord, by rwa [srcRun_nil]⟩, fun y hy => (hiff y).2 hy⟩
    intro y hy z hz
    exact Or.inr ((hiff z).2 (TnDesc.mem_predsOf.1 hz).1)

/-- **A block has the same effect as the source action sequence.** -/
theorem transitionSeq_block {i : ℕ} (hi : i < d.methods.length) (s : Set ℕ) (xs : List ℕ)
    (hmem : ∀ x ∈ xs, x ∈ pOf d i) (hcomp : ∀ x ∈ pOf d i, x ∈ xs) :
    (problem (tokDom d) q').transitionSeq (strtA i :: (xs.map (doA i) ++ [finA i]))
        (stateF '' s) =
      stateF '' ((problem d q).transitionSeq (xs.map (TnDesc.actOf (tOf d i))) s) := by
  rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    transition_strtA hi s, transitionSeq_doList (q := q) hi xs [] s hmem,
    List.nil_append, ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
    transition_finA hi s xs hcomp hmem]
  rfl

end Syn

end HTN
