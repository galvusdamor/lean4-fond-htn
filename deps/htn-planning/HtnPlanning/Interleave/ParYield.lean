import HtnPlanning.Core.TONormalForm
import HtnPlanning.Interleave.InterleaveList
/-!
# Refining several task sequences in parallel

`HtnPlanning/Core/TONormalForm.lean` describes the refinement of *one* task sequence in a
totally ordered domain: `HTN.Domain.YieldSeq xs as` is the leftmost derivation relation of the
context-free grammar whose productions are the methods.  An initial task network that consists
of several **unordered** compound tasks refines into an *interleaving* of refinements of those
tasks, and a compilation that has to simulate such a network with a single compound task has to
interleave them one step at a time.  This file supplies that relation:

* `HTN.Domain.ParYield D L as` — the list of task sequences `L` (one per process) refines into
  the action sequence `as`, one step of one process at a time: a leading primitive task of some
  process is executed, or a leading compound task of some process is replaced by the body of one
  of its methods, and the derivation ends when every process has run out of tasks;
* `HTN.Domain.parYield_iff_interleaveList` — **the two readings agree**: `ParYield D L as` holds
  exactly when `as` is an interleaving of refinements of the individual sequences.

The theorem is the bridge between the source side of a compilation, where the processes are
independent tasks of the initial task network and their refinements interleave, and its target
side, where a single compound task carrying the whole configuration takes the steps one at a
time.
-/

namespace HTN

/-! ### Splitting a `List.Forall₂` at a position -/

/-- A `Forall₂` over a list split at one entry splits accordingly. -/
theorem forall₂_append_cons_inv {α β : Type*} {R : α → β → Prop} :
    ∀ {L₁ : List α} {x : α} {L₂ : List α} {ys : List β},
      List.Forall₂ R (L₁ ++ x :: L₂) ys →
        ∃ Y₁ w Y₂, ys = Y₁ ++ w :: Y₂ ∧ List.Forall₂ R L₁ Y₁ ∧ R x w ∧ List.Forall₂ R L₂ Y₂
  | [], x, L₂, ys, h => by
      cases h with
      | cons hx hrest => exact ⟨[], _, _, rfl, List.Forall₂.nil, hx, hrest⟩
  | u :: L₁, x, L₂, ys, h => by
      cases h with
      | cons hu hrest =>
          obtain ⟨Y₁, w, Y₂, rfl, h₁, hw, h₂⟩ := forall₂_append_cons_inv hrest
          exact ⟨_ :: Y₁, w, Y₂, rfl, List.Forall₂.cons hu h₁, hw, h₂⟩

/-- A `Forall₂` can be assembled from a split. -/
theorem forall₂_append_cons {α β : Type*} {R : α → β → Prop} :
    ∀ {L₁ : List α} {Y₁ : List β} {x : α} {w : β} {L₂ : List α} {Y₂ : List β},
      List.Forall₂ R L₁ Y₁ → R x w → List.Forall₂ R L₂ Y₂ →
        List.Forall₂ R (L₁ ++ x :: L₂) (Y₁ ++ w :: Y₂)
  | [], _, x, w, L₂, Y₂, h₁, hw, h₂ => by
      cases h₁
      exact List.Forall₂.cons hw h₂
  | u :: L₁, Y₁, x, w, L₂, Y₂, h₁, hw, h₂ => by
      cases h₁ with
      | cons hu hrest => exact List.Forall₂.cons hu (forall₂_append_cons hrest hw h₂)

namespace Domain

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- **Refinement of a list of task sequences, one step at a time.**  Every step picks one of the
sequences and either executes its leading primitive task or replaces its leading compound task
by the body of one of its methods; the derivation ends when all sequences are empty. -/
inductive ParYield (D : Domain F A C I) : List (List (A ⊕ C)) → List A → Prop
  /-- All processes have finished. -/
  | done {L : List (List (A ⊕ C))} (h : ∀ xs ∈ L, xs = []) : ParYield D L []
  /-- The leading primitive task of one process is executed. -/
  | prim {L₁ L₂ : List (List (A ⊕ C))} {a : A} {xs : List (A ⊕ C)} {as : List A}
      (h : ParYield D (L₁ ++ xs :: L₂) as) :
      ParYield D (L₁ ++ (Sum.inl a :: xs) :: L₂) (a :: as)
  /-- The leading compound task of one process is decomposed. -/
  | comp {L₁ L₂ : List (List (A ⊕ C))} {c : C} {bs xs : List (A ⊕ C)} {as : List A}
      (hm : D.SeqBody c bs) (h : ParYield D (L₁ ++ (bs ++ xs) :: L₂) as) :
      ParYield D (L₁ ++ (Sum.inr c :: xs) :: L₂) as

variable {D : Domain F A C I}

/-! ### Small facts about the relation -/

/-- A finished process may be added in front. -/
theorem ParYield.nil_cons {L : List (List (A ⊕ C))} {as : List A} (h : ParYield D L as) :
    ParYield D ([] :: L) as := by
  induction h with
  | done h =>
      refine ParYield.done ?_
      intro xs hxs
      rcases List.mem_cons.1 hxs with rfl | hxs
      · rfl
      · exact h xs hxs
  | @prim L₁ L₂ a xs as _ ih =>
      exact ParYield.prim (L₁ := [] :: L₁) (L₂ := L₂) (a := a) (xs := xs) ih
  | @comp L₁ L₂ c bs xs as hm _ ih =>
      exact ParYield.comp (L₁ := [] :: L₁) (L₂ := L₂) (c := c) (bs := bs) (xs := xs) hm ih

/-- A single process refines exactly as the task sequence does. -/
theorem parYield_singleton_of_yieldSeq {xs : List (A ⊕ C)} {as : List A}
    (h : D.YieldSeq xs as) : ParYield D [xs] as := by
  induction h with
  | nil => exact ParYield.done (by simp)
  | @prim a zs bs _ ih => exact ParYield.prim (L₁ := []) (L₂ := []) ih
  | @comp c cs zs bs hm _ ih =>
      exact ParYield.comp (L₁ := []) (L₂ := []) hm (by simpa using ih)

/-- Empty processes refine into empty action sequences. -/
theorem forall₂_yieldSeq_nil :
    ∀ {L : List (List (A ⊕ C))}, (∀ xs ∈ L, xs = []) →
      List.Forall₂ D.YieldSeq L (L.map fun _ => [])
  | [], _ => List.Forall₂.nil
  | x :: L, h => by
      have hx : x = [] := h x (by simp)
      subst hx
      exact List.Forall₂.cons YieldSeq.nil
        (forall₂_yieldSeq_nil fun y hy => h y (List.mem_cons_of_mem _ hy))

/-! ### From the parallel relation to interleavings -/

/-- Prefixing an action to one component of an interleaving prefixes it to the interleaving. -/
theorem interleaveList_cons_component {α : Type*} :
    ∀ {A₁ A₂ : List (List α)} {w : List α} {a : α} {z : List α},
      InterleaveList (A₁ ++ w :: A₂) z → InterleaveList (A₁ ++ (a :: w) :: A₂) (a :: z)
  | [], A₂, w, a, z, h => by
      cases h with
      | cons hrest hint => exact InterleaveList.cons hrest (Interleave.left a hint)
  | u :: A₁, A₂, w, a, z, h => by
      cases h with
      | cons hrest hint =>
          exact InterleaveList.cons (interleaveList_cons_component hrest)
            (Interleave.right a hint)

/-- **Every parallel refinement is an interleaving of refinements of the components.** -/
theorem exists_interleaveList_of_parYield {L : List (List (A ⊕ C))} {as : List A}
    (h : ParYield D L as) :
    ∃ ass, InterleaveList ass as ∧ List.Forall₂ D.YieldSeq L ass := by
  induction h with
  | @done L h =>
      exact ⟨L.map fun _ => [], InterleaveList.of_forall_nil (by simp), forall₂_yieldSeq_nil h⟩
  | @prim L₁ L₂ a xs as _ ih =>
      obtain ⟨ass, hint, hall⟩ := ih
      obtain ⟨Y₁, w, Y₂, rfl, h₁, hw, h₂⟩ := forall₂_append_cons_inv hall
      exact ⟨Y₁ ++ (a :: w) :: Y₂, interleaveList_cons_component hint,
        forall₂_append_cons h₁ (YieldSeq.prim hw) h₂⟩
  | @comp L₁ L₂ c bs xs as hm _ ih =>
      obtain ⟨ass, hint, hall⟩ := ih
      obtain ⟨Y₁, w, Y₂, rfl, h₁, hw, h₂⟩ := forall₂_append_cons_inv hall
      exact ⟨Y₁ ++ w :: Y₂, hint, forall₂_append_cons h₁ (YieldSeq.comp hm hw) h₂⟩

/-! ### From interleavings to the parallel relation -/

/-- **Prepending a process**: a refinement of `xs` interleaved with a parallel refinement of `L`
is a parallel refinement of `xs :: L`. -/
theorem YieldSeq.parYield_cons {xs : List (A ⊕ C)} {as₁ : List A} (hy : D.YieldSeq xs as₁) :
    ∀ {L : List (List (A ⊕ C))} {as₂ : List A}, ParYield D L as₂ →
      ∀ {as : List A}, Interleave as₁ as₂ as → ParYield D (xs :: L) as := by
  induction hy with
  | nil =>
      intro L as₂ hp as hint
      rw [hint.eq_of_nil_left]
      exact hp.nil_cons
  | @prim a zs bs hzs ih =>
      intro L as₂ hp
      induction hp with
      | @done L hL =>
          intro as hint
          have has : as = a :: bs := hint.eq_of_nil_right
          subst has
          exact ParYield.prim (L₁ := []) (L₂ := L) (a := a) (xs := zs)
            (ih (ParYield.done hL) (Interleave.nil_right bs))
      | @prim L₁ L₂ b ys as' hp' ihp =>
          intro as hint
          cases hint with
          | left _ hint' =>
              exact ParYield.prim (L₁ := []) (L₂ := L₁ ++ (Sum.inl b :: ys) :: L₂)
                (a := a) (xs := zs) (ih (ParYield.prim hp') hint')
          | right _ hint' =>
              exact ParYield.prim (L₁ := (Sum.inl a :: zs) :: L₁) (L₂ := L₂) (a := b) (xs := ys)
                (ihp hint')
      | @comp L₁ L₂ c bs' ys as' hm hp' ihp =>
          intro as hint
          exact ParYield.comp (L₁ := (Sum.inl a :: zs) :: L₁) (L₂ := L₂) hm (ihp hint)
  | @comp c bs' zs as' hm hy' ih =>
      intro L as₂ hp as hint
      exact ParYield.comp (L₁ := []) (L₂ := L) hm (by simpa using ih hp hint)

/-- **Every interleaving of refinements of the components is a parallel refinement.** -/
theorem parYield_of_interleaveList {L : List (List (A ⊕ C))} {ass : List (List A)} {as : List A}
    (hall : List.Forall₂ D.YieldSeq L ass) (hint : InterleaveList ass as) : ParYield D L as := by
  induction hall generalizing as with
  | nil =>
      cases hint
      exact ParYield.done (by simp)
  | @cons x w L ass hx hall ih =>
      cases hint with
      | cons hrest hint' => exact hx.parYield_cons (ih hrest) hint'

/-- **The two readings of a parallel refinement agree.** -/
theorem parYield_iff_interleaveList {L : List (List (A ⊕ C))} {as : List A} :
    ParYield D L as ↔ ∃ ass, InterleaveList ass as ∧ List.Forall₂ D.YieldSeq L ass :=
  ⟨exists_interleaveList_of_parYield, fun ⟨_, hint, hall⟩ =>
    parYield_of_interleaveList hall hint⟩

end Domain

end HTN
