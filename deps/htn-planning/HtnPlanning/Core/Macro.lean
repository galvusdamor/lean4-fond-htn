import HtnPlanning.Core.Classical
/-!
# Macro actions: sequential composition of STRIPS actions

A sequence of STRIPS actions has exactly the same effect as a *single* STRIPS action, and it is
applicable in exactly those states in which a single (statically determined) precondition
holds — provided the sequence is not *statically infeasible*, i.e. provided no action of the
sequence deletes a fact that a later action needs and no intermediate action re-adds.

Concretely, for `δ = (prec, add, del)` and a list `os` of actions we define

* `δ.seqDel os`, `δ.seqAdd os` with `γ(os, s) = (s \ seqDel os) ∪ seqAdd os`
  (`ActionModel.transitionSeq_eq`),
* `δ.seqPre os` and the static predicate `δ.SeqFeasible os` with
  `SeqApplicable os s ↔ SeqFeasible os ∧ seqPre os ⊆ s`
  (`ActionModel.seqApplicable_iff`).

This is the tool that turns the body `o₁ … oₙ` of a *totally ordered* decomposition method into
one classical action, which is how regular HTN problems are compiled into STRIPS in
`HtnComplexity/Regular/RegularToStrips.lean`.
-/

namespace HTN

namespace ActionModel

universe u v

variable {F : Type u} {A : Type v} (δ : ActionModel F A)

/-- The facts deleted by a sequence of actions and not re-added afterwards are contained in
`seqDel`; more precisely `γ(os, s) = (s \ seqDel os) ∪ seqAdd os`. -/
def seqDel : List A → Set F
  | [] => ∅
  | o :: os => δ.del o ∪ seqDel os

/-- The facts that hold after executing the sequence of actions, independently of the state it
is executed in. -/
def seqAdd : List A → Set F
  | [] => ∅
  | o :: os => seqAdd os ∪ (δ.add o \ δ.seqDel os)

/-- The precondition of the macro action of a sequence: the facts that have to hold in the
state in which the sequence is started. -/
def seqPre : List A → Set F
  | [] => ∅
  | o :: os => δ.prec o ∪ (seqPre os \ δ.add o)

/-- A sequence of actions is *statically feasible* iff no action deletes a fact required later
on which is not re-established in between.  An infeasible sequence is applicable in no state at
all. -/
def SeqFeasible : List A → Prop
  | [] => True
  | o :: os => SeqFeasible os ∧ Disjoint (δ.seqPre os \ δ.add o) (δ.del o)

@[simp] lemma seqDel_nil : δ.seqDel [] = ∅ := rfl
@[simp] lemma seqAdd_nil : δ.seqAdd [] = ∅ := rfl
@[simp] lemma seqPre_nil : δ.seqPre [] = ∅ := rfl
lemma seqFeasible_nil : δ.SeqFeasible [] := trivial

@[simp] lemma seqDel_cons (o : A) (os : List A) :
    δ.seqDel (o :: os) = δ.del o ∪ δ.seqDel os := rfl

@[simp] lemma seqAdd_cons (o : A) (os : List A) :
    δ.seqAdd (o :: os) = δ.seqAdd os ∪ (δ.add o \ δ.seqDel os) := rfl

@[simp] lemma seqPre_cons (o : A) (os : List A) :
    δ.seqPre (o :: os) = δ.prec o ∪ (δ.seqPre os \ δ.add o) := rfl

@[simp] lemma seqFeasible_cons (o : A) (os : List A) :
    δ.SeqFeasible (o :: os) ↔
      δ.SeqFeasible os ∧ Disjoint (δ.seqPre os \ δ.add o) (δ.del o) := Iff.rfl

/-- **The effect of a sequence of actions is the effect of a single STRIPS action.** -/
theorem transitionSeq_eq (os : List A) (s : Set F) :
    δ.transitionSeq os s = (s \ δ.seqDel os) ∪ δ.seqAdd os := by
  induction os generalizing s with
  | nil => simp
  | cons o os ih =>
      rw [transitionSeq_cons, ih]
      ext x
      simp only [transition, Set.mem_union, Set.mem_diff, seqDel_cons, seqAdd_cons]
      tauto

/-- **The applicability of a sequence of actions is the applicability of a single STRIPS
action**, once the (state independent) feasibility test is passed. -/
theorem seqApplicable_iff (os : List A) (s : Set F) :
    δ.SeqApplicable os s ↔ (δ.SeqFeasible os ∧ δ.seqPre os ⊆ s) := by
  induction os generalizing s with
  | nil => simp [SeqApplicable, δ.seqFeasible_nil]
  | cons o os ih =>
      rw [seqApplicable_cons, ih]
      constructor
      · rintro ⟨hpre, hfeas, hsub⟩
        refine ⟨⟨hfeas, ?_⟩, ?_⟩
        · rw [Set.disjoint_left]
          rintro x ⟨hx, hxadd⟩ hxdel
          have := hsub hx
          simp only [transition, Set.mem_union, Set.mem_diff] at this
          tauto
        · rintro x (hx | ⟨hx, hxadd⟩)
          · exact hpre hx
          · have := hsub hx
            simp only [transition, Set.mem_union, Set.mem_diff] at this
            tauto
      · rintro ⟨⟨hfeas, hdisj⟩, hsub⟩
        refine ⟨fun x hx => hsub (Or.inl hx), hfeas, ?_⟩
        intro x hx
        by_cases hxadd : x ∈ δ.add o
        · exact Or.inr hxadd
        · have hx' : x ∈ δ.seqPre os \ δ.add o := ⟨hx, hxadd⟩
          have hxdel : x ∉ δ.del o := fun h => (Set.disjoint_left.1 hdisj hx') h
          exact Or.inl ⟨hsub (Or.inr hx'), hxdel⟩

/-- An infeasible sequence of actions is applicable in no state whatsoever. -/
lemma not_seqApplicable_of_not_feasible {os : List A} (h : ¬ δ.SeqFeasible os) (s : Set F) :
    ¬ δ.SeqApplicable os s := fun hcon => h ((δ.seqApplicable_iff os s).1 hcon).1

lemma seqDel_append (os os' : List A) :
    δ.seqDel (os ++ os') = δ.seqDel os ∪ δ.seqDel os' := by
  induction os with
  | nil => simp
  | cons o os ih => rw [List.cons_append, seqDel_cons, ih, seqDel_cons, Set.union_assoc]

end ActionModel

end HTN
