import HtnPlanning.Core.ProofList
/-!
# Short proof lists for a given plan

`HtnPlanning/Core/ProofList.lean` bounds the length of a proof list of a provable triple by
the *number of triples* of the signature, which is exponential.  That is the right bound when
nothing is known about the plan; but if a concrete refinement `D.Yield x as` of the initial task
into an executable action sequence `as` is at hand, the derivation that follows its
decomposition tree is much smaller: in a domain all of whose method bodies have **exactly two**
subtasks the tree has `|as|` leaves, hence `2·|as| − 1` nodes, and the proof list read off it is
that long.

`HTN.Domain.exists_proofList_yield_le` is that statement.  It is what turns the completeness
theorem of the TO-HTN ⟶ HTN-AC compilation into a bound on the *length* of the compiled plan
(`HtnCompilability/ToHtnAc/ToHtnAcPlanLength.lean`): the compiled plan is one block per entry of the
proof list, so a source plan of `n` actions is simulated by a compiled plan of `O(n)` blocks.
-/

namespace HTN

namespace Domain

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} {D : Domain F A C I}

/-- **A proof list following the decomposition tree of a plan.**  In a domain whose method
bodies all have exactly two subtasks, an executable refinement `as` of the task `x` gives a
proof list headed by the triple `(s, x, γ*(as, s))` with at most `2·|as| − 1` entries.

(The bound is stated as `l.length + 2 ≤ 2 * as.length`, `l` being the list *behind* the head, so
that no truncated subtraction occurs; note that it forces `as ≠ []`, which is indeed the case
when every method has two subtasks.) -/
theorem exists_proofList_yield_le
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ y z, xs = [y, z]) :
    ∀ {x : A ⊕ C} {as : List A}, D.Yield x as → ∀ {s : Set F}, D.SeqApplicable as s →
      ∃ l : List (Trip F A C),
        D.ProofList ((s, x, D.transitionSeq as s) :: l) ∧ l.length + 2 ≤ 2 * as.length := by
  intro x as hy
  induction hy with
  | prim a =>
      intro s happ
      refine ⟨[], ProofList.cons ProofList.nil (Justified.prim happ.1), by simp⟩
  | zero h => exact absurd (hbin _ [] h) (by simp)
  | one h _ _ => exact absurd (hbin _ [_] h) (by simp)
  | @two c y z as bs hb _ _ ihx ihy =>
      intro s happ
      rw [ActionModel.seqApplicable_append] at happ
      obtain ⟨lx, hlx, hlenx⟩ := ihx happ.1
      obtain ⟨ly, hly, hleny⟩ := ihy happ.2
      refine ⟨((D.transitionSeq as s, z, D.transitionSeq bs (D.transitionSeq as s)) :: ly) ++
        ((s, y, D.transitionSeq as s) :: lx), ?_, ?_⟩
      · rw [ActionModel.transitionSeq_append]
        exact ProofList.cons (hlx.append hly)
          (Justified.two (s'' := D.transitionSeq as s) hb (by simp) (by simp))
      · simp only [List.length_append, List.length_cons, List.length_append]
        omega

end Domain

end HTN
