import HtnComplexity.Computable.TestChain
/-!
# The step-chain gadget: a chain of compound tasks over actions *with effects*

`HtnComplexity/Computable/TestChain.lean` reads a state through a chain of compound tasks,
but its actions are effect-free, so the gadget can only test the initial state.  This file is
the same gadget with **arbitrary actions**:

* `HTN.Syn.stepDom P` — the **step domain** of a list of *named steps* `(c, prec, add, del)`:
  one action per entry and one method decomposing the compound task `c` into it.  Several
  entries may carry the same name, and those are the alternatives the planner chooses between;
* `HTN.Syn.stepInst S L G` — the facts `L` hold initially, the goal is `G`, and the initial task
  network is the *chain* of the compound tasks `S`;
* `HTN.Syn.solvable_step_iff` — the gadget is solvable exactly when there is a choice of one
  step per task of the chain whose action sequence is applicable in the initial state and
  reaches the goal.

So a step chain is a **nondeterministic finite-state computation driven by the instance**: the
instance supplies the sequence of names, the domain the moves available under each name.  The
gadget is totally ordered, regular, acyclic and tail recursive, as in `TestChain.lean`, and its
initial task network is again *not* rooted — the length of the computation is bounded by the
size of the instance, not of the domain.  `TestChain.lean` is the special case of effect-free
actions and an empty goal.
-/

namespace HTN

namespace Syn

open TaskNetwork

/-! ### The gadget -/

/-- A **named step**: a compound task name together with the precondition, add and delete list
of the action it decomposes into. -/
abbrev StepEntry : Type := ℕ × List ℕ × List ℕ × List ℕ

/-- The **step domain** of a list of named steps: one action per entry, and one method
decomposing that entry's compound name into it. -/
def stepDom (P : List StepEntry) : DomDesc :=
  ((List.range P.length).map fun m => (m, (P.getI m).2.1, (P.getI m).2.2.1, (P.getI m).2.2.2),
    (List.range P.length).map fun m =>
      ((P.getI m).1, (([0], [], [(0, false, m)]) : TnDesc)))

/-- The **step instance**: the facts `L` hold initially, the goal is `G`, and the initial task
network is the chain of the compound tasks `S`. -/
def stepInst (S L G : List ℕ) : InstDesc := (L, G, chainTnDesc S)

variable {P : List StepEntry} {S L G : List ℕ}

@[simp] theorem stepDom_methods :
    (stepDom P).methods =
      (List.range P.length).map fun m =>
        ((P.getI m).1, (([0], [], [(0, false, m)]) : TnDesc)) := rfl

@[simp] theorem stepDom_actions :
    (stepDom P).actions =
      (List.range P.length).map fun m =>
        (m, (P.getI m).2.1, (P.getI m).2.2.1, (P.getI m).2.2.2) := rfl

@[simp] theorem stepInst_initList : (stepInst S L G).initList = L := rfl

@[simp] theorem stepInst_goalList : (stepInst S L G).goalList = G := rfl

@[simp] theorem stepInst_tnI : (stepInst S L G).tnI = chainTnDesc S := rfl

theorem length_stepDom_methods : (stepDom P).methods.length = P.length := by simp

/-! ### The gadget lies in the classes -/

theorem stepDom_method_mem {e : MethodDesc} (he : e ∈ (stepDom P).methods) :
    ∃ m, e = ((P.getI m).1, (([0], [], [(0, false, m)]) : TnDesc)) := by
  simp only [stepDom_methods, List.mem_map, List.mem_range] at he
  obtain ⟨m, -, rfl⟩ := he
  exact ⟨m, rfl⟩

theorem stepDom_methodsTO : (stepDom P).MethodsTO := by
  intro e he
  obtain ⟨m, rfl⟩ := stepDom_method_mem he
  intro x hx y hy hxy
  exact absurd ((testDom_mem_T hx).trans (testDom_mem_T hy).symm) hxy

theorem stepDom_methodsReg : (stepDom P).MethodsReg := by
  intro e he
  obtain ⟨m, rfl⟩ := stepDom_method_mem he
  refine ⟨fun x hx y hy _ _ => (testDom_mem_T hx).trans (testDom_mem_T hy).symm,
    fun x hx hax y _ _ => ?_⟩
  exact absurd (show (TnDesc.toTaskNetwork (([0], [], [(0, false, m)]) : TnDesc)).IsAbstractId 0
    from testDom_mem_T hx ▸ hax) testDom_not_abstract

theorem stepDom_isAcyclic : (stepDom P).IsAcyclic := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he t ht c hc
  obtain ⟨m, rfl⟩ := stepDom_method_mem he
  exact absurd (show (TnDesc.toTaskNetwork (([0], [], [(0, false, m)]) : TnDesc)).IsAbstractId 0
    from ⟨c, testDom_mem_T ht ▸ hc⟩) testDom_not_abstract

theorem stepDom_isTailRec : (stepDom P).IsTailRec :=
  SynClass.isAcyclic_isTailRec stepDom_isAcyclic

theorem stepInst_isTO : (stepInst S L G).IsTO :=
  (chainTnDesc_isSeqNet (S := S)).isTotallyOrdered

/-! ### The bodies, the preconditions and the effects -/

/-- The head of the `m`-th method of a step domain is the name of the `m`-th step. -/
theorem hd_stepDom {m : ℕ} (h : m < P.length) : (stepDom P).hd m = (P.getI m).1 := by
  rw [DomDesc.hd, stepDom_methods, getI_range_map _ h]

/-- The body of the `m`-th method of a step domain is the single primitive task `m`. -/
theorem bd_stepDom {m : ℕ} (h : m < P.length) : (stepDom P).bd m = [Sum.inl m] := by
  rw [DomDesc.bd, stepDom_methods, getI_range_map _ h]
  rfl

theorem prec_stepDom {m : ℕ} (h : m < P.length) :
    (stepDom P).prec m = {f | f ∈ (P.getI m).2.1} := by
  have hlookup := lookup_range_map
    (fun j => ((P.getI j).2.1, (P.getI j).2.2.1, (P.getI j).2.2.2)) h
  simp only [DomDesc.prec, stepDom_actions]
  rw [hlookup]
  rfl

theorem add_stepDom {m : ℕ} (h : m < P.length) :
    (stepDom P).add m = {f | f ∈ (P.getI m).2.2.1} := by
  have hlookup := lookup_range_map
    (fun j => ((P.getI j).2.1, (P.getI j).2.2.1, (P.getI j).2.2.2)) h
  simp only [DomDesc.add, stepDom_actions]
  rw [hlookup]
  rfl

theorem del_stepDom {m : ℕ} (h : m < P.length) :
    (stepDom P).del m = {f | f ∈ (P.getI m).2.2.2} := by
  have hlookup := lookup_range_map
    (fun j => ((P.getI j).2.1, (P.getI j).2.2.1, (P.getI j).2.2.2)) h
  simp only [DomDesc.del, stepDom_actions]
  rw [hlookup]
  rfl

/-- Looking up an index beyond the range in a list indexed by `List.range`. -/
theorem lookup_range_map_none {β : Type} (f : ℕ → β) {n m : ℕ} (h : n ≤ m) :
    ((List.range n).map (fun j => (j, f j))).lookup m = none := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.lookup_append, ih (by omega)]
    have hne : (m == n) = false := by simp; omega
    simp [List.lookup_cons, hne]

theorem prec_stepDom_of_le {m : ℕ} (h : P.length ≤ m) : (stepDom P).prec m = ∅ := by
  simp only [DomDesc.prec, stepDom_actions]
  rw [lookup_range_map_none (fun j => ((P.getI j).2.1, (P.getI j).2.2.1, (P.getI j).2.2.2)) h]
  simp

theorem add_stepDom_of_le {m : ℕ} (h : P.length ≤ m) : (stepDom P).add m = ∅ := by
  simp only [DomDesc.add, stepDom_actions]
  rw [lookup_range_map_none (fun j => ((P.getI j).2.1, (P.getI j).2.2.1, (P.getI j).2.2.2)) h]
  simp

theorem del_stepDom_of_le {m : ℕ} (h : P.length ≤ m) : (stepDom P).del m = ∅ := by
  simp only [DomDesc.del, stepDom_actions]
  rw [lookup_range_map_none (fun j => ((P.getI j).2.1, (P.getI j).2.2.1, (P.getI j).2.2.2)) h]
  simp

/-! ### Refinements of the chain -/

/-- The refinements of a single compound task of a step domain are the one-element action
sequences of the steps carrying that name. -/
theorem yieldSeq_stepDom_singleton {c : ℕ} {as : List ℕ} :
    (stepDom P).toDomain.YieldSeq [Sum.inr c] as ↔
      ∃ m, m < P.length ∧ (P.getI m).1 = c ∧ as = [m] := by
  constructor
  · intro h
    cases h with
    | comp hm h =>
      obtain ⟨m, hm', hhd, hbd⟩ := (DomDesc.seqBody_iff stepDom_methodsTO).1 hm
      rw [length_stepDom_methods] at hm'
      rw [bd_stepDom hm'] at hbd
      subst hbd
      rw [List.append_nil] at h
      cases h with
      | prim h =>
        cases h
        exact ⟨m, hm', by rw [← hd_stepDom hm']; exact hhd, rfl⟩
  · rintro ⟨m, hm, hname, rfl⟩
    refine Domain.YieldSeq.comp (bs := [Sum.inl m]) ?_ ?_
    · refine (DomDesc.seqBody_iff stepDom_methodsTO).2 ⟨m, ?_, ?_, bd_stepDom hm⟩
      · rwa [length_stepDom_methods]
      · rw [hd_stepDom hm]; exact hname
    · simpa using Domain.YieldSeq.prim (as := []) Domain.YieldSeq.nil

/-- The refinements of a chain of compound tasks of a step domain are the sequences of chosen
steps. -/
theorem yieldSeq_stepDom_chain {as : List ℕ} :
    (stepDom P).toDomain.YieldSeq (S.map Sum.inr) as ↔
      List.Forall₂ (fun c m => m < P.length ∧ (P.getI m).1 = c) S as := by
  induction S generalizing as with
  | nil =>
    constructor
    · intro h
      cases h
      exact List.Forall₂.nil
    · intro h
      cases h
      exact Domain.YieldSeq.nil
  | cons c S ih =>
    constructor
    · intro h
      rw [List.map_cons, show (Sum.inr c :: S.map Sum.inr) = [Sum.inr c] ++ S.map Sum.inr from
        rfl] at h
      obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h.split
      obtain ⟨m, hm, hname, rfl⟩ := yieldSeq_stepDom_singleton.1 h₁
      exact List.Forall₂.cons ⟨hm, hname⟩ (ih.1 h₂)
    · intro h
      obtain ⟨m, as', hcm, hrest, rfl⟩ :
          ∃ m as', (m < P.length ∧ (P.getI m).1 = c) ∧
            List.Forall₂ (fun c m => m < P.length ∧ (P.getI m).1 = c) S as' ∧ as = m :: as' := by
        cases h with
        | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
      rw [List.map_cons, show (Sum.inr c :: S.map Sum.inr) = [Sum.inr c] ++ S.map Sum.inr from
        rfl, show (m :: as') = [m] ++ as' from rfl]
      exact Domain.YieldSeq.append (yieldSeq_stepDom_singleton.2 ⟨m, hcm.1, hcm.2, rfl⟩)
        (ih.2 hrest)

/-! ### Solvability of the gadget -/

/-- **The step-chain gadget is solvable exactly when some choice of one step per task of the
chain is applicable in the initial state and reaches the goal.** -/
theorem solvable_step_iff :
    Solvable (stepDom P) (stepInst S L G) ↔
      ∃ as : List ℕ, List.Forall₂ (fun c m => m < P.length ∧ (P.getI m).1 = c) S as ∧
        (stepDom P).toDomain.SeqApplicable as {f | f ∈ L} ∧
        ∀ f ∈ G, f ∈ (stepDom P).toDomain.transitionSeq as {f | f ∈ L} := by
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (stepDom P) (stepInst S L G))
    (isTO_problem stepDom_methodsTO stepInst_isTO).2
    (l₀ := (List.range S.length).map (Nat.pair 0)) (xs₀ := S.map Sum.inr)
    chainTnDesc_isSeqNet
  rw [show Solvable (stepDom P) (stepInst S L G) = (problem (stepDom P) (stepInst S L G)).Solvable
    from rfl, hnorm]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    exact ⟨as, yieldSeq_stepDom_chain.1 hy, happ, fun f hf => hgoal hf⟩
  · rintro ⟨as, hf, happ, hgoal⟩
    exact ⟨as, yieldSeq_stepDom_chain.2 hf, happ, fun f hf => hgoal f hf⟩

end Syn

end HTN
