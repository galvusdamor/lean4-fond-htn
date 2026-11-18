import HtnComplexity.Computable.Guard
import HtnComplexity.Computable.GridDesc
import HtnPlanning.Interleave.ChainPrefix
/-!
# The test-chain gadget: what an instance can say through its task network

The guard gadget of `HtnComplexity/Computable/Guard.lean` is the simplest described problem
that reads a state: its instance transmits a list of facts, and the domain answers the
*disjunction* of its guards.  Its initial task network is a single compound task, so the only
channel from the instance to the domain is the initial state.

A described instance has a second channel, which the classes of the table leave free for every
target class except the `STRIPS` one: **its initial task network**.  This file formalises what
that channel can carry.

* `HTN.Syn.testDom P` — the **test domain** of a list `P` of *named tests* `(c, p)`: one
  effect-free action per entry, with the precondition `p`, and one method decomposing the
  compound task `c` into it.  Several entries may carry the same name `c`, and those are the
  alternatives the planner may choose between.
* `HTN.Syn.testInst S L` — the **test instance**: the facts `L` hold initially, there is no
  goal, and the initial task network is the *chain* of the compound tasks `S`.
* `HTN.Syn.solvable_test_iff` — the gadget is solvable exactly when **every** name the instance
  lists has *some* test that the state satisfies:

      Solvable (testDom P) (testInst S L) ↔
        ∀ c ∈ S, ∃ m < P.length, (P.getI m).1 = c ∧ ∀ f ∈ (P.getI m).2, f ∈ L

  so the instance selects, through its task network, a **conjunction of disjunctions** of the
  tests the domain provides — one conjunct per task, and a name for which the domain has no
  method makes the problem unsolvable.  The guard gadget is the special case of a single task
  and a single name (`HTN.Syn.solvable_guard_iff` is `solvable_test_iff` for `S = [0]`).

The gadget is totally ordered, regular and acyclic, so it lies in every class of the table
except the two `NOOP` ones; unlike the guard gadget its instance is **not** rooted, which is
exactly the point — the number of conjuncts is bounded by the size of the *instance*, not of the
domain.
-/

namespace HTN

namespace Syn

open TaskNetwork

/-! ### The gadget -/

/-- The **test domain** of a list of named tests: one effect-free action per entry, with that
entry's precondition, and one method decomposing that entry's compound task name into it. -/
def testDom (P : List (ℕ × List ℕ)) : DomDesc :=
  ((List.range P.length).map fun m => (m, (P.getI m).2, ([] : List ℕ), ([] : List ℕ)),
    (List.range P.length).map fun m =>
      ((P.getI m).1, (([0], [], [(0, false, m)]) : TnDesc)))

/-- The description of a **chain** of compound tasks. -/
def chainTnDesc (S : List ℕ) : TnDesc := gridDesc [S.map fun c => (true, c)]

/-- The **test instance**: the facts `L` hold initially, there is no goal, and the initial task
network is the chain of the compound tasks `S`. -/
def testInst (S L : List ℕ) : InstDesc := (L, [], chainTnDesc S)

variable {P : List (ℕ × List ℕ)} {S L : List ℕ}

@[simp] theorem testDom_methods :
    (testDom P).methods =
      (List.range P.length).map fun m =>
        ((P.getI m).1, (([0], [], [(0, false, m)]) : TnDesc)) := rfl

@[simp] theorem testDom_actions :
    (testDom P).actions =
      (List.range P.length).map fun m =>
        (m, (P.getI m).2, ([] : List ℕ), ([] : List ℕ)) := rfl

@[simp] theorem testInst_initList : (testInst S L).initList = L := rfl

@[simp] theorem testInst_goalList : (testInst S L).goalList = [] := rfl

@[simp] theorem testInst_tnI : (testInst S L).tnI = chainTnDesc S := rfl

theorem length_testDom_methods : (testDom P).methods.length = P.length := by simp

/-! ### The gadget lies in the classes -/

/-- The subtask network of a method of a test domain has the single identifier `0`, labelled
with an action. -/
theorem testDom_method_mem {e : MethodDesc} (he : e ∈ (testDom P).methods) :
    ∃ m, e = ((P.getI m).1, (([0], [], [(0, false, m)]) : TnDesc)) := by
  simp only [testDom_methods, List.mem_map, List.mem_range] at he
  obtain ⟨m, -, rfl⟩ := he
  exact ⟨m, rfl⟩

theorem testDom_mem_T {m x : ℕ}
    (hx : x ∈ (TnDesc.toTaskNetwork (([0], [], [(0, false, m)]) : TnDesc)).T) : x = 0 := by
  simpa [TnDesc.toTaskNetwork, TnDesc.ids] using hx

theorem testDom_not_abstract {m : ℕ} :
    ¬ (TnDesc.toTaskNetwork (([0], [], [(0, false, m)]) : TnDesc)).IsAbstractId 0 := by
  rintro ⟨c, hc⟩
  simp [TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl] at hc

theorem testDom_methodsTO : (testDom P).MethodsTO := by
  intro e he
  obtain ⟨m, rfl⟩ := testDom_method_mem he
  intro x hx y hy hxy
  exact absurd ((testDom_mem_T hx).trans (testDom_mem_T hy).symm) hxy

theorem testDom_methodsReg : (testDom P).MethodsReg := by
  intro e he
  obtain ⟨m, rfl⟩ := testDom_method_mem he
  refine ⟨fun x hx y hy _ _ => (testDom_mem_T hx).trans (testDom_mem_T hy).symm,
    fun x hx hax y _ _ => ?_⟩
  exact absurd (show (TnDesc.toTaskNetwork (([0], [], [(0, false, m)]) : TnDesc)).IsAbstractId 0
    from testDom_mem_T hx ▸ hax) testDom_not_abstract

theorem testDom_isAcyclic : (testDom P).IsAcyclic := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he t ht c hc
  obtain ⟨m, rfl⟩ := testDom_method_mem he
  exact absurd (show (TnDesc.toTaskNetwork (([0], [], [(0, false, m)]) : TnDesc)).IsAbstractId 0
    from ⟨c, testDom_mem_T ht ▸ hc⟩) testDom_not_abstract

theorem testDom_isTailRec : (testDom P).IsTailRec :=
  SynClass.isAcyclic_isTailRec testDom_isAcyclic

/-! ### The bodies and the preconditions -/

/-- The head of the `m`-th method of a test domain is the name of the `m`-th test. -/
theorem hd_testDom {m : ℕ} (h : m < P.length) : (testDom P).hd m = (P.getI m).1 := by
  rw [DomDesc.hd, testDom_methods, getI_range_map _ h]

/-- The body of the `m`-th method of a test domain is the single primitive task `m`. -/
theorem bd_testDom {m : ℕ} (h : m < P.length) : (testDom P).bd m = [Sum.inl m] := by
  rw [DomDesc.bd, testDom_methods, getI_range_map _ h]
  rfl

/-- The precondition of the `m`-th action of a test domain is the `m`-th test. -/
theorem prec_testDom {m : ℕ} (h : m < P.length) :
    (testDom P).prec m = {f | f ∈ (P.getI m).2} := by
  have hlookup := lookup_range_map (fun j => ((P.getI j).2, ([] : List ℕ), ([] : List ℕ))) h
  simp only [DomDesc.prec, testDom_actions]
  rw [hlookup]
  rfl

/-! ### The chain description -/

theorem cellIds_chain :
    cellIds [S.map fun c => (true, c)] = (List.range S.length).map (Nat.pair 0) := by
  simp [cellIds, gridRow]

theorem gridRow_chain : gridRow [S.map fun c => (true, c)] 0 = S.map fun c => (true, c) := rfl

/-- The label of the `j`-th task of a chain description is the `j`-th name. -/
theorem label_chainTnDesc {j : ℕ} (hj : j < S.length) :
    (chainTnDesc S).label (Nat.pair 0 j) = Sum.inr (S.getI j) := by
  have hj' : j < (gridRow [S.map fun c => (true, c)] 0).length := by
    rw [gridRow_chain]; simpa using hj
  have hlk := lookup_cellLbl (ls := [S.map fun c => (true, c)]) (i := 0) (j := j) (by simp) hj'
  have hval : (gridRow [S.map fun c => (true, c)] 0).getD j (false, 0) = (true, S.getI j) := by
    rw [gridRow_chain]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem hj]
    simp [List.getI_eq_getElem _ hj]
  rw [TnDesc.label]
  simp only [chainTnDesc, gridDesc_lbl] at *
  rw [hlk, hval]

/-- **A chain description is a sequence network**: its tasks, enumerated in the order of `S`,
carry the names `S`. -/
theorem chainTnDesc_isSeqNet :
    (chainTnDesc S).toTaskNetwork.IsSeqNet ((List.range S.length).map (Nat.pair 0))
      (S.map Sum.inr) := by
  have hids : (chainTnDesc S).ids = (List.range S.length).map (Nat.pair 0) := by
    rw [chainTnDesc, gridDesc_ids, cellIds_chain]
  have hnd : ((List.range S.length).map (Nat.pair 0)).Nodup := by
    refine List.Nodup.map (fun x y h => ?_) List.nodup_range
    exact (Nat.pair_eq_pair.1 h).2
  have hmem : ∀ t, t ∈ (chainTnDesc S).toTaskNetwork.T ↔
      t ∈ (List.range S.length).map (Nat.pair 0) := by
    intro t
    rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, hids]
  have hpair : ((List.range S.length).map (Nat.pair 0)).Pairwise
      (chainTnDesc S).toTaskNetwork.ord := by
    rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro j j' hj hj' hlt
    have hjS : j < S.length := by simpa using hj
    have hj'S : j' < S.length := by simpa using hj'
    simp only [List.getElem_range]
    rw [chainTnDesc, gridDesc_ord]
    exact ⟨0, j, j', by simp, hlt, by rw [gridRow_chain]; simpa using hj'S, rfl, rfl⟩
  have hseq := TaskNetwork.isSeqNet_of_pairwise_ord (tn := (chainTnDesc S).toTaskNetwork)
    (l := (List.range S.length).map (Nat.pair 0)) (TnDesc.toTaskNetwork_wf _) hnd hmem hpair
  have hmapeq : ((List.range S.length).map (Nat.pair 0)).map
      (chainTnDesc S).toTaskNetwork.α = S.map Sum.inr := by
    rw [List.map_map]
    refine List.ext_getElem (by simp) (fun j h1 h2 => ?_)
    have hj : j < S.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [TnDesc.toTaskNetwork_α, label_chainTnDesc hj, List.getI_eq_getElem _ hj]
  rwa [hmapeq] at hseq

theorem testInst_isTO : (testInst S L).IsTO :=
  (chainTnDesc_isSeqNet (S := S)).isTotallyOrdered

/-! ### Solvability of the gadget -/

/-- The refinements of a single compound task of a test domain are the one-element action
sequences of the tests carrying that name. -/
theorem yieldSeq_testDom_singleton {c : ℕ} {as : List ℕ} :
    (testDom P).toDomain.YieldSeq [Sum.inr c] as ↔
      ∃ m, m < P.length ∧ (P.getI m).1 = c ∧ as = [m] := by
  constructor
  · intro h
    cases h with
    | comp hm h =>
      obtain ⟨m, hm', hhd, hbd⟩ := (DomDesc.seqBody_iff testDom_methodsTO).1 hm
      rw [length_testDom_methods] at hm'
      rw [bd_testDom hm'] at hbd
      subst hbd
      rw [List.append_nil] at h
      cases h with
      | prim h =>
        cases h
        exact ⟨m, hm', by rw [← hd_testDom hm']; exact hhd, rfl⟩
  · rintro ⟨m, hm, hname, rfl⟩
    refine Domain.YieldSeq.comp (bs := [Sum.inl m]) ?_ ?_
    · refine (DomDesc.seqBody_iff testDom_methodsTO).2 ⟨m, ?_, ?_, bd_testDom hm⟩
      · rwa [length_testDom_methods]
      · rw [hd_testDom hm]; exact hname
    · simpa using Domain.YieldSeq.prim (as := []) Domain.YieldSeq.nil

/-- The refinements of a chain of compound tasks of a test domain are the sequences of chosen
tests. -/
theorem yieldSeq_testDom_chain {as : List ℕ} :
    (testDom P).toDomain.YieldSeq (S.map Sum.inr) as ↔
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
      obtain ⟨m, hm, hname, rfl⟩ := yieldSeq_testDom_singleton.1 h₁
      exact List.Forall₂.cons ⟨hm, hname⟩ (ih.1 h₂)
    · intro h
      obtain ⟨m, as', hcm, hrest, rfl⟩ :
          ∃ m as', (m < P.length ∧ (P.getI m).1 = c) ∧
            List.Forall₂ (fun c m => m < P.length ∧ (P.getI m).1 = c) S as' ∧ as = m :: as' := by
        cases h with
        | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
      rw [List.map_cons, show (Sum.inr c :: S.map Sum.inr) = [Sum.inr c] ++ S.map Sum.inr from
        rfl, show (m :: as') = [m] ++ as' from rfl]
      exact Domain.YieldSeq.append (yieldSeq_testDom_singleton.2 ⟨m, hcm.1, hcm.2, rfl⟩) (ih.2 hrest)

/-- Every task of the chain is served by one of the chosen tests. -/
theorem exists_mem_of_forall₂_testDom {T as : List ℕ}
    (h : List.Forall₂ (fun c m => m < P.length ∧ (P.getI m).1 = c) T as) :
    ∀ c ∈ T, ∃ m, m ∈ as ∧ m < P.length ∧ (P.getI m).1 = c := by
  induction h with
  | nil => simp
  | @cons c m T as' hcm hrest ih =>
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc''
    · exact ⟨m, by simp, hcm.1, hcm.2⟩
    · obtain ⟨m', hm', h'⟩ := ih c' hc''
      exact ⟨m', by simp [hm'], h'⟩

/-- **The test-chain gadget is solvable exactly when every task the instance lists has a test
that the initial state satisfies.** -/
theorem solvable_test_iff :
    Solvable (testDom P) (testInst S L) ↔
      ∀ c ∈ S, ∃ m, m < P.length ∧ (P.getI m).1 = c ∧ ∀ f ∈ (P.getI m).2, f ∈ L := by
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (testDom P) (testInst S L))
    (isTO_problem testDom_methodsTO testInst_isTO).2
    (l₀ := (List.range S.length).map (Nat.pair 0)) (xs₀ := S.map Sum.inr)
    chainTnDesc_isSeqNet
  rw [show Solvable (testDom P) (testInst S L) = (problem (testDom P) (testInst S L)).Solvable
    from rfl, hnorm]
  -- an effect-free plan of tests leaves the state unchanged
  have hstay : ∀ (T : List ℕ) (as : List ℕ),
      List.Forall₂ (fun c m => m < P.length ∧ (P.getI m).1 = c) T as →
      (problem (testDom P) (testInst S L)).transitionSeq as
          {f | f ∈ (testInst S L).initList} = {f | f ∈ L} ∧
        ((problem (testDom P) (testInst S L)).SeqApplicable as
            {f | f ∈ (testInst S L).initList} ↔
          ∀ m ∈ as, ∀ f ∈ (P.getI m).2, f ∈ L) := by
    intro T as h
    induction h with
    | nil => simp [ActionModel.transitionSeq, ActionModel.SeqApplicable]
    | @cons c m T as hcm hrest ih =>
      have hlookup := lookup_range_map (fun j => ((P.getI j).2, ([] : List ℕ), ([] : List ℕ)))
        hcm.1
      have hadd : (problem (testDom P) (testInst S L)).add m = ∅ := by
        simp only [problem_add, DomDesc.add, testDom_actions]
        rw [hlookup]
        simp
      have hdel : (problem (testDom P) (testInst S L)).del m = ∅ := by
        simp only [problem_del, DomDesc.del, testDom_actions]
        rw [hlookup]
        simp
      have hstep : (problem (testDom P) (testInst S L)).transition m {f | f ∈ L} = {f | f ∈ L} :=
        by simp [ActionModel.transition, hadd, hdel]
      have hprec : (problem (testDom P) (testInst S L)).prec m = {f | f ∈ (P.getI m).2} := by
        rw [problem_prec, prec_testDom hcm.1]
      have hinit : {f | f ∈ (testInst S L).initList} = {f | f ∈ L} := rfl
      rw [hinit, ActionModel.transitionSeq_cons, hstep]
      rw [hinit] at ih
      refine ⟨ih.1, ?_⟩
      have happ_iff : (problem (testDom P) (testInst S L)).Applicable m {f | f ∈ L} ↔
          ∀ f ∈ (P.getI m).2, f ∈ L := by
        rw [ActionModel.Applicable, hprec]
        exact Iff.rfl
      rw [ActionModel.seqApplicable_cons, hstep, ih.2, happ_iff]
      constructor
      · rintro ⟨h1, h2⟩ x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact h1
        · exact h2 x hx'
      · intro h
        exact ⟨fun f hf => h m (by simp) f hf, fun x hx => h x (by simp [hx])⟩
  constructor
  · rintro ⟨as, hy, happ, -⟩
    have hf := yieldSeq_testDom_chain.1 hy
    obtain ⟨-, happ'⟩ := hstay S as hf
    have hall := happ'.1 happ
    intro c hc
    obtain ⟨m, hmem, hlt, hname⟩ := exists_mem_of_forall₂_testDom hf c hc
    exact ⟨m, hlt, hname, hall m hmem⟩
  · intro h
    -- choose a test for every task of the chain
    obtain ⟨as, hf⟩ : ∃ as, List.Forall₂
        (fun c m => (m < P.length ∧ (P.getI m).1 = c) ∧ ∀ f ∈ (P.getI m).2, f ∈ L) S as := by
      refine (Domain.exists_forall₂_iff).2 fun c hc => ?_
      obtain ⟨m, hm, hname, hsat⟩ := h c hc
      exact ⟨m, ⟨hm, hname⟩, hsat⟩
    obtain ⟨hf1, hf2⟩ := (Domain.forall₂_and_mem_iff
      (p := fun m => ∀ f ∈ (P.getI m).2, f ∈ L)).2 hf
    obtain ⟨hstate, happ⟩ := hstay S as hf1
    refine ⟨as, yieldSeq_testDom_chain.2 hf1, happ.2 hf2, ?_⟩
    intro f hf'
    simp only [problem_goal, testInst_goalList, Set.mem_setOf_eq, List.not_mem_nil] at hf'

/-! ### The gadget is not vacuous

Three checks on the domain with the two tests `5 ↦ [1]`, `5 ↦ [2]` and the test `7 ↦ []`. -/

/-- Both tasks are served: `5` by the test requiring the fact `1`, and `7` by the empty test. -/
example : Solvable (testDom [(5, [1]), (5, [2]), (7, [])]) (testInst [5, 7] [1]) := by
  rw [solvable_test_iff]
  decide

/-- A task whose name heads no method makes the problem unsolvable. -/
example : ¬ Solvable (testDom [(5, [1]), (5, [2]), (7, [])]) (testInst [5, 9] [1]) := by
  rw [solvable_test_iff]
  decide

/-- A task none of whose tests is satisfied makes the problem unsolvable. -/
example : ¬ Solvable (testDom [(5, [1]), (5, [2]), (7, [])]) (testInst [5, 7] [3]) := by
  rw [solvable_test_iff]
  decide

end Syn

end HTN
