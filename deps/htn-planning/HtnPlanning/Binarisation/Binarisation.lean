import HtnPlanning.Core.TONormalForm
import HtnPlanning.Core.Construction
/-!
# Binarisation: totally ordered methods with at most two subtasks

The proof-tuple characterisation of totally ordered HTN planning
(`HtnPlanning/Core/ProofTuples.lean`, `HTN.Domain.provable_iff_yield`) and the compilation of
totally ordered problems into acyclic ones (`HtnComplexity/ToHtnAc/ToHtnAc.lean`) assume, following
the source, that every method has **at most two subtasks** — "which can always be obtained by a
linear compilation".  This file formalises that compilation and proves it correct.

The construction is the usual binarisation (right-linearisation) of a context-free grammar.  The
compound task names of the compiled domain are

* `Sum.inl c` for a compound task name `c` of the source domain, and
* `Sum.inr bs` for a *task sequence* `bs` of the source domain (in practice a suffix of a method
  body),

and its methods are

* `⟨c⟩ ↦ ⟨bs⟩` for every method `c ↦ bs` of the source domain (one subtask),
* `⟨[]⟩ ↦ ε` (no subtask), and
* `⟨x :: bs⟩ ↦ x ⟨bs⟩` for every task `x` and every task sequence `bs` (two subtasks).

All subtask networks are totally ordered chains (`TaskNetwork.seq`), so the compiled problem is
totally ordered, and every method has at most two subtasks (`Bin.card_subtasks_le`).

The main results are

* `HTN.Bin.yieldSeq_iff` — the compiled domain refines `⟨xs⟩` into exactly the action sequences
  into which the source domain refines the task sequence `xs`;
* `HTN.Bin.solvable_iff` — the compiled problem is solvable iff the source problem is;
* `HTN.Bin.solvable_iff_provable` — consequently, **solvability of an arbitrary well-formed
  totally ordered HTN problem is characterised by the proof tuples** of the binarised domain,
  with no assumption on the number of subtasks of its methods.
-/

namespace HTN

universe u v w x

namespace TaskNetwork

variable {A : Type v} {C : Type w} [Inhabited A]

/-- The identifiers of the chain network `TaskNetwork.seq l`, in their order. -/
def seqIds (n : ℕ) : List (ℕ × ℕ) := (List.range n).map fun j => (0, j)

@[simp] lemma length_seqIds (n : ℕ) : (seqIds n).length = n := by simp [seqIds]

@[simp] lemma mem_seqIds {n : ℕ} {p : ℕ × ℕ} : p ∈ seqIds n ↔ p.1 = 0 ∧ p.2 < n := by
  obtain ⟨i, j⟩ := p
  constructor
  · intro h
    simp only [seqIds, List.mem_map, List.mem_range] at h
    obtain ⟨k, hk, hk2⟩ := h
    cases hk2
    exact ⟨rfl, hk⟩
  · rintro ⟨rfl, hj⟩
    simp only [seqIds, List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩

lemma nodup_seqIds (n : ℕ) : (seqIds n).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro x _ y _ hxy
  simpa using hxy

lemma getElem_seqIds {n j : ℕ} (h : j < n) : (seqIds n)[j]'(by simpa using h) = (0, j) := by
  simp [seqIds]

lemma pairwise_ord_seqIds (l : List (A ⊕ C)) : (seqIds l.length).Pairwise (seq l).ord := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [length_seqIds] at hi hj
  rw [getElem_seqIds hi, getElem_seqIds hj]
  exact ⟨rfl, hij, by simpa [seq] using hj⟩

lemma map_α_seqIds (l : List (A ⊕ C)) : (seqIds l.length).map (seq l).α = l := by
  refine List.ext_getElem (by simp) ?_
  intro j h1 h2
  have hj : j < l.length := by simpa using h2
  rw [List.getElem_map, getElem_seqIds hj, seq_α hj]

/-- **The chain network of a task list is the corresponding sequence network.** -/
lemma seq_isSeqNet (l : List (A ⊕ C)) : (seq l).IsSeqNet (seqIds l.length) l := by
  have h := isSeqNet_of_pairwise_ord (tn := seq l) seq_wf (nodup_seqIds _)
    (fun p => by rw [mem_seq_T, mem_seqIds]) (pairwise_ord_seqIds l)
  rwa [map_α_seqIds] at h

/-- The method whose subtask network is a chain has exactly that chain as its body. -/
lemma hasSeqBody_seq_iff {C : Type w} {c : C} {l bs : List (A ⊕ C)} :
    (Method.mk c (seq l)).HasSeqBody bs ↔ bs = l :=
  Method.hasSeqBody_iff_of_isSeqNet (seq_isSeqNet l)

@[simp] lemma card_seq_T (l : List (A ⊕ C)) : (seq l).T.card = l.length := by
  classical
  have : (seq l).T = (seqIds l.length).toFinset := by
    ext p
    rw [mem_seq_T, List.mem_toFinset, mem_seqIds]
  rw [this, List.toFinset_card_of_nodup (nodup_seqIds _), length_seqIds]

end TaskNetwork

namespace Bin

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [Inhabited A]

open TaskNetwork

/-- The compound task names of the binarised domain: those of the source domain, plus one name
per task sequence of the source domain. -/
abbrev Name (A : Type v) (C : Type w) : Type max v w := C ⊕ List (A ⊕ C)

/-- The embedding of source tasks into tasks of the binarised domain. -/
def emb : (A ⊕ C) → (A ⊕ Name A C)
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (Sum.inl c)

/-- The task sequence of the source domain denoted by a task of the binarised domain. -/
def back : (A ⊕ Name A C) → List (A ⊕ C)
  | Sum.inl a => [Sum.inl a]
  | Sum.inr (Sum.inl c) => [Sum.inr c]
  | Sum.inr (Sum.inr bs) => bs

omit [Inhabited A] in
@[simp] lemma back_emb (x : A ⊕ C) : back (emb x) = [x] := by
  cases x <;> rfl

omit [Inhabited A] in
@[simp] lemma back_tuple (bs : List (A ⊕ C)) :
    back (Sum.inr (Sum.inr bs) : A ⊕ Name A C) = bs := rfl

omit [Inhabited A] in
@[simp] lemma flatMap_back_map_emb (xs : List (A ⊕ C)) : (xs.map emb).flatMap back = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The method of the binarised domain that consumes the first task of a task sequence:
`⟨[]⟩ ↦ ε` for the empty sequence and `⟨x bs⟩ ↦ x ⟨bs⟩` for a non-empty one. -/
def methodOf : List (A ⊕ C) → Method (ℕ × ℕ) A (Name A C)
  | [] => ⟨Sum.inr ([] : List (A ⊕ C)), seq []⟩
  | x :: bs => ⟨Sum.inr (x :: bs), seq [emb x, Sum.inr (Sum.inr bs)]⟩

/-- The methods of the binarised domain, restricted to the set `S` of task sequences: the
methods `⟨c⟩ ↦ ⟨bs⟩` for the methods `c ↦ bs` of the source domain with `bs ∈ S`, and the
methods `HTN.Bin.methodOf bs` for `bs ∈ S`. -/
def methodsOn (D : Domain F A C I) (S : Set (List (A ⊕ C))) :
    Set (Method (ℕ × ℕ) A (Name A C)) :=
  {m | (∃ c bs, D.SeqBody c bs ∧ bs ∈ S ∧ m = ⟨Sum.inl c, seq [Sum.inr (Sum.inr bs)]⟩) ∨
    (∃ bs ∈ S, m = methodOf bs)}

/-- The binarised domain restricted to the task sequences `S`. -/
def domainOn (D : Domain F A C I) (S : Set (List (A ⊕ C))) : Domain F A (Name A C) (ℕ × ℕ) where
  toActionModel := D.toActionModel
  methods := methodsOn D S

/-- The methods of the binarised domain (all task sequences are allowed). -/
def methods (D : Domain F A C I) : Set (Method (ℕ × ℕ) A (Name A C)) :=
  methodsOn D Set.univ

/-- The binarised domain. -/
def domain (D : Domain F A C I) : Domain F A (Name A C) (ℕ × ℕ) := domainOn D Set.univ

@[simp] lemma domainOn_methods (D : Domain F A C I) (S : Set (List (A ⊕ C))) :
    (domainOn D S).methods = methodsOn D S := rfl

@[simp] lemma domainOn_toActionModel (D : Domain F A C I) (S : Set (List (A ⊕ C))) :
    (domainOn D S).toActionModel = D.toActionModel := rfl

@[simp] lemma domain_methods (D : Domain F A C I) : (domain D).methods = methods D := rfl

@[simp] lemma domain_eq (D : Domain F A C I) : domain D = domainOn D Set.univ := rfl

/-- A set `S` of task sequences is *adequate* for the source domain `D` if it contains the
empty sequence and all method bodies of `D`, and is closed under taking the tail.  It then
contains every suffix of every method body, which is all the binarisation ever needs. -/
structure Covers (D : Domain F A C I) (S : Set (List (A ⊕ C))) : Prop where
  /-- The empty task sequence belongs to `S`. -/
  nil : [] ∈ S
  /-- `S` is closed under taking the tail of a task sequence. -/
  tail : ∀ {x : A ⊕ C} {bs : List (A ⊕ C)}, (x :: bs) ∈ S → bs ∈ S
  /-- Every method body of the source domain belongs to `S`. -/
  body : ∀ {c : C} {bs : List (A ⊕ C)}, D.SeqBody c bs → bs ∈ S

omit [Inhabited A] in
/-- The set of all task sequences is adequate. -/
lemma covers_univ (D : Domain F A C I) : Covers D (Set.univ : Set (List (A ⊕ C))) where
  nil := trivial
  tail := fun _ => trivial
  body := fun _ => trivial

variable {S : Set (List (A ⊕ C))}

/-- Every method of the binarised domain has at most two subtasks. -/
theorem card_subtasks_le {D : Domain F A C I} {m : Method (ℕ × ℕ) A (Name A C)}
    (hm : m ∈ methodsOn D S) : m.subtasks.T.card ≤ 2 := by
  rcases hm with ⟨c, bs, -, -, rfl⟩ | ⟨bs, -, rfl⟩
  · simp
  · cases bs <;> simp [methodOf]

/-- All subtask networks of the binarised domain are well formed. -/
theorem subtasks_wf {D : Domain F A C I} {m : Method (ℕ × ℕ) A (Name A C)}
    (hm : m ∈ methodsOn D S) : m.subtasks.WF := by
  rcases hm with ⟨c, bs, -, -, rfl⟩ | ⟨bs, -, rfl⟩
  · exact seq_wf
  · cases bs <;> exact seq_wf

/-- All subtask networks of the binarised domain are totally ordered. -/
theorem subtasks_isTotallyOrdered {D : Domain F A C I} {m : Method (ℕ × ℕ) A (Name A C)}
    (hm : m ∈ methodsOn D S) : m.subtasks.IsTotallyOrdered := by
  rcases hm with ⟨c, bs, -, -, rfl⟩ | ⟨bs, -, rfl⟩
  · exact seq_isTotallyOrdered
  · cases bs <;> exact seq_isTotallyOrdered

/-- **The method bodies of the binarised domain.** -/
theorem seqBody_iff {D : Domain F A C I} {c' : Name A C} {bs' : List (A ⊕ Name A C)} :
    (domainOn D S).SeqBody c' bs' ↔
      (∃ c bs, c' = Sum.inl c ∧ D.SeqBody c bs ∧ bs ∈ S ∧ bs' = [Sum.inr (Sum.inr bs)]) ∨
      (c' = Sum.inr [] ∧ [] ∈ S ∧ bs' = []) ∨
      (∃ x bs, c' = Sum.inr (x :: bs) ∧ (x :: bs) ∈ S ∧ bs' = [emb x, Sum.inr (Sum.inr bs)]) := by
  constructor
  · rintro ⟨m, hm, hc, hbody⟩
    rcases hm with ⟨c, bs, hD, hS, rfl⟩ | ⟨bs, hS, rfl⟩
    · exact Or.inl ⟨c, bs, hc.symm ▸ rfl, hD, hS, hasSeqBody_seq_iff.1 hbody⟩
    · cases bs with
      | nil =>
          exact Or.inr (Or.inl ⟨hc.symm ▸ rfl, hS, hasSeqBody_seq_iff.1 hbody⟩)
      | cons x bs =>
          exact Or.inr (Or.inr ⟨x, bs, hc.symm ▸ rfl, hS, hasSeqBody_seq_iff.1 hbody⟩)
  · rintro (⟨c, bs, rfl, hD, hS, rfl⟩ | ⟨rfl, hS, rfl⟩ | ⟨x, bs, rfl, hS, rfl⟩)
    · exact ⟨_, Or.inl ⟨c, bs, hD, hS, rfl⟩, rfl, hasSeqBody_seq_iff.2 rfl⟩
    · exact ⟨_, Or.inr ⟨[], hS, rfl⟩, rfl, hasSeqBody_seq_iff.2 rfl⟩
    · exact ⟨_, Or.inr ⟨x :: bs, hS, rfl⟩, rfl, hasSeqBody_seq_iff.2 rfl⟩

/-! ### Correctness of the binarisation -/

variable {D : Domain F A C I}

/-- A task sequence of the source domain is refined by the corresponding compound task of the
binarised domain. -/
lemma yieldSeq_tuple_of_yieldSeq_map (hS : Covers D S) {bs : List (A ⊕ C)} (hbs : bs ∈ S)
    {as : List A} (h : (domainOn D S).YieldSeq (bs.map emb) as) :
    (domainOn D S).YieldSeq [Sum.inr (Sum.inr bs)] as := by
  induction bs generalizing as with
  | nil =>
      refine Domain.YieldSeq.comp (seqBody_iff.2 (Or.inr (Or.inl ⟨rfl, hbs, rfl⟩))) ?_
      simpa using h
  | cons x bs ih =>
      rw [List.map_cons, show (emb x :: bs.map emb) = [emb x] ++ bs.map emb from rfl] at h
      obtain ⟨u, v, rfl, hu, hv⟩ := h.split
      refine Domain.YieldSeq.comp
        (seqBody_iff.2 (Or.inr (Or.inr ⟨x, bs, rfl, hbs, rfl⟩))) ?_
      simpa using hu.append (ih (hS.tail hbs) hv)

/-- **The binarised domain refines the embedded task sequences exactly as the source domain
refines them.** (The easy direction.) -/
lemma yieldSeq_map_emb_of_yieldSeq (hS : Covers D S) {xs : List (A ⊕ C)} {as : List A}
    (h : D.YieldSeq xs as) : (domainOn D S).YieldSeq (xs.map emb) as := by
  induction h with
  | nil => exact Domain.YieldSeq.nil
  | prim _ ih => exact Domain.YieldSeq.prim ih
  | @comp c bs xs as hm _ ih =>
      refine Domain.YieldSeq.comp (seqBody_iff.2 (Or.inl ⟨c, bs, rfl, hm, hS.body hm, rfl⟩)) ?_
      rw [List.singleton_append]
      rw [List.map_append] at ih
      obtain ⟨u, v, rfl, hu, hv⟩ := ih.split
      exact (yieldSeq_tuple_of_yieldSeq_map hS (hS.body hm) hu).append hv

/-- **Every refinement in the binarised domain comes from a refinement in the source domain.** -/
lemma yieldSeq_flatMap_back {ys : List (A ⊕ Name A C)} {as : List A}
    (h : (domainOn D S).YieldSeq ys as) : D.YieldSeq (ys.flatMap back) as := by
  induction h with
  | nil => exact Domain.YieldSeq.nil
  | @prim a ys as _ ih =>
      rw [List.flatMap_cons]
      exact Domain.YieldSeq.prim ih
  | @comp c' bs' ys as hm _ ih =>
      rcases seqBody_iff.1 hm with ⟨c, bs, rfl, hD, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨x, bs, rfl, -, rfl⟩
      · rw [List.flatMap_cons]
        refine Domain.yieldSeq_of_subst (xs₁ := []) hD ?_
        simpa using ih
      · simpa using ih
      · simpa using ih

/-- **Correctness of the binarisation at the level of refinements.** -/
theorem yieldSeq_iff (hS : Covers D S) {xs : List (A ⊕ C)} (hxs : xs ∈ S) {as : List A} :
    (domainOn D S).YieldSeq [Sum.inr (Sum.inr xs)] as ↔ D.YieldSeq xs as := by
  constructor
  · intro h
    simpa using yieldSeq_flatMap_back h
  · intro h
    exact yieldSeq_tuple_of_yieldSeq_map hS hxs (yieldSeq_map_emb_of_yieldSeq hS h)

/-! ### Correctness of the binarisation for planning problems -/

/-- The binarisation of a planning problem, restricted to the task sequences `S`: the binarised
domain, the initial state and the goal of the source problem, and the single initial compound
task `⟨xs₀⟩` for the initial task sequence `xs₀` of the source problem. -/
def problemOn (P : Problem F A C I) (xs₀ : List (A ⊕ C)) (S : Set (List (A ⊕ C))) :
    Problem F A (Name A C) (ℕ × ℕ) :=
  (domainOn P.domain S).mkProblem
    { init := P.init, goal := P.goal, tnI := seq [Sum.inr (Sum.inr xs₀)] }

/-- The binarisation of a planning problem. -/
def problem (P : Problem F A C I) (xs₀ : List (A ⊕ C)) : Problem F A (Name A C) (ℕ × ℕ) :=
  problemOn P xs₀ Set.univ

variable {P : Problem F A C I} {xs₀ : List (A ⊕ C)}

@[simp] lemma problemOn_init : (problemOn P xs₀ S).init = P.init := rfl

@[simp] lemma problemOn_goal : (problemOn P xs₀ S).goal = P.goal := rfl

@[simp] lemma problemOn_domain : (problemOn P xs₀ S).domain = domainOn P.domain S := rfl

@[simp] lemma problem_eq : problem P xs₀ = problemOn P xs₀ Set.univ := rfl

@[simp] lemma problem_init : (problem P xs₀).init = P.init := rfl

@[simp] lemma problem_goal : (problem P xs₀).goal = P.goal := rfl

@[simp] lemma problem_domain : (problem P xs₀).domain = domain P.domain := rfl

/-- The binarised problem is well formed. -/
theorem problemOn_wf : (problemOn P xs₀ S).WF where
  tnI := seq_wf
  methods := fun _ hm => subtasks_wf hm

/-- All methods of the binarised problem are totally ordered. -/
theorem problemOn_isTO_M : (problemOn P xs₀ S).IsTO_M :=
  fun _ hm => subtasks_isTotallyOrdered hm.1

theorem problem_wf : (problem P xs₀).WF := problemOn_wf

theorem problem_isTO_M : (problem P xs₀).IsTO_M := problemOn_isTO_M

/-- The initial task network of the binarised problem is the single compound task `⟨xs₀⟩`. -/
lemma problemOn_tnI_T : (problemOn P xs₀ S).tnI.T = {(0, 0)} := by
  ext p
  obtain ⟨i, j⟩ := p
  simp [problemOn, Domain.mkProblem, mem_seq_T, Prod.ext_iff]

lemma problemOn_tnI_α :
    (problemOn P xs₀ S).tnI.α (0, 0) = Sum.inr (Sum.inr xs₀ : Name A C) := by
  simpa using seq_α (l := [Sum.inr (Sum.inr xs₀ : Name A C)]) (j := 0) (by simp)

/-- **The binarisation preserves and reflects solvability.** -/
theorem solvableOn_iff [DecidableEq I] [Infinite I] (hwf : P.WF) (hto : P.IsTO_M)
    (hS : Covers P.domain S) (hxs₀ : xs₀ ∈ S) {l₀ : List I}
    (h₀ : P.tnI.IsSeqNet l₀ xs₀) : (problemOn P xs₀ S).Solvable ↔ P.Solvable := by
  have hbin : (problemOn P xs₀ S).tnI.IsSeqNet (seqIds 1) [Sum.inr (Sum.inr xs₀ : Name A C)] :=
    seq_isSeqNet _
  rw [Problem.solvable_iff_yieldSeq problemOn_wf problemOn_isTO_M hbin,
    Problem.solvable_iff_yieldSeq hwf hto h₀]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    exact ⟨as, (yieldSeq_iff hS hxs₀).1 hy, happ, hgoal⟩
  · rintro ⟨as, hy, happ, hgoal⟩
    exact ⟨as, (yieldSeq_iff hS hxs₀).2 hy, happ, hgoal⟩

/-- **The binarisation preserves and reflects solvability.** -/
theorem solvable_iff [DecidableEq I] [Infinite I] (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I}
    (h₀ : P.tnI.IsSeqNet l₀ xs₀) : (problem P xs₀).Solvable ↔ P.Solvable :=
  solvableOn_iff hwf hto (covers_univ _) trivial h₀

/-- **Solvability of an arbitrary totally ordered HTN problem is characterised by the proof
tuples of its binarisation.**  This removes the assumption of the source that all methods have
at most two subtasks: the binarisation is a solution-preserving compilation that establishes
it. -/
theorem solvableOn_iff_provable [DecidableEq I] [Infinite I] (hwf : P.WF) (hto : P.IsTO_M)
    (hS : Covers P.domain S) (hxs₀ : xs₀ ∈ S) {l₀ : List I} (h₀ : P.tnI.IsSeqNet l₀ xs₀) :
    P.Solvable ↔ ∃ s' : Set F,
      (domainOn P.domain S).Provable P.init (Sum.inr (Sum.inr xs₀)) s' ∧ P.GoalState s' := by
  have hbody : ∀ (c' : Name A C) (bs' : List (A ⊕ Name A C)),
      (problemOn P xs₀ S).domain.SeqBody c' bs' → bs'.length ≤ 2 := by
    intro c' bs' hb
    rcases seqBody_iff.1 hb with ⟨c, bs, -, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨x, bs, -, -, rfl⟩ <;> simp
  rw [← solvableOn_iff hwf hto hS hxs₀ h₀,
    Problem.solvable_iff_provable problemOn_wf problemOn_isTO_M hbody problemOn_tnI_T
      problemOn_tnI_α]
  exact Iff.rfl

/-- **Solvability of an arbitrary totally ordered HTN problem is characterised by the proof
tuples of its binarisation.** -/
theorem solvable_iff_provable [DecidableEq I] [Infinite I] (hwf : P.WF) (hto : P.IsTO_M)
    {l₀ : List I} (h₀ : P.tnI.IsSeqNet l₀ xs₀) :
    P.Solvable ↔ ∃ s' : Set F,
      (domain P.domain).Provable P.init (Sum.inr (Sum.inr xs₀)) s' ∧ P.GoalState s' :=
  solvableOn_iff_provable hwf hto (covers_univ _) trivial h₀

end Bin

end HTN
