import HtnPlanning.Core.ClassicalPlanLength
import HtnPlanning.Core.TONormalForm
import HtnPlanning.Core.Strips
import HtnPlanning.Core.Construction
import HtnPlanning.Binarisation.Binarisation
import HtnPlanning.Core.SizeOn
/-!
# Compiling classical planning problems into *acyclic* totally ordered HTN problems

The encoding of a classical planning problem as an HTN problem in
`HtnPlanning/Core/Strips.lean` is *recursive*: the single compound task `c` decomposes into
`a c`, so it lies in `TO-HTN-REG` but not in `TO-HTN-AC`.  This file gives an **acyclic**
encoding, following the idea recorded in the project's `README.md`:

```
T_{k+1} → T_k T_k      (k < K)
T_0     → a            (for every action a)
T_0     → ε
```

with the initial task network `T_K` for `K` levels.  The hierarchy is acyclic — the level `k`
of a compound task strictly decreases along every method — and a task `T_k` refines exactly
into the action sequences of length at most `2 ^ k`.  Choosing `K = |F|` is enough by the loop
removal lemma `HTN.ClassicalProblem.exists_solution_length_lt`: a solvable classical problem
over the facts `F` has a solution of length `< 2 ^ |F|`.

Main results:

* `HTN.StripsToAc.yieldSeq_iff` — `T_k` refines exactly into the action sequences of length at
  most `2 ^ k`;
* `HTN.ClassicalProblem.toTOAC_mem_TO_HTN_AC` — the compiled problem is totally ordered and
  acyclic;
* `HTN.ClassicalProblem.toTOAC_solvable_iff` — for `K ≥ |F|` the compiled problem is solvable
  exactly when the classical problem is;
* `HTN.ClassicalProblem.toTOAC_isSolutionPlan_iff` — the plans of the compiled problem are
  exactly the solutions of the classical problem of length at most `2 ^ K`, so plans are
  preserved *without any change at all*;
* `HTN.ClassicalProblem.toTOAC_sizeOn_le` — the compiled domain has linear size.
-/

namespace HTN

universe u v

namespace StripsToAc

variable {F : Type u} {A : Type v} [Inhabited A]

open TaskNetwork

/-- The label of a task of a chain network occurs in the chain. -/
lemma α_mem_of_mem_seq_T {C : Type*} {l : List (A ⊕ C)} {t : ℕ × ℕ}
    (ht : t ∈ (TaskNetwork.seq l).T) : (TaskNetwork.seq l).α t ∈ l := by
  simpa using TaskNetwork.grid_α_mem_flatten (ls := [l]) ht

/-- A method whose subtask network is a chain has exactly that chain as its body. -/
lemma hasSeqBody_iff {C : Type*} {l bs : List (A ⊕ C)}
    {m : Method (ℕ × ℕ) A C} (hm : m.subtasks = TaskNetwork.seq l) :
    m.HasSeqBody bs ↔ bs = l := by
  cases m with
  | mk c st => cases hm; exact TaskNetwork.hasSeqBody_seq_iff

/-! ### The compiled domain -/

/-- The method `T_{k+1} → T_k T_k`. -/
def splitMethod (A : Type v) [Inhabited A] (k : ℕ) : Method (ℕ × ℕ) A ℕ :=
  ⟨k + 1, TaskNetwork.seq [Sum.inr k, Sum.inr k]⟩

/-- The method `T_0 → a`. -/
def actMethod (a : A) : Method (ℕ × ℕ) A ℕ := ⟨0, TaskNetwork.seq [Sum.inl a]⟩

/-- The method `T_0 → ε`. -/
def nilMethod (A : Type v) [Inhabited A] : Method (ℕ × ℕ) A ℕ :=
  ⟨0, TaskNetwork.seq ([] : List (A ⊕ ℕ))⟩

/-- **The compiled domain**: `K` levels of compound tasks, each splitting into two tasks of the
next lower level, and a lowest level generating one action or nothing. -/
def domain (δ : ActionModel F A) (K : ℕ) : Domain F A ℕ (ℕ × ℕ) where
  toActionModel := δ
  methods := {m | (∃ k, k < K ∧ m = splitMethod A k) ∨ (∃ a : A, m = actMethod a) ∨
    m = nilMethod A}

@[simp] lemma domain_toActionModel (δ : ActionModel F A) (K : ℕ) :
    (domain δ K).toActionModel = δ := rfl

lemma mem_domain_methods {δ : ActionModel F A} {K : ℕ} {m : Method (ℕ × ℕ) A ℕ} :
    m ∈ (domain δ K).methods ↔ (∃ k, k < K ∧ m = splitMethod A k) ∨ (∃ a : A, m = actMethod a) ∨
      m = nilMethod A := Iff.rfl

/-- Every method of the compiled domain has a chain as its subtask network. -/
lemma exists_seq_subtasks {δ : ActionModel F A} {K : ℕ} {m : Method (ℕ × ℕ) A ℕ}
    (hm : m ∈ (domain δ K).methods) : ∃ l : List (A ⊕ ℕ), m.subtasks = TaskNetwork.seq l := by
  rcases hm with ⟨k, -, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **The bodies of the compiled domain.** -/
lemma seqBody_iff {δ : ActionModel F A} {K : ℕ} {c : ℕ} {bs : List (A ⊕ ℕ)} :
    (domain δ K).SeqBody c bs ↔
      ((∃ k, k < K ∧ c = k + 1 ∧ bs = [Sum.inr k, Sum.inr k]) ∨
        (c = 0 ∧ ∃ a : A, bs = [Sum.inl a]) ∨ (c = 0 ∧ bs = [])) := by
  constructor
  · rintro ⟨m, hm, rfl, hbody⟩
    rcases hm with ⟨k, hk, rfl⟩ | ⟨a, rfl⟩ | rfl
    · exact Or.inl ⟨k, hk, rfl, (hasSeqBody_iff (l := [Sum.inr k, Sum.inr k]) rfl).1 hbody⟩
    · exact Or.inr (Or.inl ⟨rfl, a, (hasSeqBody_iff (l := [Sum.inl a]) rfl).1 hbody⟩)
    · exact Or.inr (Or.inr ⟨rfl, (hasSeqBody_iff (l := []) rfl).1 hbody⟩)
  · rintro (⟨k, hk, rfl, rfl⟩ | ⟨rfl, a, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨splitMethod A k, Or.inl ⟨k, hk, rfl⟩, rfl, (hasSeqBody_iff rfl).2 rfl⟩
    · exact ⟨actMethod a, Or.inr (Or.inl ⟨a, rfl⟩), rfl, (hasSeqBody_iff rfl).2 rfl⟩
    · exact ⟨nilMethod A, Or.inr (Or.inr rfl), rfl, (hasSeqBody_iff rfl).2 rfl⟩

/-! ### What the compound tasks refine into -/

/-- The maximal number of actions a task can be refined into: one for a primitive task and
`2 ^ k` for the compound task of level `k`. -/
def wt : A ⊕ ℕ → ℕ
  | Sum.inl _ => 1
  | Sum.inr k => 2 ^ k

/-- The body of a method does not increase the maximal number of actions. -/
lemma sum_map_wt_le_of_seqBody {δ : ActionModel F A} {K : ℕ} {c : ℕ} {bs : List (A ⊕ ℕ)}
    (h : (domain δ K).SeqBody c bs) : ((bs.map wt).sum) ≤ wt (Sum.inr c : A ⊕ ℕ) := by
  rcases seqBody_iff.1 h with ⟨k, -, rfl, rfl⟩ | ⟨rfl, a, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_succ]
    omega
  · simp [wt]
  · simp [wt]

/-- **Every refinement is short.** -/
lemma yieldSeq_length_le {δ : ActionModel F A} {K : ℕ} {xs : List (A ⊕ ℕ)} {as : List A}
    (h : (domain δ K).YieldSeq xs as) : as.length ≤ (xs.map wt).sum := by
  induction h with
  | nil => simp
  | @prim a xs as _ ih =>
      simp only [wt, List.map_cons, List.sum_cons, List.length_cons]
      omega
  | @comp c bs xs as hm _ ih =>
      have hb := sum_map_wt_le_of_seqBody hm
      simp only [List.map_append, List.sum_append] at ih
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **Every short action sequence is a refinement.** -/
lemma yieldSeq_of_length_le {δ : ActionModel F A} {K : ℕ} :
    ∀ {k : ℕ}, k ≤ K → ∀ {as : List A}, as.length ≤ 2 ^ k →
      (domain δ K).YieldSeq [Sum.inr k] as := by
  intro k
  induction k with
  | zero =>
      intro _ as hlen
      simp only [pow_zero] at hlen
      rcases as with _ | ⟨a, as⟩
      · exact Domain.YieldSeq.comp (bs := []) (seqBody_iff.2 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
          (by simpa using Domain.YieldSeq.nil)
      · have hnil : as = [] := by
          rw [List.length_cons] at hlen
          exact List.length_eq_zero_iff.1 (by omega)
        subst hnil
        refine Domain.YieldSeq.comp (bs := [Sum.inl a])
          (seqBody_iff.2 (Or.inr (Or.inl ⟨rfl, a, rfl⟩))) ?_
        simpa using Domain.YieldSeq.prim (as := []) Domain.YieldSeq.nil
  | succ k ih =>
      intro hk as hlen
      have hkK : k < K := by omega
      have h₁ : (as.take (2 ^ k)).length ≤ 2 ^ k := by simp
      have h₂ : (as.drop (2 ^ k)).length ≤ 2 ^ k := by
        have : as.length ≤ 2 ^ k + 2 ^ k := by
          have h := hlen
          rw [pow_succ] at h
          omega
        simp only [List.length_drop]
        omega
      have hy₁ := ih (by omega) h₁
      have hy₂ := ih (by omega) h₂
      refine Domain.YieldSeq.comp (bs := [Sum.inr k, Sum.inr k])
        (seqBody_iff.2 (Or.inl ⟨k, hkK, rfl, rfl⟩)) ?_
      have := hy₁.append hy₂
      simpa [List.take_append_drop] using this

/-- **The refinements of the compound task of level `k`** are exactly the action sequences of
length at most `2 ^ k`. -/
theorem yieldSeq_iff {δ : ActionModel F A} {K k : ℕ} (hk : k ≤ K) {as : List A} :
    (domain δ K).YieldSeq [Sum.inr k] as ↔ as.length ≤ 2 ^ k := by
  refine ⟨fun h => ?_, yieldSeq_of_length_le hk⟩
  simpa [wt] using yieldSeq_length_le h

end StripsToAc

/-! ### The compiled problem -/

namespace ClassicalProblem

variable {F : Type u} {A : Type v} [Inhabited A]

open StripsToAc TaskNetwork

/-- The problem instance of the compiled problem: the initial state and goal of the classical
problem, and the compound task of the top level as the initial task network. -/
def toTOACInstance (Pc : ClassicalProblem F A) (K : ℕ) : Instance F A ℕ (ℕ × ℕ) where
  init := Pc.init
  goal := Pc.goal
  tnI := TaskNetwork.seq [Sum.inr K]

/-- **The acyclic, totally ordered HTN encoding of a classical planning problem** with `K`
levels of compound tasks. -/
def toTOAC (Pc : ClassicalProblem F A) (K : ℕ) : Problem F A ℕ (ℕ × ℕ) :=
  (domain Pc.toActionModel K).mkProblem (Pc.toTOACInstance K)

variable (Pc : ClassicalProblem F A) (K : ℕ)

@[simp] lemma toTOAC_domain : (Pc.toTOAC K).domain = domain Pc.toActionModel K := rfl

@[simp] lemma toTOAC_init : (Pc.toTOAC K).init = Pc.init := rfl

@[simp] lemma toTOAC_goal : (Pc.toTOAC K).goal = Pc.goal := rfl

@[simp] lemma toTOAC_tnI : (Pc.toTOAC K).tnI = TaskNetwork.seq [Sum.inr K] := rfl

@[simp] lemma toTOAC_toClassicalProblem : (Pc.toTOAC K).toClassicalProblem = Pc := rfl

/-- The initial task network of the encoding is the one-element chain `T_K`. -/
lemma toTOAC_isSeqNet :
    (Pc.toTOAC K).tnI.IsSeqNet (TaskNetwork.seqIds [(Sum.inr K : A ⊕ ℕ)].length)
      [Sum.inr K] :=
  TaskNetwork.seq_isSeqNet _

/-- The encoding is well formed. -/
theorem toTOAC_wf : (Pc.toTOAC K).WF where
  tnI := TaskNetwork.seq_wf
  methods := by
    intro m hm
    obtain ⟨l, hl⟩ := exists_seq_subtasks (δ := Pc.toActionModel) (K := K) hm
    rw [hl]
    exact TaskNetwork.seq_wf

/-- The encoding is totally ordered. -/
theorem toTOAC_isTO : (Pc.toTOAC K).IsTO := by
  constructor
  · exact (TaskNetwork.seq_isSeqNet _).isTotallyOrdered
  · intro m hm
    obtain ⟨l, hl⟩ := exists_seq_subtasks (δ := Pc.toActionModel) (K := K) hm.1
    rw [hl]
    exact (TaskNetwork.seq_isSeqNet l).isTotallyOrdered

/-- The encoding is acyclic: the level of a compound task strictly decreases along every
method. -/
theorem toTOAC_isAcyclic : (Pc.toTOAC K).IsAcyclic := by
  refine Problem.isAcyclic_of_rank _ id ?_
  intro m hm t ht c hc
  rcases hm.1 with ⟨k, -, rfl⟩ | ⟨a, rfl⟩ | rfl
  · have hmem := α_mem_of_mem_seq_T (l := [(Sum.inr k : A ⊕ ℕ), Sum.inr k]) ht
    have hc' : (TaskNetwork.seq [(Sum.inr k : A ⊕ ℕ), Sum.inr k]).α t = Sum.inr c := hc
    rw [hc'] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hmem
    rcases hmem with rfl | rfl <;> simp [splitMethod]
  · have hmem := α_mem_of_mem_seq_T (l := [(Sum.inl a : A ⊕ ℕ)]) ht
    have hc' : (TaskNetwork.seq [(Sum.inl a : A ⊕ ℕ)]).α t = Sum.inr c := hc
    rw [hc'] at hmem
    simp at hmem
  · have hmem := α_mem_of_mem_seq_T (l := ([] : List (A ⊕ ℕ))) ht
    simp at hmem

/-- **The encoding is a totally ordered acyclic HTN planning problem.** -/
theorem toTOAC_mem_TO_HTN_AC : Pc.toTOAC K ∈ Classes.TO_HTN_AC F A ℕ (ℕ × ℕ) :=
  ⟨Pc.toTOAC_isTO K, Pc.toTOAC_isAcyclic K⟩

/-! ### Correctness -/

/-- The solutions of the compiled problem are the refinements of the top level task that are
executable and reach the goal. -/
theorem toTOAC_solvable_iff_yieldSeq :
    (Pc.toTOAC K).Solvable ↔ ∃ as : List A,
      (domain Pc.toActionModel K).YieldSeq [Sum.inr K] as ∧ Pc.SeqApplicable as Pc.init ∧
        Pc.GoalState (Pc.transitionSeq as Pc.init) :=
  Problem.solvable_iff_yieldSeq (Pc.toTOAC_wf K) (Pc.toTOAC_isTO K).2 (Pc.toTOAC_isSeqNet K)

/-- **The plans of the compiled problem are exactly the solutions of the classical problem of
length at most `2 ^ K`** — the compilation preserves plans unchanged. -/
theorem toTOAC_isSolutionPlan_iff {as : List A} :
    (Pc.toTOAC K).IsSolutionPlan as ↔ Pc.IsSolution as ∧ as.length ≤ 2 ^ K := by
  constructor
  · intro h
    obtain ⟨-, -, -, -, -, -, happ, hgoal⟩ := id h
    have hy := Problem.yieldSeq_of_isSolutionPlan (Pc.toTOAC_wf K) (Pc.toTOAC_isTO K).2
      (Pc.toTOAC_isSeqNet K) h
    exact ⟨⟨happ, hgoal⟩, (yieldSeq_iff le_rfl).1 hy⟩
  · rintro ⟨⟨happ, hgoal⟩, hlen⟩
    exact Problem.isSolutionPlan_of_yieldSeq (Pc.toTOAC_wf K)
      (Pc.toTOAC_isSeqNet K) ((yieldSeq_iff le_rfl).2 hlen) happ hgoal

/-- **Correctness of the compilation.**  With at least `|F|` levels the compiled problem is
solvable exactly when the classical problem is. -/
theorem toTOAC_solvable_iff [Fintype F] (hK : Fintype.card F ≤ K) :
    (Pc.toTOAC K).Solvable ↔ Pc.Solvable := by
  rw [Problem.solvable_iff_exists_solutionPlan]
  constructor
  · rintro ⟨as, has⟩
    exact ⟨as, ((Pc.toTOAC_isSolutionPlan_iff K).1 has).1⟩
  · intro h
    obtain ⟨plan, hplan, hlen⟩ := exists_solution_length_lt h
    refine ⟨plan, (Pc.toTOAC_isSolutionPlan_iff K).2 ⟨hplan, ?_⟩⟩
    have : (2 : ℕ) ^ Fintype.card F ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
    omega

/-- The compiled problem and the (recursive) `STRIPS`-class encoding of the same classical
problem are equivalent. -/
theorem toTOAC_solvable_iff_toHTN_solvable [Fintype F] (hK : Fintype.card F ≤ K) :
    (Pc.toTOAC K).Solvable ↔ Pc.toHTN.Solvable := by
  rw [Pc.toTOAC_solvable_iff K hK, Strips.toHTN_solvable_iff]

end ClassicalProblem

end HTN
