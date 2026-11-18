import HtnComplexity.Undec.Bridge
import HtnPlanning.Interleave.InterleaveList
import HtnComplexity.Hypotheses.Planning
/-!
# A fixed domain description whose instance problem is the merge (shuffle) problem

§20.4 of `NOTES.md` records what the open cells of the block "unrestricted source → rooted
target" of the 21 × 21 table still owe.  By
`HtnCompilability/Computable/RootedEff.lean` a modular compilation into a class of **rooted**
instance descriptions makes plan existence for every *fixed* source domain description a
"translate, profile, look up in a constant table" reduction; for an undecidable source class
that is already a contradiction (`HTN.Syn.not_rooting_HTN`), and for the classes that are still
open it becomes a statement about *resources*.  What is missing is therefore

> a **fixed** domain description of a decidable hierarchical class whose *instance* problem —
> the unbounded parameter being the initial task network — is hard.

This file supplies one, and the next two files compute its instance problem exactly.

## The domain

`HTN.Merge.mergeDom` has **no methods at all** and four actions over the four facts
`0, 1, 2, 3`:

| action | precondition | add | delete | reading |
| --- | --- | --- | --- | --- |
| `0` | `0` | `1, 2` | `0, 3` | write the bit `false` into the buffer |
| `1` | `0` | `1, 3` | `0, 2` | write the bit `true` into the buffer |
| `2` | `1, 2` | `0` | `1, 2` | read the bit `false` from the buffer |
| `3` | `1, 3` | `0` | `1, 3` | read the bit `true` from the buffer |

The fact `0` says "the buffer is empty", the fact `1` says "the buffer is full", and the facts
`2`, `3` carry the bit in the buffer.  With the initial state `{0}` and the goal `{0}` an
executable action sequence is exactly an alternation `write b₁, read b₁, write b₂, read b₂, …`
(`HtnComplexity/Computable/MergeRun.lean`).

Since the domain has no methods, *every* structural restriction on methods holds vacuously: the
domain description belongs to `HTN`, `HTN-TR`, `HTN-REG` and `HTN-AC` — the rows of the rooted
block that are still open — and it is totally ordered and acyclic as well.  The unbounded part
of an instance is then the initial task network alone, which is exactly the situation §20.4
describes.

## The instances

`HTN.Merge.mergeInst ws z` is the instance whose initial task network is the parallel
composition (a `HTN.TaskNetwork.grid`) of

* one chain of *write* actions per word `w ∈ ws`, and
* one chain of *read* actions for the word `z`,

the chains being unordered relative to each other.  A plan has to execute all of these tasks in
*some* linearization, so it has to interleave the writes of the `ws` against the reads of `z`,
and the buffer forces the `i`-th bit read to be the `i`-th bit written:

    HTN.Merge.solvable_mergeInst_iff :  Solvable mergeDom (mergeInst ws z) ↔ InterleaveList ws z

i.e. the instance problem of the single domain description `mergeDom` **is** the merge problem
"is the word `z` a shuffle of the words `ws`?", which is the classical NP-complete problem of
Mansfield and of Warmuth–Haussler.

This file sets up the two descriptions, the semantic problem they denote and the bridge between
them, ending with the description of solvability in terms of interleavings
(`HTN.Merge.solvable_mergeInst_iff_interleave`).  The automaton analysis is in
`HtnComplexity/Computable/MergeRun.lean` and the two are combined in
`HtnComplexity/Computable/MergeCorrect.lean`.
-/

namespace HTN

namespace Merge

open Syn TaskNetwork Domain

/-! ### The alphabet -/

theorem aName_injective : Function.Injective aName := by
  intro b b' h; cases b <;> cases b' <;> simp_all [aName]

theorem bName_injective : Function.Injective bName := by
  intro b b' h; cases b <;> cases b' <;> simp_all [bName]

theorem aName_lt_two (b : Bool) : aName b < 2 := by cases b <;> simp [aName]

theorem two_le_bName (b : Bool) : 2 ≤ bName b := by cases b <;> simp [bName]

/-! ### The descriptions -/

/-- **The fixed domain description**: four actions, no methods. -/
def mergeDom : DomDesc :=
  ([(0, ([0], [1, 2], [0, 3])), (1, ([0], [1, 3], [0, 2])),
      (2, ([1, 2], [0], [1, 2])), (3, ([1, 3], [0], [1, 3]))], [])

@[simp] theorem mergeDom_methods : mergeDom.methods = [] := rfl

@[simp] theorem mergeInst_initList (ws : List (List Bool)) (z : List Bool) :
    (mergeInst ws z).initList = [0] := rfl

@[simp] theorem mergeInst_goalList (ws : List (List Bool)) (z : List Bool) :
    (mergeInst ws z).goalList = [0] := rfl

@[simp] theorem mergeInst_tnI (ws : List (List Bool)) (z : List Bool) :
    (mergeInst ws z).tnI = gridDescOf id id (chains ws z) := rfl

/-! ### The semantic problem -/

/-- **The domain of the encoding**, as a semantic object over the grid identifiers `ℕ × ℕ`: the
action model is the one described by `mergeDom`, and there are no methods. -/
def semDom : Domain ℕ ℕ ℕ (ℕ × ℕ) where
  prec := mergeDom.prec
  add := mergeDom.add
  del := mergeDom.del
  methods := ∅

@[simp] theorem semDom_methods : semDom.methods = (∅ : Set (Method (ℕ × ℕ) ℕ ℕ)) := rfl

/-- **The instance of the encoding**, semantically. -/
def semInst (ws : List (List Bool)) (z : List Bool) : Instance ℕ ℕ ℕ (ℕ × ℕ) where
  init := {f | f ∈ [0]}
  goal := {f | f ∈ [0]}
  tnI := TaskNetwork.grid (chains ws z)

/-- The semantic problem of the encoding. -/
def semProblem (ws : List (List Bool)) (z : List Bool) : Problem ℕ ℕ ℕ (ℕ × ℕ) :=
  semDom.mkProblem (semInst ws z)

/-! ### The described problem is the semantic one -/

/-- The described domain has no methods, so the two method sets are trivially equivalent. -/
theorem methodsIsoEquiv_mergeDom :
    Problem.MethodsIsoEquiv {m : Method ℕ ℕ ℕ | ∃ e ∈ mergeDom.methods, e.toMethod = m}
      (Method.relabel id id Nat.pairEquiv '' semDom.methods) := by
  constructor
  · rintro m ⟨e, he, -⟩
    simp at he
  · rintro m ⟨m', hm', -⟩
    simp at hm'

/-- **The described problem of the encoding is the semantic problem of the encoding.** -/
theorem solvable_mergeInst_iff_sem (ws : List (List Bool)) (z : List Bool) :
    Syn.Solvable mergeDom (mergeInst ws z) ↔ (semProblem ws z).Solvable := by
  classical
  set PD := Syn.problem mergeDom (mergeInst ws z)
  set PS := semProblem ws z
  set tn' := TaskNetwork.relabel id id Nat.pairEquiv PS.tnI
  set N := Method.relabel (I := ℕ × ℕ) (I' := ℕ) id id Nat.pairEquiv '' PS.methods
  have htnIiso : PD.tnI.Iso tn' := gridDesc_iso id id (chains ws z)
  have hwfPD : PD.tnI.WF := TnDesc.toTaskNetwork_wf _
  have hwftn' : tn'.WF := TaskNetwork.relabel_wf TaskNetwork.grid_wf
  have step1 : PD.Solvable ↔ (PD.withTnI tn').Solvable := by
    refine Iff.trans (Iff.of_eq (congrArg Problem.Solvable (rfl : PD = PD.withTnI PD.tnI))) ?_
    exact Problem.solvable_congr_tnI_iff PD hwfPD hwftn' htnIiso
  have hmiso : Problem.MethodsIsoEquiv (PD.withTnI tn').methods N := methodsIsoEquiv_mergeDom
  have step2 : (PD.withTnI tn').Solvable ↔ ((PD.withTnI tn').withMethods N).Solvable :=
    (Problem.solvable_congr_methods hmiso).symm
  have step3 : ((PD.withTnI tn').withMethods N).Solvable ↔ PS.Solvable := by
    refine Problem.solvable_relabel_iff (eF := id) (eA := id) (eC := id) (eI := Nat.pairEquiv)
      Function.injective_id Function.injective_id Function.injective_id
      (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ TaskNetwork.grid_wf rfl rfl
    · show mergeDom.prec o = _
      rw [Set.image_id]
      rfl
    · show mergeDom.add o = _
      rw [Set.image_id]
      rfl
    · show mergeDom.del o = _
      rw [Set.image_id]
      rfl
    · show {f | f ∈ [0]} = _
      rw [Set.image_id]
      rfl
    · show {f | f ∈ [0]} = _
      rw [Set.image_id]
      rfl
  exact step1.trans (step2.trans step3)

/-! ### Refinements of a grid of primitive chains

The domain has no methods, so a grid of primitive chains refines into exactly the interleavings
of its branches, in no decomposition step at all. -/

variable {F : Type*} {A : Type*} {C : Type*} [Inhabited A]

/-- A chain of primitive tasks refines only into itself, in a domain without methods. -/
theorem chainYieldN_primChain {D : Domain F A C (ℕ × ℕ)} :
    ∀ {n : ℕ} {l : List A} {as : List A},
      D.ChainYieldN n (l.map Sum.inl) as ↔ n = 0 ∧ as = l := by
  intro n l
  induction l generalizing n with
  | nil => intro as; simp
  | cons a l ih =>
      intro as
      rw [List.map_cons, chainYieldN_cons_inl_iff]
      constructor
      · rintro ⟨bs, rfl, h⟩
        obtain ⟨rfl, rfl⟩ := (ih (as := bs)).1 h
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨l, rfl, (ih (as := l)).2 ⟨rfl, rfl⟩⟩

/-- **A grid of primitive chains refines into exactly the interleavings of its branches.** -/
theorem gridYieldN_primChains {D : Domain F A C (ℕ × ℕ)} :
    ∀ {n : ℕ} {ls : List (List A)} {as : List A},
      D.GridYieldN n (ls.map (List.map Sum.inl)) as ↔ n = 0 ∧ InterleaveList ls as := by
  intro n ls
  induction ls generalizing n with
  | nil =>
      intro as
      rw [List.map_nil, gridYieldN_nil_iff]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, InterleaveList.nil⟩
      · rintro ⟨rfl, h⟩; cases h; exact ⟨rfl, rfl⟩
  | cons l ls ih =>
      intro as
      rw [List.map_cons, gridYieldN_cons_iff]
      constructor
      · rintro ⟨k₁, k₂, bs, cs, hn, hc, hg, hint⟩
        obtain ⟨rfl, rfl⟩ := chainYieldN_primChain.1 hc
        obtain ⟨rfl, hg'⟩ := (ih (as := cs)).1 hg
        exact ⟨by omega, InterleaveList.cons hg' hint⟩
      · rintro ⟨rfl, h⟩
        cases h with
        | @cons bs cs ds _ hg hint =>
            exact ⟨0, 0, l, cs, rfl, chainYieldN_primChain.2 ⟨rfl, rfl⟩,
              (ih (as := cs)).2 ⟨rfl, hg⟩, hint⟩

/-! ### Solvability in terms of interleavings -/

/-- **Solvability of the encoding, in terms of the interleavings of its branches.**  The plan of
a solution is an interleaving of the write chains of the `ws` and of the read chain of `z`, and
it has to be executable from the empty buffer and to end with an empty buffer. -/
theorem solvable_mergeInst_iff_interleave (ws : List (List Bool)) (z : List Bool) :
    Syn.Solvable mergeDom (mergeInst ws z) ↔
      ∃ as, InterleaveList (letters ws z) as ∧ semDom.SeqApplicable as {f | f ∈ [0]} ∧
        {f | f ∈ [0]} ⊆ semDom.transitionSeq as {f | f ∈ [0]} := by
  rw [solvable_mergeInst_iff_sem, semProblem, Problem.solvable_iff_netYield]
  refine exists_congr fun as => ?_
  refine and_congr ?_ Iff.rfl
  have hgrid : ∀ m ∈ semDom.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls := by
    intro m hm; simp at hm
  rw [show (semDom.mkProblem (semInst ws z)).tnI = TaskNetwork.grid (chains ws z) from rfl]
  rw [show (semDom.mkProblem (semInst ws z)).domain = semDom from rfl]
  rw [netYield_grid_iff hgrid]
  constructor
  · rintro ⟨n, h⟩
    exact ((gridYieldN_primChains (D := semDom)).1 h).2
  · intro h
    exact ⟨0, (gridYieldN_primChains (D := semDom)).2 ⟨rfl, h⟩⟩

end Merge

end HTN
