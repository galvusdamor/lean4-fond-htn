import HtnPlanning.Computable.Relevance
import HtnComplexity.Computable.Rooted
import HtnPlanning.Core.SolutionIso
import HtnPlanning.Core.DecompPersist
/-!
# The window of a domain description

A domain description is a finite text, and this file measures exactly how much of a *rooted*
instance description it can read.

Two ingredients.

* **Dead compound names.**  A compound task whose name no method decomposes can never be
  decomposed, so it survives every decomposition sequence and no reachable network is primitive:
  `HTN.Problem.not_solvable_of_deadName`.  For descriptions this is
  `HTN.Syn.not_solvable_of_dead_task` — an instance description mentioning a compound name
  outside `HTN.Syn.DomDesc.heads` is unsolvable.
* **Inert facts.**  The relevance theorem of `Computable/Relevance.lean`: only the facts of
  `HTN.Syn.DomDesc.domFacts` matter.

Put together, a rooted instance description is seen by a fixed domain description `d` only
through its **profile** (`HTN.Syn.profile`): which of the `domFacts d` hold initially, which of
them are goals, which method of `d` (if any) the root name heads, and the single bit whether the
goal facts `d` never mentions already hold initially.  `HTN.Syn.solvable_rooted_of_profile_eq`
is the resulting congruence, and `HTN.Syn.card_profile_le` bounds the number of profiles by

    2 ^ (2 * d.size) * (d.size + 1) * 2

— *a fixed domain description sorts all rooted instance descriptions into a number of
solvability classes bounded by an explicit function of its own size.*

The reason to care: in a modular compilation the translation of instances does not see the
domain, so, when the target class only has rooted instances, everything the compiled domain will
ever learn about the source instance is this profile
(`HTN.Syn.solvable_congr_of_rooted_target`).
-/

namespace HTN

/-! ### Dead compound names -/

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

/-- **A dead compound name**: no method of `M` decomposes it. -/
def DeadName (M : Set (Method I A C)) (c : C) : Prop := ∀ m ∈ M, m.abstractTask ≠ c

/-- A task with a dead compound name is not touched by a decomposition step, and keeps its
name. -/
theorem DecompStep'.mem_of_deadName [DecidableEq I] {M : Set (Method I A C)}
    {tn tna : TaskNetwork I A C} (hstep : DecompStep' M tn tna) {x : I} {c : C} (hx : x ∈ tn.T)
    (hα : tn.α x = Sum.inr c) (hc : DeadName M c) : x ∈ tna.T ∧ tna.α x = Sum.inr c := by
  obtain ⟨t, m, hm, htT, hαt, u, -, -, hdisj, rfl⟩ := hstep
  have hxt : x ≠ t := by
    rintro rfl
    rw [hα] at hαt
    exact hc m hm (Sum.inr.inj hαt.symm)
  have hxu : x ∉ u.T := Finset.disjoint_left.1 hdisj hx
  exact ⟨mem_decomposeWith_T.2 (Or.inl ⟨hx, hxt⟩), by simp [decomposeWith_α, hxu, hα]⟩

/-- **A task with a dead compound name survives every decomposition sequence**, with its name. -/
theorem DecomposesTo.mem_of_deadName [DecidableEq I] {M : Set (Method I A C)}
    {tn tnStar : TaskNetwork I A C} (h : DecomposesTo M tn tnStar) {x : I} {c : C}
    (hc : DeadName M c) : x ∈ tn.T → tn.α x = Sum.inr c → x ∈ tnStar.T ∧ tnStar.α x = Sum.inr c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hx hα => ⟨hx, hα⟩
  | @head a b hstep _ ih =>
    intro hx hα
    obtain ⟨hxb, hαb⟩ := hstep.mem_of_deadName hx hα hc
    exact ih hxb hαb

/-- **A dead compound task makes a problem unsolvable.** -/
theorem Problem.not_solvable_of_deadName {F : Type*} [DecidableEq I]
    (P : Problem F A C I) {x : I} {c : C} (hx : x ∈ P.tnI.T) (hα : P.tnI.α x = Sum.inr c)
    (hc : DeadName P.methods c) : ¬ P.Solvable := by
  rintro ⟨tn, hreach, hprim, -⟩
  obtain ⟨hxtn, hαtn⟩ := DecomposesTo.mem_of_deadName hreach hc hx hα
  obtain ⟨a, ha⟩ := hprim x hxtn
  rw [ha] at hαtn
  exact Sum.inl_ne_inr hαtn

namespace Syn

/-! ### Dead compound names, for descriptions -/

/-- The compound names the methods of a domain description decompose. -/
def DomDesc.heads (d : DomDesc) : List ℕ := d.methods.map Prod.fst

@[simp] theorem mem_heads_iff {d : DomDesc} {c : ℕ} :
    c ∈ d.heads ↔ ∃ e ∈ d.methods, e.1 = c := by
  simp [DomDesc.heads]

/-- A compound name outside `heads` is dead for the described problem. -/
theorem deadName_of_notMem_heads {d : DomDesc} {q : InstDesc} {c : ℕ} (h : c ∉ d.heads) :
    DeadName (problem d q).methods c := by
  rintro m ⟨e, he, rfl⟩ hm
  exact h (mem_heads_iff.2 ⟨e, he, hm⟩)

/-- **An instance description whose initial task network mentions a compound name the domain
never decomposes is unsolvable.** -/
theorem not_solvable_of_dead_task {d : DomDesc} {q : InstDesc} {t c : ℕ}
    (ht : t ∈ q.tnI.toTaskNetwork.T) (hα : q.tnI.toTaskNetwork.α t = Sum.inr c)
    (hc : c ∉ d.heads) : ¬ Solvable d q :=
  Problem.not_solvable_of_deadName (problem d q) (by simpa using ht) (by simpa using hα)
    (deadName_of_notMem_heads hc)

/-- A rooted instance description whose root name heads no method is unsolvable. -/
theorem not_solvable_of_rooted_dead {d : DomDesc} {q : InstDesc} (hq : q.IsRooted)
    (hc : rootName q ∉ d.heads) : ¬ Solvable d q := by
  obtain ⟨t, hT, hα⟩ := InstDesc.rootName_spec hq
  exact not_solvable_of_dead_task (by rw [hT]; simp) hα hc

/-! ### Solvability depends on the initial task network only up to isomorphism -/

/-- **Solvability of a described problem only depends on the initial task network up to
isomorphism.** -/
theorem solvable_congr_tnI_iso (d : DomDesc) (Ini Goal : List ℕ) (t t' : TnDesc)
    (hiso : t.toTaskNetwork.Iso t'.toTaskNetwork) :
    Solvable d (Ini, Goal, t) ↔ Solvable d (Ini, Goal, t') := by
  have h := Problem.solvable_congr_tnI_iff (problem d (Ini, Goal, t)) t.toTaskNetwork_wf
    t'.toTaskNetwork_wf hiso
  have e1 : (problem d (Ini, Goal, t)).withTnI t.toTaskNetwork = problem d (Ini, Goal, t) := rfl
  have e2 : (problem d (Ini, Goal, t)).withTnI t'.toTaskNetwork = problem d (Ini, Goal, t') := rfl
  rw [e1, e2] at h
  exact h

/-- Two rooted instance descriptions with the same root name have isomorphic initial task
networks. -/
theorem isRooted_iso {q q' : InstDesc} (hq : q.IsRooted) (hq' : q'.IsRooted)
    (hname : rootName q = rootName q') :
    q.tnI.toTaskNetwork.Iso q'.tnI.toTaskNetwork := by
  obtain ⟨t, hT, hα⟩ := InstDesc.rootName_spec hq
  obtain ⟨t', hT', hα'⟩ := InstDesc.rootName_spec hq'
  have ht'mem : t' ∈ (q'.tnI.toTaskNetwork.T : Set ℕ) := by
    have : t' ∈ q'.tnI.toTaskNetwork.T := by rw [hT']; exact Finset.mem_singleton_self t'
    simpa using this
  have htmem : t ∈ (q.tnI.toTaskNetwork.T : Set ℕ) := by
    have : t ∈ q.tnI.toTaskNetwork.T := by rw [hT]; exact Finset.mem_singleton_self t
    simpa using this
  refine ⟨fun _ => t', ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x _
    exact ht'mem
  · intro x _ y _ _
    have hx : x ∈ q.tnI.toTaskNetwork.T := by simpa using ‹x ∈ (q.tnI.toTaskNetwork.T : Set ℕ)›
    have hy : y ∈ q.tnI.toTaskNetwork.T := by simpa using ‹y ∈ (q.tnI.toTaskNetwork.T : Set ℕ)›
    rw [hT] at hx hy
    simp only [Finset.mem_singleton] at hx hy
    rw [hx, hy]
  · intro y hy
    have hy' : y ∈ q'.tnI.toTaskNetwork.T := by simpa using hy
    rw [hT'] at hy'
    simp only [Finset.mem_singleton] at hy'
    subst hy'
    exact ⟨t, htmem, rfl⟩
  · intro x hx y hy
    have hwf := q.tnI.toTaskNetwork_wf
    have hwf' := q'.tnI.toTaskNetwork_wf
    have hxT : x ∈ q.tnI.toTaskNetwork.T := by simpa using hx
    have hyT : y ∈ q.tnI.toTaskNetwork.T := by simpa using hy
    rw [hT] at hxT hyT
    simp only [Finset.mem_singleton] at hxT hyT
    rw [hxT, hyT]
    exact ⟨fun h => absurd h (hwf.irrefl _), fun h => absurd h (hwf'.irrefl _)⟩
  · intro x hx
    rw [hT] at hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    rw [hα, hα', hname]

/-! ### The window of a domain description -/

/-- **Two rooted instance descriptions a domain description cannot tell apart.**  They have the
same root name, the same initial state and goal on the facts the domain mentions, and the same
answer to the question whether the remaining goal facts already hold initially. -/
theorem solvable_rooted_congr (d : DomDesc) {q q' : InstDesc} (hq : q.IsRooted)
    (hq' : q'.IsRooted) (hname : rootName q = rootName q')
    (hinit : ∀ f ∈ d.domFacts, (f ∈ q.initList ↔ f ∈ q'.initList))
    (hgoal : ∀ f ∈ d.domFacts, (f ∈ q.goalList ↔ f ∈ q'.goalList))
    (hout : (∀ f ∈ q.goalList, f ∉ d.domFacts → f ∈ q.initList) ↔
      (∀ f ∈ q'.goalList, f ∉ d.domFacts → f ∈ q'.initList)) :
    Solvable d q ↔ Solvable d q' := by
  have h1 : Solvable d q ↔ Solvable d (q.initList, q.goalList, q'.tnI) :=
    solvable_congr_tnI_iso d q.initList q.goalList q.tnI q'.tnI (isRooted_iso hq hq' hname)
  have h2 : Solvable d (q.initList, q.goalList, q'.tnI) ↔ Solvable d q' :=
    solvable_congr_domFacts d _ q' rfl hinit hgoal hout
  exact h1.trans h2

/-- **The profile of an instance description with respect to a domain description**: which of
the facts the domain mentions hold initially, which of them are goals, which method of the
domain the root name heads (the last value if none does), and whether the goal facts the domain
never mentions already hold initially. -/
abbrev Profile (d : DomDesc) : Type :=
  (Fin d.domFacts.length → Bool) × (Fin d.domFacts.length → Bool) × Fin (d.methods.length + 1) ×
    Bool

/-- The index of the root name of `q` among the method heads of `d`, or `d.methods.length` if
no method of `d` decomposes it. -/
def rootIdx (d : DomDesc) (q : InstDesc) : Fin (d.methods.length + 1) :=
  ⟨d.heads.idxOf (rootName q), by
    have h := List.idxOf_le_length (a := rootName q) (l := d.heads)
    have hlen : d.heads.length = d.methods.length := by simp [DomDesc.heads]
    omega⟩

/-- The profile of `q` seen by `d`. -/
def profile (d : DomDesc) (q : InstDesc) : Profile d :=
  (fun i => decide (d.domFacts[i] ∈ q.initList),
    fun i => decide (d.domFacts[i] ∈ q.goalList),
    rootIdx d q,
    decide (∀ f ∈ q.goalList, f ∉ d.domFacts → f ∈ q.initList))

/-- **A domain description sees a rooted instance description only through its profile.** -/
theorem solvable_rooted_of_profile_eq (d : DomDesc) {q q' : InstDesc} (hq : q.IsRooted)
    (hq' : q'.IsRooted) (h : profile d q = profile d q') : Solvable d q ↔ Solvable d q' := by
  have hI := congrArg (fun p => p.1) h
  have hG := congrArg (fun p => p.2.1) h
  have hR := congrArg (fun p => p.2.2.1) h
  have hB := congrArg (fun p => p.2.2.2) h
  simp only [profile] at hI hG hR hB
  -- the facts the domain mentions
  have hmem : ∀ f ∈ d.domFacts, ∃ i : Fin d.domFacts.length, d.domFacts[i] = f := by
    intro f hf
    obtain ⟨i, hi, hif⟩ := List.getElem_of_mem hf
    exact ⟨⟨i, hi⟩, hif⟩
  have hinit : ∀ f ∈ d.domFacts, (f ∈ q.initList ↔ f ∈ q'.initList) := by
    intro f hf
    obtain ⟨i, rfl⟩ := hmem f hf
    have := congrFun hI i
    simpa using this
  have hgoal : ∀ f ∈ d.domFacts, (f ∈ q.goalList ↔ f ∈ q'.goalList) := by
    intro f hf
    obtain ⟨i, rfl⟩ := hmem f hf
    have := congrFun hG i
    simpa using this
  have hout : (∀ f ∈ q.goalList, f ∉ d.domFacts → f ∈ q.initList) ↔
      (∀ f ∈ q'.goalList, f ∉ d.domFacts → f ∈ q'.initList) := by
    simpa using hB
  -- the root name
  have hidx : d.heads.idxOf (rootName q) = d.heads.idxOf (rootName q') := congrArg Fin.val hR
  by_cases hqmem : rootName q ∈ d.heads
  · have hlt : d.heads.idxOf (rootName q) < d.heads.length := List.idxOf_lt_length_of_mem hqmem
    have hq'mem : rootName q' ∈ d.heads := by
      by_contra hc
      rw [hidx, List.idxOf_eq_length_iff.2 hc] at hlt
      exact absurd hlt (lt_irrefl _)
    have hlt' : d.heads.idxOf (rootName q') < d.heads.length :=
      List.idxOf_lt_length_of_mem hq'mem
    have h1 := List.getElem_idxOf hlt
    have h2 := List.getElem_idxOf hlt'
    have hname : rootName q = rootName q' := by
      rw [← h1, ← h2]
      simp [hidx]
    exact solvable_rooted_congr d hq hq' hname hinit hgoal hout
  · have hq'mem : rootName q' ∉ d.heads := by
      have : d.heads.idxOf (rootName q') = d.heads.length := by
        rw [← hidx]
        exact List.idxOf_eq_length_iff.2 hqmem
      exact List.idxOf_eq_length_iff.1 this
    constructor
    · intro hs
      exact absurd hs (not_solvable_of_rooted_dead hq hqmem)
    · intro hs
      exact absurd hs (not_solvable_of_rooted_dead hq' hq'mem)

/-- The number of facts a domain description mentions is bounded by its size. -/
theorem domFacts_length_le_size (d : DomDesc) : d.domFacts.length ≤ d.size := by
  have key : ∀ l : List ActionDesc,
      (l.flatMap fun ad => ad.2.1 ++ ad.2.2.1 ++ ad.2.2.2).length ≤ (l.map ActionDesc.size).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
        ActionDesc.size]
      omega
  have h := key d.actions
  simp only [DomDesc.size, DomDesc.domFacts]
  omega

/-- The number of methods of a domain description is bounded by its size. -/
theorem methods_length_le_size (d : DomDesc) : d.methods.length ≤ d.size := by
  have key : ∀ l : List MethodDesc, l.length ≤ (l.map MethodDesc.size).sum := by
    intro l
    induction l with
    | nil => simp
    | cons m l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons, MethodDesc.size]
      omega
  have h := key d.methods
  simp only [DomDesc.size]
  omega

/-- **The window of a domain description is bounded by its size**: a domain description of size
`n` sorts all rooted instance descriptions into at most `2 ^ (2 * n) * (n + 1) * 2` solvability
classes. -/
theorem card_profile_le (d : DomDesc) :
    Fintype.card (Profile d) ≤ 2 ^ (2 * d.size) * (d.size + 1) * 2 := by
  have hcard : Fintype.card (Profile d)
      = 2 ^ (2 * d.domFacts.length) * (d.methods.length + 1) * 2 := by
    simp only [Profile, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      two_mul, pow_add]
    ring
  rw [hcard]
  have h1 : (2 : ℕ) ^ (2 * d.domFacts.length) ≤ 2 ^ (2 * d.size) :=
    Nat.pow_le_pow_right (by norm_num) (by have := domFacts_length_le_size d; omega)
  have h2 : d.methods.length + 1 ≤ d.size + 1 := by
    have := methods_length_le_size d; omega
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)

end Syn

end HTN
