import HtnPlanning.Core.Reachability
/-!
# Only the reachable methods matter

A domain may carry methods that no decomposition of the initial task network can ever apply:
their decomposed task name is not reachable from `tn_I` (`HTN.Problem.ReachableMethod`).  This
file proves that such methods can be added or removed without changing solvability:

> `HTN.Problem.solvable_withMethods_iff` — if `M` is contained in the methods of `P` and
> contains every *reachable* method of `P`, then `P` with the methods `M` is solvable exactly
> when `P` is.

This is what allows a *finite description* to represent an infinite method set: the semantic
constructions of this development (for instance the compilation
`HtnComplexity/ToHtnAc/ToHtnAc.lean`, whose compiled domain has a method for every value of an
infinite family of counting tasks) generate infinitely many methods, of which only finitely
many are reachable, and only those have to be written down.
-/

namespace HTN

namespace Problem

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- The same planning problem with a different set of methods. -/
def withMethods (P : Problem F A C I) (M : Set (Method I A C)) : Problem F A C I :=
  { P with methods := M }

@[simp] lemma withMethods_methods (P : Problem F A C I) (M : Set (Method I A C)) :
    (P.withMethods M).methods = M := rfl

@[simp] lemma withMethods_tnI (P : Problem F A C I) (M : Set (Method I A C)) :
    (P.withMethods M).tnI = P.tnI := rfl

@[simp] lemma withMethods_init (P : Problem F A C I) (M : Set (Method I A C)) :
    (P.withMethods M).init = P.init := rfl

@[simp] lemma withMethods_goal (P : Problem F A C I) (M : Set (Method I A C)) :
    (P.withMethods M).goal = P.goal := rfl

@[simp] lemma withMethods_toActionModel (P : Problem F A C I) (M : Set (Method I A C)) :
    (P.withMethods M).toActionModel = P.toActionModel := rfl

@[simp] lemma withMethods_executable (P : Problem F A C I) (M : Set (Method I A C))
    (tn : TaskNetwork I A C) : (P.withMethods M).Executable tn ↔ P.Executable tn := Iff.rfl

variable [DecidableEq I]

/-- Decomposition is monotone in the method set. -/
theorem decomposesTo_mono {M N : Set (Method I A C)} (h : M ⊆ N) {tn tn' : TaskNetwork I A C}
    (hd : HTN.DecomposesTo M tn tn') : HTN.DecomposesTo N tn tn' := by
  induction hd with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨t, m, hm, ht, hα, rest⟩ := hstep
    exact Relation.ReflTransGen.tail ih ⟨t, m, h hm, ht, hα, rest⟩

/-- **A decomposition of the initial task network only uses reachable methods**, so it can be
replayed with any method set that contains them. -/
theorem decomposesTo_withMethods {P : Problem F A C I} {M : Set (Method I A C)}
    (hreach : ∀ m, P.ReachableMethod m → m ∈ M) {tn : TaskNetwork I A C}
    (h : P.DecomposesTo P.tnI tn) : (P.withMethods M).DecomposesTo (P.withMethods M).tnI tn := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    obtain ⟨t, m, hstep⟩ := hbc
    have hm : m ∈ M := hreach m (reachableMethod_of_decomposesTo hab hstep)
    obtain ⟨-, ht, hα, rest⟩ := hstep
    exact Relation.ReflTransGen.tail ih ⟨t, m, hm, ht, hα, rest⟩

/-! ### Methods only matter up to isomorphism of their subtask networks -/

/-- Two sets of methods are **equivalent up to isomorphism** iff every method of one has a
counterpart in the other decomposing the same task name by an isomorphic subtask network. -/
def MethodsIsoEquiv (M N : Set (Method I A C)) : Prop :=
  (∀ m ∈ M, ∃ n ∈ N, n.abstractTask = m.abstractTask ∧ m.subtasks.Iso n.subtasks) ∧
    (∀ n ∈ N, ∃ m ∈ M, m.abstractTask = n.abstractTask ∧ n.subtasks.Iso m.subtasks)

omit [DecidableEq I] in
theorem MethodsIsoEquiv.symm {M N : Set (Method I A C)} (h : MethodsIsoEquiv M N) :
    MethodsIsoEquiv N M := ⟨h.2, h.1⟩

/-- A decomposition step can be replayed with an equivalent set of methods: the step inserts a
fresh *isomorphic copy* of the subtask network, so an isomorphic method does the same job. -/
theorem decompStep'_congr_methods {M N : Set (Method I A C)} (h : MethodsIsoEquiv M N)
    {tn tn' : TaskNetwork I A C} (hd : HTN.DecompStep' M tn tn') : HTN.DecompStep' N tn tn' := by
  obtain ⟨t, m, hm, ht, hα, u, huwf, huiso, hdisj, rfl⟩ := hd
  obtain ⟨n, hn, hname, hiso⟩ := h.1 m hm
  exact ⟨t, n, hn, ht, by rw [hname]; exact hα, u, huwf, huiso.trans hiso, hdisj, rfl⟩

theorem decomposesTo_congr_methods {M N : Set (Method I A C)} (h : MethodsIsoEquiv M N)
    {tn tn' : TaskNetwork I A C} (hd : HTN.DecomposesTo M tn tn') :
    HTN.DecomposesTo N tn tn' := by
  induction hd with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih (decompStep'_congr_methods h hstep)

/-- **Solvability only depends on the methods up to isomorphism of their subtask networks.** -/
theorem solvable_congr_methods {P : Problem F A C I} {N : Set (Method I A C)}
    (h : MethodsIsoEquiv P.methods N) : (P.withMethods N).Solvable ↔ P.Solvable := by
  constructor
  · rintro ⟨tn, hr, hprim, hexec⟩
    exact ⟨tn, decomposesTo_congr_methods h.symm hr, hprim, hexec⟩
  · rintro ⟨tn, hr, hprim, hexec⟩
    exact ⟨tn, decomposesTo_congr_methods h hr, hprim, hexec⟩

/-- **Solvability only depends on the reachable methods.** -/
theorem solvable_withMethods_iff {P : Problem F A C I} {M : Set (Method I A C)}
    (hsub : M ⊆ P.methods) (hreach : ∀ m, P.ReachableMethod m → m ∈ M) :
    (P.withMethods M).Solvable ↔ P.Solvable := by
  constructor
  · rintro ⟨tn, hr, hprim, hexec⟩
    exact ⟨tn, decomposesTo_mono hsub hr, hprim, hexec⟩
  · rintro ⟨tn, hr, hprim, hexec⟩
    exact ⟨tn, decomposesTo_withMethods hreach hr, hprim, hexec⟩

end Problem

end HTN
