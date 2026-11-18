import HtnPlanning.Core.Size
import HtnPlanning.Core.ClassHierarchy
import HtnPlanning.Classes.Basic
/-!
# STRIPS as a sub-class of totally ordered regular HTN planning

Erol et al. observed — and Thm. 4.3.1 of Bercher et al. restates — that classical (STRIPS)
planning problems are a special case of *totally ordered regular* HTN planning problems: a
STRIPS problem is encoded by a single compound task `c` together with the methods

```
c ↦ a c   (for every action a)
c ↦ ε
```

This file formalises

* `Problem.IsStripsLike`, the syntactic class `STRIPS` of HTN planning problems of exactly this
  shape, and `Classes.STRIPS`;
* `Classes.STRIPS_subset_TO_HTN_REG` : `STRIPS ⊆ TO-HTN-REG`;
* `ClassicalProblem.toHTN`, the encoding of a classical planning problem, together with
  `ClassicalProblem.toHTN_isStripsLike` and
  `ClassicalProblem.toHTN_solvable_iff` : the encoding preserves and reflects solvability;
* `ClassicalProblem.toHTN_domain_size_le` : the encoding has linear size.
-/

namespace HTN

universe u v w x

/-! ### The syntactic class `STRIPS` -/

namespace TaskNetwork

variable {I : Type x} {A : Type v} {C : Type w} [DecidableEq I]

end TaskNetwork

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

/-- A STRIPS-like problem has a totally ordered initial task network. -/
theorem IsStripsLike.isTO_tnI {P : Problem F A C I} (h : P.IsStripsLike) : P.IsTO_tnI := by
  obtain ⟨c, ⟨t, hT, -⟩, -⟩ := h
  intro x hx y hy hne
  rw [hT] at hx hy
  simp only [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hne

/-- A STRIPS-like problem is totally ordered. -/
theorem IsStripsLike.isTO {P : Problem F A C I} (h : P.IsStripsLike) : P.IsTO := by
  refine ⟨h.isTO_tnI, ?_⟩
  obtain ⟨c, -, hm⟩ := h
  intro m hmr
  rcases (hm m hmr).2 with hempty | ⟨t₁, t₂, hne, hT, -, -, hord⟩
  · intro x hx
    rw [hempty] at hx
    exact absurd hx (Finset.notMem_empty x)
  · intro x hx y hy hxy
    rw [hT] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl ((hord x y).2 ⟨rfl, rfl⟩)
    · exact Or.inr ((hord y x).2 ⟨rfl, rfl⟩)
    · exact absurd rfl hxy

/-- All reachable methods of a STRIPS-like problem are regular. -/
theorem IsStripsLike.isRegularM {P : Problem F A C I} (h : P.IsStripsLike) : P.IsRegularM := by
  obtain ⟨c, -, hm⟩ := h
  intro m hmr
  rcases (hm m hmr).2 with hempty | ⟨t₁, t₂, hne, hT, ⟨a, ha⟩, hα₂, hord⟩
  · refine ⟨?_, ?_⟩ <;> intro x hx <;> rw [hempty] at hx <;> exact absurd hx (Finset.notMem_empty x)
  · have hprim₁ : ¬ m.subtasks.IsAbstractId t₁ := by
      rintro ⟨c', hc'⟩
      rw [ha] at hc'
      exact absurd hc' (by simp)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hax hay
      rw [hT] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl
      · exact absurd hax hprim₁
      · rcases hy with rfl | rfl
        · exact absurd hay hprim₁
        · rfl
    · intro x hx hax y hy hne'
      rw [hT] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl
      · exact absurd hax hprim₁
      · rcases hy with rfl | rfl
        · exact (hord y x).2 ⟨rfl, rfl⟩
        · exact absurd rfl hne'

/-- A STRIPS-like problem is regular. -/
theorem IsStripsLike.isRegular {P : Problem F A C I} (h : P.IsStripsLike) : P.IsRegular :=
  ⟨by obtain ⟨c, ⟨t, hT, -⟩, -⟩ := h; exact TaskNetwork.isRegular_of_T_eq_singleton hT,
    h.isRegularM⟩

end Problem

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x) [DecidableEq I]

variable {F A C I}

/-- **`STRIPS ⊆ TO-HTN-REG`.** -/
theorem STRIPS_subset_TO_HTN_REG : STRIPS F A C I ⊆ TO_HTN_REG F A C I :=
  fun _ h => ⟨h.isTO, h.isRegular⟩

/-- **`STRIPS ⊆ TO-HTN-TR`.** -/
theorem STRIPS_subset_TO_HTN_TR : STRIPS F A C I ⊆ TO_HTN_TR F A C I :=
  STRIPS_subset_TO_HTN_REG.trans TO_HTN_REG_subset_TO_HTN_TR

end Classes

/-! ### The encoding of a classical planning problem -/

namespace Strips

variable {F : Type u} {A : Type v}

/-- The subtask network `a c` of the method for the action `a`. -/
def stepNet (a : A) : TaskNetwork ℕ A Unit where
  T := {0, 1}
  ord := fun x y => x = 0 ∧ y = 1
  α := fun i => if i = 0 then Sum.inl a else Sum.inr ()

/-- The empty subtask network (of the method that finishes the plan). -/
def emptyNet : TaskNetwork ℕ A Unit where
  T := ∅
  ord := fun _ _ => False
  α := fun _ => Sum.inr ()

/-- The initial task network: a single occurrence of the compound task. -/
def initNet : TaskNetwork ℕ A Unit where
  T := {0}
  ord := fun _ _ => False
  α := fun _ => Sum.inr ()

/-- A fresh copy of `stepNet a`, using the task identifiers `n+1` and `n+2`. -/
def pairNet (n : ℕ) (a : A) : TaskNetwork ℕ A Unit where
  T := {n + 1, n + 2}
  ord := fun x y => x = n + 1 ∧ y = n + 2
  α := fun i => if i = n + 1 then Sum.inl a else Sum.inr ()

lemma stepNet_wf (a : A) : (stepNet a).WF where
  mem_left := by rintro x y ⟨rfl, -⟩; simp [stepNet]
  mem_right := by rintro x y ⟨-, rfl⟩; simp [stepNet]
  irrefl := by rintro x ⟨rfl, h⟩; exact absurd h (by simp)
  trans := by rintro x y z ⟨rfl, rfl⟩ ⟨h, -⟩; exact absurd h (by simp)

lemma emptyNet_wf : (emptyNet (A := A)).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma initNet_wf : (initNet (A := A)).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma pairNet_wf (n : ℕ) (a : A) : (pairNet n a).WF where
  mem_left := by rintro x y ⟨rfl, -⟩; simp [pairNet]
  mem_right := by rintro x y ⟨-, rfl⟩; simp [pairNet]
  irrefl := by rintro x ⟨rfl, h⟩; omega
  trans := by rintro x y z ⟨rfl, rfl⟩ ⟨h, -⟩; omega

/-- The fresh copy `pairNet n a` is isomorphic to the method's subtask network
`stepNet a`. -/
lemma pairNet_iso (n : ℕ) (a : A) : (pairNet n a).Iso (stepNet a) := by
  refine ⟨fun x => if x = n + 1 then 0 else 1, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [pairNet, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [stepNet]
  · intro x hx y hy hxy
    simp only [pairNet, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
  · intro y hy
    simp only [stepNet, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨n + 1, by simp [pairNet], by simp⟩
    · exact ⟨n + 2, by simp [pairNet], by simp⟩
  · intro x hx y hy
    simp only [pairNet, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [pairNet, stepNet]
  · intro x hx
    simp only [pairNet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [pairNet, stepNet]

/-- **The HTN encoding of a classical planning problem.** -/
def _root_.HTN.ClassicalProblem.toHTN (Pc : ClassicalProblem F A) : Problem F A Unit ℕ where
  toActionModel := Pc.toActionModel
  methods := (Set.range fun a : A => (⟨(), stepNet a⟩ : Method ℕ A Unit)) ∪ {⟨(), emptyNet⟩}
  init := Pc.init
  goal := Pc.goal
  tnI := initNet

variable (Pc : ClassicalProblem F A)

@[simp] lemma toHTN_tnI : Pc.toHTN.tnI = initNet := rfl

@[simp] lemma toHTN_init : Pc.toHTN.init = Pc.init := rfl

@[simp] lemma toHTN_goal : Pc.toHTN.goal = Pc.goal := rfl

/-- The classical problem underlying the encoding is the original classical problem. -/
@[simp] lemma toHTN_toClassicalProblem : Pc.toHTN.toClassicalProblem = Pc := rfl

lemma stepMethod_mem (a : A) : (⟨(), stepNet a⟩ : Method ℕ A Unit) ∈ Pc.toHTN.methods :=
  Or.inl ⟨a, rfl⟩

lemma emptyMethod_mem : (⟨(), emptyNet⟩ : Method ℕ A Unit) ∈ Pc.toHTN.methods :=
  Or.inr rfl

/-- The encoding of a classical planning problem is a STRIPS-like HTN planning problem. -/
theorem toHTN_isStripsLike : Pc.toHTN.IsStripsLike := by
  refine ⟨(), ⟨0, rfl, rfl⟩, ?_⟩
  rintro m ⟨(⟨a, rfl⟩ | hm), -⟩
  · refine ⟨rfl, Or.inr ⟨0, 1, by decide, rfl, ⟨a, rfl⟩, rfl, fun x y => Iff.rfl⟩⟩
  · simp only [Set.mem_singleton_iff] at hm
    subst hm
    exact ⟨rfl, Or.inl rfl⟩

/-- The encoding of a classical planning problem is totally ordered and regular. -/
theorem toHTN_mem_TO_HTN_REG : Pc.toHTN ∈ Classes.TO_HTN_REG F A Unit ℕ :=
  Classes.STRIPS_subset_TO_HTN_REG (toHTN_isStripsLike Pc)

/-- The encoding is well formed. -/
theorem toHTN_wf : Pc.toHTN.WF where
  tnI := initNet_wf
  methods := by
    rintro m (⟨a, rfl⟩ | hm)
    · exact stepNet_wf a
    · simp only [Set.mem_singleton_iff] at hm
      subst hm
      exact emptyNet_wf

/-! ### The chain invariant

Decomposing the initial task network `n` times yields a totally ordered chain of `n` primitive
tasks followed by the compound task; this is the invariant of the correctness proof. -/

/-- `IsOpenChain tn as l n` states that the task network `tn` consists of the primitive tasks
with identifiers `l` (increasing, all of them smaller than `n`) labelled by the actions `as`,
followed by the compound task with identifier `n`, and that the ordering of `tn` is the linear
order of the identifiers. -/
structure IsOpenChain (tn : TaskNetwork ℕ A Unit) (as : List A) (l : List ℕ) (n : ℕ) : Prop where
  /-- The primitive task ids are strictly increasing. -/
  sorted : l.Pairwise (· < ·)
  /-- All primitive task ids are smaller than the id of the compound task. -/
  lt : ∀ i ∈ l, i < n
  /-- The task ids of `tn` are the primitive ones together with the compound one. -/
  memT : ∀ x, x ∈ tn.T ↔ (x ∈ l ∨ x = n)
  /-- The primitive tasks are labelled by the actions `as`. -/
  labels : l.map tn.α = as.map Sum.inl
  /-- The last task is the compound task. -/
  compound : tn.α n = Sum.inr ()
  /-- The ordering is the linear order of the identifiers. -/
  ord : ∀ x y, tn.ord x y ↔ (x ∈ tn.T ∧ y ∈ tn.T ∧ x < y)

namespace IsOpenChain

variable {tn : TaskNetwork ℕ A Unit} {as : List A} {l : List ℕ} {n : ℕ}

lemma le_of_memT (hc : IsOpenChain tn as l n) {x : ℕ} (hx : x ∈ tn.T) : x ≤ n := by
  rcases (hc.memT x).1 hx with hx | rfl
  · exact le_of_lt (hc.lt x hx)
  · exact le_rfl

lemma mem_T_compound (hc : IsOpenChain tn as l n) : n ∈ tn.T := (hc.memT n).2 (Or.inr rfl)

lemma isPrimitiveId (hc : IsOpenChain tn as l n) {x : ℕ} (hx : x ∈ l) : tn.IsPrimitiveId x := by
  have : tn.α x ∈ l.map tn.α := List.mem_map_of_mem hx
  rw [hc.labels] at this
  obtain ⟨a, -, ha⟩ := List.mem_map.1 this
  exact ⟨a, ha.symm⟩

end IsOpenChain

/-- The initial task network is an open chain for the empty plan. -/
lemma isOpenChain_initNet : IsOpenChain (initNet (A := A)) [] [] 0 where
  sorted := List.Pairwise.nil
  lt := by simp
  memT := by intro x; simp [initNet]
  labels := rfl
  compound := rfl
  ord := by
    intro x y
    constructor
    · intro h; exact (h : False).elim
    · rintro ⟨hx, hy, hlt⟩
      simp only [initNet, Finset.mem_singleton] at hx hy
      omega

/-! ### One decomposition step: appending an action -/

/-- Decomposing the compound task of an open chain with the method for the action `a` yields
the open chain of the plan extended by `a`. -/
theorem isOpenChain_step {tn : TaskNetwork ℕ A Unit} {as : List A} {l : List ℕ} {n : ℕ}
    (hc : IsOpenChain tn as l n) (a : A) :
    IsOpenChain (decomposeWith tn n (pairNet n a)) (as ++ [a]) (l ++ [n + 1]) (n + 2) := by
  have hpair : ∀ x : ℕ, x ∈ (pairNet n a : TaskNetwork ℕ A Unit).T ↔ (x = n + 1 ∨ x = n + 2) := by
    intro x; simp [pairNet]
  have hmem : ∀ x : ℕ, x ∈ (decomposeWith tn n (pairNet n a)).T ↔
      (x ∈ l ∨ x = n + 1 ∨ x = n + 2) := by
    intro x
    rw [mem_decomposeWith_T, hpair]
    constructor
    · rintro (⟨hx, hxn⟩ | hx)
      · rcases (hc.memT x).1 hx with hx' | rfl
        · exact Or.inl hx'
        · exact absurd rfl hxn
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl ⟨(hc.memT x).2 (Or.inl hx), by have := hc.lt x hx; omega⟩
      · exact Or.inr hx
  have hnotmem : ∀ x ∈ l, x ∉ (pairNet n a : TaskNetwork ℕ A Unit).T := by
    intro x hx hcon
    have := hc.lt x hx
    rcases (hpair x).1 hcon with rfl | rfl <;> omega
  have hmem' : ∀ x : ℕ, x ∈ (decomposeWith tn n (pairNet n a)).T ↔
      (x ∈ l ++ [n + 1] ∨ x = n + 2) := by
    intro x
    rw [hmem x]
    simp only [List.mem_append, List.mem_singleton]
    tauto
  refine ⟨?_, ?_, hmem', ?_, ?_, ?_⟩
  · refine List.pairwise_append.2 ⟨hc.sorted, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    have := hc.lt x hx
    simp only [List.mem_singleton] at hy
    omega
  · intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · have := hc.lt i hi; omega
    · simp only [List.mem_singleton] at hi; omega
  · rw [List.map_append, List.map_append]
    congr 1
    · rw [← hc.labels]
      refine List.map_congr_left ?_
      intro x hx
      simp [decomposeWith_α, hnotmem x hx]
    · simp [decomposeWith_α, pairNet]
  · simp [decomposeWith_α, pairNet]
  · intro x y
    rw [decomposeWith_ord_iff, hmem, hmem]
    constructor
    · rintro (hord | ⟨hxn, hy⟩ | ⟨hny, hx⟩ | ⟨hord, hxn, hyn⟩)
      · obtain ⟨rfl, rfl⟩ : x = n + 1 ∧ y = n + 2 := hord
        exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), by omega⟩
      · obtain ⟨hxT, -, hlt⟩ := (hc.ord x n).1 hxn
        rcases (hc.memT x).1 hxT with hx' | rfl
        · rcases (hpair y).1 hy with rfl | rfl <;>
            exact ⟨Or.inl hx', by simp, by omega⟩
        · omega
      · obtain ⟨-, hyT, hlt⟩ := (hc.ord n y).1 hny
        have := hc.le_of_memT hyT
        omega
      · obtain ⟨hxT, hyT, hlt⟩ := (hc.ord x y).1 hord
        rcases (hc.memT x).1 hxT with hx' | rfl
        · rcases (hc.memT y).1 hyT with hy' | rfl
          · exact ⟨Or.inl hx', Or.inl hy', hlt⟩
          · exact absurd rfl hyn
        · exact absurd rfl hxn
    · rintro ⟨hx, hy, hlt⟩
      rcases hx with hx | rfl | rfl
      · have hxn := hc.lt x hx
        rcases hy with hy | rfl | rfl
        · refine Or.inr (Or.inr (Or.inr ⟨(hc.ord x y).2 ⟨(hc.memT x).2 (Or.inl hx),
            (hc.memT y).2 (Or.inl hy), hlt⟩, by omega, ?_⟩))
          have := hc.lt y hy
          omega
        · exact Or.inr (Or.inl ⟨(hc.ord x n).2 ⟨(hc.memT x).2 (Or.inl hx),
            hc.mem_T_compound, hxn⟩, (hpair _).2 (Or.inl rfl)⟩)
        · exact Or.inr (Or.inl ⟨(hc.ord x n).2 ⟨(hc.memT x).2 (Or.inl hx),
            hc.mem_T_compound, hxn⟩, (hpair _).2 (Or.inr rfl)⟩)
      · rcases hy with hy | rfl | rfl
        · have := hc.lt y hy; omega
        · omega
        · exact Or.inl ⟨rfl, rfl⟩
      · rcases hy with hy | rfl | rfl
        · have := hc.lt y hy; omega
        · omega
        · omega

/-- The decomposition step of `isOpenChain_step` is a legal decomposition step of the encoded
problem. -/
theorem decompStep_step {tn : TaskNetwork ℕ A Unit} {as : List A} {l : List ℕ} {n : ℕ}
    (hc : IsOpenChain tn as l n) (a : A) :
    DecompStep' Pc.toHTN.methods tn (decomposeWith tn n (pairNet n a)) := by
  refine ⟨n, ⟨(), stepNet a⟩, stepMethod_mem Pc a, hc.mem_T_compound, hc.compound,
    pairNet n a, pairNet_wf n a, pairNet_iso n a, ?_, rfl⟩
  refine Finset.disjoint_left.2 ?_
  intro x hx hcon
  have hle := hc.le_of_memT hx
  simp only [pairNet, Finset.mem_insert, Finset.mem_singleton] at hcon
  omega

/-- Every plan of the classical problem can be produced by decomposing the initial task
network of the encoding. -/
theorem exists_openChain (as : List A) :
    ∃ (tn : TaskNetwork ℕ A Unit) (l : List ℕ) (n : ℕ),
      Pc.toHTN.Reachable tn ∧ IsOpenChain tn as l n := by
  induction as using List.reverseRecOn with
  | nil => exact ⟨initNet, [], 0, Relation.ReflTransGen.refl, isOpenChain_initNet⟩
  | append_singleton as a ih =>
    obtain ⟨tn, l, n, hreach, hc⟩ := ih
    exact ⟨decomposeWith tn n (pairNet n a), l ++ [n + 1], n + 2,
      Relation.ReflTransGen.tail hreach (decompStep_step Pc hc a), isOpenChain_step hc a⟩

/-! ### Closing the chain -/

/-- Decomposing the last compound task of an open chain with the empty method yields a
primitive task network whose (unique) linearization induces the plan. -/
theorem decompStep_close {tn : TaskNetwork ℕ A Unit} {as : List A} {l : List ℕ} {n : ℕ}
    (hc : IsOpenChain tn as l n) :
    DecompStep' Pc.toHTN.methods tn (decomposeWith tn n emptyNet) ∧
      (decomposeWith tn n (emptyNet (A := A))).IsPrimitive ∧
      (decomposeWith tn n (emptyNet (A := A))).IsLinearization l ∧
      (decomposeWith tn n (emptyNet (A := A))).IsActionSeq l as := by
  have hmem : ∀ x : ℕ, x ∈ (decomposeWith tn n (emptyNet (A := A))).T ↔ x ∈ l := by
    intro x
    rw [mem_decomposeWith_T]
    constructor
    · rintro (⟨hx, hxn⟩ | hx)
      · rcases (hc.memT x).1 hx with hx' | rfl
        · exact hx'
        · exact absurd rfl hxn
      · exact absurd hx (by simp [emptyNet])
    · intro hx
      exact Or.inl ⟨(hc.memT x).2 (Or.inl hx), by have := hc.lt x hx; omega⟩
  have hα : ∀ x ∈ l, (decomposeWith tn n (emptyNet (A := A))).α x = tn.α x := by
    intro x _
    simp [decomposeWith_α, emptyNet]
  have hord : ∀ x y, (decomposeWith tn n (emptyNet (A := A))).ord x y → x < y := by
    intro x y h
    rcases decomposeWith_ord_iff.1 h with h | ⟨-, hy⟩ | ⟨-, hx⟩ | ⟨h, -, -⟩
    · exact absurd h (by simp [emptyNet])
    · exact absurd hy (by simp [emptyNet])
    · exact absurd hx (by simp [emptyNet])
    · exact ((hc.ord x y).1 h).2.2
  refine ⟨⟨n, ⟨(), emptyNet⟩, emptyMethod_mem Pc, hc.mem_T_compound, hc.compound,
    emptyNet, emptyNet_wf, TaskNetwork.Iso.refl _, ?_, rfl⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [emptyNet]
  · intro x hx
    obtain ⟨a, ha⟩ := hc.isPrimitiveId ((hmem x).1 hx)
    exact ⟨a, by rw [hα x ((hmem x).1 hx)]; exact ha⟩
  · exact List.Pairwise.nodup hc.sorted
  · intro t; rw [hmem]
  · refine List.Pairwise.imp ?_ hc.sorted
    intro x y hxy hcon
    have := hord y x hcon
    omega
  · show l.map (decomposeWith tn n (emptyNet (A := A))).α = as.map Sum.inl
    rw [← hc.labels]
    exact List.map_congr_left hα

/-! ### Correctness of the encoding -/

/-- **The encoding preserves and reflects solvability.** -/
theorem toHTN_solvable_iff : Pc.toHTN.Solvable ↔ Pc.Solvable := by
  constructor
  · intro h
    simpa using h.classical
  · rintro ⟨as, happ, hgoal⟩
    obtain ⟨tn, l, n, hreach, hc⟩ := exists_openChain Pc as
    obtain ⟨hstep, hprim, hlin, hseq⟩ := decompStep_close Pc hc
    refine ⟨decomposeWith tn n emptyNet, Relation.ReflTransGen.tail hreach hstep, hprim,
      l, as, hlin, hseq, ?_, ?_⟩
    · exact happ
    · exact hgoal

/-- **The encoding preserves plans exactly**: every solution of the classical problem is,
literally, a solution plan of its HTN encoding (so the encoding is linear in the sense of the
compilation-scheme definition, with no blow-up of the plan at all). -/
theorem toHTN_isSolutionPlan {as : List A} (h : Pc.IsSolution as) :
    Pc.toHTN.IsSolutionPlan as := by
  obtain ⟨tn, l, n, hreach, hc⟩ := exists_openChain Pc as
  obtain ⟨hstep, hprim, hlin, hseq⟩ := decompStep_close Pc hc
  exact ⟨decomposeWith tn n emptyNet, l, Relation.ReflTransGen.tail hreach hstep, hprim,
    hlin, hseq, h.1, h.2⟩

/-- Conversely, every solution plan of the encoding is a solution of the classical problem. -/
theorem isSolution_of_toHTN_isSolutionPlan {as : List A} (h : Pc.toHTN.IsSolutionPlan as) :
    Pc.IsSolution as := by
  simpa using h.classical

/-! ### The size of the encoding

The encoding is *linear*: the compiled HTN domain is at most a constant factor larger than the
classical domain it is built from.  (As instructed, the statement that the construction can be
carried out in polynomial time is not formalised; the statement below is about the size of the
result of the construction.) -/

section Size

variable [Fintype A]

open scoped Classical in
/-- The method set of the encoding, as a finite set. -/
lemma toHTN_methods_eq :
    Pc.toHTN.methods = ((Finset.univ.image fun a : A => (⟨(), stepNet a⟩ : Method ℕ A Unit)) ∪
      {⟨(), emptyNet⟩} : Finset (Method ℕ A Unit)) := by
  ext m
  simp [ClassicalProblem.toHTN]

omit [Fintype A] in
/-- Every method of the encoding has size at most `7`. -/
lemma method_size_le {m : Method ℕ A Unit} (hm : m ∈ Pc.toHTN.methods) : m.size ≤ 7 := by
  have hstep : ∀ a : A, (⟨(), stepNet a⟩ : Method ℕ A Unit).size ≤ 7 := by
    intro a
    have hcard : (stepNet a : TaskNetwork ℕ A Unit).T.card = 2 := by
      simp [stepNet]
    have := (stepNet a : TaskNetwork ℕ A Unit).size_le
    rw [hcard] at this
    simpa [Method.size] using Nat.add_le_add_left this 1
  rcases hm with ⟨a, rfl⟩ | hm
  · exact hstep a
  · simp only [Set.mem_singleton_iff] at hm
    subst hm
    have hcard : (emptyNet : TaskNetwork ℕ A Unit).T.card = 0 := by simp [emptyNet]
    have := (emptyNet : TaskNetwork ℕ A Unit).size_le
    rw [hcard] at this
    simp only [Method.size]
    omega

/-- The total size of the methods of the encoding is linear in the number of actions. -/
lemma toHTN_methods_size_le :
    (∑ᶠ m ∈ Pc.toHTN.methods, m.size) ≤ 7 * Nat.card A + 7 := by
  classical
  rw [toHTN_methods_eq Pc, finsum_mem_coe_finset]
  calc
    ∑ m ∈ ((Finset.univ.image fun a : A => (⟨(), stepNet a⟩ : Method ℕ A Unit)) ∪
        {⟨(), emptyNet⟩}), m.size
        ≤ ∑ m ∈ (Finset.univ.image fun a : A => (⟨(), stepNet a⟩ : Method ℕ A Unit)), m.size +
            ∑ m ∈ ({⟨(), emptyNet⟩} : Finset (Method ℕ A Unit)), m.size := by
          calc _ ≤ _ + ∑ m ∈ ((Finset.univ.image fun a : A => (⟨(), stepNet a⟩ :
                    Method ℕ A Unit)) ∩ {⟨(), emptyNet⟩}), m.size := Nat.le_add_right _ _
            _ = _ := Finset.sum_union_inter
    _ ≤ 7 * Nat.card A + 7 := by
        have h₁ : ∑ m ∈ (Finset.univ.image fun a : A => (⟨(), stepNet a⟩ : Method ℕ A Unit)),
            m.size ≤ 7 * Nat.card A := by
          have hle : ∀ m ∈ (Finset.univ.image fun a : A => (⟨(), stepNet a⟩ : Method ℕ A Unit)),
              m.size ≤ 7 := by
            intro m hm
            obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hm
            exact method_size_le Pc (Or.inl ⟨a, rfl⟩)
          calc _ ≤ (Finset.univ.image fun a : A => (⟨(), stepNet a⟩ :
                  Method ℕ A Unit)).card • 7 := Finset.sum_le_card_nsmul _ _ 7 hle
            _ ≤ (Finset.univ : Finset A).card • 7 :=
                Nat.mul_le_mul_right _ (Finset.card_image_le)
            _ = 7 * Nat.card A := by
                rw [Nat.card_eq_fintype_card, Finset.card_univ]
                simp [Nat.mul_comm]
        have h₂ : ∑ m ∈ ({⟨(), emptyNet⟩} : Finset (Method ℕ A Unit)), m.size ≤ 7 := by
          simpa using method_size_le Pc (emptyMethod_mem Pc)
        omega

/-- **The encoding has linear size.** -/
theorem toHTN_domain_size_le :
    Pc.toHTN.domain.size ≤ 8 * Pc.toActionModel.size + 8 := by
  have hcard : Nat.card A ≤ ∑ᶠ a : A, Pc.actionSize a := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← Finset.card_univ]
    calc (Finset.univ : Finset A).card = ∑ _a ∈ Finset.univ, 1 := by simp
      _ ≤ ∑ a ∈ Finset.univ, Pc.actionSize a :=
          Finset.sum_le_sum (fun x _ => by simp only [ActionModel.actionSize]; omega)
  have hmethods := toHTN_methods_size_le Pc
  have hsize : Pc.toHTN.domain.size =
      Nat.card F + Nat.card Unit + (∑ᶠ a : A, Pc.actionSize a) +
        (∑ᶠ m ∈ Pc.toHTN.methods, m.size) := rfl
  have hunit : Nat.card Unit = 1 := by simp
  have hactionmodel : Pc.toActionModel.size = Nat.card F + ∑ᶠ a : A, Pc.actionSize a := rfl
  omega

end Size

end Strips

end HTN
