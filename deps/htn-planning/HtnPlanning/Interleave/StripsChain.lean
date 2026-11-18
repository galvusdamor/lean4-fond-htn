import HtnPlanning.Core.Strips
/-!
# Plans of a STRIPS-like hierarchy

`HtnPlanning/Core/Strips.lean` encodes a classical planning problem as an HTN problem whose
only compound task `c` decomposes either into nothing or into an action followed by `c`, and
proves that the encoding is solvable exactly when the classical problem is.  That development
is tied to the *particular* encoding it builds (one method for every action of the type, the
compound name `Unit`).

This file redoes its chain argument for an **arbitrary** hierarchy of that shape, which is what
a compilation into the class `STRIPS` produces:

* `HTN.StripsChain.IsStepBody nt c₀ a` — `nt` is a body decomposing `c₀` into the action `a`
  followed by `c₀`;
* `HTN.StripsChain.exists_solution_of_plan` — if the method set contains such a body for every
  action of `as` and an empty body for `c₀`, then the network consisting of the single compound
  task `c₀` can be decomposed into a primitive network whose linearization induces `as`.

Together with `HTN.Problem.Solvable.classical` — the converse direction, which holds for every
hierarchy — this characterises solvability of a STRIPS-like problem as classical plan existence
over the actions the hierarchy offers.
-/

namespace HTN

namespace StripsChain

universe u v w

variable {F : Type u} {A : Type v} {C : Type w}

/-- **A step body**: the subtask network of a method decomposing `c₀` into the action `a`
followed by `c₀`. -/
def IsStepBody (nt : TaskNetwork ℕ A C) (c₀ : C) (a : A) : Prop :=
  ∃ t₁ t₂ : ℕ, t₁ ≠ t₂ ∧ nt.T = {t₁, t₂} ∧ nt.α t₁ = Sum.inl a ∧ nt.α t₂ = Sum.inr c₀ ∧
    ∀ x y, nt.ord x y ↔ (x = t₁ ∧ y = t₂)

/-- A fresh copy of a step body for `a`, on the identifiers `n+1` and `n+2`. -/
def pairNet (c₀ : C) (n : ℕ) (a : A) : TaskNetwork ℕ A C where
  T := {n + 1, n + 2}
  ord := fun x y => x = n + 1 ∧ y = n + 2
  α := fun i => if i = n + 1 then Sum.inl a else Sum.inr c₀

lemma pairNet_wf (c₀ : C) (n : ℕ) (a : A) : (pairNet c₀ n a).WF where
  mem_left := by rintro x y ⟨rfl, -⟩; simp [pairNet]
  mem_right := by rintro x y ⟨-, rfl⟩; simp [pairNet]
  irrefl := by rintro x ⟨rfl, h⟩; omega
  trans := by rintro x y z ⟨rfl, rfl⟩ ⟨h, -⟩; omega

/-- The fresh copy is isomorphic to any step body for the same action. -/
lemma pairNet_iso {nt : TaskNetwork ℕ A C} {c₀ : C} {a : A} (h : IsStepBody nt c₀ a) (n : ℕ) :
    (pairNet c₀ n a).Iso nt := by
  obtain ⟨t₁, t₂, hne, hT, hα₁, hα₂, hord⟩ := h
  refine ⟨fun x => if x = n + 1 then t₁ else t₂, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [pairNet, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [hT]
  · intro x hx y hy hxy
    simp only [pairNet, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
  · intro y hy
    simp only [hT, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨n + 1, by simp [pairNet], by simp⟩
    · exact ⟨n + 2, by simp [pairNet], by simp⟩
  · intro x hx y hy
    simp only [pairNet, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [pairNet, hord, hne, hne.symm]
  · intro x hx
    simp only [pairNet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [pairNet, hα₁, hα₂]

/-! ### The chain invariant -/

/-- `IsOpenChain c₀ tn as l n`: the network `tn` consists of the primitive tasks `l`
(increasing, all below `n`) labelled by `as`, followed by the compound task `c₀` with the
identifier `n`, ordered linearly by the identifiers. -/
structure IsOpenChain (c₀ : C) (tn : TaskNetwork ℕ A C) (as : List A) (l : List ℕ) (n : ℕ) :
    Prop where
  /-- The primitive task ids are strictly increasing. -/
  sorted : l.Pairwise (· < ·)
  /-- All primitive task ids are smaller than the id of the compound task. -/
  lt : ∀ i ∈ l, i < n
  /-- The task ids are the primitive ones together with the compound one. -/
  memT : ∀ x, x ∈ tn.T ↔ (x ∈ l ∨ x = n)
  /-- The primitive tasks are labelled by the actions `as`. -/
  labels : l.map tn.α = as.map Sum.inl
  /-- The last task is the compound task. -/
  compound : tn.α n = Sum.inr c₀
  /-- The ordering is the linear order of the identifiers. -/
  ord : ∀ x y, tn.ord x y ↔ (x ∈ tn.T ∧ y ∈ tn.T ∧ x < y)

namespace IsOpenChain

variable {c₀ : C} {tn : TaskNetwork ℕ A C} {as : List A} {l : List ℕ} {n : ℕ}

lemma le_of_memT (hc : IsOpenChain c₀ tn as l n) {x : ℕ} (hx : x ∈ tn.T) : x ≤ n := by
  rcases (hc.memT x).1 hx with hx | rfl
  · exact le_of_lt (hc.lt x hx)
  · exact le_rfl

lemma mem_T_compound (hc : IsOpenChain c₀ tn as l n) : n ∈ tn.T := (hc.memT n).2 (Or.inr rfl)

lemma isPrimitiveId (hc : IsOpenChain c₀ tn as l n) {x : ℕ} (hx : x ∈ l) :
    tn.IsPrimitiveId x := by
  have : tn.α x ∈ l.map tn.α := List.mem_map_of_mem hx
  rw [hc.labels] at this
  obtain ⟨a, -, ha⟩ := List.mem_map.1 this
  exact ⟨a, ha.symm⟩

end IsOpenChain

/-- A single compound task is an open chain for the empty plan. -/
lemma isOpenChain_single {c₀ : C} {tn : TaskNetwork ℕ A C} {n₀ : ℕ} (hT : tn.T = {n₀})
    (hα : tn.α n₀ = Sum.inr c₀) (hord : ∀ x y, ¬ tn.ord x y) :
    IsOpenChain c₀ tn [] [] n₀ where
  sorted := List.Pairwise.nil
  lt := by simp
  memT := by intro x; simp [hT]
  labels := rfl
  compound := hα
  ord := by
    intro x y
    refine ⟨fun h => absurd h (hord x y), ?_⟩
    rintro ⟨hx, hy, hlt⟩
    rw [hT] at hx hy
    simp only [Finset.mem_singleton] at hx hy
    omega

/-! ### One decomposition step: appending an action -/

/-- Decomposing the compound task of an open chain with a step body for `a` yields the open
chain of the plan extended by `a`. -/
theorem isOpenChain_step {c₀ : C} {tn : TaskNetwork ℕ A C} {as : List A} {l : List ℕ} {n : ℕ}
    (hc : IsOpenChain c₀ tn as l n) (a : A) :
    IsOpenChain c₀ (decomposeWith tn n (pairNet c₀ n a)) (as ++ [a]) (l ++ [n + 1]) (n + 2) := by
  have hpair : ∀ x : ℕ, x ∈ (pairNet c₀ n a).T ↔ (x = n + 1 ∨ x = n + 2) := by
    intro x; simp [pairNet]
  have hmem : ∀ x : ℕ, x ∈ (decomposeWith tn n (pairNet c₀ n a)).T ↔
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
  have hnotmem : ∀ x ∈ l, x ∉ (pairNet c₀ n a).T := by
    intro x hx hcon
    have := hc.lt x hx
    rcases (hpair x).1 hcon with rfl | rfl <;> omega
  have hmem' : ∀ x : ℕ, x ∈ (decomposeWith tn n (pairNet c₀ n a)).T ↔
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

section Steps

variable {M : Set (Method ℕ A C)} {c₀ : C}

/-- Appending an action is a legal decomposition step. -/
theorem decompStep_step {tn : TaskNetwork ℕ A C} {as : List A} {l : List ℕ} {n : ℕ}
    (hc : IsOpenChain c₀ tn as l n) {a : A} {nt : TaskNetwork ℕ A C}
    (hmem : (⟨c₀, nt⟩ : Method ℕ A C) ∈ M) (hbody : IsStepBody nt c₀ a) :
    DecompStep' M tn (decomposeWith tn n (pairNet c₀ n a)) := by
  refine ⟨n, ⟨c₀, nt⟩, hmem, hc.mem_T_compound, hc.compound,
    pairNet c₀ n a, pairNet_wf c₀ n a, pairNet_iso hbody n, ?_, rfl⟩
  refine Finset.disjoint_left.2 ?_
  intro x hx hcon
  have hle := hc.le_of_memT hx
  simp only [pairNet, Finset.mem_insert, Finset.mem_singleton] at hcon
  omega

/-- Every plan over the available actions can be laid out as an open chain. -/
theorem exists_openChain {tn₀ : TaskNetwork ℕ A C} {n₀ : ℕ} (hc₀ : IsOpenChain c₀ tn₀ [] [] n₀)
    {Acts : Set A} (hstep : ∀ a ∈ Acts, ∃ nt, (⟨c₀, nt⟩ : Method ℕ A C) ∈ M ∧ IsStepBody nt c₀ a)
    (as : List A) (has : ∀ a ∈ as, a ∈ Acts) :
    ∃ (tn : TaskNetwork ℕ A C) (l : List ℕ) (n : ℕ),
      DecomposesTo M tn₀ tn ∧ IsOpenChain c₀ tn as l n := by
  induction as using List.reverseRecOn with
  | nil => exact ⟨tn₀, [], n₀, Relation.ReflTransGen.refl, hc₀⟩
  | append_singleton as a ih =>
    obtain ⟨tn, l, n, hreach, hc⟩ := ih fun b hb => has b (by simp [hb])
    obtain ⟨nt, hmem, hbody⟩ := hstep a (has a (by simp))
    exact ⟨decomposeWith tn n (pairNet c₀ n a), l ++ [n + 1], n + 2,
      Relation.ReflTransGen.tail hreach (decompStep_step hc hmem hbody), isOpenChain_step hc a⟩

/-- Closing the chain with an empty body yields a primitive network whose linearization induces
the plan. -/
theorem decompStep_close {tn : TaskNetwork ℕ A C} {as : List A} {l : List ℕ} {n : ℕ}
    (hc : IsOpenChain c₀ tn as l n) {ne : TaskNetwork ℕ A C}
    (hmem : (⟨c₀, ne⟩ : Method ℕ A C) ∈ M) (hnewf : ne.WF) (hne : ne.T = ∅) :
    DecompStep' M tn (decomposeWith tn n ne) ∧
      (decomposeWith tn n ne).IsPrimitive ∧
      (decomposeWith tn n ne).IsLinearization l ∧
      (decomposeWith tn n ne).IsActionSeq l as := by
  have hnemem : ∀ x : ℕ, x ∉ ne.T := by
    intro x hx
    rw [hne] at hx
    exact absurd hx (Finset.notMem_empty x)
  have hmemT : ∀ x : ℕ, x ∈ (decomposeWith tn n ne).T ↔ x ∈ l := by
    intro x
    rw [mem_decomposeWith_T]
    constructor
    · rintro (⟨hx, hxn⟩ | hx)
      · rcases (hc.memT x).1 hx with hx' | rfl
        · exact hx'
        · exact absurd rfl hxn
      · exact absurd hx (hnemem x)
    · intro hx
      exact Or.inl ⟨(hc.memT x).2 (Or.inl hx), by have := hc.lt x hx; omega⟩
  have hα : ∀ x ∈ l, (decomposeWith tn n ne).α x = tn.α x := by
    intro x _
    simp [decomposeWith_α, hnemem x]
  have hordne : ∀ x y : ℕ, ¬ ne.ord x y := fun x _ h => hnemem x (hnewf.mem_left h)
  have hordlt : ∀ x y, (decomposeWith tn n ne).ord x y → x < y := by
    intro x y h
    rcases decomposeWith_ord_iff.1 h with h | ⟨-, hy⟩ | ⟨-, hx⟩ | ⟨h, -, -⟩
    · exact absurd h (hordne x y)
    · exact absurd hy (hnemem y)
    · exact absurd hx (hnemem x)
    · exact ((hc.ord x y).1 h).2.2
  refine ⟨⟨n, ⟨c₀, ne⟩, hmem, hc.mem_T_compound, hc.compound,
    ne, hnewf, TaskNetwork.Iso.refl _, ?_, rfl⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hne]
    exact Finset.disjoint_empty_right _
  · intro x hx
    obtain ⟨a, ha⟩ := hc.isPrimitiveId ((hmemT x).1 hx)
    exact ⟨a, by rw [hα x ((hmemT x).1 hx)]; exact ha⟩
  · exact List.Pairwise.nodup hc.sorted
  · intro t; rw [hmemT]
  · refine List.Pairwise.imp ?_ hc.sorted
    intro x y hxy hcon
    have := hordlt y x hcon
    omega
  · show l.map (decomposeWith tn n ne).α = as.map Sum.inl
    rw [← hc.labels]
    exact List.map_congr_left hα

/-- **Every plan over the available actions is produced by the hierarchy.** -/
theorem exists_solution_of_plan {tn₀ : TaskNetwork ℕ A C} {n₀ : ℕ}
    (hc₀ : IsOpenChain c₀ tn₀ [] [] n₀)
    {Acts : Set A} (hstep : ∀ a ∈ Acts, ∃ nt, (⟨c₀, nt⟩ : Method ℕ A C) ∈ M ∧ IsStepBody nt c₀ a)
    {ne : TaskNetwork ℕ A C} (hmem : (⟨c₀, ne⟩ : Method ℕ A C) ∈ M) (hnewf : ne.WF)
    (hne : ne.T = ∅) {as : List A} (has : ∀ a ∈ as, a ∈ Acts) :
    ∃ tn : TaskNetwork ℕ A C, DecomposesTo M tn₀ tn ∧ tn.IsPrimitive ∧
      ∃ l : List ℕ, tn.IsLinearization l ∧ tn.IsActionSeq l as := by
  obtain ⟨tn, l, n, hreach, hc⟩ := exists_openChain hc₀ hstep as has
  obtain ⟨hstep', hprim, hlin, hseq⟩ := decompStep_close hc hmem hnewf hne
  exact ⟨decomposeWith tn n ne, Relation.ReflTransGen.tail hreach hstep', hprim, l, hlin, hseq⟩

end Steps

end StripsChain

end HTN
