import HtnPlanning.Interleave.NetYield
import HtnPlanning.Core.Construction
/-!
# Additive invariants of decomposition

Many statements about a plan of an HTN problem are *counting* statements: an action of one kind
occurs as often as an action of another kind.  Such statements are best proved not along the
plan but along the *hierarchy*: if a weight `ω : A ⊕ C → ℤ` is such that the subtask network of
every method weighs exactly as much as the task it decomposes (`HTN.Balanced`), then
decomposition does not change the weight of a task network, so the weight of the initial task
network is the weight of every plan.

* `HTN.TaskNetwork.weight ω tn` — the total weight `∑_{t ∈ T} ω(α(t))` of a task network;
* `HTN.TaskNetwork.weight_iso` — the weight only depends on the network up to renaming;
* `HTN.weight_of_decompStep`, `HTN.weight_of_decomposesTo` — a balanced weight is invariant
  under decomposition;
* `HTN.weight_of_netYield` — **the weight of a refinement**: if `tn` refines into the action
  sequence `as` then `∑_{a ∈ as} ω(a) = ω(tn)`.

The application in this development is the lock-step counting argument for the Turing-machine
encoding (`HtnComplexity/TMEnc/TMEncCount.lean`), where the weights count the four actions of a
synchronisation channel.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace TaskNetwork

/-- The total weight of a task network for a weight function on task names. -/
def weight (ω : A ⊕ C → ℤ) (tn : TaskNetwork I A C) : ℤ :=
  ∑ t ∈ tn.T, ω (tn.α t)

variable {ω : A ⊕ C → ℤ}

/-- **The weight of a task network does not change under renaming of the task ids.** -/
lemma weight_iso {tn tn' : TaskNetwork I A C} (h : tn.Iso tn') :
    weight ω tn = weight ω tn' := by
  obtain ⟨σ, hbij, -, hα⟩ := h
  refine Finset.sum_bij (fun t _ => σ t) (fun t ht => by simpa using hbij.mapsTo (by simpa using ht))
    (fun t ht t' ht' hst => hbij.injOn (by simpa using ht) (by simpa using ht') hst)
    (fun t ht => ?_) (fun t ht => congrArg ω (hα t ht))
  obtain ⟨u, hu, rfl⟩ := hbij.surjOn (show t ∈ (tn'.T : Set I) by simpa using ht)
  exact ⟨u, by simpa using hu, rfl⟩

/-- **The weight of a decomposed network.**  Decomposing the task `t` of `tn₁` by the (disjoint)
network `tn'` removes the weight of `t` and adds the weight of `tn'`. -/
lemma weight_decomposeWith [DecidableEq I] {tn₁ tn' : TaskNetwork I A C} {t : I}
    (ht : t ∈ tn₁.T) (hdisj : Disjoint tn₁.T tn'.T) :
    weight ω (decomposeWith tn₁ t tn') = weight ω tn₁ - ω (tn₁.α t) + weight ω tn' := by
  have hdisj' : Disjoint (tn₁.T.erase t) tn'.T :=
    Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
  have hsplit : weight ω (decomposeWith tn₁ t tn') =
      (∑ x ∈ tn₁.T.erase t, ω ((decomposeWith tn₁ t tn').α x)) +
        ∑ x ∈ tn'.T, ω ((decomposeWith tn₁ t tn').α x) := by
    rw [weight, decomposeWith_T, Finset.sum_union hdisj']
  rw [hsplit]
  have h₁ : ∀ x ∈ tn₁.T.erase t, ω ((decomposeWith tn₁ t tn').α x) = ω (tn₁.α x) := by
    intro x hx
    have hx' : x ∉ tn'.T := by
      have hx₁ : x ∈ tn₁.T := Finset.mem_of_mem_erase hx
      exact fun hcon => (Finset.disjoint_left.1 hdisj hx₁) hcon
    rw [decomposeWith_α, if_neg hx']
  have h₂ : ∀ x ∈ tn'.T, ω ((decomposeWith tn₁ t tn').α x) = ω (tn'.α x) := by
    intro x hx
    rw [decomposeWith_α, if_pos hx]
  rw [Finset.sum_congr rfl h₁, Finset.sum_congr rfl h₂]
  have : ∑ x ∈ tn₁.T, ω (tn₁.α x) = ω (tn₁.α t) + ∑ x ∈ tn₁.T.erase t, ω (tn₁.α x) :=
    (Finset.add_sum_erase _ _ ht).symm
  rw [weight, weight, this]
  ring

/-! ### The weight of the grid networks -/

section Grid

variable [Inhabited A]

omit [Inhabited A] in
/-- The sum of a weight over the indices of a list. -/
lemma sum_range_getD {X : Type*} (f : X → ℤ) (r : List X) (d : X) :
    ∑ i ∈ Finset.range r.length, f (r.getD i d) = (r.map f).sum := by
  induction r with
  | nil => simp
  | cons a r ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih]
      simp [add_comm]

/-- **The weight of a grid** is the weight of all the tasks occurring in it. -/
lemma weight_grid (ω : A ⊕ C → ℤ) (ls : List (List (A ⊕ C))) :
    weight ω (grid ls) = (ls.flatten.map ω).sum := by
  have hdisj : (↑(Finset.range ls.length) : Set ℕ).PairwiseDisjoint
      fun i => (Finset.range (ls.getD i []).length).image fun j => ((i, j) : ℕ × ℕ) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 ?_
    rintro ⟨a, b⟩ ha hb
    simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at ha hb
    obtain ⟨-, -, rfl, -⟩ := ha
    obtain ⟨-, -, h, -⟩ := hb
    exact hij h.symm
  rw [weight]
  show ∑ p ∈ (Finset.range ls.length).biUnion
      (fun i => (Finset.range (ls.getD i []).length).image fun j => ((i, j) : ℕ × ℕ)),
      ω ((grid ls).α p) = _
  rw [Finset.sum_biUnion hdisj]
  have hinner : ∀ i ∈ Finset.range ls.length,
      (∑ p ∈ (Finset.range (ls.getD i []).length).image fun j => ((i, j) : ℕ × ℕ),
        ω ((grid ls).α p)) = ((ls.getD i []).map ω).sum := by
    intro i _
    rw [Finset.sum_image (by rintro a - b - h; exact (Prod.mk.injEq _ _ _ _ ▸ h).2)]
    exact sum_range_getD ω (ls.getD i []) (Sum.inl default)
  rw [Finset.sum_congr rfl hinner, sum_range_getD (fun r => (r.map ω).sum) ls [],
    List.map_flatten, List.sum_flatten, List.map_map]
  rfl

/-- **The weight of a grid with a tail** is the weight of all the tasks occurring in it. -/
lemma weight_gridTail (ω : A ⊕ C → ℤ) (ls : List (List (A ⊕ C))) (tl : List (A ⊕ C)) :
    weight ω (gridTail ls tl) = ((ls ++ [tl]).flatten.map ω).sum := by
  rw [← weight_grid ω (ls ++ [tl])]
  rfl

end Grid

end TaskNetwork

open TaskNetwork

/-- A weight is *balanced* for a set of methods iff every method's subtask network weighs
exactly as much as the task that the method decomposes. -/
def Balanced (M : Set (Method I A C)) (ω : A ⊕ C → ℤ) : Prop :=
  ∀ m ∈ M, weight ω m.subtasks = ω (Sum.inr m.abstractTask)

variable [DecidableEq I] {M : Set (Method I A C)} {ω : A ⊕ C → ℤ}

/-- **A balanced weight is invariant under one decomposition step.** -/
lemma weight_of_decompStep (hbal : Balanced M ω) {tn₁ tn₂ : TaskNetwork I A C} {t : I}
    {m : Method I A C} (h : DecompStep M tn₁ t m tn₂) :
    weight ω tn₂ = weight ω tn₁ := by
  obtain ⟨hm, ht, hα, tn', -, hiso, hdisj, rfl⟩ := h
  rw [weight_decomposeWith ht hdisj, hα, weight_iso hiso, hbal m hm]
  ring

/-- **A balanced weight is invariant under decomposition.** -/
lemma weight_of_decomposesTo (hbal : Balanced M ω) {tn tn' : TaskNetwork I A C}
    (h : DecomposesTo M tn tn') : weight ω tn' = weight ω tn := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨t, m, hstep⟩ := hstep
      rw [weight_of_decompStep hbal hstep, ih]

/-- The weight of a primitive network is the weight of its action sequence. -/
lemma weight_of_isActionSeq {tn : TaskNetwork I A C} {l : List I} {as : List A}
    (hlin : tn.IsLinearization l) (has : tn.IsActionSeq l as) :
    weight ω tn = (as.map fun a => ω (Sum.inl a)).sum := by
  have hT : tn.T = l.toFinset := by
    ext x
    simp [← hlin.2.1 x]
  have hsum : weight ω tn = (l.map fun t => ω (tn.α t)).sum := by
    rw [weight, hT, List.sum_toFinset _ hlin.1]
  rw [hsum]
  have : (l.map fun t => ω (tn.α t)) = as.map fun a => ω (Sum.inl a) := by
    have h := has
    rw [TaskNetwork.IsActionSeq] at h
    calc (l.map fun t => ω (tn.α t)) = (l.map tn.α).map ω := by simp [List.map_map]
      _ = (as.map (Sum.inl (β := C))).map ω := by rw [h]
      _ = as.map fun a => ω (Sum.inl a) := by simp [List.map_map]
  rw [this]

/-- **The weight of a refinement.**  If the task network `tn` refines into the action sequence
`as` and the weight is balanced for the methods of the domain, then the weight of `as` is the
weight of `tn`. -/
theorem weight_of_netYield {D : Domain F A C I} (hbal : Balanced D.methods ω)
    {tn : TaskNetwork I A C} {as : List A} (h : D.NetYield tn as) :
    (as.map fun a => ω (Sum.inl a)).sum = weight ω tn := by
  obtain ⟨tn', hd, -, l, hlin, has⟩ := Domain.netYield_iff.1 h
  rw [← weight_of_isActionSeq hlin has, weight_of_decomposesTo hbal hd]

/-! ### Properties inherited by every plan

A property of actions that holds of every action occurring in a method body, and of every action
of the initial task network, holds of every action of every plan.  This is the special case of
the weight invariant where the weight counts the *violations* of the property. -/

open scoped Classical in
/-- The weight that counts the actions violating a property of actions. -/
noncomputable def violationWeight (P : A → Prop) : A ⊕ C → ℤ
  | Sum.inl a => if P a then 0 else 1
  | Sum.inr _ => 0

omit [DecidableEq I] in
open scoped Classical in
lemma weight_violationWeight_eq_zero {P : A → Prop} {tn : TaskNetwork I A C}
    (h : ∀ t ∈ tn.T, ∀ a : A, tn.α t = Sum.inl a → P a) :
    weight (violationWeight (C := C) P) tn = 0 := by
  refine Finset.sum_eq_zero fun t ht => ?_
  rcases hα : tn.α t with a | c
  · rw [violationWeight, if_pos (h t ht a hα)]
  · rfl

open scoped Classical in
lemma sum_violationWeight_nonneg (P : A → Prop) (as : List A) :
    0 ≤ (as.map fun a => violationWeight (C := C) P (Sum.inl a)).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons]
      have : 0 ≤ violationWeight (C := C) P (Sum.inl a) := by
        rw [violationWeight]; split <;> norm_num
      omega

open scoped Classical in
lemma forall_of_sum_violationWeight_eq_zero {P : A → Prop} {as : List A}
    (h : (as.map fun a => violationWeight (C := C) P (Sum.inl a)).sum = 0) :
    ∀ a ∈ as, P a := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons] at h
      have hnn := sum_violationWeight_nonneg (C := C) P as
      have ha : violationWeight (C := C) P (Sum.inl a) = 0 := by
        have : 0 ≤ violationWeight (C := C) P (Sum.inl a) := by
          rw [violationWeight]; split <;> norm_num
        omega
      have hPa : P a := by
        by_contra hcon
        rw [violationWeight, if_neg hcon] at ha
        exact one_ne_zero ha
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hPa
      · exact ih (by omega) b hb

open scoped Classical in
/-- **A property of actions that all method bodies and the initial task network satisfy holds of
every action of every plan.** -/
theorem forall_mem_of_netYield {D : Domain F A C I} {P : A → Prop}
    (hbody : ∀ m ∈ D.methods, ∀ t ∈ m.subtasks.T, ∀ a : A, m.subtasks.α t = Sum.inl a → P a)
    {tn : TaskNetwork I A C} (htn : ∀ t ∈ tn.T, ∀ a : A, tn.α t = Sum.inl a → P a)
    {as : List A} (h : D.NetYield tn as) : ∀ a ∈ as, P a := by
  have hbal : Balanced D.methods (violationWeight (C := C) P) := by
    intro m hm
    rw [weight_violationWeight_eq_zero (hbody m hm)]
    rfl
  have := weight_of_netYield hbal h
  rw [weight_violationWeight_eq_zero htn] at this
  exact forall_of_sum_violationWeight_eq_zero this

end HTN
