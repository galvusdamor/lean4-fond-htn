import HtnComplexity.Complexity.ChainDesc
import HtnComplexity.Computable.ChainTn
import HtnPlanning.Interleave.ChainPrefix
/-!
# Splitting a described chain of compound tasks into its first task and the rest

A source instance of a bounded-chain class has the chain `HTN.Syn.chainTn ws` of compound tasks
as its initial task network.  The product construction compiles it into a *single* compound task
whose name carries the whole chain, so its correctness proof has to compare a refinement of the
chain with a refinement of that one task.  The first half of that comparison is the statement of
this file: a refinement of a chain is a refinement of its first task followed by a refinement of
the rest.

* `HTN.Syn.isSeries_chainTn` — the described chain `c :: ws` is the **sequential composition** of
  the single task `c` and a copy of the chain `ws`;
* `HTN.Syn.netYield_chainTn_cons_iff` — hence its refinements are the concatenations;
* `HTN.Syn.netYield_chainTn_nil_iff` — the empty chain refines only into the empty action
  sequence.

The copy of `ws` is the description `HTN.Syn.tailTn ws`, which renames the identifier of the
`j`-th task of `chainTn ws` to that of the `j + 1`-st; it is isomorphic to `chainTn ws` by
`HTN.Syn.TnDesc.mapIds_iso`, and refinement is invariant under isomorphism
(`HTN.Domain.NetYieldN.iso`).
-/

namespace HTN

namespace Syn

open TaskNetwork

/-! ### The described chain, task by task -/

theorem mem_chainTn_ids_iff {ws : List ℕ} {x : ℕ} :
    x ∈ (chainTn ws).ids ↔ ∃ j, j < ws.length ∧ x = Nat.pair 0 j := by
  rw [chainTn_ids]
  simp [eq_comm]

theorem chainTn_ord_iff {ws : List ℕ} {x y : ℕ} :
    (chainTn ws).toTaskNetwork.ord x y ↔
      ∃ i j, i < j ∧ j < ws.length ∧ x = Nat.pair 0 i ∧ y = Nat.pair 0 j := by
  have hrow : (gridRow [ws.map fun c => ((true, c) : Bool × ℕ)] 0).length = ws.length := by
    rw [chainRow]; simp
  rw [show chainTn ws = gridDesc [ws.map fun c => ((true, c) : Bool × ℕ)] from rfl, gridDesc_ord]
  constructor
  · rintro ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact ⟨j, j', hjj, by rwa [hrow] at hj', rfl, rfl⟩
  · rintro ⟨i, j, hij, hj, rfl, rfl⟩
    exact ⟨0, i, j, by simp, hij, by rwa [hrow], rfl, rfl⟩

/-! ### The tail of a described chain -/

/-- The identifier of the task following the one named `x` in a described chain. -/
def shiftId (x : ℕ) : ℕ := Nat.pair 0 (x.unpair.2 + 1)

@[simp] theorem shiftId_pair (j : ℕ) : shiftId (Nat.pair 0 j) = Nat.pair 0 (j + 1) := by
  simp [shiftId]

/-- **The tail copy of a described chain**: the chain `ws`, with the identifier of its `j`-th
task moved to that of the `j + 1`-st. -/
def tailTn (ws : List ℕ) : TnDesc := (chainTn ws).mapIds shiftId

theorem mem_tailTn_ids_iff {ws : List ℕ} {x : ℕ} :
    x ∈ (tailTn ws).ids ↔ ∃ j, j < ws.length ∧ x = Nat.pair 0 (j + 1) := by
  rw [tailTn, TnDesc.mapIds_ids]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj, rfl⟩ := mem_chainTn_ids_iff.1 hy
    exact ⟨j, hj, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.2 ⟨Nat.pair 0 j, mem_chainTn_ids_iff.2 ⟨j, hj, rfl⟩, by simp⟩

theorem shiftId_injOn (ws : List ℕ) :
    Set.InjOn shiftId {x | x ∈ (chainTn ws).ids} := by
  intro x hx y hy hxy
  obtain ⟨i, -, rfl⟩ := mem_chainTn_ids_iff.1 hx
  obtain ⟨j, -, rfl⟩ := mem_chainTn_ids_iff.1 hy
  rw [shiftId_pair, shiftId_pair] at hxy
  obtain ⟨-, h⟩ := Nat.pair_eq_pair.1 hxy
  have : i = j := by omega
  rw [this]

theorem chainTn_ordList_mem {ws : List ℕ} {p : ℕ × ℕ} (hp : p ∈ (chainTn ws).ordList) :
    p.1 ∈ (chainTn ws).ids ∧ p.2 ∈ (chainTn ws).ids := by
  have hrow : (gridRow [ws.map fun c => ((true, c) : Bool × ℕ)] 0).length = ws.length := by
    rw [chainRow]; simp
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_cellOrd.1 hp
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  rw [hrow] at hj
  exact ⟨mem_chainTn_ids_iff.2 ⟨j, by omega, rfl⟩, mem_chainTn_ids_iff.2 ⟨j + 1, hj, rfl⟩⟩

theorem chainTn_lbl_mem {ws : List ℕ} {l : ℕ × Bool × ℕ} (hl : l ∈ (chainTn ws).lbl) :
    l.1 ∈ (chainTn ws).ids := by
  have hrow : (gridRow [ws.map fun c => ((true, c) : Bool × ℕ)] 0).length = ws.length := by
    rw [chainRow]; simp
  simp only [chainTn, gridDesc_lbl, cellLbl, List.mem_flatMap, List.mem_map,
    List.mem_range] at hl
  obtain ⟨i, hi, j, hj, rfl⟩ := hl
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  rw [hrow] at hj
  exact mem_chainTn_ids_iff.2 ⟨j, hj, rfl⟩

/-- **The tail copy is an isomorphic copy.** -/
theorem tailTn_iso (ws : List ℕ) : (chainTn ws).toTaskNetwork.Iso (tailTn ws).toTaskNetwork :=
  TnDesc.mapIds_iso (fun _ hp => chainTn_ordList_mem hp) (fun _ hl => chainTn_lbl_mem hl)
    (shiftId_injOn ws)

theorem tailTn_ord_iff {ws : List ℕ} {i j : ℕ} (hi : i < ws.length) (hj : j < ws.length) :
    (tailTn ws).toTaskNetwork.ord (Nat.pair 0 (i + 1)) (Nat.pair 0 (j + 1)) ↔
      (chainTn ws).toTaskNetwork.ord (Nat.pair 0 i) (Nat.pair 0 j) := by
  have hmi : Nat.pair 0 i ∈ (chainTn ws).ids := mem_chainTn_ids_iff.2 ⟨i, hi, rfl⟩
  have hmj : Nat.pair 0 j ∈ (chainTn ws).ids := mem_chainTn_ids_iff.2 ⟨j, hj, rfl⟩
  have hord : ∀ p ∈ (chainTn ws).ordList, p.1 ∈ (chainTn ws).ids ∧ p.2 ∈ (chainTn ws).ids :=
    fun _ hp => chainTn_ordList_mem hp
  have hinj := shiftId_injOn ws
  simp only [tailTn, TnDesc.toTaskNetwork_ord]
  rw [← shiftId_pair i, ← shiftId_pair j]
  constructor
  · rintro ⟨-, -, h1, h2⟩
    exact ⟨hmi, hmj, (TnDesc.preOrd_mapIds_iff hord hinj hmi hmj).1 h1,
      fun hc => h2 ((TnDesc.preOrd_mapIds_iff hord hinj hmj hmi).2 hc)⟩
  · rintro ⟨-, -, h1, h2⟩
    exact ⟨List.mem_map.2 ⟨_, hmi, rfl⟩, List.mem_map.2 ⟨_, hmj, rfl⟩,
      (TnDesc.preOrd_mapIds_iff hord hinj hmi hmj).2 h1,
      fun hc => h2 ((TnDesc.preOrd_mapIds_iff hord hinj hmj hmi).1 hc)⟩

theorem tailTn_label {ws : List ℕ} {j : ℕ} (hj : j < ws.length) :
    (tailTn ws).label (Nat.pair 0 (j + 1)) = Sum.inr ws[j] := by
  have hm : Nat.pair 0 j ∈ (chainTn ws).ids := mem_chainTn_ids_iff.2 ⟨j, hj, rfl⟩
  rw [tailTn, ← shiftId_pair j,
    TnDesc.label_mapIds (fun _ hl => chainTn_lbl_mem hl) (shiftId_injOn ws) hm]
  exact chainTn_label ws hj

/-! ### The sequential decomposition -/

theorem pair_zero_zero : Nat.pair 0 0 = 0 := rfl

@[simp] theorem singleTn_label (c : ℕ) : (singleTn c).label 0 = Sum.inr c := rfl

theorem mem_singleTn_ids {c x : ℕ} : x ∈ (singleTn c).ids ↔ x = 0 := by
  simp [singleTn, TnDesc.ids]

theorem mem_singleTn_T {c x : ℕ} : x ∈ (singleTn c).toTaskNetwork.T ↔ x = 0 := by
  simp [singleTn, TnDesc.ids]

theorem not_singleTn_ord {c x y : ℕ} : ¬ (singleTn c).toTaskNetwork.ord x y := by
  rintro ⟨-, -, h, -⟩
  induction h with
  | single hr => exact absurd hr (by simp [TnDesc.listRel, singleTn, TnDesc.ordList])
  | tail _ hr _ => exact absurd hr (by simp [TnDesc.listRel, singleTn, TnDesc.ordList])

/-- **A described chain is the sequential composition of its first task and the rest.** -/
theorem isSeries_chainTn (c : ℕ) (ws : List ℕ) :
    IsSeries (chainTn (c :: ws)).toTaskNetwork (singleTn c).toTaskNetwork
      (tailTn ws).toTaskNetwork := by
  have hne : ∀ j : ℕ, Nat.pair 0 (j + 1) ≠ 0 := by
    intro j hcon
    rw [← pair_zero_zero] at hcon
    exact absurd (Nat.pair_eq_pair.1 hcon).2 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_singleTn_T] at hx
    subst hx
    obtain ⟨j, -, hj⟩ := mem_tailTn_ids_iff.1 (by simpa using hx')
    exact hne j hj.symm
  · intro x
    simp only [TnDesc.toTaskNetwork_T, List.mem_toFinset, mem_chainTn_ids_iff,
      mem_singleTn_ids, mem_tailTn_ids_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      match j with
      | 0 => exact Or.inl (by simpa using pair_zero_zero)
      | (j + 1) => exact Or.inr ⟨j, by simpa using hj, rfl⟩
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact ⟨0, by simp, by rw [h, pair_zero_zero]⟩
      · exact ⟨j + 1, by simpa using hj, rfl⟩
  · intro x hx
    have hx0 : x = 0 := mem_singleTn_T.1 hx
    subst hx0
    have h1 : (chainTn (c :: ws)).label (Nat.pair 0 0) = Sum.inr (c :: ws)[0] :=
      chainTn_label (c :: ws) (by simp)
    rw [pair_zero_zero] at h1
    show (chainTn (c :: ws)).label 0 = (singleTn c).label 0
    rw [h1]
    simp
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_tailTn_ids_iff.1 (by simpa using hx)
    have hlt : j + 1 < (c :: ws).length := by simpa using hj
    have h1 : (chainTn (c :: ws)).label (Nat.pair 0 (j + 1)) = Sum.inr ws[j] := by
      rw [chainTn_label (c :: ws) hlt]
      simp
    show (chainTn (c :: ws)).label (Nat.pair 0 (j + 1)) =
      (tailTn ws).label (Nat.pair 0 (j + 1))
    rw [h1, tailTn_label hj]
  · intro a b
    rw [chainTn_ord_iff]
    constructor
    · rintro ⟨i, j, hij, hj, rfl, rfl⟩
      match i, j with
      | 0, 0 => omega
      | 0, (j + 1) =>
          refine Or.inr (Or.inr ⟨by rw [pair_zero_zero]; exact mem_singleTn_T.2 rfl, ?_⟩)
          simpa using mem_tailTn_ids_iff.2 ⟨j, by simpa using hj, rfl⟩
      | (i + 1), 0 => omega
      | (i + 1), (j + 1) =>
          have hj' : j < ws.length := by simpa using hj
          have hi' : i < ws.length := by omega
          refine Or.inr (Or.inl ?_)
          rw [tailTn_ord_iff hi' hj']
          exact chainTn_ord_iff.2 ⟨i, j, by omega, hj', rfl, rfl⟩
    · rintro (h | h | ⟨ha, hb⟩)
      · exact absurd h not_singleTn_ord
      · obtain ⟨i, hi, rfl⟩ := mem_tailTn_ids_iff.1
          (by simpa using (tailTn ws).toTaskNetwork_wf.mem_left h)
        obtain ⟨j, hj, rfl⟩ := mem_tailTn_ids_iff.1
          (by simpa using (tailTn ws).toTaskNetwork_wf.mem_right h)
        rw [tailTn_ord_iff hi hj, chainTn_ord_iff] at h
        obtain ⟨i', j', hij, hj', hi'e, hj'e⟩ := h
        obtain ⟨-, rfl⟩ := Nat.pair_eq_pair.1 hi'e.symm
        obtain ⟨-, rfl⟩ := Nat.pair_eq_pair.1 hj'e.symm
        exact ⟨i' + 1, j' + 1, by omega, by simpa using hj', rfl, rfl⟩
      · rw [mem_singleTn_T] at ha
        subst ha
        obtain ⟨j, hj, rfl⟩ := mem_tailTn_ids_iff.1 (by simpa using hb)
        exact ⟨0, j + 1, by omega, by simpa using hj, pair_zero_zero.symm, rfl⟩

/-! ### Refinements of a described chain -/

variable {D : Domain ℕ ℕ ℕ ℕ}

/-- **The refinements of a described chain split at its first task.** -/
theorem netYield_chainTn_cons_iff {c : ℕ} {ws : List ℕ} {as : List ℕ} :
    D.NetYield (chainTn (c :: ws)).toTaskNetwork as ↔
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ D.NetYield (singleTn c).toTaskNetwork as₁ ∧
        D.NetYield (chainTn ws).toTaskNetwork as₂ := by
  constructor
  · rintro ⟨n, hy⟩
    obtain ⟨n₁, n₂, as₁, as₂, -, rfl, hy₁, hy₂⟩ :=
      (Domain.netYieldN_isSeries_iff (D := D) (isSeries_chainTn c ws)
        (singleTn c).toTaskNetwork_wf (tailTn ws).toTaskNetwork_wf).1 hy
    exact ⟨as₁, as₂, rfl, ⟨n₁, hy₁⟩,
      ⟨n₂, hy₂.iso (tailTn ws).toTaskNetwork_wf (chainTn ws).toTaskNetwork_wf
        (tailTn_iso ws).symm⟩⟩
  · rintro ⟨as₁, as₂, rfl, ⟨n₁, hy₁⟩, ⟨n₂, hy₂⟩⟩
    exact ⟨n₁ + n₂, (Domain.netYieldN_isSeries_iff (D := D) (isSeries_chainTn c ws)
      (singleTn c).toTaskNetwork_wf (tailTn ws).toTaskNetwork_wf).2
      ⟨n₁, n₂, as₁, as₂, rfl, rfl, hy₁,
        hy₂.iso (chainTn ws).toTaskNetwork_wf (tailTn ws).toTaskNetwork_wf (tailTn_iso ws)⟩⟩

theorem chainTn_nil_T : (chainTn []).toTaskNetwork.T = ∅ := rfl

/-- A network without tasks does not decompose. -/
theorem eq_of_decomposesTo_empty {M : Set (Method ℕ ℕ ℕ)} {tn sol : TaskNetwork ℕ ℕ ℕ}
    (h : DecomposesTo M tn sol) (hT : tn.T = ∅) : sol = tn := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨u, hstep, -⟩
  · rfl
  · obtain ⟨t, m, -, ht, -⟩ := hstep
    rw [hT] at ht
    simp at ht

/-- **The empty chain refines only into the empty action sequence.** -/
theorem netYield_chainTn_nil_iff {as : List ℕ} :
    D.NetYield (chainTn []).toTaskNetwork as ↔ as = [] := by
  constructor
  · rintro ⟨n, sol, hsteps, -, l, hlin, has⟩
    have hsol : sol = (chainTn []).toTaskNetwork :=
      eq_of_decomposesTo_empty hsteps.decomposesTo chainTn_nil_T
    subst hsol
    have hl : l = [] := by
      refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
      have := (hlin.2.1 x).1 hx
      rw [chainTn_nil_T] at this
      simp at this
    subst hl
    simpa using has.symm
  · rintro rfl
    refine ⟨0, (chainTn []).toTaskNetwork, StepsN.refl _, ?_, [],
      ⟨List.nodup_nil, ?_, List.Pairwise.nil⟩, rfl⟩
    · intro x hx
      rw [chainTn_nil_T] at hx
      exact absurd hx (by simp)
    · intro t
      rw [chainTn_nil_T]
      simp

end Syn

end HTN
