import HtnComplexity.Computable.ChainSplit
import HtnComplexity.Computable.NetTn
import HtnPlanning.Interleave.ParYield
import HtnPlanning.Interleave.NetYieldSeq
/-!
# Splitting an unordered described network into its first task and the rest

`HtnComplexity/Computable/ChainSplit.lean` splits a described **chain** as a sequential
composition.  A source instance whose initial task network is a set of *unordered* compound
tasks needs the other composition: the described network `HTN.Syn.netTn ws []` is the
**parallel** composition of its first task and a copy of the rest.

* `HTN.Syn.isPar_netTn` — the decomposition itself;
* `HTN.Syn.netYield_netTn_cons_iff` — hence its refinements are the interleavings;
* `HTN.Syn.netYield_netTn_nil_iff` — the empty network refines only into the empty action
  sequence;
* `HTN.Syn.netYield_netTn_iff_interleaveList` — the refinements of `netTn ws []` are exactly the
  interleavings of refinements of its tasks.

The copy of the rest is `HTN.Syn.parTailTn ws`, the network `netTn ws []` with every identifier
increased by one; it is isomorphic to `netTn ws []` by `HTN.Syn.TnDesc.mapIds_iso`, and
refinement is invariant under isomorphism.
-/

namespace HTN

namespace Syn

open TaskNetwork

/-! ### The described unordered network, task by task -/

@[simp] theorem mem_netTn_ids_iff {ws : List ℕ} {ord : List (ℕ × ℕ)} {x : ℕ} :
    x ∈ (netTn ws ord).ids ↔ x < ws.length := by
  rw [netTn_ids]
  simp

theorem netTn_label {ws : List ℕ} {ord : List (ℕ × ℕ)} {j : ℕ} (hj : j < ws.length) :
    (netTn ws ord).label j = Sum.inr ws[j] := by
  have hmem : j ∈ List.range ws.length := by simpa using hj
  have hlk := lookup_map_self (fun i => ((true, ws.getD i 0) : Bool × ℕ)) hmem
  rw [TnDesc.label, netTn_lbl, hlk]
  show Sum.inr (ws.getD j 0) = Sum.inr ws[j]
  rw [List.getD_eq_getElem _ _ hj]

/-- An unordered described network orders nothing. -/
theorem not_netTn_ord {ws : List ℕ} {x y : ℕ} : ¬ (netTn ws []).toTaskNetwork.ord x y := by
  rintro ⟨-, -, h, -⟩
  induction h with
  | single hr => exact absurd hr (by simp [TnDesc.listRel, TnDesc.ordList, netTn])
  | tail _ hr _ => exact absurd hr (by simp [TnDesc.listRel, TnDesc.ordList, netTn])

theorem netTn_ordList_mem {ws : List ℕ} {p : ℕ × ℕ} (hp : p ∈ (netTn ws []).ordList) :
    p.1 ∈ (netTn ws []).ids ∧ p.2 ∈ (netTn ws []).ids := by
  rw [netTn_ordList] at hp
  exact absurd hp (by simp)

theorem netTn_lbl_mem {ws : List ℕ} {ord : List (ℕ × ℕ)} {l : ℕ × Bool × ℕ}
    (hl : l ∈ (netTn ws ord).lbl) : l.1 ∈ (netTn ws ord).ids := by
  rw [netTn_lbl] at hl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
  simpa using hi

/-! ### The shifted copy of the rest -/

/-- **The tail copy of an unordered described network**: the network `ws`, with every identifier
increased by one. -/
def parTailTn (ws : List ℕ) : TnDesc := (netTn ws []).mapIds (· + 1)

theorem mem_parTailTn_ids_iff {ws : List ℕ} {x : ℕ} :
    x ∈ (parTailTn ws).ids ↔ ∃ j, j < ws.length ∧ x = j + 1 := by
  rw [parTailTn, TnDesc.mapIds_ids]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨y, mem_netTn_ids_iff.1 hy, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.2 ⟨j, mem_netTn_ids_iff.2 hj, rfl⟩

theorem succ_injOn (ws : List ℕ) :
    Set.InjOn (fun x => x + 1) {x | x ∈ (netTn ws []).ids} := by
  intro x _ y _ hxy
  simpa using hxy

/-- **The tail copy is an isomorphic copy.** -/
theorem parTailTn_iso (ws : List ℕ) :
    (netTn ws []).toTaskNetwork.Iso (parTailTn ws).toTaskNetwork :=
  TnDesc.mapIds_iso (fun _ hp => netTn_ordList_mem hp) (fun _ hl => netTn_lbl_mem hl)
    (succ_injOn ws)

theorem parTailTn_label {ws : List ℕ} {j : ℕ} (hj : j < ws.length) :
    (parTailTn ws).label (j + 1) = Sum.inr ws[j] := by
  have hm : j ∈ (netTn ws []).ids := mem_netTn_ids_iff.2 hj
  have := TnDesc.label_mapIds (f := fun x => x + 1) (t := netTn ws [])
    (fun _ hl => netTn_lbl_mem hl) (succ_injOn ws) hm
  rw [parTailTn, this]
  exact netTn_label hj

/-- The tail copy orders nothing either. -/
theorem not_parTailTn_ord {ws : List ℕ} {x y : ℕ} : ¬ (parTailTn ws).toTaskNetwork.ord x y := by
  rintro ⟨-, -, h, -⟩
  have hnil : (parTailTn ws).ordList = [] := by
    rw [parTailTn, TnDesc.mapIds_ordList, netTn_ordList]
    rfl
  induction h with
  | single hr => exact absurd hr (by simp [TnDesc.listRel, hnil])
  | tail _ hr _ => exact absurd hr (by simp [TnDesc.listRel, hnil])

/-! ### The parallel decomposition -/

/-- **An unordered described network is the parallel composition of its first task and the
rest.** -/
theorem isPar_netTn (c : ℕ) (ws : List ℕ) :
    IsPar (netTn (c :: ws) []).toTaskNetwork (singleTn c).toTaskNetwork
      (parTailTn ws).toTaskNetwork := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_singleTn_T] at hx
    subst hx
    obtain ⟨j, -, hj⟩ := mem_parTailTn_ids_iff.1 (by simpa using hx')
    omega
  · intro x
    simp only [TnDesc.toTaskNetwork_T, List.mem_toFinset, mem_netTn_ids_iff,
      mem_singleTn_ids, mem_parTailTn_ids_iff]
    constructor
    · intro hx
      match x with
      | 0 => exact Or.inl rfl
      | (j + 1) => exact Or.inr ⟨j, by simpa using hx, rfl⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · simp
      · simpa using hj
  · intro x hx
    have hx0 : x = 0 := mem_singleTn_T.1 hx
    subst hx0
    show (netTn (c :: ws) []).label 0 = (singleTn c).label 0
    rw [netTn_label (by simp), singleTn_label]
    rfl
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_parTailTn_ids_iff.1 (by simpa using hx)
    have hlt : j + 1 < (c :: ws).length := by simpa using hj
    show (netTn (c :: ws) []).label (j + 1) = (parTailTn ws).label (j + 1)
    rw [netTn_label hlt, parTailTn_label hj]
    simp
  · intro a b
    constructor
    · intro h
      exact absurd h not_netTn_ord
    · rintro (h | h)
      · exact absurd h not_singleTn_ord
      · exact absurd h not_parTailTn_ord

/-! ### Refinements of an unordered described network -/

variable {D : Domain ℕ ℕ ℕ ℕ}

/-- **The refinements of an unordered described network split at its first task.** -/
theorem netYield_netTn_cons_iff {c : ℕ} {ws : List ℕ} {as : List ℕ} :
    D.NetYield (netTn (c :: ws) []).toTaskNetwork as ↔
      ∃ as₁ as₂, Interleave as₁ as₂ as ∧ D.NetYield (singleTn c).toTaskNetwork as₁ ∧
        D.NetYield (netTn ws []).toTaskNetwork as₂ := by
  constructor
  · rintro ⟨n, hy⟩
    obtain ⟨n₁, n₂, as₁, as₂, -, hint, hy₁, hy₂⟩ :=
      (Domain.netYieldN_isPar_iff (D := D) (isPar_netTn c ws)
        (singleTn c).toTaskNetwork_wf (parTailTn ws).toTaskNetwork_wf).1 hy
    exact ⟨as₁, as₂, hint, ⟨n₁, hy₁⟩,
      ⟨n₂, hy₂.iso (parTailTn ws).toTaskNetwork_wf (netTn ws []).toTaskNetwork_wf
        (parTailTn_iso ws).symm⟩⟩
  · rintro ⟨as₁, as₂, hint, ⟨n₁, hy₁⟩, ⟨n₂, hy₂⟩⟩
    exact ⟨n₁ + n₂, (Domain.netYieldN_isPar_iff (D := D) (isPar_netTn c ws)
      (singleTn c).toTaskNetwork_wf (parTailTn ws).toTaskNetwork_wf).2
      ⟨n₁, n₂, as₁, as₂, rfl, hint, hy₁,
        hy₂.iso (netTn ws []).toTaskNetwork_wf (parTailTn ws).toTaskNetwork_wf
          (parTailTn_iso ws)⟩⟩

theorem netTn_nil_T : (netTn [] []).toTaskNetwork.T = ∅ := rfl

/-- **The empty network refines only into the empty action sequence.** -/
theorem netYield_netTn_nil_iff {as : List ℕ} :
    D.NetYield (netTn [] []).toTaskNetwork as ↔ as = [] := by
  constructor
  · rintro ⟨n, sol, hsteps, -, l, hlin, has⟩
    have hsol : sol = (netTn [] []).toTaskNetwork :=
      eq_of_decomposesTo_empty hsteps.decomposesTo netTn_nil_T
    subst hsol
    have hl : l = [] := by
      refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
      have := (hlin.2.1 x).1 hx
      rw [netTn_nil_T] at this
      simp at this
    subst hl
    simpa using has.symm
  · rintro rfl
    refine ⟨0, (netTn [] []).toTaskNetwork, StepsN.refl _, ?_, [],
      ⟨List.nodup_nil, ?_, List.Pairwise.nil⟩, rfl⟩
    · intro x hx
      rw [netTn_nil_T] at hx
      exact absurd hx (by simp)
    · intro t
      rw [netTn_nil_T]
      simp

/-- **The refinements of an unordered described network are the interleavings of refinements of
its tasks.** -/
theorem netYield_netTn_iff_interleaveList :
    ∀ {ws : List ℕ} {as : List ℕ},
      D.NetYield (netTn ws []).toTaskNetwork as ↔
        ∃ ass, InterleaveList ass as ∧
          List.Forall₂ (fun c w => D.NetYield (singleTn c).toTaskNetwork w) ws ass
  | [], as => by
      rw [netYield_netTn_nil_iff]
      constructor
      · rintro rfl
        exact ⟨[], InterleaveList.nil, List.Forall₂.nil⟩
      · rintro ⟨ass, hint, hall⟩
        cases hall
        cases hint
        rfl
  | c :: ws, as => by
      rw [netYield_netTn_cons_iff]
      constructor
      · rintro ⟨as₁, as₂, hint, h₁, h₂⟩
        obtain ⟨ass, hintl, hall⟩ := netYield_netTn_iff_interleaveList.1 h₂
        exact ⟨as₁ :: ass, InterleaveList.cons hintl hint, List.Forall₂.cons h₁ hall⟩
      · rintro ⟨ass, hint, hall⟩
        rcases hall with _ | ⟨h₁, hall'⟩
        cases hint with
        | cons hrest hint' =>
            exact ⟨_, _, hint', h₁,
              netYield_netTn_iff_interleaveList.2 ⟨_, hrest, hall'⟩⟩

end Syn

end HTN
