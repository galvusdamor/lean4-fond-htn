import HtnComplexity.HDDecide.Complete
import HtnPlanning.Core.Unroll
/-!
# The isolation statement: one hole by the search on pieces, the others unrolled first

`htn-complexity/HD2_LU.md` (§6.6) observes that in a two-hole-digging problem one hole can always
be handled by Dekker and Behnke's search on pieces, which decomposes a compound task only when it
is isolated, provided the other hole may be decomposed freely.  Since decompositions do not touch
the states, the other hole may as well be decomposed completely *before* the search starts.  This
file proves that version, for any number of holes:

* `HTN.HD.descOf` — a description of a task network over `ℕ`, isomorphic to it by the identity
  (`HTN.HD.descOf_iso`);
* **`HTN.HD.isolation`** — if every method has at most one compound task and the problem is
  solvable, then for every task `x₀` of the initial network there is a network `tn₁`, reachable
  from the initial one, in which `x₀` is untouched and is the only compound task, such that the
  problem started from (a description of) `tn₁` is one-hole-digging and solved by the search on
  pieces.

The statement carries little information beyond Lemma 6: all the structure of the unrolled holes
ends up in one primitive network of unbounded size.
-/

namespace HTN

namespace HD

open Syn

/-! ### A description of a task network -/

open Classical in
/-- A description of a task network over `ℕ`: its tasks in increasing order, its ordering pairs,
and the labels of its tasks. -/
noncomputable def descOf (tn : TaskNetwork ℕ ℕ ℕ) : TnDesc :=
  (tn.T.sort (· ≤ ·), ((tn.T ×ˢ tn.T).filter fun p => tn.ord p.1 p.2).toList,
    (tn.T.sort (· ≤ ·)).map fun i =>
      match tn.α i with
      | Sum.inl a => (i, false, a)
      | Sum.inr c => (i, true, c))

theorem mem_ids_descOf {tn : TaskNetwork ℕ ℕ ℕ} {x : ℕ} : x ∈ (descOf tn).ids ↔ x ∈ tn.T :=
  Finset.mem_sort _

theorem descOf_T (tn : TaskNetwork ℕ ℕ ℕ) : (descOf tn).toTaskNetwork.T = tn.T := by
  ext x
  simp only [TnDesc.toTaskNetwork, List.mem_toFinset, mem_ids_descOf]

theorem listRel_descOf {tn : TaskNetwork ℕ ℕ ℕ} {a b : ℕ} :
    (descOf tn).listRel a b ↔ a ∈ tn.T ∧ b ∈ tn.T ∧ tn.ord a b := by
  classical
  simp only [TnDesc.listRel, TnDesc.ordList, descOf, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_product, and_assoc]

theorem preOrd_descOf {tn : TaskNetwork ℕ ℕ ℕ} (hwf : tn.WF) {a b : ℕ} :
    (descOf tn).preOrd a b ↔ tn.ord a b := by
  constructor
  · intro h
    induction h with
    | single h => exact (listRel_descOf.1 h).2.2
    | tail _ h ih => exact hwf.trans ih (listRel_descOf.1 h).2.2
  · intro h
    exact Relation.TransGen.single (listRel_descOf.2 ⟨hwf.mem_left h, hwf.mem_right h, h⟩)

/-- Looking up an identifier in a list of entries indexed by a list containing it. -/
theorem lookup_map_mem {β : Type} (g : ℕ → β) :
    ∀ {l : List ℕ} {x : ℕ}, x ∈ l → (l.map fun i => (i, g i)).lookup x = some (g x)
  | [], _, h => absurd h (List.not_mem_nil)
  | i :: l, x, h => by
    by_cases hx : x = i
    · subst hx
      simp
    · have hm : x ∈ l := (List.mem_cons.1 h).resolve_left hx
      have hb : (x == i) = false := beq_eq_false_iff_ne.2 hx
      simp only [List.map_cons, List.lookup, hb]
      exact lookup_map_mem g hm

theorem label_descOf {tn : TaskNetwork ℕ ℕ ℕ} {x : ℕ} (hx : x ∈ tn.T) :
    (descOf tn).label x = tn.α x := by
  have key := lookup_map_mem
    (fun i => match tn.α i with | Sum.inl a => (false, a) | Sum.inr c => (true, c))
    (mem_ids_descOf.2 hx)
  have hl : (descOf tn).lbl = ((descOf tn).ids.map fun i =>
      (i, match tn.α i with | Sum.inl a => (false, a) | Sum.inr c => (true, c))) := by
    simp only [TnDesc.lbl, TnDesc.ids, descOf, List.map_inj_left]
    intro i _
    cases tn.α i <;> rfl
  unfold TnDesc.label
  rw [hl, key]
  rcases h : tn.α x with a | c <;> simp [h]

/-- **The description denotes the network**, up to the identity isomorphism. -/
theorem descOf_iso {tn : TaskNetwork ℕ ℕ ℕ} (hwf : tn.WF) : (descOf tn).toTaskNetwork.Iso tn := by
  refine ⟨id, ?_, ?_, ?_⟩
  · rw [descOf_T]
    exact Set.bijOn_id _
  · intro a ha b hb
    rw [descOf_T] at ha hb
    change (descOf tn).ordOf a b ↔ tn.ord a b
    unfold TnDesc.ordOf
    rw [preOrd_descOf hwf, preOrd_descOf hwf, mem_ids_descOf, mem_ids_descOf]
    constructor
    · rintro ⟨-, -, h, -⟩
      exact h
    · intro h
      exact ⟨ha, hb, h, fun h' => hwf.irrefl a (hwf.trans h h')⟩
  · intro a ha
    rw [descOf_T] at ha
    exact label_descOf ha

/-! ### The isolation statement -/

/-- **The isolation statement.**  Let every method have at most one compound task, and let the
described problem be solvable.  For every task `x₀` of the initial network there are a network
`tn₁` and an instance description `q₁` with the same initial state and goal such that

* `tn₁` is reachable from the initial network, `x₀` is still in it with its label, and `q₁`
  describes `tn₁` (up to the identity isomorphism);
* `q₁` is one-hole-digging — `x₀` is its only compound task — and **the search on pieces solves
  it**, i.e. the hole of `x₀` is handled by decompositions of isolated tasks only.

For a two-hole-digging problem with holes `x₀` and `y₀` this says: unroll the hole of `y₀`
completely, then the hole of `x₀` needs only isolated decompositions. -/
theorem isolation {d : DomDesc} {q : InstDesc} (hd : d.MethodsHD1) (hsol : Solvable d q)
    {x₀ : ℕ} (hx₀ : x₀ ∈ q.tnI.toTaskNetwork.T) :
    ∃ (q₁ : InstDesc) (tn₁ : TaskNetwork ℕ ℕ ℕ),
      q₁.initList = q.initList ∧ q₁.goalList = q.goalList ∧
      (problem d q).Reachable tn₁ ∧ q₁.tnI.toTaskNetwork.Iso tn₁ ∧
      x₀ ∈ tn₁.T ∧ tn₁.α x₀ = q.tnI.toTaskNetwork.α x₀ ∧
      q₁.IsHD1 ∧ PiecesSolvable d q₁ := by
  obtain ⟨tn₁, hreach, hwf₁, hx, hα, hall, hsol₁⟩ :=
    (problem d q).exists_unroll_except (TnDesc.toTaskNetwork_wf _) hsol hx₀
  let q₁ : InstDesc := (q.initList, q.goalList, descOf tn₁)
  have hiso : q₁.tnI.toTaskNetwork.Iso tn₁ := descOf_iso hwf₁
  have hq₁ : q₁.IsHD1 := by
    intro a ha b hb ⟨c, hc⟩ ⟨c', hc'⟩
    change a ∈ (descOf tn₁).toTaskNetwork.T at ha
    change b ∈ (descOf tn₁).toTaskNetwork.T at hb
    rw [descOf_T] at ha hb
    change (descOf tn₁).label a = _ at hc
    change (descOf tn₁).label b = _ at hc'
    rw [label_descOf ha] at hc
    rw [label_descOf hb] at hc'
    exact (hall a ha ⟨c, hc⟩).trans (hall b hb ⟨c', hc'⟩).symm
  have hsolv : Solvable d q₁ :=
    (problem d q).solvable_congr_tnI hwf₁ (TnDesc.toTaskNetwork_wf _) hiso.symm hsol₁
  exact ⟨q₁, tn₁, rfl, rfl, hreach, hiso, hx, hα, hq₁, piecesSolvable_of_solvable hd hq₁ hsolv⟩

end HD

end HTN
