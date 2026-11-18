import HtnPlanning.Interleave.SegChain
import HtnComplexity.Computable.AcFreeRow
/-!
# Chains of segments: the generic calculus for an unrestricted initial task network

The compilation of `(TO-HTN, HTN-AC)` for an **unrestricted** (totally ordered) initial task
network (`HtnCompilability/Computable/ChainCorrect.lean`) emits one *block* of target tasks per
task of the source's initial task network and lays the blocks out as a single row.  This file
provides the three generic tools the correctness proof needs:

* `HTN.relChain_append`, `HTN.relChain_flatMap` — composing state relations along concatenated
  lists, so that the relation of a row made of blocks is the composite of the block relations;
* `HTN.relChain_sim` — a **one-directional** simulation along a chain.  Unlike
  `HTN.exists_relChain_congr` it lets the two directions of a correctness proof use two different
  representation relations, which is what an under-approximating compilation needs: the
  completeness direction keeps the compiled state *exact*, the soundness direction only keeps it
  *below* the source state;
* `HTN.Syn.Chain.netReach_isSeqNet` — the state transformer of a sequence network (in an
  arbitrary, not necessarily totally ordered, domain whose identifiers are natural numbers) is the
  composite of the state transformers of its one-task networks.
-/

namespace HTN

/-! ### Composing along concatenations -/

theorem relChain_append {F C : Type*} {R : C → Set F → Set F → Prop} (xs ys : List C)
    {s s'' : Set F} :
    RelChain R (xs ++ ys) s s'' ↔ ∃ s', RelChain R xs s s' ∧ RelChain R ys s' s'' := by
  induction xs generalizing s with
  | nil =>
    simp only [List.nil_append, relChain_nil]
    exact ⟨fun h => ⟨s, rfl, h⟩, fun ⟨s', hs', h⟩ => hs' ▸ h⟩
  | cons x xs ih =>
    simp only [List.cons_append, relChain_cons]
    constructor
    · rintro ⟨s₁, h₁, h₂⟩
      obtain ⟨s', h₃, h₄⟩ := ih.1 h₂
      exact ⟨s', ⟨s₁, h₁, h₃⟩, h₄⟩
    · rintro ⟨s', ⟨s₁, h₁, h₃⟩, h₄⟩
      exact ⟨s₁, h₁, ih.2 ⟨s', h₃, h₄⟩⟩

theorem relChain_flatMap {F C C' : Type*} (R : C' → Set F → Set F → Prop) (g : C → List C')
    (xs : List C) {s s' : Set F} :
    RelChain R (xs.flatMap g) s s' ↔ RelChain (fun x => RelChain R (g x)) xs s s' := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, relChain_append, relChain_cons]
    exact exists_congr fun s₁ => and_congr_right fun _ => ih

/-- **A one-directional simulation along a chain.** -/
theorem relChain_sim {F G C : Type*} {Rs : C → Set F → Set F → Prop}
    {Rt : C → Set G → Set G → Prop} {Rep : Set F → Set G → Prop} (cs : List C)
    (h : ∀ c ∈ cs, ∀ s t s', Rep s t → Rs c s s' → ∃ t', Rt c t t' ∧ Rep s' t')
    {s : Set F} {t : Set G} {s' : Set F} (hst : Rep s t) (hs : RelChain Rs cs s s') :
    ∃ t', RelChain Rt cs t t' ∧ Rep s' t' := by
  induction cs generalizing s t with
  | nil =>
    rw [relChain_nil] at hs
    subst hs
    exact ⟨t, rfl, hst⟩
  | cons c cs ih =>
    obtain ⟨s₁, h₁, h₂⟩ := hs
    obtain ⟨t₁, ht₁, hrep₁⟩ := h c List.mem_cons_self s t s₁ hst h₁
    obtain ⟨t', ht', hrep'⟩ :=
      ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) hrep₁ h₂
    exact ⟨t', ⟨t₁, ht₁, ht'⟩, hrep'⟩

namespace Syn

namespace Chain

open AcFree TaskNetwork

/-! ### Sequence networks over natural-number identifiers -/

/-- The network `tn` restricted to the identifiers of `l`. -/
def tailNet (tn : TaskNetwork ℕ ℕ ℕ) (l : List ℕ) : TaskNetwork ℕ ℕ ℕ where
  T := l.toFinset
  ord := fun a b => tn.ord a b ∧ a ∈ l ∧ b ∈ l
  α := tn.α

lemma idxOf_cons_of_ne {i a : ℕ} {l : List ℕ} (h : a ≠ i) :
    (i :: l).idxOf a = l.idxOf a + 1 := by
  rw [List.idxOf_cons_ne _ (Ne.symm h)]

/-- **Peeling the first task off a sequence network.** -/
theorem isSeries_of_isSeqNet_cons {tn : TaskNetwork ℕ ℕ ℕ} {i : ℕ} {l : List ℕ} {x : ℕ ⊕ ℕ}
    {xs : List (ℕ ⊕ ℕ)} (h : tn.IsSeqNet (i :: l) (x :: xs)) :
    tn.IsSeries (netSingle i x) (tailNet tn l) ∧ (tailNet tn l).IsSeqNet l xs := by
  have hnd := h.nodup
  have hil : i ∉ l := (List.nodup_cons.1 hnd).1
  have hndl : l.Nodup := (List.nodup_cons.1 hnd).2
  have hlab : tn.α i = x ∧ l.map tn.α = xs := by
    have := h.labels
    simp only [List.map_cons, List.cons.injEq] at this
    exact this
  have hne : ∀ a ∈ l, a ≠ i := fun a ha hai => hil (hai ▸ ha)
  -- the ordering of the tail
  have hordT : ∀ a b, a ∈ l → b ∈ l → (tn.ord a b ↔ l.idxOf a < l.idxOf b) := by
    intro a b ha hb
    rw [h.ord, idxOf_cons_of_ne (hne a ha), idxOf_cons_of_ne (hne b hb)]
    simp only [List.mem_cons, ha, hb, or_true, true_and]
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨hndl, ?_, hlab.2, ?_⟩⟩
  · simp only [netSingle_T, tailNet, Finset.disjoint_singleton_left, List.mem_toFinset]
    exact hil
  · intro t
    rw [h.memT]
    simp [netSingle, tailNet]
  · intro t ht
    simp only [netSingle_T, Finset.mem_singleton] at ht
    subst ht
    simpa using hlab.1
  · intro t _
    rfl
  · intro a b
    simp only [netSingle_ord, netSingle_T, Finset.mem_singleton, tailNet, List.mem_toFinset,
      false_or]
    constructor
    · intro hab
      have hab' := (h.ord a b).1 hab
      obtain ⟨ha, hb, hlt⟩ := hab'
      by_cases hai : a = i
      · subst hai
        refine Or.inr ⟨rfl, ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact absurd hlt (lt_irrefl _)
        · exact hb'
      · have ha' : a ∈ l := by
          rcases List.mem_cons.1 ha with rfl | ha'
          · exact absurd rfl hai
          · exact ha'
        have hb' : b ∈ l := by
          rcases List.mem_cons.1 hb with rfl | hb'
          · rw [List.idxOf_cons_self] at hlt
            exact absurd hlt (Nat.not_lt_zero _)
          · exact hb'
        exact Or.inl ⟨hab, ha', hb'⟩
    · rintro (⟨hab, -, -⟩ | ⟨rfl, hb⟩)
      · exact hab
      · rw [h.ord]
        refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ hb, ?_⟩
        rw [List.idxOf_cons_self, idxOf_cons_of_ne (hne b hb)]
        omega
  · intro t
    simp [tailNet]
  · intro a b
    simp only [tailNet]
    constructor
    · rintro ⟨hab, ha, hb⟩
      exact ⟨ha, hb, (hordT a b ha hb).1 hab⟩
    · rintro ⟨ha, hb, hlt⟩
      exact ⟨(hordT a b ha hb).2 hlt, ha, hb⟩

/-- A network without tasks refines only into the empty plan. -/
lemma netYieldN_empty {D : Domain ℕ ℕ ℕ ℕ} {n : ℕ} {tn : TaskNetwork ℕ ℕ ℕ} {as : List ℕ}
    (hT : tn.T = ∅) : D.NetYieldN n tn as ↔ n = 0 ∧ as = [] := by
  constructor
  · rintro ⟨sol, hsteps, hprim, l, hlin, has⟩
    have hn : n = 0 := by
      by_contra hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨tn₂, ⟨t, m, -, ht, -⟩, -⟩ := hsteps.exists_head
      rw [hT] at ht
      simp at ht
    subst hn
    cases hsteps with
    | refl =>
        have hl : l = [] := by
          cases l with
          | nil => rfl
          | cons x l =>
              have := (hlin.2.1 x).1 (by simp)
              rw [hT] at this
              simp at this
        subst hl
        have : ([] : List (ℕ ⊕ ℕ)) = as.map Sum.inl := has
        exact ⟨rfl, by simpa using this.symm⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨tn, StepsN.refl _, ?_, [], ⟨by simp, ?_, by simp⟩, rfl⟩
    · intro x hx
      rw [hT] at hx
      simp at hx
    · intro x
      rw [hT]
      simp

/-- A network without tasks does not change the state. -/
lemma netReach_empty {D : Domain ℕ ℕ ℕ ℕ} {tn : TaskNetwork ℕ ℕ ℕ} (hT : tn.T = ∅)
    {s s' : Set ℕ} : D.NetReach tn s s' ↔ s' = s := by
  constructor
  · rintro ⟨as, ⟨n, hy⟩, -, rfl⟩
    obtain ⟨-, rfl⟩ := (netYieldN_empty hT).1 hy
    rfl
  · rintro rfl
    exact ⟨[], ⟨0, (netYieldN_empty hT).2 ⟨rfl, rfl⟩⟩, by simp [ActionModel.SeqApplicable],
      rfl⟩

/-- The identifier of a one-task network does not matter. -/
lemma netReach_netSingle_congr {D : Domain ℕ ℕ ℕ ℕ} (i j : ℕ) (x : ℕ ⊕ ℕ) {s s' : Set ℕ} :
    D.NetReach (netSingle i x) s s' ↔ D.NetReach (netSingle j x) s s' := by
  have hiso : ∀ i j : ℕ, (netSingle i x).Iso (netSingle j x) := by
    intro i j
    refine ⟨fun _ => j, ?_, ?_, ?_⟩
    · refine ⟨fun t _ => by simp [netSingle], fun a ha b hb _ => ?_, fun t ht => ?_⟩
      · simp only [netSingle_T, Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
        rw [ha, hb]
      · simp only [netSingle_T, Finset.coe_singleton, Set.mem_singleton_iff] at ht
        exact ⟨i, by simp, ht.symm⟩
    · intro t _ t' _
      simp
    · intro t _
      rfl
  constructor
  · rintro ⟨as, ⟨n, hy⟩, happ, hs⟩
    exact ⟨as, ⟨n, hy.iso netSingle_wf netSingle_wf (hiso i j)⟩, happ, hs⟩
  · rintro ⟨as, ⟨n, hy⟩, happ, hs⟩
    exact ⟨as, ⟨n, hy.iso netSingle_wf netSingle_wf (hiso j i)⟩, happ, hs⟩

/-- **The state transformer of a sequence network is the composite of the state transformers of
its one-task networks.** -/
theorem netReach_isSeqNet {D : Domain ℕ ℕ ℕ ℕ} {tn : TaskNetwork ℕ ℕ ℕ} {l : List ℕ}
    {xs : List (ℕ ⊕ ℕ)} (h : tn.IsSeqNet l xs) {s s' : Set ℕ} :
    D.NetReach tn s s' ↔ RelChain (fun x => D.NetReach (netSingle 0 x)) xs s s' := by
  induction l generalizing tn xs s with
  | nil =>
    have hxs : xs = [] := by
      have := h.labels
      simp only [List.map_nil] at this
      exact this.symm
    subst hxs
    have hT : tn.T = ∅ := by
      ext t
      rw [h.memT]
      simp
    rw [netReach_empty hT, relChain_nil]
  | cons i l ih =>
    obtain ⟨x, xs, rfl⟩ : ∃ x xs', xs = x :: xs' := by
      have hl := h.length_eq
      cases xs with
      | nil => simp at hl
      | cons x xs' => exact ⟨x, xs', rfl⟩
    obtain ⟨hser, htail⟩ := isSeries_of_isSeqNet_cons h
    rw [Domain.netReach_isSeries_iff hser netSingle_wf htail.wf, relChain_cons]
    refine exists_congr fun s₁ => and_congr (netReach_netSingle_congr i 0 x) (ih htail)

/-- **The state transformer of a one-row described grid.** -/
theorem netReach_oneRow {D : Domain ℕ ℕ ℕ ℕ} (row : List (Bool × ℕ)) {s s' : Set ℕ} :
    D.NetReach (gridDesc [row]).toTaskNetwork s s' ↔
      RelChain (fun x => D.NetReach (netSingle 0 x)) (rowLabels row) s s' :=
  netReach_isSeqNet oneRow_isSeqNet

end Chain

end Syn

end HTN
