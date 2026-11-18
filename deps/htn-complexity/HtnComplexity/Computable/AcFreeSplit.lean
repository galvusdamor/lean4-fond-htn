import HtnComplexity.Computable.AcFreeBoot
/-!
# Splitting the wrapped problem into its three phases

The initial task network of `HTN.Syn.AcFree.wrapInst` is the chain `aBoot ; t_I ; tPost`.  Its
three tasks are executed in that order by every solution, so a solution of the wrapped problem
is exactly

* the boot action, which produces the initial state `HTN.Syn.AcFree.acStart` of the acyclic
  construction next to the facts `HTN.Syn.AcFree.wrapExtra` of the wrapper,
* a refinement of the initial task `tTI` of the acyclic construction, which — by conservativity
  and the frame property of `HtnComplexity/Computable/AcFreePhases.lean` — behaves exactly
  as in the description that is wrapped, and
* a refinement of the verification phase, computed in
  `HtnComplexity/Computable/AcFreeTail.lean`.

`HTN.Syn.AcFree.solvable_wrap_split` is that decomposition.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

variable {V : List ℕ} {d₀ : DomDesc}

/-- A one-task network labelled by an action is refined only by that action. -/
lemma netYield_netSingle_prim {D : Domain ℕ ℕ ℕ ℕ} {i a : ℕ} {as : List ℕ} :
    D.NetYield (netSingle i (Sum.inl a)) as ↔ as = [a] :=
  ⟨fun ⟨_, hn⟩ =>
    ((Domain.netYieldN_single_prim (D := D) isSingle_netSingle rfl).1 hn).2,
   fun h => ⟨0, (Domain.netYieldN_single_prim (D := D) isSingle_netSingle rfl).2 ⟨rfl, h⟩⟩⟩

/-- **The three phases of the wrapped problem.** -/
theorem solvable_wrap_split (hshape : BaseShaped d₀) (q : InstDesc) :
    Solvable (wrapDom V d₀) (wrapInst q) ↔
      ∃ bs, d₀.toDomain.NetYield (netSingle (Nat.pair 0 1) (Sum.inr tTI)) bs ∧
        d₀.toDomain.SeqApplicable bs (acStart V) ∧
        (∀ v ∈ V,
          fNeg v 0 ∈ d₀.toDomain.transitionSeq bs (acStart V) ∪ wrapExtra V q ∨
            (fPos v 0 ∈ d₀.toDomain.transitionSeq bs (acStart V) ∪ wrapExtra V q ∧
              fLic v ∈ d₀.toDomain.transitionSeq bs (acStart V) ∪ wrapExtra V q)) ∧
        {f | f ∈ (wrapInst q).goalList} ⊆
          (d₀.toDomain.transitionSeq bs (acStart V) ∪ wrapExtra V q) ∪
            earned V (d₀.toDomain.transitionSeq bs (acStart V) ∪ wrapExtra V q) := by
  classical
  have hne : (Nat.pair 0 1 : ℕ) ≠ Nat.pair 0 2 := pair_ne_pair (by omega)
  have hX : acStart V ⊆ baseFacts := acStart_subset_baseFacts
  have hE : ∀ f ∈ wrapExtra V q, f ∉ baseFacts := not_baseFact_wrapExtra
  have hlab : ∀ t ∈ (netSingle (Nat.pair 0 1) (Sum.inr tTI)).T,
      GoodLabel ((netSingle (Nat.pair 0 1) (Sum.inr tTI)).α t) := fun _ _ => baseTask_tTI
  rw [Solvable, Problem.solvable_isSeries_iff (wrapInst_isSeries q) netSingle_wf
    (netPair_wf hne)]
  simp only [netYield_netSingle_prim, exists_eq_left]
  have hboot : (problem (wrapDom V d₀) (wrapInst q)).transitionSeq [aBoot]
      (problem (wrapDom V d₀) (wrapInst q)).init = acStart V ∪ wrapExtra V q := by
    show (wrapDom V d₀).toDomain.transitionSeq [aBoot] {f | f ∈ (wrapInst q).initList} = _
    rw [ActionModel.transitionSeq_cons]
    show (wrapDom V d₀).toDomain.transitionSeq []
      ((wrapDom V d₀).toDomain.transition aBoot {f | f ∈ (wrapInst q).initList}) = _
    rw [transition_boot hshape]
    rfl
  have happ : (problem (wrapDom V d₀) (wrapInst q)).SeqApplicable [aBoot]
      (problem (wrapDom V d₀) (wrapInst q)).init := by
    refine ⟨?_, trivial⟩
    show (wrapDom V d₀).prec aBoot ⊆ _
    rw [prec_boot V d₀ hshape]
    exact Set.empty_subset _
  have hrr : ∀ (s s' : Set ℕ) (tn tn' : TaskNetwork ℕ ℕ ℕ),
      ((problem (wrapDom V d₀) (wrapInst q)).restart s tn).restart s' tn' =
        (problem (wrapDom V d₀) (wrapInst q)).restart s' tn' := fun _ _ _ _ => rfl
  rw [iff_iff_implies_and_implies]
  constructor
  · rintro ⟨-, hsolv⟩
    rw [hboot] at hsolv
    rw [Problem.solvable_isSeries_iff (P := ((problem (wrapDom V d₀) (wrapInst q)).restart
      (acStart V ∪ wrapExtra V q) (netPair (Nat.pair 0 1) (Nat.pair 0 2) (Sum.inr tTI)
        (Sum.inr tPost)))) (netPair_isSeries hne) netSingle_wf netSingle_wf] at hsolv
    simp only [Problem.restart_init, Problem.restart_toActionModel, hrr] at hsolv
    obtain ⟨bs, hy, happ', htail⟩ := hsolv
    have hy' : d₀.toDomain.NetYield (netSingle (Nat.pair 0 1) (Sum.inr tTI)) bs :=
      (netYield_wrap_iff (V := V) hshape hlab).1 hy
    have hbs : ∀ a ∈ bs, BaseAct a := baseAct_of_netYield hshape hlab hy'
    refine ⟨bs, hy', (seqApplicable_wrap_iff (V := V) hshape hbs hX hE).1 happ', ?_, ?_⟩ <;>
      [skip; skip] <;>
    · have hts : (problem (wrapDom V d₀) (wrapInst q)).transitionSeq bs
          (acStart V ∪ wrapExtra V q) =
          d₀.toDomain.transitionSeq bs (acStart V) ∪ wrapExtra V q :=
        transitionSeq_wrap (V := V) hshape hbs hX hE
      rw [hts] at htail
      have := (solvable_post hshape (wrapInst q) _ (Nat.pair 0 2)).1 htail
      first
        | exact this.1
        | exact this.2
  · rintro ⟨bs, hy', happ', hcond, hgoal⟩
    have hbs : ∀ a ∈ bs, BaseAct a := baseAct_of_netYield hshape hlab hy'
    refine ⟨happ, ?_⟩
    rw [hboot, Problem.solvable_isSeries_iff (P := ((problem (wrapDom V d₀) (wrapInst q)).restart
      (acStart V ∪ wrapExtra V q) (netPair (Nat.pair 0 1) (Nat.pair 0 2) (Sum.inr tTI)
        (Sum.inr tPost)))) (netPair_isSeries hne) netSingle_wf netSingle_wf]
    refine ⟨bs, (netYield_wrap_iff (V := V) hshape hlab).2 hy',
      (seqApplicable_wrap_iff (V := V) hshape hbs hX hE).2 happ', ?_⟩
    have hts : (problem (wrapDom V d₀) (wrapInst q)).transitionSeq bs
        (acStart V ∪ wrapExtra V q) =
        d₀.toDomain.transitionSeq bs (acStart V) ∪ wrapExtra V q :=
      transitionSeq_wrap (V := V) hshape hbs hX hE
    simp only [Problem.restart_init, Problem.restart_toActionModel, hrr]
    rw [hts]
    exact (solvable_post hshape (wrapInst q) _ (Nat.pair 0 2)).2 ⟨hcond, hgoal⟩

end AcFree

end Syn

end HTN
