import HtnComplexity.Undec.Encoding
import HtnPlanning.Core.Transfer
import HtnPlanning.Core.MethodRestrict
import HtnPlanning.Interleave.NetYield
/-!
# The described problem of the encoding is the semantic one

`HTN.Undec.tsmDom` and `HTN.Undec.tsmInst` are *descriptions*; `HTN.Undec.semProblem` is the
planning problem they are meant to denote, over the grid identifiers `ℕ × ℕ`.  This file proves
that the two are solvable together (`HTN.Undec.solvable_tsm_iff_sem`), by the three bridges the
development uses everywhere:

1. `HTN.Problem.solvable_congr_tnI_iff` — the described initial task network and the relabelled
   grid are isomorphic (`HTN.Syn.gridDesc_iso`), not equal, because the labelling function of a
   task network is total and the two disagree off the network;
2. `HTN.Problem.solvable_congr_methods` — the same for the method bodies;
3. `HTN.Problem.solvable_relabel_iff` — the change of identifiers `ℕ ≃ ℕ × ℕ`; here the facts,
   the action names and the compound task names are *unchanged*, so all its hypotheses about the
   action model are equalities of the two descriptions of the same action model
   (`HTN.Undec.prec_tsmDom` and friends).

Combined with `HTN.Problem.solvable_iff_netYield` and `HTN.Domain.netYield_grid_iff` this gives
`HTN.Undec.solvable_tsm_iff_grid`: the described problem is solvable exactly when the grid of
the two stacks refines into an executable action sequence reaching the goal.
-/

namespace HTN

namespace Undec

open Syn TaskNetwork Domain

/-- The methods of the described domain are, up to isomorphism of their bodies, the relabelled
methods of `semDom`. -/
theorem methodsIsoEquiv_tsmDom (M : TSM) :
    Problem.MethodsIsoEquiv
      {m : Method ℕ ℕ ℕ | ∃ e ∈ (tsmDom M).methods, e.toMethod = m}
      (Method.relabel id id Nat.pairEquiv '' (semDom M).methods) := by
  constructor
  · rintro m ⟨e, he, rfl⟩
    simp only [tsmDom, DomDesc.methods, List.mem_map, List.mem_range] at he
    obtain ⟨n, hn, rfl⟩ := he
    refine ⟨Method.relabel id id Nat.pairEquiv
      ⟨tskName (M.trAt n).stk (M.trAt n).pop, TaskNetwork.grid (bodyOf n (M.trAt n))⟩,
      ⟨_, ⟨n, hn, rfl⟩, rfl⟩, rfl, ?_⟩
    exact gridDesc_iso id id (bodyOf n (M.trAt n))
  · rintro m ⟨m', ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨MethodDesc.toMethod (tskName (M.trAt n).stk (M.trAt n).pop,
      gridDescOf id id (bodyOf n (M.trAt n))), ⟨_, ?_, rfl⟩, rfl, ?_⟩
    · simp only [tsmDom, DomDesc.methods, List.mem_map, List.mem_range]
      exact ⟨n, hn, rfl⟩
    · exact (gridDesc_iso id id (bodyOf n (M.trAt n))).symm

/-- **The described problem of the encoding is the semantic problem of the encoding.** -/
theorem solvable_tsm_iff_sem (M : TSM) (s1 s2 : List ℕ) :
    Syn.Solvable (tsmDom M) (tsmInst M s1 s2) ↔ (semProblem M s1 s2).Solvable := by
  classical
  set PD := Syn.problem (tsmDom M) (tsmInst M s1 s2)
  set PS := semProblem M s1 s2
  set tn' := TaskNetwork.relabel id id Nat.pairEquiv PS.tnI
  set N := Method.relabel (I := ℕ × ℕ) (I' := ℕ) id id Nat.pairEquiv '' PS.methods
  have htnIiso : PD.tnI.Iso tn' := gridDesc_iso id id [stackChain false s1, stackChain true s2]
  have hwfPD : PD.tnI.WF := TnDesc.toTaskNetwork_wf _
  have hwftn' : tn'.WF := TaskNetwork.relabel_wf TaskNetwork.grid_wf
  have step1 : PD.Solvable ↔ (PD.withTnI tn').Solvable := by
    refine Iff.trans (Iff.of_eq (congrArg Problem.Solvable (rfl : PD = PD.withTnI PD.tnI))) ?_
    exact Problem.solvable_congr_tnI_iff PD hwfPD hwftn' htnIiso
  have hmiso : Problem.MethodsIsoEquiv (PD.withTnI tn').methods N := methodsIsoEquiv_tsmDom M
  have step2 : (PD.withTnI tn').Solvable ↔ ((PD.withTnI tn').withMethods N).Solvable :=
    (Problem.solvable_congr_methods hmiso).symm
  have step3 : ((PD.withTnI tn').withMethods N).Solvable ↔ PS.Solvable := by
    refine Problem.solvable_relabel_iff (eF := id) (eA := id) (eC := id) (eI := Nat.pairEquiv)
      Function.injective_id Function.injective_id Function.injective_id
      (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ TaskNetwork.grid_wf rfl rfl
    · show (tsmDom M).prec o = _
      rw [prec_tsmDom, Set.image_id]
      rfl
    · show (tsmDom M).add o = _
      rw [add_tsmDom, Set.image_id]
      rfl
    · show (tsmDom M).del o = _
      rw [del_tsmDom, Set.image_id]
      rfl
    · show {f | f ∈ [M.start]} = _
      rw [Set.image_id]
      show {f | f ∈ [M.start]} = ({M.start} : Set ℕ)
      ext x
      simp
    · show {f | f ∈ [M.acc]} = _
      rw [Set.image_id]
      show {f | f ∈ [M.acc]} = ({M.acc} : Set ℕ)
      ext x
      simp
  exact step1.trans (step2.trans step3)

/-- **Solvability of the encoding in terms of the refinements of the grid of the two stacks.** -/
theorem solvable_tsm_iff_grid (M : TSM) (s1 s2 : List ℕ) :
    Syn.Solvable (tsmDom M) (tsmInst M s1 s2) ↔
      ∃ as, (semDom M).GridYield [stackChain false s1, stackChain true s2] as ∧
        (semDom M).SeqApplicable as {M.start} ∧
        {M.acc} ⊆ (semDom M).transitionSeq as {M.start} := by
  rw [solvable_tsm_iff_sem, semProblem, Problem.solvable_iff_netYield]
  refine exists_congr fun as => ?_
  refine and_congr ?_ Iff.rfl
  exact netYield_grid_iff (semDom_grid M)

end Undec

end HTN
