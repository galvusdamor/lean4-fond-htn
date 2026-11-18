import HtnComplexity.Computable.AcActions
import HtnPlanning.Core.MethodRestrict
import HtnPlanning.Core.SolutionIso
import HtnPlanning.Core.Transfer
import HtnComplexity.ToHtnAc.ToHtnAcComplete
/-!
# The compilation of a totally ordered problem into an acyclic one, on descriptions

This file assembles the pieces of `AcNum.lean`, `AcBodies.lean`, `AcTasks.lean` and
`AcActions.lean` into

* `HTN.Syn.Ac.acDomOf` — the **description of the compiled acyclic domain**, and
* `HTN.Syn.Ac.acInstOf` — the description of the compiled problem instance,

and proves the theorem the lift is for:

> `HTN.Syn.Ac.solvable_acDesc_iff` — the described compiled problem is solvable exactly when
> the compiled problem of `HtnComplexity/ToHtnAc/ToHtnAc.lean` is.

So the description *is* the construction, and every result about the construction — soundness
(`HTN.ToAc.yield_of_solvable_problem'`), completeness
(`HTN.ToAc.solvable_problem'_of_yield`), acyclicity of the target
(`HTN.ToAc.isAcyclic`) and the size bound (`HTN.ToAc.method_size_le`) — transfers to it.

Three adjustments are needed on the way, and they are exactly the three bridges of
`HtnPlanning/Core/Relabel.lean`, `HtnPlanning/Core/Transfer.lean` and
`HtnPlanning/Core/MethodRestrict.lean`:

1. the compiled signature is numbered (`HTN.ToAc.encFact`, `…encAct`, `…encTask`) and the
   identifiers `ℕ × ℕ` are numbered by `Nat.pairEquiv`;
2. the compiled domain has infinitely many methods, of which only the ones listed by
   `HTN.Syn.Ac.taskListNum` are reachable;
3. a described task network and the relabelled grid it stands for agree on the network but not
   off it (a labelling function is total), so they are compared up to isomorphism.
-/

namespace HTN

namespace Syn

namespace Ac

open ToAc

/-! ### The two descriptions -/

/-- **The description of the compiled acyclic domain.** -/
def acDomOf (V UA UC : List ℕ) (tuples : List (ℕ × ℕ × ℕ)) (pre ad de : ℕ → List ℕ)
    (bound : ℕ) : DomDesc :=
  ((allActs V (nameListOf UA UC) UA).map fun x => (x, actInfo (nameListOf UA UC) pre ad de x),
   (taskListNum V.length bound).flatMap fun t =>
     (bodyNum V UA UC tuples bound t).map fun b => (t, gridDesc b))

/-- **The description of the compiled problem instance.** -/
def acInstOf (V initL goalL : List ℕ) (root : ℕ) : InstDesc :=
  (fKey0 :: V.flatMap fun v => (List.range 5).map fun i => fNeg v i,
   (initL.map fun u => fPos u 0) ++ ((V.filter fun u => !memB initL u).map fun u => fNeg u 0) ++
     (goalL.map fun u => fPos u 2) ++ [fTask (nC root)],
   gridDesc [[pTsk tTI]])

/-! ### Correctness -/

section Denote

variable {F A C I : Type} {f : F → ℕ} {a : A → ℕ} {c : C → ℕ} {D : Domain F A C I}
  {Q : Instance F A C I} {vars : List F} {bound : ℕ} {tI0 : C}
  {V UA UC : List ℕ} {tuples : List (ℕ × ℕ × ℕ)} {pre ad de : ℕ → List ℕ}
  {initL goalL : List ℕ} {root : ℕ}

/-- The methods of the compiled domain that a description lists. -/
def listedMethods (D : Domain F A C I) (vars : List F) (bound : ℕ) :
    Set (Method (ℕ × ℕ) (AcAct F A C) (AcTask F A C)) :=
  {m | m ∈ ToAc.methods D vars bound ∧ InTaskSet vars.length bound m.abstractTask}

/-- **Every reachable compound task name of the compiled problem is listed.** -/
lemma inTaskSet_of_reachableName {t : AcTask F A C}
    (h : (problem' D Q vars bound tI0).ReachableName t) :
    InTaskSet vars.length bound t := by
  induction h with
  | @tnI x nm ht hc =>
      have hx : x ∈ (TaskNetwork.seq [(Sum.inr AcTask.tI : AcAct F A C ⊕ AcTask F A C)]).T := ht
      rw [TaskNetwork.mem_seq_T] at hx
      have hx0 : x = (0, 0) := by
        obtain ⟨i, j⟩ := x
        simp only [List.length_singleton] at hx
        simp only [Prod.mk.injEq]
        exact ⟨hx.1, by omega⟩
      subst hx0
      have hα : (TaskNetwork.seq [(Sum.inr AcTask.tI : AcAct F A C ⊕ AcTask F A C)]).α (0, 0) =
          Sum.inr AcTask.tI := TaskNetwork.seq_α (by simp)
      have hnm : (Sum.inr AcTask.tI : AcAct F A C ⊕ AcTask F A C) = Sum.inr nm := by
        rw [← hα]; exact hc
      have ht' : (AcTask.tI : AcTask F A C) = nm := by simpa using hnm
      subst ht'
      exact trivial
  | @method m x ct hm _ hxT hxα ih =>
      obtain ⟨ls, hls, hsub⟩ := hm
      have hmem : m.subtasks.α x ∈ ls.flatten := by
        rw [hsub] at hxT ⊢
        exact TaskNetwork.grid_α_mem_flatten hxT
      rw [hxα] at hmem
      exact inTaskSet_of_mem_bodies ih hls hmem

/-- **The listed methods are the methods of the described domain**, up to isomorphism of the
subtask networks. -/
lemma methodsIsoEquiv_acDomOf (hb : SourceData f a c D vars V UA UC tuples)
    (hVlen : V.length = vars.length) :
    Problem.MethodsIsoEquiv
      ({m : Method ℕ ℕ ℕ | ∃ e ∈ (acDomOf V UA UC tuples pre ad de bound).methods,
        e.toMethod = m})
      (Method.relabel (encAct f a c) (encTask f a c) Nat.pairEquiv ''
        listedMethods D vars bound) := by
  constructor
  · rintro m ⟨e, he, rfl⟩
    simp only [acDomOf, DomDesc.methods, List.mem_flatMap, List.mem_map] at he
    obtain ⟨t, htl, b, hbm, rfl⟩ := he
    rw [hVlen] at htl
    obtain ⟨T, rfl, hT⟩ := exists_encTask_of_mem_taskListNum (f := f) (a := a) (c := c) htl
    obtain ⟨ls, hls, rfl⟩ := (mem_bodyNum hb T b).1 hbm
    refine ⟨Method.relabel (encAct f a c) (encTask f a c) Nat.pairEquiv
      ⟨T, TaskNetwork.grid ls⟩, ⟨⟨T, TaskNetwork.grid ls⟩, ⟨⟨ls, hls, rfl⟩, hT⟩, rfl⟩, rfl, ?_⟩
    exact gridDesc_iso (encAct f a c) (encTask f a c) ls
  · rintro n ⟨m, ⟨⟨ls, hls, hsub⟩, hT⟩, rfl⟩
    obtain ⟨T, tn⟩ := m
    simp only at hsub hT
    subst hsub
    refine ⟨⟨encTask f a c T, (gridDesc (encBody f a c ls)).toTaskNetwork⟩, ?_, rfl, ?_⟩
    · refine ⟨(encTask f a c T, gridDesc (encBody f a c ls)), ?_, rfl⟩
      simp only [acDomOf, DomDesc.methods, List.mem_flatMap, List.mem_map]
      refine ⟨encTask f a c T, ?_, encBody f a c ls, ?_, rfl⟩
      · rw [hVlen]; exact mem_taskListNum_of_inTaskSet hT
      · exact (mem_bodyNum hb T _).2 ⟨ls, hls, rfl⟩
    · exact (gridDesc_iso (encAct f a c) (encTask f a c) ls).symm

/-- **The described compiled problem is the compiled problem.** -/
theorem solvable_acDesc_iff (hb : SourceData f a c D vars V UA UC tuples)
    (ha : ActData f a c D vars V UA UC pre ad de) (hfinj : Function.Injective f)
    (hinitL : {u | u ∈ initL} = f '' Q.init) (hgoalL : {u | u ∈ goalL} = f '' Q.goal)
    (hroot : c tI0 = root) :
    Solvable (acDomOf V UA UC tuples pre ad de bound) (acInstOf V initL goalL root) ↔
      (problem' D Q vars bound tI0).Solvable := by
  classical
  have hVlen : V.length = vars.length := by rw [hb.facts, List.length_map]
  have hmemV : ∀ u, u ∈ V ↔ ∃ v : F, v ∈ vars ∧ f v = u := by
    intro u; rw [hb.facts, List.mem_map]
  set EF := encFact f a c with hEF
  set EA := encAct f a c with hEA
  set EC := encTask f a c with hEC
  set PD := problem (acDomOf V UA UC tuples pre ad de bound) (acInstOf V initL goalL root)
    with hPDdef
  set PS := problem' D Q vars bound tI0 with hPSdef
  set M := listedMethods D vars bound with hMdef
  set N := Method.relabel EA EC Nat.pairEquiv '' M with hNdef
  set tn' := TaskNetwork.relabel EA EC Nat.pairEquiv PS.tnI with htn'
  -- the action model of the description is the compiled action model
  have hlookup : ∀ o : AcAct F A C,
      (acDomOf V UA UC tuples pre ad de bound).actions.lookup (EA o) =
        some (actInfo (nameListOf UA UC) pre ad de (EA o)) :=
    fun o => lookup_map_self _ _ (encAct_mem_allActs ha o)
  have hprec : ∀ o : AcAct F A C, PD.prec (EA o) = EF '' PS.prec o := by
    intro o
    show {x | x ∈ ((acDomOf V UA UC tuples pre ad de bound).actions.lookup
      (EA o)).elim [] fun y => y.1} = _
    rw [hlookup o]
    exact actInfo_prec ha o
  have hadd : ∀ o : AcAct F A C, PD.add (EA o) = EF '' PS.add o := by
    intro o
    show {x | x ∈ ((acDomOf V UA UC tuples pre ad de bound).actions.lookup
      (EA o)).elim [] fun y => y.2.1} = _
    rw [hlookup o]
    exact actInfo_add ha o
  have hdel : ∀ o : AcAct F A C, PD.del (EA o) = EF '' PS.del o := by
    intro o
    show {x | x ∈ ((acDomOf V UA UC tuples pre ad de bound).actions.lookup
      (EA o)).elim [] fun y => y.2.2} = _
    rw [hlookup o]
    exact actInfo_del ha o
  -- the initial state
  have hinitEq : PD.init = EF '' PS.init := by
    show {u | u ∈ (acInstOf V initL goalL root).initList} = _
    ext u
    simp only [acInstOf, InstDesc.initList, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.mem_map, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro (rfl | ⟨v, hv, i, hi, rfl⟩)
      · exact ⟨AcFact.key0, Or.inl rfl, rfl⟩
      · obtain ⟨w, -, rfl⟩ := (hmemV v).1 hv
        exact ⟨AcFact.neg w ⟨i, hi⟩, Or.inr ⟨w, ⟨i, hi⟩, rfl⟩, rfl⟩
    · rintro ⟨g, (rfl | ⟨w, i, rfl⟩), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨f w, (hmemV _).2 ⟨w, ha.vars_all w, rfl⟩, i, i.isLt, rfl⟩
  -- the goal
  have hgoalEq : PD.goal = EF '' PS.goal := by
    show {u | u ∈ (acInstOf V initL goalL root).goalList} = _
    have hinitMem : ∀ u : ℕ, u ∈ initL ↔ ∃ v ∈ Q.init, f v = u := by
      intro u
      constructor
      · intro hu
        have hu' : u ∈ f '' Q.init := by rw [← hinitL]; exact hu
        obtain ⟨v, hv, hvu⟩ := hu'
        exact ⟨v, hv, hvu⟩
      · rintro ⟨v, hv, rfl⟩
        have hv' : f v ∈ f '' Q.init := ⟨v, hv, rfl⟩
        rw [← hinitL] at hv'
        exact hv'
    have hgoalMem : ∀ u : ℕ, u ∈ goalL ↔ ∃ v ∈ Q.goal, f v = u := by
      intro u
      constructor
      · intro hu
        have hu' : u ∈ f '' Q.goal := by rw [← hgoalL]; exact hu
        obtain ⟨v, hv, hvu⟩ := hu'
        exact ⟨v, hv, hvu⟩
      · rintro ⟨v, hv, rfl⟩
        have hv' : f v ∈ f '' Q.goal := ⟨v, hv, rfl⟩
        rw [← hgoalL] at hv'
        exact hv'
    ext u
    simp only [acInstOf, InstDesc.goalList, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_singleton, Set.mem_image, Set.mem_setOf_eq,
      hinitMem, hgoalMem, Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · rintro (((⟨x, ⟨v, hv, rfl⟩, rfl⟩ | ⟨x, ⟨hxV, hxn⟩, rfl⟩) | ⟨x, ⟨v, hv, rfl⟩, rfl⟩) | rfl)
      · exact ⟨AcFact.pos v 0, Or.inl (Or.inl (Or.inl ⟨v, hv, rfl⟩)), rfl⟩
      · obtain ⟨w, hw, rfl⟩ := (hmemV x).1 hxV
        refine ⟨AcFact.neg w 0, Or.inl (Or.inl (Or.inr ⟨w, ⟨hw, ?_⟩, rfl⟩)), rfl⟩
        intro hc
        rw [memB_iff.2 ((hinitMem (f w)).2 ⟨w, hc, rfl⟩)] at hxn
        exact absurd hxn (by simp)
      · exact ⟨AcFact.pos v 2, Or.inl (Or.inr ⟨v, hv, rfl⟩), rfl⟩
      · exact ⟨AcFact.task (Sum.inr tI0), Or.inr rfl, by subst hroot; rfl⟩
    · rintro ⟨g, ((⟨v, hv, rfl⟩ | ⟨v, ⟨hv, hvn⟩, rfl⟩) | ⟨v, hv, rfl⟩) | rfl, rfl⟩
      · exact Or.inl (Or.inl (Or.inl ⟨f v, ⟨v, hv, rfl⟩, rfl⟩))
      · refine Or.inl (Or.inl (Or.inr ⟨f v, ⟨(hmemV _).2 ⟨v, hv, rfl⟩, ?_⟩, rfl⟩))
        rcases hm : memB initL (f v) with _ | _
        · rfl
        · obtain ⟨w, hw, hwv⟩ := (hinitMem (f v)).1 (memB_iff.1 hm)
          exact absurd (hfinj hwv ▸ hw) hvn
      · exact Or.inl (Or.inr ⟨f v, ⟨v, hv, rfl⟩, rfl⟩)
      · exact Or.inr (by subst hroot; rfl)
  -- the initial task network, up to isomorphism
  have htnIiso : PD.tnI.Iso tn' := by
    exact gridDesc_iso EA EC [[(Sum.inr AcTask.tI : AcAct F A C ⊕ AcTask F A C)]]
  -- the four steps
  have hwfPD : PD.tnI.WF := TnDesc.toTaskNetwork_wf _
  have hwftn' : tn'.WF := TaskNetwork.relabel_wf TaskNetwork.seq_wf
  have step1 : PD.Solvable ↔ (PD.withTnI tn').Solvable := by
    refine Iff.trans (Iff.of_eq (congrArg Problem.Solvable (rfl : PD = PD.withTnI PD.tnI))) ?_
    exact Problem.solvable_congr_tnI_iff PD hwfPD hwftn' htnIiso
  have hmiso : Problem.MethodsIsoEquiv (PD.withTnI tn').methods N :=
    methodsIsoEquiv_acDomOf hb hVlen
  have step2 : (PD.withTnI tn').Solvable ↔ ((PD.withTnI tn').withMethods N).Solvable :=
    (Problem.solvable_congr_methods hmiso).symm
  have step3 : ((PD.withTnI tn').withMethods N).Solvable ↔ (PS.withMethods M).Solvable := by
    refine Problem.solvable_relabel_iff (eF := EF) (eA := EA) (eC := EC) (eI := Nat.pairEquiv)
      (encFact_injective hfinj ha.act_inj ha.name_inj)
      (encAct_injective hfinj ha.act_inj ha.name_inj) encTask_injective
      (fun o _ => hprec o) (fun o _ => hadd o) (fun o _ => hdel o) hinitEq hgoalEq
      TaskNetwork.seq_wf rfl rfl
  have step4 : (PS.withMethods M).Solvable ↔ PS.Solvable := by
    refine Problem.solvable_withMethods_iff (fun m hm => hm.1) (fun m hm => ⟨hm.1, ?_⟩)
    exact inTaskSet_of_reachableName hm.2
  exact step1.trans (step2.trans (step3.trans step4))

end Denote

end Ac

end Syn

end HTN
