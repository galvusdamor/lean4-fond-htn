import HtnComplexity.Computable.TailDesc
import HtnPlanning.Core.MethodRestrict
import HtnPlanning.Core.Transfer
import HtnPlanning.Core.Reachability
/-!
# Writing a semantic problem down as a description

Every construction of this development that has to be *measured* — a hardness family, a cell of
one of the tables — lives in the finite description language of
`HtnPlanning/Computable/Syntax.lean`, whereas the constructions that are easiest to
*reason* about live over abstract signatures (`HtnComplexity/TMEnc/TMEncoding.lean` and the
`TMEncFix*` files are the extreme case).  Bridging the two has so far been done by hand, once
per construction, most fully in `HtnComplexity/Computable/AcDom.lean`.

This file extracts that argument once and for all.  A `HTN.Syn.Rendering P` is the data needed
to write a semantic problem `P` over the identifiers `ℕ × ℕ` down as a pair of descriptions:

* numberings `eF`, `eA`, `eC` of the facts, the actions and the compound task names, each
  injective;
* the finite list `acts` of actions to be described, with their precondition, add and delete
  lists, covering every action the problem can use (`HTN.Problem.UsedAction`);
* the finite list `bodies` of methods, each a compound task name together with the **shape** of
  its subtask network (`HTN.Syn.Shape`: parallel rows, one of which may be ordered after all
  the rows before it), which is the shape of every method body of this development.  The list has to contain every *reachable* method
  (`HTN.Problem.ReachableMethod`) and only methods of `P`; unreachable methods of `P` may be
  left out, which is what makes the tool applicable to a domain with infinitely many methods;
* the initial state, the goal and the initial task network, the last again a shape.

The results are

* `HTN.Syn.Rendering.domDesc`, `HTN.Syn.Rendering.instDesc` — the two descriptions, and
* `HTN.Syn.Rendering.solvable_iff` — **the described problem is solvable exactly when the
  semantic one is**.

The proof is the four-step argument of `AcDom.lean`: the described initial task network is the
relabelled one up to isomorphism (`HTN.Syn.gridDesc_iso`), so is every described method body,
the change of signature preserves solvability (`HTN.Problem.solvable_relabel_iff`), and the
methods that were left out are unreachable (`HTN.Problem.solvable_withMethods_iff`).
-/

namespace HTN

namespace Syn

open TaskNetwork

variable {F A C : Type} [Inhabited A]

/-! ### Looking up a numbered key -/

/-- A lookup in a list keyed by an injective numbering finds the entry of the key. -/
theorem lookup_map_inj {α β : Type} (e : α → ℕ) (he : Function.Injective e) (g : α → β)
    {l : List α} {o : α} (ho : o ∈ l) :
    (l.map fun x => (e x, g x)).lookup (e o) = some (g o) := by
  induction l with
  | nil => simp at ho
  | cons x xs ih =>
    rw [List.map_cons, List.lookup_cons]
    by_cases h : e o = e x
    · have hx : o = x := he h
      subst hx
      simp
    · rw [show (e o == e x) = false by simp [h]]
      exact ih ((List.mem_cons.1 ho).resolve_left fun hc => h (congrArg e hc))

/-! ### The data of a rendering -/

/-- **What it takes to write a semantic problem down as a description**: injective numberings of
the three kinds of name, a list of actions covering the ones the problem uses, a list of methods
covering the reachable ones — each with a grid body — and the initial state, goal and initial
task network. -/
structure Rendering (P : Problem F A C (ℕ × ℕ)) where
  /-- The numbering of the facts. -/
  eF : F → ℕ
  /-- The numbering of the action names. -/
  eA : A → ℕ
  /-- The numbering of the compound task names. -/
  eC : C → ℕ
  /-- The facts are numbered injectively. -/
  eF_inj : Function.Injective eF
  /-- The action names are numbered injectively. -/
  eA_inj : Function.Injective eA
  /-- The compound task names are numbered injectively. -/
  eC_inj : Function.Injective eC
  /-- The actions the description lists. -/
  acts : List A
  /-- The precondition of an action, as a list. -/
  precL : A → List F
  /-- The add list of an action. -/
  addL : A → List F
  /-- The delete list of an action. -/
  delL : A → List F
  /-- The methods the description lists: a compound task name and the shape of its body. -/
  bodies : List (C × Shape A C)
  /-- The initial task network, as a shape. -/
  tnIshape : Shape A C
  /-- The initial state, as a list. -/
  initL : List F
  /-- The goal, as a list. -/
  goalL : List F
  /-- Every action the problem can use is listed. -/
  used_mem : ∀ o, P.UsedAction o → o ∈ acts
  /-- The listed precondition is the precondition. -/
  precL_eq : ∀ o ∈ acts, {v | v ∈ precL o} = P.prec o
  /-- The listed add list is the add list. -/
  addL_eq : ∀ o ∈ acts, {v | v ∈ addL o} = P.add o
  /-- The listed delete list is the delete list. -/
  delL_eq : ∀ o ∈ acts, {v | v ∈ delL o} = P.del o
  /-- The listed initial state is the initial state. -/
  init_eq : {v | v ∈ initL} = P.init
  /-- The listed goal is the goal. -/
  goal_eq : {v | v ∈ goalL} = P.goal
  /-- The initial task network is well formed. -/
  tnI_wf : P.tnI.WF
  /-- The initial task network is the network of the listed shape, up to isomorphism. -/
  tnI_iso : P.tnI.Iso tnIshape.net
  /-- Every listed method is a method of the problem, up to isomorphism of the body. -/
  bodies_sub : ∀ p ∈ bodies, ∃ m ∈ P.methods,
    m.abstractTask = p.1 ∧ m.subtasks.Iso p.2.net
  /-- Every reachable method of the problem is listed, up to isomorphism of the body. -/
  bodies_all : ∀ m, P.ReachableMethod m → ∃ p ∈ bodies,
    m.abstractTask = p.1 ∧ m.subtasks.Iso p.2.net


/-! ### Discharging the two method conditions

The two method conditions of a rendering are usually verified through a list of the compound
task names the problem can reach: every reachable name is listed, and for every listed name
every method of the problem decomposing it appears in `bodies`. -/

/-- **The reachable methods are listed**, from a list of the reachable compound task names. -/
theorem bodies_all_of_names {P : Problem F A C (ℕ × ℕ)}
    {bodies : List (C × Shape A C)} {names : List C}
    (hnames : ∀ t : C, P.ReachableName t → t ∈ names)
    (hlist : ∀ m ∈ P.methods, m.abstractTask ∈ names →
      ∃ p ∈ bodies, m.abstractTask = p.1 ∧ m.subtasks.Iso p.2.net) :
    ∀ m, P.ReachableMethod m →
      ∃ p ∈ bodies, m.abstractTask = p.1 ∧ m.subtasks.Iso p.2.net :=
  fun m hm => hlist m hm.1 (hnames _ hm.2)

namespace Rendering

variable {P : Problem F A C (ℕ × ℕ)} (R : Rendering P)

/-- **The description of the domain**: the listed actions with their numbered precondition, add
and delete lists, and the listed methods with their described bodies. -/
def domDesc : DomDesc :=
  (R.acts.map fun o =>
      (R.eA o, ((R.precL o).map R.eF, (R.addL o).map R.eF, (R.delL o).map R.eF)),
    R.bodies.map fun p => (R.eC p.1, p.2.desc R.eA R.eC))

/-- **The description of the problem instance.** -/
def instDesc : InstDesc :=
  (R.initL.map R.eF, R.goalL.map R.eF, R.tnIshape.desc R.eA R.eC)

/-- The methods of `P` that the rendering lists. -/
def listed : Set (Method (ℕ × ℕ) A C) :=
  {m | m ∈ P.methods ∧ ∃ p ∈ R.bodies,
    m.abstractTask = p.1 ∧ m.subtasks.Iso p.2.net}

theorem listed_subset : R.listed ⊆ P.methods := fun _ hm => hm.1

/-! ### The described action model -/

theorem lookup_domDesc {o : A} (ho : o ∈ R.acts) :
    R.domDesc.actions.lookup (R.eA o) =
      some ((R.precL o).map R.eF, (R.addL o).map R.eF, (R.delL o).map R.eF) :=
  lookup_map_inj R.eA R.eA_inj _ ho

theorem prec_domDesc {o : A} (ho : o ∈ R.acts) :
    R.domDesc.prec (R.eA o) = R.eF '' P.prec o := by
  have h : R.domDesc.prec (R.eA o) = {x | x ∈ (R.precL o).map R.eF} := by
    show {x | x ∈ (R.domDesc.actions.lookup (R.eA o)).elim [] fun y => y.1} = _
    rw [R.lookup_domDesc ho]
    rfl
  rw [h, ← R.precL_eq o ho]
  ext x
  simp [Set.mem_image, eq_comm]

theorem add_domDesc {o : A} (ho : o ∈ R.acts) :
    R.domDesc.add (R.eA o) = R.eF '' P.add o := by
  have h : R.domDesc.add (R.eA o) = {x | x ∈ (R.addL o).map R.eF} := by
    show {x | x ∈ (R.domDesc.actions.lookup (R.eA o)).elim [] fun y => y.2.1} = _
    rw [R.lookup_domDesc ho]
    rfl
  rw [h, ← R.addL_eq o ho]
  ext x
  simp [Set.mem_image, eq_comm]

theorem del_domDesc {o : A} (ho : o ∈ R.acts) :
    R.domDesc.del (R.eA o) = R.eF '' P.del o := by
  have h : R.domDesc.del (R.eA o) = {x | x ∈ (R.delL o).map R.eF} := by
    show {x | x ∈ (R.domDesc.actions.lookup (R.eA o)).elim [] fun y => y.2.2} = _
    rw [R.lookup_domDesc ho]
    rfl
  rw [h, ← R.delL_eq o ho]
  ext x
  simp [Set.mem_image, eq_comm]

theorem init_instDesc : {x | x ∈ R.instDesc.initList} = R.eF '' P.init := by
  rw [← R.init_eq]
  ext x
  simp [instDesc, InstDesc.initList, Set.mem_image, eq_comm]

theorem goal_instDesc : {x | x ∈ R.instDesc.goalList} = R.eF '' P.goal := by
  rw [← R.goal_eq]
  ext x
  simp [instDesc, InstDesc.goalList, Set.mem_image, eq_comm]

/-! ### The described methods -/

/-- **The described methods are the listed ones**, up to isomorphism of the subtask networks. -/
theorem methodsIsoEquiv :
    Problem.MethodsIsoEquiv
      ({m : Method ℕ ℕ ℕ | ∃ e ∈ R.domDesc.methods, e.toMethod = m})
      (Method.relabel R.eA R.eC Nat.pairEquiv '' R.listed) := by
  constructor
  · rintro m ⟨e, he, rfl⟩
    simp only [domDesc, DomDesc.methods, List.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨m, hmP, hmt, hmiso⟩ := R.bodies_sub p hp
    refine ⟨Method.relabel R.eA R.eC Nat.pairEquiv m, ⟨m, ⟨hmP, p, hp, hmt, hmiso⟩, rfl⟩, ?_, ?_⟩
    · show R.eC m.abstractTask = R.eC p.1
      rw [hmt]
    · exact (Shape.desc_iso R.eA R.eC p.2).trans (TaskNetwork.Iso.relabel hmiso.symm)
  · rintro n ⟨m, ⟨hmP, p, hp, hmt, hmiso⟩, rfl⟩
    refine ⟨MethodDesc.toMethod (R.eC p.1, p.2.desc R.eA R.eC),
      ⟨⟨R.eC p.1, p.2.desc R.eA R.eC⟩, ?_, rfl⟩, ?_, ?_⟩
    · simp only [domDesc, DomDesc.methods, List.mem_map]
      exact ⟨p, hp, rfl⟩
    · show R.eC p.1 = R.eC m.abstractTask
      rw [hmt]
    · exact (TaskNetwork.Iso.relabel hmiso).trans (Shape.desc_iso R.eA R.eC p.2).symm

/-! ### The theorem -/

/-- **The described problem is the semantic problem.** -/
theorem solvable_iff [Nonempty C] : Solvable R.domDesc R.instDesc ↔ P.Solvable := by
  classical
  set PD := problem R.domDesc R.instDesc with hPD
  set M := R.listed with hM
  set tn' := TaskNetwork.relabel R.eA R.eC Nat.pairEquiv P.tnI with htn'
  set N := Method.relabel R.eA R.eC Nat.pairEquiv '' M with hN
  have hwfP : P.tnI.WF := R.tnI_wf
  -- step 1: the described initial task network is the relabelled one, up to isomorphism
  have htnIiso : PD.tnI.Iso tn' :=
    (Shape.desc_iso R.eA R.eC R.tnIshape).trans (TaskNetwork.Iso.relabel R.tnI_iso.symm)
  have step1 : PD.Solvable ↔ (PD.withTnI tn').Solvable := by
    refine Iff.trans (Iff.of_eq (congrArg Problem.Solvable (rfl : PD = PD.withTnI PD.tnI))) ?_
    exact Problem.solvable_congr_tnI_iff PD (TnDesc.toTaskNetwork_wf _)
      (TaskNetwork.relabel_wf hwfP) htnIiso
  -- step 2: the described methods are the listed ones, up to isomorphism
  have step2 : (PD.withTnI tn').Solvable ↔ ((PD.withTnI tn').withMethods N).Solvable :=
    (Problem.solvable_congr_methods (R.methodsIsoEquiv)).symm
  -- step 3: the change of signature
  have hused : ∀ o : A, (P.withMethods M).UsedAction o → o ∈ R.acts := by
    rintro o (⟨t, ht, hα⟩ | ⟨m, hm, t, ht, hα⟩)
    · exact R.used_mem o (Or.inl ⟨t, ht, hα⟩)
    · exact R.used_mem o (Or.inr ⟨m, R.listed_subset hm, t, ht, hα⟩)
  have step3 : ((PD.withTnI tn').withMethods N).Solvable ↔ (P.withMethods M).Solvable := by
    refine Problem.solvable_relabel_iff (eF := R.eF) (eA := R.eA) (eC := R.eC)
      (eI := Nat.pairEquiv) R.eF_inj R.eA_inj R.eC_inj
      (fun o ho => R.prec_domDesc (hused o ho)) (fun o ho => R.add_domDesc (hused o ho))
      (fun o ho => R.del_domDesc (hused o ho)) R.init_instDesc R.goal_instDesc hwfP rfl rfl
  -- step 4: the methods that were left out are unreachable
  have step4 : (P.withMethods M).Solvable ↔ P.Solvable :=
    Problem.solvable_withMethods_iff R.listed_subset fun m hm => ⟨hm.1, R.bodies_all m hm⟩
  exact step1.trans (step2.trans (step3.trans step4))



/-! ### The size of a rendering

A hardness family bounds the *size* of the two descriptions, so the bridge has to say how large
the descriptions of a rendering are.  Both bounds are read off the lists the rendering carries:
one symbol per listed action and per fact it mentions, and at most three per cell of a body
(`HTN.Syn.Shape.size_desc_le`). -/

/-- **The size of the described domain**: one symbol per listed action, one per fact it
mentions, one per listed method and at most three per cell of its body. -/
theorem size_domDesc_le :
    R.domDesc.size ≤
      (R.acts.map fun o => 1 + (R.precL o).length + (R.addL o).length + (R.delL o).length).sum +
        (R.bodies.map fun p => 1 + 3 * p.2.cells + p.2.after).sum := by
  refine Nat.add_le_add ?_ ?_
  · show ((R.acts.map fun o =>
      (R.eA o, ((R.precL o).map R.eF, (R.addL o).map R.eF, (R.delL o).map R.eF))).map
        ActionDesc.size).sum ≤ _
    rw [List.map_map]
    refine List.sum_le_sum fun o _ => ?_
    simp [ActionDesc.size]
  · show ((R.bodies.map fun p => (R.eC p.1, p.2.desc R.eA R.eC)).map MethodDesc.size).sum ≤ _
    rw [List.map_map]
    refine List.sum_le_sum fun p _ => ?_
    have := Shape.size_desc_le R.eA R.eC p.2
    show 1 + (p.2.desc R.eA R.eC).size ≤ 1 + 3 * p.2.cells + p.2.after
    omega

/-- **The size of the described instance.** -/
theorem size_instDesc_le :
    R.instDesc.size ≤
      R.initL.length + R.goalL.length + 3 * R.tnIshape.cells + R.tnIshape.after := by
  have h := Shape.size_desc_le R.eA R.eC R.tnIshape
  have h2 : R.instDesc.size =
      R.initL.length + R.goalL.length + (R.tnIshape.desc R.eA R.eC).size := by
    simp [InstDesc.size, instDesc, InstDesc.initList, InstDesc.goalList, InstDesc.tnI]
  omega

end Rendering

end Syn

end HTN
