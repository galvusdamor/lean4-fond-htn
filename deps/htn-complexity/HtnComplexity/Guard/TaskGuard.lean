import HtnComplexity.Guard.TaskExt
import HtnPlanning.Core.Transfer
/-!
# Method guards: the guard tasks change nothing

`HtnComplexity/Guard/Resplit.lean` guards *actions*; re-splitting a construction so that the
input word sits in the instance rather than in the domain needs, in general, a guard on a
**method** — "the method that writes the letter `c` at position `i` may only be applied when the
instance says that `c` sits at `i`".  The HTN formalism has no such device, and the standard way
of simulating it is to put an extra, unordered primitive subtask into the method's body whose
action is a no-op with the guard fact as its precondition.

This file proves that the simulation is faithful:

> `HTN.GuardTask.solvable_guardTasks_iff` — if the guard facts hold in the initial state and no
> action deletes one, then the domain whose methods carry guard tasks is solvable exactly when
> the original one is.

Composed with `HTN.Guard.solvable_resplit_iff`, this is the missing half of the method-guard
re-split: guarding the *actions* of the guard tasks selects the methods the instance admits, and
the theorem below identifies the plans of the admitted sub-domain with the plans of the original,
word-carrying construction.

The proof puts together the three ingredients of `Guard/Insert.lean`, `Guard/Order.lean` and
`Guard/TaskExt.lean`: the derivations of the two domains correspond, a linearization of the
original network extends to one of the guarded network, and the extra actions of the extended
plan are no-ops whose preconditions hold throughout.
-/

namespace HTN

namespace GuardTask

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

variable {Chk : A → Prop}

omit [DecidableEq I] in
/-- The two networks of an extension induce the same action sequences on the old tasks. -/
theorem Ext.isActionSeq_iff {tn tng : TaskNetwork I A C} {K : Finset I}
    (hext : Ext Chk tn tng K) {l : List I} {as : List A} (hl : ∀ z ∈ l, z ∈ tn.T) :
    tng.IsActionSeq l as ↔ tn.IsActionSeq l as := by
  have hmap : l.map tng.α = l.map tn.α :=
    List.map_congr_left fun z hz => hext.lab z (hl z hz)
  simp only [TaskNetwork.IsActionSeq, hmap]

omit [DecidableEq I] in
/-- A network extended by guard tasks is primitive when the original one is. -/
theorem Ext.isPrimitive {tn tng : TaskNetwork I A C} {K : Finset I} (hext : Ext Chk tn tng K)
    (hprim : tn.IsPrimitive) : tng.IsPrimitive := by
  intro z hz
  rcases (hext.memT z).1 hz with h | h
  · obtain ⟨a, ha⟩ := hprim z h
    exact ⟨a, by rw [hext.lab z h, ha]⟩
  · obtain ⟨a, ha, -⟩ := hext.chk z h
    exact ⟨a, ha⟩

omit [DecidableEq I] in
/-- The original network of an extension is primitive when the extended one is. -/
theorem Ext.isPrimitive_of {tn tng : TaskNetwork I A C} {K : Finset I} (hext : Ext Chk tn tng K)
    (hprim : tng.IsPrimitive) : tn.IsPrimitive := by
  intro z hz
  obtain ⟨a, ha⟩ := hprim z (hext.mem_of_mem hz)
  exact ⟨a, by rw [← hext.lab z hz, ha]⟩

/-! ### The main theorem -/

variable {D Dg : Domain F A C I} {Q : Instance F A C I}
variable {gid : Method I A C → I} {gact : Method I A C → A} {G : Set F}

/-- **Guard tasks do not change solvability.**

`Dg` is the domain whose methods are those of `D` with a guard task added
(`HTN.GuardTask.guardMethod`): an extra, unordered primitive subtask labelled by the method's
guard action.  If every guard action is a no-op whose precondition consists of facts of `G`, the
facts of `G` hold initially and no action deletes one, then the guarded problem and the original
problem are solvable together.

The hypotheses on the two method sets are stated as inclusions in both directions rather than as
an equality of images, so that the theorem applies to a domain presented in any other way. -/
theorem solvable_guardTasks_iff [Infinite I]
    (hact : Dg.toActionModel = D.toActionModel)
    (hmeth : ∀ m ∈ D.methods, guardMethod gid gact m ∈ Dg.methods)
    (hmeth' : ∀ mg ∈ Dg.methods, ∃ m ∈ D.methods, mg = guardMethod gid gact m)
    (hwfm : ∀ m ∈ D.methods, m.subtasks.WF)
    (hfresh : ∀ m ∈ D.methods, gid m ∉ m.subtasks.T)
    (hguard : ∀ m ∈ D.methods, D.prec (gact m) ⊆ G ∧ D.add (gact m) = ∅ ∧ D.del (gact m) = ∅)
    (hdel : ∀ a : A, ∀ f ∈ G, f ∉ D.del a) (hG : G ⊆ Q.init) (hwfI : Q.tnI.WF) :
    (Dg.mkProblem Q).Solvable ↔ (D.mkProblem Q).Solvable := by
  classical
  set Chk : A → Prop := fun a => ∃ m ∈ D.methods, a = gact m with hChkdef
  have hChk : ∀ m ∈ D.methods, Chk (gact m) := fun m hm => ⟨m, hm, rfl⟩
  have hP : ∀ a, Chk a → D.prec a ⊆ G ∧ D.add a = ∅ ∧ D.del a = ∅ := by
    rintro a ⟨m, hm, rfl⟩
    exact hguard m hm
  have hPadd : ∀ a, Chk a → D.add a = ∅ ∧ D.del a = ∅ := fun a ha => ⟨(hP a ha).2.1, (hP a ha).2.2⟩
  -- the two problems have the same action model
  have hmodel : (Dg.mkProblem Q).toActionModel = D.toActionModel := hact
  have hmodel' : (D.mkProblem Q).toActionModel = D.toActionModel := rfl
  rw [Problem.solvable_iff_netYield, Problem.solvable_iff_netYield]
  constructor
  · -- a plan of the guarded domain is a plan of the original one
    rintro ⟨asg, hy, happ, hgoal⟩
    obtain ⟨tngf, hdecg, hprimg, lg, hling, hseqg⟩ := Domain.netYield_iff.1 hy
    obtain ⟨tnf, K, hdecf, hext⟩ :=
      exists_proj_of_decomposesTo (Chk := Chk) hmeth' hwfm hfresh hChk hwfI hwfI
        (Ext.refl Q.tnI) hdecg
    have hprimf : tnf.IsPrimitive := hext.isPrimitive_of hprimg
    set l : List I := lg.filter (fun z => decide (z ∈ tnf.T)) with hl
    have hlmem : ∀ z ∈ l, z ∈ tnf.T := by
      intro z hz
      rw [hl, List.mem_filter] at hz
      simpa using hz.2
    have hlin : tnf.IsLinearization l := by
      refine ⟨hling.1.filter _, ?_, ?_⟩
      · intro z
        constructor
        · exact fun hz => hlmem z hz
        · intro hz
          rw [hl, List.mem_filter]
          exact ⟨(hling.2.1 z).2 (hext.mem_of_mem hz), by simpa using hz⟩
      · have hsub : l.Pairwise (fun a b => ¬ tngf.ord b a) :=
          List.Pairwise.sublist (List.filter_sublist) hling.2.2
        refine List.Pairwise.imp_of_mem ?_ hsub
        intro a b ha hb hab hcon
        exact hab ((hext.ord_iff b (hlmem b hb) a (hlmem a ha)).2 hcon)
    obtain ⟨as, hseq⟩ := TaskNetwork.exists_actionSeq (fun z hz => hprimf z (hlmem z hz))
    have hseqg' : tngf.IsActionSeq l as := (hext.isActionSeq_iff hlmem).2 hseq
    have hins : Ins Chk as asg := by
      refine ins_of_actionSeq (P := Chk) (tn := tngf) (p := fun z => decide (z ∈ tnf.T))
        hseqg (by rw [← hl]; exact hseqg') ?_
      intro z hz hpz a ha
      have hzT : z ∈ tngf.T := (hling.2.1 z).1 hz
      have hznot : z ∉ tnf.T := by simpa using hpz
      rcases (hext.memT z).1 hzT with h | h
      · exact absurd h hznot
      · obtain ⟨b, hb, hbchk⟩ := hext.chk z h
        have : a = b := Sum.inl_injective (by rw [← ha, hb])
        rw [this]; exact hbchk
    refine ⟨as, Domain.netYield_iff.2 ⟨tnf, hdecf, hprimf, l, hlin, hseq⟩, ?_, ?_⟩
    · have happ' : D.toActionModel.SeqApplicable asg Q.init := by
        rw [← hmodel]; exact happ
      have := (seqApplicable_iff D.toActionModel (P := Chk) (G := G) hP hdel hins hG).1 happ'
      exact this
    · show (D.mkProblem Q).GoalState (D.toActionModel.transitionSeq as Q.init)
      have hg2 : (Dg.mkProblem Q).GoalState (D.toActionModel.transitionSeq asg Q.init) := by
        have heq : (Dg.mkProblem Q).transitionSeq asg (Dg.mkProblem Q).init
            = D.toActionModel.transitionSeq asg Q.init := by rw [← hmodel]; rfl
        rwa [heq] at hgoal
      have hstate : D.toActionModel.transitionSeq asg Q.init
          = D.toActionModel.transitionSeq as Q.init :=
        transitionSeq_eq D.toActionModel hPadd hins Q.init
      rw [hstate] at hg2
      exact hg2
  · -- a plan of the original domain is a plan of the guarded one
    rintro ⟨as, hy, happ, hgoal⟩
    obtain ⟨tnf, hdec, hprim, l, hlin, hseq⟩ := Domain.netYield_iff.1 hy
    obtain ⟨tngf, K, hdecg, hext, -⟩ :=
      exists_ext_of_decomposesTo (Chk := Chk) hmeth hwfm hfresh hChk hwfI hdec ∅
    have hwff : tnf.WF := HTN.DecomposesTo.wf hdec hwfI
    have hwfg : tngf.WF := HTN.DecomposesTo.wf hdecg hwfI
    have hprimg : tngf.IsPrimitive := hext.isPrimitive hprim
    obtain ⟨lg, hling, hfil⟩ :=
      exists_linearization_ext (tn := tnf) (tng := tngf) (K := K) hwff hwfg hext.memT
        (fun a ha b hb h => (hext.ord_iff a ha b hb).1 h) hlin
    obtain ⟨asg, hseqg⟩ :=
      TaskNetwork.exists_actionSeq (fun z hz => hprimg z ((hling.2.1 z).1 hz))
    have hlmem : ∀ z ∈ l, z ∈ tnf.T := fun z hz => (hlin.2.1 z).1 hz
    have hins : Ins Chk as asg := by
      refine ins_of_actionSeq (P := Chk) (tn := tngf) (p := fun z => decide (z ∈ tnf.T))
        hseqg ?_ ?_
      · rw [hfil]
        exact (hext.isActionSeq_iff hlmem).2 hseq
      · intro z hz hpz a ha
        have hzT : z ∈ tngf.T := (hling.2.1 z).1 hz
        have hznot : z ∉ tnf.T := by simpa using hpz
        rcases (hext.memT z).1 hzT with h | h
        · exact absurd h hznot
        · obtain ⟨b, hb, hbchk⟩ := hext.chk z h
          have : a = b := Sum.inl_injective (by rw [← ha, hb])
          rw [this]; exact hbchk
    refine ⟨asg, Domain.netYield_iff.2 ⟨tngf, hdecg, hprimg, lg, hling, hseqg⟩, ?_, ?_⟩
    · have happ' : D.toActionModel.SeqApplicable as Q.init := happ
      have := (seqApplicable_iff D.toActionModel (P := Chk) (G := G) hP hdel hins hG).2 happ'
      rw [hmodel]
      exact this
    · have hstate : D.toActionModel.transitionSeq asg Q.init
          = D.toActionModel.transitionSeq as Q.init :=
        transitionSeq_eq D.toActionModel hPadd hins Q.init
      show (Dg.mkProblem Q).GoalState ((Dg.mkProblem Q).transitionSeq asg (Dg.mkProblem Q).init)
      rw [show (Dg.mkProblem Q).transitionSeq asg (Dg.mkProblem Q).init
          = D.toActionModel.transitionSeq asg Q.init from by rw [← hmodel]; rfl, hstate]
      exact hgoal

end GuardTask

end HTN
