import HtnComplexity.Guard.TaskGuard
import HtnComplexity.Guard.Resplit
/-!
# The method-guard re-split

This file assembles the tools of the `Guard/` directory into the step a hardness family asks for:
moving a parameter of a construction out of the **domain** and into the **instance**, when the
choice the parameter makes is a choice of *method* and not merely a choice of action.

The setting is the one of `HtnComplexity/Guard/Resplit.lean`: `Dall` offers, at each choice
point, one method per letter of the alphabet — it does not mention the word — and `Dspec ⊆ Dall`
is the sub-domain of the methods of *the* word.  Each method `m` of `Dall` carries a guard
action `gact m` whose precondition is the fact "the instance admits `m`", and `Dfam` is `Dall`
with a guard task in every method body (`HTN.GuardTask.guardMethod`).  The instance carries the
word as a set `Gw` of guard facts in its initial state.

> `HTN.GuardTask.solvable_methodGuard_resplit_iff` — the guarded family problem, over the
> instance enlarged by `Gw`, is solvable exactly when the original word problem is.

The proof is in three steps:

* a plan of the family domain can only use methods the instance admits, because the guard fact
  of any other one is never in a reachable state
  (`HTN.GuardTask.prec_mem_of_seqApplicable`, then `HTN.Taint.netYield_of_clean`);
* the admitted methods with their guard tasks may be replaced by the admitted methods without
  them (`HTN.GuardTask.solvable_guardTasks_iff`);
* the guard facts in the initial state are inert for the original domain
  (`HTN.Guard.solvable_withGuards_iff_of_guards_ok`, with an empty guard).
-/

namespace HTN

namespace GuardTask

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

/-! ### The guard facts of a reachable state are the ones the instance carries -/

/-- **The preconditions of the actions of an executable plan hold in the reachable states**, and
the guard facts of a reachable state are exactly those the initial state carries: hence a guard
fact occurring in the precondition of an action of an executable plan belongs to `Gw`. -/
theorem prec_mem_of_seqApplicable {δ : ActionModel F A} {G Gw : Set F} (hGw : Gw ⊆ G)
    (hadd : ∀ a : A, ∀ f ∈ δ.add a, f ∉ G) (hdel : ∀ a : A, ∀ f ∈ δ.del a, f ∉ G) :
    ∀ {as : List A} {s : Set F}, (∀ f ∈ s, f ∉ G) → δ.SeqApplicable as (s ∪ Gw) →
      ∀ a ∈ as, ∀ f ∈ δ.prec a, f ∈ G → f ∈ Gw := by
  intro as
  induction as with
  | nil => intro s _ _ a ha; simp at ha
  | cons b as ih =>
      intro s hs happ a ha f hf hfG
      simp only [ActionModel.SeqApplicable] at happ
      obtain ⟨happ1, happ2⟩ := happ
      rcases List.mem_cons.1 ha with rfl | ha'
      · rcases happ1 hf with h | h
        · exact absurd hfG (hs f h)
        · exact h
      · have hstep : δ.transition b (s ∪ Gw) = δ.transition b s ∪ Gw := by
          ext g
          simp only [ActionModel.transition, Set.mem_union, Set.mem_diff]
          constructor
          · rintro (⟨hgs | hgG, hgd⟩ | hadd')
            · exact Or.inl (Or.inl ⟨hgs, hgd⟩)
            · exact Or.inr hgG
            · exact Or.inl (Or.inr hadd')
          · rintro ((⟨hgs, hgd⟩ | hadd') | hgG)
            · exact Or.inl ⟨Or.inl hgs, hgd⟩
            · exact Or.inr hadd'
            · exact Or.inl ⟨Or.inr hgG, fun hd => hdel b g hd (hGw hgG)⟩
        rw [hstep] at happ2
        refine ih (s := δ.transition b s) ?_ happ2 a ha' f hf hfG
        rintro g (⟨hgs, -⟩ | hga)
        · exact hs g hgs
        · exact hadd b g hga

/-- An empty guard does not change the action model. -/
theorem withGuards_empty (δ : ActionModel F A) : Guard.withGuards δ (fun _ => ∅) = δ := by
  cases δ
  simp [Guard.withGuards]

/-! ### The re-split -/

variable {Dall Dspec Dfam : Domain F A C I} {Q : Instance F A C I} {G Gw : Set F}
variable {gid : Method I A C → I} {gact : Method I A C → A}

/-- **The method-guard re-split.**

`Dall` is the domain that offers one method per letter, `Dspec ⊆ Dall` the sub-domain of the
methods of the word, and `Dfam` is `Dall` with a guard task in every method body.  The instance
admits a method exactly when its guard fact belongs to `Gw`, the set of guard facts the instance
carries.  Under the hypotheses that the guard actions are no-ops whose preconditions are guard
facts, that no action touches a guard fact, and that neither the initial state nor the goal
mentions one, the guarded family problem over the enlarged instance is solvable exactly when the
original word problem is. -/
theorem solvable_methodGuard_resplit_iff [Infinite I]
    (hactspec : Dspec.toActionModel = Dall.toActionModel)
    (hactfam : Dfam.toActionModel = Dall.toActionModel)
    (hsub : Dspec.methods ⊆ Dall.methods)
    (hfam : ∀ m ∈ Dall.methods, guardMethod gid gact m ∈ Dfam.methods)
    (hfam' : ∀ mg ∈ Dfam.methods, ∃ m ∈ Dall.methods, mg = guardMethod gid gact m)
    (hwfm : ∀ m ∈ Dall.methods, m.subtasks.WF)
    (hfresh : ∀ m ∈ Dall.methods, gid m ∉ m.subtasks.T)
    (hguard : ∀ m ∈ Dall.methods,
      Dall.prec (gact m) ⊆ G ∧ Dall.add (gact m) = ∅ ∧ Dall.del (gact m) = ∅)
    (hgranted : ∀ m ∈ Dall.methods, (m ∈ Dspec.methods ↔ Dall.prec (gact m) ⊆ Gw))
    (hGw : Gw ⊆ G)
    (hadd : ∀ a : A, ∀ f ∈ Dall.add a, f ∉ G) (hdel : ∀ a : A, ∀ f ∈ Dall.del a, f ∉ G)
    (hprec : ∀ a : A, (Dspec.mkProblem Q).UsedAction a → ∀ f ∈ Dall.prec a, f ∉ G)
    (hinit : ∀ f ∈ Q.init, f ∉ G) (hgoal : ∀ f ∈ Q.goal, f ∉ G) (hwfI : Q.tnI.WF) :
    (Dfam.mkProblem ⟨Q.init ∪ Gw, Q.goal, Q.tnI⟩).Solvable ↔ (Dspec.mkProblem Q).Solvable := by
  classical
  set Qw : Instance F A C I := ⟨Q.init ∪ Gw, Q.goal, Q.tnI⟩ with hQw
  -- the admitted methods, with their guard tasks
  set Dspecg : Domain F A C I :=
    ⟨Dall.toActionModel, (fun m => guardMethod gid gact m) '' Dspec.methods⟩ with hDspecg
  have hmodelfam : Dfam.toActionModel = Dspecg.toActionModel := hactfam
  -- Step 1: a plan of the family domain uses only admitted methods
  have hstep1 : (Dfam.mkProblem Qw).Solvable ↔ (Dspecg.mkProblem Qw).Solvable := by
    rw [Problem.solvable_iff_netYield, Problem.solvable_iff_netYield]
    constructor
    · rintro ⟨as, hy, happ, hg⟩
      have happ' : Dall.toActionModel.SeqApplicable as (Q.init ∪ Gw) := by
        rw [← hactfam]; exact happ
      have hclean : ∀ a ∈ as, ¬ (Dall.prec a ⊆ G ∧ ¬ Dall.prec a ⊆ Gw) := by
        rintro a ha ⟨haG, hnot⟩
        exact hnot fun f hf =>
          prec_mem_of_seqApplicable hGw hadd hdel hinit happ' a ha f hf (haG hf)
      have hy' : Dspecg.NetYield Qw.tnI as := by
        refine Taint.netYield_of_clean (D := Dfam) (D' := Dspecg)
          (BadAct := fun a => Dall.prec a ⊆ G ∧ ¬ Dall.prec a ⊆ Gw) (Taint := fun _ => False)
          ⟨fun m _ hc => hc.elim⟩ ?_ hy hclean
        intro mg hmg hnot
        obtain ⟨m, hm, rfl⟩ := hfam' mg hmg
        have hmspec : m ∉ Dspec.methods := by
          intro hms
          exact hnot ⟨m, hms, rfl⟩
        refine ⟨gid m, ?_, Or.inl ⟨gact m, ?_, (hguard m hm).1, ?_⟩⟩
        · simp [guardMethod, addTask_T]
        · simp [guardMethod, addTask_α_self]
        · intro hcon
          exact hmspec ((hgranted m hm).2 hcon)
      refine ⟨as, hy', ?_, ?_⟩
      · show Dspecg.toActionModel.SeqApplicable as (Q.init ∪ Gw)
        exact happ'
      · show (Dspecg.mkProblem Qw).GoalState
          (Dspecg.toActionModel.transitionSeq as (Q.init ∪ Gw))
        rw [show Dspecg.toActionModel = Dall.toActionModel from rfl, ← hactfam]
        exact hg
    · rintro ⟨as, hy, happ, hg⟩
      have hsub' : Dspecg.methods ⊆ Dfam.methods := by
        rintro mg ⟨m, hm, rfl⟩
        exact hfam m (hsub hm)
      refine ⟨as, Taint.netYield_mono hsub' hy, ?_, ?_⟩
      · show Dfam.toActionModel.SeqApplicable as (Q.init ∪ Gw)
        rw [hactfam]
        exact happ
      · show (Dfam.mkProblem Qw).GoalState
          (Dfam.toActionModel.transitionSeq as (Q.init ∪ Gw))
        rw [hactfam]
        exact hg
  -- Step 2: the guard tasks of the admitted methods change nothing
  have hstep2 : (Dspecg.mkProblem Qw).Solvable ↔ (Dspec.mkProblem Qw).Solvable := by
    refine solvable_guardTasks_iff (G := Gw) (gid := gid) (gact := gact) hactspec.symm ?_ ?_ ?_ ?_
      ?_ ?_ ?_ hwfI
    · intro m hm
      exact ⟨m, hm, rfl⟩
    · rintro mg ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · intro m hm
      exact hwfm m (hsub hm)
    · intro m hm
      exact hfresh m (hsub hm)
    · intro m hm
      have hmall : m ∈ Dall.methods := hsub hm
      refine ⟨?_, ?_, ?_⟩
      · rw [show Dspec.prec = Dall.prec from by rw [hactspec]]
        exact (hgranted m hmall).1 hm
      · rw [show Dspec.add = Dall.add from by rw [hactspec]]
        exact (hguard m hmall).2.1
      · rw [show Dspec.del = Dall.del from by rw [hactspec]]
        exact (hguard m hmall).2.2
    · intro a f hf hcon
      exact hdel a f (by rwa [show Dspec.del = Dall.del from by rw [hactspec]] at hcon) (hGw hf)
    · exact fun f hf => Or.inr hf
  -- Step 3: the guard facts are inert for the original domain
  have hstep3 : (Dspec.mkProblem Qw).Solvable ↔ (Dspec.mkProblem Q).Solvable := by
    have heq : Guard.guardedProblem (Dspec.mkProblem Q) (fun _ => ∅) Gw = Dspec.mkProblem Qw := by
      simp [Guard.guardedProblem, Domain.mkProblem, withGuards_empty, hQw]
    have hprec' : Dspec.prec = Dall.prec := by rw [hactspec]
    have hadd' : Dspec.add = Dall.add := by rw [hactspec]
    have hdel' : Dspec.del = Dall.del := by rw [hactspec]
    have hstat : Guard.StaticGuards (Dspec.mkProblem Q).toActionModel
        (Dspec.mkProblem Q).UsedAction G (fun _ => ∅) := by
      refine ⟨fun _ => by simp, ?_, ?_, ?_⟩
      · intro a hu f hf
        exact hprec a hu f (hprec' ▸ hf)
      · intro a _ f hf
        exact hadd a f (hadd' ▸ hf)
      · intro a _ f hf
        exact hdel a f (hdel' ▸ hf)
    have := Guard.solvable_withGuards_iff_of_guards_ok (P := Dspec.mkProblem Q) (Gw := Gw)
      hstat hGw hinit hgoal (fun as _ a _ => by simp)
    rw [heq] at this
    exact this
  exact (hstep1.trans hstep2).trans hstep3

end GuardTask

end HTN
