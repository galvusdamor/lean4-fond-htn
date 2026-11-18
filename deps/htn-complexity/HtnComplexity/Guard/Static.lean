import HtnPlanning.Core.Transfer
import HtnPlanning.Interleave.NetYield
/-!
# Static guards: moving a parameter out of the domain and into the instance

A *hardness family* in the sense of `HTN.Syn.Coded.HardFamilyPT` consists of a domain
description per input **length** and an instance description per input **word**: the domain is
not allowed to see the word.  Constructions in the literature — Theorem 4.3.7 of Bercher et al.
among them — are usually written the other way round, with the word baked into the domain (its
methods write the input onto the simulated tape).  Turning such a construction into a family
means *re-splitting* it: the domain keeps one method per position **and per symbol**, and the
instance says which of them may be used, by carrying a set of *static facts* in its initial
state.

This file provides the semantic tool for that step, once and for all.

## The setting

Fix an action model `δ`, a set `G` of **guard facts** and an assignment `g` of a set of guard
facts to every action — the guard of that action.  `HTN.Guard.withGuards δ g` is the action
model that asks, in addition to the original precondition of `a`, for the facts `g a`.  The
guard facts are *static*: no action that the problem can ever execute adds one, deletes one, or
has one in its original precondition (`HTN.Guard.StaticGuards`).

Under those hypotheses a plan behaves in the guarded problem with the enlarged initial state
`s₀ ∪ Gw` exactly as it behaves in the original problem with `s₀`, except that it may only use
actions whose guard is contained in `Gw`:

* `HTN.Guard.transitionSeq_union` — the state reached is the original one, with `Gw` added;
* `HTN.Guard.seqApplicable_withGuards_iff` — applicability splits into the original
  applicability and the guard condition;
* `HTN.Guard.solvable_withGuards_iff` — hence solvability of the guarded problem is solvability
  of the original one *restricted to the plans the guards admit*.

Decomposition — and with it `HTN.Domain.NetYield` — does not look at the action model at all, so
nothing has to be re-proved about the hierarchy: the guards act on the **executability** half of
the solution criteria only.  This is what makes the re-split cheap: the correctness proof of the
original construction is reused verbatim, and the guards are analysed separately.

## Main results

* `HTN.Guard.withGuards`, `HTN.Guard.Problem.withGuards` — the guarded action model and the
  guarded problem;
* `HTN.Guard.StaticGuards` — the hypotheses: the guard facts are untouched by the actions;
* `HTN.Guard.solvable_withGuards_iff` — the characterisation of solvability of the guarded
  problem;
* `HTN.Guard.solvable_withGuards_iff_of_guards_ok` — its corollary when every plan of the
  original problem satisfies the guard condition anyway: then the guards change nothing, which
  is the half of the re-split that reuses the original correctness theorem.
-/

namespace HTN

namespace Guard

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### The guarded action model -/

/-- **The guarded action model**: every action keeps its effects and acquires the extra
precondition `g a`. -/
def withGuards (δ : ActionModel F A) (g : A → Set F) : ActionModel F A where
  prec a := δ.prec a ∪ g a
  add := δ.add
  del := δ.del

@[simp] lemma withGuards_prec (δ : ActionModel F A) (g : A → Set F) (a : A) :
    (withGuards δ g).prec a = δ.prec a ∪ g a := rfl

@[simp] lemma withGuards_add (δ : ActionModel F A) (g : A → Set F) (a : A) :
    (withGuards δ g).add a = δ.add a := rfl

@[simp] lemma withGuards_del (δ : ActionModel F A) (g : A → Set F) (a : A) :
    (withGuards δ g).del a = δ.del a := rfl

@[simp] lemma withGuards_transition (δ : ActionModel F A) (g : A → Set F) (a : A) (s : Set F) :
    (withGuards δ g).transition a s = δ.transition a s := rfl

@[simp] lemma withGuards_transitionSeq (δ : ActionModel F A) (g : A → Set F) (as : List A)
    (s : Set F) : (withGuards δ g).transitionSeq as s = δ.transitionSeq as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [ActionModel.transitionSeq, ih]

/-- **The guard facts are static.**  For every action the problem can execute — `Used a` — the
original precondition, the add list and the delete list avoid the guard facts `G`, and the guard
of an action consists of guard facts.  Thus the guard facts of a state are exactly those it
started with, and they can neither help nor hinder the original preconditions. -/
structure StaticGuards (δ : ActionModel F A) (Used : A → Prop) (G : Set F)
    (g : A → Set F) : Prop where
  /-- The guard of an action consists of guard facts. -/
  guard_mem : ∀ a, g a ⊆ G
  /-- No guard fact is an original precondition of an action that can be executed. -/
  prec_disj : ∀ a, Used a → ∀ f ∈ δ.prec a, f ∉ G
  /-- No executable action adds a guard fact. -/
  add_disj : ∀ a, Used a → ∀ f ∈ δ.add a, f ∉ G
  /-- No executable action deletes a guard fact. -/
  del_disj : ∀ a, Used a → ∀ f ∈ δ.del a, f ∉ G

variable {δ : ActionModel F A} {Used : A → Prop} {G : Set F} {g : A → Set F}

/-- **The guard facts travel unchanged along a plan.**  If the state `s` avoids the guard facts
and `Gw ⊆ G`, then executing a plan of executable actions from `s ∪ Gw` reaches the state it
reaches from `s`, with `Gw` added. -/
theorem transitionSeq_union (h : StaticGuards δ Used G g) {Gw : Set F} (hGw : Gw ⊆ G)
    {as : List A} (hused : ∀ a ∈ as, Used a) (s : Set F) :
    δ.transitionSeq as (s ∪ Gw) = δ.transitionSeq as s ∪ Gw := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      have hstep : δ.transition a (s ∪ Gw) = δ.transition a s ∪ Gw := by
        have hdel : ∀ f ∈ Gw, f ∉ δ.del a := by
          intro f hf hmem
          exact h.del_disj a (hused a (by simp)) f hmem (hGw hf)
        ext f
        simp only [ActionModel.transition, Set.mem_union, Set.mem_diff]
        constructor
        · rintro ((⟨hfs | hfG, hfd⟩) | hadd)
          · exact Or.inl (Or.inl ⟨hfs, hfd⟩)
          · exact Or.inr hfG
          · exact Or.inl (Or.inr hadd)
        · rintro ((⟨hfs, hfd⟩ | hadd) | hfG)
          · exact Or.inl ⟨Or.inl hfs, hfd⟩
          · exact Or.inr hadd
          · exact Or.inl ⟨Or.inr hfG, hdel f hfG⟩
      simp only [ActionModel.transitionSeq, hstep]
      exact ih (fun b hb => hused b (by simp [hb])) _

/-- **The guard facts of a reachable state are exactly the ones the plan started with.** -/
theorem transitionSeq_disjoint (h : StaticGuards δ Used G g) {as : List A}
    (hused : ∀ a ∈ as, Used a) {s : Set F} (hs : ∀ f ∈ s, f ∉ G) :
    ∀ f ∈ δ.transitionSeq as s, f ∉ G := by
  induction as generalizing s with
  | nil => exact hs
  | cons a as ih =>
      refine ih (fun b hb => hused b (by simp [hb])) ?_
      rintro f (⟨hfs, -⟩ | hadd)
      · exact hs f hfs
      · exact h.add_disj a (hused a (by simp)) f hadd

/-- **Applicability in the guarded problem splits.**  A plan of executable actions is applicable
in `s ∪ Gw` for the guarded action model exactly when it is applicable in `s` for the original
one and every one of its actions has its guard inside `Gw`. -/
theorem seqApplicable_withGuards_iff (h : StaticGuards δ Used G g) {Gw : Set F} (hGw : Gw ⊆ G)
    {as : List A} (hused : ∀ a ∈ as, Used a) {s : Set F} (hs : ∀ f ∈ s, f ∉ G) :
    (withGuards δ g).SeqApplicable as (s ∪ Gw) ↔
      δ.SeqApplicable as s ∧ ∀ a ∈ as, g a ⊆ Gw := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
      have hua : Used a := hused a (by simp)
      have hused' : ∀ b ∈ as, Used b := fun b hb => hused b (by simp [hb])
      have hstep : δ.transition a (s ∪ Gw) = δ.transition a s ∪ Gw := by
        have := transitionSeq_union h hGw (as := [a]) (by simpa using hua) s
        simpa [ActionModel.transitionSeq] using this
      have hs' : ∀ f ∈ δ.transition a s, f ∉ G := by
        have := transitionSeq_disjoint h (as := [a]) (by simpa using hua) hs
        simpa [ActionModel.transitionSeq] using this
      have happ : (withGuards δ g).Applicable a (s ∪ Gw) ↔
          δ.Applicable a s ∧ g a ⊆ Gw := by
        constructor
        · intro hap
          constructor
          · intro f hf
            rcases hap (Or.inl hf) with hfs | hfG
            · exact hfs
            · exact absurd (hGw hfG) (h.prec_disj a hua f hf)
          · intro f hf
            rcases hap (Or.inr hf) with hfs | hfG
            · exact absurd (h.guard_mem a hf) (hs f hfs)
            · exact hfG
        · rintro ⟨hap, hg⟩ f (hf | hf)
          · exact Or.inl (hap hf)
          · exact Or.inr (hg hf)
      rw [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_cons, happ,
        withGuards_transition, hstep, ih hused' hs']
      constructor
      · rintro ⟨⟨hap, hga⟩, happ', hgs⟩
        refine ⟨⟨hap, happ'⟩, ?_⟩
        rintro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact hga
        · exact hgs b hb
      · rintro ⟨⟨hap, happ'⟩, hgs⟩
        exact ⟨⟨hap, hgs a (by simp)⟩, happ', fun b hb => hgs b (by simp [hb])⟩

/-! ### The guarded problem -/

/-- **The guarded problem**: the same hierarchy, the guarded action model, and the guard facts
`Gw` added to the initial state.  This is the shape of a re-split construction: the guards and
`Gw` are what the *instance* contributes, the rest is the domain. -/
def guardedProblem (P : Problem F A C I) (g : A → Set F) (Gw : Set F) : Problem F A C I where
  toActionModel := Guard.withGuards P.toActionModel g
  methods := P.methods
  init := P.init ∪ Gw
  goal := P.goal
  tnI := P.tnI

@[simp] lemma guardedProblem_methods (P : Problem F A C I) (g : A → Set F) (Gw : Set F) :
    (guardedProblem P g Gw).methods = P.methods := rfl

@[simp] lemma guardedProblem_tnI (P : Problem F A C I) (g : A → Set F) (Gw : Set F) :
    (guardedProblem P g Gw).tnI = P.tnI := rfl

@[simp] lemma guardedProblem_init (P : Problem F A C I) (g : A → Set F) (Gw : Set F) :
    (guardedProblem P g Gw).init = P.init ∪ Gw := rfl

@[simp] lemma guardedProblem_goal (P : Problem F A C I) (g : A → Set F) (Gw : Set F) :
    (guardedProblem P g Gw).goal = P.goal := rfl

theorem seqApplicable_guardedProblem_iff {P : Problem F A C I} {Gw : Set F}
    (h : StaticGuards P.toActionModel P.UsedAction G g) (hGw : Gw ⊆ G)
    (hinit : ∀ f ∈ P.init, f ∉ G) {as : List A} (hused : ∀ a ∈ as, P.UsedAction a) :
    (guardedProblem P g Gw).SeqApplicable as (guardedProblem P g Gw).init ↔
      P.SeqApplicable as P.init ∧ ∀ a ∈ as, g a ⊆ Gw :=
  seqApplicable_withGuards_iff h hGw hused hinit

/-- The state a plan reaches in the guarded problem is the one it reaches in the original
problem, with the guard facts added. -/
theorem transitionSeq_guardedProblem {P : Problem F A C I} {Gw : Set F}
    (h : StaticGuards P.toActionModel P.UsedAction G g) (hGw : Gw ⊆ G)
    {as : List A} (hused : ∀ a ∈ as, P.UsedAction a) :
    (guardedProblem P g Gw).transitionSeq as (guardedProblem P g Gw).init
      = P.transitionSeq as P.init ∪ Gw := by
  have hrfl : (guardedProblem P g Gw).transitionSeq as (guardedProblem P g Gw).init
      = P.toActionModel.transitionSeq as (P.init ∪ Gw) :=
    withGuards_transitionSeq P.toActionModel g as (P.init ∪ Gw)
  rw [hrfl]
  exact transitionSeq_union h hGw hused P.init

/-! ### Every action of a plan is used -/

variable [DecidableEq I]

/-- **The actions of a refinement of the initial task network are used by the problem.** -/
theorem usedAction_of_netYield {P : Problem F A C I} {as : List A}
    (h : P.domain.NetYield P.tnI as) : ∀ a ∈ as, P.UsedAction a := by
  obtain ⟨tn, hdec, -, l, hlin, hseq⟩ := Domain.netYield_iff.1 h
  have hused := HTN.Problem.actionsUsed_of_decomposesTo (P := P) hdec
  intro a ha
  have hmem : (Sum.inl a : A ⊕ C) ∈ l.map tn.α := by
    rw [hseq]
    exact List.mem_map_of_mem ha
  obtain ⟨t, htl, hα⟩ := List.mem_map.1 hmem
  exact hused t ((hlin.2.1 t).1 htl) a hα

/-! ### Solvability of the guarded problem -/

/-- **Solvability of the guarded problem.**  The guarded problem, whose initial state carries
the guard facts `Gw`, is solvable exactly when the original problem has a plan all of whose
actions are admitted by `Gw`.

Read in the intended application: the domain offers one method per position and per symbol of
the input alphabet, the instance carries the facts `Gw` that say which symbol belongs at which
position, and a plan of the guarded problem is a plan of the original construction for *that*
input. -/
theorem solvable_withGuards_iff {P : Problem F A C I} {Gw : Set F}
    (h : StaticGuards P.toActionModel P.UsedAction G g) (hGw : Gw ⊆ G)
    (hinit : ∀ f ∈ P.init, f ∉ G) (hgoal : ∀ f ∈ P.goal, f ∉ G) :
    (guardedProblem P g Gw).Solvable ↔
      ∃ as : List A, P.domain.NetYield P.tnI as ∧ P.SeqApplicable as P.init ∧
        P.GoalState (P.transitionSeq as P.init) ∧ ∀ a ∈ as, g a ⊆ Gw := by
  rw [Problem.solvable_iff_netYield]
  refine exists_congr fun as => ?_
  constructor
  · rintro ⟨hy, happ, hg⟩
    have hy' : P.domain.NetYield P.tnI as := hy
    have hused := usedAction_of_netYield hy'
    rw [seqApplicable_guardedProblem_iff h hGw hinit hused] at happ
    rw [transitionSeq_guardedProblem h hGw hused] at hg
    refine ⟨hy', happ.1, ?_, happ.2⟩
    intro f hf
    rcases hg hf with hfs | hfG
    · exact hfs
    · exact absurd (hGw hfG) (hgoal f hf)
  · rintro ⟨hy, happ, hgoalst, hgs⟩
    have hused := usedAction_of_netYield hy
    refine ⟨hy, ?_, ?_⟩
    · rw [seqApplicable_guardedProblem_iff h hGw hinit hused]
      exact ⟨happ, hgs⟩
    · rw [transitionSeq_guardedProblem h hGw hused]
      exact fun f hf => Or.inl (hgoalst hf)

/-- **When the guards are satisfied by every plan, they change nothing.**  This is the half of a
re-split that reuses the correctness theorem of the original, word-carrying construction: if
every refinement of the initial task network only uses actions admitted by `Gw`, then the
guarded problem — whose domain no longer mentions the word — is solvable exactly when the
original problem is. -/
theorem solvable_withGuards_iff_of_guards_ok {P : Problem F A C I} {Gw : Set F}
    (h : StaticGuards P.toActionModel P.UsedAction G g) (hGw : Gw ⊆ G)
    (hinit : ∀ f ∈ P.init, f ∉ G) (hgoal : ∀ f ∈ P.goal, f ∉ G)
    (hok : ∀ as : List A, P.domain.NetYield P.tnI as → ∀ a ∈ as, g a ⊆ Gw) :
    (guardedProblem P g Gw).Solvable ↔ P.Solvable := by
  rw [solvable_withGuards_iff h hGw hinit hgoal, Problem.solvable_iff_netYield]
  refine exists_congr fun as => ⟨?_, ?_⟩
  · rintro ⟨hy, happ, hg, -⟩
    exact ⟨hy, happ, hg⟩
  · rintro ⟨hy, happ, hg⟩
    exact ⟨hy, happ, hg, hok as hy⟩

end Guard

end HTN
