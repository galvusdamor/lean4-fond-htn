import HtnPlanning.Interleave.GridYield
/-!
# Splitting a chain initial task network into a prefix and a rest

Every *gadget* that has to run before (or after) the rest of a planning problem is a chain of
tasks put in front of (behind) the initial task network: the ordering constraints of the chain
are inherited by every decomposition, so the actions of the gadget are executed before (after)
all others.  This file proves the corresponding decomposition of solvability, for a domain all
of whose method bodies are grids — the shape of every compiled domain in this development:

`HTN.Problem.solvable_seq_append_iff`

    tn_I = seq (xs ++ ys)  →
      P.Solvable ↔ ∃ as, ChainYield xs as ∧ SeqApplicable as P.init ∧
                        (P with init := transitionSeq as P.init, tnI := seq ys).Solvable

so a prefix chain `xs` acts exactly as a nondeterministic *state transformer*: the problem that
remains is the original one, started in the state the prefix reached.  The underlying statement,
for an arbitrary domain and an arbitrary *sequential composition* of task networks, is
`HTN.Problem.solvable_isSeries_iff`.

The proof is the refinement calculus of `HtnPlanning/Interleave/NetYield.lean` and
`HtnPlanning/Interleave/GridYield.lean`: solutions are refinements of the initial task network
(`HTN.Problem.solvable_iff_netYield`), refinements of a chain are the syntactic chain
refinements (`HTN.Domain.netYield_seq_iff`), and those of a concatenation split
(`HTN.Domain.chainYield_append_iff`).
-/

namespace HTN

namespace Domain

universe u v w

variable {F : Type u} {A : Type v} {C : Type w} [Inhabited A] {D : Domain F A C (ℕ × ℕ)}

/-- **A choice task**: the methods of the compound task `c` are exactly the ones executing a
single action from the list `opts c`.  This is the shape of every gadget task in this
development: a task whose only job is to pick one of finitely many actions. -/
def IsChoiceTask (D : Domain F A C (ℕ × ℕ)) (opts : C → List A) (c : C) : Prop :=
  ∀ ls, D.GridBody c ls ↔ ∃ a ∈ opts c, ls = [[Sum.inl a]]

/-- A single choice task refines exactly into the one-element sequences of its options. -/
theorem chainYield_choiceTask {opts : C → List A} {c : C} (h : D.IsChoiceTask opts c)
    {as : List A} : D.ChainYield [Sum.inr c] as ↔ ∃ a ∈ opts c, as = [a] := by
  rw [chainYield_singleton_inr_iff]
  constructor
  · rintro ⟨ls, hb, hy⟩
    obtain ⟨a, ha, rfl⟩ := (h ls).1 hb
    rw [gridYield_singleton_iff, chainYield_cons_inl_iff] at hy
    obtain ⟨bs, rfl, hbs⟩ := hy
    rw [chainYield_nil_iff] at hbs
    exact ⟨a, ha, by simp [hbs]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨[[Sum.inl a]], (h _).2 ⟨a, ha, rfl⟩, by
      rw [gridYield_singleton_iff, chainYield_cons_inl_iff]
      exact ⟨[], rfl, chainYield_nil_iff.2 rfl⟩⟩

/-- **A chain of choice tasks refines exactly into the sequences of chosen actions.** -/
theorem chainYield_map_inr_iff {opts : C → List A} {cs : List C}
    (h : ∀ c ∈ cs, D.IsChoiceTask opts c) {as : List A} :
    D.ChainYield (cs.map Sum.inr) as ↔ List.Forall₂ (fun c a => a ∈ opts c) cs as := by
  induction cs generalizing as with
  | nil => simp [List.forall₂_nil_left_iff]
  | cons c cs ih =>
    rw [List.map_cons, chainYield_cons_inr_iff]
    constructor
    · rintro ⟨ls, bs, rest, hb, hy, hrest, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (h c (by simp) ls).1 hb
      rw [gridYield_singleton_iff, chainYield_cons_inl_iff] at hy
      obtain ⟨bs', rfl, hbs⟩ := hy
      rw [chainYield_nil_iff] at hbs
      subst hbs
      exact List.Forall₂.cons ha ((ih fun c' hc' => h c' (by simp [hc'])).1 hrest)
    · intro hf
      obtain ⟨a, as', ha, hrest, rfl⟩ :
          ∃ a as', a ∈ opts c ∧ List.Forall₂ (fun c a => a ∈ opts c) cs as' ∧ as = a :: as' := by
        cases hf with
        | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
      refine ⟨[[Sum.inl a]], [a], as', (h c (by simp) _).2 ⟨a, ha, rfl⟩, ?_, ?_, by simp⟩
      · rw [gridYield_singleton_iff, chainYield_cons_inl_iff]
        exact ⟨[], rfl, chainYield_nil_iff.2 rfl⟩
      · exact (ih fun c' hc' => h c' (by simp [hc'])).2 hrest

/-- Combining a `Forall₂` with a pointwise property of the second list. -/
theorem forall₂_and_mem_iff {α β : Type*} {R : α → β → Prop} {p : β → Prop} {l : List α}
    {l' : List β} :
    (List.Forall₂ R l l' ∧ ∀ b ∈ l', p b) ↔ List.Forall₂ (fun a b => R a b ∧ p b) l l' := by
  constructor
  · rintro ⟨h, hp⟩
    induction h with
    | nil => exact List.Forall₂.nil
    | @cons a b l l' hab _ ih =>
      exact List.Forall₂.cons ⟨hab, hp b (by simp)⟩ (ih fun x hx => hp x (by simp [hx]))
  · intro h
    induction h with
    | nil => exact ⟨List.Forall₂.nil, by simp⟩
    | @cons a b l l' hab _ ih =>
      exact ⟨List.Forall₂.cons hab.1 ih.1, by
        rintro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact hab.2
        · exact ih.2 x hx'⟩

/-- A list of choices exists exactly when each entry can be chosen. -/
theorem exists_forall₂_iff {α β : Type*} {R : α → β → Prop} {l : List α} :
    (∃ l', List.Forall₂ R l l') ↔ ∀ a ∈ l, ∃ b, R a b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    constructor
    · rintro ⟨l', hl⟩
      obtain ⟨b, l'', hab, hrest, rfl⟩ :
          ∃ b l'', R a b ∧ List.Forall₂ R l l'' ∧ l' = b :: l'' := by
        cases hl with
        | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨b, hab⟩
      · exact ih.1 ⟨l'', hrest⟩ x hx'
    · intro h
      obtain ⟨b, hb⟩ := h a (by simp)
      obtain ⟨l', hl'⟩ := ih.2 fun x hx => h x (by simp [hx])
      exact ⟨b :: l', List.Forall₂.cons hb hl'⟩

end Domain

namespace Problem

universe u v w

variable {F : Type u} {A : Type v} {C : Type w} {I : Type*}

/-- The same planning problem, started in the state `s` with the initial task network `tn`. -/
def restart (P : Problem F A C I) (s : Set F) (tn : TaskNetwork I A C) : Problem F A C I :=
  { P with init := s, tnI := tn }

@[simp] lemma restart_init (P : Problem F A C I) (s : Set F)
    (tn : TaskNetwork I A C) : (P.restart s tn).init = s := rfl

@[simp] lemma restart_goal (P : Problem F A C I) (s : Set F)
    (tn : TaskNetwork I A C) : (P.restart s tn).goal = P.goal := rfl

@[simp] lemma restart_tnI (P : Problem F A C I) (s : Set F)
    (tn : TaskNetwork I A C) : (P.restart s tn).tnI = tn := rfl

@[simp] lemma restart_methods (P : Problem F A C I) (s : Set F)
    (tn : TaskNetwork I A C) : (P.restart s tn).methods = P.methods := rfl

@[simp] lemma restart_toActionModel (P : Problem F A C I) (s : Set F)
    (tn : TaskNetwork I A C) : (P.restart s tn).toActionModel = P.toActionModel := rfl

@[simp] lemma restart_domain (P : Problem F A C I) (s : Set F)
    (tn : TaskNetwork I A C) : (P.restart s tn).domain = P.domain := rfl

@[simp] lemma domain_methods (P : Problem F A C I) : P.domain.methods = P.methods := rfl

@[simp] lemma domain_toActionModel (P : Problem F A C I) :
    P.domain.toActionModel = P.toActionModel := rfl

/-- **A sequential composition of the initial task network splits solvability.**  If the initial
task network is `tn₁ ; tn₂`, then the problem is solvable exactly when `tn₁` refines into an
action sequence that is executable in the initial state and leaves a state from which the
problem with the initial task network `tn₂` is solvable.  No hypothesis on the domain is needed:
the ordering constraints of a sequential composition are inherited by every decomposition. -/
theorem solvable_isSeries_iff [DecidableEq I] [Infinite I] {P : Problem F A C I}
    {tn₁ tn₂ : TaskNetwork I A C} (h : TaskNetwork.IsSeries P.tnI tn₁ tn₂) (hw₁ : tn₁.WF)
    (hw₂ : tn₂.WF) :
    P.Solvable ↔ ∃ as, P.domain.NetYield tn₁ as ∧ P.SeqApplicable as P.init ∧
      (P.restart (P.transitionSeq as P.init) tn₂).Solvable := by
  rw [solvable_iff_netYield]
  constructor
  · rintro ⟨cs, ⟨n, hy⟩, happ, hgoal⟩
    obtain ⟨n₁, n₂, as, bs, -, rfl, hy₁, hy₂⟩ :=
      (Domain.netYieldN_isSeries_iff (D := P.domain) h hw₁ hw₂).1 hy
    refine ⟨as, ⟨n₁, hy₁⟩, ((ActionModel.seqApplicable_append _ _ _ _).1 happ).1, ?_⟩
    rw [solvable_iff_netYield]
    refine ⟨bs, ⟨n₂, hy₂⟩, ((ActionModel.seqApplicable_append _ _ _ _).1 happ).2, ?_⟩
    show P.goal ⊆ _
    rw [restart_toActionModel, restart_init]
    simpa [ActionModel.transitionSeq_append] using hgoal
  · rintro ⟨as, ⟨n₁, hy₁⟩, happ, hsolv⟩
    rw [solvable_iff_netYield] at hsolv
    obtain ⟨bs, ⟨n₂, hy₂⟩, happ', hgoal⟩ := hsolv
    refine ⟨as ++ bs, ⟨n₁ + n₂, (Domain.netYieldN_isSeries_iff (D := P.domain) h hw₁ hw₂).2
      ⟨n₁, n₂, as, bs, rfl, rfl, hy₁, hy₂⟩⟩, ?_, ?_⟩
    · rw [ActionModel.seqApplicable_append]
      exact ⟨happ, happ'⟩
    · show P.goal ⊆ _
      rw [ActionModel.transitionSeq_append]
      exact hgoal

/-- **A prefix chain of the initial task network is a state transformer.**  If the initial task
network is the chain `xs ++ ys`, then the problem is solvable exactly when the prefix `xs`
refines into an action sequence that is executable in the initial state and leaves a state from
which the problem with the initial task network `ys` is solvable. -/
theorem solvable_seq_append_iff [Inhabited A] {P : Problem F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ P.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {xs ys : List (A ⊕ C)} (htn : P.tnI = TaskNetwork.seq (xs ++ ys)) :
    P.Solvable ↔ ∃ as, P.domain.ChainYield xs as ∧ P.SeqApplicable as P.init ∧
      (P.restart (P.transitionSeq as P.init) (TaskNetwork.seq ys)).Solvable := by
  have hgrid' : ∀ m ∈ P.domain.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls := hgrid
  rw [solvable_iff_netYield, htn]
  simp only [Domain.netYield_seq_iff hgrid', Domain.chainYield_append_iff]
  constructor
  · rintro ⟨cs, ⟨as, bs, rfl, hxs, hys⟩, happ, hgoal⟩
    refine ⟨as, hxs, ((ActionModel.seqApplicable_append _ _ _ _).1 happ).1, ?_⟩
    rw [solvable_iff_netYield]
    refine ⟨bs, ?_, ?_, ?_⟩
    · simpa [Domain.netYield_seq_iff hgrid'] using hys
    · exact ((ActionModel.seqApplicable_append _ _ _ _).1 happ).2
    · show P.goal ⊆ _
      rw [restart_toActionModel, restart_init]
      simpa [ActionModel.transitionSeq_append] using hgoal
  · rintro ⟨as, hxs, happ, hsolv⟩
    rw [solvable_iff_netYield] at hsolv
    obtain ⟨bs, hys, happ', hgoal⟩ := hsolv
    refine ⟨as ++ bs, ⟨as, bs, rfl, hxs, ?_⟩, ?_, ?_⟩
    · simpa [Domain.netYield_seq_iff hgrid'] using hys
    · rw [ActionModel.seqApplicable_append]
      exact ⟨happ, happ'⟩
    · show P.goal ⊆ _
      rw [ActionModel.transitionSeq_append]
      exact hgoal

/-- **A prefix of choice tasks.**  The gadget tasks `cs`, put in front of the initial task
network, contribute exactly one action each, chosen from their options. -/
theorem solvable_choicePrefix_iff [Inhabited A] {P : Problem F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ P.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls) {opts : C → List A}
    {cs : List C} {ys : List (A ⊕ C)} (hc : ∀ c ∈ cs, P.domain.IsChoiceTask opts c)
    (htn : P.tnI = TaskNetwork.seq (cs.map Sum.inr ++ ys)) :
    P.Solvable ↔ ∃ as, List.Forall₂ (fun c a => a ∈ opts c) cs as ∧ P.SeqApplicable as P.init ∧
      (P.restart (P.transitionSeq as P.init) (TaskNetwork.seq ys)).Solvable := by
  rw [solvable_seq_append_iff hgrid htn]
  exact exists_congr fun as => and_congr_left' (Domain.chainYield_map_inr_iff hc)

/-- **A chain of tests.**  If the whole initial task network is a chain of choice tasks all of
whose options are *effect-free* actions, then the problem is solvable exactly when the goal
already holds initially and each test has an option whose precondition holds — the gadget checks
a conjunction of disjunctions of preconditions and changes nothing. -/
theorem solvable_testChain_iff [Inhabited A] {P : Problem F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ P.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls) {opts : C → List A}
    {cs : List C} (hc : ∀ c ∈ cs, P.domain.IsChoiceTask opts c)
    (hno : ∀ c ∈ cs, ∀ a ∈ opts c, P.add a = ∅ ∧ P.del a = ∅)
    (htn : P.tnI = TaskNetwork.seq (cs.map Sum.inr)) :
    P.Solvable ↔ P.goal ⊆ P.init ∧ ∀ c ∈ cs, ∃ a ∈ opts c, P.prec a ⊆ P.init := by
  classical
  -- an effect-free plan of chosen actions leaves the state unchanged
  have hstay : ∀ (l : List C) (as : List A),
      (∀ c ∈ l, ∀ a ∈ opts c, P.add a = ∅ ∧ P.del a = ∅) →
      List.Forall₂ (fun c a => a ∈ opts c) l as →
      P.transitionSeq as P.init = P.init ∧
        (P.SeqApplicable as P.init ↔ ∀ a ∈ as, P.prec a ⊆ P.init) := by
    intro l as hno' h
    induction h with
    | nil => simp [ActionModel.transitionSeq, ActionModel.SeqApplicable]
    | @cons c a l l' hca hrest ih =>
      have hne := hno' c (by simp) a hca
      have hstep : P.transition a P.init = P.init := by
        simp [ActionModel.transition, hne.1, hne.2]
      have ih' := ih (fun c' hc' => hno' c' (by simp [hc']))
      rw [ActionModel.transitionSeq_cons, hstep]
      refine ⟨ih'.1, ?_⟩
      rw [ActionModel.seqApplicable_cons, hstep, ih'.2]
      constructor
      · rintro ⟨h1, h2⟩ x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact h1
        · exact h2 x hx'
      · intro h
        exact ⟨h a (by simp), fun x hx => h x (by simp [hx])⟩
  rw [solvable_choicePrefix_iff hgrid hc (ys := []) (by simpa using htn)]
  constructor
  · rintro ⟨as, hf, happ, hsolv⟩
    obtain ⟨hstate, happ'⟩ := hstay cs as hno hf
    have hgoal : P.goal ⊆ P.init := by
      obtain ⟨bs, hy, -, hg⟩ := solvable_iff_netYield.1 hsolv
      have hbs : bs = [] := by
        have : P.domain.ChainYield [] bs := by
          simpa [Domain.netYield_seq_iff (D := P.domain) hgrid] using hy
        simpa using Domain.chainYield_nil_iff.1 this
      subst hbs
      simpa [hstate, ActionModel.transitionSeq] using hg
    refine ⟨hgoal, ?_⟩
    have := (Domain.forall₂_and_mem_iff (p := fun a => P.prec a ⊆ P.init)).1
      ⟨hf, (happ'.1 happ)⟩
    intro c hcs
    obtain ⟨a, ha⟩ := (Domain.exists_forall₂_iff
      (R := fun c a => a ∈ opts c ∧ P.prec a ⊆ P.init)).1 ⟨as, this⟩ c hcs
    exact ⟨a, ha.1, ha.2⟩
  · rintro ⟨hgoal, hch⟩
    obtain ⟨as, hf⟩ := (Domain.exists_forall₂_iff
      (R := fun c a => a ∈ opts c ∧ P.prec a ⊆ P.init)).2
      (fun c hc' => (hch c hc').imp fun a ha => ⟨ha.1, ha.2⟩)
    obtain ⟨hf1, hf2⟩ := (Domain.forall₂_and_mem_iff (p := fun a => P.prec a ⊆ P.init)).2 hf
    obtain ⟨hstate, happ'⟩ := hstay cs as hno hf1
    refine ⟨as, hf1, happ'.2 hf2, ?_⟩
    rw [solvable_iff_netYield]
    refine ⟨[], ?_, ?_, ?_⟩
    · simp [Domain.netYield_seq_iff (D := P.domain) hgrid]
    · simp [ActionModel.SeqApplicable]
    · show P.goal ⊆ _
      simpa [hstate, ActionModel.transitionSeq] using hgoal

end Problem

end HTN
