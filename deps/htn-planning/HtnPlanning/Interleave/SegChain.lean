import HtnPlanning.Interleave.ChainPrefix
import HtnPlanning.Core.TONormalForm
/-!
# Chains of tasks as compositions of state transformers

`HtnPlanning/Interleave/ChainPrefix.lean` shows that a *prefix* of the initial task network acts as
a nondeterministic state transformer.  This file turns that observation into a small calculus
for the **whole** initial task network, which is what a compilation that has to carry the
initial task network of the source over to the target needs: the compiled instance emits one
target task per source task, and the two chains have to compose the same way.

* `HTN.Domain.ChainReach D xs s s'` — the chain of tasks `xs` refines into an action sequence
  that is executable in `s` and reaches `s'` (the interleaving refinement relation, for a domain
  whose method bodies are grids);
* `HTN.Domain.YieldReach D xs s s'` — the same for the totally ordered refinement relation
  `HTN.Domain.YieldSeq`, which is the one available for an arbitrary totally ordered domain;
* both compose along `++` (`chainReach_append_iff`, `yieldReach_append_iff`), so a chain of
  compound tasks realises the **composite** of the per-task relations (`RelChain`);
* `HTN.Problem.solvable_chainReach_iff`, `HTN.Problem.solvable_yieldReach_iff` — solvability of a
  problem whose initial task network is such a chain;
* `HTN.exists_relChain_congr` — if the per-task relations of two problems are related by a
  simulation in both directions along a representation relation `Rep`, and the two goal
  conditions agree on represented states, then the two chains are solvable together;
* `HTN.Problem.solvable_iff_of_segSim` — **the reduction**: a compilation whose compiled instance
  emits one target task per task of the source's initial task network is correct as soon as it is
  correct *segment by segment*.  This is the generic half of a compilation of problems with an
  **unrestricted** initial task network into a class whose instances may carry a task network;
  what remains to be proved for such a compilation is the per-segment statement.
-/

namespace HTN

/-! ### The composite of a family of state relations along a list -/

/-- The composite of the relations `R c`, `c` running through a list. -/
def RelChain {F C : Type*} (R : C → Set F → Set F → Prop) : List C → Set F → Set F → Prop
  | [], s, s' => s' = s
  | c :: cs, s, s'' => ∃ s', R c s s' ∧ RelChain R cs s' s''

@[simp] theorem relChain_nil {F C : Type*} {R : C → Set F → Set F → Prop} {s s' : Set F} :
    RelChain R [] s s' ↔ s' = s := Iff.rfl

@[simp] theorem relChain_cons {F C : Type*} {R : C → Set F → Set F → Prop} {c : C} {cs : List C}
    {s s'' : Set F} :
    RelChain R (c :: cs) s s'' ↔ ∃ s', R c s s' ∧ RelChain R cs s' s'' := Iff.rfl

/-- Composing along a mapped list is composing along the list with the composed family. -/
theorem relChain_map {F C C' : Type*} (R : C' → Set F → Set F → Prop) (g : C → C')
    (cs : List C) {s s' : Set F} :
    RelChain R (cs.map g) s s' ↔ RelChain (fun c => R (g c)) cs s s' := by
  induction cs generalizing s with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, relChain_cons, ih]

/-- **Solvability transfers along a chainwise simulation.**  If the initial states are related,
each source step is matched by a target step and conversely, and the two goal conditions agree on
related states, then a chain of tasks is solvable on the source side exactly when it is on the
target side. -/
theorem exists_relChain_congr {F G C : Type*} {Rsrc : C → Set F → Set F → Prop}
    {Rtgt : C → Set G → Set G → Prop} {Rep : Set F → Set G → Prop}
    {Gsrc : Set F → Prop} {Gtgt : Set G → Prop} (cs : List C)
    (hfwd : ∀ c ∈ cs, ∀ s t s', Rep s t → Rsrc c s s' → ∃ t', Rtgt c t t' ∧ Rep s' t')
    (hbwd : ∀ c ∈ cs, ∀ s t t', Rep s t → Rtgt c t t' → ∃ s', Rsrc c s s' ∧ Rep s' t')
    (hgoal : ∀ s t, Rep s t → (Gsrc s ↔ Gtgt t))
    {s : Set F} {t : Set G} (hst : Rep s t) :
    (∃ s', RelChain Rsrc cs s s' ∧ Gsrc s') ↔ ∃ t', RelChain Rtgt cs t t' ∧ Gtgt t' := by
  induction cs generalizing s t with
  | nil =>
    constructor
    · rintro ⟨s', hs', hg⟩
      exact ⟨t, rfl, (hgoal s t hst).1 (hs' ▸ hg)⟩
    · rintro ⟨t', ht', hg⟩
      exact ⟨s, rfl, (hgoal s t hst).2 (ht' ▸ hg)⟩
  | cons c cs ih =>
    have ihmem : ∀ {s : Set F} {t : Set G}, Rep s t →
        ((∃ s', RelChain Rsrc cs s s' ∧ Gsrc s') ↔ ∃ t', RelChain Rtgt cs t t' ∧ Gtgt t') :=
      fun {s t} h => ih (fun c' hc' => hfwd c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hbwd c' (List.mem_cons_of_mem _ hc')) h
    constructor
    · rintro ⟨s', ⟨s₁, hstep, hrest⟩, hg⟩
      obtain ⟨t₁, hstep', hrep₁⟩ := hfwd c List.mem_cons_self s t s₁ hst hstep
      obtain ⟨t₂, ht₂, hg₂⟩ := (ihmem hrep₁).1 ⟨s', hrest, hg⟩
      exact ⟨t₂, ⟨t₁, hstep', ht₂⟩, hg₂⟩
    · rintro ⟨t', ⟨t₁, hstep, hrest⟩, hg⟩
      obtain ⟨s₁, hstep', hrep₁⟩ := hbwd c List.mem_cons_self s t t₁ hst hstep
      obtain ⟨s₂, hs₂, hg₂⟩ := (ihmem hrep₁).2 ⟨t', hrest, hg⟩
      exact ⟨s₂, ⟨s₁, hstep', hs₂⟩, hg₂⟩

namespace Domain

universe u v w

variable {F : Type u} {A : Type v} {C : Type w} [Inhabited A] {D : Domain F A C (ℕ × ℕ)}

/-! ### The state transformer of a chain, for the interleaving refinement -/

/-- **The nondeterministic state transformer of a chain of tasks**: `xs` refines into an action
sequence executable in `s` whose execution reaches `s'`. -/
def ChainReach (D : Domain F A C (ℕ × ℕ)) (xs : List (A ⊕ C)) (s s' : Set F) : Prop :=
  ∃ as, D.ChainYield xs as ∧ D.SeqApplicable as s ∧ D.transitionSeq as s = s'

theorem chainReach_nil_iff {s s' : Set F} : D.ChainReach [] s s' ↔ s' = s := by
  constructor
  · rintro ⟨as, hy, -, hs⟩
    rw [chainYield_nil_iff] at hy
    subst hy
    simpa using hs.symm
  · rintro rfl
    exact ⟨[], chainYield_nil_iff.2 rfl, by simp [ActionModel.SeqApplicable], by simp⟩

/-- **A chain composes**: the state transformer of `xs ++ ys` is the composite of those of `xs`
and of `ys`. -/
theorem chainReach_append_iff {xs ys : List (A ⊕ C)} {s s'' : Set F} :
    D.ChainReach (xs ++ ys) s s'' ↔ ∃ s', D.ChainReach xs s s' ∧ D.ChainReach ys s' s'' := by
  constructor
  · rintro ⟨cs, hy, happ, hs⟩
    obtain ⟨as, bs, rfl, hxs, hys⟩ := chainYield_append_iff.1 hy
    obtain ⟨happ₁, happ₂⟩ := (ActionModel.seqApplicable_append _ _ _ _).1 happ
    refine ⟨D.transitionSeq as s, ⟨as, hxs, happ₁, rfl⟩, ⟨bs, hys, happ₂, ?_⟩⟩
    rw [← hs, ActionModel.transitionSeq_append]
  · rintro ⟨s', ⟨as, hxs, happ₁, rfl⟩, ⟨bs, hys, happ₂, rfl⟩⟩
    refine ⟨as ++ bs, chainYield_append_iff.2 ⟨as, bs, rfl, hxs, hys⟩, ?_, ?_⟩
    · rw [ActionModel.seqApplicable_append]
      exact ⟨happ₁, happ₂⟩
    · rw [ActionModel.transitionSeq_append]

/-- **A chain of tasks realises the composite of the per-task relations.** -/
theorem chainReach_list_iff {R : A ⊕ C → Set F → Set F → Prop} {xs : List (A ⊕ C)}
    (hseg : ∀ x ∈ xs, ∀ s s' : Set F, D.ChainReach [x] s s' ↔ R x s s')
    {s s' : Set F} : D.ChainReach xs s s' ↔ RelChain R xs s s' := by
  induction xs generalizing s with
  | nil => simpa using chainReach_nil_iff
  | cons x xs ih =>
    have hcons : D.ChainReach (x :: xs) s s' ↔
        ∃ s₁, D.ChainReach [x] s s₁ ∧ D.ChainReach xs s₁ s' :=
      chainReach_append_iff (xs := [x]) (ys := xs)
    rw [hcons, relChain_cons]
    refine exists_congr fun s₁ => and_congr (hseg x (by simp) s s₁) ?_
    exact ih fun x' hx' => hseg x' (by simp [hx'])

/-- **A chain of compound tasks realises the composite of the per-task relations.** -/
theorem chainReach_map_inr_iff {R : C → Set F → Set F → Prop} {cs : List C}
    (hseg : ∀ c ∈ cs, ∀ s s' : Set F, D.ChainReach [Sum.inr c] s s' ↔ R c s s')
    {s s' : Set F} : D.ChainReach (cs.map Sum.inr) s s' ↔ RelChain R cs s s' := by
  induction cs generalizing s with
  | nil => simpa using chainReach_nil_iff
  | cons c cs ih =>
    have hsplit : (Sum.inr c :: cs.map Sum.inr : List (A ⊕ C)) =
        [Sum.inr c] ++ cs.map Sum.inr := rfl
    rw [List.map_cons, hsplit, chainReach_append_iff, relChain_cons]
    refine exists_congr fun s₁ => and_congr (hseg c (by simp) s s₁) ?_
    exact ih fun c' hc' => hseg c' (by simp [hc'])

/-! ### The state transformer of an arbitrary task network -/

section Net

variable {I : Type*} [DecidableEq I] {D : Domain F A C I}

/-- **The nondeterministic state transformer of a task network**: `tn` refines into an action
sequence executable in `s` whose execution reaches `s'`.  Unlike `HTN.Domain.ChainReach` this
makes sense for an arbitrary network, in particular for the networks a finite *description*
denotes, whose task identifiers are natural numbers. -/
def NetReach (D : Domain F A C I) (tn : TaskNetwork I A C) (s s' : Set F) : Prop :=
  ∃ as, D.NetYield tn as ∧ D.SeqApplicable as s ∧ D.transitionSeq as s = s'

omit [Inhabited A] in
/-- **A sequential composition of networks composes the state transformers.** -/
theorem netReach_isSeries_iff [Infinite I] {tn tn₁ tn₂ : TaskNetwork I A C}
    (h : TaskNetwork.IsSeries tn tn₁ tn₂) (hw₁ : tn₁.WF) (hw₂ : tn₂.WF) {s s'' : Set F} :
    D.NetReach tn s s'' ↔ ∃ s', D.NetReach tn₁ s s' ∧ D.NetReach tn₂ s' s'' := by
  constructor
  · rintro ⟨cs, ⟨n, hy⟩, happ, hs⟩
    obtain ⟨n₁, n₂, as, bs, -, rfl, hy₁, hy₂⟩ := (netYieldN_isSeries_iff h hw₁ hw₂).1 hy
    obtain ⟨happ₁, happ₂⟩ := (ActionModel.seqApplicable_append _ _ _ _).1 happ
    refine ⟨D.transitionSeq as s, ⟨as, ⟨n₁, hy₁⟩, happ₁, rfl⟩, ⟨bs, ⟨n₂, hy₂⟩, happ₂, ?_⟩⟩
    rw [← hs, ActionModel.transitionSeq_append]
  · rintro ⟨s', ⟨as, ⟨n₁, hy₁⟩, happ₁, rfl⟩, ⟨bs, ⟨n₂, hy₂⟩, happ₂, rfl⟩⟩
    refine ⟨as ++ bs, ⟨n₁ + n₂, (netYieldN_isSeries_iff h hw₁ hw₂).2
      ⟨n₁, n₂, as, bs, rfl, rfl, hy₁, hy₂⟩⟩, ?_, ?_⟩
    · rw [ActionModel.seqApplicable_append]
      exact ⟨happ₁, happ₂⟩
    · rw [ActionModel.transitionSeq_append]

end Net

/-- **A task network is a chain of the networks `tns`**: it is the iterated sequential
composition of them.  The well-formedness of the parts is carried along, because that is what
the splitting of a refinement needs. -/
inductive SeriesChain {I : Type*} :
    TaskNetwork I A C → List (TaskNetwork I A C) → Prop
  | single {tn : TaskNetwork I A C} : SeriesChain tn [tn]
  | cons {tn tn₁ rest : TaskNetwork I A C} {tns : List (TaskNetwork I A C)}
      (h : TaskNetwork.IsSeries tn tn₁ rest) (hw₁ : tn₁.WF) (hwr : rest.WF)
      (hr : SeriesChain rest tns) : SeriesChain tn (tn₁ :: tns)

omit [Inhabited A] in
/-- **A chain of networks composes the state transformers**: refining the whole network is
refining its segments one after the other. -/
theorem netReach_seriesChain {I : Type*} [DecidableEq I] [Infinite I] {D : Domain F A C I}
    {tn : TaskNetwork I A C} {tns : List (TaskNetwork I A C)} (h : SeriesChain tn tns)
    {s s' : Set F} :
    D.NetReach tn s s' ↔ RelChain (fun t s s' => D.NetReach t s s') tns s s' := by
  induction h generalizing s with
  | single =>
    constructor
    · intro hr
      exact ⟨s', hr, rfl⟩
    · rintro ⟨s₁, hr, rfl⟩
      exact hr
  | cons hser hw₁ hwr _ ih =>
    rw [netReach_isSeries_iff hser hw₁ hwr, relChain_cons]
    exact exists_congr fun s₁ => and_congr_right fun _ => ih

/-! ### The state transformer of a chain, for the totally ordered refinement -/

section Yield

variable {I : Type*} {D : Domain F A C I}

/-- **The nondeterministic state transformer of a totally ordered task sequence.** -/
def YieldReach (D : Domain F A C I) (xs : List (A ⊕ C)) (s s' : Set F) : Prop :=
  ∃ as, D.YieldSeq xs as ∧ D.SeqApplicable as s ∧ D.transitionSeq as s = s'

omit [Inhabited A] in
theorem yieldReach_nil_iff {s s' : Set F} : D.YieldReach [] s s' ↔ s' = s := by
  constructor
  · rintro ⟨as, hy, -, hs⟩
    cases hy with
    | nil => simpa using hs.symm
  · rintro rfl
    exact ⟨[], Domain.YieldSeq.nil, by simp [ActionModel.SeqApplicable], by simp⟩

omit [Inhabited A] in
theorem yieldReach_append_iff {xs ys : List (A ⊕ C)} {s s'' : Set F} :
    D.YieldReach (xs ++ ys) s s'' ↔ ∃ s', D.YieldReach xs s s' ∧ D.YieldReach ys s' s'' := by
  constructor
  · rintro ⟨cs, hy, happ, hs⟩
    obtain ⟨as, bs, rfl, hxs, hys⟩ := hy.split
    obtain ⟨happ₁, happ₂⟩ := (ActionModel.seqApplicable_append _ _ _ _).1 happ
    refine ⟨D.transitionSeq as s, ⟨as, hxs, happ₁, rfl⟩, ⟨bs, hys, happ₂, ?_⟩⟩
    rw [← hs, ActionModel.transitionSeq_append]
  · rintro ⟨s', ⟨as, hxs, happ₁, rfl⟩, ⟨bs, hys, happ₂, rfl⟩⟩
    refine ⟨as ++ bs, hxs.append hys, ?_, ?_⟩
    · rw [ActionModel.seqApplicable_append]
      exact ⟨happ₁, happ₂⟩
    · rw [ActionModel.transitionSeq_append]

omit [Inhabited A] in
/-- **A totally ordered sequence of tasks realises the composite of the per-task relations.** -/
theorem yieldReach_list_iff {R : A ⊕ C → Set F → Set F → Prop} {xs : List (A ⊕ C)}
    (hseg : ∀ x ∈ xs, ∀ s s' : Set F, D.YieldReach [x] s s' ↔ R x s s')
    {s s' : Set F} : D.YieldReach xs s s' ↔ RelChain R xs s s' := by
  induction xs generalizing s with
  | nil => simpa using yieldReach_nil_iff
  | cons x xs ih =>
    have hcons : D.YieldReach (x :: xs) s s' ↔
        ∃ s₁, D.YieldReach [x] s s₁ ∧ D.YieldReach xs s₁ s' :=
      yieldReach_append_iff (xs := [x]) (ys := xs)
    rw [hcons, relChain_cons]
    refine exists_congr fun s₁ => and_congr (hseg x (by simp) s s₁) ?_
    exact ih fun x' hx' => hseg x' (by simp [hx'])

omit [Inhabited A] in
/-- **A totally ordered sequence of compound tasks realises the composite of the per-task
relations.** -/
theorem yieldReach_map_inr_iff {R : C → Set F → Set F → Prop} {cs : List C}
    (hseg : ∀ c ∈ cs, ∀ s s' : Set F, D.YieldReach [Sum.inr c] s s' ↔ R c s s')
    {s s' : Set F} : D.YieldReach (cs.map Sum.inr) s s' ↔ RelChain R cs s s' := by
  induction cs generalizing s with
  | nil => simpa using yieldReach_nil_iff
  | cons c cs ih =>
    have hsplit : (Sum.inr c :: cs.map Sum.inr : List (A ⊕ C)) =
        [Sum.inr c] ++ cs.map Sum.inr := rfl
    rw [List.map_cons, hsplit, yieldReach_append_iff, relChain_cons]
    refine exists_congr fun s₁ => and_congr (hseg c (by simp) s s₁) ?_
    exact ih fun c' hc' => hseg c' (by simp [hc'])

end Yield

end Domain

namespace Problem

universe u v w

variable {F : Type u} {A : Type v} {C : Type w}

/-- **Solvability of a problem whose initial task network is a chain**, in terms of the state
transformer of that chain. -/
theorem solvable_chainReach_iff [Inhabited A] {P : Problem F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ P.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls) {xs : List (A ⊕ C)}
    (htn : P.tnI = TaskNetwork.seq xs) :
    P.Solvable ↔ ∃ s', P.domain.ChainReach xs P.init s' ∧ P.goal ⊆ s' := by
  have hgrid' : ∀ m ∈ P.domain.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls := hgrid
  rw [solvable_iff_netYield, htn]
  simp only [Domain.netYield_seq_iff hgrid']
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    exact ⟨P.transitionSeq as P.init, ⟨as, hy, happ, rfl⟩, hgoal⟩
  · rintro ⟨s', ⟨as, hy, happ, rfl⟩, hgoal⟩
    exact ⟨as, hy, happ, hgoal⟩

/-- **Solvability in terms of the state transformer of the initial task network.** -/
theorem solvable_netReach_iff {I : Type*} [DecidableEq I] {P : Problem F A C I} :
    P.Solvable ↔ ∃ s', P.domain.NetReach P.tnI P.init s' ∧ P.goal ⊆ s' := by
  rw [solvable_iff_netYield]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    exact ⟨P.transitionSeq as P.init, ⟨as, hy, happ, rfl⟩, hgoal⟩
  · rintro ⟨s', ⟨as, hy, happ, rfl⟩, hgoal⟩
    exact ⟨as, hy, happ, hgoal⟩

/-- **Solvability of a totally ordered problem whose initial task network is the sequence
`xs`**, in terms of the state transformer of that sequence. -/
theorem solvable_yieldReach_iff {I : Type*} [DecidableEq I] [Infinite I] {P : Problem F A C I}
    (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I} {xs : List (A ⊕ C)}
    (h₀ : P.tnI.IsSeqNet l₀ xs) :
    P.Solvable ↔ ∃ s', P.domain.YieldReach xs P.init s' ∧ P.goal ⊆ s' := by
  rw [solvable_iff_yieldSeq hwf hto h₀]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    exact ⟨P.transitionSeq as P.init, ⟨as, hy, happ, rfl⟩, hgoal⟩
  · rintro ⟨s', ⟨as, hy, happ, rfl⟩, hgoal⟩
    exact ⟨as, hy, happ, hgoal⟩

end Problem


/-! ### The reduction of a compilation with an unrestricted initial task network -/

namespace Problem

universe u' v' w'

/-- **A compilation whose compiled instance copies the initial task network of the source is
correct as soon as it is correct segment by segment.**

`P` is the source problem, totally ordered, with the initial task sequence `xs`; `P'` is the
compiled problem, whose initial task network is the chain of the compiled tasks `g x`, one per
task `x` of `xs`.  `Rep` is the representation of a source state in the compiled problem.  Under
the two simulation conditions — every source segment is matched by a compiled segment and
conversely — and the agreement of the two goal conditions on represented states, the two
problems are solvable together.

This isolates the generic half of a compilation for a source problem whose initial task network
is *not* a single compound task: what remains to be proved is the per-segment statement, that
the compiled task `g x` is a faithful state transformer for the source task `x`. -/
theorem solvable_iff_of_segSim {F : Type u} {A : Type v} {C : Type w} {I : Type*}
    {F' : Type u'} {A' : Type v'} {C' : Type w'} [DecidableEq I] [Infinite I] [Inhabited A']
    {P : Problem F A C I} {P' : Problem F' A' C' (ℕ × ℕ)}
    (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I} {xs : List (A ⊕ C)}
    (h₀ : P.tnI.IsSeqNet l₀ xs)
    (hgrid : ∀ m ∈ P'.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {g : A ⊕ C → A' ⊕ C'} (htn : P'.tnI = TaskNetwork.seq (xs.map g))
    {Rep : Set F → Set F' → Prop} (hinit : Rep P.init P'.init)
    (hfwd : ∀ x ∈ xs, ∀ s t s', Rep s t → P.domain.YieldReach [x] s s' →
      ∃ t', P'.domain.ChainReach [g x] t t' ∧ Rep s' t')
    (hbwd : ∀ x ∈ xs, ∀ s t t', Rep s t → P'.domain.ChainReach [g x] t t' →
      ∃ s', P.domain.YieldReach [x] s s' ∧ Rep s' t')
    (hgoal : ∀ s t, Rep s t → (P.goal ⊆ s ↔ P'.goal ⊆ t)) :
    P.Solvable ↔ P'.Solvable := by
  rw [solvable_yieldReach_iff hwf hto h₀, solvable_chainReach_iff hgrid htn]
  have hsrc : ∀ {s s' : Set F},
      (P.domain.YieldReach xs s s' ↔
        RelChain (fun x s s' => P.domain.YieldReach [x] s s') xs s s') :=
    fun {s s'} => Domain.yieldReach_list_iff (fun _ _ _ _ => Iff.rfl)
  have htgt : ∀ {t t' : Set F'},
      (P'.domain.ChainReach (xs.map g) t t' ↔
        RelChain (fun x t t' => P'.domain.ChainReach [g x] t t') xs t t') := by
    intro t t'
    rw [Domain.chainReach_list_iff (R := fun y t t' => P'.domain.ChainReach [y] t t')
      (fun _ _ _ _ => Iff.rfl), relChain_map]
  calc (∃ s', P.domain.YieldReach xs P.init s' ∧ P.goal ⊆ s')
      ↔ ∃ s', RelChain (fun x s s' => P.domain.YieldReach [x] s s') xs P.init s' ∧
          P.goal ⊆ s' := by
        exact exists_congr fun s' => and_congr_left' hsrc
    _ ↔ ∃ t', RelChain (fun x t t' => P'.domain.ChainReach [g x] t t') xs P'.init t' ∧
          P'.goal ⊆ t' :=
        exists_relChain_congr xs hfwd hbwd hgoal hinit
    _ ↔ ∃ t', P'.domain.ChainReach (xs.map g) P'.init t' ∧ P'.goal ⊆ t' := by
        exact exists_congr fun t' => and_congr_left' htgt.symm


/-- **The reduction, for an arbitrary target identifier type.**  Same statement as
`HTN.Problem.solvable_iff_of_segSim`, with the initial task network of the compiled problem
given as an iterated sequential composition (`HTN.Domain.SeriesChain`) of the compiled segments
rather than as a chain over the identifiers `ℕ × ℕ`.  This is the form a compilation of
*descriptions* needs, since a described network has natural numbers as task identifiers. -/
theorem solvable_iff_of_netSegSim {F : Type u} {A : Type v} {C : Type w} {I : Type*}
    {F' : Type u'} {A' : Type v'} {C' : Type w'} {I' : Type*}
    [DecidableEq I] [Infinite I] [DecidableEq I'] [Infinite I']
    {P : Problem F A C I} {P' : Problem F' A' C' I'}
    (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I} {xs : List (A ⊕ C)}
    (h₀ : P.tnI.IsSeqNet l₀ xs)
    {g : A ⊕ C → TaskNetwork I' A' C'} (hchain : Domain.SeriesChain P'.tnI (xs.map g))
    {Rep : Set F → Set F' → Prop} (hinit : Rep P.init P'.init)
    (hfwd : ∀ x ∈ xs, ∀ s t s', Rep s t → P.domain.YieldReach [x] s s' →
      ∃ t', P'.domain.NetReach (g x) t t' ∧ Rep s' t')
    (hbwd : ∀ x ∈ xs, ∀ s t t', Rep s t → P'.domain.NetReach (g x) t t' →
      ∃ s', P.domain.YieldReach [x] s s' ∧ Rep s' t')
    (hgoal : ∀ s t, Rep s t → (P.goal ⊆ s ↔ P'.goal ⊆ t)) :
    P.Solvable ↔ P'.Solvable := by
  rw [solvable_yieldReach_iff hwf hto h₀, solvable_netReach_iff]
  have hsrc : ∀ {s s' : Set F},
      (P.domain.YieldReach xs s s' ↔
        RelChain (fun x s s' => P.domain.YieldReach [x] s s') xs s s') :=
    fun {s s'} => Domain.yieldReach_list_iff (fun _ _ _ _ => Iff.rfl)
  have htgt : ∀ {t t' : Set F'},
      (P'.domain.NetReach P'.tnI t t' ↔
        RelChain (fun x t t' => P'.domain.NetReach (g x) t t') xs t t') := by
    intro t t'
    rw [Domain.netReach_seriesChain hchain, relChain_map]
  calc (∃ s', P.domain.YieldReach xs P.init s' ∧ P.goal ⊆ s')
      ↔ ∃ s', RelChain (fun x s s' => P.domain.YieldReach [x] s s') xs P.init s' ∧
          P.goal ⊆ s' := exists_congr fun s' => and_congr_left' hsrc
    _ ↔ ∃ t', RelChain (fun x t t' => P'.domain.NetReach (g x) t t') xs P'.init t' ∧
          P'.goal ⊆ t' := exists_relChain_congr xs hfwd hbwd hgoal hinit
    _ ↔ ∃ t', P'.domain.NetReach P'.tnI P'.init t' ∧ P'.goal ⊆ t' :=
        exists_congr fun t' => and_congr_left' htgt.symm

end Problem

end HTN
