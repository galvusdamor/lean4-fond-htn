import HtnPlanning.Core.TONormalForm
/-!
# Plan existence for totally ordered HTN as reachability between states

`HtnPlanning/Core/TONormalForm.lean` reduces solvability of a totally ordered problem to the
existence of a *plan*: an action sequence into which the initial task sequence can be refined,
executable in the initial state and reaching the goal
(`HTN.Problem.solvable_iff_yieldSeq`).  A plan can be exponentially — indeed unboundedly — long,
so that criterion is not yet an algorithm.

This file gives the criterion that is one: the relation *"executing a refinement of the task
sequence `xs` can lead from the state `s` to the state `u`"*, defined directly, without
mentioning the plan.  It is the classical state-pair characterisation behind the
exponential-time algorithm for totally ordered HTN planning: the relevant information about a
compound task is the set of *pairs of states* `(s, u)` its refinements realise, and that set is
the least fixpoint of a monotone operator over pairs of states — exponentially many when the
number of facts is finite.

## Main definitions

* `HTN.Domain.SeqReach D xs s u` — some refinement of the task sequence `xs` is executable in `s`
  and leads to `u`.

## Main results

* `HTN.Domain.seqReach_append_iff` — the relation is transitive along concatenation of task
  sequences: a task sequence `xs ++ ys` leads from `s` to `u` exactly when some intermediate
  state `t` is reachable by `xs` and leads on to `u` by `ys`.  This is the composition rule that
  makes the state-pair information *sufficient*;
* `HTN.Domain.seqReach_iff_exists_yieldSeq` — **the relation is exactly the plan criterion**:
  `SeqReach xs s u` holds iff some refinement `as` of `xs` is executable in `s` with
  `transitionSeq as s = u`;
* `HTN.Problem.solvable_iff_seqReach` — **plan existence for a totally ordered problem is
  reachability of a goal state from the initial state along the initial task sequence**.  Plans
  no longer occur in the statement, which is what an algorithm searching over state pairs needs.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Domain

variable (D : Domain F A C I)

/-- **Reachability along a task sequence.**  `D.SeqReach xs s u` states that some refinement of
the totally ordered task sequence `xs` is executable in the state `s` and leads to the state `u`.

The three rules are the ones an algorithm over pairs of states uses: the empty sequence changes
nothing; a leading primitive task must be applicable and moves the state; a leading compound task
is replaced by the body of one of its methods, which leads to some intermediate state from which
the rest of the sequence continues. -/
inductive SeqReach : List (A ⊕ C) → Set F → Set F → Prop
  /-- The empty task sequence leads from a state to itself. -/
  | nil {s : Set F} : SeqReach [] s s
  /-- A leading primitive task is executed, if it is applicable. -/
  | prim {a : A} {xs : List (A ⊕ C)} {s u : Set F} (h : D.toActionModel.Applicable a s)
      (hs : SeqReach xs (D.toActionModel.transition a s) u) : SeqReach (Sum.inl a :: xs) s u
  /-- A leading compound task is replaced by the body of one of its methods. -/
  | comp {c : C} {bs xs : List (A ⊕ C)} {s t u : Set F} (hm : D.SeqBody c bs)
      (hb : SeqReach bs s t) (hs : SeqReach xs t u) : SeqReach (Sum.inr c :: xs) s u

variable {D}

/-- **Composition.**  Two reachabilities in a row are a reachability along the concatenated task
sequence. -/
theorem SeqReach.append {xs ys : List (A ⊕ C)} {s t u : Set F} (hx : D.SeqReach xs s t)
    (hy : D.SeqReach ys t u) : D.SeqReach (xs ++ ys) s u := by
  induction hx with
  | nil => simpa using hy
  | prim h _ ih => exact SeqReach.prim h (ih hy)
  | comp hm hb _ _ ihs => exact SeqReach.comp hm hb (ihs hy)

/-- **Decomposition.**  A reachability along a concatenated task sequence passes through an
intermediate state. -/
theorem SeqReach.split {xs ys : List (A ⊕ C)} {s u : Set F} (h : D.SeqReach (xs ++ ys) s u) :
    ∃ t, D.SeqReach xs s t ∧ D.SeqReach ys t u := by
  induction xs generalizing s with
  | nil => exact ⟨s, SeqReach.nil, by simpa using h⟩
  | cons x xs ih =>
      cases x with
      | inl a =>
          rw [List.cons_append] at h
          cases h with
          | prim happ hrest =>
              obtain ⟨t, h₁, h₂⟩ := ih hrest
              exact ⟨t, SeqReach.prim happ h₁, h₂⟩
      | inr c =>
          rw [List.cons_append] at h
          cases h with
          | comp hm hb hrest =>
              obtain ⟨t, h₁, h₂⟩ := ih hrest
              exact ⟨t, SeqReach.comp hm hb h₁, h₂⟩

/-- **Reachability along a concatenation**, in both directions. -/
theorem seqReach_append_iff {xs ys : List (A ⊕ C)} {s u : Set F} :
    D.SeqReach (xs ++ ys) s u ↔ ∃ t, D.SeqReach xs s t ∧ D.SeqReach ys t u :=
  ⟨SeqReach.split, fun ⟨_, h₁, h₂⟩ => h₁.append h₂⟩

/-- **Soundness**: a reachability is realised by an executable refinement. -/
theorem exists_yieldSeq_of_seqReach {xs : List (A ⊕ C)} {s u : Set F}
    (h : D.SeqReach xs s u) : ∃ as : List A, D.YieldSeq xs as ∧
      D.toActionModel.SeqApplicable as s ∧ D.toActionModel.transitionSeq as s = u := by
  induction h with
  | nil => exact ⟨[], YieldSeq.nil, trivial, rfl⟩
  | @prim a xs s u happ _ ih =>
      obtain ⟨as, hy, happ', htr⟩ := ih
      exact ⟨a :: as, YieldSeq.prim hy, ⟨happ, happ'⟩, htr⟩
  | @comp c bs xs s t u hm _ _ ihb ihs =>
      obtain ⟨as₁, hy₁, happ₁, htr₁⟩ := ihb
      obtain ⟨as₂, hy₂, happ₂, htr₂⟩ := ihs
      refine ⟨as₁ ++ as₂, YieldSeq.comp hm (hy₁.append hy₂), ?_, ?_⟩
      · rw [ActionModel.seqApplicable_append]
        exact ⟨happ₁, by rw [htr₁]; exact happ₂⟩
      · rw [ActionModel.transitionSeq_append, htr₁]; exact htr₂

/-- **Completeness**: an executable refinement realises a reachability. -/
theorem seqReach_of_yieldSeq {xs : List (A ⊕ C)} {as : List A} (hy : D.YieldSeq xs as) :
    ∀ s : Set F, D.toActionModel.SeqApplicable as s →
      D.SeqReach xs s (D.toActionModel.transitionSeq as s) := by
  induction hy with
  | nil => intro s _; exact SeqReach.nil
  | @prim a xs as _ ih =>
      intro s happ
      exact SeqReach.prim happ.1 (ih _ happ.2)
  | @comp c bs xs as hm _ ih =>
      intro s happ
      obtain ⟨t, h₁, h₂⟩ := (ih s happ).split
      exact SeqReach.comp hm h₁ h₂

/-- **Reachability along a task sequence is the plan criterion.**  The state pairs realised by a
task sequence are exactly those realised by its executable refinements — so an algorithm may
work with pairs of states and forget the plans. -/
theorem seqReach_iff_exists_yieldSeq {xs : List (A ⊕ C)} {s u : Set F} :
    D.SeqReach xs s u ↔ ∃ as : List A, D.YieldSeq xs as ∧
      D.toActionModel.SeqApplicable as s ∧ D.toActionModel.transitionSeq as s = u := by
  refine ⟨exists_yieldSeq_of_seqReach, ?_⟩
  rintro ⟨as, hy, happ, rfl⟩
  exact seqReach_of_yieldSeq hy s happ

/-! ### The fixpoint, round by round

The rules of `HTN.Domain.SeqReach` are the rules of a monotone operator on relations between
states, indexed by the compound tasks: given what is known about the state pairs each compound
task realises, one round of the operator reads off what its methods' bodies realise.  Iterating
the operator from the empty relation computes the reachability relation, and when there are
finitely many facts and compound tasks the iteration stabilises — which is what turns the
characterisation into an algorithm. -/

/-- **Reachability along a task sequence, relative to an approximation `T`** of the state pairs
realised by the compound tasks.  Unlike `HTN.Domain.SeqReach` this is a structural recursion on
the task sequence: no unfolding of compound tasks happens inside it. -/
def seqOf (D : Domain F A C I) (T : C → Set F → Set F → Prop) :
    List (A ⊕ C) → Set F → Set F → Prop
  | [], s, u => s = u
  | Sum.inl a :: xs, s, u =>
      D.toActionModel.Applicable a s ∧ seqOf D T xs (D.toActionModel.transition a s) u
  | Sum.inr c :: xs, s, u => ∃ t, T c s t ∧ seqOf D T xs t u

/-- **One round of the operator**: a compound task realises what the body of one of its methods
realises, according to the current approximation. -/
def compStep (D : Domain F A C I) (T : C → Set F → Set F → Prop) :
    C → Set F → Set F → Prop :=
  fun c s u => ∃ bs, D.SeqBody c bs ∧ D.seqOf T bs s u

/-- **The iteration of the operator** from the empty approximation. -/
def compIter (D : Domain F A C I) : ℕ → C → Set F → Set F → Prop
  | 0 => fun _ _ _ => False
  | n + 1 => D.compStep (compIter D n)

lemma seqOf_mono {T T' : C → Set F → Set F → Prop} (h : ∀ c s u, T c s u → T' c s u) :
    ∀ (xs : List (A ⊕ C)) (s u : Set F), D.seqOf T xs s u → D.seqOf T' xs s u := by
  intro xs
  induction xs with
  | nil => intro s u h'; exact h'
  | cons x xs ih =>
      cases x with
      | inl a => exact fun s u h' => ⟨h'.1, ih _ _ h'.2⟩
      | inr c => exact fun s u ⟨t, ht, hrest⟩ => ⟨t, h c s t ht, ih _ _ hrest⟩

lemma compStep_mono {T T' : C → Set F → Set F → Prop} (h : ∀ c s u, T c s u → T' c s u) :
    ∀ c s u, D.compStep T c s u → D.compStep T' c s u :=
  fun _ _ _ ⟨bs, hm, hb⟩ => ⟨bs, hm, seqOf_mono h _ _ _ hb⟩

lemma compIter_mono_succ : ∀ (n : ℕ) (c : C) (s u : Set F),
    D.compIter n c s u → D.compIter (n + 1) c s u := by
  intro n
  induction n with
  | zero => intro c s u h; exact h.elim
  | succ n ih => exact compStep_mono ih

lemma compIter_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ (c : C) (s u : Set F), D.compIter n c s u → D.compIter m c s u := by
  induction m with
  | zero => intro c s u h; rw [Nat.le_zero.1 hnm] at h; exact h
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact fun c s u h => compIter_mono_succ m c s u (ih (by omega) c s u h)
      · have : n = m + 1 := by omega
        subst this
        exact fun _ _ _ h => h

/-- Every finite approximation is sound for the reachability relation. -/
theorem seqReach_of_seqOf_compIter : ∀ (n : ℕ) (xs : List (A ⊕ C)) (s u : Set F),
    D.seqOf (D.compIter n) xs s u → D.SeqReach xs s u := by
  intro n
  induction n with
  | zero =>
      intro xs
      induction xs with
      | nil => intro s u h; subst h; exact SeqReach.nil
      | cons x xs ih =>
          cases x with
          | inl a => exact fun s u h => SeqReach.prim h.1 (ih _ _ h.2)
          | inr c => exact fun s u ⟨_, hT, _⟩ => hT.elim
  | succ n ihn =>
      intro xs
      induction xs with
      | nil => intro s u h; subst h; exact SeqReach.nil
      | cons x xs ih =>
          cases x with
          | inl a => exact fun s u h => SeqReach.prim h.1 (ih _ _ h.2)
          | inr c =>
              rintro s u ⟨t, ⟨bs, hm, hb⟩, hrest⟩
              exact SeqReach.comp hm (ihn bs s t hb) (ih _ _ hrest)

/-- Conversely, every reachability is found after finitely many rounds. -/
theorem exists_seqOf_compIter_of_seqReach {xs : List (A ⊕ C)} {s u : Set F}
    (h : D.SeqReach xs s u) : ∃ n, D.seqOf (D.compIter n) xs s u := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | prim happ _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, happ, hn⟩
  | @comp c bs xs s t u hm _ _ ihb ihs =>
      obtain ⟨n₁, h₁⟩ := ihb
      obtain ⟨n₂, h₂⟩ := ihs
      refine ⟨max n₁ n₂ + 1, t, ⟨bs, hm, ?_⟩, ?_⟩
      · exact seqOf_mono (compIter_mono (le_max_left n₁ n₂)) _ _ _ h₁
      · exact seqOf_mono (compIter_mono (by omega)) _ _ _ h₂

/-- **The reachability relation is the iteration, once the iteration is closed.**  If one round
of the operator adds nothing at stage `n`, the stage-`n` approximation already answers every
reachability question. -/
theorem seqReach_iff_seqOf_compIter_of_closed {n : ℕ}
    (hcl : ∀ (c : C) (s u : Set F), D.compIter (n + 1) c s u → D.compIter n c s u)
    {xs : List (A ⊕ C)} {s u : Set F} :
    D.SeqReach xs s u ↔ D.seqOf (D.compIter n) xs s u := by
  have hstab : ∀ m, ∀ (c : C) (s u : Set F), D.compIter m c s u → D.compIter n c s u := by
    intro m
    induction m with
    | zero => intro c s u h; exact h.elim
    | succ m ih =>
        intro c s u h
        exact hcl c s u (compStep_mono ih c s u h)
  refine ⟨fun h => ?_, seqReach_of_seqOf_compIter n xs s u⟩
  obtain ⟨m, hm⟩ := exists_seqOf_compIter_of_seqReach h
  exact seqOf_mono (hstab m) _ _ _ hm

/-- **The iteration closes.**  With finitely many facts and finitely many compound tasks there
are finitely many triples `(c, s, u)`, so the increasing chain of approximations cannot grow
forever: some round adds nothing, and by
`HTN.Domain.seqReach_iff_seqOf_compIter_of_closed` that round's approximation decides
reachability.  This is the termination of the state-pair algorithm; the number of rounds is
bounded by the number of triples, which is exponential in the number of facts. -/
theorem exists_compIter_closed [Finite F] [Finite C] :
    ∃ n : ℕ, ∀ (c : C) (s u : Set F), D.compIter (n + 1) c s u → D.compIter n c s u := by
  by_contra hcon
  push_neg at hcon
  choose c s u hmem hnot using hcon
  have hne : ∀ n m : ℕ, n < m → (c n, s n, u n) ≠ (c m, s m, u m) := by
    intro n m hlt heq
    have hc : c n = c m := congrArg (fun t => t.1) heq
    have hs : s n = s m := congrArg (fun t => t.2.1) heq
    have hu : u n = u m := congrArg (fun t => t.2.2) heq
    refine hnot m ?_
    rw [← hc, ← hs, ← hu]
    exact compIter_mono (by omega) _ _ _ (hmem n)
  obtain ⟨n, m, hnm, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (c n, s n, u n))
  rcases Nat.lt_or_ge n m with hlt | hge
  · exact hne n m hlt heq
  · exact hne m n (by omega) heq.symm

end Domain

namespace Problem

variable [DecidableEq I] {P : Problem F A C I}

/-- **Plan existence for a totally ordered HTN problem is reachability of a goal state.**  A
well-formed problem with totally ordered methods whose initial task network is the task sequence
`xs₀` is solvable exactly when some state satisfying the goal is reachable from the initial state
along `xs₀`.

Compared with `HTN.Problem.solvable_iff_yieldSeq`, the plan has disappeared from the statement:
what is quantified over is a *state*, and the relation `HTN.Domain.SeqReach` is the least
fixpoint of a monotone operator on pairs of states.  This is the form the exponential-time
algorithm for totally ordered HTN planning searches. -/
theorem solvable_iff_seqReach [Infinite I] (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I}
    {xs₀ : List (A ⊕ C)} (h₀ : P.tnI.IsSeqNet l₀ xs₀) :
    P.Solvable ↔ ∃ u : Set F, P.domain.SeqReach xs₀ P.init u ∧ P.GoalState u := by
  rw [solvable_iff_yieldSeq hwf hto h₀]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    exact ⟨_, Domain.seqReach_of_yieldSeq hy P.init happ, hgoal⟩
  · rintro ⟨u, hreach, hgoal⟩
    obtain ⟨as, hy, happ, htr⟩ := Domain.exists_yieldSeq_of_seqReach hreach
    exact ⟨as, hy, happ, by rw [show P.transitionSeq as P.init = u from htr]; exact hgoal⟩

/-- **Plan existence for a totally ordered problem, as a terminating computation.**  Once the
iteration of the state-pair operator is closed — which happens after finitely many rounds when
there are finitely many facts and compound tasks, by `HTN.Domain.exists_compIter_closed` — the
problem is solvable exactly when the stage-`n` approximation leads from the initial state to a
goal state along the initial task sequence.  Every ingredient of the right-hand side is a
finite computation over pairs of states. -/
theorem solvable_iff_seqOf_compIter [Infinite I] (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I}
    {xs₀ : List (A ⊕ C)} (h₀ : P.tnI.IsSeqNet l₀ xs₀) {n : ℕ}
    (hcl : ∀ (c : C) (s u : Set F),
      P.domain.compIter (n + 1) c s u → P.domain.compIter n c s u) :
    P.Solvable ↔ ∃ u : Set F, P.domain.seqOf (P.domain.compIter n) xs₀ P.init u ∧
      P.GoalState u := by
  rw [solvable_iff_seqReach hwf hto h₀]
  exact exists_congr fun u =>
    and_congr_left fun _ => Domain.seqReach_iff_seqOf_compIter_of_closed hcl

end Problem

end HTN
