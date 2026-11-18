import HtnComplexity.ToHtnAc.ToHtnAcBodies
/-!
# Simulation lemmas for the TO-HTN ⟶ HTN-AC compilation

`HtnComplexity/ToHtnAc/ToHtnAc.lean` builds, from a totally ordered HTN problem, an acyclic one
whose plans are meant to be *proofs* (in the sense of the proof tuples of
`HtnPlanning/Core/ProofTuples.lean`) that the source problem is solvable.  Its structural
properties (well-formedness, acyclicity, size) are proved there; what is missing for a full
correctness proof is the *simulation*: that the compiled tasks really do what they are meant to
do.

This file proves the **gadget-level half of that simulation**: what the action sequences that
the compiled compound tasks refine into do to the state.  (Which sequences these are is
determined in `HtnComplexity/ToHtnAc/ToHtnAcBodies.lean`.)  The gadgets treated here are:

* `SEL^i` / `SEL_n^i` (`HTN.ToAc.yieldSeq_SEL_spec`, `HTN.ToAc.exists_yieldSeq_SEL`) —
  **guessing a state**: every refinement of `SEL^i` is executable in every state, changes only
  the `i`-th copy of the facts, and leaves a copy that represents *some* source state; and for
  *every* source state there is a refinement producing it.  This is the statement that `SEL^i`
  nondeterministically guesses one of the `2^{|V|}` states into copy `i`.
* `EQ^{i,j}` / `EQ_n^{i,j}` (`HTN.ToAc.yieldSeq_EQn_spec`, `HTN.ToAc.exists_yieldSeq_EQn`,
  `HTN.ToAc.eq_executable_iff`) — **comparing two copies**: refinements of `EQ^{i,j}` never
  change the state, and one of them is executable in `s` exactly when the copies `i` and `j` of
  `s` represent the same source state.
* `STATE_n^1` / `STATE_n^3` (`HTN.ToAc.yieldSeq_STATE1_spec`, `HTN.ToAc.yieldSeq_STATE3_spec`)
  — **copying a state copy**: an executable refinement of `STATE_n^1` leaves the fourth copy
  representing the state stored in the first copy (and likewise `STATE_n^3` copies the third
  into the fifth).
* `MEM` (`HTN.ToAc.yieldSeq_MEM_iff`, `HTN.ToAc.yieldSeq_MEM_spec`) — **a memory cell**:
  it refines into `accept_W`, a refinement of `STATE_{|V|}^1`, `done_R`, and executing it
  records the state stored in the first copy into the fourth copy.
* `𝔠̄^k_t` (`HTN.ToAc.yieldSeq_cnt_iff`) — **counting**: the action sequences that the counting
  task `𝔠̄^k_t` refines into are exactly those refining a sequence of at most `k` copies of `t`.
  This is what makes the exponentially many memory cells of the construction available from
  logarithmically many methods.

What is *not* proved here is the global interleaving argument (the `lock`/`ask`/`accept`/
`done`/`wait` semaphores force the parallel `MEM` and `TUPLE` tasks to enumerate exactly the
derivable proof tuples); see `NOTES.md`.

Throughout, refinement is `HTN.Domain.YieldSeq` — the leftmost-derivation relation of the
grammar formed by the totally ordered method bodies, introduced in
`HtnPlanning/Core/TONormalForm.lean`.  All the gadgets treated here have single-chain bodies,
so this is the right notion for them.
-/

namespace HTN

namespace ToAc

universe u v w x

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

/-! ### The actions of the gadgets -/

@[simp] lemma mem_transition_setV {v : F} {i : Fin 5} {s : Set (AcFact F A C)}
    {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition (AcAct.setV v i) s ↔
      (f ∈ s ∧ f ≠ AcFact.neg v i) ∨ f = AcFact.pos v i := by
  simp [ActionModel.transition, domain, actionModel, add, del, or_comm]

@[simp] lemma mem_transition_delV {v : F} {i : Fin 5} {s : Set (AcFact F A C)}
    {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition (AcAct.delV v i) s ↔
      (f ∈ s ∧ f ≠ AcFact.pos v i) ∨ f = AcFact.neg v i := by
  simp [ActionModel.transition, domain, actionModel, add, del, or_comm]

@[simp] lemma applicable_setV {v : F} {i : Fin 5} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.setV v i) s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma applicable_delV {v : F} {i : Fin 5} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.delV v i) s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma transition_prePV {v : F} {i j : Fin 5} {s : Set (AcFact F A C)} :
    (domain D vars bound).transition (AcAct.prePV v i j) s = s := by
  simp [ActionModel.transition, domain, actionModel, add, del]

@[simp] lemma transition_preNV {v : F} {i j : Fin 5} {s : Set (AcFact F A C)} :
    (domain D vars bound).transition (AcAct.preNV v i j) s = s := by
  simp [ActionModel.transition, domain, actionModel, add, del]

@[simp] lemma applicable_prePV_iff {v : F} {i j : Fin 5} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.prePV v i j) s ↔
      AcFact.pos v i ∈ s ∧ AcFact.pos v j ∈ s := by
  simp [ActionModel.Applicable, domain, actionModel, prec, Set.insert_subset_iff]

@[simp] lemma applicable_preNV_iff {v : F} {i j : Fin 5} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.preNV v i j) s ↔
      AcFact.neg v i ∈ s ∧ AcFact.neg v j ∈ s := by
  simp [ActionModel.Applicable, domain, actionModel, prec, Set.insert_subset_iff]

/-! ### Representing a source state in a copy -/

/-- `s` represents the source state `S` in its `i`-th copy, as far as the facts `vs` are
concerned. -/
def RepresentsOn (s : Set (AcFact F A C)) (i : Fin 5) (S : Set F) (vs : List F) : Prop :=
  ∀ v ∈ vs, (AcFact.pos v i ∈ s ↔ v ∈ S) ∧ (AcFact.neg v i ∈ s ↔ v ∉ S)

/-- In the `i`-th copy of `s` the facts `vs` have a definite truth value: `pos v i` and
`neg v i` are complementary. -/
def ComplementaryOn (s : Set (AcFact F A C)) (i : Fin 5) (vs : List F) : Prop :=
  ∀ v ∈ vs, (AcFact.pos v i ∈ s ↔ AcFact.neg v i ∉ s)

/-- `s'` differs from `s` at most in the `i`-th copy of the facts `vs`. -/
def UnchangedOutside (s s' : Set (AcFact F A C)) (i : Fin 5) (vs : List F) : Prop :=
  ∀ f, (∀ v ∈ vs, f ≠ AcFact.pos v i ∧ f ≠ AcFact.neg v i) → (f ∈ s ↔ f ∈ s')

/-- A copy in which every fact has a definite truth value represents a source state, namely the
set of facts that are true in it. -/
lemma representsOn_of_complementaryOn {s : Set (AcFact F A C)} {i : Fin 5} {vs : List F}
    (h : ComplementaryOn s i vs) : RepresentsOn s i {u | AcFact.pos u i ∈ s} vs := by
  intro v hv
  refine ⟨Iff.rfl, ?_⟩
  have := h v hv
  simp only [Set.mem_setOf_eq]
  tauto

/-! ### `SEL`: guessing a state -/

private lemma sel_cons_spec {n : ℕ} {i : Fin 5} {v : F} {a : AcAct F A C}
    {as' : List (AcAct F A C)}
    (happ : ∀ s : Set (AcFact F A C), (domain D vars bound).Applicable a s)
    (hmem : ∀ (s : Set (AcFact F A C)) (f : AcFact F A C),
      f ≠ AcFact.pos v i → f ≠ AcFact.neg v i →
      (f ∈ s ↔ f ∈ (domain D vars bound).transition a s))
    (hcompl : ∀ s : Set (AcFact F A C),
      (AcFact.pos v i ∈ (domain D vars bound).transition a s ↔
        AcFact.neg v i ∉ (domain D vars bound).transition a s))
    (htake : vars.take (n + 1) = vars.take n ++ [v])
    (IH : ∀ s : Set (AcFact F A C),
      (domain D vars bound).SeqApplicable as' s ∧
      UnchangedOutside s ((domain D vars bound).transitionSeq as' s) i (vars.take n) ∧
      ComplementaryOn ((domain D vars bound).transitionSeq as' s) i (vars.take n))
    (s : Set (AcFact F A C)) :
      (domain D vars bound).SeqApplicable (a :: as') s ∧
      UnchangedOutside s ((domain D vars bound).transitionSeq (a :: as') s) i
        (vars.take (n + 1)) ∧
      ComplementaryOn ((domain D vars bound).transitionSeq (a :: as') s) i
        (vars.take (n + 1)) := by
  obtain ⟨happ', hunch, hcomp⟩ := IH ((domain D vars bound).transition a s)
  refine ⟨⟨happ s, happ'⟩, ?_, ?_⟩
  · intro f hf
    rw [htake] at hf
    obtain ⟨hf1, hf2⟩ := hf v (by simp)
    refine (hmem s f hf1 hf2).trans (hunch f ?_)
    intro u hu
    exact hf u (List.mem_append_left _ hu)
  · rw [htake]
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact hcomp u hu
    · simp only [List.mem_singleton] at hu
      subst hu
      by_cases huin : u ∈ vars.take n
      · exact hcomp u huin
      · have hp := hunch (AcFact.pos u i) (by
          intro y hy
          refine ⟨?_, by simp⟩
          intro heq
          rw [AcFact.pos.injEq] at heq
          exact huin (by rw [heq.1]; exact hy))
        have hq := hunch (AcFact.neg u i) (by
          intro y hy
          refine ⟨by simp, ?_⟩
          intro heq
          rw [AcFact.neg.injEq] at heq
          exact huin (by rw [heq.1]; exact hy))
        simp only [ActionModel.transitionSeq_cons] at *
        rw [← hp, ← hq]
        exact hcompl s

/-- **What `SEL_n^i` does.**  Every refinement of the task `SEL_n^i` is executable in every
state, changes only the `i`-th copy of the first `n` facts, and leaves that copy with a
definite truth value for each of these facts — i.e. representing some source state. -/
theorem yieldSeq_SELn_spec : ∀ {n : ℕ}, n ≤ vars.length → ∀ {i : Fin 5}
    {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.SELn n i)] as →
    ∀ s : Set (AcFact F A C),
      (domain D vars bound).SeqApplicable as s ∧
      UnchangedOutside s ((domain D vars bound).transitionSeq as s) i (vars.take n) ∧
      ComplementaryOn ((domain D vars bound).transitionSeq as s) i (vars.take n) := by
  intro n
  induction n with
  | zero =>
      intro _ i as h s
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_SELn_zero_iff] at hbs
      subst hbs
      simp only [List.nil_append, yieldSeq_nil_iff] at hy
      subst hy
      exact ⟨trivial, fun f _ => Iff.rfl, by intro v hv; simp at hv⟩
  | succ n ih =>
      intro hn i as h s
      have hn' : n < vars.length := by omega
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_SELn_succ_iff] at hbs
      obtain ⟨v, hv, hbs⟩ := hbs
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      rcases hbs with rfl | rfl <;>
        (simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
         obtain ⟨as', rfl, hy⟩ := hy)
      · exact sel_cons_spec (fun s => applicable_setV)
          (fun s f h1 h2 => by simp [h1, h2]) (fun s => by simp) htake
          (fun s => ih (by omega) hy s) s
      · exact sel_cons_spec (fun s => applicable_delV)
          (fun s f h1 h2 => by simp [h1, h2]) (fun s => by simp) htake
          (fun s => ih (by omega) hy s) s

/-- **`SEL_n^i` can guess any state.**  For every source state `S` there is a refinement of
`SEL_n^i` that is executable and leaves the `i`-th copy representing `S` (on the first `n`
facts), changing nothing else. -/
theorem exists_yieldSeq_SELn : ∀ {n : ℕ}, n ≤ vars.length → ∀ (i : Fin 5) (S : Set F)
    (s : Set (AcFact F A C)),
    ∃ as : List (AcAct F A C),
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SELn n i)] as ∧
      (domain D vars bound).SeqApplicable as s ∧
      UnchangedOutside s ((domain D vars bound).transitionSeq as s) i (vars.take n) ∧
      RepresentsOn ((domain D vars bound).transitionSeq as s) i S (vars.take n) := by
  intro n
  induction n with
  | zero =>
      intro _ i S s
      refine ⟨[], ?_, trivial, fun f _ => Iff.rfl, by intro v hv; simp at hv⟩
      exact Domain.YieldSeq.comp (seqBody_SELn_zero_iff.2 rfl) (by simp)
  | succ n ih =>
      intro hn i S s
      have hn' : n < vars.length := by omega
      obtain ⟨v, hv⟩ : ∃ v, vars[n]? = some v := ⟨vars[n], by simp [hn']⟩
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      by_cases hvS : v ∈ S
      · obtain ⟨as', hy, happ, hunch, hrep⟩ :=
          ih (by omega) i S ((domain D vars bound).transition (AcAct.setV v i) s)
        refine ⟨AcAct.setV v i :: as', ?_, ⟨by simp, happ⟩, ?_, ?_⟩
        · refine Domain.YieldSeq.comp (seqBody_SELn_succ_iff.2 ⟨v, hv, Or.inl rfl⟩) ?_
          simpa using Domain.YieldSeq.prim hy
        · intro f hf
          rw [htake] at hf
          obtain ⟨hf1, hf2⟩ := hf v (by simp)
          refine Iff.trans (by simp [hf1, hf2]) (hunch f ?_)
          intro u hu
          exact hf u (List.mem_append_left _ hu)
        · rw [htake]
          intro u hu
          rcases List.mem_append.1 hu with hu | hu
          · exact hrep u hu
          · simp only [List.mem_singleton] at hu
            subst hu
            by_cases huin : u ∈ vars.take n
            · exact hrep u huin
            · have hp := hunch (AcFact.pos u i) (by
                intro y hy'
                refine ⟨?_, by simp⟩
                intro heq
                rw [AcFact.pos.injEq] at heq
                exact huin (by rw [heq.1]; exact hy'))
              have hq := hunch (AcFact.neg u i) (by
                intro y hy'
                refine ⟨by simp, ?_⟩
                intro heq
                rw [AcFact.neg.injEq] at heq
                exact huin (by rw [heq.1]; exact hy'))
              simp only [ActionModel.transitionSeq_cons] at *
              rw [← hp, ← hq]
              simp [hvS]
      · obtain ⟨as', hy, happ, hunch, hrep⟩ :=
          ih (by omega) i S ((domain D vars bound).transition (AcAct.delV v i) s)
        refine ⟨AcAct.delV v i :: as', ?_, ⟨by simp, happ⟩, ?_, ?_⟩
        · refine Domain.YieldSeq.comp (seqBody_SELn_succ_iff.2 ⟨v, hv, Or.inr rfl⟩) ?_
          simpa using Domain.YieldSeq.prim hy
        · intro f hf
          rw [htake] at hf
          obtain ⟨hf1, hf2⟩ := hf v (by simp)
          refine Iff.trans (by simp [hf1, hf2]) (hunch f ?_)
          intro u hu
          exact hf u (List.mem_append_left _ hu)
        · rw [htake]
          intro u hu
          rcases List.mem_append.1 hu with hu | hu
          · exact hrep u hu
          · simp only [List.mem_singleton] at hu
            subst hu
            by_cases huin : u ∈ vars.take n
            · exact hrep u huin
            · have hp := hunch (AcFact.pos u i) (by
                intro y hy'
                refine ⟨?_, by simp⟩
                intro heq
                rw [AcFact.pos.injEq] at heq
                exact huin (by rw [heq.1]; exact hy'))
              have hq := hunch (AcFact.neg u i) (by
                intro y hy'
                refine ⟨by simp, ?_⟩
                intro heq
                rw [AcFact.neg.injEq] at heq
                exact huin (by rw [heq.1]; exact hy'))
              simp only [ActionModel.transitionSeq_cons] at *
              rw [← hp, ← hq]
              simp [hvS]

lemma yieldSeq_SEL_iff {i : Fin 5} {as : List (AcAct F A C)} :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL i)] as ↔
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SELn vars.length i)] as := by
  rw [yieldSeq_inr_cons_iff]
  constructor
  · rintro ⟨bs, hbs, hy⟩
    rw [seqBody_SEL_iff] at hbs
    subst hbs
    simpa using hy
  · intro hy
    exact ⟨_, seqBody_SEL_iff.2 rfl, by simpa using hy⟩

/-- **What `SEL^i` does**: it guesses a state into the `i`-th copy and changes nothing else. -/
theorem yieldSeq_SEL_spec {i : Fin 5} {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL i)] as)
    (s : Set (AcFact F A C)) :
    (domain D vars bound).SeqApplicable as s ∧
    UnchangedOutside s ((domain D vars bound).transitionSeq as s) i vars ∧
    ∃ S : Set F, RepresentsOn ((domain D vars bound).transitionSeq as s) i S vars := by
  rw [yieldSeq_SEL_iff] at h
  obtain ⟨happ, hunch, hcomp⟩ := yieldSeq_SELn_spec (le_refl vars.length) h s
  rw [List.take_length] at hunch hcomp
  exact ⟨happ, hunch, _, representsOn_of_complementaryOn hcomp⟩

/-- **`SEL^i` can guess any state.** -/
theorem exists_yieldSeq_SEL (i : Fin 5) (S : Set F) (s : Set (AcFact F A C)) :
    ∃ as : List (AcAct F A C),
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL i)] as ∧
      (domain D vars bound).SeqApplicable as s ∧
      UnchangedOutside s ((domain D vars bound).transitionSeq as s) i vars ∧
      RepresentsOn ((domain D vars bound).transitionSeq as s) i S vars := by
  obtain ⟨as, hy, happ, hunch, hrep⟩ :=
    exists_yieldSeq_SELn (D := D) (bound := bound) (le_refl vars.length) i S s
  rw [List.take_length] at hunch hrep
  exact ⟨as, yieldSeq_SEL_iff.2 hy, happ, hunch, hrep⟩

/-! ### `EQ`: comparing two copies -/

/-- **What `EQ_n^{i,j}` does.**  A refinement of `EQ_n^{i,j}` never changes the state, and it is
executable in `s` only if the copies `i` and `j` of `s` agree on the first `n` facts. -/
theorem yieldSeq_EQn_spec : ∀ {n : ℕ}, n ≤ vars.length → ∀ {i j : Fin 5}
    {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQn n i j)] as →
    ∀ s : Set (AcFact F A C),
      (domain D vars bound).transitionSeq as s = s ∧
      ((domain D vars bound).SeqApplicable as s → ∀ v ∈ vars.take n,
        (AcFact.pos v i ∈ s ∧ AcFact.pos v j ∈ s) ∨
        (AcFact.neg v i ∈ s ∧ AcFact.neg v j ∈ s)) := by
  intro n
  induction n with
  | zero =>
      intro _ i j as h s
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_EQn_zero_iff] at hbs
      subst hbs
      simp only [List.nil_append, yieldSeq_nil_iff] at hy
      subst hy
      exact ⟨rfl, by intro _ v hv; simp at hv⟩
  | succ n ih =>
      intro hn i j as h s
      have hn' : n < vars.length := by omega
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_EQn_succ_iff] at hbs
      obtain ⟨v, hv, hbs⟩ := hbs
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      rcases hbs with rfl | rfl <;>
        (simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
         obtain ⟨as', rfl, hy⟩ := hy
         obtain ⟨htr, hval⟩ := ih (by omega) hy s
         refine ⟨by simpa using htr, ?_⟩
         rintro ⟨happ, happ'⟩
         rw [htake]
         intro u hu
         rcases List.mem_append.1 hu with hu | hu
         · exact hval (by simpa using happ') u hu
         · simp only [List.mem_singleton] at hu
           subst hu
           simp only [applicable_prePV_iff, applicable_preNV_iff] at happ
           first
             | exact Or.inl happ
             | exact Or.inr happ)

/-- **`EQ_n^{i,j}` succeeds if the copies agree.**  If the copies `i` and `j` of `s` agree on the
first `n` facts then some refinement of `EQ_n^{i,j}` is executable in `s` (and does not change
it). -/
theorem exists_yieldSeq_EQn : ∀ {n : ℕ}, n ≤ vars.length → ∀ (i j : Fin 5)
    (s : Set (AcFact F A C)),
    (∀ v ∈ vars.take n, (AcFact.pos v i ∈ s ∧ AcFact.pos v j ∈ s) ∨
      (AcFact.neg v i ∈ s ∧ AcFact.neg v j ∈ s)) →
    ∃ as : List (AcAct F A C),
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQn n i j)] as ∧
      (domain D vars bound).SeqApplicable as s ∧
      (domain D vars bound).transitionSeq as s = s := by
  intro n
  induction n with
  | zero =>
      intro _ i j s _
      exact ⟨[], Domain.YieldSeq.comp (seqBody_EQn_zero_iff.2 rfl) (by simp), trivial, rfl⟩
  | succ n ih =>
      intro hn i j s hagree
      have hn' : n < vars.length := by omega
      obtain ⟨v, hv⟩ : ∃ v, vars[n]? = some v := ⟨vars[n], by simp [hn']⟩
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      have hagree' : ∀ u ∈ vars.take n, (AcFact.pos u i ∈ s ∧ AcFact.pos u j ∈ s) ∨
          (AcFact.neg u i ∈ s ∧ AcFact.neg u j ∈ s) := by
        intro u hu
        exact hagree u (by rw [htake]; exact List.mem_append_left _ hu)
      have hv' := hagree v (by rw [htake]; simp)
      obtain ⟨as', hy, happ, htr⟩ := ih (by omega) i j s hagree'
      rcases hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨AcAct.prePV v i j :: as', ?_, ⟨by simp [h1, h2], by simpa using happ⟩, ?_⟩
        · refine Domain.YieldSeq.comp (seqBody_EQn_succ_iff.2 ⟨v, hv, Or.inl rfl⟩) ?_
          simpa using Domain.YieldSeq.prim hy
        · simpa using htr
      · refine ⟨AcAct.preNV v i j :: as', ?_, ⟨by simp [h1, h2], by simpa using happ⟩, ?_⟩
        · refine Domain.YieldSeq.comp (seqBody_EQn_succ_iff.2 ⟨v, hv, Or.inr rfl⟩) ?_
          simpa using Domain.YieldSeq.prim hy
        · simpa using htr

lemma yieldSeq_EQ_iff {i j : Fin 5} {as : List (AcAct F A C)} :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ i j)] as ↔
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQn vars.length i j)] as := by
  rw [yieldSeq_inr_cons_iff]
  constructor
  · rintro ⟨bs, hbs, hy⟩
    rw [seqBody_EQ_iff] at hbs
    subst hbs
    simpa using hy
  · intro hy
    exact ⟨_, seqBody_EQ_iff.2 rfl, by simpa using hy⟩

/-- **`EQ^{i,j}` tests equality of two state copies.**  If the copies `i` and `j` of `s`
represent the source states `S` and `T`, then `EQ^{i,j}` has an executable refinement in `s`
exactly when `S` and `T` agree on all the facts. -/
theorem eq_executable_iff {i j : Fin 5} {S T : Set F} {s : Set (AcFact F A C)}
    (hS : RepresentsOn s i S vars) (hT : RepresentsOn s j T vars) :
    (∃ as : List (AcAct F A C), (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ i j)] as ∧
      (domain D vars bound).SeqApplicable as s) ↔ ∀ v ∈ vars, (v ∈ S ↔ v ∈ T) := by
  constructor
  · rintro ⟨as, hy, happ⟩
    rw [yieldSeq_EQ_iff] at hy
    obtain ⟨-, hval⟩ := yieldSeq_EQn_spec (le_refl vars.length) hy s
    intro v hv
    have hv' : v ∈ vars.take vars.length := by rwa [List.take_length]
    rcases hval happ v hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => (hT v hv).1.1 h2, fun _ => (hS v hv).1.1 h1⟩
    · constructor
      · intro hvS; exact absurd hvS ((hS v hv).2.1 h1)
      · intro hvT; exact absurd hvT ((hT v hv).2.1 h2)
  · intro heq
    have hagree : ∀ v ∈ vars.take vars.length,
        (AcFact.pos v i ∈ s ∧ AcFact.pos v j ∈ s) ∨
        (AcFact.neg v i ∈ s ∧ AcFact.neg v j ∈ s) := by
      rw [List.take_length]
      intro v hv
      by_cases hvS : v ∈ S
      · exact Or.inl ⟨(hS v hv).1.2 hvS, (hT v hv).1.2 ((heq v hv).1 hvS)⟩
      · exact Or.inr ⟨(hS v hv).2.2 hvS, (hT v hv).2.2 (fun hvT => hvS ((heq v hv).2 hvT))⟩
    obtain ⟨as, hy, happ, -⟩ :=
      exists_yieldSeq_EQn (D := D) (bound := bound) (le_refl vars.length) i j s hagree
    exact ⟨as, yieldSeq_EQ_iff.2 hy, happ⟩

/-- **Correctness of the counting task.**  The action sequences that `𝔠̄^k_t` refines into are
exactly the ones that a sequence of at most `k` consecutive copies of `t` refines into. -/
theorem yieldSeq_cnt_iff : ∀ (k : ℕ) {t : AcTask F A C} {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.cnt t k)] as ↔
      ∃ m ≤ k, (domain D vars bound).YieldSeq (List.replicate m (Sum.inr t)) as := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t as
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [yieldSeq_inr_cons_iff]
      constructor
      · rintro ⟨bs, hbs, h⟩
        rw [seqBody_cnt_zero_iff] at hbs
        subst hbs
        exact ⟨0, le_rfl, by simpa using h⟩
      · rintro ⟨m, hm, h⟩
        obtain rfl : m = 0 := Nat.le_zero.1 hm
        exact ⟨[], seqBody_cnt_zero_iff.2 rfl, by simpa using h⟩
    · rw [yieldSeq_inr_cons_iff]
      constructor
      · rintro ⟨bs, hbs, h⟩
        rcases seqBody_cnt_one_iff.1 hbs with rfl | rfl
        · exact ⟨1, le_rfl, by simpa using h⟩
        · exact ⟨0, Nat.zero_le _, by simpa using h⟩
      · rintro ⟨m, hm, h⟩
        interval_cases m
        · exact ⟨[], seqBody_cnt_one_iff.2 (Or.inr rfl), by simpa using h⟩
        · exact ⟨[Sum.inr t], seqBody_cnt_one_iff.2 (Or.inl rfl), by simpa using h⟩
  · rcases Nat.even_or_odd k with hev | hod
    · have he : k % 2 = 0 := Nat.even_iff.1 hev
      have hlt : k / 2 < k := Nat.div_lt_self (by omega) (by omega)
      rw [yieldSeq_inr_cons_iff]
      constructor
      · rintro ⟨bs, hbs, h⟩
        rw [seqBody_cnt_even_iff hk he] at hbs
        subst hbs
        have h' : (domain D vars bound).YieldSeq
            ([Sum.inr (AcTask.cnt t (k / 2))] ++ [Sum.inr (AcTask.cnt t (k / 2))]) as := by
          simpa using h
        obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h'.split
        obtain ⟨m₁, hm₁, g₁⟩ := (ih _ hlt).1 h₁
        obtain ⟨m₂, hm₂, g₂⟩ := (ih _ hlt).1 h₂
        refine ⟨m₁ + m₂, by omega, ?_⟩
        rw [List.replicate_add]
        exact g₁.append g₂
      · rintro ⟨m, hm, h⟩
        refine ⟨_, (seqBody_cnt_even_iff hk he).2 rfl, ?_⟩
        obtain ⟨m₁, m₂, rfl, hm₁, hm₂⟩ : ∃ m₁ m₂, m = m₁ + m₂ ∧ m₁ ≤ k / 2 ∧ m₂ ≤ k / 2 :=
          ⟨min m (k / 2), m - min m (k / 2), by omega, by omega, by omega⟩
        rw [List.replicate_add] at h
        obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h.split
        have := ((ih _ hlt).2 ⟨m₁, hm₁, h₁⟩).append ((ih _ hlt).2 ⟨m₂, hm₂, h₂⟩)
        simpa using this
    · have ho : k % 2 = 1 := Nat.odd_iff.1 hod
      have hlt : k - 1 < k := by omega
      rw [yieldSeq_inr_cons_iff]
      constructor
      · rintro ⟨bs, hbs, h⟩
        rcases (seqBody_cnt_odd_iff hk ho).1 hbs with rfl | rfl
        · have h' : (domain D vars bound).YieldSeq
              ([Sum.inr t] ++ [Sum.inr (AcTask.cnt t (k - 1))]) as := by simpa using h
          obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h'.split
          obtain ⟨m, hm, g⟩ := (ih _ hlt).1 h₂
          refine ⟨1 + m, by omega, ?_⟩
          rw [List.replicate_add]
          exact h₁.append g
        · obtain ⟨m, hm, g⟩ := (ih _ hlt).1 (by simpa using h)
          exact ⟨m, by omega, g⟩
      · rintro ⟨m, hm, h⟩
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · refine ⟨_, (seqBody_cnt_odd_iff hk ho).2 (Or.inr rfl), ?_⟩
          have := (ih _ hlt).2 (⟨0, Nat.zero_le _, h⟩ :
            ∃ m ≤ k - 1, (domain D vars bound).YieldSeq (List.replicate m (Sum.inr t)) as)
          simpa using this
        · refine ⟨_, (seqBody_cnt_odd_iff hk ho).2 (Or.inl rfl), ?_⟩
          obtain ⟨m', rfl⟩ : ∃ m', m = 1 + m' := ⟨m - 1, by omega⟩
          rw [List.replicate_add] at h
          obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h.split
          have := h₁.append ((ih _ hlt).2 ⟨m', by omega, h₂⟩)
          simpa using this

/-! ### `STATE^1` and `STATE^3`: copying a state copy

`STATE_n^1` reads the first state copy and writes it into the fourth, `STATE_n^3` reads the
third and writes it into the fifth.  The two are chained (`STATE_0^1` refines into
`STATE_{|V|}^3`), and the innermost body of `STATE_0^3` performs the synchronisation with the
`READ` task and stores the task name; the copying statements below are insensitive to what that
innermost body does, because it touches neither of the two copies concerned.
-/

/-- Writing a true fact into copy `j` extends the represented state by that fact. -/
private lemma represents_write {S : Set F} {j : Fin 5} {v : F} {vs : List F}
    {s : Set (AcFact F A C)} (h : RepresentsOn s j S vs) (hv : v ∈ S) :
    RepresentsOn ((domain D vars bound).transition (AcAct.setV v j) s) j S (vs ++ [v]) := by
  intro u hu
  by_cases huv : u = v
  · subst huv
    constructor
    · simp [ActionModel.transition, domain, actionModel, add, del, hv]
    · simp [ActionModel.transition, domain, actionModel, add, del, hv]
  · have hus : u ∈ vs := by
      rcases List.mem_append.1 hu with hu | hu
      · exact hu
      · exact absurd (by simpa using hu) huv
    obtain ⟨h1, h2⟩ := h u hus
    constructor
    · have : (AcFact.pos u j ∈ (domain D vars bound).transition (AcAct.setV v j) s) ↔
          AcFact.pos u j ∈ s := by
        simp [ActionModel.transition, domain, actionModel, add, del, huv]
      rw [this]; exact h1
    · have : (AcFact.neg u j ∈ (domain D vars bound).transition (AcAct.setV v j) s) ↔
          AcFact.neg u j ∈ s := by
        simp [ActionModel.transition, domain, actionModel, add, del, huv]
      rw [this]; exact h2

/-- Deleting a false fact from copy `j` extends the represented state by that fact. -/
private lemma represents_del {S : Set F} {j : Fin 5} {v : F} {vs : List F}
    {s : Set (AcFact F A C)} (h : RepresentsOn s j S vs) (hv : v ∉ S) :
    RepresentsOn ((domain D vars bound).transition (AcAct.delV v j) s) j S (vs ++ [v]) := by
  intro u hu
  by_cases huv : u = v
  · subst huv
    constructor
    · simp [ActionModel.transition, domain, actionModel, add, del, hv]
    · simp [ActionModel.transition, domain, actionModel, add, del, hv]
  · have hus : u ∈ vs := by
      rcases List.mem_append.1 hu with hu | hu
      · exact hu
      · exact absurd (by simpa using hu) huv
    obtain ⟨h1, h2⟩ := h u hus
    constructor
    · have : (AcFact.pos u j ∈ (domain D vars bound).transition (AcAct.delV v j) s) ↔
          AcFact.pos u j ∈ s := by
        simp [ActionModel.transition, domain, actionModel, add, del, huv]
      rw [this]; exact h1
    · have : (AcFact.neg u j ∈ (domain D vars bound).transition (AcAct.delV v j) s) ↔
          AcFact.neg u j ∈ s := by
        simp [ActionModel.transition, domain, actionModel, add, del, huv]
      rw [this]; exact h2

/-- **`STATE_n^1` copies the first state copy into the fourth.**  If a refinement of `STATE_n^1`
is executable in `s` and the first copy of `s` has a definite truth value for the first `n`
facts, then afterwards the fourth copy represents the state stored in the first copy. -/
theorem yieldSeq_STATE1_spec : ∀ {n : ℕ}, n ≤ vars.length → ∀ {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE1 n)] as →
    ∀ {s : Set (AcFact F A C)}, (domain D vars bound).SeqApplicable as s →
      ComplementaryOn s 0 (vars.take n) →
      RepresentsOn ((domain D vars bound).transitionSeq as s) 3
        {v | AcFact.pos v 0 ∈ s} (vars.take n) := by
  intro n
  induction n with
  | zero => intro _ as _ s _ _ v hv; simp at hv
  | succ n ih =>
      intro hn as h s happ hcompl
      have hn' : n < vars.length := by omega
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_STATE1_succ_iff] at hbs
      obtain ⟨v, hv, hbs⟩ := hbs
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      have hcompl' : ComplementaryOn s 0 (vars.take n) := fun u hu =>
        hcompl u (by rw [htake]; exact List.mem_append_left _ hu)
      obtain ⟨a, b, hbs', hab⟩ :
          ∃ a b : AcAct F A C,
            bs = [Sum.inl a, Sum.inr (AcTask.STATE1 n), Sum.inl b] ∧
            ((a = AcAct.prePV v 0 0 ∧ b = AcAct.setV v 3) ∨
             (a = AcAct.preNV v 0 0 ∧ b = AcAct.delV v 3)) := by
        rcases hbs with rfl | rfl
        · exact ⟨_, _, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩⟩
      subst hbs'
      simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
      obtain ⟨as₁, rfl, hy⟩ := hy
      have hy' : (domain D vars bound).YieldSeq
          ([Sum.inr (AcTask.STATE1 n)] ++ [Sum.inl b]) as₁ := by simpa using hy
      obtain ⟨as₂, as₃, rfl, hy₂, hy₃⟩ := hy'.split
      simp only [yieldSeq_inl_cons_iff, yieldSeq_nil_iff] at hy₃
      obtain ⟨as₄, rfl, rfl⟩ := hy₃
      rw [ActionModel.seqApplicable_cons] at happ
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- the fact `v` is true in the first copy
        have hpos : AcFact.pos v 0 ∈ s := (applicable_prePV_iff.1 happ.1).1
        have hs : (domain D vars bound).transition (AcAct.prePV v 0 0) s = s := by simp
        rw [hs] at happ
        rw [ActionModel.seqApplicable_append] at happ
        have := represents_write (D := D) (vars := vars) (bound := bound) (j := 3) (v := v)
          (ih (by omega) hy₂ happ.2.1 hcompl') hpos
        rw [htake]
        simpa [ActionModel.transitionSeq_append, hs] using this
      · -- the fact `v` is false in the first copy
        have hneg : AcFact.neg v 0 ∈ s := (applicable_preNV_iff.1 happ.1).1
        have hposn : AcFact.pos v 0 ∉ s := by
          have := hcompl v (by rw [htake]; simp)
          exact fun hp => (this.1 hp) hneg
        have hs : (domain D vars bound).transition (AcAct.preNV v 0 0) s = s := by simp
        rw [hs] at happ
        rw [ActionModel.seqApplicable_append] at happ
        have := represents_del (D := D) (vars := vars) (bound := bound) (j := 3) (v := v)
          (ih (by omega) hy₂ happ.2.1 hcompl') hposn
        rw [htake]
        simpa [ActionModel.transitionSeq_append, hs] using this

/-- **`STATE_n^3` copies the third state copy into the fifth.** -/
theorem yieldSeq_STATE3_spec : ∀ {n : ℕ}, n ≤ vars.length → ∀ {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE3 n)] as →
    ∀ {s : Set (AcFact F A C)}, (domain D vars bound).SeqApplicable as s →
      ComplementaryOn s 2 (vars.take n) →
      RepresentsOn ((domain D vars bound).transitionSeq as s) 4
        {v | AcFact.pos v 2 ∈ s} (vars.take n) := by
  intro n
  induction n with
  | zero => intro _ as _ s _ _ v hv; simp at hv
  | succ n ih =>
      intro hn as h s happ hcompl
      have hn' : n < vars.length := by omega
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_STATE3_succ_iff] at hbs
      obtain ⟨v, hv, hbs⟩ := hbs
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      have hcompl' : ComplementaryOn s 2 (vars.take n) := fun u hu =>
        hcompl u (by rw [htake]; exact List.mem_append_left _ hu)
      obtain ⟨a, b, hbs', hab⟩ :
          ∃ a b : AcAct F A C,
            bs = [Sum.inl a, Sum.inr (AcTask.STATE3 n), Sum.inl b] ∧
            ((a = AcAct.prePV v 2 2 ∧ b = AcAct.setV v 4) ∨
             (a = AcAct.preNV v 2 2 ∧ b = AcAct.delV v 4)) := by
        rcases hbs with rfl | rfl
        · exact ⟨_, _, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩⟩
      subst hbs'
      simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
      obtain ⟨as₁, rfl, hy⟩ := hy
      have hy' : (domain D vars bound).YieldSeq
          ([Sum.inr (AcTask.STATE3 n)] ++ [Sum.inl b]) as₁ := by simpa using hy
      obtain ⟨as₂, as₃, rfl, hy₂, hy₃⟩ := hy'.split
      simp only [yieldSeq_inl_cons_iff, yieldSeq_nil_iff] at hy₃
      obtain ⟨as₄, rfl, rfl⟩ := hy₃
      rw [ActionModel.seqApplicable_cons] at happ
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hpos : AcFact.pos v 2 ∈ s := (applicable_prePV_iff.1 happ.1).1
        have hs : (domain D vars bound).transition (AcAct.prePV v 2 2) s = s := by simp
        rw [hs] at happ
        rw [ActionModel.seqApplicable_append] at happ
        have := represents_write (D := D) (vars := vars) (bound := bound) (j := 4) (v := v)
          (ih (by omega) hy₂ happ.2.1 hcompl') hpos
        rw [htake]
        simpa [ActionModel.transitionSeq_append, hs] using this
      · have hneg : AcFact.neg v 2 ∈ s := (applicable_preNV_iff.1 happ.1).1
        have hposn : AcFact.pos v 2 ∉ s := by
          have := hcompl v (by rw [htake]; simp)
          exact fun hp => (this.1 hp) hneg
        have hs : (domain D vars bound).transition (AcAct.preNV v 2 2) s = s := by simp
        rw [hs] at happ
        rw [ActionModel.seqApplicable_append] at happ
        have := represents_del (D := D) (vars := vars) (bound := bound) (j := 4) (v := v)
          (ih (by omega) hy₂ happ.2.1 hcompl') hposn
        rw [htake]
        simpa [ActionModel.transitionSeq_append, hs] using this

/-! ### `READ`, `WRITE` and `MEM`

The two synchronisation tasks have a single, purely primitive body, and the memory cell `MEM`
wraps one copying task `STATE_{|V|}^1` between the two synchronisation actions.
-/

lemma yieldSeq_WRITE_iff {as : List (AcAct F A C)} :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.WRITE : AcTask F A C)] as ↔
      as = [AcAct.ask RW.write, AcAct.waitA RW.write] := by
  rw [yieldSeq_inr_cons_iff]
  constructor
  · rintro ⟨bs, hbs, hy⟩
    rw [seqBody_WRITE_iff] at hbs
    subst hbs
    simp only [List.append_nil, yieldSeq_inl_cons_iff, yieldSeq_nil_iff] at hy
    obtain ⟨as₁, rfl, as₂, rfl, rfl⟩ := hy
    rfl
  · rintro rfl
    refine ⟨_, seqBody_WRITE_iff.2 rfl, ?_⟩
    simp only [List.append_nil]
    exact Domain.YieldSeq.prim (Domain.YieldSeq.prim Domain.YieldSeq.nil)

lemma yieldSeq_READ_iff {as : List (AcAct F A C)} :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.READ : AcTask F A C)] as ↔
      as = [AcAct.ask RW.read, AcAct.waitA RW.read] := by
  rw [yieldSeq_inr_cons_iff]
  constructor
  · rintro ⟨bs, hbs, hy⟩
    rw [seqBody_READ_iff] at hbs
    subst hbs
    simp only [List.append_nil, yieldSeq_inl_cons_iff, yieldSeq_nil_iff] at hy
    obtain ⟨as₁, rfl, as₂, rfl, rfl⟩ := hy
    rfl
  · rintro rfl
    refine ⟨_, seqBody_READ_iff.2 rfl, ?_⟩
    simp only [List.append_nil]
    exact Domain.YieldSeq.prim (Domain.YieldSeq.prim Domain.YieldSeq.nil)

/-- **What a memory cell refines into**: the synchronisation action `accept_W`, then a
refinement of the copying task `STATE_{|V|}^1`, then `done_R`. -/
lemma yieldSeq_MEM_iff {as : List (AcAct F A C)} :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] as ↔
      ∃ as', (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE1 vars.length)] as' ∧
        as = AcAct.accept RW.write :: (as' ++ [AcAct.doneA RW.read]) := by
  rw [yieldSeq_inr_cons_iff]
  constructor
  · rintro ⟨bs, hbs, hy⟩
    rw [seqBody_MEM_iff] at hbs
    subst hbs
    simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
    obtain ⟨as₁, rfl, hy⟩ := hy
    have hy' : (domain D vars bound).YieldSeq
        ([Sum.inr (AcTask.STATE1 vars.length)] ++ [Sum.inl (AcAct.doneA RW.read)]) as₁ := by
      simpa using hy
    obtain ⟨as₂, as₃, rfl, hy₂, hy₃⟩ := hy'.split
    simp only [yieldSeq_inl_cons_iff, yieldSeq_nil_iff] at hy₃
    obtain ⟨as₄, rfl, rfl⟩ := hy₃
    exact ⟨as₂, hy₂, rfl⟩
  · rintro ⟨as', hy, rfl⟩
    refine ⟨_, seqBody_MEM_iff.2 rfl, ?_⟩
    simp only [List.cons_append, List.nil_append]
    refine Domain.YieldSeq.prim ?_
    have : (domain D vars bound).YieldSeq
        ([Sum.inr (AcTask.STATE1 vars.length)] ++ [Sum.inl (AcAct.doneA RW.read)])
        (as' ++ [AcAct.doneA RW.read]) :=
      hy.append (Domain.YieldSeq.prim Domain.YieldSeq.nil)
    simpa using this

@[simp] lemma mem_transition_accept {x : RW} {s : Set (AcFact F A C)} {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition (AcAct.accept x) s ↔ f ∈ s ∧ f ≠ AcFact.key1 x := by
  simp [ActionModel.transition, domain, actionModel, add, del]

@[simp] lemma mem_transition_doneA {x : RW} {s : Set (AcFact F A C)} {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition (AcAct.doneA x) s ↔ f ∈ s ∨ f = AcFact.key2 x := by
  simp [ActionModel.transition, domain, actionModel, add, del, or_comm]

/-- **What a memory cell does.**  If an executable refinement of `MEM` is run in a state whose
first copy has a definite truth value for every fact, then afterwards the fourth copy of the
state represents the state that was stored in the first copy: the cell has recorded it. -/
theorem yieldSeq_MEM_spec {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] as)
    {s : Set (AcFact F A C)} (happ : (domain D vars bound).SeqApplicable as s)
    (hcompl : ComplementaryOn s 0 vars) :
    RepresentsOn ((domain D vars bound).transitionSeq as s) 3 {v | AcFact.pos v 0 ∈ s} vars := by
  obtain ⟨as', hy, rfl⟩ := yieldSeq_MEM_iff.1 h
  set s₁ := (domain D vars bound).transition (AcAct.accept RW.write) s with hs₁
  rw [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_append] at happ
  have hcompl₁ : ComplementaryOn s₁ 0 (vars.take vars.length) := by
    rw [List.take_length]
    intro v hv
    have := hcompl v hv
    simpa [hs₁] using this
  have hset : {v : F | AcFact.pos v 0 ∈ s₁} = {v : F | AcFact.pos v 0 ∈ s} := by
    ext v; simp [hs₁]
  have ih := yieldSeq_STATE1_spec (D := D) (vars := vars) (bound := bound)
    (le_refl vars.length) hy happ.2.1 hcompl₁
  rw [List.take_length, hset] at ih
  intro v hv
  obtain ⟨h1, h2⟩ := ih v hv
  have hstep : (domain D vars bound).transitionSeq
      (AcAct.accept RW.write :: (as' ++ [AcAct.doneA RW.read])) s =
      (domain D vars bound).transition (AcAct.doneA RW.read)
        ((domain D vars bound).transitionSeq as' s₁) := by
    simp [ActionModel.transitionSeq_append, hs₁]
  rw [hstep]
  constructor
  · rw [mem_transition_doneA]
    constructor
    · rintro (hp | hp)
      · exact h1.1 hp
      · exact absurd hp (by simp)
    · exact fun hvS => Or.inl (h1.2 hvS)
  · rw [mem_transition_doneA]
    constructor
    · rintro (hp | hp)
      · exact h2.1 hp
      · exact absurd hp (by simp)
    · exact fun hvS => Or.inl (h2.2 hvS)

end ToAc

end HTN
