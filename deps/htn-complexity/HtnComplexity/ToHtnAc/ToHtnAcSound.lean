import HtnComplexity.ToHtnAc.ToHtnAcBlock
/-!
# Soundness of the TO-HTN ⟶ HTN-AC compilation

`HtnComplexity/ToHtnAc/ToHtnAcComplete.lean` proves the completeness half of the correctness of the
compilation of `HtnComplexity/ToHtnAc/ToHtnAc.lean`: a solution of the source problem is turned
into a plan of the compiled problem.  This file proves the **soundness** half: from a plan of
the compiled problem a solution of the source problem is read off.

The plan is, by `HTN.ToAc.netYield_tnI_iff`, an interleaving of the runs of the memory cells
with the runs of the proof steps.  By the block decomposition of
`HtnComplexity/ToHtnAc/ToHtnAcBlock.lean` it is a concatenation of blocks, one per proof step,
each of which

* consumes memory cells that have latched *provable* triples, in its read handshakes,
* proves one more triple, by the rules of the proof-tuple calculus of
  `HtnPlanning/Core/ProofTuples.lean`, and
* hands that triple to the memory cells answering its write requests.

The global induction (`HTN.ToAc.final_state_provable`) runs along the blocks: it maintains that
every memory cell holds a provable triple and concludes that at the end of the plan the first
copy, the stored task name and the third copy hold a provable triple.  Matching that triple
with the goal of the compiled problem gives

* `HTN.ToAc.provable_of_solvable_problem'` — a solvable compiled problem yields a derivation of
  `(s₀, t_I, S')` with `S' ⊇ g`;
* `HTN.ToAc.yield_of_solvable_problem'` — hence a refinement of `t_I` into an executable action
  sequence reaching the goal, i.e. a solution of the source problem;
* `HTN.ToAc.solvable_problem'_iff` — the two halves together: the source problem is solvable
  exactly when the compiled problem is, as soon as it has enough memory cells and proof steps.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### The global induction along the blocks -/

/-- **At the end of a plan the state holds a provable triple.**  Every plan that starts in a
clean state with all components in one of the states of `HTN.ToAc.CompInv` either performs
nothing at all, or ends in a state whose first copy, stored task name and third copy are a
triple that is derivable in the proof-tuple calculus. -/
theorem final_state_provable (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o)) :
    ∀ (n : ℕ) {ls : List (List (AcAct F A C))} {z : List (AcAct F A C)}
      {s : Set (AcFact F A C)}, z.length ≤ n →
      (∀ l ∈ ls, CompInv D vars bound l) → Clean s → Sched ls z →
      (domain D vars bound).SeqApplicable z s →
      (domain D vars bound).transitionSeq z s = s ∨
        ∃ (S S' : Set F) (tt : A ⊕ C), D.Provable S tt S' ∧
          RepresentsOn ((domain D vars bound).transitionSeq z s) 0 S vars ∧
          RepresentsOn ((domain D vars bound).transitionSeq z s) 2 S' vars ∧
          TaskOnly tt ((domain D vars bound).transitionSeq z s) := by
  intro n
  induction n with
  | zero =>
      intro ls z s hlen _ _ _ _
      have hz : z = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
      subst hz
      exact Or.inl rfl
  | succ n ih =>
      intro ls z s hlen hinv hclean hsched happ
      by_cases hz : z = []
      · subst hz; exact Or.inl rfl
      obtain ⟨p, z', ls', S, S', tt, rfl, hp, hsch', hinv', hprov, hclean', hr0, hr2, ht⟩ :=
        exists_block hvars hdisj hinv hclean hsched happ hz
      have happ' : (domain D vars bound).SeqApplicable z'
          ((domain D vars bound).transitionSeq p s) :=
        ((ActionModel.seqApplicable_append _ _ _ _).1 happ).2
      have hlen' : z'.length ≤ n := by
        have h1 : p.length ≠ 0 := fun hc => hp (List.length_eq_zero_iff.1 hc)
        rw [List.length_append] at hlen
        omega
      have hfin : (domain D vars bound).transitionSeq (p ++ z') s =
          (domain D vars bound).transitionSeq z' ((domain D vars bound).transitionSeq p s) :=
        ActionModel.transitionSeq_append _ _ _ _
      rcases ih hlen' hinv' hclean' hsch' happ' with heq | ⟨S₂, S₂', tt₂, hprov₂, h0, h2, htt⟩
      · refine Or.inr ⟨S, S', tt, hprov, ?_, ?_, ?_⟩ <;> rw [hfin, heq]
        exacts [hr0, hr2, ht]
      · refine Or.inr ⟨S₂, S₂', tt₂, hprov₂, ?_, ?_, ?_⟩ <;> rw [hfin]
        exacts [h0, h2, htt]

/-! ### Soundness -/

/-- **Soundness of the compilation.**  If the compiled problem is solvable, then the
proof-tuple calculus of the source domain derives a triple `(s₀, t_I, S')` whose final state
satisfies the goal of the source problem. -/
theorem provable_of_solvable_problem' (hnd : vars.Nodup) (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    {Q : Instance F A C I} {tI0 : C} (h : (problem' D Q vars bound tI0).Solvable) :
    ∃ S' : Set F, D.Provable Q.init (Sum.inr tI0) S' ∧ Q.goal ⊆ S' := by
  classical
  obtain ⟨as, hnet, happ, hgoal⟩ := Problem.solvable_iff_netYield.1 h
  obtain ⟨m₁, m₂, as₁, as₂, -, -, hX, hT, hint⟩ :=
    (netYield_tnI_iff (D := D) (vars := vars) (bound := bound) (Q := Q) (tI0 := tI0)).1 hnet
  obtain ⟨γs, -, hγ, hIL₁⟩ :=
    exists_interleaveList_of_gridYield_replicate (D := D) (vars := vars) (bound := bound)
      isSeqTask_MEM m₁ hX
  obtain ⟨σs, -, hσ, hIL₂⟩ :=
    exists_interleaveList_of_gridYield_replicate (D := D) (vars := vars) (bound := bound)
      isSeqTask_TUPLE m₂ hT
  have hsched : Sched (γs ++ σs) as := sched_iff_interleaveList.2 (hIL₁.append hIL₂ hint)
  have hinv : ∀ l ∈ γs ++ σs, CompInv D vars bound l := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨S, S', t, rfl⟩ := yieldSeq_MEM_phases hnd (hγ l hl)
      exact Or.inl (Or.inl ⟨S, S', t, rfl⟩)
    · exact Or.inr (Or.inl (hσ l hl))
  have htaskgoal : (AcFact.task (Sum.inr tI0) : AcFact F A C) ∈
      (domain D vars bound).transitionSeq as (instance' Q tI0 vars).init :=
    hgoal (by right; rfl)
  rcases final_state_provable hvars hdisj as.length (le_refl _) hinv
    (clean_init (vars := vars) Q tI0) hsched happ with heq | ⟨S, S', tt, hprov, hr0, hr2, ht⟩
  · -- an empty plan cannot store the initial task name
    exfalso
    rw [heq] at htaskgoal
    rcases htaskgoal with hc | ⟨v, i, hc⟩ <;> exact absurd hc (by simp)
  · -- the last proof step proves the triple asked for by the goal
    have htt : Sum.inr tI0 = tt := (ht _).1 htaskgoal
    have hinitS : S = Q.init := by
      refine Set.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
      · by_contra hc
        have : (AcFact.neg v 0 : AcFact F A C) ∈
            (domain D vars bound).transitionSeq as (instance' Q tI0 vars).init :=
          hgoal (Or.inl (Or.inl (Or.inr ⟨v, ⟨hvars v, hc⟩, rfl⟩)))
        exact ((hr0 v (hvars v)).2.1 this) hv
      · exact (hr0 v (hvars v)).1.1
          (hgoal (Or.inl (Or.inl (Or.inl ⟨v, hv, rfl⟩))))
    have hgoalS : Q.goal ⊆ S' := by
      intro v hv
      exact (hr2 v (hvars v)).1.1 (hgoal (Or.inl (Or.inr ⟨v, hv, rfl⟩)))
    exact ⟨S', by rw [htt, ← hinitS]; exact hprov, hgoalS⟩

/-- **Soundness of the compilation, in terms of the source problem.**  If the compiled problem
is solvable, then the initial compound task `t_I` of the source problem can be refined into an
action sequence that is executable in the initial state and reaches the goal. -/
theorem yield_of_solvable_problem' (hnd : vars.Nodup) (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    {Q : Instance F A C I} {tI0 : C} (h : (problem' D Q vars bound tI0).Solvable) :
    ∃ as : List A, D.Yield (Sum.inr tI0) as ∧ D.SeqApplicable as Q.init ∧
      Q.goal ⊆ D.transitionSeq as Q.init := by
  obtain ⟨S', hprov, hg⟩ := provable_of_solvable_problem' hnd hvars hdisj h
  obtain ⟨as, hy, happ, htr⟩ := (Domain.provable_iff_yield _ _ _).1 hprov
  exact ⟨as, hy, happ, by rw [htr]; exact hg⟩

/-- **Correctness of the TO-HTN ⟶ HTN-AC compilation.**  The initial compound task of the
source problem can be refined into a plan reaching the goal exactly when the compiled problem
is solvable — as soon as the compiled problem provides enough memory cells and proof steps.

The source domain is assumed to be binary (every method has exactly two subtasks), the facts of
the source problem are assumed to be enumerated without repetition by `vars`, and no action
adds and deletes the same fact. -/
theorem solvable_problem'_iff (hnd : vars.Nodup) (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ x y, xs = [x, y])
    {Q : Instance F A C I} {tI0 : C} :
    (∃ N : ℕ, ∀ bnd : ℕ, N ≤ bnd → (problem' D Q vars bnd tI0).Solvable) ↔
      ∃ as : List A, D.Yield (Sum.inr tI0) as ∧ D.SeqApplicable as Q.init ∧
        Q.goal ⊆ D.transitionSeq as Q.init := by
  constructor
  · rintro ⟨N, hN⟩
    exact yield_of_solvable_problem' hnd hvars hdisj (hN N (le_refl N))
  · rintro ⟨as, hy, happ, hg⟩
    exact solvable_problem'_of_yield hvars hdisj hbin hy happ hg

end ToAc

end HTN
