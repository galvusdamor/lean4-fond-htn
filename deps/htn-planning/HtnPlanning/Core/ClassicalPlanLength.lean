import HtnPlanning.Core.Classical
/-!
# Short plans for classical planning problems

A solvable classical (STRIPS) planning problem over a finite set of facts has a solution that
visits every state at most once, hence a solution of length less than `2 ^ |F|`: the number of
states.  This is the standard "loop removal" argument.

* `HTN.ClassicalProblem.IsSolution.cut` — cutting a loop out of a solution again gives a
  solution;
* `HTN.ClassicalProblem.exists_solution_length_lt` — a solvable problem over a finite fact type
  has a solution of length `< 2 ^ |F|`.

The bound is what makes the compilation of classical planning problems into *acyclic* HTN
problems work (`HtnComplexity/ToHtnAc/StripsToAc.lean`): an acyclic hierarchy of `|F|` levels of
compound tasks, each of which splits into two tasks of the next lower level, can generate every
action sequence of length at most `2 ^ |F|`.
-/

namespace HTN

universe u v

namespace ClassicalProblem

variable {F : Type u} {A : Type v} (P : ClassicalProblem F A)

/-- **Loop removal.**  If the states reached after the first `i` and after the first `j` steps
of a solution coincide, then the actions between them may be dropped. -/
theorem IsSolution.cut {plan : List A} (h : P.IsSolution plan) {i j : ℕ} (hij : i ≤ j)
    (hst : P.transitionSeq (plan.take i) P.init = P.transitionSeq (plan.take j) P.init) :
    P.IsSolution (plan.take i ++ plan.drop j) := by
  obtain ⟨happ, hgoal⟩ := h
  -- `plan.take j` splits as `plan.take i` followed by the part in between
  have hsplit : plan.take j = plan.take i ++ (plan.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (plan.take j)]
    rw [List.take_take, Nat.min_eq_left hij]
  have happj : P.SeqApplicable (plan.take j) P.init ∧
      P.SeqApplicable (plan.drop j) (P.transitionSeq (plan.take j) P.init) := by
    rw [← P.seqApplicable_append]
    simpa using happ
  have happi : P.SeqApplicable (plan.take i) P.init := by
    have := happj.1
    rw [hsplit, P.seqApplicable_append] at this
    exact this.1
  have hend : P.transitionSeq (plan.take i ++ plan.drop j) P.init =
      P.transitionSeq plan P.init := by
    rw [P.transitionSeq_append, hst, ← P.transitionSeq_append, List.take_append_drop]
  refine ⟨?_, ?_⟩
  · rw [P.seqApplicable_append]
    exact ⟨happi, by rw [hst]; exact happj.2⟩
  · rw [hend]; exact hgoal

variable {P}

/-- A solvable problem has a solution of minimal length. -/
theorem exists_solution_minimal (h : P.Solvable) :
    ∃ plan, P.IsSolution plan ∧ ∀ q : List A, P.IsSolution q → plan.length ≤ q.length := by
  classical
  set S : Set ℕ := {n | ∃ q : List A, P.IsSolution q ∧ q.length = n} with hS
  obtain ⟨plan₀, hplan₀⟩ := h
  have hne : S.Nonempty := ⟨plan₀.length, plan₀, hplan₀, rfl⟩
  obtain ⟨plan, hplan, hlen⟩ := Nat.sInf_mem hne
  refine ⟨plan, hplan, fun q hq => ?_⟩
  rw [hlen]
  exact Nat.sInf_le ⟨q, hq, rfl⟩

/-- **A solvable classical planning problem has a short solution.**  Over a finite set of facts
`F` there are `2 ^ |F|` states, and a shortest solution visits each of them at most once, so it
has length less than `2 ^ |F|`. -/
theorem exists_solution_length_lt [Fintype F] (h : P.Solvable) :
    ∃ plan : List A, P.IsSolution plan ∧ plan.length < 2 ^ Fintype.card F := by
  classical
  obtain ⟨plan, hplan, hmin⟩ := exists_solution_minimal h
  refine ⟨plan, hplan, ?_⟩
  by_contra hcon
  push_neg at hcon
  -- the states visited by the plan, indexed by the number of steps taken
  set g : Fin (plan.length + 1) → Set F :=
    fun i => P.transitionSeq (plan.take i) P.init with hg
  have hcard : Fintype.card (Set F) < Fintype.card (Fin (plan.length + 1)) := by
    have : Fintype.card (Set F) = 2 ^ Fintype.card F := by
      simp [Fintype.card_set]
    rw [this, Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  -- order the two indices
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hsol := IsSolution.cut P hplan (i := (i : ℕ)) (j := (j : ℕ)) hlt.le hgij
    have hle := hmin _ hsol
    have hj : (j : ℕ) ≤ plan.length := by omega
    simp only [List.length_append, List.length_take, List.length_drop] at hle
    have hi : (i : ℕ) ≤ plan.length := by omega
    omega
  · have hsol := IsSolution.cut P hplan (i := (j : ℕ)) (j := (i : ℕ)) hlt.le hgij.symm
    have hle := hmin _ hsol
    have hi : (i : ℕ) ≤ plan.length := by omega
    simp only [List.length_append, List.length_take, List.length_drop] at hle
    have hj : (j : ℕ) ≤ plan.length := by omega
    omega

end ClassicalProblem

end HTN
