import HtnPlanning.Computable.Syntax
/-!
# Problems without hierarchy and with an unordered initial task network

`HTN.Article.flatTn k` describes the task network of `k` unordered primitive tasks, the task `i`
labelled with the action `i`.  For a domain description without methods,

* **`HTN.Article.solvable_flat_iff`** — the problem with initial task network `flatTn k` is
  solvable iff some ordering of the actions `0, …, k - 1` is executable from the initial state
  and reaches the goal.
-/

namespace HTN

namespace Article

open Syn

/-- `k` unordered primitive tasks, the task `i` labelled with the action `i`. -/
def flatTn (k : ℕ) : TnDesc := (List.range k, [], (List.range k).map fun i => (i, false, i))

theorem label_flatTn {k i : ℕ} (hi : i < k) : (flatTn k).label i = Sum.inl i := by
  unfold TnDesc.label TnDesc.lbl flatTn
  · have : ((List.range k).map fun i => (i, false, i)).lookup i = some (false, i) := by
      have key : ∀ l : List ℕ, i ∈ l → (l.map fun i => (i, false, i)).lookup i = some (false, i) := by
        intro l hl
        induction l with
        | nil => simp at hl
        | cons x l ih =>
          rw [List.map_cons, List.lookup_cons]
          by_cases hx : i = x
          · subst hx; simp
          · rw [show (i == x) = false by simp [hx]]
            exact ih ((List.mem_cons.1 hl).resolve_left hx)
      exact key _ (List.mem_range.2 hi)
    simp [this]

theorem not_ord_flatTn {k a b : ℕ} : ¬ (flatTn k).toTaskNetwork.ord a b := by
  rintro ⟨-, -, h, -⟩
  induction h with
  | single h => simp [TnDesc.listRel, TnDesc.ordList, flatTn] at h
  | tail _ h _ => simp [TnDesc.listRel, TnDesc.ordList, flatTn] at h

/-- **Plan existence without methods, from an unordered network of actions.** -/
theorem solvable_flat_iff {d : DomDesc} (hm : d.methods = []) (init goal : List ℕ) (k : ℕ) :
    Syn.Solvable d (init, goal, flatTn k) ↔
      ∃ l : List ℕ, l.Perm (List.range k) ∧
        (problem d (init, goal, flatTn k)).SeqApplicable l {f | f ∈ init} ∧
        {f | f ∈ goal} ⊆ (problem d (init, goal, flatTn k)).transitionSeq l {f | f ∈ init} := by
  set P := problem d (init, goal, flatTn k)
  have hreach : ∀ tn, P.Reachable tn → tn = P.tnI := by
    intro tn h
    induction h with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨t, m, hm', -⟩ := hs
      exfalso
      obtain ⟨e, he, -⟩ := hm'
      simp [DomDesc.toDomain, hm] at he
  constructor
  · rintro ⟨tn, hr, -, l, as, hl, has, happ, hgoal⟩
    obtain rfl := hreach tn hr
    have hmem : ∀ i ∈ l, i < k := fun i hi => by
      have := (hl.2.1 i).1 hi
      simpa [P, problem, Domain.mkProblem, InstDesc.toInstance, InstDesc.tnI, flatTn, TnDesc.ids]
        using this
    have hlab : l.map P.tnI.α = l.map Sum.inl := by
      refine List.map_congr_left fun i hi => ?_
      show (flatTn k).label i = _
      exact label_flatTn (hmem i hi)
    have has' : as = l := by
      have : as.map Sum.inl = l.map (Sum.inl : ℕ → ℕ ⊕ ℕ) := by rw [← has, hlab]
      exact List.map_injective_iff.2 Sum.inl_injective this
    subst has'
    refine ⟨as, ?_, happ, hgoal⟩
    refine (List.perm_ext_iff_of_nodup hl.1 List.nodup_range).2 fun i => ?_
    rw [hl.2.1 i]
    simp [P, problem, Domain.mkProblem, InstDesc.toInstance, InstDesc.tnI, flatTn, TnDesc.ids]
  · rintro ⟨l, hl, happ, hgoal⟩
    refine ⟨P.tnI, Relation.ReflTransGen.refl, ?_, l, l, ⟨hl.nodup_iff.2 List.nodup_range, ?_, ?_⟩,
      ?_, happ, hgoal⟩
    · intro i hi
      have : i < k := by
        simpa [P, problem, Domain.mkProblem, InstDesc.toInstance, InstDesc.tnI, flatTn, TnDesc.ids]
          using hi
      exact ⟨i, label_flatTn this⟩
    · intro i
      rw [hl.mem_iff]
      simp [P, problem, Domain.mkProblem, InstDesc.toInstance, InstDesc.tnI, flatTn, TnDesc.ids]
    · exact List.Pairwise.imp (fun _ => not_ord_flatTn) (List.pairwise_of_forall (fun _ _ => trivial))
    · show l.map (flatTn k).label = l.map Sum.inl
      exact List.map_congr_left fun i hi => label_flatTn (List.mem_range.1 (hl.mem_iff.1 hi))

end Article

end HTN
