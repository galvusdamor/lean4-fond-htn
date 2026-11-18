import HtnComplexity.Article.StripsTI
/-!
# Short STRIPS plans

`HTN.Article.exists_short_plan`: if a STRIPS problem has a plan, it has one of length less than
`2 ^ |V|`, where `V` (`HTN.Article.StripsDesc.facts`) lists the facts of the initial state and of
the positive effects — the only facts a reachable state can contain.  A longer plan passes twice
through the same state (pigeonhole), and the loop in between can be cut out.  This is the bound
the proof of Thm. 4.3.4 relies on.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

namespace StripsDesc

/-- The facts that can ever be true: those of the initial state and of the positive effects. -/
def facts (d : StripsDesc) : List ℕ := (d.init ++ d.actions.flatMap fun a => a.2.2.2.1).dedup

/-- The number of facts. -/
def nV (d : StripsDesc) : ℕ := d.facts.length

end StripsDesc

section Short

variable (d : StripsDesc)

theorem run_append {P : Problem ℕ ℕ ℕ ℕ} : ∀ (π₁ π₂ : List ℕ) (s s' : Set ℕ),
    P.Run (π₁ ++ π₂) s s' ↔ ∃ m, P.Run π₁ s m ∧ P.Run π₂ m s' := by
  intro π₁
  induction π₁ with
  | nil => intro π₂ s s'; exact ⟨fun h => ⟨s, rfl, h⟩, fun ⟨m, hm, h⟩ => by cases hm; exact h⟩
  | cons a π₁ ih =>
    intro π₂ s s'
    rw [List.cons_append]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨m, hm, h3⟩ := (ih π₂ _ s').1 h2
      exact ⟨m, ⟨h1, hm⟩, h3⟩
    · rintro ⟨m, ⟨h1, h2⟩, h3⟩
      exact ⟨h1, (ih π₂ _ s').2 ⟨m, h2, h3⟩⟩

/-- The effects of every action lie in `V`. -/
theorem add_subset_facts (a : ℕ) :
    (d.toProbDesc.toProblem.δ a).add ⊆ {f | f ∈ d.facts} := by
  intro f hf
  show f ∈ d.facts
  change f ∈ (d.toProbDesc.δ a).add at hf
  unfold ProbDesc.δ at hf
  simp only [StripsDesc.toProbDesc, ProbDesc.actions] at hf
  split at hf
  · rename_i x hx
    have hxm := List.mem_of_find?_eq_some hx
    simp only [ActDesc.toAction, Set.mem_setOf_eq] at hf
    simp only [StripsDesc.facts, List.mem_dedup, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨x, hxm, hf⟩
  · simp at hf

/-- **Reachable states lie in `V`.** -/
theorem run_subset_facts : ∀ (π : List ℕ) (s s' : Set ℕ), d.toProbDesc.toProblem.Run π s s' →
    s ⊆ {f | f ∈ d.facts} → s' ⊆ {f | f ∈ d.facts} := by
  intro π
  induction π with
  | nil => intro s s' h hs; cases h; exact hs
  | cons a π ih =>
    intro s s' h hs
    exact ih _ _ h.2 (Set.union_subset (Set.diff_subset.trans hs) (add_subset_facts d a))

theorem init_subset_facts : {f | f ∈ d.init} ⊆ {f | f ∈ d.facts} := by
  intro f hf
  simp only [Set.mem_setOf_eq, StripsDesc.facts, List.mem_dedup, List.mem_append] at hf ⊢
  exact Or.inl hf

/-- Two subsets of `V` with the same elements of `V` are equal. -/
theorem eq_of_filter_eq [DecidablePred (· ∈ (∅ : Set ℕ))] {s t : Set ℕ} (hs : s ⊆ {f | f ∈ d.facts})
    (ht : t ⊆ {f | f ∈ d.facts}) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (h : d.facts.toFinset.filter (· ∈ s) = d.facts.toFinset.filter (· ∈ t)) : s = t := by
  ext f
  constructor
  · intro hf
    have : f ∈ d.facts.toFinset.filter (· ∈ s) := Finset.mem_filter.2 ⟨by simpa using hs hf, hf⟩
    rw [h] at this
    exact (Finset.mem_filter.1 this).2
  · intro hf
    have : f ∈ d.facts.toFinset.filter (· ∈ t) := Finset.mem_filter.2 ⟨by simpa using ht hf, hf⟩
    rw [← h] at this
    exact (Finset.mem_filter.1 this).2

/-- **A plan of length at least `2 ^ |V|` can be shortened.** -/
theorem exists_shorter {π : List ℕ} {s₀ s' : Set ℕ} (hs₀ : s₀ ⊆ {f | f ∈ d.facts})
    (hrun : d.toProbDesc.toProblem.Run π s₀ s') (hlen : 2 ^ d.nV ≤ π.length) :
    ∃ π', π'.length < π.length ∧ (∀ a ∈ π', a ∈ π) ∧ d.toProbDesc.toProblem.Run π' s₀ s' := by
  classical
  set P := d.toProbDesc.toProblem
  -- the state after `k` actions
  have hpre : ∀ k ≤ π.length, ∃ m, P.Run (π.take k) s₀ m ∧ P.Run (π.drop k) m s' := by
    intro k _
    have := hrun
    rw [← List.take_append_drop k π, run_append] at this
    exact this
  choose st hst using hpre
  let F : Fin (π.length + 1) → Finset ℕ := fun k =>
    d.facts.toFinset.filter (· ∈ st k.val (by omega))
  have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin (π.length + 1))),
      F k ∈ d.facts.toFinset.powerset := fun k _ => Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hcard : d.facts.toFinset.powerset.card < (Finset.univ : Finset (Fin (π.length + 1))).card := by
    have hnd : d.facts.Nodup := List.nodup_dedup _
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup hnd]
    unfold StripsDesc.nV at hlen; omega
  obtain ⟨i, -, j, -, hij, hF⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  wlog hlt : i < j generalizing i j
  · exact this j i (Ne.symm hij) hF.symm (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij))
  have hsub : ∀ k (hk : k ≤ π.length), st k hk ⊆ {f | f ∈ d.facts} := fun k hk =>
    run_subset_facts d _ _ _ (hst k hk).1 hs₀
  have heq : st i.val (by omega) = st j.val (by omega) :=
    eq_of_filter_eq d (hsub _ _) (hsub _ _) hF
  refine ⟨π.take i ++ π.drop j, ?_, fun a ha => ?_, ?_⟩
  · simp only [List.length_append, List.length_take, List.length_drop]
    have := j.2; omega
  · rcases List.mem_append.1 ha with ha | ha
    · exact List.mem_of_mem_take ha
    · exact List.mem_of_mem_drop ha
  · rw [run_append]
    exact ⟨_, (hst i (by omega)).1, heq ▸ (hst j (by omega)).2⟩

/-- **Short plans** (`< 2 ^ |V|` actions). -/
theorem exists_short_plan (h : d.Solvable) :
    ∃ π : List ℕ, π.length < 2 ^ d.nV ∧ (∀ a ∈ π, d.toProbDesc.Declared a) ∧
      ∃ s, d.toProbDesc.toProblem.Run π {f | f ∈ d.init} s ∧ d.toProbDesc.toProblem.GoalState s := by
  obtain ⟨π, hdec, s, hrun, hg⟩ := h
  induction hn : π.length using Nat.strong_induction_on generalizing π with
  | _ n ih =>
    by_cases hlen : π.length < 2 ^ d.nV
    · exact ⟨π, hlen, hdec, s, hrun, hg⟩
    · obtain ⟨π', hlt, hmem, hrun'⟩ := exists_shorter d (init_subset_facts d) hrun (by omega)
      exact ih π'.length (by omega) π' (fun a ha => hdec a (hmem a ha)) hrun' rfl

end Short

end Article

end HTN
