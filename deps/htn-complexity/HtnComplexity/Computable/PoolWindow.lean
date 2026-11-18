import HtnComplexity.Computable.Window
/-!
# The window of a *pool* of facts

`HtnComplexity/Computable/Window.lean` measures how much of a rooted instance description a
*fixed* domain description can read: its profile over `HTN.Syn.DomDesc.domFacts`.  The counting
argument of `HtnCompilability/Computable/NoVocCompilation.lean` needs the same statement for
**many domain descriptions at once**, and what they then share is not their fact list but a
common *pool* of facts containing all of them.

* `HTN.Syn.rootName_isStrips` — a `STRIPS` instance description has the root name `0`, so the
  root component of the profile carries nothing;
* `HTN.Syn.solvable_strips_pool_congr` — two `STRIPS` instance descriptions that agree on the
  pool `P`, and on whether their goal facts outside `P` already hold, are indistinguishable by
  *every* domain description whose facts lie in `P`;
* `HTN.Syn.poolProfile` and `HTN.Syn.solvable_of_poolProfile_eq` — the same as a function into a
  type of `2 ^ (2 * |P| + 1)` values (`HTN.Syn.card_poolProfile`).

So a pool of `p` facts sorts all `STRIPS` instance descriptions into at most `2 ^ (2 * p + 1)`
classes, *uniformly* in the domain description that reads them.
-/

namespace HTN

namespace Syn

/-- The root name of a `STRIPS` instance description is `0`. -/
theorem rootName_isStrips {q : InstDesc} (h : q.IsStrips) : rootName q = 0 := by
  obtain ⟨t, hT, hα⟩ := h
  obtain ⟨t', hT', hα'⟩ := InstDesc.rootName_spec (InstDesc.IsStrips.isRooted ⟨t, hT, hα⟩)
  have htt : t' = t := by
    have : ({t'} : Finset ℕ) = {t} := by rw [← hT', hT]
    simpa using this
  subst htt
  rw [hα] at hα'
  exact (Sum.inr.inj hα').symm

/-- **Two `STRIPS` instance descriptions that agree on a pool of facts** are indistinguishable by
every domain description whose facts lie in the pool. -/
theorem solvable_strips_pool_congr (d : DomDesc) (P : List ℕ) (hdP : ∀ f ∈ d.domFacts, f ∈ P)
    {q q' : InstDesc} (hq : q.IsStrips) (hq' : q'.IsStrips)
    (hinit : ∀ f ∈ P, (f ∈ q.initList ↔ f ∈ q'.initList))
    (hgoal : ∀ f ∈ P, (f ∈ q.goalList ↔ f ∈ q'.goalList))
    (hout : (∀ f ∈ q.goalList, f ∉ P → f ∈ q.initList) ↔
      (∀ f ∈ q'.goalList, f ∉ P → f ∈ q'.initList)) :
    Solvable d q ↔ Solvable d q' := by
  have key : ∀ x : InstDesc, (∀ f ∈ x.goalList, f ∉ d.domFacts → f ∈ x.initList) ↔
      ((∀ f ∈ x.goalList, f ∉ P → f ∈ x.initList) ∧
        ∀ f ∈ x.goalList, f ∈ P → f ∉ d.domFacts → f ∈ x.initList) := by
    intro x
    constructor
    · intro h
      exact ⟨fun f hf hnp => h f hf (fun hd => hnp (hdP f hd)), fun f hf _ hnd => h f hf hnd⟩
    · rintro ⟨h1, h2⟩ f hf hnd
      by_cases hp : f ∈ P
      · exact h2 f hf hp hnd
      · exact h1 f hf hp
  refine solvable_rooted_congr d (InstDesc.IsStrips.isRooted hq) (InstDesc.IsStrips.isRooted hq')
    (by rw [rootName_isStrips hq, rootName_isStrips hq'])
    (fun f hf => hinit f (hdP f hf)) (fun f hf => hgoal f (hdP f hf)) ?_
  rw [key q, key q']
  refine and_congr hout ⟨fun h f hf hp hnd => ?_, fun h f hf hp hnd => ?_⟩
  · exact (hinit f hp).1 (h f ((hgoal f hp).2 hf) hp hnd)
  · exact (hinit f hp).2 (h f ((hgoal f hp).1 hf) hp hnd)

/-- **The profile of an instance description over a pool of facts**: which facts of the pool hold
initially, which of them are goals, and whether the goal facts outside the pool already hold. -/
def poolProfile (P : List ℕ) (q : InstDesc) :
    (Fin P.length → Bool) × (Fin P.length → Bool) × Bool :=
  (fun k => decide (P[k] ∈ q.initList), fun k => decide (P[k] ∈ q.goalList),
    decide (∀ f ∈ q.goalList, f ∉ P → f ∈ q.initList))

/-- **A domain description whose facts lie in a pool sees a `STRIPS` instance description only
through its profile over the pool.** -/
theorem solvable_of_poolProfile_eq (d : DomDesc) (P : List ℕ) (hdP : ∀ f ∈ d.domFacts, f ∈ P)
    {q q' : InstDesc} (hq : q.IsStrips) (hq' : q'.IsStrips)
    (h : poolProfile P q = poolProfile P q') : Solvable d q ↔ Solvable d q' := by
  have hI := congrArg (fun x => x.1) h
  have hG := congrArg (fun x => x.2.1) h
  have hB := congrArg (fun x => x.2.2) h
  simp only [poolProfile] at hI hG hB
  have hmem : ∀ f ∈ P, ∃ k : Fin P.length, P[k] = f := by
    intro f hf
    obtain ⟨k, hk, hkf⟩ := List.getElem_of_mem hf
    exact ⟨⟨k, hk⟩, hkf⟩
  refine solvable_strips_pool_congr d P hdP hq hq' (fun f hf => ?_) (fun f hf => ?_) ?_
  · obtain ⟨k, rfl⟩ := hmem f hf
    simpa using congrFun hI k
  · obtain ⟨k, rfl⟩ := hmem f hf
    simpa using congrFun hG k
  · simpa using hB

/-- **The window of a pool**: a pool of `p` facts sorts the `STRIPS` instance descriptions into
at most `2 ^ (2 * p + 1)` classes. -/
theorem card_poolProfile (P : List ℕ) :
    Fintype.card ((Fin P.length → Bool) × (Fin P.length → Bool) × Bool)
      = 2 ^ (2 * P.length + 1) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    two_mul, pow_add, pow_one]
  ring

end Syn

end HTN
