import HtnPlanning.Regular.RegularStructure
import HtnPlanning.Progression.Progression
/-!
# Regular problems have boundedly many open tasks

A *regular* method (Def. 3.3) has at most one compound subtask, and that subtask is ordered
after all the others.  Consequently a compound task behaves like a **finite-state process**
rather than like a stack: while its refinement is running, the tasks it has produced are a
single body — at most `m` of them — and the next refinement step can only happen once all the
primitive tasks of that body have been executed, because the compound subtask is ordered last.

Finitely many such processes, running side by side, therefore keep the task network small.
This file makes that precise and proves it, for an arbitrary (partially ordered) task network:

* `HTN.TaskNetwork.SlotBound tn own K m` — the *slot invariant*: the ownership map `own`
  assigns every task of `tn` a slot below `K`, every slot carries at most `m` tasks, and every
  compound task is ordered after all the other tasks of its own slot;
* `HTN.TaskNetwork.SlotBounded.card_le` — a network with the slot invariant has at most
  `m * K` tasks;
* `HTN.TaskNetwork.SlotBound.progress` and `HTN.TaskNetwork.SlotBound.decomposeWith` — **the
  invariant is preserved** by the two operations of the progression search, the second one for
  a *regular* subtask network of at most `m` tasks, which is inserted into the slot of the task
  it decomposes.

The decomposition case is where regularity enters twice: the decomposed task `t` is
unconstrained, so — by the invariant — its slot contains nothing but `t` itself and the
inserted body has the slot to itself; and the body is regular, so its own compound task is
ordered after the rest of the body, which re-establishes the invariant.
-/

namespace HTN

universe u v w x

variable {I : Type x} {A : Type v} {C : Type w}

namespace TaskNetwork

variable [DecidableEq I]

omit [DecidableEq I] in
/-- Regularity is transported along an isomorphism. -/
theorem Iso.isRegular {tn tn' : TaskNetwork I A C} (h : tn.Iso tn') (h' : tn'.IsRegular) :
    tn.IsRegular := by
  obtain ⟨σ, hbij, hord, hα⟩ := h
  refine ⟨Iso.subsingletonAbstract ⟨σ, hbij, hord, hα⟩ h'.1, ?_⟩
  intro t ht habs t' ht' hne
  have hσt : σ t ∈ tn'.T := by simpa using hbij.mapsTo (by simpa using ht)
  have hσt' : σ t' ∈ tn'.T := by simpa using hbij.mapsTo (by simpa using ht')
  have hne' : σ t' ≠ σ t := fun hc =>
    hne (hbij.injOn (by simpa using ht') (by simpa using ht) hc)
  exact (hord t' ht' t ht).2 (h'.2 (σ t) hσt ((Iso.isAbstractId hα ht).1 habs) (σ t') hσt' hne')

/-- **The slot invariant.**  `own` distributes the tasks of `tn` over the slots `0, …, K - 1`,
at most `m` tasks per slot, in such a way that a compound task is ordered after every other task
of its slot. -/
structure SlotBound (tn : TaskNetwork I A C) (own : I → ℕ) (K m : ℕ) : Prop where
  /-- Every task has a slot below `K`. -/
  lt : ∀ t ∈ tn.T, own t < K
  /-- Every slot carries at most `m` tasks. -/
  fiber : ∀ s : ℕ, (tn.T.filter (fun t => own t = s)).card ≤ m
  /-- A compound task is ordered after every other task of its slot. -/
  last : ∀ c ∈ tn.T, tn.IsAbstractId c → ∀ x ∈ tn.T, x ≠ c → own x = own c → tn.ord x c

/-- A task network is *slot bounded* by `K` slots of `m` tasks iff some ownership map satisfies
the slot invariant. -/
def SlotBounded (tn : TaskNetwork I A C) (K m : ℕ) : Prop := ∃ own, SlotBound tn own K m

omit [DecidableEq I] in
/-- **A slot bounded task network has at most `m * K` tasks.** -/
theorem SlotBounded.card_le {tn : TaskNetwork I A C} {K m : ℕ} (h : SlotBounded tn K m) :
    tn.T.card ≤ m * K := by
  obtain ⟨own, h⟩ := h
  have h₁ : tn.T.card ≤ m * (tn.T.image own).card :=
    Finset.card_le_mul_card_image _ _ (fun a _ => h.fiber a)
  have h₂ : (tn.T.image own).card ≤ K := by
    have hsub : tn.T.image own ⊆ Finset.range K := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
      exact Finset.mem_range.2 (h.lt t ht)
    simpa using Finset.card_le_card hsub
  exact h₁.trans (Nat.mul_le_mul_left m h₂)

/-- **The slot invariant is preserved by progression**: executing a task only removes it. -/
theorem SlotBound.progress {tn : TaskNetwork I A C} {own : I → ℕ} {K m : ℕ}
    (h : SlotBound tn own K m) (t : I) : SlotBound (tn.progress t) own K m where
  lt := by
    intro x hx
    exact h.lt x (Finset.mem_of_mem_erase hx)
  fiber := by
    intro s
    refine le_trans (Finset.card_le_card ?_) (h.fiber s)
    intro x hx
    simp only [Finset.mem_filter, progress_T] at hx ⊢
    exact ⟨Finset.mem_of_mem_erase hx.1, hx.2⟩
  last := by
    intro c hc habs x hx hxc hown
    have hc' : c ∈ tn.T := Finset.mem_of_mem_erase hc
    have hx' : x ∈ tn.T := Finset.mem_of_mem_erase hx
    have hxt : x ≠ t := Finset.ne_of_mem_erase hx
    exact ⟨h.last c hc' habs x hx' hxc hown, hxt⟩

/-- **The slot invariant is preserved by decomposition** of an unconstrained compound task `t`
by a *regular* subtask network `u` of at most `m` tasks: the body is inserted into the slot
of `t`, which the invariant guarantees to be free. -/
theorem SlotBound.decompose {tn u : TaskNetwork I A C} {own : I → ℕ} {K m : ℕ} {t : I}
    (h : SlotBound tn own K m) (hu : tn.Unconstrained t) (habs : tn.IsAbstractId t)
    (hreg : u.IsRegular) (hcard : u.T.card ≤ m) :
    SlotBound (HTN.decomposeWith tn t u) (fun x => if x ∈ u.T then own t else own x) K m := by
  classical
  have htT : t ∈ tn.T := hu.1
  -- the slot of `t` contains nothing but `t`
  have hfree : ∀ x ∈ tn.T, x ≠ t → own x ≠ own t := by
    intro x hx hxt hown
    exact hu.2 x hx (h.last t htT habs x hx hxt hown)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases hxu : x ∈ u.T
    · simpa [hxu] using h.lt t htT
    · rcases mem_decomposeWith_T.1 hx with ⟨hx₁, -⟩ | hx₂
      · simpa [hxu] using h.lt x hx₁
      · exact absurd hx₂ hxu
  · intro s
    by_cases hs : s = own t
    · subst hs
      have hset : (HTN.decomposeWith tn t u).T.filter
          (fun x => (if x ∈ u.T then own t else own x) = own t) = u.T := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, hown⟩
          by_cases hxu : x ∈ u.T
          · exact hxu
          · rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx₂
            · rw [if_neg hxu] at hown
              exact absurd hown (hfree x hx₁ hxt)
            · exact absurd hx₂ hxu
        · intro hxu
          exact ⟨mem_decomposeWith_T.2 (Or.inr hxu), by simp [hxu]⟩
      rw [hset]
      exact hcard
    · refine le_trans (Finset.card_le_card ?_) (h.fiber s)
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      obtain ⟨hxT, hown⟩ := hx
      have hxu : x ∉ u.T := by
        intro hxu
        rw [if_pos hxu] at hown
        exact hs hown.symm
      rw [if_neg hxu] at hown
      rcases mem_decomposeWith_T.1 hxT with ⟨hx₁, -⟩ | hx₂
      · exact ⟨hx₁, hown⟩
      · exact absurd hx₂ hxu
  · intro c hc habsc x hx hxc hown
    by_cases hcu : c ∈ u.T
    · -- the compound task lies in the inserted body
      have habsu : u.IsAbstractId c := by
        obtain ⟨n, hn⟩ := habsc
        exact ⟨n, by simpa [hcu] using hn⟩
      by_cases hxu : x ∈ u.T
      · exact Or.inl (hreg.2 c hcu habsu x hxu hxc)
      · rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx₂
        · have hownx : own x = own t := by simpa [hxu, hcu] using hown
          exact Or.inr (Or.inl ⟨h.last t htT habs x hx₁ hxt hownx, hcu⟩)
        · exact absurd hx₂ hxu
    · -- the compound task is an old task
      have hc₁ : c ∈ tn.T ∧ c ≠ t := by
        rcases mem_decomposeWith_T.1 hc with h' | h'
        · exact h'
        · exact absurd h' hcu
      have habsc' : tn.IsAbstractId c := by
        obtain ⟨n, hn⟩ := habsc
        exact ⟨n, by simpa [hcu] using hn⟩
      by_cases hxu : x ∈ u.T
      · -- impossible: `c` would be in the slot of `t`, hence ordered both ways with `t`
        exfalso
        have hownc : own c = own t := by simpa [hxu, hcu] using hown.symm
        exact hfree c hc₁.1 hc₁.2 hownc
      · rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx₂
        · have hownx : own x = own c := by simpa [hxu, hcu] using hown
          exact Or.inr (Or.inr (Or.inr
            ⟨h.last c hc₁.1 habsc' x hx₁ hxc hownx, hxt, hc₁.2⟩))
        · exact absurd hx₂ hxu

end TaskNetwork

end HTN
