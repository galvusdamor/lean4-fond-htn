import HtnComplexity.Article.StripsShort
/-!
# Short runs and short gaps

The states reached from the initial state of a description lie in the list `V`
(`HTN.Article.pfacts`) of the facts of the initial state and of the positive effects, so a run
passes through at most `2 ^ |V|` states.

* `HTN.Article.exists_short_run` — a run can be shortened to fewer than `2 ^ |V|` actions, all
  taken from the original run;
* **`HTN.Article.exists_short_gaps`** — the *gap lemma* used for TIHTN planning (Thms. 4.2.6,
  Cor. 4.2.7): if the run `π` contains `as` as a subsequence, the actions between consecutive
  actions of `as` can be shortened as well; the result still contains `as` and is at most
  `(|as| + 1) · 2 ^ |V|` long.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-- The facts that can ever be true in a run from the initial state. -/
def pfacts (p : ProbDesc) : List ℕ := (p.init ++ p.actions.flatMap fun a => a.2.2.2.1).dedup

theorem add_subset_pfacts (p : ProbDesc) (a : ℕ) :
    (p.toProblem.δ a).add ⊆ {f | f ∈ pfacts p} := by
  intro f hf
  show f ∈ pfacts p
  change f ∈ (p.δ a).add at hf
  unfold ProbDesc.δ at hf
  split at hf
  · rename_i x hx
    have hxm := List.mem_of_find?_eq_some hx
    simp only [ActDesc.toAction, Set.mem_setOf_eq] at hf
    simp only [pfacts, List.mem_dedup, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨x, hxm, hf⟩
  · simp at hf

theorem apply_subset_pfacts (p : ProbDesc) (a : ℕ) {s : Set ℕ} (hs : s ⊆ {f | f ∈ pfacts p}) :
    (p.toProblem.δ a).apply s ⊆ {f | f ∈ pfacts p} :=
  Set.union_subset (Set.diff_subset.trans hs) (add_subset_pfacts p a)

theorem run_subset_pfacts (p : ProbDesc) : ∀ (π : List ℕ) (s s' : Set ℕ), p.toProblem.Run π s s' →
    s ⊆ {f | f ∈ pfacts p} → s' ⊆ {f | f ∈ pfacts p} := by
  intro π
  induction π with
  | nil => intro s s' h hs; cases h; exact hs
  | cons a π ih => intro s s' h hs; exact ih _ _ h.2 (apply_subset_pfacts p a hs)

theorem init_subset_pfacts (p : ProbDesc) : p.toProblem.init ⊆ {f | f ∈ pfacts p} := by
  intro f hf
  change f ∈ p.init at hf
  simp only [Set.mem_setOf_eq, pfacts, List.mem_dedup, List.mem_append]
  exact Or.inl hf

/-- **A run of at least `2 ^ |V|` actions can be shortened.** -/
theorem exists_shorter_run (p : ProbDesc) {π : List ℕ} {s₀ s' : Set ℕ}
    (hs₀ : s₀ ⊆ {f | f ∈ pfacts p}) (hrun : p.toProblem.Run π s₀ s')
    (hlen : 2 ^ (pfacts p).length ≤ π.length) :
    ∃ π', π'.length < π.length ∧ (∀ a ∈ π', a ∈ π) ∧ p.toProblem.Run π' s₀ s' := by
  classical
  set P := p.toProblem
  have hpre : ∀ k ≤ π.length, ∃ m, P.Run (π.take k) s₀ m ∧ P.Run (π.drop k) m s' := by
    intro k _
    have := hrun
    rw [← List.take_append_drop k π, run_append] at this
    exact this
  choose st hst using hpre
  let F : Fin (π.length + 1) → Finset ℕ := fun k =>
    (pfacts p).toFinset.filter (· ∈ st k.val (by omega))
  have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin (π.length + 1))),
      F k ∈ (pfacts p).toFinset.powerset :=
    fun k _ => Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hcard : (pfacts p).toFinset.powerset.card <
      (Finset.univ : Finset (Fin (π.length + 1))).card := by
    have hnd : (pfacts p).Nodup := List.nodup_dedup _
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup hnd]
    omega
  obtain ⟨i, -, j, -, hij, hF⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  wlog hlt : i < j generalizing i j
  · exact this j i (Ne.symm hij) hF.symm (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij))
  have hsub : ∀ k (hk : k ≤ π.length), st k hk ⊆ {f | f ∈ pfacts p} := fun k hk =>
    run_subset_pfacts p _ _ _ (hst k hk).1 hs₀
  have heq : st i.val (by omega) = st j.val (by omega) := by
    ext f
    constructor
    · intro hf
      have : f ∈ F i := Finset.mem_filter.2 ⟨by simpa using hsub _ _ hf, hf⟩
      rw [hF] at this
      exact (Finset.mem_filter.1 this).2
    · intro hf
      have : f ∈ F j := Finset.mem_filter.2 ⟨by simpa using hsub _ _ hf, hf⟩
      rw [← hF] at this
      exact (Finset.mem_filter.1 this).2
  refine ⟨π.take i ++ π.drop j, ?_, fun a ha => ?_, ?_⟩
  · simp only [List.length_append, List.length_take, List.length_drop]
    have := j.2; omega
  · rcases List.mem_append.1 ha with ha | ha
    · exact List.mem_of_mem_take ha
    · exact List.mem_of_mem_drop ha
  · rw [run_append]
    exact ⟨_, (hst i (by omega)).1, heq ▸ (hst j (by omega)).2⟩

/-- **Short runs** (`< 2 ^ |V|` actions). -/
theorem exists_short_run (p : ProbDesc) {s₀ s' : Set ℕ} (hs₀ : s₀ ⊆ {f | f ∈ pfacts p}) :
    ∀ π : List ℕ, p.toProblem.Run π s₀ s' →
      ∃ π', π'.length < 2 ^ (pfacts p).length ∧ (∀ a ∈ π', a ∈ π) ∧ p.toProblem.Run π' s₀ s' := by
  intro π hrun
  induction hn : π.length using Nat.strong_induction_on generalizing π with
  | _ n ih =>
    by_cases hlen : π.length < 2 ^ (pfacts p).length
    · exact ⟨π, hlen, fun a ha => ha, hrun⟩
    · obtain ⟨π', hlt, hmem, hrun'⟩ := exists_shorter_run p hs₀ hrun (by omega)
      obtain ⟨π'', h1, h2, h3⟩ := ih π'.length (by omega) π' hrun' rfl
      exact ⟨π'', h1, fun a ha => hmem a (h2 a ha), h3⟩

theorem exists_split_of_cons_sublist {a : ℕ} {l : List ℕ} :
    ∀ {π : List ℕ}, (a :: l).Sublist π → ∃ π₀ π₁, π = π₀ ++ a :: π₁ ∧ l.Sublist π₁
  | [], h => by simp at h
  | b :: π, h => by
    cases h with
    | cons _ h =>
      obtain ⟨π₀, π₁, rfl, h'⟩ := exists_split_of_cons_sublist h
      exact ⟨b :: π₀, π₁, rfl, h'⟩
    | cons₂ _ h => exact ⟨[], π, rfl, h⟩

/-- **The gap lemma**: a run containing `as` as a subsequence can be shortened to at most
`(|as| + 1) · 2 ^ |V|` actions, all from the original run, still containing `as`. -/
theorem exists_short_gaps (p : ProbDesc) : ∀ (as π : List ℕ) {s₀ s' : Set ℕ},
    s₀ ⊆ {f | f ∈ pfacts p} → as.Sublist π → p.toProblem.Run π s₀ s' →
    ∃ π', as.Sublist π' ∧ π'.length ≤ (as.length + 1) * 2 ^ (pfacts p).length ∧
      (∀ a ∈ π', a ∈ π) ∧ p.toProblem.Run π' s₀ s' := by
  intro as
  induction as with
  | nil =>
    intro π s₀ s' hs₀ _ hrun
    obtain ⟨π', h1, h2, h3⟩ := exists_short_run p hs₀ π hrun
    exact ⟨π', List.nil_sublist _, by simp; omega, h2, h3⟩
  | cons a as ih =>
    intro π s₀ s' hs₀ hsub hrun
    obtain ⟨π₀, π₁, rfl, hsub'⟩ := exists_split_of_cons_sublist hsub
    obtain ⟨m, hm₀, hm₁⟩ := (run_append π₀ (a :: π₁) s₀ s').1 hrun
    obtain ⟨π₀', h01, h02, h03⟩ := exists_short_run p hs₀ π₀ hm₀
    have hm : m ⊆ {f | f ∈ pfacts p} := run_subset_pfacts p _ _ _ hm₀ hs₀
    obtain ⟨happ, hr₁⟩ := hm₁
    obtain ⟨π₁', h11, h12, h13, h14⟩ := ih π₁ (apply_subset_pfacts p a hm) hsub' hr₁
    refine ⟨π₀' ++ a :: π₁', ?_, ?_, fun b hb => ?_, ?_⟩
    · exact (List.cons_sublist_cons.2 h11).trans (List.sublist_append_right _ _)
    · simp only [List.length_append, List.length_cons]
      have : 1 ≤ 2 ^ (pfacts p).length := Nat.one_le_two_pow
      nlinarith
    · rcases List.mem_append.1 hb with hb | hb
      · exact List.mem_append_left _ (h02 b hb)
      · rcases List.mem_cons.1 hb with rfl | hb
        · simp
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (h13 b hb))
    · exact (run_append π₀' (a :: π₁') s₀ s').2 ⟨m, h03, happ, h14⟩

end Article

end HTN
