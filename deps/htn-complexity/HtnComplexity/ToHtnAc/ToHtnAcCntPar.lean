import HtnPlanning.Interleave.GridYield
import HtnComplexity.ToHtnAc.ToHtnAc
/-!
# The parallel counting task of the TO-HTN ⟶ HTN-AC compilation

The initial task network of the compilation of `HtnComplexity/ToHtnAc/ToHtnAc.lean` is
`𝔠^bound_MEM ∥ 𝔠^bound_TUPLE`: two *parallel* counting tasks, each of which generates up to
`bound` unordered copies of a memory cell resp. of a proof step.  Since a parallel counting task
has methods with two parallel chains, its refinements cannot be described by the totally ordered
refinement relation `HTN.Domain.YieldSeq` used in `HtnComplexity/ToHtnAc/ToHtnAcBodies.lean`; they
are described here with the interleaving refinement relation `HTN.Domain.GridYield` of
`HtnPlanning/Interleave/GridYield.lean`.

Results:

* `HTN.ToAc.chainYield_singleton_ac_iff` — a single compound task of the compiled domain refines
  exactly like the grid bodies listed in `HTN.ToAc.bodies`;
* `HTN.ToAc.gridYield_cntPar_iff` — **the parallel counting task `𝔠^k_t` refines exactly into the
  refinements of at most `k` unordered copies of `t`**; this is the unordered counterpart of
  `HTN.ToAc.yieldSeq_cnt_iff` and shows that the logarithmically many counting methods really do
  make `k` (exponentially many) parallel copies available;
* `HTN.ToAc.chainYield_tI_iff` — consequently the plans of the compiled problem are exactly the
  interleavings of the refinements of at most `bound` memory cells with those of at most `bound`
  proof steps;
* `HTN.ToAc.netYield_tnI_iff` — the same statement for the initial task network of the compiled
  problem, i.e. for its solution plans.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open TaskNetwork Domain

/-! ### Grid bodies of the compiled domain -/

/-- Every method of the compiled domain has a grid as its subtask network. -/
lemma methods_grid :
    ∀ m ∈ (domain D vars bound).methods, ∃ ls, m.subtasks = TaskNetwork.grid ls := by
  rintro ⟨c, tn⟩ ⟨ls, hls, rfl⟩
  exact ⟨ls, rfl⟩

/-- Two presentations of the same grid have the same refinements. -/
lemma gridYield_congr {ls ls' : List (List (AcAct F A C ⊕ AcTask F A C))}
    {as : List (AcAct F A C)} (h : TaskNetwork.grid ls = TaskNetwork.grid ls') :
    (domain D vars bound).GridYield ls as ↔ (domain D vars bound).GridYield ls' as := by
  rw [← netYield_grid_iff (methods_grid (D := D) (vars := vars) (bound := bound)),
    ← netYield_grid_iff (methods_grid (D := D) (vars := vars) (bound := bound)), h]

/-- **A single compound task of the compiled domain refines exactly like the grid bodies of its
methods.** -/
lemma chainYield_singleton_ac_iff {c : AcTask F A C} {as : List (AcAct F A C)} :
    (domain D vars bound).ChainYield [Sum.inr c] as ↔
      ∃ ls ∈ bodies D vars bound c, (domain D vars bound).GridYield ls as := by
  rw [chainYield_singleton_inr_iff]
  constructor
  · rintro ⟨ls, ⟨m, hm, rfl, hsub⟩, hy⟩
    obtain ⟨ls', hls', hsub'⟩ := hm
    refine ⟨ls', hls', ?_⟩
    exact (gridYield_congr (by rw [← hsub', hsub])).1 hy
  · rintro ⟨ls, hls, hy⟩
    exact ⟨ls, ⟨⟨c, TaskNetwork.grid ls⟩, ⟨ls, hls, rfl⟩, rfl, rfl⟩, hy⟩

/-! ### The bodies of the parallel counting task -/

lemma bodies_cntPar_zero {t : AcTask F A C}
    {ls : List (List (AcAct F A C ⊕ AcTask F A C))} :
    ls ∈ bodies D vars bound (AcTask.cntPar t 0) ↔ ls = [] := by
  simp [bodies]

lemma bodies_cntPar_one {t : AcTask F A C}
    {ls : List (List (AcAct F A C ⊕ AcTask F A C))} :
    ls ∈ bodies D vars bound (AcTask.cntPar t 1) ↔ ls = [[Sum.inr t]] ∨ ls = [] := by
  simp [bodies]

lemma bodies_cntPar_even {t : AcTask F A C} {k : ℕ} (hk : 2 ≤ k) (he : k % 2 = 0)
    {ls : List (List (AcAct F A C ⊕ AcTask F A C))} :
    ls ∈ bodies D vars bound (AcTask.cntPar t k) ↔
      ls = [[Sum.inr (AcTask.cntPar t (k / 2))], [Sum.inr (AcTask.cntPar t (k / 2))]] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  simp [bodies, h0, h1, he]

lemma bodies_cntPar_odd {t : AcTask F A C} {k : ℕ} (hk : 2 ≤ k) (ho : k % 2 = 1)
    {ls : List (List (AcAct F A C ⊕ AcTask F A C))} :
    ls ∈ bodies D vars bound (AcTask.cntPar t k) ↔
      ls = [[Sum.inr t], [Sum.inr (AcTask.cntPar t (k - 1))]] ∨
        ls = [[Sum.inr (AcTask.cntPar t (k - 1))]] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  have he : ¬ (k % 2 = 0) := by omega
  simp [bodies, h0, h1, he]

/-! ### Refinements of the parallel counting task -/

/-- Refinements of a pair of parallel chains split into interleavings. -/
lemma gridYield_pair_iff {l l' : List (AcAct F A C ⊕ AcTask F A C)} {as : List (AcAct F A C)} :
    (domain D vars bound).GridYield [l, l'] as ↔ ∃ as₁ as₂,
      (domain D vars bound).ChainYield l as₁ ∧ (domain D vars bound).ChainYield l' as₂ ∧
        Interleave as₁ as₂ as := by
  rw [gridYield_cons_iff]
  constructor
  · rintro ⟨as₁, as₂, hc, hg, hint⟩
    exact ⟨as₁, as₂, hc, gridYield_singleton_iff.1 hg, hint⟩
  · rintro ⟨as₁, as₂, hc, hc', hint⟩
    exact ⟨as₁, as₂, hc, gridYield_singleton_iff.2 hc', hint⟩

/-- **The parallel counting task `𝔠^k_t` refines exactly into the refinements of at most `k`
unordered copies of `t`.** -/
theorem gridYield_cntPar_iff : ∀ (k : ℕ) {t : AcTask F A C} {as : List (AcAct F A C)},
    (domain D vars bound).ChainYield [Sum.inr (AcTask.cntPar t k)] as ↔
      ∃ m ≤ k, (domain D vars bound).GridYield (List.replicate m [Sum.inr t]) as := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t as
  rw [chainYield_singleton_ac_iff]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodies_cntPar_zero] at hls
        subst hls
        exact ⟨0, le_rfl, by simpa using hy⟩
      · rintro ⟨m, hm, hy⟩
        obtain rfl : m = 0 := Nat.le_zero.1 hm
        exact ⟨[], bodies_cntPar_zero.2 rfl, by simpa using hy⟩
    · constructor
      · rintro ⟨ls, hls, hy⟩
        rcases bodies_cntPar_one.1 hls with rfl | rfl
        · exact ⟨1, le_rfl, by simpa using hy⟩
        · exact ⟨0, Nat.zero_le _, by simpa using hy⟩
      · rintro ⟨m, hm, hy⟩
        interval_cases m
        · exact ⟨[], bodies_cntPar_one.2 (Or.inr rfl), by simpa using hy⟩
        · exact ⟨[[Sum.inr t]], bodies_cntPar_one.2 (Or.inl rfl), by simpa using hy⟩
  · rcases Nat.even_or_odd k with hev | hod
    · have he : k % 2 = 0 := Nat.even_iff.1 hev
      have hlt : k / 2 < k := Nat.div_lt_self (by omega) (by omega)
      constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodies_cntPar_even hk he] at hls
        subst hls
        obtain ⟨as₁, as₂, h₁, h₂, hint⟩ := gridYield_pair_iff.1 hy
        obtain ⟨m₁, hm₁, g₁⟩ := (ih _ hlt).1 h₁
        obtain ⟨m₂, hm₂, g₂⟩ := (ih _ hlt).1 h₂
        refine ⟨m₁ + m₂, by omega, ?_⟩
        rw [List.replicate_add]
        exact gridYield_append_iff.2 ⟨as₁, as₂, g₁, g₂, hint⟩
      · rintro ⟨m, hm, hy⟩
        refine ⟨_, (bodies_cntPar_even hk he).2 rfl, ?_⟩
        obtain ⟨m₁, m₂, rfl, hm₁, hm₂⟩ : ∃ m₁ m₂, m = m₁ + m₂ ∧ m₁ ≤ k / 2 ∧ m₂ ≤ k / 2 :=
          ⟨min m (k / 2), m - min m (k / 2), by omega, by omega, by omega⟩
        rw [List.replicate_add] at hy
        obtain ⟨as₁, as₂, g₁, g₂, hint⟩ := gridYield_append_iff.1 hy
        exact gridYield_pair_iff.2 ⟨as₁, as₂, (ih _ hlt).2 ⟨m₁, hm₁, g₁⟩,
          (ih _ hlt).2 ⟨m₂, hm₂, g₂⟩, hint⟩
    · have ho : k % 2 = 1 := Nat.odd_iff.1 hod
      have hlt : k - 1 < k := by omega
      constructor
      · rintro ⟨ls, hls, hy⟩
        rcases (bodies_cntPar_odd hk ho).1 hls with rfl | rfl
        · obtain ⟨as₁, as₂, h₁, h₂, hint⟩ := gridYield_pair_iff.1 hy
          obtain ⟨m₂, hm₂, g₂⟩ := (ih _ hlt).1 h₂
          refine ⟨1 + m₂, by omega, ?_⟩
          rw [List.replicate_add]
          refine gridYield_append_iff.2 ⟨as₁, as₂, ?_, g₂, hint⟩
          simpa using gridYield_singleton_iff.2 h₁
        · rw [gridYield_singleton_iff] at hy
          obtain ⟨m, hm, g⟩ := (ih _ hlt).1 hy
          exact ⟨m, by omega, g⟩
      · rintro ⟨m, hm, hy⟩
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · refine ⟨[[Sum.inr (AcTask.cntPar t (k - 1))]],
            (bodies_cntPar_odd hk ho).2 (Or.inr rfl), ?_⟩
          exact gridYield_singleton_iff.2 ((ih _ hlt).2 ⟨0, Nat.zero_le _, hy⟩)
        · obtain ⟨m', rfl⟩ : ∃ m', m = 1 + m' := ⟨m - 1, by omega⟩
          refine ⟨[[Sum.inr t], [Sum.inr (AcTask.cntPar t (k - 1))]],
            (bodies_cntPar_odd hk ho).2 (Or.inl rfl), ?_⟩
          rw [List.replicate_add] at hy
          obtain ⟨as₁, as₂, g₁, g₂, hint⟩ := gridYield_append_iff.1 hy
          refine gridYield_pair_iff.2 ⟨as₁, as₂, ?_, (ih _ hlt).2 ⟨m', by omega, g₂⟩, hint⟩
          simpa using gridYield_singleton_iff.1 (by simpa using g₁)

/-- The parallel counting task can always produce no copy at all. -/
lemma chainYield_cntPar_nil {t : AcTask F A C} {k : ℕ} :
    (domain D vars bound).ChainYield [Sum.inr (AcTask.cntPar t k)] [] :=
  (gridYield_cntPar_iff k).2 ⟨0, Nat.zero_le _, by simp⟩

/-- The parallel counting task can produce one copy, hence refines like `t` itself. -/
lemma chainYield_cntPar_of_single {t : AcTask F A C} {k : ℕ} {as : List (AcAct F A C)}
    (hk : 1 ≤ k) (h : (domain D vars bound).ChainYield [Sum.inr t] as) :
    (domain D vars bound).ChainYield [Sum.inr (AcTask.cntPar t k)] as :=
  (gridYield_cntPar_iff k).2 ⟨1, hk, by simpa using gridYield_singleton_iff.2 h⟩

/-! ### The initial task of the compiled problem -/

/-- **The refinements of the initial task `t_I` are exactly the interleavings of the refinements
of at most `bound` memory cells with those of at most `bound` proof steps.** -/
theorem chainYield_tI_iff {as : List (AcAct F A C)} :
    (domain D vars bound).ChainYield [Sum.inr AcTask.tI] as ↔
      ∃ (m₁ m₂ : ℕ) (as₁ as₂ : List (AcAct F A C)), m₁ ≤ bound ∧ m₂ ≤ bound ∧
        (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁ ∧
        (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂ ∧
        Interleave as₁ as₂ as := by
  rw [chainYield_singleton_ac_iff]
  constructor
  · rintro ⟨ls, hls, hy⟩
    have hls' : ls = [[Sum.inr (AcTask.cntPar AcTask.MEM bound)],
        [Sum.inr (AcTask.cntPar AcTask.TUPLE bound)]] := by
      simpa [bodies] using hls
    subst hls'
    obtain ⟨as₁, as₂, h₁, h₂, hint⟩ := gridYield_pair_iff.1 hy
    obtain ⟨m₁, hm₁, g₁⟩ := (gridYield_cntPar_iff bound).1 h₁
    obtain ⟨m₂, hm₂, g₂⟩ := (gridYield_cntPar_iff bound).1 h₂
    exact ⟨m₁, m₂, as₁, as₂, hm₁, hm₂, g₁, g₂, hint⟩
  · rintro ⟨m₁, m₂, as₁, as₂, hm₁, hm₂, g₁, g₂, hint⟩
    refine ⟨[[Sum.inr (AcTask.cntPar AcTask.MEM bound)],
      [Sum.inr (AcTask.cntPar AcTask.TUPLE bound)]], by simp [bodies], ?_⟩
    exact gridYield_pair_iff.2 ⟨as₁, as₂, (gridYield_cntPar_iff bound).2 ⟨m₁, hm₁, g₁⟩,
      (gridYield_cntPar_iff bound).2 ⟨m₂, hm₂, g₂⟩, hint⟩

/-- **The action sequences that the initial task network of the compiled problem refines into**
are the interleavings of the refinements of at most `bound` memory cells with those of at most
`bound` proof steps. -/
theorem netYield_tnI_iff {Q : Instance F A C I} {tI0 : C} {as : List (AcAct F A C)} :
    (domain D vars bound).NetYield (instance_ Q tI0).tnI as ↔
      ∃ (m₁ m₂ : ℕ) (as₁ as₂ : List (AcAct F A C)), m₁ ≤ bound ∧ m₂ ≤ bound ∧
        (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁ ∧
        (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂ ∧
        Interleave as₁ as₂ as := by
  rw [show (instance_ Q tI0).tnI = TaskNetwork.seq [Sum.inr AcTask.tI] from rfl,
    netYield_seq_iff (methods_grid (D := D) (vars := vars) (bound := bound)), chainYield_tI_iff]

end ToAc

end HTN
