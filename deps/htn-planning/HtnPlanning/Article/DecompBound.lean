import HtnPlanning.Article.Classes
import HtnPlanning.Core.Reachability
import HtnPlanning.Core.DecompCommute
/-!
# The number of decompositions in acyclic problems (Lemma 4.2.4, corrected)

**Lemma 4.2.4** of the article claims that for `P ∈ ACYC` with `k` initial tasks, at most `m`
tasks per reachable method and a `≤₀`-stratification of height `h`, every sequence of
decompositions of `tn_I` has length at most `k · m^(h-1) ≤ r^h` (`r = max(k, m)`).

**This bound is wrong.**  A decomposition tree of height `h` and width `m` has up to
`1 + m + … + m^(h-1)` inner nodes, not `m^(h-1)`.  Counterexample: `tn_I = {A, A}`, methods
`A → {B, B}` and `B → {a}`; strata `B < A` (`h = 2`), `k = m = r = 2`.  Decomposing both `A`s
and all four `B`s takes `6` steps, while `k · m^(h-1) = 4` and `r^h = 4`.

**Corrected statement** (`HTN.Problem.length_decomposition_le`,
`HTN.Article.Problem.lem_4_2_4`): every sequence of decompositions of `tn_I` has length at most
`k · (1 + m + … + m^(h-1)) < (r + 1)^h`.  The consequences drawn in the article (Thm. 4.2.5,
Thm. 4.2.6: exponentially many decompositions; Cor. 4.2.8: polynomially many for fixed `h`) are
unaffected.

The proof is a potential argument: a compound task of rank `j` (its stratum) is worth
`1 + m + … + m^j`; a decomposition replaces a task of rank `j` by at most `m` tasks of ranks `< j`,
which lowers the total worth by at least one.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- `1 + m + … + m^(j-1)`. -/
def geomSum (m j : ℕ) : ℕ := ∑ d ∈ Finset.range j, m ^ d

theorem geomSum_succ (m j : ℕ) : geomSum m (j + 1) = 1 + m * geomSum m j := by
  unfold geomSum
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  simp [pow_succ, mul_comm]

theorem geomSum_mono (m : ℕ) {i j : ℕ} (h : i ≤ j) : geomSum m i ≤ geomSum m j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- `k · (1 + m + … + m^(h-1)) < (max k m + 1)^h` for `h ≥ 1`, and `≤` in general. -/
theorem mul_geomSum_lt (k m h : ℕ) : k * geomSum m h + 1 ≤ (max k m + 1) ^ h := by
  set r := max k m
  have hk : k ≤ r := le_max_left _ _
  have hm : m ≤ r := le_max_right _ _
  have key : ∀ h, k * geomSum m h ≤ ∑ d ∈ Finset.range h, r ^ (d + 1) := by
    intro h
    unfold geomSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [pow_succ']
    exact Nat.mul_le_mul hk (Nat.pow_le_pow_left hm d)
  have geo : ∀ h, ∑ d ∈ Finset.range h, r ^ (d + 1) + 1 ≤ (r + 1) ^ h := by
    intro h
    induction h with
    | zero => simp
    | succ h ih =>
      rw [Finset.sum_range_succ]
      have : r ^ (h + 1) ≤ r * (r + 1) ^ h := by
        rw [pow_succ']
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ r) h)
      have e : (r + 1) ^ (h + 1) = (r + 1) ^ h + r * (r + 1) ^ h := by ring
      rw [e]
      linarith
  exact (Nat.add_le_add_right (key h) 1).trans (geo h)

namespace Problem

variable [DecidableEq I]

/-- The worth of a task name under the ranking `f`: `1 + m + … + m^(f c)` for a compound name. -/
def worth (m : ℕ) (f : C → ℕ) : A ⊕ C → ℕ := Sum.elim (fun _ => 0) fun c => geomSum m (f c + 1)

/-- The potential of a task network. -/
def potential (m : ℕ) (f : C → ℕ) (tn : TaskNetwork I A C) : ℕ :=
  ∑ t ∈ tn.T, worth m f (tn.α t)

/-- **One decomposition lowers the potential.** -/
theorem potential_step (P : Problem F A C I) {le : C → C → Prop} (hs : P.IsStrat0 le)
    {f : C → ℕ} (hf : ∀ c c', P.ReachableName c → P.ReachableName c' → (le c c' ↔ f c ≤ f c'))
    {mm : ℕ} (hmm : ∀ m, P.ReachableMethod m → m.subtasks.T.card ≤ mm)
    {tn₁ tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    (h : DecompStep P.methods tn₁ t m tn₂) (hn : P.NamesReachable tn₁) :
    potential mm f tn₂ + 1 ≤ potential mm f tn₁ := by
  have hrm : P.ReachableMethod m := reachableMethod_of_decompStep h hn
  obtain ⟨hm, htT, hαt, tn', -, ⟨σ, hbij, -, hα⟩, hdisj, rfl⟩ := h
  have hrc : P.ReachableName m.abstractTask := hn t htT _ hαt
  set c := m.abstractTask
  have hd : Disjoint (tn₁.T.erase t) tn'.T :=
    Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
  have hT₂ : (decomposeWith tn₁ t tn').T = tn₁.T.erase t ∪ tn'.T := rfl
  unfold potential
  rw [hT₂, Finset.sum_union hd, ← Finset.add_sum_erase _ _ htT, hαt]
  have e1 : ∑ x ∈ tn₁.T.erase t, worth mm f ((decomposeWith tn₁ t tn').α x) =
      ∑ x ∈ tn₁.T.erase t, worth mm f (tn₁.α x) :=
    Finset.sum_congr rfl fun x hx => by
      have : x ∉ tn'.T := Finset.disjoint_left.1 hdisj (Finset.mem_of_mem_erase hx)
      simp [decomposeWith_α, this]
  have e2 : ∑ x ∈ tn'.T, worth mm f ((decomposeWith tn₁ t tn').α x) ≤ mm * geomSum mm (f c) := by
    have hb : ∀ x ∈ tn'.T, worth mm f ((decomposeWith tn₁ t tn').α x) ≤ geomSum mm (f c) := by
      intro x hx
      have hx' : σ x ∈ m.subtasks.T := hbij.mapsTo hx
      simp only [decomposeWith_α, hx, if_true, hα x hx]
      cases hcx : m.subtasks.α (σ x) with
      | inl a => simp [worth]
      | inr d =>
        have hrd : P.ReachableName d := ReachableName.method hm hrc hx' hcx
        obtain ⟨h1, h2⟩ := hs.decreasing m hrm (σ x) hx' d hcx
        have hlt : f d < f c := by
          rw [hf d c hrd hrc] at h1
          rw [hf c d hrc hrd] at h2
          omega
        exact geomSum_mono mm (by omega)
    have hcard : tn'.T.card ≤ mm := by
      have : tn'.T.card = m.subtasks.T.card := by
        have := Finset.card_nbij σ (fun x hx => hbij.mapsTo hx) hbij.injOn hbij.surjOn
        exact this
      rw [this]; exact hmm m hrm
    calc ∑ x ∈ tn'.T, worth mm f ((decomposeWith tn₁ t tn').α x)
        ≤ tn'.T.card * geomSum mm (f c) := by
          have := Finset.sum_le_card_nsmul tn'.T _ _ hb
          simpa using this
      _ ≤ mm * geomSum mm (f c) := Nat.mul_le_mul_right _ hcard
  rw [e1]
  have : worth mm f (Sum.inr c : A ⊕ C) = 1 + mm * geomSum mm (f c) := by
    simp [worth, geomSum_succ]
  rw [this]
  omega

/-- The potential bounds the number of decompositions. -/
theorem add_potential_le (P : Problem F A C I) {le : C → C → Prop} (hs : P.IsStrat0 le)
    {f : C → ℕ} (hf : ∀ c c', P.ReachableName c → P.ReachableName c' → (le c c' ↔ f c ≤ f c'))
    {mm : ℕ} (hmm : ∀ m, P.ReachableMethod m → m.subtasks.T.card ≤ mm) {n : ℕ}
    {tn tn' : TaskNetwork I A C} (hd : DecomposesToN P.methods n tn tn') :
    P.NamesReachable tn → n + potential mm f tn' ≤ potential mm f tn := by
  induction hd with
  | refl => intro _; simp
  | head hstep _ ih =>
    intro hn
    obtain ⟨t, m, hs'⟩ := hstep
    have h1 := potential_step P hs hf hmm hs' hn
    have h2 := ih (namesReachable_of_decompStep hs' hn)
    omega

/-- **Lemma 4.2.4 (corrected).** In a problem with a `≤₀`-stratification of height at most `h`
and at most `mm` tasks in every reachable method, every sequence of decompositions of `tn_I` has
at most `|tn_I| · (1 + mm + … + mm^(h-1))` steps. -/
theorem length_decomposition_le (P : Problem F A C I) {le : C → C → Prop} (hs : P.IsStrat0 le)
    {h : ℕ} (hh : P.HasHeightLE le h) {mm : ℕ}
    (hmm : ∀ m, P.ReachableMethod m → m.subtasks.T.card ≤ mm) {n : ℕ} {tn : TaskNetwork I A C}
    (hd : DecomposesToN P.methods n P.tnI tn) : n ≤ P.tnI.T.card * geomSum mm h := by
  obtain ⟨f, hfh, hf⟩ := hh
  have h1 := add_potential_le P hs hf hmm hd P.namesReachable_tnI
  have h2 : potential mm f P.tnI ≤ P.tnI.T.card * geomSum mm h := by
    unfold potential
    have := Finset.sum_le_card_nsmul P.tnI.T (fun t => worth mm f (P.tnI.α t)) (geomSum mm h)
      fun t ht => by
        cases hc : P.tnI.α t with
        | inl a => simp [worth, hc]
        | inr c =>
          simp only [worth, hc, Sum.elim_inr]
          exact geomSum_mono mm (hfh c (ReachableName.tnI ht hc))
    simpa using this
  omega

end Problem

namespace Article

namespace Problem

variable [DecidableEq I]

/-- **Lemma 4.2.4 (corrected), for the article's model.**  For `P ∈ ACYC_h` with at most `k`
initial tasks and at most `m` tasks in every reachable method, every sequence of decompositions
of `tn_I` has at most `k · (1 + m + … + m^(h-1))` steps, and fewer than `(max(k, m) + 1)^h`. -/
theorem lem_4_2_4 (P : Problem F A C I) {h : ℕ} (hP : P.IsACYC_h h) {k m : ℕ}
    (hk : P.tnI.T.card ≤ k) (hm : ∀ m', P.toPos.ReachableMethod m' → m'.subtasks.T.card ≤ m)
    {n : ℕ} {tn : TaskNetwork I A C} (hd : DecomposesToN P.methods n P.tnI tn) :
    n ≤ k * geomSum m h ∧ n < (max k m + 1) ^ h := by
  obtain ⟨le, hs, hh⟩ := hP
  have h1 : n ≤ P.tnI.T.card * geomSum m h :=
    HTN.Problem.length_decomposition_le P.toPos hs hh hm hd
  have h2 : P.tnI.T.card * geomSum m h ≤ k * geomSum m h := Nat.mul_le_mul_right _ hk
  have h3 := mul_geomSum_lt k m h
  exact ⟨h1.trans h2, by omega⟩

end Problem

end Article

end HTN
