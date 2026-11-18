import ComplexityTheory.Petri.Steps
/-!
# Decomposition steps (b): bounded edges and bounded `ω`-coordinates

* **Bounded edge** (`edgeAlts`, `edge_local`, `edge_local'`): if a run uses the edge `e₀` exactly
  `n` times, it is a run of the chain `chainFrom … n` of `n + 1` blocks over the component
  without `e₀`, linked by `e₀`.
* **Bounded input / output coordinate** (`inpAlts`, `outAlts`): an `ω` in the input (output) is
  replaced by each value `≤ B`.

Together with `solvable_replace_of_bound` these give the replacement steps for variables that
are bounded in every solution of the characteristic system.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

variable {ι : Type*}

/-! ### Edge counts of index walks -/

theorem count_map_edge (C : Comp ι) [DecidableEq (Edge ι)] (e : Edge ι) (π : List ℕ)
    (hπ : ∀ k ∈ π, k < C.edges.length) :
    (π.map C.edge).count e =
      ∑ k ∈ range C.edges.length, if C.edge k = e then π.count k else 0 := by
  induction π with
  | nil => simp
  | cons k π ih =>
    rw [sum_ite_count_cons _ k (hπ k (by simp)) π (fun k' => C.edge k' = e),
      ← ih fun k' h => hπ k' (List.mem_cons_of_mem _ h), List.map_cons, List.count_cons]
    simp [beq_iff_eq]

/-! ### Bounded edges -/

section Edge

variable [DecidableEq (Edge ι)] (b : Block ι) (e₀ : Edge ι)

/-- The component without the edge `e₀`, with given entry and exit. -/
def Block.minus (s t : ℕ) : Comp ι := b.comp.sub (fun _ => True) (· ≠ e₀) s t

/-- The chain of blocks for runs from `u` (with link vector `pre` and input `inp`) using `e₀`
exactly `n` times. -/
def chainFrom (pre : ι → ℤ) (inp : ι → ℕ∞) (u : ℕ) : ℕ → List (Block ι)
  | 0 => [⟨pre, inp, b.minus e₀ u b.comp.exit, b.out⟩]
  | n + 1 => ⟨pre, inp, b.minus e₀ u e₀.1, b.comp.lab e₀.1⟩ ::
      chainFrom e₀.2.1 (b.comp.lab e₀.2.2) e₀.2.2 n

/-- The alternatives for a block whose edge `e₀` is used at most `B` times. -/
def edgeAlts (B : ℕ) : List (List (Block ι)) :=
  (List.range (B + 1)).map (chainFrom b e₀ b.pre b.inp b.comp.entry)

variable {b e₀}

theorem chain_iff (he₀ : e₀ ∈ b.comp.edges) : ∀ (n : ℕ) (pre : ι → ℤ) (inp : ι → ℕ∞) (u : ℕ)
    (M M' : ι → ℤ), ListRun (chainFrom b e₀ pre inp u n) M M' ↔
      Agree (M + pre) inp ∧ ∃ es, RunC b.comp u b.comp.exit (M + pre) es ∧ es.count e₀ = n ∧
        M' = M + pre + teff es ∧ Agree M' b.out
  | 0, pre, inp, u, M, M' => by
    rw [chainFrom, listRun_singleton, blockRun_iff_runC]
    simp only [Block.minus, runC_sub, List.count_eq_zero]
    constructor
    · rintro ⟨h1, es, ⟨hr, hq⟩, h2, h3⟩
      exact ⟨h1, es, hr, fun h => hq e₀ h rfl, h2, h3⟩
    · rintro ⟨h1, es, hr, hq, h2, h3⟩
      exact ⟨h1, es, ⟨hr, fun e he h => hq (h ▸ he)⟩, h2, h3⟩
  | n + 1, pre, inp, u, M, M' => by
    rw [chainFrom, ListRun]
    simp only [chain_iff he₀ n]
    constructor
    · rintro ⟨M₁, hb, hA2, es₂, hr2, hc2, he2, hA'⟩
      obtain ⟨hA1, es₁, hr1, he1, hAo⟩ := blockRun_iff_runC.1 hb
      simp only [Block.minus, runC_sub] at hr1
      refine ⟨hA1, es₁ ++ e₀ :: es₂, ?_, ?_, ?_, hA'⟩
      · refine runC_append.2 ⟨e₀.1, hr1.1, runC_cons.2 ⟨rfl, he₀, ?_, ?_, ?_⟩⟩
        · exact hr1.1.last.1
        · rw [← he1]; exact hAo
        · rw [← he1]; exact hr2
      · rw [List.count_append, List.count_cons_self, hc2,
          List.count_eq_zero.2 fun h => hr1.2 e₀ h rfl]
        ring
      · rw [he2, he1, teff_append, teff_cons]; abel
    · rintro ⟨hA1, es, hr, hc, he, hA'⟩
      have hmem : e₀ ∈ es := List.count_pos_iff.1 (by omega)
      obtain ⟨es₁, es₂, rfl, hn⟩ := exists_first hmem
      obtain ⟨v, hr1, hr2⟩ := runC_append.1 hr
      obtain ⟨rfl, -, hpos, hag, hr3⟩ := runC_cons.1 hr2
      refine ⟨M + pre + teff es₁, ?_, hr3.first.2, es₂, hr3, ?_, ?_, hA'⟩
      · refine blockRun_iff_runC.2 ⟨hA1, es₁, ?_, rfl, hag⟩
        simp only [Block.minus, runC_sub]
        exact ⟨hr1, fun e he h => hn (h ▸ he)⟩
      · rw [List.count_append, List.count_cons_self, List.count_eq_zero.2 hn] at hc
        omega
      · rw [he, teff_append, teff_cons]; abel

/-- Every run of the block using `e₀` at most `B` times is a run of an alternative. -/
theorem edge_local (he₀ : e₀ ∈ b.comp.edges) (B : ℕ) (t : Tri ι) (ht : RunData b t)
    (hQ : (∑ k ∈ range b.comp.edges.length, if b.comp.edge k = e₀ then t.ψ k else 0) ≤ B) :
    ∃ A ∈ edgeAlts b e₀ B, ListRun A (t.M₁ - b.pre) t.M' := by
  obtain ⟨hA, hA', π, hπ, hf, hl, he, hψ⟩ := ht
  have hc : (π.map b.comp.edge).count e₀ ≤ B := by
    rw [count_map_edge _ _ _ hπ.lt']
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) hQ
    rw [hψ k (Finset.mem_range.1 hk)]
  refine ⟨chainFrom b e₀ b.pre b.inp b.comp.entry ((π.map b.comp.edge).count e₀), ?_, ?_⟩
  · exact List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩
  · have e : t.M₁ - b.pre + b.pre = t.M₁ := by abel
    rw [chain_iff he₀]
    rw [e]
    exact ⟨hA, _, ⟨hπ.toT, hf, hl⟩, rfl, he, hA'⟩

/-- The runs of the alternatives are runs of the block. -/
theorem edge_local' (he₀ : e₀ ∈ b.comp.edges) (B : ℕ) :
    ∀ A ∈ edgeAlts b e₀ B, ∀ M M', ListRun A M M' → BlockRun b M M' := by
  intro A hA M M' h
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hA
  obtain ⟨h1, es, hr, -, h2, h3⟩ := (chain_iff he₀ n _ _ _ M M').1 h
  exact blockRun_iff_runC.2 ⟨h1, es, hr, h2, h3⟩

end Edge

/-! ### Bounded input and output coordinates -/

theorem agree_of_update {x : ι → ℤ} {μ : ι → ℕ∞} [DecidableEq ι] {j : ι} {k : ℕ∞}
    (hj : μ j = ⊤) (h : Agree x (Function.update μ j k)) : Agree x μ := by
  intro j' hj'
  have hne : j' ≠ j := fun h' => hj' (h' ▸ hj)
  have := h j' (by rwa [Function.update_of_ne hne])
  rwa [Function.update_of_ne hne] at this

theorem agree_update {x : ι → ℤ} {μ : ι → ℕ∞} [DecidableEq ι] {j : ι} (h : Agree x μ)
    (hx : 0 ≤ x j) : Agree x (Function.update μ j ((x j).toNat : ℕ∞)) := by
  intro j' hj'
  by_cases hne : j' = j
  · subst hne
    simp [Int.toNat_of_nonneg hx]
  · rw [Function.update_of_ne hne] at hj' ⊢
    exact h j' hj'

section Coord

variable [DecidableEq ι] (b : Block ι) (j : ι)

/-- The alternatives for an input coordinate bounded by `B`. -/
def inpAlts (B : ℕ) : List (List (Block ι)) :=
  (List.range (B + 1)).map fun k : ℕ => [{ b with inp := Function.update b.inp j (k : ℕ∞) }]

/-- The alternatives for an output coordinate bounded by `B`. -/
def outAlts (B : ℕ) : List (List (Block ι)) :=
  (List.range (B + 1)).map fun k : ℕ => [{ b with out := Function.update b.out j (k : ℕ∞) }]

variable {b j}

theorem inp_local (B : ℕ) (t : Tri ι) (ht : RunData b t) (hQ : t.M₁ j ≤ B) :
    ∃ A ∈ inpAlts b j B, ListRun A (t.M₁ - b.pre) t.M' := by
  obtain ⟨hA, hA', π, hπ, hf, hl, he, hψ⟩ := ht
  have hx : 0 ≤ t.M₁ j := hf.start j trivial
  refine ⟨[{ b with inp := Function.update b.inp j ((t.M₁ j).toNat : ℕ∞) }], ?_, ?_⟩
  · have hk : (t.M₁ j).toNat < B + 1 := by omega
    exact List.mem_map.2 ⟨(t.M₁ j).toNat, List.mem_range.2 hk, rfl⟩
  · refine listRun_singleton.2 (blockRun_iff.2 ⟨t.ψ, ?_⟩)
    have e : t.M₁ - b.pre + b.pre = t.M₁ := by abel
    rw [e]
    exact ⟨agree_update hA hx, hA', π, hπ, hf, hl, he, hψ⟩

theorem inp_local' (hj : b.inp j = ⊤) (B : ℕ) :
    ∀ A ∈ inpAlts b j B, ∀ M M', ListRun A M M' → BlockRun b M M' := by
  intro A hA M M' h
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hA
  obtain ⟨h1, h2⟩ := listRun_singleton.1 h
  exact ⟨agree_of_update hj h1, h2⟩

theorem out_local (B : ℕ) (t : Tri ι) (ht : RunData b t) (hQ : t.M' j ≤ B) :
    ∃ A ∈ outAlts b j B, ListRun A (t.M₁ - b.pre) t.M' := by
  have hc := ht.charOK
  obtain ⟨hA, hA', π, hπ, hf, hl, he, hψ⟩ := ht
  have hx : 0 ≤ t.M' j := hc.2.2.2.2.1 j
  refine ⟨[{ b with out := Function.update b.out j ((t.M' j).toNat : ℕ∞) }], ?_, ?_⟩
  · have hk : (t.M' j).toNat < B + 1 := by omega
    exact List.mem_map.2 ⟨(t.M' j).toNat, List.mem_range.2 hk, rfl⟩
  · refine listRun_singleton.2 (blockRun_iff.2 ⟨t.ψ, ?_⟩)
    have e : t.M₁ - b.pre + b.pre = t.M₁ := by abel
    rw [e]
    exact ⟨hA, agree_update hA' hx, π, hπ, hf, hl, he, hψ⟩

theorem out_local' (hj : b.out j = ⊤) (B : ℕ) :
    ∀ A ∈ outAlts b j B, ∀ M M', ListRun A M M' → BlockRun b M M' := by
  intro A hA M M' h
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hA
  obtain ⟨h1, es, h2, h3, h4, h5, h6⟩ := listRun_singleton.1 h
  exact ⟨h1, es, h2, h3, h4, h5, agree_of_update hj h6⟩

end Coord

end KLM

end Petri

end HTN
