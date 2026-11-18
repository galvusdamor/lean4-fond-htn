import FondHtn.AcycHard.Chains
import FondHtn.IsoLemmas
/-!
# Chain-shaped method networks

A *chain method network* lists primitive tasks `xs` in a total order, optionally followed by
one compound task `oc` (`FOND.PCP.IsChainNet`).  A copy of such a network (an isomorphic
network, as inserted by a decomposition step) is a chain on some list of fresh ids
(`FOND.PCP.chain_of_iso`).  Order in a list: `FOND.AcycHard.Before`.
-/

namespace FOND

namespace PCP

open HTN FOND.AcycHard

variable {I : Type} [DecidableEq I]

theorem before_iff_idx {l : List I} {a b : I} :
    Before l a b ↔ ∃ i j : ℕ, i < j ∧ l[i]? = some a ∧ l[j]? = some b := by
  constructor
  · rintro ⟨l₁, l₂, rfl, hb⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    refine ⟨l₁.length, l₁.length + 1 + k, by omega, by simp, ?_⟩
    rw [List.getElem?_append_right (by omega)]
    simp only [show l₁.length + 1 + k - l₁.length = k + 1 by omega, List.getElem?_cons_succ]
    exact List.getElem?_eq_getElem hk
  · rintro ⟨i, j, hij, hi, hj⟩
    have hil : i < l.length := by
      rcases Nat.lt_or_ge i l.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hi; cases hi
    have hjl : j < l.length := by
      rcases Nat.lt_or_ge j l.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj; cases hj
    refine ⟨l.take i, l.drop (i + 1), ?_, ?_⟩
    · have : l.drop i = a :: l.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hil]
        rw [List.getElem?_eq_getElem hil] at hi
        simp only [Option.some.injEq] at hi
        rw [hi]
      rw [← this, List.take_append_drop]
    · rw [List.mem_iff_getElem?]
      refine ⟨j - (i + 1), ?_⟩
      rw [List.getElem?_drop, show i + 1 + (j - (i + 1)) = j by omega, hj]

theorem before_append {l L : List I} {a b : I} :
    Before (l ++ L) a b ↔ Before l a b ∨ (a ∈ l ∧ b ∈ L) ∨ Before L a b := by
  simp only [before_iff_idx]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases Nat.lt_or_ge i l.length with hil | hil
    · rw [List.getElem?_append_left hil] at hi
      rcases Nat.lt_or_ge j l.length with hjl | hjl
      · rw [List.getElem?_append_left hjl] at hj
        exact Or.inl ⟨i, j, hij, hi, hj⟩
      · rw [List.getElem?_append_right hjl] at hj
        exact Or.inr (Or.inl ⟨List.mem_iff_getElem?.2 ⟨i, hi⟩, List.mem_iff_getElem?.2 ⟨_, hj⟩⟩)
    · rw [List.getElem?_append_right hil] at hi
      rw [List.getElem?_append_right (by omega)] at hj
      exact Or.inr (Or.inr ⟨i - l.length, j - l.length, by omega, hi, hj⟩)
  · rintro (⟨i, j, hij, hi, hj⟩ | ⟨ha, hb⟩ | ⟨i, j, hij, hi, hj⟩)
    · have hil : i < l.length := (List.getElem?_eq_some_iff.1 hi).1
      have hjl : j < l.length := (List.getElem?_eq_some_iff.1 hj).1
      exact ⟨i, j, hij, by rwa [List.getElem?_append_left hil],
        by rwa [List.getElem?_append_left hjl]⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hb
      have hil : i < l.length := (List.getElem?_eq_some_iff.1 hi).1
      refine ⟨i, l.length + j, by omega, by rwa [List.getElem?_append_left hil], ?_⟩
      rw [List.getElem?_append_right (by omega)]; simpa using hj
    · refine ⟨l.length + i, l.length + j, by omega, ?_, ?_⟩
      · rw [List.getElem?_append_right (by omega)]; simpa using hi
      · rw [List.getElem?_append_right (by omega)]; simpa using hj

theorem before_snoc_ne {l : List I} {p a b : I} (hb : b ≠ p) :
    Before (l ++ [p]) a b ↔ Before l a b := by
  rw [before_append]
  constructor
  · rintro (h | ⟨-, h⟩ | h)
    · exact h
    · exact absurd (List.mem_singleton.1 h) hb
    · exact absurd (List.mem_singleton.1 (before_mem h).2) hb
  · exact fun h => Or.inl h

theorem not_before_singleton {p a b : I} : ¬ Before [p] a b := by
  rw [before_cons]
  rintro (⟨-, h⟩ | h)
  · simp at h
  · exact before_nil h

theorem before_snoc_last {l : List I} {p a : I} (hp : p ∉ l) : ¬ Before (l ++ [p]) p a := by
  rw [before_append]
  rintro (h | ⟨h, -⟩ | h)
  · exact hp (before_mem h).1
  · exact hp h
  · exact not_before_singleton h

theorem before_snoc_to {l : List I} {p a : I} (hp : p ∉ l) :
    Before (l ++ [p]) a p ↔ a ∈ l := by
  rw [before_append]
  constructor
  · rintro (h | ⟨h, -⟩ | h)
    · exact absurd (before_mem h).2 hp
    · exact h
    · exact absurd h not_before_singleton
  · exact fun h => Or.inr (Or.inl ⟨h, List.mem_singleton_self _⟩)

theorem before_map_range {τ : ℕ → I} {n : ℕ} (hinj : Set.InjOn τ (Set.Iio n)) {i j : ℕ}
    (hi : i < n) (hj : j < n) :
    Before ((List.range n).map τ) (τ i) (τ j) ↔ i < j := by
  rw [before_iff_idx]
  have key : ∀ k x, ((List.range n).map τ)[k]? = some x → k < n ∧ τ k = x := by
    intro k x h
    rcases Nat.lt_or_ge k n with hk | hk
    · rw [List.getElem?_map, List.getElem?_range hk] at h
      exact ⟨hk, by simpa using h⟩
    · rw [List.getElem?_eq_none (by simpa using hk)] at h; cases h
  constructor
  · rintro ⟨i', j', hij, hi', hj'⟩
    obtain ⟨h1, hi'⟩ := key _ _ hi'
    obtain ⟨h2, hj'⟩ := key _ _ hj'
    have := hinj (show i' ∈ Set.Iio n from h1) (show i ∈ Set.Iio n from hi) hi'
    have := hinj (show j' ∈ Set.Iio n from h2) (show j ∈ Set.Iio n from hj) hj'
    omega
  · intro hij
    exact ⟨i, j, hij, by simp [List.getElem?_range hi], by simp [List.getElem?_range hj]⟩

/-! ## Chain method networks -/

/-- The network lists `xs` (primitive) in order, followed by the compound task `oc` if any,
on the ids `0, 1, …`. -/
structure IsChainNet {A C : Type} (tn : TaskNetwork ℕ A C) (xs : List A) (oc : Option C) :
    Prop where
  T : tn.T = Finset.range (xs.length + oc.toList.length)
  ord : ∀ i j, tn.ord i j ↔ i < j ∧ j < xs.length + oc.toList.length
  lab : ∀ i (h : i < xs.length), tn.α i = Sum.inl xs[i]
  labc : ∀ c, oc = some c → tn.α xs.length = Sum.inr c

/-- **A copy of a chain method network is a chain.** -/
theorem chain_of_iso {A C : Type} {u m : TaskNetwork ℕ A C} {xs : List A} {oc : Option C}
    (hm : IsChainNet m xs oc) (hu : u.WF) (hiso : u.Iso m) :
    ∃ L : List ℕ, L.Nodup ∧ L.length = xs.length + oc.toList.length ∧
      (∀ x, x ∈ u.T ↔ x ∈ L) ∧ (∀ a b, u.ord a b ↔ Before L a b) ∧
      (L.take xs.length).map u.α = xs.map Sum.inl ∧
      (∀ c, oc = some c → ∃ p, L = L.take xs.length ++ [p] ∧ u.α p = Sum.inr c) ∧
      (oc = none → L.length = xs.length) := by
  obtain ⟨σ, hσ⟩ := hiso
  replace hσ : TaskNetwork.IsoVia σ u m := hσ
  obtain ⟨τ, hτ, hστ⟩ := TaskNetwork.IsoVia.exists_inv hσ
  set n := xs.length + oc.toList.length with hn
  have hmT : ∀ i, i ∈ m.T ↔ i < n := fun i => by rw [hm.T]; simp [hn]
  have hτmem : ∀ i < n, τ i ∈ u.T := fun i hi => hτ.mem ((hmT i).2 hi)
  have hinj : Set.InjOn τ (Set.Iio n) := fun i hi j hj h =>
    hτ.inj ((hmT i).2 hi) ((hmT j).2 hj) h
  have hσlt : ∀ x ∈ u.T, σ x < n := fun x hx => (hmT _).1 (hσ.mem hx)
  have hmemL : ∀ x, x ∈ (List.range n).map τ ↔ x ∈ u.T := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hτmem i (List.mem_range.1 hi)
    · intro hx
      exact List.mem_map.2 ⟨σ x, List.mem_range.2 (hσlt x hx), hστ x hx⟩
  refine ⟨(List.range n).map τ, ?_, by simp, fun x => (hmemL x).symm, ?_, ?_, ?_, ?_⟩
  · exact (List.nodup_range).map_on fun i hi j hj h =>
      hinj (List.mem_range.1 hi) (List.mem_range.1 hj) h
  · intro a b
    constructor
    · intro hab
      have ha := hu.mem_left hab
      have hb := hu.mem_right hab
      rw [← hστ a ha, ← hστ b hb] at hab ⊢
      rw [before_map_range hinj (hσlt a ha) (hσlt b hb)]
      have := (hτ.2.1 (σ a) (hσ.mem ha) (σ b) (hσ.mem hb)).2 hab
      exact ((hm.ord _ _).1 this).1
    · intro hab
      obtain ⟨ha, hb⟩ := before_mem hab
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
      have hi' := List.mem_range.1 hi
      have hj' := List.mem_range.1 hj
      rw [before_map_range hinj hi' hj'] at hab
      exact (hτ.2.1 i ((hmT i).2 hi') j ((hmT j).2 hj')).1 ((hm.ord i j).2 ⟨hab, hj'⟩)
  · have hk : xs.length ≤ n := by simp [hn]
    rw [← List.map_take, List.take_range, Nat.min_eq_left hk, List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    simp only [List.length_map, List.length_range] at h1
    rw [hτ.α_eq ((hmT i).2 (by omega)), hm.lab i h1]
  · intro c hc
    refine ⟨τ xs.length, ?_, ?_⟩
    · have : n = xs.length + 1 := by simp [hn, hc]
      rw [this, List.range_succ, List.map_append, List.take_append_of_le_length (by simp)]
      simp
    · rw [hτ.α_eq ((hmT _).2 (by simp [hn, hc])), hm.labc c hc]
  · intro hc
    simp [hn, hc]

end PCP

end FOND
