import FondHtn.AcycHard.Hier
import HtnPlanning.Progression.Progression
/-!
# Tagged unions of chains

`FOND.HardTR.TC tn cs`: the task network `tn` is the disjoint union of the chains `cs`.  A chain
carries a tag: free (`none`), a *pre-chain* of the group `g` (`some (g, false)`) or the
*post-chain* of `g` (`some (g, true)`).  Tasks are ordered when they are in the same chain in that
order, or when the first lies in a pre-chain and the second in a post-chain of the same group.
These are the networks of the tail-recursive encoding: the threads of the current block of a
loop precede the loop task.

Steps: a sequence decomposition inside a chain (`FOND.HardTR.TC.step_seq`), a set decomposition
of a singleton chain (`FOND.HardTR.TC.step_set`), the execution of an unconstrained head
(`FOND.HardTR.TC.progress`), and re-reading a post-chain as a pre-chain followed by a post-chain
when the group has no pending pre-tasks (`FOND.HardTR.TC.split`).
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

open HTN AcycHard

variable {A C : Type}

/-- A tagged chain. -/
structure TCh (A C : Type) where
  ids : List ℕ
  lab : List (A ⊕ C)
  tag : Option (Bool × Bool)

/-- The cross order: `x` in a pre-chain, `y` in the post-chain of the same group. -/
def Cross (cs : List (TCh A C)) (x y : ℕ) : Prop :=
  ∃ i j, ∃ hi : i < cs.length, ∃ hj : j < cs.length, ∃ g,
    cs[i].tag = some (g, false) ∧ cs[j].tag = some (g, true) ∧ x ∈ cs[i].ids ∧ y ∈ cs[j].ids

/-- **The network is the tagged union of the chains.** -/
structure TC (tn : TaskNetwork ℕ A C) (cs : List (TCh A C)) : Prop where
  mem : ∀ x, x ∈ tn.T ↔ ∃ j, ∃ hj : j < cs.length, x ∈ cs[j].ids
  ord : ∀ x y, tn.ord x y ↔ (∃ j, ∃ hj : j < cs.length, Before cs[j].ids x y) ∨ Cross cs x y
  lab : ∀ j (hj : j < cs.length), cs[j].ids.map tn.α = cs[j].lab
  nodup : ∀ j (hj : j < cs.length), cs[j].ids.Nodup
  disj : ∀ i j (hi : i < cs.length) (hj : j < cs.length), i ≠ j → ∀ x ∈ cs[i].ids, x ∉ cs[j].ids

namespace TC

variable {tn : TaskNetwork ℕ A C} {cs : List (TCh A C)}

theorem chain_of_mem (h : TC tn cs) {k : ℕ} (hk : k < cs.length) {x : ℕ} (hx : x ∈ cs[k].ids) :
    ∀ j (hj : j < cs.length), x ∈ cs[j].ids → j = k := by
  intro j hj hxj
  by_contra hne
  exact h.disj k j hk hj (Ne.symm hne) x hx hxj

/-- A head task is unconstrained when its chain is not a post-chain, or its group has no
pending pre-tasks. -/
theorem unconstrained (h : TC tn cs) {k : ℕ} (hk : k < cs.length) {t : ℕ} {rest : List ℕ}
    (hc : cs[k].ids = t :: rest)
    (hpre : ∀ g, cs[k].tag = some (g, true) → ∀ i (hi : i < cs.length), cs[i].tag = some (g, false) →
      cs[i].ids = []) :
    tn.Unconstrained t := by
  have htk : t ∈ cs[k].ids := by rw [hc]; simp
  have hnd := h.nodup k hk
  rw [hc] at hnd
  refine ⟨(h.mem t).2 ⟨k, hk, htk⟩, fun t' _ hord => ?_⟩
  rcases (h.ord t' t).1 hord with ⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩
  · obtain rfl := h.chain_of_mem hk htk j hj (before_mem hb).2
    rw [hc] at hb
    rcases before_cons.1 hb with ⟨-, ht⟩ | hb
    · exact (List.nodup_cons.1 hnd).1 ht
    · exact (List.nodup_cons.1 hnd).1 (before_mem hb).2
  · obtain rfl := h.chain_of_mem hk htk j hj hy
    rw [hpre g htj i hi hti] at hx
    simp at hx

theorem mem_of_ord_left (h : TC tn cs) {a b : ℕ} (hab : tn.ord a b) : a ∈ tn.T := by
  rcases (h.ord a b).1 hab with ⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, -, -, hx, -⟩
  · exact (h.mem a).2 ⟨j, hj, (before_mem hb).1⟩
  · exact (h.mem a).2 ⟨i, hi, hx⟩

/-- **Executing an unconstrained head of a chain.** -/
theorem progress (h : TC tn cs) {k : ℕ} (hk : k < cs.length) {t : ℕ} {rest : List ℕ}
    {y : A ⊕ C} {labs : List (A ⊕ C)} {τ : Option (Bool × Bool)}
    (hc : cs[k] = ⟨t :: rest, y :: labs, τ⟩) (hu : tn.Unconstrained t) :
    TC (tn.progress t) (cs.set k ⟨rest, labs, τ⟩) := by
  have htk : t ∈ cs[k].ids := by rw [hc]; simp
  have ht_only : ∀ j (hj : j < cs.length), t ∈ cs[j].ids → j = k := h.chain_of_mem hk htk
  have hnd := h.nodup k hk
  rw [hc] at hnd
  have hlab := h.lab k hk
  rw [hc] at hlab
  simp only [List.map_cons, List.cons.injEq] at hlab
  have hgs : ∀ j (hj : j < cs.length), (cs.set k ⟨rest, labs, τ⟩)[j]'(by simpa using hj) =
      if k = j then ⟨rest, labs, τ⟩ else cs[j] := fun j hj => by
    simp [List.getElem_set]
  have htag : ∀ j (hj : j < cs.length), ((cs.set k ⟨rest, labs, τ⟩)[j]'(by simpa using hj)).tag =
      cs[j].tag := fun j hj => by
    rw [hgs j hj]; split_ifs with hjk
    · subst hjk; rw [hc]
    · rfl
  have hids : ∀ j (hj : j < cs.length) x, x ∈ ((cs.set k ⟨rest, labs, τ⟩)[j]'(by simpa using hj)).ids ↔
      x ∈ cs[j].ids ∧ x ≠ t := fun j hj x => by
    rw [hgs j hj]; split_ifs with hjk
    · subst hjk; rw [hc]
      simp only [List.mem_cons]
      constructor
      · intro hx; exact ⟨Or.inr hx, fun e => (List.nodup_cons.1 hnd).1 (e ▸ hx)⟩
      · rintro ⟨hx | hx, hne⟩
        · exact absurd hx hne
        · exact hx
    · constructor
      · intro hx; exact ⟨hx, fun e => hjk (ht_only j hj (e ▸ hx)).symm⟩
      · exact fun h => h.1
  have hbef : ∀ j (hj : j < cs.length) a b, Before ((cs.set k ⟨rest, labs, τ⟩)[j]'(by simpa using hj)).ids a b ↔
      Before cs[j].ids a b ∧ a ≠ t := fun j hj a b => by
    rw [hgs j hj]; split_ifs with hjk
    · subst hjk; rw [hc]
      simp only [before_cons]
      constructor
      · intro hb
        refine ⟨Or.inr hb, fun e => ?_⟩
        subst e; exact (List.nodup_cons.1 hnd).1 (before_mem hb).1
      · rintro ⟨⟨rfl, -⟩ | hb, hne⟩
        · exact absurd rfl hne
        · exact hb
    · constructor
      · intro hb; exact ⟨hb, fun e => hjk (ht_only j hj (e ▸ (before_mem hb).1)).symm⟩
      · exact fun h => h.1
  have hnot : ∀ a, ¬ tn.ord a t := fun a hat => hu.2 a (h.mem_of_ord_left hat) hat
  refine ⟨fun x => ?_, fun a b => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · simp only [TaskNetwork.progress_T, Finset.mem_erase, h.mem, List.length_set]
    constructor
    · rintro ⟨hne, j, hj, hx⟩; exact ⟨j, hj, (hids j hj x).2 ⟨hx, hne⟩⟩
    · rintro ⟨j, hj, hx⟩; exact ⟨((hids j hj x).1 hx).2, j, hj, ((hids j hj x).1 hx).1⟩
  · simp only [TaskNetwork.progress_ord, Cross, List.length_set]
    constructor
    · rintro ⟨hab, hne⟩
      have hbt : b ≠ t := fun e => hnot a (e ▸ hab)
      rcases (h.ord a b).1 hab with ⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩
      · exact Or.inl ⟨j, hj, (hbef j hj a b).2 ⟨hb, hne⟩⟩
      · exact Or.inr ⟨i, j, hi, hj, g, by rw [htag i hi]; exact hti, by rw [htag j hj]; exact htj,
          (hids i hi a).2 ⟨hx, hne⟩, (hids j hj b).2 ⟨hy, hbt⟩⟩
    · rintro (⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩)
      · obtain ⟨hb, hne⟩ := (hbef j hj a b).1 hb
        exact ⟨(h.ord a b).2 (Or.inl ⟨j, hj, hb⟩), hne⟩
      · rw [htag i hi] at hti; rw [htag j hj] at htj
        obtain ⟨hx, hne⟩ := (hids i hi a).1 hx
        exact ⟨(h.ord a b).2 (Or.inr ⟨i, j, hi, hj, g, hti, htj, hx, ((hids j hj b).1 hy).1⟩), hne⟩
  · simp only [List.length_set] at hj
    rw [hgs j hj]
    split_ifs with hjk
    · subst hjk; simpa using hlab.2
    · simpa using h.lab j hj
  · simp only [List.length_set] at hj
    rw [hgs j hj]
    split_ifs with hjk
    · subst hjk; exact (List.nodup_cons.1 hnd).2
    · exact h.nodup j hj
  · simp only [List.length_set] at hi hj
    have hx' := (hids i hi x).1 hx
    intro hy
    exact h.disj i j hi hj hij x hx'.1 ((hids j hj x).1 hy).1

theorem mem_of_ord_right (h : TC tn cs) {a b : ℕ} (hab : tn.ord a b) : b ∈ tn.T := by
  rcases (h.ord a b).1 hab with ⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, -, -, -, hy⟩
  · exact (h.mem b).2 ⟨j, hj, (before_mem hb).2⟩
  · exact (h.mem b).2 ⟨j, hj, hy⟩

/-- **A task inside a chain decomposed by a sequence network.** -/
theorem step_seq (h : TC tn cs) {k : ℕ} (hk : k < cs.length) {l₁ l₂ : List ℕ}
    {xs₁ xs₂ : List (A ⊕ C)} {t : ℕ} {y : A ⊕ C} {τ : Option (Bool × Bool)}
    (hc : cs[k] = ⟨l₁ ++ t :: l₂, xs₁ ++ y :: xs₂, τ⟩)
    (hlen : l₁.length = xs₁.length) {u : TaskNetwork ℕ A C} {lm : List ℕ} {bs : List (A ⊕ C)}
    (hu : u.IsSeqNet lm bs) (hdisj : Disjoint tn.T u.T) :
    TC (decomposeWith tn t u) (cs.set k ⟨l₁ ++ lm ++ l₂, xs₁ ++ bs ++ xs₂, τ⟩) := by
  have hnd := h.nodup k hk
  rw [hc] at hnd
  have htk : t ∈ cs[k].ids := by rw [hc]; simp
  have hkT : ∀ x ∈ cs[k].ids, x ∈ tn.T := fun x hx => (h.mem x).2 ⟨k, hk, hx⟩
  have htT : t ∈ tn.T := hkT t htk
  have hlmT : ∀ x ∈ lm, x ∉ tn.T := fun x hx hT =>
    Finset.disjoint_left.1 hdisj hT ((hu.memT x).2 hx)
  have ht_only : ∀ j (hj : j < cs.length), t ∈ cs[j].ids → j = k := h.chain_of_mem hk htk
  have ht1 : t ∉ l₁ := fun h' => (List.nodup_append.1 hnd).2.2 _ h' t (by simp) rfl
  have ht2 : t ∉ l₂ := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  set cs' := cs.set k ⟨l₁ ++ lm ++ l₂, xs₁ ++ bs ++ xs₂, τ⟩ with hcs'
  have hlen' : cs'.length = cs.length := by simp [cs']
  have hgs : ∀ j (hj : j < cs.length), cs'[j]'(by simpa [cs'] using hj) =
      if k = j then ⟨l₁ ++ lm ++ l₂, xs₁ ++ bs ++ xs₂, τ⟩ else cs[j] := fun j hj => by
    simp [cs', List.getElem_set]
  have htag : ∀ j (hj : j < cs.length), (cs'[j]'(by simpa [cs'] using hj)).tag = cs[j].tag :=
    fun j hj => by
      rw [hgs j hj]; split_ifs with hjk
      · subst hjk; rw [hc]
      · rfl
  have hids : ∀ j (hj : j < cs.length) x, x ∈ (cs'[j]'(by simpa [cs'] using hj)).ids ↔
      (x ∈ cs[j].ids ∧ x ≠ t) ∨ (j = k ∧ x ∈ lm) := fun j hj x => by
    rw [hgs j hj]; split_ifs with hjk
    · subst hjk; rw [hc]
      simp only [List.mem_append, List.mem_cons, true_and]
      constructor
      · rintro ((hx | hx) | hx)
        · exact Or.inl ⟨Or.inl hx, fun e => ht1 (e ▸ hx)⟩
        · exact Or.inr hx
        · exact Or.inl ⟨Or.inr (Or.inr hx), fun e => ht2 (e ▸ hx)⟩
      · rintro (⟨hx | hx | hx, hne⟩ | hx)
        · exact Or.inl (Or.inl hx)
        · exact absurd hx hne
        · exact Or.inr hx
        · exact Or.inl (Or.inr hx)
    · constructor
      · intro hx; exact Or.inl ⟨hx, fun e => hjk (ht_only j hj (e ▸ hx)).symm⟩
      · rintro (⟨hx, -⟩ | ⟨e, -⟩)
        · exact hx
        · exact absurd e.symm hjk
  -- the order of `t`
  have hordL : ∀ a, tn.ord a t ↔ a ∈ l₁ ∨ ∃ i, ∃ hi : i < cs.length, ∃ g,
      cs[i].tag = some (g, false) ∧ τ = some (g, true) ∧ a ∈ cs[i].ids := by
    intro a
    rw [h.ord]
    constructor
    · rintro (⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩)
      · obtain rfl := ht_only j hj (before_mem hb).2
        rw [hc] at hb; exact Or.inl ((before_mid_left hnd).1 hb)
      · obtain rfl := ht_only j hj hy
        rw [hc] at htj
        exact Or.inr ⟨i, hi, g, hti, htj, hx⟩
    · rintro (ha | ⟨i, hi, g, hti, hτ, hx⟩)
      · exact Or.inl ⟨k, hk, by rw [hc]; exact (before_mid_left hnd).2 ha⟩
      · exact Or.inr ⟨i, k, hi, hk, g, hti, by rw [hc]; exact hτ, hx, htk⟩
  have hordR : ∀ b, tn.ord t b ↔ b ∈ l₂ ∨ ∃ j, ∃ hj : j < cs.length, ∃ g,
      τ = some (g, false) ∧ cs[j].tag = some (g, true) ∧ b ∈ cs[j].ids := by
    intro b
    rw [h.ord]
    constructor
    · rintro (⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩)
      · obtain rfl := ht_only j hj (before_mem hb).1
        rw [hc] at hb; exact Or.inl ((before_mid_right hnd).1 hb)
      · obtain rfl := ht_only i hi hx
        rw [hc] at hti
        exact Or.inr ⟨j, hj, g, hti, htj, hy⟩
    · rintro (hb | ⟨j, hj, g, hτ, htj, hy⟩)
      · exact Or.inl ⟨k, hk, by rw [hc]; exact (before_mid_right hnd).2 hb⟩
      · exact Or.inr ⟨k, j, hk, hj, g, by rw [hc]; exact hτ, htj, htk, hy⟩
  have hlmu : ∀ w, w ∈ u.T ↔ w ∈ lm := hu.memT
  have hfresh : ∀ w ∈ lm, ∀ j (hj : j < cs.length), w ∉ cs[j].ids :=
    fun w hw j hj hwj => hlmT w hw ((h.mem w).2 ⟨j, hj, hwj⟩)
  have hτk : cs[k].tag = τ := by rw [hc]
  refine ⟨fun x => ?_, fun a b => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · -- membership
    rw [mem_decomposeWith_T, h.mem, hlmu]
    constructor
    · rintro (⟨⟨j, hj, hx⟩, hxt⟩ | hx)
      · exact ⟨j, by rw [hlen']; exact hj, (hids j hj x).2 (Or.inl ⟨hx, hxt⟩)⟩
      · exact ⟨k, by rw [hlen']; exact hk, (hids k hk x).2 (Or.inr ⟨rfl, hx⟩)⟩
    · rintro ⟨j, hj, hx⟩
      rw [hlen'] at hj
      rcases (hids j hj x).1 hx with ⟨hx, hxt⟩ | ⟨-, hx⟩
      · exact Or.inl ⟨⟨j, hj, hx⟩, hxt⟩
      · exact Or.inr hx
  · -- order
    have hcross : Cross cs' a b ↔ ∃ i j, ∃ hi : i < cs.length, ∃ hj : j < cs.length, ∃ g,
        cs[i].tag = some (g, false) ∧ cs[j].tag = some (g, true) ∧
        ((a ∈ cs[i].ids ∧ a ≠ t) ∨ (i = k ∧ a ∈ lm)) ∧ ((b ∈ cs[j].ids ∧ b ≠ t) ∨ (j = k ∧ b ∈ lm)) := by
      unfold Cross
      constructor
      · rintro ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩
        rw [hlen'] at hi hj
        exact ⟨i, j, hi, hj, g, by rw [← htag i hi]; exact hti, by rw [← htag j hj]; exact htj,
          (hids i hi a).1 hx, (hids j hj b).1 hy⟩
      · rintro ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩
        exact ⟨i, j, by rw [hlen']; exact hi, by rw [hlen']; exact hj, g,
          by rw [htag i hi]; exact hti, by rw [htag j hj]; exact htj, (hids i hi a).2 hx,
          (hids j hj b).2 hy⟩
    have hbef : (∃ j, ∃ hj : j < cs'.length, Before (cs'[j]).ids a b) ↔
        (∃ j, ∃ hj : j < cs.length, j ≠ k ∧ Before cs[j].ids a b) ∨ Before (l₁ ++ lm ++ l₂) a b := by
      constructor
      · rintro ⟨j, hj, hb⟩
        rw [hlen'] at hj
        rw [hgs j hj] at hb
        split_ifs at hb with hjk
        · exact Or.inr hb
        · exact Or.inl ⟨j, hj, Ne.symm hjk, hb⟩
      · rintro (⟨j, hj, hjk, hb⟩ | hb)
        · exact ⟨j, by rw [hlen']; exact hj, by rw [hgs j hj, if_neg (Ne.symm hjk)]; exact hb⟩
        · exact ⟨k, by rw [hlen']; exact hk, by rw [hgs k hk, if_pos rfl]; exact hb⟩
    show (decomposeWith tn t u).ord a b ↔ _
    simp only [decomposeWith]
    rw [hbef, hcross, hu.ord, hlmu, hlmu, hordL, hordR]
    have hidx : (a ∈ lm ∧ b ∈ lm ∧ lm.idxOf a < lm.idxOf b) ↔ Before lm a b :=
      (before_nodup_iff hu.nodup).symm
    rw [hidx]
    constructor
    · rintro (hb | ⟨ha | ⟨i, hi, g, hti, hτ, hx⟩, hbm⟩ | ⟨hb | ⟨j, hj, g, hτ, htj, hy⟩, ham⟩ |
          ⟨hab, hat, hbt⟩)
      · exact Or.inl (Or.inr (before_three.2 (Or.inr (Or.inl hb))))
      · exact Or.inl (Or.inr (before_three.2 (Or.inr (Or.inr (Or.inl ⟨ha, hbm⟩)))))
      · refine Or.inr ⟨i, k, hi, hk, g, hti, by rw [hτk]; exact hτ, Or.inl ⟨hx, fun e => ?_⟩,
          Or.inr ⟨rfl, hbm⟩⟩
        subst e
        obtain rfl := ht_only i hi hx
        rw [hτk, hτ] at hti; simp at hti
      · exact Or.inl (Or.inr (before_three.2 (Or.inr (Or.inr (Or.inr ⟨ham, hb⟩)))))
      · refine Or.inr ⟨k, j, hk, hj, g, by rw [hτk]; exact hτ, htj, Or.inr ⟨rfl, ham⟩,
          Or.inl ⟨hy, fun e => ?_⟩⟩
        subst e
        obtain rfl := ht_only j hj hy
        rw [hτk, hτ] at htj; simp at htj
      · rcases (h.ord a b).1 hab with ⟨j, hj, hb⟩ | ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩
        · by_cases hjk : j = k
          · subst hjk
            rw [hc, before_mid_ne hat hbt] at hb
            exact Or.inl (Or.inr (before_three.2 (Or.inl hb)))
          · exact Or.inl (Or.inl ⟨j, hj, hjk, hb⟩)
        · exact Or.inr ⟨i, j, hi, hj, g, hti, htj, Or.inl ⟨hx, hat⟩, Or.inl ⟨hy, hbt⟩⟩
    · rintro ((⟨j, hj, hjk, hb⟩ | hb) | ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩)
      · have hat : a ≠ t := fun e => hjk (ht_only j hj (e ▸ (before_mem hb).1))
        have hbt : b ≠ t := fun e => hjk (ht_only j hj (e ▸ (before_mem hb).2))
        exact Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inl ⟨j, hj, hb⟩), hat, hbt⟩))
      · rcases before_three.1 hb with hb | hb | ⟨ha, hbm⟩ | ⟨ham, hb'⟩
        · have hm := before_mem hb
          simp only [List.mem_append] at hm
          have hat : a ≠ t := fun e => by subst e; rcases hm.1 with h1 | h1 <;> contradiction
          have hbt : b ≠ t := fun e => by subst e; rcases hm.2 with h1 | h1 <;> contradiction
          refine Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inl ⟨k, hk, ?_⟩), hat, hbt⟩))
          rw [hc, before_mid_ne hat hbt]; exact hb
        · exact Or.inl hb
        · exact Or.inr (Or.inl ⟨Or.inl ha, hbm⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hb', ham⟩))
      · rcases hx with ⟨hx, hat⟩ | ⟨rfl, ham⟩ <;> rcases hy with ⟨hy, hbt⟩ | ⟨rfl, hbm⟩
        · exact Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inr ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩),
            hat, hbt⟩))
        · rw [hτk] at htj
          exact Or.inr (Or.inl ⟨Or.inr ⟨i, hi, g, hti, htj, hx⟩, hbm⟩)
        · rw [hτk] at hti
          exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨j, hj, g, hti, htj, hy⟩, ham⟩))
        · rw [hti] at htj; simp at htj
  · -- labels
    have hj' : j < cs.length := by rw [← hlen']; exact hj
    have hlab := h.lab k hk
    rw [hc] at hlab
    simp only [List.map_append, List.map_cons] at hlab
    obtain ⟨hl1, hl2⟩ := List.append_inj hlab (by simpa using hlen)
    have hl2' := List.cons.inj hl2
    show (cs'[j]).ids.map (decomposeWith tn t u).α = (cs'[j]).lab
    rw [hgs j hj']
    split_ifs with hjk
    · subst hjk
      simp only [List.map_append, decomposeWith]
      have e1 : l₁.map (fun x => if x ∈ u.T then u.α x else tn.α x) = xs₁ := by
        rw [← hl1]; refine List.map_congr_left fun x hx => ?_
        rw [if_neg fun h' => hlmT x ((hu.memT x).1 h') (hkT x (by rw [hc]; simp [hx]))]
      have e2 : l₂.map (fun x => if x ∈ u.T then u.α x else tn.α x) = xs₂ := by
        rw [← hl2'.2]; refine List.map_congr_left fun x hx => ?_
        rw [if_neg fun h' => hlmT x ((hu.memT x).1 h') (hkT x (by rw [hc]; simp [hx]))]
      have e3 : lm.map (fun x => if x ∈ u.T then u.α x else tn.α x) = bs := by
        rw [← hu.labels]; refine List.map_congr_left fun x hx => ?_
        rw [if_pos ((hu.memT x).2 hx)]
      rw [e1, e2, e3]
    · rw [← h.lab j hj']
      simp only [decomposeWith]
      refine List.map_congr_left fun x hx => ?_
      rw [if_neg fun h' => hlmT x ((hu.memT x).1 h') ((h.mem x).2 ⟨j, hj', hx⟩)]
  · -- distinct ids
    have hj' : j < cs.length := by rw [← hlen']; exact hj
    show (cs'[j]).ids.Nodup
    rw [hgs j hj']
    split_ifs with hjk
    · subst hjk
      rw [List.nodup_append, List.nodup_append]
      have := List.nodup_append.1 hnd
      refine ⟨⟨this.1, hu.nodup, fun a ha b hb => fun e => ?_⟩, (List.nodup_cons.1 this.2.1).2,
        fun a ha b hb => ?_⟩
      · subst e; exact hlmT a hb (hkT a (by rw [hc]; simp [ha]))
      · simp only [List.mem_append] at ha
        rcases ha with ha | ha
        · exact fun e => this.2.2 a ha b (by simp [hb]) e
        · exact fun e => by subst e; exact hlmT a ha (hkT a (by rw [hc]; simp [hb]))
    · exact h.nodup j hj'
  · -- disjointness
    have hi' : i < cs.length := by rw [← hlen']; exact hi
    have hj' : j < cs.length := by rw [← hlen']; exact hj
    intro hy
    rcases (hids i hi' x).1 hx with ⟨hx1, -⟩ | ⟨rfl, hxm⟩ <;>
      rcases (hids j hj' x).1 hy with ⟨hy1, -⟩ | ⟨rfl, hym⟩
    · exact h.disj i j hi' hj' hij x hx1 hy1
    · exact hfresh x hym i hi' hx1
    · exact hfresh x hxm j hj' hy1
    · exact hij rfl

/-- Tasks in chains of a given tag. -/
def InTag (cs : List (TCh A C)) (x : ℕ) (σ : Option (Bool × Bool)) : Prop :=
  ∃ i, ∃ hi : i < cs.length, cs[i].tag = σ ∧ x ∈ cs[i].ids

theorem cross_iff {cs : List (TCh A C)} {a b : ℕ} :
    Cross cs a b ↔ ∃ g, InTag cs a (some (g, false)) ∧ InTag cs b (some (g, true)) := by
  constructor
  · rintro ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩; exact ⟨g, ⟨i, hi, hti, hx⟩, ⟨j, hj, htj, hy⟩⟩
  · rintro ⟨g, ⟨i, hi, hti, hx⟩, ⟨j, hj, htj, hy⟩⟩; exact ⟨i, j, hi, hj, g, hti, htj, hx, hy⟩

/-- The singleton chains of a set network, all with the tag `τ`. -/
def singlesT (lm : List ℕ) (bs : List (A ⊕ C)) (τ : Option (Bool × Bool)) : List (TCh A C) :=
  (lm.zip bs).map fun p => ⟨[p.1], [p.2], τ⟩

theorem singlesT_get {lm : List ℕ} {bs : List (A ⊕ C)} {τ : Option (Bool × Bool)} {j : ℕ}
    (hj : j < (singlesT lm bs τ).length) :
    ∃ (hl : j < lm.length) (hb : j < bs.length), (singlesT lm bs τ)[j] = ⟨[lm[j]], [bs[j]], τ⟩ := by
  simp only [singlesT, List.length_map, List.length_zip, lt_min_iff] at hj
  exact ⟨hj.1, hj.2, by simp [singlesT]⟩

theorem mem_singlesT {lm : List ℕ} {bs : List (A ⊕ C)} {τ : Option (Bool × Bool)}
    (hl : lm.length = bs.length) {x : ℕ} :
    (∃ j, ∃ hj : j < (singlesT lm bs τ).length, x ∈ (singlesT lm bs τ)[j].ids) ↔ x ∈ lm := by
  constructor
  · rintro ⟨j, hj, hx⟩
    obtain ⟨hl', hb', he⟩ := singlesT_get hj
    rw [he] at hx; simp at hx; rw [hx]; exact List.getElem_mem hl'
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < (singlesT lm bs τ).length := by simp [singlesT]; omega
    obtain ⟨hl', hb', he⟩ := singlesT_get hj'
    exact ⟨j, hj', by rw [he]; simp⟩

set_option maxHeartbeats 2000000 in
/-- **A task forming its own chain decomposed by a set network.** -/
theorem step_set (h : TC tn cs) {k : ℕ} (hk : k < cs.length) {t : ℕ} {y : A ⊕ C}
    {τ : Option (Bool × Bool)} (hc : cs[k] = ⟨[t], [y], τ⟩) {u : TaskNetwork ℕ A C} {lm : List ℕ}
    {bs : List (A ⊕ C)} (hu : SetNet u lm bs) (hdisj : Disjoint tn.T u.T) :
    TC (decomposeWith tn t u) (cs.set k ⟨[], [], τ⟩ ++ singlesT lm bs τ) := by
  have hlm : lm.length = bs.length := by rw [← hu.labels, List.length_map]
  have htk : t ∈ cs[k].ids := by rw [hc]; simp
  have ht_only : ∀ j (hj : j < cs.length), t ∈ cs[j].ids → j = k := h.chain_of_mem hk htk
  have hlmT : ∀ x ∈ lm, x ∉ tn.T := fun x hx hT =>
    Finset.disjoint_left.1 hdisj hT ((hu.memT x).2 hx)
  have hfresh : ∀ w ∈ lm, ∀ j (hj : j < cs.length), w ∉ cs[j].ids :=
    fun w hw j hj hwj => hlmT w hw ((h.mem w).2 ⟨j, hj, hwj⟩)
  have hτk : cs[k].tag = τ := by rw [hc]
  set cs₁ := cs.set k ⟨[], [], τ⟩ with hcs₁
  have hlen₁ : cs₁.length = cs.length := by simp [cs₁]
  have hgs : ∀ j (hj : j < cs.length), cs₁[j]'(by simpa [cs₁] using hj) =
      if k = j then ⟨[], [], τ⟩ else cs[j] := fun j hj => by
    simp [cs₁, List.getElem_set]
  have hids₁ : ∀ j (hj : j < cs.length) x, x ∈ (cs₁[j]'(by simpa [cs₁] using hj)).ids ↔
      x ∈ cs[j].ids ∧ x ≠ t := fun j hj x => by
    rw [hgs j hj]; split_ifs with hjk
    · subst hjk; rw [hc]; simp
    · constructor
      · intro hx; exact ⟨hx, fun e => hjk (ht_only j hj (e ▸ hx)).symm⟩
      · exact fun h => h.1
  have htag₁ : ∀ j (hj : j < cs.length), (cs₁[j]'(by simpa [cs₁] using hj)).tag = cs[j].tag :=
    fun j hj => by
      rw [hgs j hj]; split_ifs with hjk
      · subst hjk; rw [hc]
      · rfl
  have hall : ∀ {P : TCh A C → Prop},
      (∃ j, ∃ hj : j < (cs₁ ++ singlesT lm bs τ).length, P (cs₁ ++ singlesT lm bs τ)[j]) ↔
        (∃ j, ∃ hj : j < cs.length, P (cs₁[j]'(by simpa [cs₁] using hj))) ∨
          (∃ j, ∃ hj : j < (singlesT lm bs τ).length, P (singlesT lm bs τ)[j]) := by
    intro P
    rw [AcycHard.exists_idx_append]
    constructor
    · rintro (⟨j, hj, hP⟩ | h2)
      · exact Or.inl ⟨j, by simpa [cs₁] using hj, hP⟩
      · exact Or.inr h2
    · rintro (⟨j, hj, hP⟩ | h2)
      · exact Or.inl ⟨j, by simpa [cs₁] using hj, hP⟩
      · exact Or.inr h2
  have hmemN : ∀ x, (∃ j, ∃ hj : j < (cs₁ ++ singlesT lm bs τ).length,
      x ∈ (cs₁ ++ singlesT lm bs τ)[j].ids) ↔ (∃ j, ∃ hj : j < cs.length, x ∈ cs[j].ids ∧ x ≠ t) ∨ x ∈ lm := by
    intro x
    have e := hall (P := fun c => x ∈ c.ids)
    beta_reduce at e
    rw [e, mem_singlesT hlm]
    constructor
    · rintro (⟨j, hj, hx⟩ | hx)
      · exact Or.inl ⟨j, hj, (hids₁ j hj x).1 hx⟩
      · exact Or.inr hx
    · rintro (⟨j, hj, hx⟩ | hx)
      · exact Or.inl ⟨j, hj, (hids₁ j hj x).2 hx⟩
      · exact Or.inr hx
  have hbefN : ∀ a b, (∃ j, ∃ hj : j < (cs₁ ++ singlesT lm bs τ).length,
      Before (cs₁ ++ singlesT lm bs τ)[j].ids a b) ↔
        ∃ j, ∃ hj : j < cs.length, j ≠ k ∧ Before cs[j].ids a b := by
    intro a b
    have e := hall (P := fun c => Before c.ids a b)
    beta_reduce at e
    rw [e]
    constructor
    · rintro (⟨j, hj, hb⟩ | ⟨j, hj, hb⟩)
      · rw [hgs j hj] at hb
        split_ifs at hb with hjk
        · exact absurd hb before_nil
        · exact ⟨j, hj, Ne.symm hjk, hb⟩
      · obtain ⟨hl', hb', he⟩ := singlesT_get hj
        rw [he] at hb
        obtain ⟨l₁, l₂, e, hb2⟩ := hb
        rcases l₁ with _ | ⟨z, l₁⟩
        · simp only [List.nil_append, List.cons.injEq] at e; rw [← e.2] at hb2; simp at hb2
        · have := congrArg List.length e; simp at this
    · rintro ⟨j, hj, hjk, hb⟩
      exact Or.inl ⟨j, hj, by rw [hgs j hj, if_neg (Ne.symm hjk)]; exact hb⟩
  have htagN : ∀ x σ, InTag (cs₁ ++ singlesT lm bs τ) x σ ↔ (InTag cs x σ ∧ x ≠ t) ∨ (σ = τ ∧ x ∈ lm) := by
    intro x σ
    unfold InTag
    have e := hall (P := fun c => c.tag = σ ∧ x ∈ c.ids)
    beta_reduce at e
    rw [e]
    constructor
    · rintro (⟨j, hj, htj, hx⟩ | ⟨j, hj, htj, hx⟩)
      · rw [htag₁ j hj] at htj
        obtain ⟨hx, hxt⟩ := (hids₁ j hj x).1 hx
        exact Or.inl ⟨⟨j, hj, htj, hx⟩, hxt⟩
      · obtain ⟨hl', hb', he⟩ := singlesT_get hj
        rw [he] at htj hx
        simp at hx
        exact Or.inr ⟨htj.symm, by rw [hx]; exact List.getElem_mem hl'⟩
    · rintro (⟨⟨j, hj, htj, hx⟩, hxt⟩ | ⟨rfl, hx⟩)
      · exact Or.inl ⟨j, hj, by rw [htag₁ j hj]; exact htj, (hids₁ j hj x).2 ⟨hx, hxt⟩⟩
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have hj' : j < (singlesT lm bs σ).length := by simp [singlesT]; omega
        obtain ⟨hl', hb', he⟩ := singlesT_get hj'
        exact Or.inr ⟨j, hj', by rw [he], by rw [he]; simp⟩
  have hordL : ∀ a, tn.ord a t ↔ ∃ g, τ = some (g, true) ∧ InTag cs a (some (g, false)) := by
    intro a
    rw [h.ord, cross_iff]
    constructor
    · rintro (⟨j, hj, hb⟩ | ⟨g, hx, ⟨j, hj, htj, hy⟩⟩)
      · obtain rfl := ht_only j hj (before_mem hb).2
        rw [hc] at hb
        rcases before_cons.1 hb with ⟨-, h'⟩ | h' <;> simp_all [before_nil]
      · obtain rfl := ht_only j hj hy
        exact ⟨g, by rw [← hτk]; exact htj, hx⟩
    · rintro ⟨g, hτ, hx⟩
      exact Or.inr ⟨g, hx, ⟨k, hk, by rw [hτk]; exact hτ, htk⟩⟩
  have hordR : ∀ b, tn.ord t b ↔ ∃ g, τ = some (g, false) ∧ InTag cs b (some (g, true)) := by
    intro b
    rw [h.ord, cross_iff]
    constructor
    · rintro (⟨j, hj, hb⟩ | ⟨g, ⟨i, hi, hti, hx⟩, hy⟩)
      · obtain rfl := ht_only j hj (before_mem hb).1
        rw [hc] at hb
        rcases before_cons.1 hb with ⟨-, h'⟩ | h' <;> simp_all [before_nil]
      · obtain rfl := ht_only i hi hx
        exact ⟨g, by rw [← hτk]; exact hti, hy⟩
    · rintro ⟨g, hτ, hy⟩
      exact Or.inr ⟨g, ⟨k, hk, by rw [hτk]; exact hτ, htk⟩, hy⟩
  have hlmu : ∀ w, w ∈ u.T ↔ w ∈ lm := hu.memT
  have hinT : ∀ x σ, InTag cs x σ → x ∈ tn.T := fun x σ ⟨j, hj, _, hx⟩ => (h.mem x).2 ⟨j, hj, hx⟩
  refine ⟨fun x => ?_, fun a b => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · rw [mem_decomposeWith_T, h.mem, hlmu, hmemN]
    constructor
    · rintro (⟨⟨j, hj, hx⟩, hxt⟩ | hx)
      · exact Or.inl ⟨j, hj, hx, hxt⟩
      · exact Or.inr hx
    · rintro (⟨j, hj, hx, hxt⟩ | hx)
      · exact Or.inl ⟨⟨j, hj, hx⟩, hxt⟩
      · exact Or.inr hx
  · show (decomposeWith tn t u).ord a b ↔ _
    simp only [decomposeWith]
    rw [hbefN, cross_iff, hlmu, hlmu, hordL, hordR]
    simp only [htagN]
    have hnou : ¬ u.ord a b := hu.ord a b
    constructor
    · rintro (hab | ⟨⟨g, hτ, hx⟩, hbm⟩ | ⟨⟨g, hτ, hy⟩, ham⟩ | ⟨hab, hat, hbt⟩)
      · exact absurd hab hnou
      · exact Or.inr ⟨g, Or.inl ⟨hx, fun e => by
          subst e; obtain ⟨i, hi, hti, hx⟩ := hx
          obtain rfl := ht_only i hi hx; rw [hτk, hτ] at hti; simp at hti⟩, Or.inr ⟨hτ.symm, hbm⟩⟩
      · exact Or.inr ⟨g, Or.inr ⟨hτ.symm, ham⟩, Or.inl ⟨hy, fun e => by
          subst e; obtain ⟨j, hj, htj, hy⟩ := hy
          obtain rfl := ht_only j hj hy; rw [hτk, hτ] at htj; simp at htj⟩⟩
      · rcases (h.ord a b).1 hab with ⟨j, hj, hb⟩ | hcr
        · refine Or.inl ⟨j, hj, fun e => ?_, hb⟩
          subst e; rw [hc] at hb
          rcases before_cons.1 hb with ⟨e, -⟩ | h' <;> simp_all [before_nil]
        · obtain ⟨g, hx, hy⟩ := cross_iff.1 hcr
          exact Or.inr ⟨g, Or.inl ⟨hx, hat⟩, Or.inl ⟨hy, hbt⟩⟩
    · rintro (⟨j, hj, hjk, hb⟩ | ⟨g, ⟨hx, hat⟩ | ⟨hτ, ham⟩, ⟨hy, hbt⟩ | ⟨hτ', hbm⟩⟩)
      · have hat : a ≠ t := fun e => hjk (ht_only j hj (e ▸ (before_mem hb).1))
        have hbt : b ≠ t := fun e => hjk (ht_only j hj (e ▸ (before_mem hb).2))
        exact Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inl ⟨j, hj, hb⟩), hat, hbt⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨(h.ord a b).2 (Or.inr (cross_iff.2 ⟨g, hx, hy⟩)), hat, hbt⟩))
      · exact Or.inr (Or.inl ⟨⟨g, hτ'.symm, hx⟩, hbm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨g, hτ.symm, hy⟩, ham⟩))
      · rw [← hτ] at hτ'; simp at hτ'
  · -- labels
    have hlab' : ∀ x ∈ lm, (decomposeWith tn t u).α x = u.α x := fun x hx => by
      simp [decomposeWith, (hu.memT x).2 hx]
    rw [List.getElem_append]
    split_ifs with hj1
    · have hj' : j < cs.length := by simpa [cs₁] using hj1
      show (cs₁[j]).ids.map (decomposeWith tn t u).α = (cs₁[j]).lab
      rw [hgs j hj']
      split_ifs with hjk
      · rfl
      · rw [← h.lab j hj']
        refine List.map_congr_left fun x hx => ?_
        simp only [decomposeWith]
        rw [if_neg fun h' => hlmT x ((hu.memT x).1 h') ((h.mem x).2 ⟨j, hj', hx⟩)]
    · have hj2 : j - cs₁.length < (singlesT lm bs τ).length := by
        simp only [List.length_append] at hj; omega
      obtain ⟨hl', hb', he⟩ := singlesT_get hj2
      rw [he]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [hlab' _ (List.getElem_mem hl')]
      have := congrArg (·[j - cs₁.length]?) hu.labels
      simp only [List.getElem?_map, List.getElem?_eq_getElem hl', List.getElem?_eq_getElem hb',
        Option.map_some, Option.some.injEq] at this
      exact this
  · rw [List.getElem_append]
    split_ifs with hj1
    · have hj' : j < cs.length := by simpa [cs₁] using hj1
      show (cs₁[j]).ids.Nodup
      rw [hgs j hj']
      split_ifs
      · exact List.nodup_nil
      · exact h.nodup j hj'
    · have hj2 : j - cs₁.length < (singlesT lm bs τ).length := by
        simp only [List.length_append] at hj; omega
      obtain ⟨hl', hb', he⟩ := singlesT_get hj2
      rw [he]; exact List.nodup_singleton _
  · -- disjointness
    intro hy
    have key : ∀ j (hj : j < (cs₁ ++ singlesT lm bs τ).length) x, x ∈ (cs₁ ++ singlesT lm bs τ)[j].ids →
        (∃ hj' : j < cs.length, x ∈ cs[j].ids ∧ x ≠ t) ∨
          (∃ hj' : cs.length ≤ j, ∃ hl : j - cs.length < lm.length, x = lm[j - cs.length]) := by
      intro j hj x hx
      rw [List.getElem_append] at hx
      split_ifs at hx with hj1
      · have hj' : j < cs.length := by simpa [cs₁] using hj1
        exact Or.inl ⟨hj', (hids₁ j hj' x).1 hx⟩
      · have hj2 : j - cs₁.length < (singlesT lm bs τ).length := by
          simp only [List.length_append] at hj; omega
        obtain ⟨hl', hb', he⟩ := singlesT_get hj2
        rw [he] at hx; simp at hx
        exact Or.inr ⟨by simpa [cs₁] using hj1, by simpa [cs₁] using hl', by simpa [cs₁] using hx⟩
    rcases key i hi x hx with ⟨hi', hxi, -⟩ | ⟨hi', hli, rfl⟩ <;>
      rcases key j hj _ hy with ⟨hj', hxj, -⟩ | ⟨hj', hlj, hxe⟩
    · exact h.disj i j hi' hj' hij _ hxi hxj
    · exact hfresh _ (by rw [hxe]; exact List.getElem_mem hlj) i hi' hxi
    · exact hfresh _ (List.getElem_mem hli) j hj' hxj
    · have := (List.Nodup.getElem_inj_iff hu.nodup).1 hxe
      omega


set_option maxHeartbeats 2000000 in
/-- **Splitting a post-chain**: when the group has no pending pre-tasks and no other post-tasks,
the front part of its post-chain can be read as a pre-chain. -/
theorem split (h : TC tn cs) {k : ℕ} (hk : k < cs.length) {l₁ l₂ : List ℕ}
    {xs₁ xs₂ : List (A ⊕ C)} {g : Bool} (hc : cs[k] = ⟨l₁ ++ l₂, xs₁ ++ xs₂, some (g, true)⟩)
    (hlen : l₁.length = xs₁.length)
    (hpre : ∀ i (hi : i < cs.length), cs[i].tag = some (g, false) → cs[i].ids = [])
    (hpost : ∀ i (hi : i < cs.length), i ≠ k → cs[i].tag = some (g, true) → cs[i].ids = []) :
    TC tn (cs.set k ⟨l₂, xs₂, some (g, true)⟩ ++ [⟨l₁, xs₁, some (g, false)⟩]) := by
  have hnd := h.nodup k hk
  rw [hc] at hnd
  have hlab := h.lab k hk
  rw [hc] at hlab
  simp only [List.map_append] at hlab
  obtain ⟨hl1, hl2⟩ := List.append_inj hlab (by simpa using hlen)
  set cs₁ := cs.set k ⟨l₂, xs₂, some (g, true)⟩ with hcs₁
  set e : TCh A C := ⟨l₁, xs₁, some (g, false)⟩ with he
  have hlen₁ : cs₁.length = cs.length := by simp [cs₁]
  have hgs : ∀ j (hj : j < cs.length), cs₁[j]'(by simpa [cs₁] using hj) =
      if k = j then ⟨l₂, xs₂, some (g, true)⟩ else cs[j] := fun j hj => by
    simp [cs₁, List.getElem_set]
  have hex : ∀ {P : TCh A C → Prop}, (∃ j, ∃ hj : j < (cs₁ ++ [e]).length, P (cs₁ ++ [e])[j]) ↔
      (∃ j, ∃ hj : j < cs.length, j ≠ k ∧ P cs[j]) ∨ P ⟨l₂, xs₂, some (g, true)⟩ ∨ P e := by
    intro P
    rw [AcycHard.exists_idx_append]
    constructor
    · rintro (⟨j, hj, hP⟩ | ⟨j, hj, hP⟩)
      · have hj' : j < cs.length := by simpa [cs₁] using hj
        rw [hgs j hj'] at hP
        split_ifs at hP with h2
        · exact Or.inr (Or.inl hP)
        · exact Or.inl ⟨j, hj', Ne.symm h2, hP⟩
      · simp at hj; subst hj; exact Or.inr (Or.inr hP)
    · rintro (⟨j, hj, hjk, hP⟩ | hP | hP)
      · exact Or.inl ⟨j, by simpa [cs₁] using hj, by rw [hgs j hj, if_neg (Ne.symm hjk)]; exact hP⟩
      · exact Or.inl ⟨k, by simpa [cs₁] using hk, by rw [hgs k hk, if_pos rfl]; exact hP⟩
      · exact Or.inr ⟨0, by simp, hP⟩
  have hexo : ∀ {P : TCh A C → Prop}, (∃ j, ∃ hj : j < cs.length, P cs[j]) ↔
      (∃ j, ∃ hj : j < cs.length, j ≠ k ∧ P cs[j]) ∨ P ⟨l₁ ++ l₂, xs₁ ++ xs₂, some (g, true)⟩ := by
    intro P
    constructor
    · rintro ⟨j, hj, hP⟩
      by_cases hjk : j = k
      · subst hjk; rw [hc] at hP; exact Or.inr hP
      · exact Or.inl ⟨j, hj, hjk, hP⟩
    · rintro (⟨j, hj, -, hP⟩ | hP)
      · exact ⟨j, hj, hP⟩
      · exact ⟨k, hk, by rw [hc]; exact hP⟩
  -- tasks of other chains, by tag
  have hpreE : ∀ j (hj : j < cs.length), j ≠ k → cs[j].tag = some (g, false) → ∀ x, x ∉ cs[j].ids :=
    fun j hj _ ht x hx => by rw [hpre j hj ht] at hx; simp at hx
  have hpostE : ∀ j (hj : j < cs.length), j ≠ k → cs[j].tag = some (g, true) → ∀ x, x ∉ cs[j].ids :=
    fun j hj hjk ht x hx => by rw [hpost j hj hjk ht] at hx; simp at hx
  have hInO : ∀ x σ, InTag cs x σ ↔ (∃ j, ∃ hj : j < cs.length, j ≠ k ∧ cs[j].tag = σ ∧ x ∈ cs[j].ids) ∨
      (σ = some (g, true) ∧ (x ∈ l₁ ∨ x ∈ l₂)) := by
    intro x σ; unfold InTag
    rw [hexo (P := fun c => c.tag = σ ∧ x ∈ c.ids)]
    simp only [List.mem_append]
    constructor
    · rintro (h1 | ⟨h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h2.symm, h3⟩
    · rintro (h1 | ⟨h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h2.symm, h3⟩
  have hInN : ∀ x σ, InTag (cs₁ ++ [e]) x σ ↔ (∃ j, ∃ hj : j < cs.length, j ≠ k ∧ cs[j].tag = σ ∧ x ∈ cs[j].ids) ∨
      (σ = some (g, true) ∧ x ∈ l₂) ∨ (σ = some (g, false) ∧ x ∈ l₁) := by
    intro x σ; unfold InTag
    rw [hex (P := fun c => c.tag = σ ∧ x ∈ c.ids)]
    constructor
    · rintro (h1 | ⟨h2, h3⟩ | ⟨h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h2.symm, h3⟩)
      · exact Or.inr (Or.inr ⟨h2.symm, h3⟩)
    · rintro (h1 | ⟨h2, h3⟩ | ⟨h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h2.symm, h3⟩)
      · exact Or.inr (Or.inr ⟨h2.symm, h3⟩)
  refine ⟨fun x => ?_, fun a b => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · rw [h.mem, hexo (P := fun c => x ∈ c.ids), hex (P := fun c => x ∈ c.ids)]
    simp only [List.mem_append, e]
    exact or_congr_right or_comm
  · rw [h.ord, hexo (P := fun c => Before c.ids a b), hex (P := fun c => Before c.ids a b), cross_iff,
      cross_iff, PCP.before_append]
    simp only [hInO, hInN]
    constructor
    · rintro ((h1 | h2 | h3 | h4) | ⟨g', h5, h6⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (Or.inr h2))
      · exact Or.inr ⟨g, Or.inr (Or.inr ⟨rfl, h3.1⟩), Or.inr (Or.inl ⟨rfl, h3.2⟩)⟩
      · exact Or.inl (Or.inr (Or.inl h4))
      · rcases h5 with ⟨j, hj, hjk, htj, hx⟩ | ⟨h5, -⟩
        · rcases h6 with ⟨j', hj', hjk', htj', hy⟩ | ⟨h6, hy⟩
          · exact Or.inr ⟨g', Or.inl ⟨j, hj, hjk, htj, hx⟩, Or.inl ⟨j', hj', hjk', htj', hy⟩⟩
          · simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h6
            subst h6
            exact absurd hx (hpreE j hj hjk htj a)
        · simp at h5
    · rintro ((h1 | h2 | h3) | ⟨g', h5, h6⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (Or.inr (Or.inr h2)))
      · exact Or.inl (Or.inr (Or.inl h3))
      · rcases h5 with ⟨j, hj, hjk, htj, hx⟩ | ⟨h5, -⟩ | ⟨h5, hx⟩
        · rcases h6 with ⟨j', hj', hjk', htj', hy⟩ | ⟨h6, hy⟩ | ⟨h6, -⟩
          · exact Or.inr ⟨g', Or.inl ⟨j, hj, hjk, htj, hx⟩, Or.inl ⟨j', hj', hjk', htj', hy⟩⟩
          · simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h6
            subst h6
            exact absurd hx (hpreE j hj hjk htj a)
          · simp at h6
        · simp at h5
        · simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h5
          subst h5
          rcases h6 with ⟨j', hj', hjk', htj', hy⟩ | ⟨-, hy⟩ | ⟨h6, -⟩
          · exact absurd hy (hpostE j' hj' hjk' htj' b)
          · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hx, hy⟩)))
          · simp at h6
  · -- labels
    rw [List.getElem_append]
    split_ifs with hj1
    · have hj' : j < cs.length := by simpa [cs₁] using hj1
      show (cs₁[j]).ids.map tn.α = (cs₁[j]).lab
      rw [hgs j hj']
      split_ifs with hjk
      · exact hl2
      · exact h.lab j hj'
    · simp [e, hl1]
  · rw [List.getElem_append]
    split_ifs with hj1
    · have hj' : j < cs.length := by simpa [cs₁] using hj1
      show (cs₁[j]).ids.Nodup
      rw [hgs j hj']
      split_ifs
      · exact (List.nodup_append.1 hnd).2.1
      · exact h.nodup j hj'
    · simp [e]; exact (List.nodup_append.1 hnd).1
  · -- disjointness
    intro hy
    have key : ∀ j (hj : j < (cs₁ ++ [e]).length) x, x ∈ (cs₁ ++ [e])[j].ids →
        (∃ hj' : j < cs.length, j ≠ k ∧ x ∈ cs[j].ids) ∨ (j = k ∧ x ∈ l₂) ∨ (j = cs.length ∧ x ∈ l₁) := by
      intro j hj x hx
      rw [List.getElem_append] at hx
      split_ifs at hx with hj1
      · have hj' : j < cs.length := by simpa [cs₁] using hj1
        rw [hgs j hj'] at hx
        split_ifs at hx with hjk
        · exact Or.inr (Or.inl ⟨hjk.symm, hx⟩)
        · exact Or.inl ⟨hj', Ne.symm hjk, hx⟩
      · simp [cs₁] at hj1 hj
        exact Or.inr (Or.inr ⟨by omega, by simpa [e] using hx⟩)
    have hk1 : ∀ x ∈ l₁, x ∈ cs[k].ids := fun x hx => by rw [hc]; simp [hx]
    have hk2 : ∀ x ∈ l₂, x ∈ cs[k].ids := fun x hx => by rw [hc]; simp [hx]
    have h12 : ∀ x ∈ l₁, x ∉ l₂ := fun x h1 h2 => (List.nodup_append.1 hnd).2.2 x h1 x h2 rfl
    rcases key i hi x hx with ⟨hi', hik, hxi⟩ | ⟨rfl, hx2⟩ | ⟨rfl, hx1⟩ <;>
      rcases key j hj x hy with ⟨hj', hjk, hxj⟩ | ⟨rfl, hy2⟩ | ⟨rfl, hy1⟩
    · exact h.disj i j hi' hj' hij x hxi hxj
    · exact h.disj i _ hi' hk hik x hxi (hk2 x hy2)
    · exact h.disj i _ hi' hk hik x hxi (hk1 x hy1)
    · exact h.disj _ j hk hj' (Ne.symm hjk) x (hk2 x hx2) hxj
    · exact hij rfl
    · exact h12 x hy1 hx2
    · exact h.disj _ j hk hj' (Ne.symm hjk) x (hk1 x hx1) hxj
    · exact h12 x hx1 hy2
    · exact hij rfl

/-- **Re-tagging a free chain** as the post-chain of a group without pre-tasks. -/
theorem retag (h : TC tn cs) {k : ℕ} (hk : k < cs.length) {ids : List ℕ} {lab : List (A ⊕ C)} {g : Bool}
    (hc : cs[k] = ⟨ids, lab, none⟩)
    (hpre : ∀ i (hi : i < cs.length), cs[i].tag = some (g, false) → cs[i].ids = []) :
    TC tn (cs.set k ⟨ids, lab, some (g, true)⟩) := by
  have hgs : ∀ j (hj : j < cs.length), (cs.set k ⟨ids, lab, some (g, true)⟩)[j]'(by simpa using hj) =
      if k = j then ⟨ids, lab, some (g, true)⟩ else cs[j] := fun j hj => by
    simp [List.getElem_set]
  have hids : ∀ j (hj : j < cs.length), ((cs.set k ⟨ids, lab, some (g, true)⟩)[j]'(by simpa using hj)).ids =
      cs[j].ids := fun j hj => by
    rw [hgs j hj]; split_ifs with hjk
    · subst hjk; rw [hc]
    · rfl
  have hlab : ∀ j (hj : j < cs.length), ((cs.set k ⟨ids, lab, some (g, true)⟩)[j]'(by simpa using hj)).lab =
      cs[j].lab := fun j hj => by
    rw [hgs j hj]; split_ifs with hjk
    · subst hjk; rw [hc]
    · rfl
  refine ⟨fun x => ?_, fun a b => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · rw [h.mem]; simp only [List.length_set]
    exact exists_congr fun j => ⟨fun ⟨hj, hx⟩ => ⟨hj, by rw [hids j hj]; exact hx⟩,
      fun ⟨hj, hx⟩ => ⟨hj, by rw [hids j hj] at hx; exact hx⟩⟩
  · rw [h.ord, cross_iff, cross_iff]
    unfold InTag
    simp only [List.length_set]
    constructor
    · rintro (⟨j, hj, hb⟩ | ⟨g', ⟨i, hi, hti, hx⟩, ⟨j, hj, htj, hy⟩⟩)
      · exact Or.inl ⟨j, hj, by rw [hids j hj]; exact hb⟩
      · have hik : i ≠ k := fun e => by subst e; rw [hc] at hti; simp at hti
        have hjk : j ≠ k := fun e => by subst e; rw [hc] at htj; simp at htj
        refine Or.inr ⟨g', ⟨i, hi, ?_, by rw [hids i hi]; exact hx⟩, ⟨j, hj, ?_, by rw [hids j hj]; exact hy⟩⟩
        · rw [hgs i hi, if_neg (Ne.symm hik)]; exact hti
        · rw [hgs j hj, if_neg (Ne.symm hjk)]; exact htj
    · rintro (⟨j, hj, hb⟩ | ⟨g', ⟨i, hi, hti, hx⟩, ⟨j, hj, htj, hy⟩⟩)
      · exact Or.inl ⟨j, hj, by rw [hids j hj] at hb; exact hb⟩
      · rw [hids i hi] at hx; rw [hids j hj] at hy
        have hik : i ≠ k := fun e => by rw [hgs i hi, if_pos e.symm] at hti; simp at hti
        rw [hgs i hi, if_neg (Ne.symm hik)] at hti
        by_cases hjk : j = k
        · subst hjk
          rw [hgs j hj, if_pos rfl] at htj
          simp only [Option.some.injEq, Prod.mk.injEq, and_true] at htj
          subst htj
          rw [hpre i hi hti] at hx; simp at hx
        · rw [hgs j hj, if_neg (Ne.symm hjk)] at htj
          exact Or.inr ⟨g', ⟨i, hi, hti, hx⟩, ⟨j, hj, htj, hy⟩⟩
  · have hj' : j < cs.length := by simpa using hj
    rw [hids j hj', hlab j hj']; exact h.lab j hj'
  · have hj' : j < cs.length := by simpa using hj
    rw [hids j hj']; exact h.nodup j hj'
  · have hi' : i < cs.length := by simpa using hi
    have hj' : j < cs.length := by simpa using hj
    rw [hids i hi'] at hx; rw [hids j hj']
    exact h.disj i j hi' hj' hij x hx

/-- A sequence network is a single free chain. -/
theorem of_isSeqNet {l : List ℕ} {xs : List (A ⊕ C)} (h : tn.IsSeqNet l xs) : TC tn [⟨l, xs, none⟩] where
  mem x := by rw [h.memT]; simp
  ord a b := by
    rw [h.ord, ← before_nodup_iff h.nodup]
    simp [Cross]
  lab j hj := by
    simp at hj; subst hj; exact h.labels
  nodup j hj := by
    simp at hj; subst hj; exact h.nodup
  disj i j hi hj hij := by simp at hi hj; omega

end TC

end HardTR

end FOND
