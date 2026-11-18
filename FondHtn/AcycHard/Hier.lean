import FondHtn.PCP.ChainNet
import FondHtn.FixedMethods
import HtnPlanning.Core.TONormalForm
import HtnPlanning.Core.Decomposition
/-!
# Networks of labelled chains and their decomposition

`FOND.AcycHard.UC tn cs`: the task network `tn` is the disjoint union of the chains `cs`; a chain
is a list of task ids with their labels (primitive or compound), totally ordered by position,
and tasks of different chains are unordered.

Decomposition steps (`HTN.decomposeWith`) on such networks:

* `FOND.AcycHard.UC.step_seq` — a task inside a chain decomposed by a *sequence* network: the
  task is replaced by the sequence in its chain;
* `FOND.AcycHard.UC.step_set` — a task forming a chain of its own decomposed by a *set* network
  (no order): the chain is emptied and every subtask forms a new chain.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

open HTN

variable {I : Type} [DecidableEq I]

/-! ## Order in lists -/

theorem before_nodup_iff {l : List I} (hl : l.Nodup) {a b : I} :
    Before l a b ↔ a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b := by
  rw [PCP.before_iff_idx]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    have hil : i < l.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
    have hjl : j < l.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
    rw [List.getElem?_eq_getElem hil, Option.some.injEq] at hi
    rw [List.getElem?_eq_getElem hjl, Option.some.injEq] at hj
    subst hi hj
    refine ⟨List.getElem_mem _, List.getElem_mem _, ?_⟩
    rw [List.Nodup.idxOf_getElem hl, List.Nodup.idxOf_getElem hl]
    exact hij
  · rintro ⟨ha, hb, hlt⟩
    exact ⟨_, _, hlt, by simp [List.getElem?_idxOf ha], by simp [List.getElem?_idxOf hb]⟩

theorem before_mid_left {l₁ l₂ : List I} {t a : I} (hnd : (l₁ ++ t :: l₂).Nodup) :
    Before (l₁ ++ t :: l₂) a t ↔ a ∈ l₁ := by
  rw [PCP.before_append, before_cons]
  have ht1 : t ∉ l₁ := fun h => (List.nodup_append.1 hnd).2.2 t h t (by simp) rfl
  have ht2 : t ∉ l₂ := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  constructor
  · rintro (h | ⟨h, -⟩ | ⟨-, h⟩ | h)
    · exact absurd (before_mem h).2 ht1
    · exact h
    · exact absurd h ht2
    · exact absurd (before_mem h).2 ht2
  · intro h; exact Or.inr (Or.inl ⟨h, by simp⟩)

theorem before_mid_right {l₁ l₂ : List I} {t b : I} (hnd : (l₁ ++ t :: l₂).Nodup) :
    Before (l₁ ++ t :: l₂) t b ↔ b ∈ l₂ := by
  rw [PCP.before_append, before_cons]
  have ht1 : t ∉ l₁ := fun h => (List.nodup_append.1 hnd).2.2 t h t (by simp) rfl
  have ht2 : t ∉ l₂ := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  constructor
  · rintro (h | ⟨h, -⟩ | ⟨-, h⟩ | h)
    · exact absurd (before_mem h).1 ht1
    · exact absurd h ht1
    · exact h
    · exact absurd (before_mem h).1 ht2
  · intro h; exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))

theorem before_mid_ne {l₁ l₂ : List I} {t a b : I} (ha : a ≠ t) (hb : b ≠ t) :
    Before (l₁ ++ t :: l₂) a b ↔ Before (l₁ ++ l₂) a b := by
  rw [PCP.before_append, PCP.before_append, before_cons]
  simp only [List.mem_cons, hb, false_or, ha, false_and]

theorem before_three {l₁ m l₂ : List I} {a b : I} :
    Before (l₁ ++ m ++ l₂) a b ↔
      Before (l₁ ++ l₂) a b ∨ Before m a b ∨ (a ∈ l₁ ∧ b ∈ m) ∨ (a ∈ m ∧ b ∈ l₂) := by
  rw [PCP.before_append, PCP.before_append, PCP.before_append]
  simp only [List.mem_append]
  tauto

/-! ## Unions of chains -/

/-- A chain: task ids and their labels. -/
abbrev Ch (I A C : Type) := List I × List (A ⊕ C)

variable {A C : Type}

/-- **The task network is the disjoint union of the chains.** -/
structure UC (tn : TaskNetwork I A C) (cs : List (Ch I A C)) : Prop where
  mem : ∀ x, x ∈ tn.T ↔ ∃ j, ∃ hj : j < cs.length, x ∈ cs[j].1
  ord : ∀ x y, tn.ord x y ↔ ∃ j, ∃ hj : j < cs.length, Before cs[j].1 x y
  lab : ∀ j (hj : j < cs.length), cs[j].1.map tn.α = cs[j].2
  nodup : ∀ j (hj : j < cs.length), cs[j].1.Nodup
  disj : ∀ i j (hi : i < cs.length) (hj : j < cs.length), i ≠ j → ∀ x ∈ cs[i].1, x ∉ cs[j].1

/-- A set network: the ids `l` with labels `bs`, no order. -/
structure SetNet (tn : TaskNetwork I A C) (l : List I) (bs : List (A ⊕ C)) : Prop where
  nodup : l.Nodup
  memT : ∀ x, x ∈ tn.T ↔ x ∈ l
  labels : l.map tn.α = bs
  ord : ∀ x y, ¬ tn.ord x y

namespace UC

variable {tn : TaskNetwork I A C} {cs : List (Ch I A C)}

theorem chain_of_mem (h : UC tn cs) {k : ℕ} (hk : k < cs.length) {x : I} (hx : x ∈ cs[k].1) :
    ∀ j (hj : j < cs.length), x ∈ cs[j].1 → j = k := by
  intro j hj hxj
  by_contra hne
  exact h.disj k j hk hj (Ne.symm hne) x hx hxj

/-- **A task inside a chain decomposed by a sequence network.** -/
theorem step_seq (h : UC tn cs) {k : ℕ} (hk : k < cs.length) {l₁ l₂ : List I}
    {xs₁ xs₂ : List (A ⊕ C)} {t : I} {y : A ⊕ C} (hc : cs[k] = (l₁ ++ t :: l₂, xs₁ ++ y :: xs₂))
    (hlen : l₁.length = xs₁.length) {u : TaskNetwork I A C} {lm : List I} {bs : List (A ⊕ C)}
    (hu : u.IsSeqNet lm bs) (hdisj : Disjoint tn.T u.T) :
    UC (decomposeWith tn t u) (cs.set k (l₁ ++ lm ++ l₂, xs₁ ++ bs ++ xs₂)) := by
  have hnd := h.nodup k hk
  rw [hc] at hnd
  have hkT : ∀ x ∈ cs[k].1, x ∈ tn.T := fun x hx => (h.mem x).2 ⟨k, hk, hx⟩
  rw [hc] at hkT
  have htT : t ∈ tn.T := hkT t (by simp)
  have hlmT : ∀ x ∈ lm, x ∉ tn.T := fun x hx hT =>
    Finset.disjoint_left.1 hdisj hT ((hu.memT x).2 hx)
  have ht_only : ∀ j (hj : j < cs.length), t ∈ cs[j].1 → j = k :=
    h.chain_of_mem hk (by rw [hc]; simp)
  have hlab := h.lab k hk
  rw [hc] at hlab
  simp only [List.map_append, List.map_cons] at hlab
  obtain ⟨hl1, hl2⟩ := List.append_inj hlab (by simpa using hlen)
  have hl2' := List.cons.inj hl2
  refine ⟨fun x => ?_, fun x z => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · -- membership
    rw [mem_decomposeWith_T, h.mem, hu.memT]
    simp only [List.length_set, List.getElem_set]
    constructor
    · rintro (⟨⟨j, hj, hx⟩, hxt⟩ | hx)
      · refine ⟨j, hj, ?_⟩
        split_ifs with hjk
        · subst hjk; rw [hc] at hx
          simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto
        · exact hx
      · exact ⟨k, hk, by simp [hx]⟩
    · rintro ⟨j, hj, hx⟩
      split_ifs at hx with hjk
      · subst hjk
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · refine Or.inl ⟨⟨k, hk, by rw [hc]; simp [hx]⟩, fun e => ?_⟩
          subst e; exact (List.nodup_append.1 hnd).2.2 _ hx _ (by simp) rfl
        · exact Or.inr hx
        · refine Or.inl ⟨⟨k, hk, by rw [hc]; simp [hx]⟩, fun e => ?_⟩
          subst e; exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 hx
      · refine Or.inl ⟨⟨j, by simpa using hj, hx⟩, fun e => ?_⟩
        subst e; exact hjk (ht_only j (by simpa using hj) hx).symm
  · -- order
    simp only [decomposeWith, List.length_set, List.getElem_set]
    rw [h.ord, h.ord, h.ord, hu.ord]
    have hT : ∀ w, w ∈ u.T ↔ w ∈ lm := hu.memT
    rw [hT, hT]
    -- the order of the chain `k` around `t`
    have hLk : ∀ w, (∃ j, ∃ hj : j < cs.length, Before cs[j].1 w t) ↔ w ∈ l₁ := by
      intro w
      constructor
      · rintro ⟨j, hj, hb⟩
        obtain rfl := ht_only j hj (before_mem hb).2
        rw [hc] at hb; exact (before_mid_left hnd).1 hb
      · intro hw; exact ⟨k, hk, by rw [hc]; exact (before_mid_left hnd).2 hw⟩
    have hRk : ∀ w, (∃ j, ∃ hj : j < cs.length, Before cs[j].1 t w) ↔ w ∈ l₂ := by
      intro w
      constructor
      · rintro ⟨j, hj, hb⟩
        obtain rfl := ht_only j hj (before_mem hb).1
        rw [hc] at hb; exact (before_mid_right hnd).1 hb
      · intro hw; exact ⟨k, hk, by rw [hc]; exact (before_mid_right hnd).2 hw⟩
    rw [hLk, hRk]
    have hidx : (x ∈ lm ∧ z ∈ lm ∧ lm.idxOf x < lm.idxOf z) ↔ Before lm x z :=
      (before_nodup_iff hu.nodup).symm
    rw [hidx]
    constructor
    · rintro (hb | ⟨hx, hz⟩ | ⟨hz, hx⟩ | ⟨⟨j, hj, hb⟩, hxt, hzt⟩)
      · exact ⟨k, hk, by simp only [if_pos rfl]; exact before_three.2 (Or.inr (Or.inl hb))⟩
      · exact ⟨k, hk, by simp only [if_pos rfl]; exact before_three.2 (Or.inr (Or.inr (Or.inl ⟨hx, hz⟩)))⟩
      · exact ⟨k, hk, by simp only [if_pos rfl]; exact before_three.2 (Or.inr (Or.inr (Or.inr ⟨hx, hz⟩)))⟩
      · refine ⟨j, hj, ?_⟩
        split_ifs with hjk
        · subst hjk; rw [hc, before_mid_ne hxt hzt] at hb
          exact before_three.2 (Or.inl hb)
        · exact hb
    · rintro ⟨j, hj, hb⟩
      split_ifs at hb with hjk
      · subst hjk
        rcases before_three.1 hb with hb | hb | ⟨hx, hz⟩ | ⟨hx, hz⟩
        · have hm := before_mem hb
          have hx : x ≠ t := fun e => by
            subst e; simp only [List.mem_append] at hm
            rcases hm.1 with h1 | h1
            · exact (List.nodup_append.1 hnd).2.2 _ h1 _ (by simp) rfl
            · exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 h1
          have hz : z ≠ t := fun e => by
            subst e; simp only [List.mem_append] at hm
            rcases hm.2 with h1 | h1
            · exact (List.nodup_append.1 hnd).2.2 _ h1 _ (by simp) rfl
            · exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 h1
          exact Or.inr (Or.inr (Or.inr ⟨⟨k, hk, by rw [hc, before_mid_ne hx hz]; exact hb⟩, hx, hz⟩))
        · exact Or.inl hb
        · exact Or.inr (Or.inl ⟨hx, hz⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hz, hx⟩))
      · have hm := before_mem hb
        have hx : x ≠ t := fun e => hjk (ht_only j hj (e ▸ hm.1)).symm
        have hz : z ≠ t := fun e => hjk (ht_only j hj (e ▸ hm.2)).symm
        exact Or.inr (Or.inr (Or.inr ⟨⟨j, hj, hb⟩, hx, hz⟩))
  · -- labels
    simp only [List.getElem_set]
    split_ifs with hjk
    · subst hjk
      simp only [List.map_append, decomposeWith]
      have e1 : l₁.map (fun x => if x ∈ u.T then u.α x else tn.α x) = xs₁ := by
        rw [← hl1]; refine List.map_congr_left fun x hx => ?_
        rw [if_neg fun h => hlmT x ((hu.memT x).1 h) (hkT x (by simp [hx]))]
      have e2 : l₂.map (fun x => if x ∈ u.T then u.α x else tn.α x) = xs₂ := by
        rw [← hl2'.2]; refine List.map_congr_left fun x hx => ?_
        rw [if_neg fun h => hlmT x ((hu.memT x).1 h) (hkT x (by simp [hx]))]
      have e3 : lm.map (fun x => if x ∈ u.T then u.α x else tn.α x) = bs := by
        rw [← hu.labels]; refine List.map_congr_left fun x hx => ?_
        rw [if_pos ((hu.memT x).2 hx)]
      rw [e1, e2, e3]
    · have hj' : j < cs.length := by simpa using hj
      rw [← h.lab j hj']
      simp only [decomposeWith]
      refine List.map_congr_left fun x hx => ?_
      rw [if_neg fun h' => hlmT x ((hu.memT x).1 h') ((h.mem x).2 ⟨j, hj', hx⟩)]
  · -- distinct ids
    simp only [List.getElem_set]
    split_ifs with hjk
    · subst hjk
      rw [List.nodup_append, List.nodup_append]
      have := List.nodup_append.1 hnd
      refine ⟨⟨this.1, hu.nodup, fun a ha b hb => fun e => ?_⟩, (List.nodup_cons.1 this.2.1).2,
        fun a ha b hb => ?_⟩
      · subst e; exact hlmT a hb (hkT a (by simp [ha]))
      · simp only [List.mem_append] at ha
        rcases ha with ha | ha
        · exact fun e => this.2.2 a ha b (by simp [hb]) e
        · exact fun e => by subst e; exact hlmT a ha (hkT a (by simp [hb]))
    · exact h.nodup j (by simpa using hj)
  · -- disjointness
    simp only [List.length_set] at hi hj
    simp only [List.getElem_set] at hx ⊢
    have hfresh : ∀ w ∈ lm, ∀ j' (hj' : j' < cs.length), w ∉ cs[j'].1 :=
      fun w hw j' hj' hwj => hlmT w hw ((h.mem w).2 ⟨j', hj', hwj⟩)
    by_cases h1 : k = i
    · subst h1
      rw [if_pos rfl] at hx
      rw [if_neg hij]
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact h.disj k j hk hj hij x (by rw [hc]; simp [hx])
      · exact hfresh x hx j hj
      · exact h.disj k j hk hj hij x (by rw [hc]; simp [hx])
    · rw [if_neg h1] at hx
      by_cases h2 : k = j
      · subst h2
        rw [if_pos rfl]
        simp only [List.mem_append, not_or]
        have := h.disj i k hi hk hij x hx
        rw [hc] at this
        simp only [List.mem_append, List.mem_cons, not_or] at this
        exact ⟨⟨this.1, fun hm => hfresh x hm i hi hx⟩, this.2.2⟩
      · rw [if_neg h2]
        exact h.disj i j hi hj hij x hx

end UC

theorem exists_idx_append {α : Type} {l₁ l₂ : List α} {P : α → Prop} :
    (∃ j, ∃ hj : j < (l₁ ++ l₂).length, P (l₁ ++ l₂)[j]) ↔
      (∃ j, ∃ hj : j < l₁.length, P l₁[j]) ∨ (∃ j, ∃ hj : j < l₂.length, P l₂[j]) := by
  constructor
  · rintro ⟨j, hj, hP⟩
    rw [List.getElem_append] at hP
    split_ifs at hP with h
    · exact Or.inl ⟨j, h, hP⟩
    · exact Or.inr ⟨j - l₁.length, by simp at hj; omega, hP⟩
  · rintro (⟨j, hj, hP⟩ | ⟨j, hj, hP⟩)
    · exact ⟨j, by simp; omega, by rw [List.getElem_append_left hj]; exact hP⟩
    · exact ⟨l₁.length + j, by simp; omega, by
        rw [List.getElem_append_right (by omega)]; simpa using hP⟩

/-- The singleton chains of a set network. -/
def singles (lm : List I) (bs : List (A ⊕ C)) : List (Ch I A C) := (lm.zip bs).map fun p => ([p.1], [p.2])

theorem singles_get {lm : List I} {bs : List (A ⊕ C)} (hl : lm.length = bs.length) {j : ℕ}
    (hj : j < (singles lm bs).length) :
    (singles lm bs)[j] = ([lm[j]'(by simp [singles] at hj; omega)], [bs[j]'(by simp [singles] at hj; omega)]) := by
  simp [singles]

namespace UC

variable {tn : TaskNetwork I A C} {cs : List (Ch I A C)}

/-- **A task forming its own chain decomposed by a set network.** -/
theorem step_set (h : UC tn cs) {k : ℕ} (hk : k < cs.length) {t : I} {y : A ⊕ C}
    (hc : cs[k] = ([t], [y])) {u : TaskNetwork I A C} {lm : List I} {bs : List (A ⊕ C)}
    (hu : SetNet u lm bs) (hdisj : Disjoint tn.T u.T) :
    UC (decomposeWith tn t u) (cs.set k ([], []) ++ singles lm bs) := by
  have hlm : lm.length = bs.length := by rw [← hu.labels, List.length_map]
  have hlmT : ∀ x ∈ lm, x ∉ tn.T := fun x hx hT =>
    Finset.disjoint_left.1 hdisj hT ((hu.memT x).2 hx)
  have ht_only : ∀ j (hj : j < cs.length), t ∈ cs[j].1 → j = k :=
    h.chain_of_mem hk (by rw [hc]; simp)
  have hnotk : ∀ j (hj : j < cs.length) x, x ∈ cs[j].1 → x ≠ t → j ≠ k := by
    intro j hj x hx hxt e; subst e; rw [hc] at hx; simp at hx; exact hxt hx
  have hsl : (singles lm bs).length = lm.length := by simp [singles, hlm]
  refine ⟨fun x => ?_, fun x z => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · rw [mem_decomposeWith_T, h.mem, hu.memT, exists_idx_append (P := fun c : Ch I A C => x ∈ c.1)]
    simp only [List.length_set, List.getElem_set]
    constructor
    · rintro (⟨⟨j, hj, hx⟩, hxt⟩ | hx)
      · exact Or.inl ⟨j, hj, by rw [if_neg (Ne.symm (hnotk j hj x hx hxt))]; exact hx⟩
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        exact Or.inr ⟨j, by omega, by rw [singles_get hlm]; simp⟩
    · rintro (⟨j, hj, hx⟩ | ⟨j, hj, hx⟩)
      · split_ifs at hx with hjk
        · simp at hx
        · refine Or.inl ⟨⟨j, hj, hx⟩, fun e => ?_⟩
          subst e; exact hjk (ht_only j hj hx).symm
      · rw [singles_get hlm] at hx
        simp only [List.mem_singleton] at hx
        subst hx; exact Or.inr (List.getElem_mem _)
  · simp only [decomposeWith]
    rw [exists_idx_append (P := fun c : Ch I A C => Before c.1 x z), h.ord, h.ord, h.ord]
    have hnt : ∀ w, ¬ ∃ j, ∃ hj : j < cs.length, Before cs[j].1 w t := by
      rintro w ⟨j, hj, hb⟩
      obtain rfl := ht_only j hj (before_mem hb).2
      rw [hc] at hb; exact PCP.not_before_singleton hb
    have hnt' : ∀ w, ¬ ∃ j, ∃ hj : j < cs.length, Before cs[j].1 t w := by
      rintro w ⟨j, hj, hb⟩
      obtain rfl := ht_only j hj (before_mem hb).1
      rw [hc] at hb; exact PCP.not_before_singleton hb
    simp only [List.length_set, List.getElem_set]
    constructor
    · rintro (hb | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨⟨j, hj, hb⟩, -, -⟩)
      · exact absurd hb (hu.ord x z)
      · exact absurd hb (hnt x)
      · exact absurd hb (hnt' z)
      · refine Or.inl ⟨j, hj, ?_⟩
        rw [if_neg]; exact hb
        intro e; subst e; rw [hc] at hb; exact PCP.not_before_singleton hb
    · rintro (⟨j, hj, hb⟩ | ⟨j, hj, hb⟩)
      · split_ifs at hb with hjk
        · exact absurd hb before_nil
        · have hm := before_mem hb
          refine Or.inr (Or.inr (Or.inr ⟨⟨j, hj, hb⟩, fun e => ?_, fun e => ?_⟩))
          · subst e; exact hjk (ht_only j hj hm.1).symm
          · subst e; exact hjk (ht_only j hj hm.2).symm
      · rw [singles_get hlm] at hb; exact absurd hb PCP.not_before_singleton
  · have hn : (cs.set k ([], [])).length = cs.length := List.length_set ..
    have hj2 : j < cs.length + lm.length := by simp only [List.length_append, hn, hsl] at hj; omega
    rcases Nat.lt_or_ge j cs.length with hj' | hj'
    · rw [List.getElem_append_left (by rw [hn]; exact hj')]
      simp only [List.getElem_set]
      split_ifs with hjk
      · rfl
      · rw [← h.lab j hj']
        simp only [decomposeWith]
        refine List.map_congr_left fun x hx => ?_
        rw [if_neg fun h' => hlmT x ((hu.memT x).1 h') ((h.mem x).2 ⟨j, hj', hx⟩)]
    · rw [List.getElem_append_right (by rw [hn]; exact hj'), singles_get hlm]
      simp only [List.map_cons, List.map_nil, decomposeWith, hn]
      rw [if_pos ((hu.memT _).2 (List.getElem_mem _))]
      have := congrArg (fun l => l[j - cs.length]?) hu.labels
      simp only [List.getElem?_map] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      simpa using this
  · have hn : (cs.set k ([], [])).length = cs.length := List.length_set ..
    rcases Nat.lt_or_ge j cs.length with hj' | hj'
    · rw [List.getElem_append_left (by rw [hn]; exact hj')]
      simp only [List.getElem_set]
      split_ifs
      · exact List.nodup_nil
      · exact h.nodup j hj'
    · rw [List.getElem_append_right (by rw [hn]; exact hj'), singles_get hlm]
      exact List.nodup_singleton _
  · have hn : (cs.set k ([], [])).length = cs.length := List.length_set ..
    have hi2 : i < cs.length + lm.length := by simp only [List.length_append, hn, hsl] at hi; omega
    have hj2 : j < cs.length + lm.length := by simp only [List.length_append, hn, hsl] at hj; omega
    have hinT : ∀ j' (hj' : j' < cs.length) w, w ∈ ((cs.set k ([], []))[j']'(by rw [hn]; exact hj')).1 →
        w ∈ tn.T := by
      intro j' hj' w hw
      simp only [List.getElem_set] at hw
      split_ifs at hw
      · simp at hw
      · exact (h.mem w).2 ⟨j', hj', hw⟩
    rcases Nat.lt_or_ge i cs.length with hi' | hi' <;> rcases Nat.lt_or_ge j cs.length with hj' | hj'
    · rw [List.getElem_append_left (by rw [hn]; exact hi')] at hx
      rw [List.getElem_append_left (by rw [hn]; exact hj')]
      simp only [List.getElem_set] at hx ⊢
      by_cases h3 : k = i
      · rw [if_pos h3] at hx; simp at hx
      · rw [if_neg h3] at hx
        by_cases h4 : k = j
        · rw [if_pos h4]; simp
        · rw [if_neg h4]; exact h.disj i j hi' hj' hij x hx
    · rw [List.getElem_append_left (by rw [hn]; exact hi')] at hx
      rw [List.getElem_append_right (by rw [hn]; exact hj'), singles_get hlm]
      simp only [List.mem_singleton]
      intro e; subst e
      exact hlmT _ (List.getElem_mem _) (hinT i hi' _ hx)
    · rw [List.getElem_append_right (by rw [hn]; exact hi'), singles_get hlm] at hx
      rw [List.getElem_append_left (by rw [hn]; exact hj')]
      simp only [List.mem_singleton] at hx
      subst hx
      exact fun hm => hlmT _ (List.getElem_mem _) (hinT j hj' _ hm)
    · rw [List.getElem_append_right (by rw [hn]; exact hi'), singles_get hlm] at hx
      rw [List.getElem_append_right (by rw [hn]; exact hj'), singles_get hlm]
      simp only [List.mem_singleton] at hx ⊢
      rw [hx]
      intro e
      have := (List.Nodup.getElem_inj_iff hu.nodup).1 e
      simp only [hn] at this
      omega

end UC

/-- **Set networks are invariant under renaming of the task identifiers.** -/
theorem SetNet.iso {tn tn' : TaskNetwork I A C} {l : List I} {xs : List (A ⊕ C)}
    (h : SetNet tn l xs) (hwf' : tn'.WF) (hiso : tn.Iso tn') : ∃ l₂ : List I, SetNet tn' l₂ xs := by
  classical
  obtain ⟨σ, hbij, hord, hα⟩ := hiso
  have hinj : ∀ x ∈ l, ∀ y ∈ l, σ x = σ y → x = y := by
    intro x hx y hy hxy
    exact hbij.injOn (by simpa using (h.memT x).2 hx) (by simpa using (h.memT y).2 hy) hxy
  refine ⟨l.map σ, List.Nodup.map_on hinj h.nodup, fun y => ?_, ?_, fun x y hxy => ?_⟩
  · constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hbij.surjOn (by simpa using hy)
      exact List.mem_map.2 ⟨z, (h.memT z).1 (by simpa using hz), rfl⟩
    · rintro hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      simpa using hbij.mapsTo (by simpa using (h.memT z).2 hz)
  · rw [List.map_map, ← h.labels]
    refine List.map_congr_left fun y hy => ?_
    exact (hα y ((h.memT y).2 hy)).symm
  · obtain ⟨a, ha, rfl⟩ := hbij.surjOn (by simpa using hwf'.mem_left hxy)
    obtain ⟨b, hb, rfl⟩ := hbij.surjOn (by simpa using hwf'.mem_right hxy)
    exact h.ord a b ((hord a (by simpa using ha) b (by simpa using hb)).2 hxy)

end AcycHard

end FOND
