import FondHtn.AcycHard.ChainGame
import FondHtn.FixedMethods
/-!
# Networks of chains: belief solvability is the chain game

A primitive task network that is a **disjoint union of chains** — a control chain `ctl` and a
multiset `pool` of further chains (lists of task ids), the ordering being "earlier in the same
chain" — is strongly solvable (`FOND.Problem.BeliefSolvable`, [DB25]; equivalent to strong OD
solvability, `FOND.Problem.strongOD_iff_beliefSolvable`) iff the chain game
`FOND.AcycHard.CWin` on the label lists is won.

* `FOND.AcycHard.IsChains tn ctl pool ℓ` — `tn` is the union of the chains, `ℓ` its labelling;
* **`FOND.AcycHard.beliefSolvable_iff_cwin`**.
-/

namespace FOND

namespace AcycHard

open HTN

set_option linter.unusedSectionVars false

variable {F A C I : Type} [DecidableEq I] [DecidableEq A]

/-- `a` occurs before `b` in the list `l`. -/
def Before (l : List I) (a b : I) : Prop := ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ b ∈ l₂

lemma before_nil {a b : I} : ¬ Before [] a b := by
  rintro ⟨l₁, l₂, h, -⟩
  cases l₁ <;> simp at h

lemma before_cons {x a b : I} {l : List I} :
    Before (x :: l) a b ↔ (a = x ∧ b ∈ l) ∨ Before l a b := by
  constructor
  · rintro ⟨l₁, l₂, h, hb⟩
    cases l₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, hb⟩
    | cons y l₁ =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact Or.inr ⟨l₁, l₂, h.2, hb⟩
  · rintro (⟨rfl, hb⟩ | ⟨l₁, l₂, rfl, hb⟩)
    · exact ⟨[], l, rfl, hb⟩
    · exact ⟨x :: l₁, l₂, rfl, hb⟩

lemma before_mem {l : List I} {a b : I} (h : Before l a b) : a ∈ l ∧ b ∈ l := by
  obtain ⟨l₁, l₂, rfl, hb⟩ := h
  simp [hb]

/-- `tn` is the disjoint union of the chain `ctl` and the chains of `pool`, all its tasks
primitive with labels `ℓ`. -/
structure IsChains (tn : TaskNetwork I A C) (ctl : List I) (pool : Multiset (List I))
    (ℓ : I → A) : Prop where
  mem : ∀ t, t ∈ tn.T ↔ t ∈ ctl ∨ ∃ c ∈ pool, t ∈ c
  ord : ∀ a b, tn.ord a b ↔ Before ctl a b ∨ ∃ c ∈ pool, Before c a b
  lab : ∀ t ∈ tn.T, tn.α t = Sum.inl (ℓ t)
  nodup_ctl : ctl.Nodup
  nodup_pool : ∀ c ∈ pool, c.Nodup
  disj_ctl : ∀ c ∈ pool, ∀ t ∈ c, t ∉ ctl
  disj_pool : ∀ c ∈ pool, ∀ t ∈ c, ∀ c' ∈ pool.erase c, t ∉ c'

namespace IsChains

variable {tn : TaskNetwork I A C} {ctl : List I} {pool : Multiset (List I)} {ℓ : I → A}

/-- An unconstrained task is the head of a chain. -/
lemma head_of_unconstrained (h : IsChains tn ctl pool ℓ) {t : I} (hu : tn.Unconstrained t) :
    (∃ ctl', ctl = t :: ctl') ∨ ∃ c', t :: c' ∈ pool := by
  have key : ∀ l : List I, t ∈ l → (∀ x ∈ l, x ∈ tn.T) → (∀ x, Before l x t → tn.ord x t) →
      ∃ l', l = t :: l' := by
    intro l hl hT hord
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hl
    cases l₁ with
    | nil => exact ⟨l₂, rfl⟩
    | cons x l₁ =>
      exfalso
      refine hu.2 x (hT x (by simp)) (hord x ?_)
      exact ⟨[], l₁ ++ t :: l₂, rfl, by simp⟩
  rcases (h.mem t).1 hu.1 with ht | ⟨c, hc, ht⟩
  · exact Or.inl (key ctl ht (fun x hx => (h.mem x).2 (Or.inl hx))
      (fun x hx => (h.ord x t).2 (Or.inl hx)))
  · obtain ⟨c', rfl⟩ := key c ht (fun x hx => (h.mem x).2 (Or.inr ⟨c, hc, hx⟩))
      (fun x hx => (h.ord x t).2 (Or.inr ⟨c, hc, hx⟩))
    exact Or.inr ⟨c', hc⟩

lemma unconstrained_ctl (h : IsChains tn ctl pool ℓ) {t : I} {ctl' : List I}
    (hc : ctl = t :: ctl') : tn.Unconstrained t := by
  subst hc
  refine ⟨(h.mem t).2 (Or.inl (by simp)), fun x _ hx => ?_⟩
  rcases (h.ord x t).1 hx with hb | ⟨c, hc, hb⟩
  · rcases before_cons.1 hb with ⟨rfl, ht⟩ | hb
    · exact (List.nodup_cons.1 h.nodup_ctl).1 ht
    · exact (List.nodup_cons.1 h.nodup_ctl).1 (before_mem hb).2
  · exact h.disj_ctl c hc t (before_mem hb).2 (by simp)

lemma unconstrained_pool (h : IsChains tn ctl pool ℓ) {t : I} {c' : List I}
    (hc : t :: c' ∈ pool) : tn.Unconstrained t := by
  refine ⟨(h.mem t).2 (Or.inr ⟨_, hc, by simp⟩), fun x _ hx => ?_⟩
  rcases (h.ord x t).1 hx with hb | ⟨d, hd, hb⟩
  · exact h.disj_ctl _ hc t (by simp) (before_mem hb).2
  · by_cases hdc : d = t :: c'
    · subst hdc
      rcases before_cons.1 hb with ⟨rfl, ht⟩ | hb
      · exact (List.nodup_cons.1 (h.nodup_pool _ hc)).1 ht
      · exact (List.nodup_cons.1 (h.nodup_pool _ hc)).1 (before_mem hb).2
    · exact h.disj_pool _ hc t (by simp) d (Multiset.mem_erase_of_ne hdc |>.2 hd)
        (before_mem hb).2

lemma progress_ctl (h : IsChains tn ctl pool ℓ) {t : I} {ctl' : List I} (hc : ctl = t :: ctl') :
    IsChains (tn.progress t) ctl' pool ℓ := by
  subst hc
  have hnd := List.nodup_cons.1 h.nodup_ctl
  have hne : ∀ c ∈ pool, ∀ x ∈ c, x ≠ t := by
    rintro c hc x hx rfl
    exact h.disj_ctl c hc x hx (by simp)
  refine ⟨fun x => ?_, fun a b => ?_, fun x hx => h.lab x (Finset.mem_of_mem_erase hx),
    hnd.2, h.nodup_pool, fun c hc x hx hx' => h.disj_ctl c hc x hx (by simp [hx']),
    h.disj_pool⟩
  · rw [TaskNetwork.mem_progress_T, h.mem]
    constructor
    · rintro ⟨hxt, hx | hx⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd rfl hxt
        · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | ⟨c, hc, hx⟩)
      · exact ⟨fun hxt => hnd.1 (hxt ▸ hx), Or.inl (by simp [hx])⟩
      · exact ⟨hne c hc x hx, Or.inr ⟨c, hc, hx⟩⟩
  · rw [TaskNetwork.progress_ord, h.ord, before_cons]
    constructor
    · rintro ⟨(⟨rfl, -⟩ | hb) | hb, hat⟩
      · exact absurd rfl hat
      · exact Or.inl hb
      · exact Or.inr hb
    · rintro (hb | ⟨c, hc, hb⟩)
      · exact ⟨Or.inl (Or.inr hb), fun hat => hnd.1 (hat ▸ (before_mem hb).1)⟩
      · exact ⟨Or.inr ⟨c, hc, hb⟩, hne c hc a (before_mem hb).1⟩

lemma progress_pool (h : IsChains tn ctl pool ℓ) {t : I} {c' : List I} (hc : t :: c' ∈ pool) :
    IsChains (tn.progress t) ctl (c' ::ₘ pool.erase (t :: c')) ℓ := by
  have hnd := List.nodup_cons.1 (h.nodup_pool _ hc)
  have hctl : t ∉ ctl := h.disj_ctl _ hc t (by simp)
  have hrest : ∀ d ∈ pool.erase (t :: c'), t ∉ d := h.disj_pool _ hc t (by simp)
  have hpool : pool = (t :: c') ::ₘ pool.erase (t :: c') := (Multiset.cons_erase hc).symm
  -- membership in the new pool
  have hmem' : ∀ d, d ∈ c' ::ₘ pool.erase (t :: c') → t ∉ d ∧ ∃ e ∈ pool, ∀ x ∈ d, x ∈ e := by
    intro d hd
    rcases Multiset.mem_cons.1 hd with rfl | hd
    · exact ⟨hnd.1, _, hc, fun x hx => by simp [hx]⟩
    · exact ⟨hrest d hd, d, Multiset.mem_of_mem_erase hd, fun x hx => hx⟩
  refine ⟨fun x => ?_, fun a b => ?_, fun x hx => h.lab x (Finset.mem_of_mem_erase hx),
    h.nodup_ctl, ?_, ?_, ?_⟩
  · rw [TaskNetwork.mem_progress_T, h.mem]
    constructor
    · rintro ⟨hxt, hx | ⟨d, hd, hx⟩⟩
      · exact Or.inl hx
      · by_cases hdc : d = t :: c'
        · subst hdc
          rcases List.mem_cons.1 hx with rfl | hx
          · exact absurd rfl hxt
          · exact Or.inr ⟨c', Multiset.mem_cons_self _ _, hx⟩
        · exact Or.inr ⟨d, Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne hdc).2 hd), hx⟩
    · rintro (hx | ⟨d, hd, hx⟩)
      · exact ⟨fun hxt => hctl (hxt ▸ hx), Or.inl hx⟩
      · obtain ⟨htd, e, he, hde⟩ := hmem' d hd
        exact ⟨fun hxt => htd (hxt ▸ hx), Or.inr ⟨e, he, hde x hx⟩⟩
  · rw [TaskNetwork.progress_ord, h.ord]
    constructor
    · rintro ⟨hb | ⟨d, hd, hb⟩, hat⟩
      · exact Or.inl hb
      · by_cases hdc : d = t :: c'
        · subst hdc
          rcases before_cons.1 hb with ⟨rfl, -⟩ | hb
          · exact absurd rfl hat
          · exact Or.inr ⟨c', Multiset.mem_cons_self _ _, hb⟩
        · exact Or.inr ⟨d, Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne hdc).2 hd), hb⟩
    · rintro (hb | ⟨d, hd, hb⟩)
      · exact ⟨Or.inl hb, fun hat => hctl (hat ▸ (before_mem hb).1)⟩
      · obtain ⟨htd, e, he, -⟩ := hmem' d hd
        refine ⟨?_, fun hat => htd (hat ▸ (before_mem hb).1)⟩
        rcases Multiset.mem_cons.1 hd with rfl | hd
        · exact Or.inr ⟨t :: d, hc, before_cons.2 (Or.inr hb)⟩
        · exact Or.inr ⟨d, Multiset.mem_of_mem_erase hd, hb⟩
  · intro d hd
    rcases Multiset.mem_cons.1 hd with rfl | hd
    · exact hnd.2
    · exact h.nodup_pool d (Multiset.mem_of_mem_erase hd)
  · intro d hd x hx
    obtain ⟨-, e, he, hde⟩ := hmem' d hd
    exact h.disj_ctl e he x (hde x hx)
  · intro d hd x hx d' hd'
    -- `d` and `d'` are different members of the new pool
    rcases Multiset.mem_cons.1 hd with rfl | hd
    · rw [Multiset.erase_cons_head] at hd'
      exact h.disj_pool _ hc x (by simp [hx]) d' hd'
    · by_cases hdd : d = d
      · have hd'' : d' ∈ c' ::ₘ (pool.erase (t :: c')).erase d := by
          rwa [Multiset.erase_cons_tail_of_mem hd] at hd'
        rcases Multiset.mem_cons.1 hd'' with rfl | hd''
        · intro hx'
          exact h.disj_pool _ hc x (by simp [hx']) d hd hx
        · have hdp : d ∈ pool := Multiset.mem_of_mem_erase hd
          refine h.disj_pool d hdp x hx d' ?_
          -- `d' ∈ (pool.erase (t :: c')).erase d ≤ pool.erase d`
          have : (pool.erase (t :: c')).erase d = (pool.erase d).erase (t :: c') :=
            Multiset.erase_comm _ _ _
          rw [this] at hd''
          exact Multiset.mem_of_mem_erase hd''
      · exact absurd rfl hdd

lemma empty (h : IsChains tn [] pool ℓ) (hp : ∀ c ∈ pool, c = []) : tn.T = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases (h.mem x).1 hx with hx | ⟨c, hc, hx⟩
  · simp at hx
  · rw [hp c hc] at hx; simp at hx

lemma pool_nil_of_empty (h : IsChains tn ctl pool ℓ) (hT : tn.T = ∅) :
    ctl = [] ∧ ∀ c ∈ pool, c = [] := by
  refine ⟨List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_, fun c hc => ?_⟩
  · have := (h.mem x).2 (Or.inl hx)
    simp [hT] at this
  · refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
    have := (h.mem x).2 (Or.inr ⟨c, hc, hx⟩)
    simp [hT] at this

end IsChains

lemma map_erase_of_mem {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    {s : Multiset α} {x : α} (hx : x ∈ s) : (s.erase x).map f = (s.map f).erase (f x) := by
  conv_rhs => rw [← Multiset.cons_erase hx]
  rw [Multiset.map_cons, Multiset.erase_cons_head]

variable (P : Problem F A C I)

/-- **Belief solvability of a network of chains is the chain game.** -/
theorem beliefSolvable_of_isChains {tn : TaskNetwork I A C} {s : Set F}
    (hb : P.BeliefSolvable tn s) : ∀ {ctl : List I} {pool : Multiset (List I)} {ℓ : I → A},
    IsChains tn ctl pool ℓ → CWin P.δ P.δ (ctl.map ℓ) (pool.map (List.map ℓ)) s := by
  induction hb with
  | empty hT =>
    intro ctl pool ℓ h
    obtain ⟨rfl, hp⟩ := h.pool_nil_of_empty hT
    refine CWin.done fun c hc => ?_
    obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.1 hc
    simp [hp c' hc']
  | @step tn s t a hu hα happ _ ih =>
    intro ctl pool ℓ h
    have hℓ : ℓ t = a := by
      have := h.lab t hu.1
      rw [hα] at this
      exact (Sum.inl.inj this).symm
    rcases h.head_of_unconstrained hu with ⟨ctl', rfl⟩ | ⟨c', hc⟩
    · refine CWin.ctl (by rw [hℓ]; exact happ) ?_
      intro s' hs'
      exact ih s' (by rwa [hℓ] at hs') (h.progress_ctl rfl)
    · have hc' : ℓ t :: c'.map ℓ ∈ pool.map (List.map ℓ) :=
        Multiset.mem_map.2 ⟨t :: c', hc, rfl⟩
      refine CWin.pool hc' (by rw [hℓ]; exact happ) ?_
      intro s' hs'
      have := ih s' (by rwa [hℓ] at hs') (h.progress_pool hc)
      rw [Multiset.map_cons, map_erase_of_mem _ hc] at this
      simpa using this

theorem isChains_of_cwin {ctlL : List A} {M : Multiset (List A)} {s : Set F}
    (hw : CWin P.δ P.δ ctlL M s) : ∀ {tn : TaskNetwork I A C} {ctl : List I}
    {pool : Multiset (List I)} {ℓ : I → A}, IsChains tn ctl pool ℓ → ctlL = ctl.map ℓ →
    M = pool.map (List.map ℓ) → P.BeliefSolvable tn s := by
  induction hw with
  | @done M s hM =>
    intro tn ctl pool ℓ h hctl hpool
    have hctl' : ctl = [] := List.map_eq_nil_iff.1 hctl.symm
    subst hctl'
    refine Problem.BeliefSolvable.empty (h.empty fun c hc => ?_)
    have := hM _ (hpool ▸ Multiset.mem_map_of_mem _ hc)
    exact List.map_eq_nil_iff.1 this
  | @ctl a ctlL M s happ _ ih =>
    intro tn ctl pool ℓ h hctl hpool
    obtain ⟨t, ctl', rfl, hta, rfl⟩ := List.map_eq_cons_iff.1 hctl.symm
    have hu := h.unconstrained_ctl rfl
    refine Problem.BeliefSolvable.step hu (by rw [h.lab t hu.1, hta]) happ ?_
    intro s' hs'
    exact ih s' hs' (h.progress_ctl rfl) rfl hpool
  | @pool ctlL M s a c hc happ _ ih =>
    intro tn ctl pool ℓ h hctl hpool
    subst hpool
    obtain ⟨d, hd, hde⟩ := Multiset.mem_map.1 hc
    obtain ⟨t, d', rfl, hta, rfl⟩ := List.map_eq_cons_iff.1 hde
    have hu := h.unconstrained_pool hd
    refine Problem.BeliefSolvable.step hu (by rw [h.lab t hu.1, hta]) happ ?_
    intro s' hs'
    refine ih s' hs' (h.progress_pool hd) hctl ?_
    rw [Multiset.map_cons, map_erase_of_mem _ hd]
    simp [hta]

/-- **Belief solvability of a network of chains is the chain game.** -/
theorem beliefSolvable_iff_cwin {tn : TaskNetwork I A C} {ctl : List I}
    {pool : Multiset (List I)} {ℓ : I → A} (h : IsChains tn ctl pool ℓ) (s : Set F) :
    P.BeliefSolvable tn s ↔ CWin P.δ P.δ (ctl.map ℓ) (pool.map (List.map ℓ)) s :=
  ⟨fun hb => beliefSolvable_of_isChains P hb h, fun hw => isChains_of_cwin P hw h rfl rfl⟩

/-! ## One label type for control and pool -/

section Relabel

variable {CA PA : Type} [DecidableEq CA] [DecidableEq PA]

lemma cwin_sum_of {δC : CA → Action F} {δP : PA → Action F} {ctl : List CA}
    {M : Multiset (List PA)} {s : Set F} (h : CWin δC δP ctl M s) :
    CWin (Sum.elim δC δP) (Sum.elim δC δP) (ctl.map Sum.inl) (M.map (List.map Sum.inr)) s := by
  induction h with
  | done hM =>
    refine CWin.done fun c hc => ?_
    obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.1 hc
    simp [hM c' hc']
  | ctl happ _ ih => exact CWin.ctl happ ih
  | @pool ctl M s a c hc happ _ ih =>
    refine CWin.pool (a := Sum.inr a) (c := c.map Sum.inr)
      (Multiset.mem_map.2 ⟨a :: c, hc, rfl⟩) happ fun s' hs' => ?_
    have := ih s' hs'
    rw [Multiset.map_cons, map_erase_of_mem _ hc] at this
    simpa using this

lemma cwin_of_sum {δC : CA → Action F} {δP : PA → Action F} {ctlL : List (CA ⊕ PA)}
    {ML : Multiset (List (CA ⊕ PA))} {s : Set F}
    (h : CWin (Sum.elim δC δP) (Sum.elim δC δP) ctlL ML s) :
    ∀ {ctl : List CA} {M : Multiset (List PA)}, ctlL = ctl.map Sum.inl →
      ML = M.map (List.map Sum.inr) → CWin δC δP ctl M s := by
  induction h with
  | @done ML s hM =>
    intro ctl M hctl hM'
    have : ctl = [] := List.map_eq_nil_iff.1 hctl.symm
    subst this
    refine CWin.done fun c hc => ?_
    exact List.map_eq_nil_iff.1 (hM _ (hM' ▸ Multiset.mem_map_of_mem _ hc))
  | @ctl a ctlL ML s happ _ ih =>
    intro ctl M hctl hM'
    obtain ⟨b, ctl', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hctl.symm
    exact CWin.ctl happ fun s' hs' => ih s' hs' rfl hM'
  | @pool ctlL ML s a c hc happ _ ih =>
    intro ctl M hctl hM'
    subst hM'
    obtain ⟨d, hd, hde⟩ := Multiset.mem_map.1 hc
    obtain ⟨b, d', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hde
    refine CWin.pool hd happ fun s' hs' => ih s' hs' hctl ?_
    rw [Multiset.map_cons, map_erase_of_mem _ hd]
    rfl

/-- **Relabelling**: the chain game with separate control and pool labels is the chain game
over the sum of the label types. -/
theorem cwin_sum_iff (δC : CA → Action F) (δP : PA → Action F) (ctl : List CA)
    (M : Multiset (List PA)) (s : Set F) :
    CWin (Sum.elim δC δP) (Sum.elim δC δP) (ctl.map Sum.inl) (M.map (List.map Sum.inr)) s ↔
      CWin δC δP ctl M s :=
  ⟨fun h => cwin_of_sum h rfl rfl, cwin_sum_of⟩

end Relabel

end AcycHard

end FOND
