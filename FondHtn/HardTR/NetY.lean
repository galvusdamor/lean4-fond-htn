import HtnPlanning.Interleave.NetYield
import HtnPlanning.Article.AbsProgression
import FondHtn.AcycHard.Hier
/-!
# Refinements of sequence and set networks, label by label

For a domain whose methods have well-formed subtask networks:

* **`FOND.HardTR.seqY_of_netYieldN`** — a refinement of a sequence network with labels `xs` is a
  concatenation of refinements of the single labels;
* **`FOND.HardTR.setY_of_netYieldN`** — a refinement of a set network (no order) is an
  interleaving of refinements of the single labels.

A single label refines as an action into itself, and as a compound task through one of its
methods, with fewer decomposition steps (`FOND.HardTR.YL`).
-/

namespace FOND

namespace HardTR

open HTN

variable {F A C I : Type} [DecidableEq I] [Infinite I] (D : HTN.Domain F A C I)

/-- How a single label refines within `n` decomposition steps. -/
def YL (n : ℕ) (x : A ⊕ C) (u : List A) : Prop :=
  (∃ a, x = .inl a ∧ u = [a]) ∨
    ∃ c k m, x = .inr c ∧ k < n ∧ m ∈ D.methods ∧ m.abstractTask = c ∧ D.NetYieldN k m.subtasks u

theorem YL.mono {D : HTN.Domain F A C I} {n n' : ℕ} (h : n ≤ n') {x : A ⊕ C} {u : List A}
    (hy : YL D n x u) : YL D n' x u := by
  rcases hy with h1 | ⟨c, k, m, hx, hk, hm⟩
  · exact Or.inl h1
  · exact Or.inr ⟨c, k, m, hx, by omega, hm⟩

/-- Concatenations of refinements of the labels. -/
inductive SeqY (Y : A ⊕ C → List A → Prop) : List (A ⊕ C) → List A → Prop
  | nil : SeqY Y [] []
  | cons {x : A ⊕ C} {xs : List (A ⊕ C)} {u v : List A} : Y x u → SeqY Y xs v → SeqY Y (x :: xs) (u ++ v)

/-- Interleavings of refinements of the labels. -/
inductive SetY (Y : A ⊕ C → List A → Prop) : List (A ⊕ C) → List A → Prop
  | nil : SetY Y [] []
  | cons {x : A ⊕ C} {xs : List (A ⊕ C)} {u v w : List A} : Y x u → SetY Y xs v → Interleave u v w →
      SetY Y (x :: xs) w

theorem SeqY.mono {Y Y' : A ⊕ C → List A → Prop} (hY : ∀ x u, Y x u → Y' x u) :
    ∀ {xs : List (A ⊕ C)} {as : List A}, SeqY Y xs as → SeqY Y' xs as := by
  intro xs as h
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (hY _ _ h1) ih

theorem SetY.mono {Y Y' : A ⊕ C → List A → Prop} (hY : ∀ x u, Y x u → Y' x u) :
    ∀ {xs : List (A ⊕ C)} {as : List A}, SetY Y xs as → SetY Y' xs as := by
  intro xs as h
  induction h with
  | nil => exact .nil
  | cons h1 _ hi ih => exact .cons (hY _ _ h1) ih hi

variable {D}

/-- A single task refines according to its label. -/
theorem yl_of_single (hmwf : ∀ m ∈ D.methods, m.subtasks.WF) {n : ℕ} {tn : TaskNetwork I A C} {t : I}
    (hs : TaskNetwork.IsSingle tn t) {u : List A} (h : D.NetYieldN n tn u) : YL D n (tn.α t) u := by
  cases hα : tn.α t with
  | inl a =>
    obtain ⟨-, rfl⟩ := (Domain.netYieldN_single_prim hs hα).1 h
    exact Or.inl ⟨a, rfl, rfl⟩
  | inr c =>
    obtain ⟨k, m, rfl, hm, hmc, hy⟩ := (Domain.netYieldN_single_comp hs hα hmwf).1 h
    exact Or.inr ⟨c, k, m, rfl, by omega, hm, hmc, hy⟩

/-! ## Splitting off the first task -/

theorem isSingle_restrict {tn : TaskNetwork I A C} (hwf : tn.WF) {t : I} (ht : t ∈ tn.T) :
    TaskNetwork.IsSingle (tn.restrict (· = t)) t where
  memT x := by
    simp only [TaskNetwork.restrict, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨ht, rfl⟩
  ord a b h := by
    obtain ⟨hab, rfl, rfl⟩ := h
    exact hwf.irrefl _ hab

theorem isSeqNet_tail {tn : TaskNetwork I A C} {t : I} {l : List I} {x : A ⊕ C} {xs : List (A ⊕ C)}
    (h : tn.IsSeqNet (t :: l) (x :: xs)) : (tn.restrict (· ∈ l)).IsSeqNet l xs where
  nodup := (List.nodup_cons.1 h.nodup).2
  memT y := by
    simp only [TaskNetwork.restrict, Finset.mem_filter, h.memT, List.mem_cons]
    tauto
  labels := by
    have := h.labels
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2
  ord a b := by
    simp only [TaskNetwork.restrict, h.ord, List.mem_cons]
    have hnd := List.nodup_cons.1 h.nodup
    constructor
    · rintro ⟨⟨-, -, hlt⟩, ha, hb⟩
      have hat : a ≠ t := fun e => hnd.1 (e ▸ ha)
      have hbt : b ≠ t := fun e => hnd.1 (e ▸ hb)
      rw [List.idxOf_cons_ne _ (Ne.symm hat), List.idxOf_cons_ne _ (Ne.symm hbt)] at hlt
      exact ⟨ha, hb, by omega⟩
    · rintro ⟨ha, hb, hlt⟩
      have hat : a ≠ t := fun e => hnd.1 (e ▸ ha)
      have hbt : b ≠ t := fun e => hnd.1 (e ▸ hb)
      refine ⟨⟨Or.inr ha, Or.inr hb, ?_⟩, ha, hb⟩
      rw [List.idxOf_cons_ne _ (Ne.symm hat), List.idxOf_cons_ne _ (Ne.symm hbt)]
      omega

theorem isSeries_split {tn : TaskNetwork I A C} {t : I} {l : List I} {x : A ⊕ C} {xs : List (A ⊕ C)}
    (h : tn.IsSeqNet (t :: l) (x :: xs)) :
    TaskNetwork.IsSeries tn (tn.restrict (· = t)) (tn.restrict (· ∈ l)) where
  disjoint := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [TaskNetwork.restrict, Finset.mem_filter] at hy hy'
    exact (List.nodup_cons.1 h.nodup).1 (hy.2 ▸ hy'.2)
  memT y := by
    simp only [TaskNetwork.restrict, Finset.mem_filter, h.memT, List.mem_cons]
    tauto
  α₁ _ _ := rfl
  α₂ _ _ := rfl
  ord a b := by
    have hnd := List.nodup_cons.1 h.nodup
    have key : tn.ord a b ↔ (a = t ∧ b ∈ l) ∨ (a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b) := by
      rw [h.ord]
      simp only [List.mem_cons]
      by_cases ha : a = t <;> by_cases hb : b = t
      · subst ha; subst hb; simp [hnd.1]
      · subst ha
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hb)]
        constructor
        · rintro ⟨-, hb', -⟩; exact Or.inl ⟨rfl, hb'.resolve_left hb⟩
        · rintro (⟨-, hb'⟩ | ⟨ha', -⟩)
          · exact ⟨Or.inl rfl, Or.inr hb', by omega⟩
          · exact absurd ha' hnd.1
      · subst hb
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm ha)]
        constructor
        · rintro ⟨-, -, h'⟩; omega
        · rintro (⟨h', -⟩ | ⟨-, hb', -⟩)
          · exact absurd h' ha
          · exact absurd hb' hnd.1
      · rw [List.idxOf_cons_ne _ (Ne.symm ha), List.idxOf_cons_ne _ (Ne.symm hb)]
        constructor
        · rintro ⟨ha', hb', h'⟩
          exact Or.inr ⟨ha'.resolve_left ha, hb'.resolve_left hb, by omega⟩
        · rintro (⟨h', -⟩ | ⟨ha', hb', h'⟩)
          · exact absurd h' ha
          · exact ⟨Or.inr ha', Or.inr hb', by omega⟩
    have hT : ∀ y, y ∈ tn.T ↔ y = t ∨ y ∈ l := fun y => by rw [h.memT]; simp
    simp only [TaskNetwork.restrict, Finset.mem_filter, key, hT]
    constructor
    · rintro (⟨rfl, hb⟩ | ⟨ha, hb, hlt⟩)
      · exact Or.inr (Or.inr ⟨⟨Or.inl rfl, rfl⟩, Or.inr hb, hb⟩)
      · exact Or.inr (Or.inl ⟨Or.inr ⟨ha, hb, hlt⟩, ha, hb⟩)
    · rintro (⟨h', rfl, rfl⟩ | ⟨h', -, -⟩ | ⟨⟨-, rfl⟩, -, hb⟩)
      · exact absurd (h'.elim (fun h => h.2) (fun h => h.1)) hnd.1
      · exact h'
      · exact Or.inl ⟨rfl, hb⟩

theorem netYieldN_empty {tn : TaskNetwork I A C} (hT : tn.T = ∅) {n : ℕ} {as : List A}
    (h : D.NetYieldN n tn as) : as = [] := by
  obtain ⟨tn', hs, -, l, hlin, has⟩ := h
  cases n with
  | zero =>
    cases hs
    have hl : l = [] := by
      rcases l with _ | ⟨y, l⟩
      · rfl
      · have := (hlin.2.1 y).1 (by simp); rw [hT] at this; simp at this
    subst hl
    have : ([] : List (A ⊕ C)) = as.map Sum.inl := has
    exact List.map_eq_nil_iff.1 this.symm
  | succ n =>
    obtain ⟨tn₂, ⟨t, m, -, ht, -⟩, -⟩ := hs.exists_head
    rw [hT] at ht; simp at ht

/-- **Refinements of a sequence network.** -/
theorem seqY_of_netYieldN (hmwf : ∀ m ∈ D.methods, m.subtasks.WF) :
    ∀ {l : List I} {xs : List (A ⊕ C)} {tn : TaskNetwork I A C} {n : ℕ} {as : List A},
      tn.IsSeqNet l xs → D.NetYieldN n tn as → SeqY (YL D n) xs as := by
  intro l
  induction l with
  | nil =>
    intro xs tn n as h hy
    obtain rfl : xs = [] := by have := h.labels; simpa using this.symm
    have hT : tn.T = ∅ := by ext y; simp [h.memT]
    rw [netYieldN_empty hT hy]
    exact .nil
  | cons t l ih =>
    intro xs tn n as h hy
    obtain ⟨x, xs, rfl⟩ : ∃ x xs', xs = x :: xs' := by
      have := h.labels; rcases xs with _ | ⟨x, xs⟩ <;> simp at this ⊢
    have hwf := h.wf
    have hser := isSeries_split h
    obtain ⟨n₁, n₂, as₁, as₂, rfl, rfl, h1, h2⟩ :=
      (Domain.netYieldN_isSeries_iff hser (TaskNetwork.restrict_wf hwf _)
        (TaskNetwork.restrict_wf hwf _)).1 hy
    have ht : t ∈ tn.T := (h.memT t).2 (by simp)
    have hx : tn.α t = x := by have := h.labels; simp at this; exact this.1
    have y1 := yl_of_single hmwf (isSingle_restrict hwf ht) h1
    simp only [TaskNetwork.restrict] at y1
    rw [hx] at y1
    exact .cons (y1.mono (by omega)) ((ih (isSeqNet_tail h) h2).mono fun _ _ hy => hy.mono (by omega))

/-! ## Set networks -/

theorem setNet_tail {tn : TaskNetwork I A C} {t : I} {l : List I} {x : A ⊕ C} {xs : List (A ⊕ C)}
    (h : AcycHard.SetNet tn (t :: l) (x :: xs)) : AcycHard.SetNet (tn.restrict (· ∈ l)) l xs where
  nodup := (List.nodup_cons.1 h.nodup).2
  memT y := by
    simp only [TaskNetwork.restrict, Finset.mem_filter, h.memT, List.mem_cons]
    tauto
  labels := by
    have := h.labels
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2
  ord a b hab := h.ord a b hab.1

theorem setNet_wf {tn : TaskNetwork I A C} {l : List I} {xs : List (A ⊕ C)}
    (h : AcycHard.SetNet tn l xs) : tn.WF where
  mem_left hab := absurd hab (h.ord _ _)
  mem_right hab := absurd hab (h.ord _ _)
  irrefl t hab := h.ord t t hab
  trans hab := absurd hab (h.ord _ _)

theorem isPar_split {tn : TaskNetwork I A C} {t : I} {l : List I} {x : A ⊕ C} {xs : List (A ⊕ C)}
    (h : AcycHard.SetNet tn (t :: l) (x :: xs)) :
    TaskNetwork.IsPar tn (tn.restrict (· = t)) (tn.restrict (· ∈ l)) where
  disjoint := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [TaskNetwork.restrict, Finset.mem_filter] at hy hy'
    exact (List.nodup_cons.1 h.nodup).1 (hy.2 ▸ hy'.2)
  memT y := by
    simp only [TaskNetwork.restrict, Finset.mem_filter, h.memT, List.mem_cons]
    tauto
  α₁ _ _ := rfl
  α₂ _ _ := rfl
  ord a b := by
    simp only [TaskNetwork.restrict]
    constructor
    · intro hab; exact absurd hab (h.ord a b)
    · rintro (⟨hab, -⟩ | ⟨hab, -⟩) <;> exact hab

/-- **Refinements of a set network.** -/
theorem setY_of_netYieldN (hmwf : ∀ m ∈ D.methods, m.subtasks.WF) :
    ∀ {l : List I} {xs : List (A ⊕ C)} {tn : TaskNetwork I A C} {n : ℕ} {as : List A},
      AcycHard.SetNet tn l xs → D.NetYieldN n tn as → SetY (YL D n) xs as := by
  intro l
  induction l with
  | nil =>
    intro xs tn n as h hy
    obtain rfl : xs = [] := by have := h.labels; simpa using this.symm
    have hT : tn.T = ∅ := by ext y; simp [h.memT]
    rw [netYieldN_empty hT hy]
    exact .nil
  | cons t l ih =>
    intro xs tn n as h hy
    obtain ⟨x, xs, rfl⟩ : ∃ x xs', xs = x :: xs' := by
      have := h.labels; rcases xs with _ | ⟨x, xs⟩ <;> simp at this ⊢
    have hwf := setNet_wf h
    have hpar := isPar_split h
    obtain ⟨n₁, n₂, as₁, as₂, rfl, hint, h1, h2⟩ :=
      (Domain.netYieldN_isPar_iff hpar (TaskNetwork.restrict_wf hwf _)
        (TaskNetwork.restrict_wf hwf _)).1 hy
    have ht : t ∈ tn.T := (h.memT t).2 (by simp)
    have hx : tn.α t = x := by have := h.labels; simp at this; exact this.1
    have y1 := yl_of_single hmwf (isSingle_restrict hwf ht) h1
    simp only [TaskNetwork.restrict] at y1
    rw [hx] at y1
    exact .cons (y1.mono (by omega)) ((ih (setNet_tail h) h2).mono fun _ _ hy => hy.mono (by omega)) hint

end HardTR

end FOND
