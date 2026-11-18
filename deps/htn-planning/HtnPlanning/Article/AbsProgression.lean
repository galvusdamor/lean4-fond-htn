import HtnPlanning.Progression.Progression
import HtnPlanning.Core.Reachability
import HtnPlanning.Core.DecompPersist
/-!
# Progression without states, and how a network splits under it

Progression bounds (Def. 4.3) only concern the task networks, so states are irrelevant once all
actions are applicable — the *abstraction* of Prop. 4.2.14.  This file studies the resulting
**abstract progression** `HTN.AbsStep M`: an unconstrained primitive task is removed, or an
unconstrained compound task is decomposed.

The main result is the **splitting lemma** `HTN.AbsReachN.split`: along an abstract progression
from `tn` to `tn'`, every task `x` of `tn` evolves on its own — the tasks of `tn'` descending from
`x` form a network reachable from the one-task network `{x}` — and a part is touched only once
the parts of all predecessors of `x` are empty.  Parts are compared up to `TaskNetwork.Agree`
(same tasks, same order, same labels *on the tasks*).
-/

namespace HTN

universe v w x

variable {A : Type v} {C : Type w} {I : Type x}

namespace TaskNetwork

/-- Two task networks agree: the same tasks, the same order and the same labels on the tasks. -/
def Agree (tn tn' : TaskNetwork I A C) : Prop :=
  tn.T = tn'.T ∧ tn.ord = tn'.ord ∧ ∀ t ∈ tn.T, tn.α t = tn'.α t

theorem Agree.refl (tn : TaskNetwork I A C) : tn.Agree tn := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Agree.symm {tn tn' : TaskNetwork I A C} (h : tn.Agree tn') : tn'.Agree tn :=
  ⟨h.1.symm, h.2.1.symm, fun t ht => (h.2.2 t (h.1 ▸ ht)).symm⟩

theorem Agree.trans {a b c : TaskNetwork I A C} (h₁ : a.Agree b) (h₂ : b.Agree c) : a.Agree c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun t ht => (h₁.2.2 t ht).trans (h₂.2.2 t (h₁.1 ▸ ht))⟩

/-- The sub-network on the tasks satisfying `S`. -/
def restrict (tn : TaskNetwork I A C) (S : I → Prop) [DecidablePred S] : TaskNetwork I A C where
  T := tn.T.filter S
  ord a b := tn.ord a b ∧ S a ∧ S b
  α := tn.α

theorem restrict_wf {tn : TaskNetwork I A C} (hwf : tn.WF) (S : I → Prop) [DecidablePred S] :
    (tn.restrict S).WF where
  mem_left h := Finset.mem_filter.2 ⟨hwf.mem_left h.1, h.2.1⟩
  mem_right h := Finset.mem_filter.2 ⟨hwf.mem_right h.1, h.2.2⟩
  irrefl t h := hwf.irrefl t h.1
  trans h₁ h₂ := ⟨hwf.trans h₁.1 h₂.1, h₁.2.1, h₂.2.2⟩

variable [DecidableEq I]

theorem restrict_progress_self {tn : TaskNetwork I A C} {S : I → Prop} [DecidablePred S] {t : I}
    (ht : S t) : (tn.progress t).restrict S = (tn.restrict S).progress t := by
  apply TaskNetwork.ext'
  · ext y; simp only [restrict, progress, Finset.mem_filter, Finset.mem_erase]; tauto
  · funext a b; simp only [restrict, progress]; apply propext; tauto
  · rfl

theorem agree_restrict_progress_other {tn : TaskNetwork I A C} {S : I → Prop} [DecidablePred S]
    {t : I} (ht : ¬ S t) : (tn.restrict S).Agree ((tn.progress t).restrict S) := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · ext y
    simp only [restrict, progress, Finset.mem_filter, Finset.mem_erase]
    by_cases e : y = t
    · subst e; simp [ht]
    · simp [e]
  · funext a b
    simp only [restrict, progress]
    apply propext
    constructor
    · rintro ⟨h, ha, hb⟩; exact ⟨⟨h, fun e => ht (e ▸ ha)⟩, ha, hb⟩
    · rintro ⟨⟨h, -⟩, ha, hb⟩; exact ⟨h, ha, hb⟩

theorem restrict_decompose_self {tn tn'' : TaskNetwork I A C} (hwf : tn.WF) (hwf'' : tn''.WF)
    (hdisj : Disjoint tn.T tn''.T) {S S' : I → Prop} [DecidablePred S] [DecidablePred S']
    (hS' : ∀ y, S' y ↔ y ∈ tn''.T ∨ S y) {t : I} (ht : S t) :
    (decomposeWith tn t tn'').restrict S' = decomposeWith (tn.restrict S) t tn'' := by
  have hn : ∀ y, y ∈ tn.T → y ∉ tn''.T := fun y hy => Finset.disjoint_left.1 hdisj hy
  apply TaskNetwork.ext'
  · ext y
    simp only [restrict, decomposeWith, Finset.mem_filter, Finset.mem_union, Finset.mem_erase, hS']
    tauto
  · funext a b
    simp only [restrict, decomposeWith]
    apply propext
    constructor
    · rintro ⟨h, ha, hb⟩
      rw [hS'] at ha hb
      rcases h with h | ⟨h, hb'⟩ | ⟨h, ha'⟩ | ⟨h, hat, hbt⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨⟨h, ha.resolve_left (hn a (hwf.mem_left h)), ht⟩, hb'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨h, ht, hb.resolve_left (hn b (hwf.mem_right h))⟩, ha'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨⟨h, ha.resolve_left (hn a (hwf.mem_left h)),
          hb.resolve_left (hn b (hwf.mem_right h))⟩, hat, hbt⟩))
    · rintro (h | ⟨⟨h, ha, -⟩, hb'⟩ | ⟨⟨h, -, hb⟩, ha'⟩ | ⟨⟨h, ha, hb⟩, hat, hbt⟩)
      · exact ⟨Or.inl h, (hS' a).2 (Or.inl (hwf''.mem_left h)),
          (hS' b).2 (Or.inl (hwf''.mem_right h))⟩
      · exact ⟨Or.inr (Or.inl ⟨h, hb'⟩), (hS' a).2 (Or.inr ha), (hS' b).2 (Or.inl hb')⟩
      · exact ⟨Or.inr (Or.inr (Or.inl ⟨h, ha'⟩)), (hS' a).2 (Or.inl ha'), (hS' b).2 (Or.inr hb)⟩
      · exact ⟨Or.inr (Or.inr (Or.inr ⟨h, hat, hbt⟩)), (hS' a).2 (Or.inr ha),
          (hS' b).2 (Or.inr hb)⟩
  · rfl

theorem agree_restrict_decompose_other {tn tn'' : TaskNetwork I A C} (hwf : tn.WF)
    (hwf'' : tn''.WF) (hdisj : Disjoint tn.T tn''.T) {S S' : I → Prop} [DecidablePred S] [DecidablePred S']
    (hnew : ∀ y ∈ tn''.T, ¬ S' y) (hold : ∀ y, y ∉ tn''.T → (S' y ↔ S y)) {t : I}
    (ht : ¬ S t) : (tn.restrict S).Agree ((decomposeWith tn t tn'').restrict S') := by
  have hn : ∀ y, y ∈ tn.T → y ∉ tn''.T := fun y hy => Finset.disjoint_left.1 hdisj hy
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · ext y
    simp only [restrict, decomposeWith, Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
    by_cases hy : y ∈ tn''.T
    · simp only [hy, or_true, true_and, hnew y hy, iff_false, not_and]
      exact fun h => absurd hy (hn y h)
    · rw [hold y hy]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inl ⟨fun e => ht (e ▸ h2), h1⟩, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact ⟨h1.2, h2⟩
        · exact absurd h1 hy
  · funext a b
    simp only [restrict, decomposeWith]
    apply propext
    constructor
    · rintro ⟨h, ha, hb⟩
      have ha' := hn a (hwf.mem_left h)
      have hb' := hn b (hwf.mem_right h)
      exact ⟨Or.inr (Or.inr (Or.inr ⟨h, fun e => ht (e ▸ ha), fun e => ht (e ▸ hb)⟩)),
        (hold a ha').2 ha, (hold b hb').2 hb⟩
    · rintro ⟨h, ha, hb⟩
      have ha' : a ∉ tn''.T := fun h' => hnew a h' ha
      have hb' : b ∉ tn''.T := fun h' => hnew b h' hb
      rw [hold a ha'] at ha
      rw [hold b hb'] at hb
      rcases h with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -, -⟩
      · exact absurd (hwf''.mem_left h) ha'
      · exact absurd h hb'
      · exact absurd h ha'
      · exact ⟨h, ha, hb⟩
  · have hy' : y ∈ tn.T := (Finset.mem_filter.1 hy).1
    simp [restrict, decomposeWith, hn y hy']

end TaskNetwork

open TaskNetwork

variable [DecidableEq I]

section Abs

variable (M : Set (Method I A C))

/-- **Abstract progression**: an unconstrained primitive task is removed, or an unconstrained
compound task is decomposed. -/
inductive AbsStep : TaskNetwork I A C → TaskNetwork I A C → Prop
  | prog {tn : TaskNetwork I A C} {t : I} (hu : tn.Unconstrained t) (hp : tn.IsPrimitiveId t) :
      AbsStep tn (tn.progress t)
  | decomp {tn tn' : TaskNetwork I A C} {t : I} {m : Method I A C} (hu : tn.Unconstrained t)
      (h : DecompStep M tn t m tn') : AbsStep tn tn'

/-- `n` steps of abstract progression. -/
inductive AbsReachN : ℕ → TaskNetwork I A C → TaskNetwork I A C → Prop
  | refl (tn : TaskNetwork I A C) : AbsReachN 0 tn tn
  | head {n : ℕ} {tn tn₁ tn₂ : TaskNetwork I A C} (h : AbsStep M tn tn₁)
      (hs : AbsReachN n tn₁ tn₂) : AbsReachN (n + 1) tn tn₂

variable {M}

theorem AbsReachN.tail {n : ℕ} {tn tn₁ tn₂ : TaskNetwork I A C} (h : AbsReachN M n tn tn₁)
    (hs : AbsStep M tn₁ tn₂) : AbsReachN M (n + 1) tn tn₂ := by
  induction h with
  | refl => exact .head hs (.refl _)
  | head h _ ih => exact .head h (ih hs)

theorem AbsReachN.exists_last {n : ℕ} {tn tn₂ : TaskNetwork I A C}
    (h : AbsReachN M (n + 1) tn tn₂) : ∃ tn₁, AbsReachN M n tn tn₁ ∧ AbsStep M tn₁ tn₂ := by
  induction n generalizing tn with
  | zero =>
    cases h with
    | head h hs => cases hs; exact ⟨tn, .refl _, h⟩
  | succ n ih =>
    cases h with
    | head h hs =>
      obtain ⟨tn₁, hr, hst⟩ := ih hs
      exact ⟨tn₁, .head h hr, hst⟩

theorem AbsStep.wf {tn tn' : TaskNetwork I A C} (h : AbsStep M tn tn') (hwf : tn.WF) : tn'.WF := by
  cases h with
  | prog hu _ => exact TaskNetwork.progress_wf hwf hu
  | decomp _ h => exact h.wf hwf

theorem AbsReachN.wf {n : ℕ} {tn tn' : TaskNetwork I A C} (h : AbsReachN M n tn tn')
    (hwf : tn.WF) : tn'.WF := by
  induction h with
  | refl => exact hwf
  | head h _ ih => exact ih (h.wf hwf)

theorem AbsReachN.T_empty {n : ℕ} {tn tn' : TaskNetwork I A C} (h : AbsReachN M n tn tn')
    (he : tn.T = ∅) : tn'.T = ∅ := by
  induction h with
  | refl => exact he
  | head h _ _ =>
    cases h with
    | prog hu _ => exact absurd hu.1 (by simp [he])
    | decomp hu _ => exact absurd hu.1 (by simp [he])

/-- Abstract progression depends on the labels of the tasks only. -/
theorem AbsStep.agree {tn₁ tn₁' tn₂ : TaskNetwork I A C} (hag : tn₁.Agree tn₁')
    (h : AbsStep M tn₁ tn₂) : ∃ tn₂', AbsStep M tn₁' tn₂' ∧ tn₂.Agree tn₂' := by
  obtain ⟨hT, ho, hα⟩ := hag
  cases h with
  | @prog t hu hp =>
    refine ⟨tn₁'.progress t, .prog ⟨hT ▸ hu.1, fun t' ht' => ?_⟩ ?_, ?_, ?_, ?_⟩
    · rw [← ho]; exact hu.2 t' (hT ▸ ht')
    · obtain ⟨a, ha⟩ := hp; exact ⟨a, (hα t hu.1).symm.trans ha⟩
    · simp [TaskNetwork.progress, hT]
    · funext a b; simp [TaskNetwork.progress, ho]
    · intro y hy; exact hα y (Finset.mem_of_mem_erase hy)
  | @decomp _ t m hu hd =>
    obtain ⟨hm, ht, hαt, tn'', hwf'', hiso, hdisj, rfl⟩ := hd
    refine ⟨decomposeWith tn₁' t tn'',
      .decomp ⟨hT ▸ hu.1, fun t' ht' => ?_⟩ ⟨hm, hT ▸ ht, (hα t ht).symm.trans hαt, tn'', hwf'',
        hiso, hT ▸ hdisj, rfl⟩, ?_, ?_, ?_⟩
    · rw [← ho]; exact hu.2 t' (hT ▸ ht')
    · simp [decomposeWith, hT]
    · funext a b; simp [decomposeWith, ho]
    · intro y hy
      simp only [decomposeWith]
      split_ifs with h
      · rfl
      · rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact hα y hy
        · exact absurd hy h

theorem AbsReachN.agree_tail {n : ℕ} {N tn₁ tn₂ : TaskNetwork I A C} {N₁ : TaskNetwork I A C}
    (hr : AbsReachN M n N N₁) (hag : N₁.Agree tn₁) (hs : AbsStep M tn₁ tn₂) :
    ∃ N₂, AbsReachN M (n + 1) N N₂ ∧ N₂.Agree tn₂ := by
  obtain ⟨N₂, h1, h2⟩ := hs.agree hag.symm
  exact ⟨N₂, hr.tail h1, h2.symm⟩

end Abs

/-! ### The splitting lemma -/

section Split

variable {M : Set (Method I A C)}

/-- **Splitting.**  Along `n` steps of abstract progression from `tn` to `tn'`, each task of `tn'`
descends from a task `o y` of `tn`; descendants of ordered tasks stay ordered; the descendants of
each `x` form (up to agreement) a network reachable from `{x}` in `cnt x ≤ n` steps; and a part is
touched (`0 < cnt x`) only when the parts of all predecessors of `x` are empty. -/
theorem AbsReachN.split {n : ℕ} {tn tn' : TaskNetwork I A C} (h : AbsReachN M n tn tn')
    (hwf : tn.WF) :
    ∃ (o : I → I) (cnt : I → ℕ),
      (∀ y ∈ tn'.T, o y ∈ tn.T) ∧
      (∀ y ∈ tn'.T, ∀ y' ∈ tn'.T, tn.ord (o y) (o y') → tn'.ord y y') ∧
      (∀ x ∈ tn.T, cnt x ≤ n ∧ ∃ N, AbsReachN M (cnt x) (tn.restrict (· = x)) N ∧
          N.Agree (tn'.restrict (fun y => o y = x))) ∧
      (∀ x ∈ tn.T, ∀ z ∈ tn.T, tn.ord z x → 0 < cnt x → ∀ y ∈ tn'.T, o y ≠ z) := by
  induction n generalizing tn' with
  | zero =>
    cases h
    exact ⟨fun y => y, fun _ => 0, fun y hy => hy, fun y _ y' _ h => h,
      fun x _ => ⟨le_rfl, _, .refl _, Agree.refl _⟩, fun _ _ _ _ _ h => absurd h (lt_irrefl 0)⟩
  | succ n ih =>
    obtain ⟨tn₁, hr, hs⟩ := h.exists_last
    have hwf₁ : tn₁.WF := hr.wf hwf
    obtain ⟨o, cnt, hA, hB, hC, hD⟩ := ih hr
    cases hs with
    | @prog t hu hp =>
      refine ⟨o, Function.update cnt (o t) (cnt (o t) + 1), fun y hy => hA y (Finset.mem_of_mem_erase hy),
        fun y hy y' hy' hord => ⟨hB y (Finset.mem_of_mem_erase hy) y' (Finset.mem_of_mem_erase hy')
          hord, (Finset.mem_erase.1 hy).1⟩, fun x hx => ?_, fun x hx z hz hzx hpos y hy => ?_⟩
      · obtain ⟨hcx, N, hN, hag⟩ := hC x hx
        by_cases e : x = (o t)
        · subst e
          refine ⟨by simp; omega, ?_⟩
          have hstep : AbsStep M (tn₁.restrict (fun y => o y = o t))
              ((tn₁.restrict (fun y => o y = o t)).progress t) :=
            .prog ⟨Finset.mem_filter.2 ⟨hu.1, rfl⟩, fun t' ht' h' => hu.2 t'
              (Finset.mem_filter.1 ht').1 h'.1⟩ hp
          obtain ⟨N₂, h1, h2⟩ := hN.agree_tail hag hstep
          rw [← restrict_progress_self (tn := tn₁) (S := fun y => o y = o t) (t := t) rfl] at h2
          exact ⟨N₂, by simpa using h1, h2⟩
        · rw [Function.update_of_ne e]
          exact ⟨by omega, N, hN, hag.trans (agree_restrict_progress_other (Ne.symm e))⟩
      · have hy₁ : y ∈ tn₁.T := Finset.mem_of_mem_erase hy
        by_cases e : x = (o t)
        · subst e
          intro hoy
          rw [← hoy] at hzx
          exact hu.2 y hy₁ (hB y hy₁ t hu.1 hzx)
        · rw [Function.update_of_ne e] at hpos
          exact hD x hx z hz hzx hpos y hy₁
    | @decomp _ t m hu hd =>
      have hd' := hd
      obtain ⟨hm, ht, hαt, tn'', hwf'', hiso, hdisj, rfl⟩ := hd
      have hn : ∀ y, y ∈ tn₁.T → y ∉ tn''.T := fun y hy => Finset.disjoint_left.1 hdisj hy
      let o' : I → I := fun y => if y ∈ tn''.T then (o t) else o y
      have ho'new : ∀ y ∈ tn''.T, o' y = (o t) := fun y hy => by simp [o', hy]
      have ho'old : ∀ y, y ∉ tn''.T → o' y = o y := fun y hy => by simp [o', hy]
      have hx₀ : o t ∈ tn.T := hA t ht
      refine ⟨o', Function.update cnt (o t) (cnt (o t) + 1), fun y hy => ?_, fun y hy y' hy' hord => ?_,
        fun x hx => ?_, fun x hx z hz hzx hpos y hy => ?_⟩
      · rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · rw [ho'old y (hn y hy)]; exact hA y hy
        · rw [ho'new y hy]; exact hx₀
      · rcases mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy''
        · rcases mem_decomposeWith_T.1 hy' with ⟨hy₁', hyt'⟩ | hy''
          · rw [ho'old y (hn y hy₁), ho'old y' (hn y' hy₁')] at hord
            exact (decomposeWith_ord_old_old hwf'' hdisj hy₁ hyt hy₁' hyt').2
              (hB y hy₁ y' hy₁' hord)
          · rw [ho'old y (hn y hy₁), ho'new y' hy''] at hord
            exact (decomposeWith_ord_old_new hwf₁ hwf'' hdisj hy₁ hy'').2 (hB y hy₁ t ht hord)
        · rcases mem_decomposeWith_T.1 hy' with ⟨hy₁', hyt'⟩ | hy'''
          · rw [ho'new y hy'', ho'old y' (hn y' hy₁')] at hord
            exact (decomposeWith_ord_new_old hwf₁ hwf'' hdisj hy'' hy₁').2 (hB t ht y' hy₁' hord)
          · rw [ho'new y hy'', ho'new y' hy'''] at hord
            exact absurd hord (hwf.irrefl _)
      · obtain ⟨hcx, N, hN, hag⟩ := hC x hx
        by_cases e : x = (o t)
        · subst e
          refine ⟨by simp; omega, ?_⟩
          have hS' : ∀ y, (o' y = o t) ↔ y ∈ tn''.T ∨ o y = o t := fun y => by
            by_cases hy : y ∈ tn''.T
            · simp [ho'new y hy, hy]
            · simp [ho'old y hy, hy]
          have hstep : AbsStep M (tn₁.restrict (fun y => o y = o t))
              (decomposeWith (tn₁.restrict (fun y => o y = o t)) t tn'') :=
            .decomp ⟨Finset.mem_filter.2 ⟨hu.1, rfl⟩, fun t' ht' h' => hu.2 t'
              (Finset.mem_filter.1 ht').1 h'.1⟩
              ⟨hm, Finset.mem_filter.2 ⟨ht, rfl⟩, hαt, tn'', hwf'', hiso,
                Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hdisj, rfl⟩
          obtain ⟨N₂, h1, h2⟩ := hN.agree_tail hag hstep
          rw [← restrict_decompose_self (S := fun y => o y = o t) (S' := fun y => o' y = o t) hwf₁ hwf''
            hdisj hS' (t := t) rfl] at h2
          exact ⟨N₂, by simpa using h1, h2⟩
        · rw [Function.update_of_ne e]
          refine ⟨by omega, N, hN, hag.trans (agree_restrict_decompose_other hwf₁ hwf'' hdisj
            (fun y hy h => e (by rw [← h, ho'new y hy])) (fun y hy => by rw [ho'old y hy])
            (Ne.symm e))⟩
      · by_cases e : x = (o t)
        · subst e
          rcases mem_decomposeWith_T.1 hy with ⟨hy₁, -⟩ | hy''
          · rw [ho'old y (hn y hy₁)]
            intro hoy
            rw [← hoy] at hzx
            exact hu.2 y hy₁ (hB y hy₁ t ht hzx)
          · rw [ho'new y hy'']
            intro h; rw [h] at hzx; exact hwf.irrefl _ hzx
        · rw [Function.update_of_ne e] at hpos
          rcases mem_decomposeWith_T.1 hy with ⟨hy₁, -⟩ | hy''
          · rw [ho'old y (hn y hy₁)]; exact hD x hx z hz hzx hpos y hy₁
          · rw [ho'new y hy'']; exact hD x hx z hz hzx hpos t ht

end Split

end HTN
