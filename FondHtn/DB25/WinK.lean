import FondHtn.FixedMethodsLemmas
import FondHtn.IsoLemmas
/-!
# Solvable belief states with a terminal condition; series composition

`FOND.Problem.WinK P K tn s` generalises `BeliefSolvable` (`K = ⊤`): the primitive network `tn`
can be executed strongly from `s` (some unconstrained applicable task, all outcomes recursively)
and every complete execution ends in a state satisfying `K`.

* `FOND.Problem.winK_true_iff` — `WinK ⊤ = BeliefSolvable`;
* `FOND.Problem.WinK.congr`, `WinK.isoVia`, `WinK.iso` — invariance under `SameOn` and
  isomorphisms;
* `FOND.Problem.winK_split` — **series composition**: if the tasks satisfying `S` all precede
  the others, executing `tn` with terminal condition `K` is executing the `S`-part with terminal
  condition "the rest can be executed with terminal condition `K`".
-/

namespace FOND

open HTN FOND.TaskNetwork

namespace TaskNetwork

variable {I A C : Type}

/-- The restriction of a network to the tasks satisfying `S`. -/
def restr (tn : HTN.TaskNetwork I A C) (S : I → Prop) [DecidablePred S] : HTN.TaskNetwork I A C where
  T := tn.T.filter S
  ord := fun a b => tn.ord a b ∧ S a ∧ S b
  α := tn.α

variable (tn : HTN.TaskNetwork I A C) (S : I → Prop) [DecidablePred S]

@[simp] theorem mem_restr_T {x : I} : x ∈ (restr tn S).T ↔ x ∈ tn.T ∧ S x := Finset.mem_filter

theorem SameOn.refl' : SameOn tn tn := ⟨rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem SameOn.symm' {tn tn' : HTN.TaskNetwork I A C} (h : SameOn tn tn') : SameOn tn' tn := by
  obtain ⟨hT, ho, hα⟩ := h
  refine ⟨hT.symm, fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [← hT] at ha hb; exact (ho a ha b hb).symm
  · rw [← hT] at ha; exact (hα a ha).symm

theorem SameOn.trans' {tn tn' tn'' : HTN.TaskNetwork I A C} (h : SameOn tn tn')
    (h' : SameOn tn' tn'') : SameOn tn tn'' := by
  obtain ⟨hT, ho, hα⟩ := h
  obtain ⟨hT', ho', hα'⟩ := h'
  refine ⟨hT.trans hT', fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [ho a ha b hb]; rw [hT] at ha hb; exact ho' a ha b hb
  · rw [hα a ha]; rw [hT] at ha; exact hα' a ha

variable [DecidableEq I]

/-- Progress inside the `S`-part. -/
theorem restr_progress_in {t : I} (ht : S t) :
    SameOn ((restr tn S).progress t) (restr (tn.progress t) S) := by
  refine ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩
  · ext x; simp only [HTN.TaskNetwork.progress_T, Finset.mem_erase, mem_restr_T]; tauto
  · simp only [HTN.TaskNetwork.progress_ord, restr]; tauto

/-- Progress inside the `S`-part leaves the rest unchanged. -/
theorem restr_progress_out {t : I} (ht : S t) :
    SameOn (restr tn fun x => ¬ S x) (restr (tn.progress t) fun x => ¬ S x) := by
  refine ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩
  · ext x
    simp only [mem_restr_T, HTN.TaskNetwork.progress_T, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨fun e => h2 (e ▸ ht), h1⟩, h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · simp only [mem_restr_T] at ha
    simp only [HTN.TaskNetwork.progress_ord, restr]
    constructor
    · rintro ⟨h, h1, h2⟩; exact ⟨⟨h, fun e => h1 (e ▸ ht)⟩, h1, h2⟩
    · rintro ⟨⟨h, -⟩, h1, h2⟩; exact ⟨h, h1, h2⟩

/-- If the `S`-part is empty, the network is its complement. -/
theorem restr_compl_of_empty (h : (restr tn S).T = ∅) : SameOn tn (restr tn fun x => ¬ S x) := by
  have hS : ∀ x ∈ tn.T, ¬ S x := fun x hx hs => by
    have : x ∈ (restr tn S).T := (mem_restr_T tn S).2 ⟨hx, hs⟩
    rw [h] at this; simp at this
  refine ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩
  · ext x; simp only [mem_restr_T]; exact ⟨fun hx => ⟨hx, hS x hx⟩, fun h => h.1⟩
  · simp only [restr]; exact ⟨fun h => ⟨h, hS a ha, hS b hb⟩, fun h => h.1⟩

end TaskNetwork

namespace Problem

variable {F A C I : Type} [DecidableEq I] (P : Problem F A C I)

/-- **Strong execution with a terminal condition.** -/
inductive WinK (K : Set F → Prop) : HTN.TaskNetwork I A C → Set F → Prop
  | empty {tn : HTN.TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) (hK : K s) : WinK K tn s
  | step {tn : HTN.TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, WinK K (tn.progress t) s') : WinK K tn s

variable {P}

theorem winK_true_iff {tn : HTN.TaskNetwork I A C} {s : Set F} :
    P.WinK (fun _ => True) tn s ↔ P.BeliefSolvable tn s := by
  constructor
  · intro h
    induction h with
    | empty h => exact .empty h
    | step hu hα happ _ ih => exact .step hu hα happ ih
  · intro h
    induction h with
    | empty h => exact .empty h trivial
    | step hu hα happ _ ih => exact .step hu hα happ ih

theorem WinK.mono {K K' : Set F → Prop} (hK : ∀ s, K s → K' s) {tn : HTN.TaskNetwork I A C}
    {s : Set F} (h : P.WinK K tn s) : P.WinK K' tn s := by
  induction h with
  | empty h h' => exact .empty h (hK _ h')
  | step hu hα happ _ ih => exact .step hu hα happ ih

theorem WinK.congr {K : Set F → Prop} {tn : HTN.TaskNetwork I A C} {s : Set F}
    (h : P.WinK K tn s) : ∀ {tn'}, SameOn tn tn' → P.WinK K tn' s := by
  induction h with
  | empty h hK => exact fun hs => .empty (hs.1 ▸ h) hK
  | @step tn s t a hu hα happ _ ih =>
    intro tn' hs
    exact .step (hs.unconstrained hu) ((hs.2.2 t hu.1).symm.trans hα) happ fun s' hs' =>
      ih s' hs' (hs.progress t)

theorem WinK.isoVia {K : Set F → Prop} {tn : HTN.TaskNetwork I A C} {s : Set F}
    (h : P.WinK K tn s) : ∀ {σ : I → I} {tn'}, HTN.TaskNetwork.IsoVia σ tn tn' → P.WinK K tn' s := by
  induction h with
  | empty h hK => exact fun hσ => .empty (hσ.empty h) hK
  | @step tn s t a hu hα happ _ ih =>
    intro σ tn' hσ
    exact .step (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ fun s' hs' =>
      ih s' hs' (hσ.progress hu.1)

theorem WinK.iso {K : Set F → Prop} {tn tn' : HTN.TaskNetwork I A C} {s : Set F}
    (h : P.WinK K tn s) (hi : tn.Iso tn') : P.WinK K tn' s :=
  let ⟨_, hσ⟩ := hi; h.isoVia hσ

/-! ## Series composition -/

section Split

variable (S : I → Prop) [DecidablePred S]

/-- The `S`-tasks precede the other tasks. -/
def Before (tn : HTN.TaskNetwork I A C) : Prop :=
  (∀ a ∈ tn.T, ∀ b ∈ tn.T, S a → ¬ S b → tn.ord a b) ∧
    ∀ a ∈ tn.T, ∀ b ∈ tn.T, ¬ S a → S b → ¬ tn.ord a b

theorem Before.progress {tn : HTN.TaskNetwork I A C} (h : Before S tn) (t : I) :
    Before S (tn.progress t) := by
  refine ⟨fun a ha b hb hSa hSb => ?_, fun a ha b hb hSa hSb hab => ?_⟩
  · have ha' := HTN.TaskNetwork.mem_progress_T.1 ha
    exact ⟨h.1 a ha'.2 b (HTN.TaskNetwork.mem_progress_T.1 hb).2 hSa hSb, ha'.1⟩
  · exact h.2 a (HTN.TaskNetwork.mem_progress_T.1 ha).2 b (HTN.TaskNetwork.mem_progress_T.1 hb).2 hSa hSb hab.1

/-- One direction of the series lemma, by induction on the outer game. -/
theorem winK_of_split {K : Set F → Prop} (Y : HTN.TaskNetwork I A C) {X : HTN.TaskNetwork I A C}
    {s : Set F} (h : P.WinK (P.WinK K Y) X s) :
    ∀ tn : HTN.TaskNetwork I A C, Before S tn → SameOn X (TaskNetwork.restr tn S) →
      SameOn Y (TaskNetwork.restr tn fun x => ¬ S x) → P.WinK K tn s := by
  induction h with
  | @empty X s hX hK =>
    intro tn _ hXs hYs
    have hE : (TaskNetwork.restr tn S).T = ∅ := hXs.1 ▸ hX
    exact hK.congr (hYs.trans' (TaskNetwork.restr_compl_of_empty tn S hE).symm')
  | @step X s t a hu hα happ _ ih =>
    intro tn hB hXs hYs
    have hu' := hXs.unconstrained hu
    obtain ⟨ht, hS⟩ := (TaskNetwork.mem_restr_T tn S).1 hu'.1
    refine .step (t := t) (a := a) ⟨ht, fun t' ht' hord => ?_⟩ ?_ happ fun s' hs' => ?_
    · by_cases hS' : S t'
      · exact hu'.2 t' ((TaskNetwork.mem_restr_T tn S).2 ⟨ht', hS'⟩) ⟨hord, hS', hS⟩
      · exact hB.2 t' ht' t ht hS' hS hord
    · exact (hXs.2.2 t hu.1).symm.trans hα
    · exact ih s' hs' _ (Before.progress S hB t)
        ((hXs.progress t).trans' (TaskNetwork.restr_progress_in tn S hS))
        (hYs.trans' (TaskNetwork.restr_progress_out tn S hS))

theorem split_of_winK {K : Set F → Prop} {tn : HTN.TaskNetwork I A C} {s : Set F}
    (h : P.WinK K tn s) : Before S tn →
      P.WinK (P.WinK K (TaskNetwork.restr tn fun x => ¬ S x)) (TaskNetwork.restr tn S) s := by
  induction h with
  | @empty tn s hT hK =>
    intro _
    have hE : (TaskNetwork.restr tn S).T = ∅ := by
      ext x; simp [hT]
    exact .empty hE (.empty (by ext x; simp [hT]) hK)
  | @step tn s t a hu hα happ hall ih =>
    intro hB
    by_cases hS : S t
    · refine .step (t := t) (a := a) ⟨(TaskNetwork.mem_restr_T tn S).2 ⟨hu.1, hS⟩,
        fun t' ht' hord => hu.2 t' ((TaskNetwork.mem_restr_T tn S).1 ht').1 hord.1⟩ hα happ
        fun s' hs' => ?_
      have := ih s' hs' (Before.progress S hB t)
      refine (this.mono fun s'' h'' => h''.congr
        (TaskNetwork.restr_progress_out tn S hS).symm').congr ?_
      exact (TaskNetwork.restr_progress_in tn S hS).symm'
    · by_cases hE : (TaskNetwork.restr tn S).T = ∅
      · exact .empty hE ((WinK.step hu hα happ hall).congr
          (TaskNetwork.restr_compl_of_empty tn S hE))
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hE
        obtain ⟨hxT, hSx⟩ := (TaskNetwork.mem_restr_T tn S).1 hx
        exact absurd (hB.1 x hxT t hu.1 hSx hS) (hu.2 x hxT)

/-- **Series composition.** -/
theorem winK_split {K : Set F → Prop} {tn : HTN.TaskNetwork I A C} {s : Set F}
    (hB : Before S tn) :
    P.WinK K tn s ↔
      P.WinK (P.WinK K (TaskNetwork.restr tn fun x => ¬ S x)) (TaskNetwork.restr tn S) s :=
  ⟨fun h => split_of_winK S h hB, fun h => winK_of_split S _ h tn hB (SameOn.refl' _)
    (SameOn.refl' _)⟩

end Split

/-! ## Small networks -/

theorem winK_empty_iff {K : Set F → Prop} {tn : HTN.TaskNetwork I A C} {s : Set F}
    (h : tn.T = ∅) : P.WinK K tn s ↔ K s := by
  constructor
  · intro hw
    cases hw with
    | empty _ hK => exact hK
    | step hu => have := hu.1; rw [h] at this; simp at this
  · exact fun hK => .empty h hK

/-- A network with one task. -/
theorem winK_single {K : Set F → Prop} {tn : HTN.TaskNetwork I A C} {s : Set F} {t : I} {a : A}
    (hT : tn.T = {t}) (hα : tn.α t = Sum.inl a) (hirr : ¬ tn.ord t t) :
    P.WinK K tn s ↔ (P.δ a).Applicable s ∧ ∀ s' ∈ (P.δ a).outcomes s, K s' := by
  have hp : (tn.progress t).T = ∅ := by simp [hT]
  constructor
  · intro hw
    cases hw with
    | empty h _ => rw [hT] at h; simp at h
    | @step _ _ t' a' hu hα' happ hall =>
      have : t' = t := by have := hu.1; rw [hT] at this; simpa using this
      subst this
      rw [hα] at hα'; cases hα'
      exact ⟨happ, fun s' hs' => (winK_empty_iff hp).1 (hall s' hs')⟩
  · rintro ⟨happ, hall⟩
    refine .step ⟨by rw [hT]; simp, fun t' ht' hord => ?_⟩ hα happ fun s' hs' =>
      .empty hp (hall s' hs')
    rw [hT] at ht'; obtain rfl : t' = t := by simpa using ht'
    exact hirr hord

/-- A network of two unordered tasks: either order. -/
theorem winK_pair {K : Set F → Prop} {tn : HTN.TaskNetwork I A C} {s : Set F} {t₁ t₂ : I}
    {a₁ a₂ : A} (hT : tn.T = {t₁, t₂}) (hne : t₁ ≠ t₂) (hα₁ : tn.α t₁ = Sum.inl a₁)
    (hα₂ : tn.α t₂ = Sum.inl a₂) (hord : ∀ x y, ¬ tn.ord x y) :
    P.WinK K tn s ↔
      ((P.δ a₁).Applicable s ∧ ∀ s' ∈ (P.δ a₁).outcomes s, (P.δ a₂).Applicable s' ∧
        ∀ s'' ∈ (P.δ a₂).outcomes s', K s'') ∨
      ((P.δ a₂).Applicable s ∧ ∀ s' ∈ (P.δ a₂).outcomes s, (P.δ a₁).Applicable s' ∧
        ∀ s'' ∈ (P.δ a₁).outcomes s', K s'') := by
  have hp₁ : (tn.progress t₁).T = {t₂} := by
    rw [HTN.TaskNetwork.progress_T, hT]; ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨Ne.symm hne, Or.inr rfl⟩
  have hp₂ : (tn.progress t₂).T = {t₁} := by
    rw [HTN.TaskNetwork.progress_T, hT]; ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨hne, Or.inl rfl⟩
  have hs₁ : ∀ s', P.WinK K (tn.progress t₁) s' ↔ (P.δ a₂).Applicable s' ∧
      ∀ s'' ∈ (P.δ a₂).outcomes s', K s'' := fun s' =>
    winK_single hp₁ (by simpa [HTN.TaskNetwork.progress] using hα₂) (fun h => hord _ _ h.1)
  have hs₂ : ∀ s', P.WinK K (tn.progress t₂) s' ↔ (P.δ a₁).Applicable s' ∧
      ∀ s'' ∈ (P.δ a₁).outcomes s', K s'' := fun s' =>
    winK_single hp₂ (by simpa [HTN.TaskNetwork.progress] using hα₁) (fun h => hord _ _ h.1)
  constructor
  · intro hw
    cases hw with
    | empty h _ => rw [hT] at h; simp at h
    | @step _ _ t a hu hα happ hall =>
      have := hu.1; rw [hT] at this
      rcases Finset.mem_insert.1 this with rfl | h
      · rw [hα₁] at hα; cases hα
        exact Or.inl ⟨happ, fun s' hs' => (hs₁ s').1 (hall s' hs')⟩
      · obtain rfl : t = t₂ := by simpa using h
        rw [hα₂] at hα; cases hα
        exact Or.inr ⟨happ, fun s' hs' => (hs₂ s').1 (hall s' hs')⟩
  · rintro (⟨happ, hall⟩ | ⟨happ, hall⟩)
    · exact .step ⟨by rw [hT]; simp, fun t' _ h => hord _ _ h⟩ hα₁ happ fun s' hs' =>
        (hs₁ s').2 (hall s' hs')
    · exact .step ⟨by rw [hT]; simp, fun t' _ h => hord _ _ h⟩ hα₂ happ fun s' hs' =>
        (hs₂ s').2 (hall s' hs')

end Problem

end FOND
