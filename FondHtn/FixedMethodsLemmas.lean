import FondHtn.FixedMethods
/-!
# Fixed methods: strong OD solutions are solvable belief states

`FOND.Problem.strongOD_iff_beliefSolvable`: a primitive task network `tn` admits a policy that is a
strong outcome-dependent solution in the sense of [CB21] iff `(tn, s_I)` is a solvable belief state
in the sense of [DB25].  Consequently the two notions of strong fixed-method plan existence agree
(`FOND.Problem.strongODSolvable_iff_fmSolvableDB`).
-/

namespace FOND

open HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace TaskNetwork

/-- The rest of `tn` after the tasks in `D` have been executed. -/
def rest [DecidableEq I] (tn : HTN.TaskNetwork I A C) (D : Finset I) : HTN.TaskNetwork I A C where
  T := tn.T \ D
  ord := fun a b => tn.ord a b ∧ a ∉ D
  α := tn.α

lemma rest_progress [DecidableEq I] (tn : HTN.TaskNetwork I A C) (D : Finset I) (t : I) :
    (rest tn D).progress t = rest tn (insert t D) := by
  refine HTN.TaskNetwork.ext' ?_ ?_ rfl
  · ext y
    simp only [HTN.TaskNetwork.progress_T, rest, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_insert]
    tauto
  · funext a b
    simp only [rest, HTN.TaskNetwork.progress, Finset.mem_insert, eq_iff_iff]
    tauto

/-- Two task networks agree on their tasks. -/
def SameOn (tn tn' : HTN.TaskNetwork I A C) : Prop :=
  tn.T = tn'.T ∧ (∀ a ∈ tn.T, ∀ b ∈ tn.T, (tn.ord a b ↔ tn'.ord a b)) ∧
    ∀ a ∈ tn.T, tn.α a = tn'.α a

lemma SameOn.progress [DecidableEq I] {tn tn' : HTN.TaskNetwork I A C} (h : SameOn tn tn')
    (t : I) : SameOn (tn.progress t) (tn'.progress t) := by
  obtain ⟨hT, ho, hα⟩ := h
  refine ⟨by simp [hT], ?_, ?_⟩
  · intro a ha b hb
    simp only [HTN.TaskNetwork.progress_T, Finset.mem_erase] at ha hb
    simp only [HTN.TaskNetwork.progress_ord, ho a ha.2 b hb.2]
  · intro a ha
    simp only [HTN.TaskNetwork.progress_T, Finset.mem_erase] at ha
    exact hα a ha.2

lemma SameOn.unconstrained {tn tn' : HTN.TaskNetwork I A C} (h : SameOn tn tn') {t : I}
    (hu : tn.Unconstrained t) : tn'.Unconstrained t := by
  obtain ⟨hT, ho, -⟩ := h
  refine ⟨hT ▸ hu.1, fun t' ht' hord => ?_⟩
  rw [← hT] at ht'
  exact hu.2 t' ht' ((ho t' ht' t hu.1).2 hord)

lemma sameOn_rest_empty [DecidableEq I] (tn : HTN.TaskNetwork I A C) : SameOn tn (rest tn ∅) :=
  ⟨by simp [rest], fun a _ b _ => by simp [rest], fun _ _ => rfl⟩

end TaskNetwork

namespace Problem

open FOND.TaskNetwork

variable (P : Problem F A C I) [DecidableEq I]

lemma BeliefSolvable.congr {tn : HTN.TaskNetwork I A C} {s : Set F}
    (h : P.BeliefSolvable tn s) : ∀ {tn'}, SameOn tn tn' → P.BeliefSolvable tn' s := by
  induction h with
  | empty h => exact fun hs => .empty (hs.1 ▸ h)
  | @step tn s t a hu hα happ _ ih =>
    intro tn' hs
    refine .step (hs.unconstrained hu) ((hs.2.2 t hu.1).symm.trans hα) happ fun s' hs' => ?_
    exact ih s' hs' (hs.progress t)

variable {P}

lemma fmReach_done_subset {tn : HTN.TaskNetwork I A C} {π : FMPolicy F I} {c : FMConfig F I}
    (h : P.FMReach tn π c) : c.done ⊆ tn.T := by
  induction h with
  | refl => simp
  | tail _ hstep ih =>
    obtain ⟨t, a, hv, s', -, rfl⟩ := hstep
    exact Finset.insert_subset hv.2.1 ih

/-- A strong OD policy yields a solvable belief state. -/
theorem beliefSolvable_of_strongOD {tn : HTN.TaskNetwork I A C} {π : FMPolicy F I}
    (h : P.StrongOD tn π) : P.BeliefSolvable tn P.init := by
  suffices key : ∀ n, ∀ c : FMConfig F I, (tn.T \ c.done).card = n → P.FMReach tn π c →
      P.BeliefSolvable (rest tn c.done) c.state by
    have := key _ ⟨∅, P.init⟩ rfl Relation.ReflTransGen.refl
    exact BeliefSolvable.congr P this (by
      refine ⟨by simp [rest], fun a _ b _ => by simp [rest], fun _ _ => rfl⟩)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hn hreach
    rcases h c hreach with hc | ⟨t, a, hv⟩
    · have hc' : c.done = tn.T := hc
      exact .empty (by simp [rest, hc'])
    · obtain ⟨hπ, htT, htD, hpred, hα, happ⟩ := hv
      refine .step (t := t) (a := a) ⟨by simp [rest, htT, htD], ?_⟩ hα happ ?_
      · rintro t' ht' ⟨hord, hnd⟩
        exact hnd (hpred t' (Finset.mem_sdiff.1 ht').1 hord)
      · intro s' hs'
        rw [rest_progress]
        refine ih _ ?_ ⟨insert t c.done, s'⟩ rfl
          (hreach.tail ⟨t, a, ⟨hπ, htT, htD, hpred, hα, happ⟩, s', hs', rfl⟩)
        rw [← hn]
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset_sdiff (subset_refl _) (Finset.subset_insert _ _), fun hsub => ?_⟩
        have : t ∈ tn.T \ c.done := Finset.mem_sdiff.2 ⟨htT, htD⟩
        simpa using hsub this

open Classical in
/-- The policy read off a solvable belief state. -/
noncomputable def beliefPolicy (P : Problem F A C I) (tn : HTN.TaskNetwork I A C) :
    FMPolicy F I := fun D s =>
  if h : ∃ t a, (rest tn D).Unconstrained t ∧ (rest tn D).α t = Sum.inl a ∧
      (P.δ a).Applicable s ∧ ∀ s' ∈ (P.δ a).outcomes s, P.BeliefSolvable ((rest tn D).progress t) s'
  then some h.choose else none

/-- A solvable belief state yields a strong OD policy. -/
theorem strongOD_of_beliefSolvable {tn : HTN.TaskNetwork I A C}
    (h : P.BeliefSolvable tn P.init) : P.StrongOD tn (beliefPolicy P tn) := by
  classical
  have inv : ∀ c, P.FMReach tn (beliefPolicy P tn) c →
      P.BeliefSolvable (rest tn c.done) c.state := by
    intro c hc
    induction hc with
    | refl => exact BeliefSolvable.congr P h (sameOn_rest_empty tn)
    | @tail c c' _ hstep _ =>
      obtain ⟨t, a, ⟨hπ, -, -, -, hα, -⟩, s', hs', rfl⟩ := hstep
      simp only [beliefPolicy] at hπ
      split_ifs at hπ with hex
      cases hπ
      obtain ⟨a', -, hα', -, hall⟩ := hex.choose_spec
      have : a' = a := Sum.inl_injective (hα'.symm.trans hα)
      subst this
      simpa [rest_progress] using hall s' hs'
  intro c hc
  have hsub := fmReach_done_subset hc
  by_cases hemp : tn.T \ c.done = ∅
  · left
    exact Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.1 hemp)
  · right
    have hbs := inv c hc
    have hex : ∃ t a, (rest tn c.done).Unconstrained t ∧ (rest tn c.done).α t = Sum.inl a ∧
        (P.δ a).Applicable c.state ∧ ∀ s' ∈ (P.δ a).outcomes c.state,
          P.BeliefSolvable ((rest tn c.done).progress t) s' := by
      cases hbs with
      | empty h => exact absurd h hemp
      | step hu hα happ hall => exact ⟨_, _, hu, hα, happ, hall⟩
    obtain ⟨a, hu, hα, happ, -⟩ := hex.choose_spec
    refine ⟨hex.choose, a, ?_, (Finset.mem_sdiff.1 hu.1).1, (Finset.mem_sdiff.1 hu.1).2,
      fun t' ht' hord => ?_, hα, happ⟩
    · simp only [beliefPolicy, dif_pos hex]
    · by_contra hnd
      exact hu.2 t' (Finset.mem_sdiff.2 ⟨ht', hnd⟩) ⟨hord, hnd⟩

/-- **Strong OD solutions [CB21] = solvable belief states [DB25].** -/
theorem strongOD_iff_beliefSolvable (tn : HTN.TaskNetwork I A C) :
    (∃ π, P.StrongOD tn π) ↔ P.BeliefSolvable tn P.init :=
  ⟨fun ⟨_, h⟩ => beliefSolvable_of_strongOD h, fun h => ⟨_, strongOD_of_beliefSolvable h⟩⟩

/-- Strong fixed-method plan existence: [CB21] and [DB25] agree. -/
theorem strongODSolvable_iff_fmSolvableDB : P.StrongODSolvable ↔ P.FMSolvableDB := by
  constructor
  · rintro ⟨tn, π, hach, hπ⟩
    exact ⟨tn, hach, beliefSolvable_of_strongOD hπ⟩
  · rintro ⟨tn, hach, h⟩
    exact ⟨tn, _, hach, strongOD_of_beliefSolvable h⟩

end Problem

end FOND
