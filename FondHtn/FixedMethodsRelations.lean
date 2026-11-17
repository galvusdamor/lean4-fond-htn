import FondHtn.FixedMethodsLemmas
import FondHtn.MethodPolicies
/-!
# Fixed methods: relations between the solution criteria [CB21, Props. 2.12, 2.13, 2.15]

* **Prop. 2.12** (`FOND.Problem.weakLD_iff_weakOD`, `weakLDSolvable_iff_weakODSolvable`): a
  primitive task network has a weak LD solution iff it has a weak OD solution.
* **Prop. 2.13**, first half (`FOND.Problem.strongOD_of_strongLD`,
  `strongODSolvable_of_strongLDSolvable`): a strong LD solution yields a strong OD solution.  The
  second half (the converse fails) is `FOND.Examples.prop_2_13_converse_fails` in
  `FondHtn.Examples`.
* **Prop. 2.15** (`FOND.Problem.strongLD_iff_strongOD_of_totallyOrdered`,
  `strongLDSolvable_iff_strongODSolvable`): for totally ordered problems the two strong criteria
  coincide.

The proofs go through the belief-state characterisations: `BeliefSolvable` for the strong and its
weak analogue `WeakBelief` for the weak criteria.
-/

namespace FOND

open HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ## Linearisations and progression -/

namespace TaskNetwork

variable [DecidableEq I]

omit [DecidableEq I] in
lemma isLinearization_nil {tn : HTN.TaskNetwork I A C} : tn.IsLinearization [] ↔ tn.T = ∅ := by
  simp only [HTN.TaskNetwork.IsLinearization, List.nodup_nil, List.not_mem_nil, false_iff,
    List.Pairwise.nil, and_true, true_and]
  exact ⟨fun h => Finset.eq_empty_of_forall_notMem h, fun h t => by simp [h]⟩

lemma isLinearization_cons_of {tn : HTN.TaskNetwork I A C} {t : I} {l : List I}
    (hu : tn.Unconstrained t) (hl : (tn.progress t).IsLinearization l) :
    tn.IsLinearization (t :: l) := by
  obtain ⟨hnd, hmem, hpw⟩ := hl
  have htl : t ∉ l := fun h => ((HTN.TaskNetwork.mem_progress_T.1 ((hmem t).1 h)).1 rfl)
  refine ⟨List.nodup_cons.2 ⟨htl, hnd⟩, fun y => ?_, List.pairwise_cons.2 ⟨?_, ?_⟩⟩
  · simp only [List.mem_cons, hmem, HTN.TaskNetwork.mem_progress_T]
    constructor
    · rintro (rfl | ⟨-, h⟩)
      · exact hu.1
      · exact h
    · intro h
      by_cases hyt : y = t
      · exact Or.inl hyt
      · exact Or.inr ⟨hyt, h⟩
  · intro y hy hord
    exact hu.2 y (HTN.TaskNetwork.mem_progress_T.1 ((hmem y).1 hy)).2 hord
  · refine hpw.imp_of_mem fun {a b} _ hb h hord => h ⟨hord, ?_⟩
    exact (HTN.TaskNetwork.mem_progress_T.1 ((hmem b).1 hb)).1

lemma of_isLinearization_cons {tn : HTN.TaskNetwork I A C} (hirr : ∀ a, ¬ tn.ord a a) {t : I}
    {l : List I} (hl : tn.IsLinearization (t :: l)) :
    tn.Unconstrained t ∧ (tn.progress t).IsLinearization l := by
  obtain ⟨hnd, hmem, hpw⟩ := hl
  obtain ⟨htl, hnd⟩ := List.nodup_cons.1 hnd
  obtain ⟨hhead, hpw⟩ := List.pairwise_cons.1 hpw
  refine ⟨⟨(hmem t).1 (List.mem_cons_self), fun t' ht' hord => ?_⟩, hnd, fun y => ?_, ?_⟩
  · by_cases h : t' = t
    · subst h; exact hirr _ hord
    · have : t' ∈ l := by
        rcases List.mem_cons.1 ((hmem t').2 ht') with h' | h'
        · exact absurd h' h
        · exact h'
      exact hhead t' this hord
  · rw [HTN.TaskNetwork.mem_progress_T, ← hmem, List.mem_cons]
    constructor
    · intro h; exact ⟨fun e => htl (e ▸ h), Or.inr h⟩
    · rintro ⟨hne, rfl | h⟩
      · exact absurd rfl hne
      · exact h
  · exact hpw.imp fun h hord => h hord.1

/-- Irreflexivity is preserved by progression. -/
lemma irrefl_progress {tn : HTN.TaskNetwork I A C} (hirr : ∀ a, ¬ tn.ord a a) (t : I) :
    ∀ a, ¬ (tn.progress t).ord a a := fun a h => hirr a h.1

omit [DecidableEq I] in
lemma isActionSeq_nil {tn : HTN.TaskNetwork I A C} : tn.IsActionSeq [] [] := rfl

lemma isActionSeq_cons {tn : HTN.TaskNetwork I A C} {t : I} {l : List I} {as : List A} :
    tn.IsActionSeq (t :: l) as ↔
      ∃ a as', as = a :: as' ∧ tn.α t = Sum.inl a ∧ (tn.progress t).IsActionSeq l as' := by
  unfold HTN.TaskNetwork.IsActionSeq
  cases as with
  | nil => simp
  | cons b bs =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨b, bs, ⟨rfl, rfl⟩, h1, h2⟩
    · rintro ⟨c, cs, ⟨rfl, rfl⟩, h1, h2⟩
      exact ⟨h1, h2⟩

end TaskNetwork

namespace Problem

open FOND.TaskNetwork

variable (P : Problem F A C I) [DecidableEq I]

/-! ## Weak belief states -/

/-- The weak analogue of `BeliefSolvable`: `tn` is empty, or some unconstrained primitive task is
applicable and *some* outcome leads to a weakly solvable pair. -/
inductive WeakBelief : HTN.TaskNetwork I A C → Set F → Prop
  /-- The empty task network is solved. -/
  | empty {tn : HTN.TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) : WeakBelief tn s
  /-- Execute an unconstrained applicable primitive task; some outcome must be solvable. -/
  | step {tn : HTN.TaskNetwork I A C} {s s' : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s) (hs' : s' ∈ (P.δ a).outcomes s)
      (h : WeakBelief (tn.progress t) s') : WeakBelief tn s

variable {P}

lemma WeakBelief.congr {tn : HTN.TaskNetwork I A C} {s : Set F}
    (h : P.WeakBelief tn s) : ∀ {tn'}, SameOn tn tn' → P.WeakBelief tn' s := by
  induction h with
  | empty h => exact fun hs => .empty (hs.1 ▸ h)
  | @step tn s s' t a hu hα happ hs' _ ih =>
    intro tn' hs
    exact .step (hs.unconstrained hu) ((hs.2.2 t hu.1).symm.trans hα) happ hs' (ih (hs.progress t))

/-! ### Weak LD solutions are weak belief states -/

theorem weakBelief_of_weakExec {l : List I} :
    ∀ {tn : HTN.TaskNetwork I A C} {s : Set F} {as : List A}, (∀ a, ¬ tn.ord a a) →
      tn.IsLinearization l → tn.IsActionSeq l as → P.WeakExec as s → P.WeakBelief tn s := by
  induction l with
  | nil => exact fun _ hl _ _ => .empty (isLinearization_nil.1 hl)
  | cons t l ih =>
    intro tn s as hirr hl has hex
    obtain ⟨hu, hl'⟩ := of_isLinearization_cons hirr hl
    obtain ⟨a, as', rfl, hα, has'⟩ := isActionSeq_cons.1 has
    obtain ⟨happ, s', hs', hex'⟩ := hex
    exact .step hu hα happ hs' (ih (irrefl_progress hirr t) hl' has' hex')

theorem weakExec_of_weakBelief {tn : HTN.TaskNetwork I A C} {s : Set F}
    (h : P.WeakBelief tn s) :
    ∃ l as, tn.IsLinearization l ∧ tn.IsActionSeq l as ∧ P.WeakExec as s := by
  induction h with
  | empty h => exact ⟨[], [], isLinearization_nil.2 h, isActionSeq_nil, trivial⟩
  | @step tn s s' t a hu hα happ hs' _ ih =>
    obtain ⟨l, as, hl, has, hex⟩ := ih
    exact ⟨t :: l, a :: as, isLinearization_cons_of hu hl,
      isActionSeq_cons.2 ⟨a, as, rfl, hα, has⟩, happ, s', hs', hex⟩

/-! ### Weak OD solutions are weak belief states -/

theorem weakBelief_of_weakOD {tn : HTN.TaskNetwork I A C} {π : FMPolicy F I}
    (h : P.WeakOD tn π) : P.WeakBelief tn P.init := by
  obtain ⟨c₁, hreach, hc₁⟩ := h
  have key : ∀ c, Relation.ReflTransGen (P.FMStep tn π) c c₁ →
      P.WeakBelief (rest tn c.done) c.state := by
    intro c hc
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have : c₁.done = tn.T := hc₁
      exact .empty (by simp [rest, this])
    | head hstep _ ih =>
      obtain ⟨t, a, ⟨-, htT, htD, hpred, hα, happ⟩, s', hs', rfl⟩ := hstep
      refine .step (t := t) ⟨by simp [rest, htT, htD], ?_⟩ hα happ hs' (by rwa [rest_progress])
      rintro t' ht' ⟨hord, hnd⟩
      exact hnd (hpred t' (Finset.mem_sdiff.1 ht').1 hord)
  exact WeakBelief.congr (key _ hreach) (by
    refine ⟨by simp [rest], fun a _ b _ => by simp [rest], fun _ _ => rfl⟩)

open Classical in
/-- The policy read off a weak belief state. -/
noncomputable def weakBeliefPolicy (P : Problem F A C I) (tn : HTN.TaskNetwork I A C) :
    FMPolicy F I := fun D s =>
  if h : ∃ t a, (rest tn D).Unconstrained t ∧ (rest tn D).α t = Sum.inl a ∧
      (P.δ a).Applicable s ∧ ∃ s' ∈ (P.δ a).outcomes s, P.WeakBelief ((rest tn D).progress t) s'
  then some h.choose else none

theorem weakOD_of_weakBelief {tn : HTN.TaskNetwork I A C} (h : P.WeakBelief tn P.init) :
    P.WeakOD tn (weakBeliefPolicy P tn) := by
  classical
  suffices key : ∀ n, ∀ c : FMConfig F I, (tn.T \ c.done).card = n → c.done ⊆ tn.T →
      P.WeakBelief (rest tn c.done) c.state →
      ∃ c', Relation.ReflTransGen (P.FMStep tn (weakBeliefPolicy P tn)) c c' ∧
        FMComplete tn c' by
    exact key _ ⟨∅, P.init⟩ rfl (Finset.empty_subset _)
      (WeakBelief.congr h (sameOn_rest_empty tn))
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hn hsub hwb
    by_cases hemp : tn.T \ c.done = ∅
    · exact ⟨c, .refl, Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.1 hemp)⟩
    · have hex : ∃ t a, (rest tn c.done).Unconstrained t ∧ (rest tn c.done).α t = Sum.inl a ∧
          (P.δ a).Applicable c.state ∧ ∃ s' ∈ (P.δ a).outcomes c.state,
            P.WeakBelief ((rest tn c.done).progress t) s' := by
        cases hwb with
        | empty h => exact absurd h hemp
        | step hu hα happ hs' h => exact ⟨_, _, hu, hα, happ, _, hs', h⟩
      obtain ⟨a, hu, hα, happ, s', hs', hwb'⟩ := hex.choose_spec
      set t := hex.choose
      have htT := (Finset.mem_sdiff.1 hu.1).1
      have htD := (Finset.mem_sdiff.1 hu.1).2
      have hstep : P.FMStep tn (weakBeliefPolicy P tn) c ⟨insert t c.done, s'⟩ := by
        refine ⟨t, a, ⟨?_, htT, htD, fun t' ht' hord => ?_, hα, happ⟩, s', hs', rfl⟩
        · simp only [weakBeliefPolicy, dif_pos hex]; rfl
        · by_contra hnd
          exact hu.2 t' (Finset.mem_sdiff.2 ⟨ht', hnd⟩) ⟨hord, hnd⟩
      obtain ⟨c', hc', hcomp⟩ := ih _ (by
          rw [← hn]
          apply Finset.card_lt_card
          refine ⟨Finset.sdiff_subset_sdiff (subset_refl _) (Finset.subset_insert _ _),
            fun hs => ?_⟩
          simpa using hs (Finset.mem_sdiff.2 ⟨htT, htD⟩))
        ⟨insert t c.done, s'⟩ rfl (Finset.insert_subset htT hsub) (by rwa [← rest_progress])
      exact ⟨c', .head hstep hc', hcomp⟩

/-! ## Prop. 2.12: weak LD = weak OD -/

theorem weakLD_iff_weakOD {tn : HTN.TaskNetwork I A C} (hirr : ∀ a, ¬ tn.ord a a) :
    (∃ l, P.IsWeakLDSolution tn l) ↔ ∃ π, P.IsWeakODSolution tn π := by
  constructor
  · rintro ⟨l, hach, hl, as, has, hex⟩
    exact ⟨_, hach, weakOD_of_weakBelief (weakBelief_of_weakExec hirr hl has hex)⟩
  · rintro ⟨π, hach, hπ⟩
    obtain ⟨l, as, hl, has, hex⟩ := weakExec_of_weakBelief (weakBelief_of_weakOD hπ)
    exact ⟨l, hach, hl, as, has, hex⟩

lemma AchievablePrimitive.wf (hP : P.tnI.WF) {tn : HTN.TaskNetwork I A C}
    (h : P.AchievablePrimitive tn) : tn.WF :=
  HTN.DecomposesTo.wf h.1 hP

/-- **[CB21, Prop. 2.12].** -/
theorem weakLDSolvable_iff_weakODSolvable (hP : P.tnI.WF) :
    P.WeakLDSolvable ↔ P.WeakODSolvable := by
  constructor
  · rintro ⟨tn, l, h⟩
    obtain ⟨π, hπ⟩ := (weakLD_iff_weakOD (h.1.wf hP).irrefl).1 ⟨l, h⟩
    exact ⟨tn, π, hπ⟩
  · rintro ⟨tn, π, h⟩
    obtain ⟨l, hl⟩ := (weakLD_iff_weakOD (h.1.wf hP).irrefl).2 ⟨π, h⟩
    exact ⟨tn, l, hl⟩

/-! ## Prop. 2.13: strong LD ⟹ strong OD -/

theorem beliefSolvable_of_strongExec {l : List I} :
    ∀ {tn : HTN.TaskNetwork I A C} {S : Set (Set F)} {as : List A}, (∀ a, ¬ tn.ord a a) →
      tn.IsLinearization l → tn.IsActionSeq l as → P.StrongExec as S →
      ∀ s ∈ S, P.BeliefSolvable tn s := by
  induction l with
  | nil => exact fun _ hl _ _ _ _ => .empty (isLinearization_nil.1 hl)
  | cons t l ih =>
    intro tn S as hirr hl has hex s hs
    obtain ⟨hu, hl'⟩ := of_isLinearization_cons hirr hl
    obtain ⟨a, as', rfl, hα, has'⟩ := isActionSeq_cons.1 has
    obtain ⟨happ, hex'⟩ := hex
    exact .step hu hα (happ s hs) fun s' hs' =>
      ih (irrefl_progress hirr t) hl' has' hex' s' ⟨s, hs, hs'⟩

theorem strongOD_of_strongLD {tn : HTN.TaskNetwork I A C} (hirr : ∀ a, ¬ tn.ord a a)
    {l : List I} (h : P.IsStrongLDSolution tn l) : ∃ π, P.IsStrongODSolution tn π := by
  obtain ⟨hach, hl, as, has, hex⟩ := h
  exact ⟨_, hach, strongOD_of_beliefSolvable
    (beliefSolvable_of_strongExec hirr hl has hex P.init rfl)⟩

/-- **[CB21, Prop. 2.13], first half.** -/
theorem strongODSolvable_of_strongLDSolvable (hP : P.tnI.WF) (h : P.StrongLDSolvable) :
    P.StrongODSolvable := by
  obtain ⟨tn, l, hl⟩ := h
  obtain ⟨π, hπ⟩ := strongOD_of_strongLD (hl.1.wf hP).irrefl hl
  exact ⟨tn, π, hπ⟩

/-! ## Prop. 2.15: totally ordered problems -/

lemma unconstrained_unique {tn : HTN.TaskNetwork I A C} (hto : tn.IsTotallyOrdered)
    {t t' : I} (ht : tn.Unconstrained t) (ht' : tn.Unconstrained t') : t = t' := by
  by_contra hne
  rcases hto t ht.1 t' ht'.1 hne with h | h
  · exact ht'.2 t ht.1 h
  · exact ht.2 t' ht'.1 h

lemma isTotallyOrdered_progress {tn : HTN.TaskNetwork I A C} (hto : tn.IsTotallyOrdered)
    (t : I) : (tn.progress t).IsTotallyOrdered := by
  intro a ha b hb hne
  rw [HTN.TaskNetwork.mem_progress_T] at ha hb
  rcases hto a ha.2 b hb.2 hne with h | h
  · exact Or.inl ⟨h, ha.1⟩
  · exact Or.inr ⟨h, hb.1⟩

theorem strongExec_of_beliefSolvable_TO :
    ∀ (n : ℕ) {tn : HTN.TaskNetwork I A C}, tn.T.card = n → tn.WF → tn.IsTotallyOrdered →
      tn.IsPrimitive → ∀ S : Set (Set F), (∀ s ∈ S, P.BeliefSolvable tn s) →
      ∃ l as, tn.IsLinearization l ∧ tn.IsActionSeq l as ∧ P.StrongExec as S := by
  intro n
  induction n with
  | zero =>
    intro tn hn _ _ _ S _
    exact ⟨[], [], isLinearization_nil.2 (Finset.card_eq_zero.1 hn), isActionSeq_nil, trivial⟩
  | succ n ih =>
    intro tn hn hwf hto hprim S hS
    have hne : tn.T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨t, htT, hmin⟩ := HTN.TaskNetwork.exists_minimal_of_finset hwf.irrefl hwf.trans _ hne
    have hu : tn.Unconstrained t := ⟨htT, hmin⟩
    obtain ⟨a, hα⟩ := hprim t htT
    have hS' : ∀ s ∈ S, (P.δ a).Applicable s ∧
        ∀ s' ∈ (P.δ a).outcomes s, P.BeliefSolvable (tn.progress t) s' := by
      intro s hs
      cases hS s hs with
      | empty h => simp [h] at htT
      | @step _ _ t' a' hu' hα' happ hall =>
        obtain rfl := unconstrained_unique hto hu hu'
        obtain rfl : a = a' := Sum.inl_injective (hα.symm.trans hα')
        exact ⟨happ, hall⟩
    obtain ⟨l, as, hl, has, hex⟩ := ih (tn := tn.progress t)
      (by rw [HTN.TaskNetwork.progress_T, Finset.card_erase_of_mem htT]; omega)
      (HTN.TaskNetwork.progress_wf hwf hu) (isTotallyOrdered_progress hto t) (hprim.progress t)
      {s' | ∃ s ∈ S, s' ∈ (P.δ a).outcomes s}
      (by rintro s' ⟨s, hs, hs'⟩; exact (hS' s hs).2 s' hs')
    exact ⟨t :: l, a :: as, isLinearization_cons_of hu hl,
      isActionSeq_cons.2 ⟨a, as, rfl, hα, has⟩, fun s hs => (hS' s hs).1, hex⟩

/-- **[CB21, Prop. 2.15]** for a single task network. -/
theorem strongLD_iff_strongOD_of_totallyOrdered {tn : HTN.TaskNetwork I A C} (hwf : tn.WF)
    (hto : tn.IsTotallyOrdered) :
    (∃ l, P.IsStrongLDSolution tn l) ↔ ∃ π, P.IsStrongODSolution tn π := by
  constructor
  · rintro ⟨l, hl⟩
    exact strongOD_of_strongLD hwf.irrefl hl
  · rintro ⟨π, hach, hπ⟩
    obtain ⟨l, as, hl, has, hex⟩ := strongExec_of_beliefSolvable_TO _ rfl hwf hto hach.2 {P.init}
      (by rintro s rfl; exact beliefSolvable_of_strongOD hπ)
    exact ⟨l, hach, hl, as, has, hex⟩

/-! ### Total order is preserved by decomposition -/

omit [DecidableEq I] in
lemma isTotallyOrdered_of_isoVia {tn tn' : HTN.TaskNetwork I A C} {σ : I → I}
    (h : HTN.TaskNetwork.IsoVia σ tn tn') (hto : tn'.IsTotallyOrdered) : tn.IsTotallyOrdered := by
  obtain ⟨hbij, hord, -⟩ := h
  intro a ha b hb hne
  have hσ : σ a ≠ σ b := fun e => hne (hbij.injOn (by simpa using ha) (by simpa using hb) e)
  rcases hto (σ a) (by simpa using hbij.mapsTo (by simpa using ha))
      (σ b) (by simpa using hbij.mapsTo (by simpa using hb)) hσ with h | h
  · exact Or.inl ((hord a ha b hb).2 h)
  · exact Or.inr ((hord b hb a ha).2 h)

/-- Every network reachable by decomposition in a totally ordered problem is totally ordered
(and its compound tasks carry reachable names). -/
theorem decomposesTo_isTotallyOrdered (hto : P.IsTotallyOrdered) (hwf : P.tnI.WF)
    {tn : HTN.TaskNetwork I A C} (h : P.DecomposesTo P.tnI tn) :
    tn.IsTotallyOrdered ∧ ∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → P.skeleton.ReachableName c := by
  have hwf' := HTN.DecomposesTo.wf h hwf
  induction h with
  | refl => exact ⟨hto.1, fun t ht c hc => .tnI ht hc⟩
  | @tail tn₁ tn₂ h₁ hstep ih =>
    obtain ⟨ih1, ih2⟩ := ih (HTN.DecomposesTo.wf h₁ hwf)
    have hw₁ := HTN.DecomposesTo.wf h₁ hwf
    obtain ⟨t, m, hm, htT, hαt, tn', hw', hiso, hdisj, rfl⟩ := hstep
    have hr : P.skeleton.ReachableName m.abstractTask := ih2 t htT _ hαt
    have hrm : P.skeleton.ReachableMethod m := ⟨hm, hr⟩
    obtain ⟨σ, hσ⟩ := hiso
    have hto' : tn'.IsTotallyOrdered := isTotallyOrdered_of_isoVia hσ (hto.2 m hrm)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hne
      rcases HTN.mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx'
      · rcases HTN.mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy'
        · rcases ih1 x hx₁ y hy₁ hne with h | h
          · exact Or.inl ((HTN.decomposeWith_ord_old_old hw' hdisj hx₁ hxt hy₁ hyt).2 h)
          · exact Or.inr ((HTN.decomposeWith_ord_old_old hw' hdisj hy₁ hyt hx₁ hxt).2 h)
        · rcases ih1 x hx₁ t htT hxt with h | h
          · exact Or.inl ((HTN.decomposeWith_ord_old_new hw₁ hw' hdisj hx₁ hy').2 h)
          · exact Or.inr ((HTN.decomposeWith_ord_new_old hw₁ hw' hdisj hy' hx₁).2 h)
      · rcases HTN.mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy'
        · rcases ih1 y hy₁ t htT hyt with h | h
          · exact Or.inr ((HTN.decomposeWith_ord_old_new hw₁ hw' hdisj hy₁ hx').2 h)
          · exact Or.inl ((HTN.decomposeWith_ord_new_old hw₁ hw' hdisj hx' hy₁).2 h)
        · rcases hto' x hx' y hy' hne with h | h
          · exact Or.inl ((HTN.decomposeWith_ord_new_new hw₁ hdisj hx' hy').2 h)
          · exact Or.inr ((HTN.decomposeWith_ord_new_new hw₁ hdisj hy' hx').2 h)
    · intro x hx c hc
      rw [HTN.decomposeWith_α] at hc
      by_cases hxu : x ∈ tn'.T
      · rw [if_pos hxu, hσ.2.2 x hxu] at hc
        exact .method hm hr (by simpa using hσ.1.mapsTo (by simpa using hxu)) hc
      · rw [if_neg hxu] at hc
        rcases HTN.mem_decomposeWith_T.1 hx with ⟨hx₁, -⟩ | hx'
        · exact ih2 x hx₁ c hc
        · exact absurd hx' hxu

/-- **[CB21, Prop. 2.15].**  For totally ordered problems, strong LD and strong OD plan
existence coincide. -/
theorem strongLDSolvable_iff_strongODSolvable (hto : P.IsTotallyOrdered) (hwf : P.tnI.WF) :
    P.StrongLDSolvable ↔ P.StrongODSolvable := by
  constructor
  · exact strongODSolvable_of_strongLDSolvable hwf
  · rintro ⟨tn, π, hπ⟩
    obtain ⟨l, hl⟩ := (strongLD_iff_strongOD_of_totallyOrdered (hπ.1.wf hwf)
      (decomposesTo_isTotallyOrdered hto hwf hπ.1.1).1).2 ⟨π, hπ⟩
    exact ⟨tn, l, hl⟩

end Problem

end FOND
