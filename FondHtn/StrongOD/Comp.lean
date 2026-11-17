import FondHtn.StrongOD.Dec
/-!
# Solvable belief states with prescribed leaves, and sequential composition

`FOND.SOD.BSW P W tn s` — the belief state `(tn, s)` is solvable *with all leaf states in `W`*:
as `FOND.Problem.BeliefSolvable`, but the empty network is solved only in a state of `W`.  With
`W = univ` this is `BeliefSolvable` (`FOND.SOD.bsw_univ_iff`).

**Sequential composition** (`FOND.SOD.bsw_comp`): if every task of `X ⊆ T` precedes every task
outside `X` (and no task outside `X` precedes one in `X`), then `tn` is solvable from `s` with
leaves in `W` iff the part `X` is solvable from `s` with all its leaves `s'` such that the rest
`T ∖ X` is solvable from `s'` with leaves in `W`.
-/

namespace FOND

open HTN

namespace SOD

set_option linter.unusedSectionVars false

variable {F A C I : Type} [DecidableEq I] (P : Problem F A C I)

/-- **Solvable belief states with leaves in `W`.** -/
inductive BSW (W : Set (Set F)) : TaskNetwork I A C → Set F → Prop
  | empty {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) (hs : s ∈ W) : BSW W tn s
  | step {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, BSW W (tn.progress t) s') : BSW W tn s

variable {P}

theorem BSW.mono {W W' : Set (Set F)} (hW : W ⊆ W') {tn : TaskNetwork I A C} {s : Set F}
    (h : BSW P W tn s) : BSW P W' tn s := by
  induction h with
  | empty h hs => exact .empty h (hW hs)
  | step hu hα happ _ ih => exact .step hu hα happ ih

theorem BSW.congr {W : Set (Set F)} {tn : TaskNetwork I A C} {s : Set F} (h : BSW P W tn s) :
    ∀ {tn'}, FOND.TaskNetwork.SameOn tn tn' → BSW P W tn' s := by
  induction h with
  | empty h hs => exact fun hS => .empty (hS.1 ▸ h) hs
  | @step tn s t a hu hα happ _ ih =>
    intro tn' hS
    exact .step (hS.unconstrained hu) ((hS.2.2 t hu.1).symm.trans hα) happ
      fun s' hs' => ih s' hs' (hS.progress t)

theorem BSW.isoVia {W : Set (Set F)} {tn : TaskNetwork I A C} {s : Set F} (h : BSW P W tn s) :
    ∀ {σ : I → I} {tn'}, HTN.TaskNetwork.IsoVia σ tn tn' → BSW P W tn' s := by
  induction h with
  | empty he hs => exact fun hσ => .empty (hσ.empty he) hs
  | step hu hα happ _ ih =>
    intro σ tn' hσ
    exact .step (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ
      fun s' hs' => ih s' hs' (hσ.progress hu.1)

theorem bsw_univ_iff {tn : TaskNetwork I A C} {s : Set F} :
    BSW P Set.univ tn s ↔ P.BeliefSolvable tn s := by
  constructor
  · intro h
    induction h with
    | empty h _ => exact .empty h
    | step hu hα happ _ ih => exact .step hu hα happ ih
  · intro h
    induction h with
    | empty h => exact .empty h trivial
    | step hu hα happ _ ih => exact .step hu hα happ ih

theorem sameOn_symm {tn tn' : TaskNetwork I A C} (h : FOND.TaskNetwork.SameOn tn tn') :
    FOND.TaskNetwork.SameOn tn' tn := by
  obtain ⟨hT, ho, hα⟩ := h
  exact ⟨hT.symm, fun a ha b hb => (ho a (hT ▸ ha) b (hT ▸ hb)).symm,
    fun a ha => (hα a (hT ▸ ha)).symm⟩

theorem sameOn_refl (tn : TaskNetwork I A C) : FOND.TaskNetwork.SameOn tn tn :=
  ⟨rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

/-! ## Sub-networks and prefixes -/

/-- The sub-network on the tasks `X`. -/
def sub (tn : TaskNetwork I A C) (X : Finset I) : TaskNetwork I A C where
  T := X
  ord := tn.ord
  α := tn.α

/-- `X` is a **prefix** of `tn`: its tasks precede all other tasks, and no other task precedes
one of them. -/
def Prefix (tn : TaskNetwork I A C) (X : Finset I) : Prop :=
  X ⊆ tn.T ∧ ∀ a ∈ X, ∀ b ∈ tn.T, b ∉ X → tn.ord a b ∧ ¬ tn.ord b a

theorem Prefix.progress {tn : TaskNetwork I A C} {X : Finset I} (h : Prefix tn X) {t : I}
    (_ht : t ∈ X) : Prefix (tn.progress t) (X.erase t) := by
  refine ⟨fun y hy => ?_, fun a ha b hb hbX => ?_⟩
  · rw [Finset.mem_erase] at hy
    exact Finset.mem_erase.2 ⟨hy.1, h.1 hy.2⟩
  · rw [Finset.mem_erase] at ha
    rw [HTN.TaskNetwork.progress_T, Finset.mem_erase] at hb
    have hbX' : b ∉ X := fun h' => hbX (Finset.mem_erase.2 ⟨hb.1, h'⟩)
    obtain ⟨h1, h2⟩ := h.2 a ha.2 b hb.2 hbX'
    simp only [HTN.TaskNetwork.progress_ord]
    exact ⟨⟨h1, ha.1⟩, fun h3 => h2 h3.1⟩

theorem sameOn_sub_rest {tn : TaskNetwork I A C} {X : Finset I} {t : I} (ht : t ∈ X) :
    FOND.TaskNetwork.SameOn (sub (tn.progress t) ((tn.progress t).T \ X.erase t))
      (sub tn (tn.T \ X)) := by
  have hT : (tn.progress t).T \ X.erase t = tn.T \ X := by
    ext y
    simp only [HTN.TaskNetwork.progress_T, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, fun h => h3 ⟨h1, h⟩⟩
    · rintro ⟨h2, h3⟩
      exact ⟨⟨fun e => h3 (e ▸ ht), h2⟩, fun h => h3 h.2⟩
  refine ⟨hT, fun a ha b _ => ?_, fun _ _ => rfl⟩
  have ha' : a ∈ tn.T \ X := hT ▸ ha
  have hat : a ≠ t := fun e => (Finset.mem_sdiff.1 ha').2 (e ▸ ht)
  simp only [sub, HTN.TaskNetwork.progress_ord]
  exact ⟨fun h => h.1, fun h => ⟨h, hat⟩⟩

theorem sameOn_sub_empty (tn : TaskNetwork I A C) :
    FOND.TaskNetwork.SameOn tn (sub tn (tn.T \ ∅)) :=
  ⟨by simp [sub], fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

/-- **Sequential composition of solvable belief states.** -/
theorem bsw_comp {W : Set (Set F)} {tn : TaskNetwork I A C} {X : Finset I} (hX : Prefix tn X)
    {s : Set F} : BSW P W tn s ↔
      BSW P {s' | BSW P W (sub tn (tn.T \ X)) s'} (sub tn X) s := by
  constructor
  · intro h
    induction h generalizing X with
    | empty h hs =>
      have hX0 : X = ∅ := Finset.subset_empty.1 (h ▸ hX.1)
      subst hX0
      exact .empty rfl (.empty (by simp [sub, h]) hs)
    | @step tn s t a hu hα happ hall ih =>
      by_cases hX0 : X = ∅
      · subst hX0
        exact .empty rfl ((BSW.step hu hα happ hall).congr (sameOn_sub_empty tn))
      have htX : t ∈ X := by
        by_contra htX
        obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hX0
        exact hu.2 b (hX.1 hb) (hX.2 b hb t hu.1 htX).1
      refine .step (t := t) ⟨htX, fun t' ht' => hu.2 t' (hX.1 ht')⟩ hα happ fun s' hs' => ?_
      have := ih s' hs' (hX.progress htX)
      refine BSW.mono (fun r hr => ?_) this
      exact BSW.congr hr (sameOn_sub_rest htX)
  · intro h
    suffices key : ∀ {W' : Set (Set F)} {u : TaskNetwork I A C} {s : Set F}, BSW P W' u s →
        ∀ (tn : TaskNetwork I A C) (X : Finset I), FOND.TaskNetwork.SameOn u (sub tn X) →
          Prefix tn X → (∀ r ∈ W', BSW P W (sub tn (tn.T \ X)) r) → BSW P W tn s from
      key h tn X (sameOn_refl _) hX fun r hr => hr
    intro W' u s hb
    induction hb with
    | empty he hs =>
      intro tn X hS hX hW
      have hX0 : X = ∅ := by have := hS.1; simp only [sub] at this; rw [← this, he]
      subst hX0
      exact (hW _ hs).congr (sameOn_symm (sameOn_sub_empty tn))
    | @step u s t a hu hα happ _ ih =>
      intro tn X hS hX hW
      have hu' := hS.unconstrained hu
      have htX : t ∈ X := hu'.1
      refine .step (t := t) ⟨hX.1 htX, fun t' ht' hord => ?_⟩ ((hS.2.2 t hu.1).symm.trans hα)
        happ fun s' hs' => ?_
      · by_cases ht'X : t' ∈ X
        · exact hu'.2 t' ht'X hord
        · exact (hX.2 t htX t' ht' ht'X).2 hord
      · exact ih s' hs' (tn.progress t) (X.erase t) (hS.progress t) (hX.progress htX)
          fun r hr => (hW r hr).congr (sameOn_symm (sameOn_sub_rest htX))

end SOD

end FOND
