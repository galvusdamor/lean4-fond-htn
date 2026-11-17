import FondHtn.FixedMethodsRelations
import HtnPlanning.Article.DTree
/-!
# Strong LD solvability as deterministic plan existence ([CB21, Lemma 4.6], repaired)

[CB21, Lemma 4.6] compiles a FOND HTN problem into a deterministic one whose plans are the
strong LD solutions: the state of the deterministic run is the intersection `⋂ Sᵢ` of the
belief state `Sᵢ` of the FOND run.  This is correct only for **positive** preconditions; a
negative precondition `p ∉ s` has to hold in *every* `s ∈ Sᵢ`, which the intersection cannot
express (catalogue, §3.11 and G10).

**Repair.**  We track the intersection *and the union* of the belief state, on two copies of the
facts (`ι₁`, `ι₂`): an action is applicable in all states of `S` iff its positive precondition is
contained in `⋂ S` and its negative precondition is disjoint from `⋃ S`, and both sets evolve
by STRIPS effects:

    ⋂ Sᵢ₊₁ = (⋂ Sᵢ \ delI) ∪ addI,    addI = ⋂ₑ addₑ,   delI = {f | ∃ e, f ∈ delₑ \ addₑ},
    ⋃ Sᵢ₊₁ = (⋃ Sᵢ \ delU) ∪ addU,    addU = ⋃ₑ addₑ,   delU = ⋂ₑ delₑ.

The task networks and the methods are unchanged; hence **every structural class is preserved
literally**.

* `FOND.Action.strongAct` — the deterministic action;
* `FOND.Problem.strongDet` — the deterministic problem (no goal);
* **`FOND.Problem.strongLDSolvable_iff`** — `P` has a strong LD solution iff `strongDet P` is
  solvable.
-/

namespace FOND

open HTN

variable {F F' A C I : Type}

/-- Two disjoint injective copies of the facts in `F'`. -/
structure FactSplit (F F' : Type) where
  ι₁ : F → F'
  ι₂ : F → F'
  inj₁ : Function.Injective ι₁
  inj₂ : Function.Injective ι₂
  ne : ∀ f g, ι₁ f ≠ ι₂ g

namespace FactSplit

variable (κ : FactSplit F F')

/-- The representation of a belief state by its intersection (copy 1) and union (copy 2). -/
def enc (S : Set (Set F)) : Set F' := κ.ι₁ '' (⋂₀ S) ∪ κ.ι₂ '' (⋃₀ S)

theorem ι₁_mem_enc {S : Set (Set F)} {f : F} : κ.ι₁ f ∈ κ.enc S ↔ ∀ s ∈ S, f ∈ s := by
  simp only [enc, Set.mem_union, κ.inj₁.mem_set_image, Set.mem_sInter]
  constructor
  · rintro (h | ⟨g, -, hg⟩)
    · exact h
    · exact absurd hg.symm (κ.ne f g)
  · exact Or.inl

theorem ι₂_mem_enc {S : Set (Set F)} {f : F} : κ.ι₂ f ∈ κ.enc S ↔ ∃ s ∈ S, f ∈ s := by
  simp only [enc, Set.mem_union, κ.inj₂.mem_set_image, Set.mem_sUnion]
  constructor
  · rintro (⟨g, -, hg⟩ | h)
    · exact absurd hg (κ.ne g f)
    · exact h
  · exact Or.inr

theorem ι₁_mem_ι₂_image {X : Set F} {f : F} : κ.ι₁ f ∉ κ.ι₂ '' X := by
  rintro ⟨g, -, hg⟩; exact κ.ne f g hg.symm

theorem ι₂_mem_ι₁_image {X : Set F} {f : F} : κ.ι₂ f ∉ κ.ι₁ '' X := by
  rintro ⟨g, -, hg⟩; exact κ.ne g f hg

end FactSplit

namespace Action

variable (a : Action F)

/-- Facts added by every effect. -/
def addI : Set F := {f | ∀ e ∈ a.effs, f ∈ e.1}
/-- Facts deleted and not re-added by some effect. -/
def delI : Set F := {f | ∃ e ∈ a.effs, f ∈ e.2 ∧ f ∉ e.1}
/-- Facts added by some effect. -/
def addU : Set F := {f | ∃ e ∈ a.effs, f ∈ e.1}
/-- Facts deleted by every effect. -/
def delU : Set F := {f | ∀ e ∈ a.effs, f ∈ e.2}

/-- **The deterministic action** acting on the representation `enc S` of belief states. -/
def strongAct (κ : FactSplit F F') : HTN.Article.Action F' where
  pre := κ.ι₁ '' a.pre
  preNeg := κ.ι₂ '' a.preNeg
  add := κ.ι₁ '' a.addI ∪ κ.ι₂ '' a.addU
  del := κ.ι₁ '' a.delI ∪ κ.ι₂ '' a.delU

/-- The belief state after `a`. -/
def post (S : Set (Set F)) : Set (Set F) := {s' | ∃ s ∈ S, s' ∈ a.outcomes s}

variable {a} (κ : FactSplit F F')

theorem strongAct_applicable (S : Set (Set F)) :
    (a.strongAct κ).Applicable (κ.enc S) ↔ ∀ s ∈ S, a.Applicable s := by
  constructor
  · rintro ⟨hpre, hneg⟩ s hs
    refine ⟨fun f hf => (κ.ι₁_mem_enc.1 (hpre ⟨f, hf, rfl⟩)) s hs, ?_⟩
    rw [Set.disjoint_left]
    intro f hf hfs
    exact Set.disjoint_left.1 hneg ⟨f, hf, rfl⟩ (κ.ι₂_mem_enc.2 ⟨s, hs, hfs⟩)
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact κ.ι₁_mem_enc.2 fun s hs => (h s hs).1 hf
    · rw [Set.disjoint_left]
      rintro _ ⟨f, hf, rfl⟩ hx
      obtain ⟨s, hs, hfs⟩ := κ.ι₂_mem_enc.1 hx
      exact Set.disjoint_left.1 (h s hs).2 hf hfs

theorem strongAct_apply {S : Set (Set F)} (hS : S.Nonempty) :
    (a.strongAct κ).apply (κ.enc S) = κ.enc (a.post S) := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  ext x
  simp only [HTN.Article.Action.apply, strongAct, Set.mem_union, Set.mem_diff]
  by_cases h1 : ∃ f, x = κ.ι₁ f
  · obtain ⟨f, rfl⟩ := h1
    simp only [κ.inj₁.mem_set_image, κ.ι₁_mem_ι₂_image, or_false, κ.ι₁_mem_enc]
    simp only [post, Set.mem_setOf_eq, forall_exists_index, and_imp, Action.mem_outcomes, addI,
      delI, applyEff]
    constructor
    · rintro (⟨hall, hnd⟩ | hadd) s' s hs e he rfl
      · by_cases hd : f ∈ e.2
        · exact Or.inr (by_contra fun hn => hnd ⟨e, he, hd, hn⟩)
        · exact Or.inl ⟨hall s hs, hd⟩
      · exact Or.inr (hadd e he)
    · intro h
      by_cases hadd : ∀ e ∈ a.effs, f ∈ e.1
      · exact Or.inr hadd
      · push_neg at hadd
        obtain ⟨e₀, he₀, hf₀⟩ := hadd
        refine Or.inl ⟨fun s hs => ?_, ?_⟩
        · rcases h _ s hs e₀ he₀ rfl with h' | h'
          · exact h'.1
          · exact absurd h' hf₀
        · rintro ⟨e, he, hd, hn⟩
          rcases h _ s₀ hs₀ e he rfl with h' | h'
          · exact h'.2 hd
          · exact hn h'
  by_cases h2 : ∃ f, x = κ.ι₂ f
  · obtain ⟨f, rfl⟩ := h2
    simp only [κ.inj₂.mem_set_image, κ.ι₂_mem_ι₁_image, false_or, κ.ι₂_mem_enc]
    simp only [post, Set.mem_setOf_eq, Action.mem_outcomes, addU, delU, applyEff]
    constructor
    · rintro (⟨⟨s, hs, hfs⟩, hnd⟩ | ⟨e, he, hfe⟩)
      · push_neg at hnd
        obtain ⟨e, he, hfe⟩ := hnd
        exact ⟨_, ⟨s, hs, e, he, rfl⟩, Or.inl ⟨hfs, hfe⟩⟩
      · exact ⟨_, ⟨s₀, hs₀, e, he, rfl⟩, Or.inr hfe⟩
    · rintro ⟨_, ⟨s, hs, e, he, rfl⟩, h | h⟩
      · exact Or.inl ⟨⟨s, hs, h.1⟩, fun hall => h.2 (hall e he)⟩
      · exact Or.inr ⟨e, he, h⟩
  · push_neg at h1 h2
    have hn : ∀ S : Set (Set F), x ∉ κ.enc S := by
      rintro S (⟨f, -, hf⟩ | ⟨f, -, hf⟩)
      · exact h1 f hf.symm
      · exact h2 f hf.symm
    have hn1 : ∀ X : Set F, x ∉ κ.ι₁ '' X := fun X ⟨f, _, hf⟩ => h1 f hf.symm
    have hn2 : ∀ X : Set F, x ∉ κ.ι₂ '' X := fun X ⟨f, _, hf⟩ => h2 f hf.symm
    simp only [hn, hn1, hn2, false_and, or_self]

theorem post_nonempty {S : Set (Set F)} (hS : S.Nonempty) (ha : a.WF) : (a.post S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨s', hs'⟩ := outcomes_nonempty ha s
  exact ⟨s', s, hs, hs'⟩

end Action

namespace Problem

variable (κ : FactSplit F F') (P : Problem F A C I)

/-- **The deterministic problem of strong LD solutions**: same methods and initial task network,
actions `strongAct`, initial state `enc {s_I}`, no goal. -/
def strongDet : HTN.Article.Problem F' A C I where
  δ := fun a => (P.δ a).strongAct κ
  methods := P.methods
  init := κ.enc {P.init}
  tnI := P.tnI
  goalPos := ∅
  goalNeg := ∅

variable {κ P}

theorem strongExec_iff_run (hP : ∀ a, (P.δ a).WF) :
    ∀ (as : List A) (S : Set (Set F)), S.Nonempty →
      (P.StrongExec as S ↔ ∃ s', (P.strongDet κ).Run as (κ.enc S) s') := by
  intro as
  induction as with
  | nil => intro S _; simp [StrongExec, HTN.Article.Problem.Run]
  | cons a as ih =>
    intro S hS
    show ((∀ s ∈ S, (P.δ a).Applicable s) ∧ P.StrongExec as ((P.δ a).post S)) ↔
      ∃ s', ((P.δ a).strongAct κ).Applicable (κ.enc S) ∧
        (P.strongDet κ).Run as (((P.δ a).strongAct κ).apply (κ.enc S)) s'
    rw [Action.strongAct_apply κ hS, Action.strongAct_applicable,
      ih _ (Action.post_nonempty hS (hP a))]
    constructor
    · rintro ⟨h1, s', h2⟩; exact ⟨s', h1, h2⟩
    · rintro ⟨s', h1, h2⟩; exact ⟨h1, s', h2⟩

variable [DecidableEq I]

/-- **[CB21, Lemma 4.6], repaired**: strong LD solvability is deterministic plan existence. -/
theorem strongLDSolvable_iff (hP : P.WF) : P.StrongLDSolvable ↔ (P.strongDet κ).Solvable := by
  have hwf : (P.strongDet κ).WF := ⟨hP.tnI, hP.methods⟩
  rw [HTN.Article.Problem.solvable_iff_decomp _ hwf]
  have hgoal : ∀ s, (P.strongDet κ).GoalState s := fun s =>
    ⟨Set.empty_subset _, Set.empty_disjoint _⟩
  constructor
  · rintro ⟨tn, l, ⟨hd, hprim⟩, hl, as, has, hex⟩
    obtain ⟨s', hrun⟩ := (strongExec_iff_run hP.actions as _ (Set.singleton_nonempty _)).1 hex
    exact ⟨tn, hd, hprim, l, as, s', hl, has, hrun, hgoal _⟩
  · rintro ⟨tn, hd, hprim, l, as, s', hl, has, hrun, -⟩
    exact ⟨tn, l, ⟨hd, hprim⟩, hl, as, has,
      (strongExec_iff_run hP.actions as _ (Set.singleton_nonempty _)).2 ⟨s', hrun⟩⟩

/-- **[CB21, Cor. 4.8]** (semantic part): for totally ordered problems strong OD solvability is
deterministic plan existence as well. -/
theorem strongODSolvable_iff (hP : P.WF) (hto : P.IsTotallyOrdered) :
    P.StrongODSolvable ↔ (P.strongDet κ).Solvable :=
  (strongLDSolvable_iff_strongODSolvable hto hP.tnI).symm.trans (strongLDSolvable_iff hP)

end Problem

end FOND
