import HtnPlanning.Interleave.StripsChain
import HtnPlanning.Computable.Classes
/-!
# Described STRIPS problems

A compilation into the class `STRIPS` of the computable table has to produce *descriptions* of
STRIPS problems.  This file fixes a canonical shape for them and characterises their
solvability.

* `HTN.Syn.stripsDom acts` — the domain description with the action descriptions `acts`, the
  method `0 ↦ ε` and, for every listed action, the method `0 ↦ a 0`;
* `HTN.Syn.stripsInst s g` — the instance description with the initial state `s`, the goal `g`
  and the initial task network consisting of the single compound task `0`;
* `HTN.Syn.stripsDom_isStrips`, `HTN.Syn.stripsInst_isStrips` — they satisfy the conditions of
  the class `STRIPS` of `HtnPlanning/Computable/Classes.lean`;
* `HTN.Syn.solvable_strips_iff` — **the described problem is solvable exactly when the state
  `g` can be reached from `s` by a sequence of the described actions**, i.e. exactly when the
  classical planning problem the description carries is solvable.

The right-to-left half is the chain construction of `HtnPlanning/Interleave/StripsChain.lean`; the
left-to-right half is `HTN.Problem.Solvable.classical`, together with the observation that an
action a description does not mention is a no-op and can be deleted from a plan
(`HTN.Syn.exists_plan_mem_of_plan`).
-/

namespace HTN

namespace Syn

/-! ### Actions a description does not mention -/

/-- The names of the actions a domain description mentions. -/
def DomDesc.actNames (d : DomDesc) : List ℕ := d.actions.map Prod.fst

/-- An action that is not mentioned has an empty precondition, add and delete list. -/
theorem DomDesc.unmentioned {d : DomDesc} {a : ℕ} (h : a ∉ d.actNames) :
    d.prec a = ∅ ∧ d.add a = ∅ ∧ d.del a = ∅ := by
  have hlookup : d.actions.lookup a = none := by
    rw [List.lookup_eq_none_iff]
    intro b hb
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    exact h (List.mem_map_of_mem (f := Prod.fst) hb)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [DomDesc.prec, DomDesc.add, DomDesc.del, hlookup]

/-- Deleting the actions a description does not mention from a plan changes neither its
applicability nor the state it reaches. -/
theorem exists_plan_mem_of_plan (d : DomDesc) (s : Set ℕ) (as : List ℕ)
    (happ : d.toDomain.SeqApplicable as s) :
    ∃ bs : List ℕ, (∀ a ∈ bs, a ∈ d.actNames) ∧ d.toDomain.SeqApplicable bs s ∧
      d.toDomain.transitionSeq bs s = d.toDomain.transitionSeq as s := by
  induction as generalizing s with
  | nil => exact ⟨[], by simp, trivial, rfl⟩
  | cons a as ih =>
    obtain ⟨happ₁, happ₂⟩ := happ
    by_cases hmem : a ∈ d.actNames
    · obtain ⟨bs, hbs, hb₁, hb₂⟩ := ih _ happ₂
      refine ⟨a :: bs, ?_, ⟨happ₁, hb₁⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hmem
        · exact hbs x hx
      · simpa using hb₂
    · obtain ⟨hprec, hadd, hdel⟩ := DomDesc.unmentioned hmem
      have htrans : d.toDomain.transition a s = s := by
        simp [ActionModel.transition, DomDesc.toDomain, hadd, hdel]
      rw [htrans] at happ₂
      obtain ⟨bs, hbs, hb₁, hb₂⟩ := ih _ happ₂
      exact ⟨bs, hbs, hb₁, by rw [hb₂, ActionModel.transitionSeq_cons, htrans]⟩

/-! ### The canonical descriptions -/

/-- The described body `a 0` of the method for the action `a`. -/
def stepBody (a : ℕ) : TnDesc := ([0, 1], [(0, 1)], [(0, false, a), (1, true, 0)])

/-- The described empty body. -/
def emptyBody : TnDesc := ([], [], [])

/-- The described initial task network of a STRIPS instance: the single compound task `0`. -/
def initTn : TnDesc := ([0], [], [(0, true, 0)])

/-- **The canonical STRIPS domain description** for a list of action descriptions. -/
def stripsDom (acts : List ActionDesc) : DomDesc :=
  (acts, (0, emptyBody) :: acts.map fun ad => (0, stepBody ad.1))

/-- **The canonical STRIPS instance description.** -/
def stripsInst (s g : List ℕ) : InstDesc := (s, g, initTn)

@[simp] theorem stripsDom_actions (acts : List ActionDesc) :
    (stripsDom acts).actions = acts := rfl

@[simp] theorem stripsDom_methods (acts : List ActionDesc) :
    (stripsDom acts).methods = (0, emptyBody) :: acts.map fun ad => (0, stepBody ad.1) := rfl

@[simp] theorem stripsInst_initList (s g : List ℕ) : (stripsInst s g).initList = s := rfl

@[simp] theorem stripsInst_goalList (s g : List ℕ) : (stripsInst s g).goalList = g := rfl

@[simp] theorem stripsInst_tnI (s g : List ℕ) : (stripsInst s g).tnI = initTn := rfl

/-! ### The described networks -/

/-- A description that lists no ordering pair orders nothing. -/
theorem not_preOrd_of_ordList_nil {t : TnDesc} (h : t.ordList = []) (a b : ℕ) :
    ¬ t.preOrd a b := by
  intro hab
  induction hab with
  | single hxy => simp [TnDesc.listRel, h] at hxy
  | tail _ hbc _ => simp [TnDesc.listRel, h] at hbc

theorem preOrd_stepBody {a x y : ℕ} : (stepBody a).preOrd x y ↔ (x = 0 ∧ y = 1) := by
  constructor
  · intro h
    induction h with
    | single hxy =>
      simpa [TnDesc.listRel, stepBody, TnDesc.ordList, Prod.ext_iff] using hxy
    | tail _ hbc ih =>
      obtain ⟨rfl, rfl⟩ := ih
      simp [TnDesc.listRel, stepBody, TnDesc.ordList, Prod.ext_iff] at hbc
  · rintro ⟨rfl, rfl⟩
    exact Relation.TransGen.single (by simp [TnDesc.listRel, stepBody, TnDesc.ordList])

@[simp] theorem stepBody_T (a : ℕ) : (stepBody a).toTaskNetwork.T = {0, 1} := rfl

@[simp] theorem stepBody_label_zero (a : ℕ) : (stepBody a).label 0 = Sum.inl a := rfl

@[simp] theorem stepBody_label_one (a : ℕ) : (stepBody a).label 1 = Sum.inr 0 := rfl

theorem stepBody_ord {a x y : ℕ} :
    (stepBody a).toTaskNetwork.ord x y ↔ (x = 0 ∧ y = 1) := by
  rw [TnDesc.toTaskNetwork_ord]
  constructor
  · rintro ⟨-, -, h, -⟩
    exact preOrd_stepBody.1 h
  · rintro ⟨rfl, rfl⟩
    refine ⟨by simp [stepBody, TnDesc.ids], by simp [stepBody, TnDesc.ids],
      preOrd_stepBody.2 ⟨rfl, rfl⟩, fun h => ?_⟩
    simpa using preOrd_stepBody.1 h

/-- The described step body is a step body in the sense of `HtnPlanning/Interleave/StripsChain.lean`. -/
theorem isStepBody_stepBody (a : ℕ) :
    StripsChain.IsStepBody (stepBody a).toTaskNetwork 0 a :=
  ⟨0, 1, by decide, stepBody_T a, rfl, rfl, fun _ _ => stepBody_ord⟩

@[simp] theorem emptyBody_T : emptyBody.toTaskNetwork.T = ∅ := rfl

/-- The described initial network of a STRIPS instance is an open chain for the empty plan. -/
theorem isOpenChain_initTn :
    StripsChain.IsOpenChain (A := ℕ) 0 initTn.toTaskNetwork [] [] 0 :=
  StripsChain.isOpenChain_single (by rfl) rfl
    (fun x y h => not_preOrd_of_ordList_nil (by rfl) x y h.2.2.1)

/-! ### The canonical descriptions belong to the class `STRIPS` -/

theorem stripsDom_isStrips (acts : List ActionDesc) : (stripsDom acts).IsStrips := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨rfl, Or.inl rfl⟩
  · obtain ⟨ad, -, rfl⟩ := List.mem_map.1 he
    refine ⟨rfl, Or.inr ⟨0, 1, by decide, stepBody_T ad.1, ⟨ad.1, rfl⟩, rfl,
      fun _ _ => stepBody_ord⟩⟩

theorem stripsInst_isStrips (s g : List ℕ) : (stripsInst s g).IsStrips :=
  ⟨0, by rfl, rfl⟩

/-! ### Solvability of a canonical STRIPS description -/

/-- The methods of a canonical STRIPS description contain the empty body. -/
theorem emptyMethod_mem (acts : List ActionDesc) (s g : List ℕ) :
    (⟨0, emptyBody.toTaskNetwork⟩ : Method ℕ ℕ ℕ) ∈ (problem (stripsDom acts) (stripsInst s g)).methods :=
  ⟨(0, emptyBody), by simp, rfl⟩

/-- ... and a step body for every listed action. -/
theorem stepMethod_mem {acts : List ActionDesc} {a : ℕ} (ha : a ∈ (stripsDom acts).actNames)
    (s g : List ℕ) :
    (⟨0, (stepBody a).toTaskNetwork⟩ : Method ℕ ℕ ℕ) ∈
      (problem (stripsDom acts) (stripsInst s g)).methods := by
  obtain ⟨ad, had, rfl⟩ := List.mem_map.1 ha
  refine ⟨(0, stepBody ad.1), ?_, rfl⟩
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem had)

/-- **Solvability of a described STRIPS problem is classical plan existence.** -/
theorem solvable_strips_iff (acts : List ActionDesc) (s g : List ℕ) :
    Solvable (stripsDom acts) (stripsInst s g) ↔
      ∃ as : List ℕ, (stripsDom acts).toDomain.SeqApplicable as {f | f ∈ s} ∧
        {f | f ∈ g} ⊆ (stripsDom acts).toDomain.transitionSeq as {f | f ∈ s} := by
  constructor
  · intro h
    obtain ⟨as, happ, hgoal⟩ := h.classical
    exact ⟨as, happ, hgoal⟩
  · rintro ⟨as, happ, hgoal⟩
    obtain ⟨bs, hbs, hb₁, hb₂⟩ := exists_plan_mem_of_plan (stripsDom acts) {f | f ∈ s} as happ
    obtain ⟨tn, hreach, hprim, l, hlin, hseq⟩ :=
      StripsChain.exists_solution_of_plan (M := (problem (stripsDom acts) (stripsInst s g)).methods)
        (c₀ := 0) isOpenChain_initTn
        (Acts := {a | a ∈ (stripsDom acts).actNames})
        (fun a ha => ⟨(stepBody a).toTaskNetwork, stepMethod_mem ha s g, isStepBody_stepBody a⟩)
        (emptyMethod_mem acts s g) (TnDesc.toTaskNetwork_wf _) emptyBody_T hbs
    refine ⟨tn, hreach, hprim, l, bs, hlin, hseq, hb₁, ?_⟩
    show {f | f ∈ g} ⊆ _
    rw [show (problem (stripsDom acts) (stripsInst s g)).init = {f | f ∈ s} from rfl,
      show (problem (stripsDom acts) (stripsInst s g)).transitionSeq bs {f | f ∈ s} =
        (stripsDom acts).toDomain.transitionSeq bs {f | f ∈ s} from rfl, hb₂]
    exact hgoal

/-! ### The canonical descriptions are computable -/

open Primrec

theorem primrec_stepBody : Primrec stepBody :=
  Primrec.pair (Primrec.const [0, 1])
    (Primrec.pair (Primrec.const [(0, 1)])
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) Primrec.id))
        (Primrec.const [(1, true, 0)])))

theorem primrec_stripsDom : Primrec stripsDom :=
  Primrec.pair Primrec.id
    (Primrec.list_cons.comp (Primrec.const (0, emptyBody))
      (Primrec.list_map Primrec.id
        (Primrec.pair (Primrec.const 0)
          (primrec_stepBody.comp (Primrec.fst.comp Primrec.snd)))))

theorem primrec_stripsInst : Primrec₂ stripsInst :=
  Primrec.pair Primrec.fst (Primrec.pair Primrec.snd (Primrec.const initTn))

end Syn

end HTN
