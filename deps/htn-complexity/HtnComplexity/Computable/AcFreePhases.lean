import HtnComplexity.Computable.AcFreeWrap
import HtnPlanning.Interleave.ChainPrefix
import HtnPlanning.Core.MethodRestrict
/-!
# The phases of the vocabulary-free wrapper

The initial task network of `HTN.Syn.AcFree.wrapInst` is the chain `aBoot ; t_I ; tPost`.  This
file provides the tools that split a plan of the wrapped problem along that chain:

* `HTN.Syn.AcFree.netSingle`, `HTN.Syn.AcFree.netPair` — the one- and two-task networks the
  chain splits into, and the corresponding `HTN.TaskNetwork.IsSeries` decompositions;
* `HTN.Syn.AcFree.decomposesTo_base_of_wrap` — **conservativity**: a refinement of a network
  whose labels have the shape of the numbering of the acyclic construction only uses methods of
  the wrapped description, never one of the wrapper's own; hence
  `HTN.Syn.AcFree.netYield_wrap_iff`;
* `HTN.Syn.AcFree.prec_wrapDom_base`, … — the wrapped description agrees with the description it
  wraps on every action of the base shape;
* `HTN.Syn.AcFree.seqApplicable_wrap_iff`, `HTN.Syn.AcFree.transitionSeq_wrap` — **the frame
  property**: the facts the wrapper adds are invisible to the actions of the base description.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

/-! ### Small task networks -/

/-- The task network with the single task `i`, labelled `x`. -/
def netSingle (i : ℕ) (x : ℕ ⊕ ℕ) : TaskNetwork ℕ ℕ ℕ where
  T := {i}
  ord := fun _ _ => False
  α := fun _ => x

/-- The chain of the two tasks `i` and `j`, labelled `x` and `y`. -/
def netPair (i j : ℕ) (x y : ℕ ⊕ ℕ) : TaskNetwork ℕ ℕ ℕ where
  T := {i, j}
  ord := fun a b => a = i ∧ b = j
  α := fun t => if t = i then x else y

variable {i j : ℕ} {x y : ℕ ⊕ ℕ}

@[simp] lemma netSingle_T : (netSingle i x).T = {i} := rfl

@[simp] lemma netSingle_α (t : ℕ) : (netSingle i x).α t = x := rfl

@[simp] lemma netSingle_ord (a b : ℕ) : ¬ (netSingle i x).ord a b := id

@[simp] lemma netPair_T : (netPair i j x y).T = {i, j} := rfl

lemma netSingle_wf : (netSingle i x).WF where
  mem_left := fun h => absurd h (netSingle_ord _ _)
  mem_right := fun h => absurd h (netSingle_ord _ _)
  irrefl := fun _ h => h
  trans := fun h _ => absurd h (netSingle_ord _ _)

lemma isSingle_netSingle : TaskNetwork.IsSingle (netSingle i x) i where
  memT := fun z => by simp [netSingle]
  ord := fun _ _ => id

lemma netPair_wf (h : i ≠ j) : (netPair i j x y).WF where
  mem_left := fun hab => by simp [netPair, hab.1]
  mem_right := fun hab => by simp [netPair, hab.2]
  irrefl := fun t ht => h (ht.1.symm.trans ht.2)
  trans := fun hab hbc => absurd (hbc.1.symm.trans hab.2) h

/-- The two-task chain is the sequential composition of its two tasks. -/
lemma netPair_isSeries (h : i ≠ j) :
    (netPair i j x y).IsSeries (netSingle i x) (netSingle j y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [netSingle_T, Finset.disjoint_singleton]
    exact h
  · intro t
    simp [netPair, netSingle]
  · intro t ht
    simp only [netSingle_T, Finset.mem_singleton] at ht
    subst ht
    simp [netPair, netSingle]
  · intro t ht
    simp only [netSingle_T, Finset.mem_singleton] at ht
    subst ht
    simp [netPair, netSingle, Ne.symm h]
  · intro a b
    simp only [netSingle_ord, netSingle_T, Finset.mem_singleton, false_or]
    exact Iff.rfl

/-! ### The initial task network of the wrapped instance -/

/-- The label of the `j`-th task of a one-row described grid. -/
lemma label_oneRow {row : List (Bool × ℕ)} {j : ℕ} (hj : j < row.length) :
    (gridDesc [row]).label (Nat.pair 0 j) =
      (if (row.getD j (false, 0)).1 then Sum.inr (row.getD j (false, 0)).2
        else Sum.inl (row.getD j (false, 0)).2) := by
  have hrow : gridRow [row] 0 = row := rfl
  have hj' : j < (gridRow [row] 0).length := by rw [hrow]; exact hj
  have hlk := lookup_cellLbl (ls := [row]) (i := 0) (j := j) (by simp) hj'
  rw [TnDesc.label]
  simp only [gridDesc_lbl] at *
  rw [hlk, hrow]
  rcases hx : row.getD j (false, 0) with ⟨b, n⟩
  cases b <;> simp

/-- The three identifiers of the initial task network of the wrapped instance are distinct. -/
lemma pair_ne_pair {j j' : ℕ} (h : j ≠ j') : Nat.pair 0 j ≠ Nat.pair 0 j' := fun hc =>
  h (Nat.pair_eq_pair.1 hc).2

/-- **The initial task network of the wrapped instance is the chain `aBoot ; t_I ; tPost`.** -/
lemma wrapInst_isSeries (q : InstDesc) :
    (wrapInst q).tnI.toTaskNetwork.IsSeries (netSingle (Nat.pair 0 0) (Sum.inl aBoot))
      (netPair (Nat.pair 0 1) (Nat.pair 0 2) (Sum.inr tTI) (Sum.inr tPost)) := by
  have hrow : gridRow [[pAct aBoot, pTsk tTI, pTsk tPost]] 0 =
      [pAct aBoot, pTsk tTI, pTsk tPost] := rfl
  have hmem : ∀ t : ℕ, t ∈ (wrapInst q).tnI.toTaskNetwork.T ↔
      t = Nat.pair 0 0 ∨ t = Nat.pair 0 1 ∨ t = Nat.pair 0 2 := by
    intro t
    rw [wrapInst_tnI, TnDesc.toTaskNetwork_T, List.mem_toFinset, gridDesc_ids, mem_cellIds]
    constructor
    · rintro ⟨i, j, hi, hj, rfl⟩
      simp only [List.length_singleton] at hi
      interval_cases i
      rw [hrow] at hj
      simp only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, 0, by simp, by rw [hrow]; simp, rfl⟩
      · exact ⟨0, 1, by simp, by rw [hrow]; simp, rfl⟩
      · exact ⟨0, 2, by simp, by rw [hrow]; simp, rfl⟩
  have hα0 : (wrapInst q).tnI.toTaskNetwork.α (Nat.pair 0 0) = Sum.inl aBoot := by
    rw [wrapInst_tnI, TnDesc.toTaskNetwork_α, label_oneRow (by simp)]
    rfl
  have hα1 : (wrapInst q).tnI.toTaskNetwork.α (Nat.pair 0 1) = Sum.inr tTI := by
    rw [wrapInst_tnI, TnDesc.toTaskNetwork_α, label_oneRow (by simp)]
    rfl
  have hα2 : (wrapInst q).tnI.toTaskNetwork.α (Nat.pair 0 2) = Sum.inr tPost := by
    rw [wrapInst_tnI, TnDesc.toTaskNetwork_α, label_oneRow (by simp)]
    rfl
  have hord : ∀ a b : ℕ, (wrapInst q).tnI.toTaskNetwork.ord a b ↔
      ((a = Nat.pair 0 1 ∧ b = Nat.pair 0 2) ∨
        (a = Nat.pair 0 0 ∧ (b = Nat.pair 0 1 ∨ b = Nat.pair 0 2))) := by
    intro a b
    rw [wrapInst_tnI, gridDesc_ord]
    constructor
    · rintro ⟨i, j, j', hi, hjj, hj', rfl, rfl⟩
      simp only [List.length_singleton] at hi
      interval_cases i
      rw [hrow] at hj'
      simp only [List.length_cons, List.length_nil] at hj'
      have hj3 : j < 3 := by omega
      interval_cases j <;> interval_cases j' <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩)
      · exact ⟨0, 1, 2, by simp, by omega, by rw [hrow]; simp, rfl, rfl⟩
      · exact ⟨0, 0, 1, by simp, by omega, by rw [hrow]; simp, rfl, rfl⟩
      · exact ⟨0, 0, 2, by simp, by omega, by rw [hrow]; simp, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [netSingle_T, netPair_T, Finset.disjoint_singleton_left, Finset.mem_insert,
      Finset.mem_singleton]
    push_neg
    exact ⟨pair_ne_pair (by omega), pair_ne_pair (by omega)⟩
  · intro t
    rw [hmem]
    simp [netSingle, netPair]
  · intro t ht
    simp only [netSingle_T, Finset.mem_singleton] at ht
    subst ht
    rw [hα0]
    rfl
  · intro t ht
    simp only [netPair_T, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · rw [hα1]
      simp [netPair]
    · rw [hα2]
      have : Nat.pair 0 2 ≠ Nat.pair 0 1 := pair_ne_pair (by omega)
      simp [netPair, this]
  · intro a b
    rw [hord]
    simp only [netSingle_ord, netSingle_T, Finset.mem_singleton, netPair_T, Finset.mem_insert,
      false_or]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, hb⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, by simpa using hb⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, hb⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, by simpa using hb⟩

/-! ### Conservativity -/

variable {V : List ℕ} {d₀ : DomDesc}

/-- Every method of the wrapper has a head that is not base shaped. -/
lemma not_baseTask_of_mem_wrapMeths {e : MethodDesc} (he : e ∈ wrapMeths V) :
    ¬ BaseTask e.1 := by
  simp only [wrapMeths, List.mem_cons, List.mem_flatMap] at he
  rcases he with rfl | ⟨v, -, hv⟩
  · exact not_baseTask_tPost
  · simp only [List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;>
      simp only [] <;>
      first
        | exact not_baseTask_tChk v
        | exact not_baseTask_tEarn v

/-- Every action of the wrapper has a name that is not base shaped. -/
lemma not_baseAct_of_mem_wrapActs {e : ActionDesc} (he : e ∈ wrapActs V) :
    ¬ BaseAct e.1 := by
  simp only [wrapActs, List.mem_cons, List.mem_flatMap] at he
  rcases he with rfl | rfl | ⟨v, -, hv⟩
  · exact not_baseAct_aBoot
  · exact not_baseAct_aSkip
  · simp only [List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;>
      simp only [] <;>
      first
        | exact not_baseAct_aChkN v
        | exact not_baseAct_aChkP v
        | exact not_baseAct_aEarn v

/-- On a base-shaped action the wrapper's own actions are not found. -/
lemma lookup_wrapActs_base {a : ℕ} (h : BaseAct a) : (wrapActs V).lookup a = none := by
  have key : ∀ l : List ActionDesc, (∀ e ∈ l, ¬ BaseAct e.1) → l.lookup a = none := by
    intro l hl
    induction l with
    | nil => rfl
    | cons p ps ih =>
        rw [show p = (p.1, p.2) from rfl, List.lookup_cons]
        have hne : (a == p.1) = false := by
          refine beq_eq_false_iff_ne.2 fun hc => ?_
          exact hl p (by simp) (hc ▸ h)
        rw [hne]
        exact ih fun e he => hl e (by simp [he])
  exact key _ fun e he => not_baseAct_of_mem_wrapActs he

/-- On a base-shaped action the wrapped description looks the action up in the description it
wraps. -/
lemma lookup_wrapDom_base {a : ℕ} (h : BaseAct a) :
    (wrapDom V d₀).actions.lookup a = d₀.actions.lookup a := by
  rw [wrapDom_actions, List.lookup_append, lookup_wrapActs_base h]
  cases d₀.actions.lookup a <;> rfl

/-- **Conservativity of the wrapper.**  A refinement of a network all of whose labels have the
shape of the numbering of the acyclic construction only uses the methods of the wrapped
description, and its labels have that shape again. -/
theorem decomposesTo_base_of_wrap (hshape : BaseShaped d₀) {tn tn' : TaskNetwork ℕ ℕ ℕ}
    (h₀ : ∀ t ∈ tn.T, GoodLabel (tn.α t))
    (h : DecomposesTo (wrapDom V d₀).toDomain.methods tn tn') :
    DecomposesTo d₀.toDomain.methods tn tn' ∧ ∀ t ∈ tn'.T, GoodLabel (tn'.α t) := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, h₀⟩
  | @tail u w _ hstep ih =>
      obtain ⟨hdec, hlab⟩ := ih
      obtain ⟨t, m, hm, htT, hαt, v, hvwf, ⟨σ, hbij, hord, hα⟩, hdisj, rfl⟩ := hstep
      -- the method is one of the wrapped description, not one of the wrapper
      obtain ⟨e, he, rfl⟩ := hm
      have hgood : BaseTask e.1 := by
        have := hlab t htT
        rw [hαt] at this
        exact this
      have hebase : e ∈ d₀.methods := by
        rcases List.mem_append.1 (by simpa using he) with h' | h'
        · exact h'
        · exact absurd hgood (not_baseTask_of_mem_wrapMeths h')
      have hmbase : e.toMethod ∈ d₀.toDomain.methods := ⟨e, hebase, rfl⟩
      refine ⟨Relation.ReflTransGen.tail hdec
        ⟨t, e.toMethod, hmbase, htT, hαt, v, hvwf, ⟨σ, hbij, hord, hα⟩, hdisj, rfl⟩, ?_⟩
      intro x hx
      rw [decomposeWith_α]
      by_cases hxv : x ∈ v.T
      · simp only [hxv, if_true]
        rw [hα x hxv]
        have hσ : σ x ∈ e.toMethod.subtasks.T := by
          simpa using hbij.mapsTo (by simpa using hxv)
        exact hshape.bodies e hebase _ (by simpa using hσ)
      · simp only [hxv, if_false]
        rcases mem_decomposeWith_T.1 hx with ⟨hxT, -⟩ | hxv'
        · exact hlab x hxT
        · exact absurd hxv' hxv

/-- **The wrapped description refines a base-shaped network exactly as the description it
wraps.** -/
theorem netYield_wrap_iff (hshape : BaseShaped d₀) {tn : TaskNetwork ℕ ℕ ℕ}
    (h₀ : ∀ t ∈ tn.T, GoodLabel (tn.α t)) {bs : List ℕ} :
    (wrapDom V d₀).toDomain.NetYield tn bs ↔ d₀.toDomain.NetYield tn bs := by
  have hsub : d₀.toDomain.methods ⊆ (wrapDom V d₀).toDomain.methods := by
    rintro m ⟨e, he, rfl⟩
    exact ⟨e, by simp [he], rfl⟩
  rw [Domain.netYield_iff, Domain.netYield_iff]
  constructor
  · rintro ⟨tn', hd, hprim, l, hlin, has⟩
    exact ⟨tn', (decomposesTo_base_of_wrap hshape h₀ hd).1, hprim, l, hlin, has⟩
  · rintro ⟨tn', hd, hprim, l, hlin, has⟩
    exact ⟨tn', Problem.decomposesTo_mono hsub hd, hprim, l, hlin, has⟩

/-- **The actions of a refinement of a base-shaped network are base shaped.** -/
theorem baseAct_of_netYield (hshape : BaseShaped d₀) {tn : TaskNetwork ℕ ℕ ℕ}
    (h₀ : ∀ t ∈ tn.T, GoodLabel (tn.α t)) {bs : List ℕ}
    (h : d₀.toDomain.NetYield tn bs) : ∀ a ∈ bs, BaseAct a := by
  have hsub : d₀.toDomain.methods ⊆ (wrapDom ([] : List ℕ) d₀).toDomain.methods := by
    rintro m ⟨e, he, rfl⟩
    exact ⟨e, by simp [he], rfl⟩
  obtain ⟨tn', hd, -, l, hlin, has⟩ := Domain.netYield_iff.1 h
  have hlab := (decomposesTo_base_of_wrap (V := ([] : List ℕ)) hshape h₀
    (Problem.decomposesTo_mono hsub hd)).2
  intro a ha
  -- the action occurs as a label of the primitive network
  have hmem : (Sum.inl a : ℕ ⊕ ℕ) ∈ l.map tn'.α := by
    rw [has]
    exact List.mem_map_of_mem ha
  obtain ⟨t, htl, hαt⟩ := List.mem_map.1 hmem
  have htT : t ∈ tn'.T := (hlin.2.1 t).1 htl
  have := hlab t htT
  rw [hαt] at this
  exact this

/-! ### The action model of the wrapper -/

/-- On a base-shaped action the wrapped description has the precondition of the description it
wraps. -/
theorem prec_wrapDom_base {a : ℕ} (h : BaseAct a) : (wrapDom V d₀).prec a = d₀.prec a := by
  simp only [DomDesc.prec, lookup_wrapDom_base h]

/-- On a base-shaped action the wrapped description has the add list of the description it
wraps. -/
theorem add_wrapDom_base {a : ℕ} (h : BaseAct a) : (wrapDom V d₀).add a = d₀.add a := by
  simp only [DomDesc.add, lookup_wrapDom_base h]

/-- On a base-shaped action the wrapped description has the delete list of the description it
wraps. -/
theorem del_wrapDom_base {a : ℕ} (h : BaseAct a) : (wrapDom V d₀).del a = d₀.del a := by
  simp only [DomDesc.del, lookup_wrapDom_base h]

/-! ### The frame property -/

/-- The facts of the base shape. -/
def baseFacts : Set ℕ := {f | BaseFact f}

/-- The precondition of an action of the base description consists of base-shaped facts. -/
lemma prec_subset_baseFacts (hshape : BaseShaped d₀) (a : ℕ) : d₀.prec a ⊆ baseFacts := by
  intro f hf
  rcases hx : d₀.actions.lookup a with - | x
  · rw [DomDesc.prec, hx] at hf; simp at hf
  · rw [DomDesc.prec, hx] at hf
    exact hshape.facts _ (mem_domFacts_of_lookup hx (by simp at hf ⊢; tauto))

/-- The add list of an action of the base description consists of base-shaped facts. -/
lemma add_subset_baseFacts (hshape : BaseShaped d₀) (a : ℕ) : d₀.add a ⊆ baseFacts := by
  intro f hf
  rcases hx : d₀.actions.lookup a with - | x
  · rw [DomDesc.add, hx] at hf; simp at hf
  · rw [DomDesc.add, hx] at hf
    exact hshape.facts _ (mem_domFacts_of_lookup hx (by simp at hf ⊢; tauto))

/-- The delete list of an action of the base description consists of base-shaped facts. -/
lemma del_subset_baseFacts (hshape : BaseShaped d₀) (a : ℕ) : d₀.del a ⊆ baseFacts := by
  intro f hf
  rcases hx : d₀.actions.lookup a with - | x
  · rw [DomDesc.del, hx] at hf; simp at hf
  · rw [DomDesc.del, hx] at hf
    exact hshape.facts _ (mem_domFacts_of_lookup hx (by simp at hf ⊢; tauto))

/-- **One step of the frame property.** -/
lemma frame_step (hshape : BaseShaped d₀) {a : ℕ} (ha : BaseAct a) {X E : Set ℕ}
    (hX : X ⊆ baseFacts) (hE : ∀ f ∈ E, f ∉ baseFacts) :
    (wrapDom V d₀).toDomain.transition a (X ∪ E) = d₀.toDomain.transition a X ∪ E ∧
      ((wrapDom V d₀).toDomain.Applicable a (X ∪ E) ↔ d₀.toDomain.Applicable a X) ∧
      d₀.toDomain.transition a X ⊆ baseFacts := by
  have hp : (wrapDom V d₀).prec a = d₀.prec a := prec_wrapDom_base ha
  have hadd : (wrapDom V d₀).add a = d₀.add a := add_wrapDom_base ha
  have hdel : (wrapDom V d₀).del a = d₀.del a := del_wrapDom_base ha
  refine ⟨?_, ?_, ?_⟩
  · show ((X ∪ E) \ (wrapDom V d₀).del a) ∪ (wrapDom V d₀).add a = _
    rw [hadd, hdel]
    ext f
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · rintro (⟨hf | hf, hd⟩ | hf)
      · exact Or.inl (Or.inl ⟨hf, hd⟩)
      · exact Or.inr hf
      · exact Or.inl (Or.inr hf)
    · rintro ((⟨hf, hd⟩ | hf) | hf)
      · exact Or.inl ⟨Or.inl hf, hd⟩
      · exact Or.inr hf
      · exact Or.inl ⟨Or.inr hf, fun hd => hE f hf (del_subset_baseFacts hshape a hd)⟩
  · show (wrapDom V d₀).prec a ⊆ X ∪ E ↔ d₀.prec a ⊆ X
    rw [hp]
    constructor
    · intro h f hf
      rcases h hf with h' | h'
      · exact h'
      · exact absurd (prec_subset_baseFacts hshape a hf) (hE f h')
    · intro h f hf
      exact Or.inl (h hf)
  · show (X \ d₀.del a) ∪ d₀.add a ⊆ baseFacts
    rintro f (⟨hf, -⟩ | hf)
    · exact hX hf
    · exact add_subset_baseFacts hshape a hf

/-- A plan of base-shaped actions is executable in a state enlarged by facts outside the base
shape exactly when it is executable in the state itself. -/
theorem seqApplicable_wrap_iff (hshape : BaseShaped d₀) {bs : List ℕ}
    (hbs : ∀ a ∈ bs, BaseAct a) {X E : Set ℕ} (hX : X ⊆ baseFacts)
    (hE : ∀ f ∈ E, f ∉ baseFacts) :
    (wrapDom V d₀).toDomain.SeqApplicable bs (X ∪ E) ↔ d₀.toDomain.SeqApplicable bs X := by
  induction bs generalizing X with
  | nil => simp [ActionModel.SeqApplicable]
  | cons a bs ih =>
      obtain ⟨hstep, happ, hsub⟩ := frame_step (V := V) hshape (hbs a (by simp)) hX hE
      rw [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_cons, happ, hstep,
        ih (fun x hx => hbs x (by simp [hx])) hsub]

/-- A plan of base-shaped actions leaves the facts outside the base shape untouched, and acts on
the others as in the description that is wrapped. -/
theorem transitionSeq_wrap (hshape : BaseShaped d₀) {bs : List ℕ}
    (hbs : ∀ a ∈ bs, BaseAct a) {X E : Set ℕ} (hX : X ⊆ baseFacts)
    (hE : ∀ f ∈ E, f ∉ baseFacts) :
    (wrapDom V d₀).toDomain.transitionSeq bs (X ∪ E) =
      d₀.toDomain.transitionSeq bs X ∪ E := by
  induction bs generalizing X with
  | nil => simp [ActionModel.transitionSeq]
  | cons a bs ih =>
      obtain ⟨hstep, -, hsub⟩ := frame_step (V := V) hshape (hbs a (by simp)) hX hE
      rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_cons, hstep,
        ih (fun x hx => hbs x (by simp [hx])) hsub]

/-- A plan of base-shaped actions keeps the state inside the base shape. -/
theorem transitionSeq_subset_baseFacts (hshape : BaseShaped d₀) {bs : List ℕ}
    (hbs : ∀ a ∈ bs, BaseAct a) {X : Set ℕ} (hX : X ⊆ baseFacts) :
    d₀.toDomain.transitionSeq bs X ⊆ baseFacts := by
  induction bs generalizing X with
  | nil => simpa [ActionModel.transitionSeq] using hX
  | cons a bs ih =>
      obtain ⟨-, -, hsub⟩ :=
        frame_step (V := ([] : List ℕ)) (E := (∅ : Set ℕ)) hshape (hbs a (by simp)) hX
          (fun f hf => absurd hf (Set.notMem_empty f))
      rw [ActionModel.transitionSeq_cons]
      exact ih (fun x hx => hbs x (by simp [hx])) hsub

end AcFree

end Syn

end HTN
