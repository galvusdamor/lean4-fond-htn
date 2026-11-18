import HtnPlanning.Computable.Syntax
import HtnPlanning.Core.Transfer
/-!
# A described problem lives over a finite signature

A description (`HTN.Syn.DomDesc`, `HTN.Syn.InstDesc`) denotes a planning problem over the
signature `(ℕ, ℕ, ℕ, ℕ)` — all four components are infinite — but it mentions only finitely
many facts, action names and compound task names.  Every semantic construction that needs a
*finite* signature (`Fintype F`, a list of all facts, a finite set of task names …) can
therefore still be applied to it, after moving the described problem to the finite signature it
really uses.

This file carries that out.  For two lists `facts` and `names` of numbers that cover the
description it builds

* `HTN.Syn.TnDesc.small`, `HTN.Syn.MethodDesc.small`, `HTN.Syn.DomDesc.small`,
  `HTN.Syn.InstDesc.small`, `HTN.Syn.smallProblem` — the same objects over the *subtypes*
  `{v : ℕ // v ∈ facts}` (facts) and `{v : ℕ // v ∈ names}` (action names and compound task
  names), keeping `ℕ` as the type of task identifiers,

and proves

* `HTN.Syn.relabel_small_eq` — relabelling the small objects along `Subtype.val` returns the
  described ones exactly, and
* `HTN.Syn.solvable_smallProblem_iff` — **the small problem is solvable exactly when the
  described one is** (via `HTN.Problem.solvable_relabel_iff`).

`HTN.Syn.factsOf` and `HTN.Syn.namesOf` are canonical choices of the two lists, and
`HTN.Syn.solvable_canonical_small_iff` is the theorem for them.
-/

namespace HTN

namespace Syn

open TaskNetwork

/-! ### The two lists -/

/-- The names a described task network can attach to an identifier: the ones listed, and the
default action `0`. -/
def TnDesc.namesOf (t : TnDesc) : List ℕ := 0 :: t.lbl.map (fun p => p.2.2)

/-- The facts a described domain mentions. -/
def DomDesc.factsOf (d : DomDesc) : List ℕ :=
  d.actions.flatMap fun a => a.2.1 ++ a.2.2.1 ++ a.2.2.2

/-- The action and compound task names a described domain mentions. -/
def DomDesc.namesOf (d : DomDesc) : List ℕ :=
  0 :: (d.actions.map Prod.fst ++ d.methods.flatMap fun e => e.1 :: e.2.namesOf)

/-- The facts a description mentions. -/
def factsOf (d : DomDesc) (q : InstDesc) : List ℕ :=
  d.factsOf ++ q.initList ++ q.goalList

/-- The names a description mentions. -/
def namesOf (d : DomDesc) (q : InstDesc) : List ℕ := d.namesOf ++ q.tnI.namesOf

lemma zero_mem_namesOf (d : DomDesc) (q : InstDesc) : 0 ∈ namesOf d q := by
  simp [namesOf, DomDesc.namesOf]

lemma label_mem_namesOf_of_mem {t : TnDesc} {names : List ℕ} (h : t.namesOf ⊆ names) (i : ℕ) :
    (∀ a, t.label i = Sum.inl a → a ∈ names) ∧ (∀ c, t.label i = Sum.inr c → c ∈ names) := by
  have h0 : (0 : ℕ) ∈ names := h (by simp [TnDesc.namesOf])
  constructor
  · intro a ha
    rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
    · rw [TnDesc.label, hl] at ha
      simp only [Sum.inl.injEq] at ha
      rw [← ha]
      exact h0
    · have hmem : n ∈ names := by
        refine h ?_
        simp only [TnDesc.namesOf, List.mem_cons, List.mem_map]
        exact Or.inr ⟨(i, b, n), mem_of_lookup_eq_some hl, rfl⟩
      cases b <;> rw [TnDesc.label, hl] at ha <;> simp only [Sum.inl.injEq] at ha
      · rwa [← ha]
      · exact absurd ha (by simp)
  · intro c hc
    rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
    · rw [TnDesc.label, hl] at hc
      exact absurd hc (by simp)
    · have hmem : n ∈ names := by
        refine h ?_
        simp only [TnDesc.namesOf, List.mem_cons, List.mem_map]
        exact Or.inr ⟨(i, b, n), mem_of_lookup_eq_some hl, rfl⟩
      cases b <;> rw [TnDesc.label, hl] at hc
      · exact absurd hc (by simp)
      · simp only [Sum.inr.injEq] at hc
        rwa [← hc]

/-! ### The small signature -/

variable (facts names : List ℕ)

/-- The facts of the finite signature of a description. -/
abbrev SFact : Type := {v : ℕ // v ∈ facts}

/-- The names of the finite signature of a description, used both for action names and for
compound task names. -/
abbrev SName : Type := {v : ℕ // v ∈ names}

instance : Fintype (SFact facts) := List.Subtype.fintype facts
instance : Fintype (SName names) := List.Subtype.fintype names
instance : DecidableEq (SFact facts) := Subtype.instDecidableEq
instance : DecidableEq (SName names) := Subtype.instDecidableEq

variable {names}

/-- A number as a name of the finite signature (`0` if it is not one). -/
def nm (hn : 0 ∈ names) (a : ℕ) : SName names := if h : a ∈ names then ⟨a, h⟩ else ⟨0, hn⟩

@[simp] lemma val_nm (hn : 0 ∈ names) {a : ℕ} (ha : a ∈ names) : (nm hn a).val = a := by
  simp [nm, ha]

lemma nm_injOn (hn : 0 ∈ names) {a b : ℕ} (ha : a ∈ names) (hb : b ∈ names)
    (h : nm hn a = nm hn b) : a = b := by
  have := congrArg Subtype.val h
  rwa [val_nm hn ha, val_nm hn hb] at this

/-! ### The small objects -/

/-- The described task network, over the finite signature. -/
def TnDesc.small (hn : 0 ∈ names) (t : TnDesc) : TaskNetwork ℕ (SName names) (SName names) where
  T := t.ids.toFinset
  ord := t.ordOf
  α := fun i => Sum.map (nm hn) (nm hn) (t.label i)

/-- The small task network is well formed. -/
theorem TnDesc.small_wf (hn : 0 ∈ names) (t : TnDesc) : (t.small hn).WF where
  mem_left := fun h => List.mem_toFinset.2 h.1
  mem_right := fun h => List.mem_toFinset.2 h.2.1
  irrefl := fun _ h => h.2.2.2 h.2.2.1
  trans := fun hab hbc =>
    ⟨hab.1, hbc.2.1, hab.2.2.1.trans hbc.2.2.1, fun hca => hbc.2.2.2 (hca.trans hab.2.2.1)⟩

/-- The described method, over the finite signature. -/
def MethodDesc.small (hn : 0 ∈ names) (e : MethodDesc) :
    Method ℕ (SName names) (SName names) where
  abstractTask := nm hn e.1
  subtasks := e.2.small hn

/-- The described domain, over the finite signature. -/
def DomDesc.small (d : DomDesc) (hn : 0 ∈ names) (facts : List ℕ) :
    Domain (SFact facts) (SName names) (SName names) ℕ where
  prec a := {v | v.val ∈ d.prec a.val}
  add a := {v | v.val ∈ d.add a.val}
  del a := {v | v.val ∈ d.del a.val}
  methods := {m | ∃ e ∈ d.methods, e.small hn = m}

/-- The described instance, over the finite signature. -/
def InstDesc.small (q : InstDesc) (hn : 0 ∈ names) (facts : List ℕ) :
    Instance (SFact facts) (SName names) (SName names) ℕ where
  init := {v | v.val ∈ q.initList}
  goal := {v | v.val ∈ q.goalList}
  tnI := q.tnI.small hn

/-- The described problem, over the finite signature. -/
def smallProblem (d : DomDesc) (q : InstDesc) (hn : 0 ∈ names) (facts : List ℕ) :
    Problem (SFact facts) (SName names) (SName names) ℕ :=
  (d.small hn facts).mkProblem (q.small hn facts)

/-! ### The small objects relabel to the described ones -/

section Relabel

variable {facts}

/-- Relabelling a small task network along `Subtype.val` returns the described one. -/
theorem relabel_small_tn {t : TnDesc} (hn : 0 ∈ names) (h : t.namesOf ⊆ names) :
    TaskNetwork.relabel (Subtype.val : SName names → ℕ) (Subtype.val : SName names → ℕ)
      (Equiv.refl ℕ) (t.small hn) = t.toTaskNetwork := by
  refine TaskNetwork.ext' ?_ ?_ ?_
  · show (t.ids.toFinset).image (Equiv.refl ℕ) = t.ids.toFinset
    simp
  · rfl
  · funext i
    show Sum.map _ _ (Sum.map (nm hn) (nm hn) (t.label ((Equiv.refl ℕ).symm i))) = t.label i
    obtain ⟨hl, hr⟩ := label_mem_namesOf_of_mem h i
    rcases hx : t.label i with a | c
    · simp [hx, val_nm hn (hl a hx)]
    · simp [hx, val_nm hn (hr c hx)]

/-- Relabelling a small method along `Subtype.val` returns the described one. -/
theorem relabel_small_method {e : MethodDesc} (hn : 0 ∈ names) (hc : e.1 ∈ names)
    (h : e.2.namesOf ⊆ names) :
    Method.relabel (Subtype.val : SName names → ℕ) (Subtype.val : SName names → ℕ)
      (Equiv.refl ℕ) (e.small hn) = e.toMethod := by
  show Method.mk (nm hn e.1).val
    (TaskNetwork.relabel (Subtype.val : SName names → ℕ) (Subtype.val : SName names → ℕ)
      (Equiv.refl ℕ) (e.2.small hn)) = e.toMethod
  rw [val_nm hn hc, relabel_small_tn hn h]
  rfl

end Relabel

/-! ### Solvability -/

section Solvable

/-- **The problem over the finite signature is solvable exactly when the described one is.**

The hypotheses say that the two lists cover the description: every fact it mentions is in
`facts`, and every name it mentions is in `names`. -/
theorem solvable_smallProblem_iff (d : DomDesc) (q : InstDesc) (hn : 0 ∈ names)
    (hdf : ∀ a : ℕ, d.prec a ⊆ {f | f ∈ facts} ∧ d.add a ⊆ {f | f ∈ facts} ∧
      d.del a ⊆ {f | f ∈ facts})
    (hqi : ∀ f ∈ q.initList, f ∈ facts) (hqg : ∀ f ∈ q.goalList, f ∈ facts)
    (hdn : ∀ e ∈ d.methods, e.1 ∈ names ∧ e.2.namesOf ⊆ names)
    (hqn : q.tnI.namesOf ⊆ names) :
    (smallProblem d q hn facts).Solvable ↔ Solvable d q := by
  haveI : Nonempty (SName names) := ⟨⟨0, hn⟩⟩
  have hval : Function.Injective (Subtype.val : SName names → ℕ) := Subtype.val_injective
  have hvalF : Function.Injective (Subtype.val : SFact facts → ℕ) := Subtype.val_injective
  refine (Problem.solvable_relabel_iff (P := smallProblem d q hn facts) (P' := problem d q)
    (eF := (Subtype.val : SFact facts → ℕ)) (eA := (Subtype.val : SName names → ℕ))
    (eC := (Subtype.val : SName names → ℕ)) (eI := Equiv.refl ℕ)
    hvalF hval hval ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
  · intro o _
    show d.prec o.val = _
    ext f
    simp only [Set.mem_image, Subtype.exists]
    constructor
    · intro hf
      exact ⟨f, (hdf o.val).1 hf, hf, rfl⟩
    · rintro ⟨v, hv, hv', rfl⟩
      exact hv'
  · intro o _
    show d.add o.val = _
    ext f
    simp only [Set.mem_image, Subtype.exists]
    constructor
    · intro hf
      exact ⟨f, (hdf o.val).2.1 hf, hf, rfl⟩
    · rintro ⟨v, hv, hv', rfl⟩
      exact hv'
  · intro o _
    show d.del o.val = _
    ext f
    simp only [Set.mem_image, Subtype.exists]
    constructor
    · intro hf
      exact ⟨f, (hdf o.val).2.2 hf, hf, rfl⟩
    · rintro ⟨v, hv, hv', rfl⟩
      exact hv'
  · show {f | f ∈ q.initList} = _
    ext f
    simp only [Set.mem_image, Subtype.exists]
    exact ⟨fun hf => ⟨f, hqi f hf, hf, rfl⟩, by rintro ⟨v, hv, hv', rfl⟩; exact hv'⟩
  · show {f | f ∈ q.goalList} = _
    ext f
    simp only [Set.mem_image, Subtype.exists]
    exact ⟨fun hf => ⟨f, hqg f hf, hf, rfl⟩, by rintro ⟨v, hv, hv', rfl⟩; exact hv'⟩
  · exact TnDesc.small_wf hn q.tnI
  · exact (relabel_small_tn hn hqn).symm
  · show {m | ∃ e ∈ d.methods, e.toMethod = m} = _
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.small hn, ⟨e, he, rfl⟩,
        relabel_small_method hn (hdn e he).1 (hdn e he).2⟩
    · rintro ⟨m₀, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, (relabel_small_method hn (hdn e he).1 (hdn e he).2).symm⟩

end Solvable

/-! ### The canonical lists cover the description -/

lemma prec_subset_factsOf (d : DomDesc) (q : InstDesc) (a : ℕ) :
    d.prec a ⊆ {f | f ∈ factsOf d q} ∧ d.add a ⊆ {f | f ∈ factsOf d q} ∧
      d.del a ⊆ {f | f ∈ factsOf d q} := by
  have key : ∀ (sel : List ℕ × List ℕ × List ℕ → List ℕ),
      (∀ x : List ℕ × List ℕ × List ℕ, sel x ⊆ x.1 ++ x.2.1 ++ x.2.2) →
      ∀ f, f ∈ ((d.actions.lookup a).elim [] sel) → f ∈ factsOf d q := by
    intro sel hsel f hf
    rcases hl : d.actions.lookup a with _ | x
    · rw [hl] at hf; simp at hf
    · rw [hl] at hf
      simp only [Option.elim] at hf
      have hmem : (a, x) ∈ d.actions := mem_of_lookup_eq_some hl
      have hx : f ∈ x.1 ++ x.2.1 ++ x.2.2 := hsel x hf
      simp only [factsOf, DomDesc.factsOf, List.mem_append, List.mem_flatMap]
      refine Or.inl (Or.inl ⟨(a, x), hmem, ?_⟩)
      simp only [List.mem_append] at hx ⊢
      tauto
  refine ⟨fun f hf => key (fun x => x.1) (fun x => by simp) f hf,
    fun f hf => key (fun x => x.2.1) (fun x => by simp) f hf,
    fun f hf => key (fun x => x.2.2) (fun x => by simp) f hf⟩

lemma initList_subset_factsOf (d : DomDesc) (q : InstDesc) : ∀ f ∈ q.initList,
    f ∈ factsOf d q := by
  intro f hf
  simp only [factsOf, List.mem_append]
  exact Or.inl (Or.inr hf)

lemma goalList_subset_factsOf (d : DomDesc) (q : InstDesc) : ∀ f ∈ q.goalList,
    f ∈ factsOf d q := by
  intro f hf
  simp only [factsOf, List.mem_append]
  exact Or.inr hf

lemma methods_names_subset_namesOf (d : DomDesc) (q : InstDesc) :
    ∀ e ∈ d.methods, e.1 ∈ namesOf d q ∧ e.2.namesOf ⊆ namesOf d q := by
  intro e he
  constructor
  · simp only [namesOf, DomDesc.namesOf, List.mem_append, List.mem_cons, List.mem_flatMap]
    exact Or.inl (Or.inr (Or.inr ⟨e, he, by simp⟩))
  · intro x hx
    simp only [namesOf, DomDesc.namesOf, List.mem_append, List.mem_cons, List.mem_flatMap]
    exact Or.inl (Or.inr (Or.inr ⟨e, he, by simp [hx]⟩))

lemma tnI_names_subset_namesOf (d : DomDesc) (q : InstDesc) :
    q.tnI.namesOf ⊆ namesOf d q := by
  intro x hx
  simp only [namesOf, List.mem_append]
  exact Or.inr hx

/-- **The described problem is solvability-equivalent to a problem over a finite signature.** -/
theorem solvable_canonical_small_iff (d : DomDesc) (q : InstDesc) :
    (smallProblem (names := namesOf d q) d q (zero_mem_namesOf d q) (factsOf d q)).Solvable ↔
      Solvable d q :=
  solvable_smallProblem_iff (facts := factsOf d q) d q (zero_mem_namesOf d q)
    (prec_subset_factsOf d q)
    (initList_subset_factsOf d q) (goalList_subset_factsOf d q)
    (methods_names_subset_namesOf d q) (tnI_names_subset_namesOf d q)

end Syn

end HTN
