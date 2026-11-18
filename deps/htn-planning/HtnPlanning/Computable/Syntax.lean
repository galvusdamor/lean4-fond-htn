import HtnPlanning.Basic
import HtnPlanning.Core.Classes
import HtnPlanning.Computable.ClassesSound
/-!
# A finite description language for HTN domains and problem instances

`HtnCompilability/NonComputable/Degenerate.lean` shows that the compilability notion
`HTN.Table.Comp` — an arbitrary pair of functions on the *semantic* objects `HTN.Domain` and
`HTN.Instance`, of polynomial *semantic* size — is degenerate: every cell of the table holds,
because the domain translation may be a non-computable lookup table and because the semantic
size measures collapse on infinite signatures.

`HtnCompilability/SemTable/TableComputable.lean` formalises the repair abstractly, over *split
codings*.  This file supplies what that repair needs in order to be usable for the whole
table: **one concrete finite description language**

* `HTN.Syn.DomDesc` — a description of a domain: a finite list of actions with their
  precondition, add and delete lists, and a finite list of methods;
* `HTN.Syn.InstDesc` — a description of a problem instance: the initial state, the goal, and
  the initial task network;

together with

* their decodings `HTN.Syn.DomDesc.toDomain`, `HTN.Syn.InstDesc.toInstance` into the semantic
  objects, and `HTN.Syn.problem` for the described planning problem;
* a **syntactic size** (`HTN.Syn.DomDesc.size`, `HTN.Syn.InstDesc.size`): the number of symbols
  of the description.  Unlike the semantic size this never degenerates — a description is a
  finite object, and its size is the length of the text one writes down.

Both types are built from `ℕ`, `Bool`, products and lists, so they are `Primcodable`
(`inferInstance`) and one can speak of `Computable` functions between them without any further
work; the accessors are `Primrec`, which is what a proof that a concrete compilation is
computable starts from.

## Conventions

* The signature is fixed to `ℕ` in all four components (facts, actions, compound task names,
  task identifiers), as in `HTN.Table.SplitCoding`; a description mentions only finitely many
  of them.
* A task network is described by a list of task identifiers, a list of ordering pairs and a
  list of labels; the label `(true, n)` is the compound name `n`, the label `(false, n)` is the
  action `n`, and an unlabelled identifier defaults to the action `0`.
* The ordering of the described network is the **strict part of the transitive closure** of the
  list of pairs, restricted to the listed identifiers.  Taking the transitive closure means
  that a description need not list the order in full; taking the strict part means that a
  listed cycle describes no order at all between the identifiers on it.  The point of this
  reading is that *every* description denotes a **well-formed** task network
  (`HTN.Syn.TnDesc.toTaskNetwork_wf`), hence a well-formed planning problem
  (`HTN.Syn.problem_wf`): the described objects are exactly the objects of the semantics, which
  requires `≺` to be a strict partial order, and no description has to be rejected.
* An action that the description does not mention has empty precondition, add and delete lists;
  in particular a domain description denotes a domain with finitely many non-trivial actions
  and finitely many methods.
-/

namespace HTN

namespace Syn

/-- A bound on the length of a `flatMap`. -/
theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ n) : (l.flatMap f).length ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hle := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    calc (f a).length + (l.flatMap f).length ≤ n + l.length * n := by omega
      _ = (l.length + 1) * n := by ring

/-- Membership in a list of numbers, as a `foldr` — the shape that makes it primitive
recursive. -/
def memB (l : List ℕ) (n : ℕ) : Bool := l.foldr (fun x b => if x = n then true else b) false

@[simp] theorem memB_iff {l : List ℕ} {n : ℕ} : memB l n = true ↔ n ∈ l := by
  induction l with
  | nil => simp [memB]
  | cons x xs ih =>
    by_cases h : x = n
    · subst h
      simp [memB]
    · rw [show memB (x :: xs) n = memB xs n by simp [memB, h], ih, List.mem_cons]
      exact ⟨fun hn => Or.inr hn, fun hn => hn.resolve_left fun hx => h hx.symm⟩

/-- A successful lookup finds an entry of the list. -/
theorem mem_of_lookup_eq_some {β : Type} {l : List (ℕ × β)} {a : ℕ} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p ps ih =>
    rw [show p = (p.1, p.2) from rfl, List.lookup_cons] at h
    by_cases hp : a = p.1
    · subst hp
      simp only [beq_self_eq_true, Option.some.injEq] at h
      simp [Prod.ext_iff, h]
    · have hb : (a == p.1) = false := by simp [hp]
      rw [hb] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ### Task networks -/

namespace TnDesc

/-- The label a label list attaches to the identifier `i`, as a list: the singleton of the name
if the first entry for `i` has the requested kind (`true` for a compound name, `false` for an
action), and the empty list otherwise.  An identifier with no entry defaults to the action `0`,
as `TnDesc.label` does.  This is `TnDesc.label` in the shape of a `foldr`, which is what makes
it primitive recursive. -/
def labelList (k : Bool) (l : List (ℕ × Bool × ℕ)) (i : ℕ) : List ℕ :=
  l.foldr (fun p r => if p.1 = i then (if p.2.1 = k then [p.2.2] else []) else r)
    (if k = true then [] else [0])

theorem labelList_eq (k : Bool) (l : List (ℕ × Bool × ℕ)) (i : ℕ) :
    labelList k l i = match l.lookup i with
      | some (b, c) => if b = k then [c] else []
      | none => if k = true then [] else [0] := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨n, b, c⟩ := p
    rw [List.lookup_cons]
    by_cases h : n = i
    · subst h
      simp [labelList]
    · have hb : (i == n) = false := by simp [Ne.symm h]
      simp only [labelList, List.foldr_cons, if_neg h, hb]
      exact ih

/-- The compound task names occurring in a described task network. -/
def compoundNames (t : TnDesc) : List ℕ := t.ids.flatMap (labelList true t.lbl)

/-- The action names occurring in a described task network (the unlabelled identifiers
contribute the default action `0`). -/
def actionNames (t : TnDesc) : List ℕ := t.ids.flatMap (labelList false t.lbl)

theorem mem_labelList_iff {k : Bool} {l : List (ℕ × Bool × ℕ)} {i c : ℕ} :
    c ∈ labelList k l i ↔
      (match l.lookup i with
        | some (b, n) => b = k ∧ n = c
        | none => k = false ∧ c = 0) := by
  rw [labelList_eq]
  rcases h : l.lookup i with _ | ⟨b, n⟩
  · cases k <;> simp
  · by_cases hb : b = k <;> simp [hb, eq_comm]

theorem mem_compoundNames {t : TnDesc} {c : ℕ} :
    c ∈ t.compoundNames ↔ ∃ i ∈ t.ids, t.label i = Sum.inr c := by
  simp only [compoundNames, List.mem_flatMap]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rw [mem_labelList_iff]
  rcases h : t.lbl.lookup i with _ | ⟨b, n⟩
  · simp [TnDesc.label, h]
  · cases b <;> simp [TnDesc.label, h, eq_comm]

theorem mem_actionNames {t : TnDesc} {a : ℕ} :
    a ∈ t.actionNames ↔ ∃ i ∈ t.ids, t.label i = Sum.inl a := by
  simp only [actionNames, List.mem_flatMap]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rw [mem_labelList_iff]
  rcases h : t.lbl.lookup i with _ | ⟨b, n⟩
  · simp [TnDesc.label, h, eq_comm]
  · cases b <;> simp [TnDesc.label, h, eq_comm]

/-- A described network mentions at most as many names of a kind as it has identifiers. -/
theorem length_labelList_flatMap_le (k : Bool) (t : TnDesc) :
    (t.ids.flatMap (labelList k t.lbl)).length ≤ t.ids.length := by
  have h : (t.ids.flatMap (labelList k t.lbl)).length ≤ t.ids.length * 1 := by
    refine length_flatMap_le t.ids _ 1 fun i _ => ?_
    rw [labelList_eq]
    rcases t.lbl.lookup i with _ | ⟨b, n⟩
    · cases k <;> simp
    · by_cases hb : b = k <;> simp [hb]
  rw [mul_one] at h
  exact h

theorem length_compoundNames_le (t : TnDesc) : t.compoundNames.length ≤ t.ids.length :=
  length_labelList_flatMap_le true t

theorem length_actionNames_le (t : TnDesc) : t.actionNames.length ≤ t.ids.length :=
  length_labelList_flatMap_le false t

@[simp] lemma toTaskNetwork_T (t : TnDesc) : t.toTaskNetwork.T = t.ids.toFinset := rfl

@[simp] lemma toTaskNetwork_ord (t : TnDesc) (a b : ℕ) :
    t.toTaskNetwork.ord a b ↔
      a ∈ t.ids ∧ b ∈ t.ids ∧ t.preOrd a b ∧ ¬ t.preOrd b a := Iff.rfl

@[simp] lemma toTaskNetwork_α (t : TnDesc) (i : ℕ) : t.toTaskNetwork.α i = t.label i := rfl

/-- **Every described task network is well formed.** -/
theorem toTaskNetwork_wf (t : TnDesc) : t.toTaskNetwork.WF where
  mem_left := fun h => List.mem_toFinset.2 h.1
  mem_right := fun h => List.mem_toFinset.2 h.2.1
  irrefl := fun _ h => h.2.2.2 h.2.2.1
  trans := fun hab hbc =>
    ⟨hab.1, hbc.2.1, hab.2.2.1.trans hbc.2.2.1, fun hca => hbc.2.2.2 (hca.trans hab.2.2.1)⟩

/-- A listed pair is an ordering of the described network unless it lies on a listed cycle. -/
theorem ordOf_of_mem_ordList {t : TnDesc} {a b : ℕ} (ha : a ∈ t.ids) (hb : b ∈ t.ids)
    (hab : (a, b) ∈ t.ordList) (hba : ¬ t.preOrd b a) : t.toTaskNetwork.ord a b :=
  ⟨ha, hb, Relation.TransGen.single hab, hba⟩

/-- The empty task network, described. -/
def nil : TnDesc := ([], [], [])

@[simp] lemma nil_toTaskNetwork_T : nil.toTaskNetwork.T = ∅ := rfl

end TnDesc

/-! ### Methods, actions, domains and instances -/

namespace MethodDesc

@[simp] lemma toMethod_subtasks (m : MethodDesc) : m.toMethod.subtasks = m.2.toTaskNetwork := rfl

end MethodDesc

namespace ActionDesc

end ActionDesc

namespace DomDesc

@[simp] lemma toDomain_methods (d : DomDesc) :
    d.toDomain.methods = {m | ∃ e ∈ d.methods, e.toMethod = m} := rfl

@[simp] lemma toDomain_prec (d : DomDesc) : d.toDomain.prec = d.prec := rfl

@[simp] lemma toDomain_add (d : DomDesc) : d.toDomain.add = d.add := rfl

@[simp] lemma toDomain_del (d : DomDesc) : d.toDomain.del = d.del := rfl

end DomDesc

namespace InstDesc

@[simp] lemma toInstance_tnI (q : InstDesc) : q.toInstance.tnI = q.tnI.toTaskNetwork := rfl

end InstDesc

@[simp] lemma problem_methods (d : DomDesc) (q : InstDesc) :
    (problem d q).methods = {m | ∃ e ∈ d.methods, e.toMethod = m} := rfl

@[simp] lemma problem_tnI (d : DomDesc) (q : InstDesc) :
    (problem d q).tnI = q.tnI.toTaskNetwork := rfl

@[simp] lemma problem_init (d : DomDesc) (q : InstDesc) :
    (problem d q).init = {f | f ∈ q.initList} := rfl

@[simp] lemma problem_goal (d : DomDesc) (q : InstDesc) :
    (problem d q).goal = {f | f ∈ q.goalList} := rfl

@[simp] lemma problem_prec (d : DomDesc) (q : InstDesc) : (problem d q).prec = d.prec := rfl

@[simp] lemma problem_add (d : DomDesc) (q : InstDesc) : (problem d q).add = d.add := rfl

@[simp] lemma problem_del (d : DomDesc) (q : InstDesc) : (problem d q).del = d.del := rfl

/-- **Every described problem is well formed.**  This is what the reading of the ordering of a
description as the strict part of the transitive closure of the listed pairs buys: the
description language describes exactly the well-formed problems, and the well-formedness
hypothesis of the semantics (`HTN.Problem.WF`) is available for every description. -/
theorem problem_wf (d : DomDesc) (q : InstDesc) : (problem d q).WF where
  tnI := q.tnI.toTaskNetwork_wf
  methods := by
    rintro m ⟨e, -, rfl⟩
    exact e.2.toTaskNetwork_wf

/-- Every method of a described domain comes from the method list of the description; in
particular this holds for the *reachable* methods, which is what the structural classes of
`HtnPlanning/Core/Classes.lean` constrain. -/
lemma mem_methods_of_reachable {d : DomDesc} {q : InstDesc} {m : Method ℕ ℕ ℕ}
    (h : (problem d q).ReachableMethod m) : ∃ e ∈ d.methods, e.toMethod = m := h.1

/-! ### Descriptions are codeable

The description types are built from `ℕ`, `Bool`, products and lists, so the `Primcodable`
instances are found by instance resolution; the accessors are `Primrec`.  These are the facts
a proof that a concrete compilation is computable starts from. -/

example : Primcodable DomDesc := inferInstance
example : Primcodable InstDesc := inferInstance

theorem primrec_ids : Primrec TnDesc.ids := Primrec.fst

theorem primrec_ordList : Primrec TnDesc.ordList := Primrec.fst.comp Primrec.snd

theorem primrec_lbl : Primrec TnDesc.lbl := Primrec.snd.comp Primrec.snd

theorem primrec_actions : Primrec DomDesc.actions := Primrec.fst

theorem primrec_methods : Primrec DomDesc.methods := Primrec.snd

theorem primrec_initList : Primrec InstDesc.initList := Primrec.fst

theorem primrec_goalList : Primrec InstDesc.goalList := Primrec.fst.comp Primrec.snd

theorem primrec_tnI : Primrec InstDesc.tnI := Primrec.snd.comp Primrec.snd

theorem primrec_labelList (k : Bool) : Primrec₂ (TnDesc.labelList k) := by
  have hh : Primrec₂ (fun (a : List (ℕ × Bool × ℕ) × ℕ) (z : (ℕ × Bool × ℕ) × List ℕ) =>
      if z.1.1 = a.2 then (if z.1.2.1 = k then [z.1.2.2] else []) else z.2) := by
    apply Primrec.ite (c := fun w : (List (ℕ × Bool × ℕ) × ℕ) × ((ℕ × Bool × ℕ) × List ℕ) =>
        w.2.1.1 = w.1.2)
    · exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    · apply Primrec.ite (c := fun w : (List (ℕ × Bool × ℕ) × ℕ) × ((ℕ × Bool × ℕ) × List ℕ) =>
        w.2.1.2.1 = k)
      · exact PrimrecRel.comp Primrec.eq
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.const k)
      · exact Primrec.list_cons.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.const [])
      · exact Primrec.const []
    · exact Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.fst (Primrec.const (if k = true then [] else [0])) hh

theorem primrec_compoundNames : Primrec TnDesc.compoundNames :=
  Primrec.list_flatMap primrec_ids
    ((primrec_labelList true).comp (primrec_lbl.comp Primrec.fst) Primrec.snd)

theorem primrec_memB : Primrec₂ memB := by
  have hh : Primrec₂ (fun (a : List ℕ × ℕ) (z : ℕ × Bool) =>
      if z.1 = a.2 then true else z.2) := by
    apply Primrec.ite (c := fun w : (List ℕ × ℕ) × (ℕ × Bool) => w.2.1 = w.1.2)
    · exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    · exact Primrec.const true
    · exact Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.fst (Primrec.const false) hh

theorem primrec_actionNames : Primrec TnDesc.actionNames :=
  Primrec.list_flatMap primrec_ids
    ((primrec_labelList false).comp (primrec_lbl.comp Primrec.fst) Primrec.snd)

end Syn

end HTN
