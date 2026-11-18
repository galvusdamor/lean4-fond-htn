import HtnPlanning.Computable.Rename
import HtnComplexity.Computable.Window
/-!
# Renaming the *compound task names* of a description

`HtnPlanning/Computable/Rename.lean` renames all four kinds of name of a description
uniformly, along a permutation of `ℕ`.  A compilation that has to make room for fresh compound
task names cannot afford that: the facts of the instance description are written by the
*instance* translation, which does not know the domain description and cannot rename them.

This file therefore renames the **compound task names only** — the heads of the methods and the
compound labels of the described networks — leaving facts, action names and task identifiers
untouched.  Because the identifiers are untouched, an *injection* suffices where
`HTN.Syn.solvable_rename_iff` needs a permutation:

* `HTN.Syn.TnDesc.renameC`, `HTN.Syn.MethodDesc.renameC`, `HTN.Syn.DomDesc.renameC`,
  `HTN.Syn.InstDesc.renameC` — the image of a description under a map `σ : ℕ → ℕ` of compound
  names;
* `HTN.Syn.solvable_renameC_iff` — **equivariance**: for an injective `σ` the renamed pair of
  descriptions is solvable exactly when the original pair is;
* `HTN.Syn.DomDesc.size_renameC`, `HTN.Syn.methodsTO_renameC` — renaming changes neither the
  number of symbols nor the shape of the described networks.
-/

namespace HTN

namespace Syn

/-! ### The renaming -/

namespace TnDesc

/-- The image of a described task network under a renaming of compound task names. -/
def renameC (σ : ℕ → ℕ) (t : TnDesc) : TnDesc :=
  (t.ids, t.ordList, t.lbl.map fun l => (l.1, l.2.1, if l.2.1 then σ l.2.2 else l.2.2))

@[simp] lemma renameC_ids (σ : ℕ → ℕ) (t : TnDesc) : (t.renameC σ).ids = t.ids := rfl

@[simp] lemma renameC_ordList (σ : ℕ → ℕ) (t : TnDesc) :
    (t.renameC σ).ordList = t.ordList := rfl

@[simp] lemma renameC_lbl (σ : ℕ → ℕ) (t : TnDesc) :
    (t.renameC σ).lbl = t.lbl.map fun l => (l.1, l.2.1, if l.2.1 then σ l.2.2 else l.2.2) := rfl

@[simp] lemma size_renameC (σ : ℕ → ℕ) (t : TnDesc) : (t.renameC σ).size = t.size := by
  simp [size]

end TnDesc

namespace MethodDesc

/-- The image of a described method under a renaming of compound task names. -/
def renameC (σ : ℕ → ℕ) (m : MethodDesc) : MethodDesc := (σ m.1, m.2.renameC σ)

@[simp] lemma size_renameC (σ : ℕ → ℕ) (m : MethodDesc) : (m.renameC σ).size = m.size := by
  simp [size, renameC]

end MethodDesc

namespace DomDesc

/-- The image of a domain description under a renaming of compound task names: the action list
is untouched, the methods are renamed. -/
def renameC (σ : ℕ → ℕ) (d : DomDesc) : DomDesc :=
  (d.actions, d.methods.map (MethodDesc.renameC σ))

@[simp] lemma renameC_actions (σ : ℕ → ℕ) (d : DomDesc) : (d.renameC σ).actions = d.actions := rfl

@[simp] lemma renameC_methods (σ : ℕ → ℕ) (d : DomDesc) :
    (d.renameC σ).methods = d.methods.map (MethodDesc.renameC σ) := rfl

@[simp] lemma renameC_prec (σ : ℕ → ℕ) (d : DomDesc) : (d.renameC σ).prec = d.prec := rfl

@[simp] lemma renameC_add (σ : ℕ → ℕ) (d : DomDesc) : (d.renameC σ).add = d.add := rfl

@[simp] lemma renameC_del (σ : ℕ → ℕ) (d : DomDesc) : (d.renameC σ).del = d.del := rfl

@[simp] lemma size_renameC (σ : ℕ → ℕ) (d : DomDesc) : (d.renameC σ).size = d.size := by
  simp [size, List.map_map, Function.comp_def]

end DomDesc

namespace InstDesc

/-- The image of an instance description under a renaming of compound task names. -/
def renameC (σ : ℕ → ℕ) (q : InstDesc) : InstDesc := (q.initList, q.goalList, q.tnI.renameC σ)

@[simp] lemma renameC_initList (σ : ℕ → ℕ) (q : InstDesc) :
    (q.renameC σ).initList = q.initList := rfl

@[simp] lemma renameC_goalList (σ : ℕ → ℕ) (q : InstDesc) :
    (q.renameC σ).goalList = q.goalList := rfl

@[simp] lemma renameC_tnI (σ : ℕ → ℕ) (q : InstDesc) : (q.renameC σ).tnI = q.tnI.renameC σ := rfl

@[simp] lemma size_renameC (σ : ℕ → ℕ) (q : InstDesc) : (q.renameC σ).size = q.size := by
  simp [size]

end InstDesc

/-! ### Equivariance -/

variable {σ : ℕ → ℕ}

/-- Looking a label up in a list of labels whose names have been renamed. -/
lemma lookup_map_renameC_lbl (l : List (ℕ × Bool × ℕ)) (i : ℕ) :
    (l.map fun p => (p.1, p.2.1, if p.2.1 then σ p.2.2 else p.2.2)).lookup i =
      (l.lookup i).map fun v => (v.1, if v.1 then σ v.2 else v.2) := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨n, b, c⟩ := p
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    by_cases h : i = n
    · subst h
      simp
    · have h2 : (i == n) = false := by simpa using h
      rw [h2]
      simpa using ih

/-- The label of a renamed described network. -/
lemma label_renameC (t : TnDesc) (i : ℕ) :
    (t.renameC σ).label i = Sum.map _root_.id σ (t.label i) := by
  rw [TnDesc.label, TnDesc.label, TnDesc.renameC_lbl, lookup_map_renameC_lbl]
  rcases h : t.lbl.lookup i with _ | ⟨b, c⟩
  · rfl
  · cases b <;> simp

/-- The described network of a renamed description is the image of the described network. -/
lemma toTaskNetwork_renameC (t : TnDesc) :
    (t.renameC σ).toTaskNetwork =
      TaskNetwork.relabel _root_.id σ (Equiv.refl ℕ) t.toTaskNetwork := by
  refine taskNetwork_ext ?_ ?_ ?_
  · simp [TnDesc.toTaskNetwork, TaskNetwork.relabel]
  · rfl
  · funext x
    simp only [TnDesc.toTaskNetwork, TaskNetwork.relabel, Equiv.refl_symm, Equiv.refl_apply]
    exact label_renameC t x

/-- **Equivariance of the semantics under a renaming of compound task names.** -/
theorem solvable_renameC_iff (hσ : Function.Injective σ) (d : DomDesc) (q : InstDesc) :
    Solvable (d.renameC σ) (q.renameC σ) ↔ Solvable d q := by
  refine Problem.solvable_relabel_iff (eF := _root_.id) (eA := _root_.id) (eC := σ)
    (eI := Equiv.refl ℕ) Function.injective_id Function.injective_id hσ
    (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ (problem_wf d q).tnI ?_ ?_
  · rw [Set.image_id]; rfl
  · rw [Set.image_id]; rfl
  · rw [Set.image_id]; rfl
  · rw [Set.image_id]; rfl
  · rw [Set.image_id]; rfl
  · simpa using toTaskNetwork_renameC (σ := σ) q.tnI
  · ext m
    simp only [problem_methods, Set.mem_setOf_eq, DomDesc.renameC_methods, List.mem_map,
      Set.mem_image]
    constructor
    · rintro ⟨e, ⟨e0, he0, rfl⟩, rfl⟩
      refine ⟨e0.toMethod, ⟨e0, he0, rfl⟩, ?_⟩
      refine method_ext rfl ?_
      exact (toTaskNetwork_renameC (σ := σ) e0.2).symm
    · rintro ⟨m0, ⟨e0, he0, rfl⟩, rfl⟩
      refine ⟨e0.renameC σ, ⟨e0, he0, rfl⟩, ?_⟩
      refine method_ext rfl ?_
      exact toTaskNetwork_renameC (σ := σ) e0.2

/-! ### The shape of the described networks is unchanged -/

/-- Renaming the compound names does not change the described ordering, so a totally ordered
description stays totally ordered. -/
theorem isTotallyOrdered_renameC {t : TnDesc} (h : t.toTaskNetwork.IsTotallyOrdered) :
    (t.renameC σ).toTaskNetwork.IsTotallyOrdered := h

/-- A renamed domain description is totally ordered if the original one is. -/
theorem methodsTO_renameC {d : DomDesc} (h : d.MethodsTO) : (d.renameC σ).MethodsTO := by
  rintro e he
  rw [DomDesc.renameC_methods, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  exact isTotallyOrdered_renameC (h e0 he0)

/-! ### The heads of a renamed description -/

@[simp] lemma renameC_heads (d : DomDesc) : (d.renameC σ).heads = d.heads.map σ := by
  simp [DomDesc.heads, DomDesc.renameC_methods, List.map_map, Function.comp_def,
    MethodDesc.renameC]

/-- The compound names of a renamed described network. -/
lemma compoundNames_renameC (t : TnDesc) :
    (t.renameC σ).compoundNames = t.compoundNames.map σ := by
  simp only [TnDesc.compoundNames, TnDesc.renameC_ids, List.map_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  rw [TnDesc.labelList_eq, TnDesc.labelList_eq, TnDesc.renameC_lbl, lookup_map_renameC_lbl]
  rcases h : t.lbl.lookup i with _ | ⟨b, c⟩
  · simp
  · cases b <;> simp

/-! ### Computability -/

/-- The renaming of a label list is primitive recursive. -/
theorem primrec_renameC_lbl {α : Type} [Primcodable α] {σ : ℕ → ℕ} (hσ : Primrec σ)
    {f : α → List (ℕ × Bool × ℕ)} (hf : Primrec f) :
    Primrec fun a => (f a).map fun l => (l.1, l.2.1, if l.2.1 then σ l.2.2 else l.2.2) := by
  refine Primrec.list_map hf ?_
  have hc : Primrec fun p : α × (ℕ × Bool × ℕ) =>
      cond p.2.2.1 (σ p.2.2.2) p.2.2.2 :=
    Primrec.cond (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (hσ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  refine (Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hc)).of_eq fun p => ?_
  rcases hb : p.2.2.1 with _ | _ <;> simp [hb]

/-- The renaming of a described task network is primitive recursive. -/
theorem primrec_renameC_tn {α : Type} [Primcodable α] {σ : ℕ → ℕ} (hσ : Primrec σ)
    {f : α → TnDesc} (hf : Primrec f) : Primrec fun a => (f a).renameC σ :=
  Primrec.pair (primrec_ids.comp hf)
    (Primrec.pair (primrec_ordList.comp hf)
      (primrec_renameC_lbl hσ (primrec_lbl.comp hf)))

theorem primrec_renameC_dom {σ : ℕ → ℕ} (hσ : Primrec σ) :
    Primrec fun d : DomDesc => d.renameC σ := by
  refine Primrec.pair primrec_actions ?_
  refine Primrec.list_map primrec_methods ?_
  exact Primrec.pair (hσ.comp (Primrec.fst.comp Primrec.snd))
    (primrec_renameC_tn hσ (Primrec.snd.comp Primrec.snd))

end Syn

end HTN
