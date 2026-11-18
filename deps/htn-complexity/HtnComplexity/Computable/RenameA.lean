import HtnComplexity.Computable.StripsTarget
import HtnComplexity.Computable.RenameC
/-!
# Renaming the *action names* of a description

`HtnComplexity/Computable/RenameC.lean` renames the compound task names of a description
and leaves everything else alone.  This file is its mirror image: it renames the **action
names** — the names of the described actions and the primitive labels of the described networks
— and leaves the facts, the compound task names and the task identifiers untouched.

* `HTN.Syn.TnDesc.renameA`, `HTN.Syn.MethodDesc.renameA`, `HTN.Syn.DomDesc.renameA`,
  `HTN.Syn.InstDesc.renameA` — the image of a description under a map `σ : ℕ → ℕ` of action
  names;
* `HTN.Syn.solvable_renameA_iff` — **equivariance**: for an injective `σ` that fixes the default
  action name `0` the renamed pair of descriptions is solvable exactly when the original pair
  is;
* `HTN.Syn.DomDesc.allActNames`, `HTN.Syn.renameA_dom_eq_self` — the action names a domain
  description mentions, and the fact that renaming along a map which fixes each of them (and
  `0`) leaves the description unchanged.  Together with the equivariance this says that a
  *permutation of the unmentioned action names* is invisible to a fixed domain description,
  which is what `HtnComplexity/Computable/CanonAct.lean` needs.

The hypothesis `σ 0 = 0` is not cosmetic: an identifier carrying no label denotes the action `0`
(`HTN.Syn.TnDesc.label`), and a renaming cannot move that default, so a renaming that moved `0`
would not act on the described network at all.
-/

namespace HTN

namespace Syn

/-! ### The renaming -/

namespace TnDesc

/-- The image of a described task network under a renaming of action names. -/
def renameA (σ : ℕ → ℕ) (t : TnDesc) : TnDesc :=
  (t.ids, t.ordList, t.lbl.map fun l => (l.1, l.2.1, if l.2.1 then l.2.2 else σ l.2.2))

@[simp] lemma renameA_ids (σ : ℕ → ℕ) (t : TnDesc) : (t.renameA σ).ids = t.ids := rfl

@[simp] lemma renameA_ordList (σ : ℕ → ℕ) (t : TnDesc) :
    (t.renameA σ).ordList = t.ordList := rfl

@[simp] lemma renameA_lbl (σ : ℕ → ℕ) (t : TnDesc) :
    (t.renameA σ).lbl = t.lbl.map fun l => (l.1, l.2.1, if l.2.1 then l.2.2 else σ l.2.2) := rfl

@[simp] lemma size_renameA (σ : ℕ → ℕ) (t : TnDesc) : (t.renameA σ).size = t.size := by
  simp [size]

end TnDesc

namespace MethodDesc

/-- The image of a described method under a renaming of action names. -/
def renameA (σ : ℕ → ℕ) (m : MethodDesc) : MethodDesc := (m.1, m.2.renameA σ)

@[simp] lemma size_renameA (σ : ℕ → ℕ) (m : MethodDesc) : (m.renameA σ).size = m.size := by
  simp [size, renameA]

end MethodDesc

namespace ActionDesc

/-- The image of a described action under a renaming of action names. -/
def renameA (σ : ℕ → ℕ) (a : ActionDesc) : ActionDesc := (σ a.1, a.2)

@[simp] lemma size_renameA (σ : ℕ → ℕ) (a : ActionDesc) : (a.renameA σ).size = a.size := by
  simp [size, renameA]

end ActionDesc

namespace DomDesc

/-- The image of a domain description under a renaming of action names. -/
def renameA (σ : ℕ → ℕ) (d : DomDesc) : DomDesc :=
  (d.actions.map (ActionDesc.renameA σ), d.methods.map (MethodDesc.renameA σ))

@[simp] lemma renameA_actions (σ : ℕ → ℕ) (d : DomDesc) :
    (d.renameA σ).actions = d.actions.map (ActionDesc.renameA σ) := rfl

@[simp] lemma renameA_methods (σ : ℕ → ℕ) (d : DomDesc) :
    (d.renameA σ).methods = d.methods.map (MethodDesc.renameA σ) := rfl

@[simp] lemma size_renameA (σ : ℕ → ℕ) (d : DomDesc) : (d.renameA σ).size = d.size := by
  simp [size, List.map_map, Function.comp_def]

@[simp] lemma renameA_heads (σ : ℕ → ℕ) (d : DomDesc) : (d.renameA σ).heads = d.heads := by
  simp [DomDesc.heads, List.map_map, Function.comp_def, MethodDesc.renameA]

end DomDesc

namespace InstDesc

/-- The image of an instance description under a renaming of action names. -/
def renameA (σ : ℕ → ℕ) (q : InstDesc) : InstDesc := (q.initList, q.goalList, q.tnI.renameA σ)

@[simp] lemma renameA_initList (σ : ℕ → ℕ) (q : InstDesc) :
    (q.renameA σ).initList = q.initList := rfl

@[simp] lemma renameA_goalList (σ : ℕ → ℕ) (q : InstDesc) :
    (q.renameA σ).goalList = q.goalList := rfl

@[simp] lemma renameA_tnI (σ : ℕ → ℕ) (q : InstDesc) : (q.renameA σ).tnI = q.tnI.renameA σ := rfl

@[simp] lemma size_renameA (σ : ℕ → ℕ) (q : InstDesc) : (q.renameA σ).size = q.size := by
  simp [size]

end InstDesc

/-! ### Equivariance -/

variable {σ : ℕ → ℕ}

/-- Looking a label up in a list of labels whose action names have been renamed. -/
lemma lookup_map_renameA_lbl (l : List (ℕ × Bool × ℕ)) (i : ℕ) :
    (l.map fun p => (p.1, p.2.1, if p.2.1 then p.2.2 else σ p.2.2)).lookup i =
      (l.lookup i).map fun v => (v.1, if v.1 then v.2 else σ v.2) := by
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

/-- The label of a described network whose action names have been renamed. -/
lemma label_renameA (hσ0 : σ 0 = 0) (t : TnDesc) (i : ℕ) :
    (t.renameA σ).label i = Sum.map σ _root_.id (t.label i) := by
  rw [TnDesc.label, TnDesc.label, TnDesc.renameA_lbl, lookup_map_renameA_lbl]
  rcases h : t.lbl.lookup i with _ | ⟨b, c⟩
  · simpa using hσ0.symm
  · cases b <;> simp

/-- The described network of a renamed description is the image of the described network. -/
lemma toTaskNetwork_renameA (hσ0 : σ 0 = 0) (t : TnDesc) :
    (t.renameA σ).toTaskNetwork =
      TaskNetwork.relabel σ _root_.id (Equiv.refl ℕ) t.toTaskNetwork := by
  refine taskNetwork_ext ?_ ?_ ?_
  · simp [TnDesc.toTaskNetwork, TaskNetwork.relabel]
  · rfl
  · funext x
    simp only [TnDesc.toTaskNetwork, TaskNetwork.relabel, Equiv.refl_symm, Equiv.refl_apply]
    exact label_renameA hσ0 t x

/-- Looking an action up in a list of actions whose names have been renamed injectively. -/
lemma lookup_map_renameA_actions (hσ : Function.Injective σ)
    (l : List ActionDesc) (a : ℕ) :
    (l.map (ActionDesc.renameA σ)).lookup (σ a) = l.lookup a := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    by_cases h : a = p.1
    · subst h
      simp [ActionDesc.renameA]
    · have h1 : (a == p.1) = false := by simpa using h
      have h2 : (σ a == (ActionDesc.renameA σ p).1) = false := by
        simp only [ActionDesc.renameA]
        simpa using fun hc => h (hσ hc)
      simp only [h1, h2, ih]

/-- **Equivariance of the semantics under a renaming of action names.** -/
theorem solvable_renameA_iff (hσ : Function.Injective σ) (hσ0 : σ 0 = 0) (d : DomDesc)
    (q : InstDesc) : Solvable (d.renameA σ) (q.renameA σ) ↔ Solvable d q := by
  have hact : ∀ a : ℕ, (d.renameA σ).actions.lookup (σ a) = d.actions.lookup a := fun a =>
    lookup_map_renameA_actions hσ d.actions a
  refine Problem.solvable_relabel_iff (eF := _root_.id) (eA := σ) (eC := _root_.id)
    (eI := Equiv.refl ℕ) Function.injective_id hσ Function.injective_id
    (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ (problem_wf d q).tnI ?_ ?_
  · rw [Set.image_id]
    show (d.renameA σ).prec (σ o) = d.prec o
    simp only [DomDesc.prec, hact]
  · rw [Set.image_id]
    show (d.renameA σ).add (σ o) = d.add o
    simp only [DomDesc.add, hact]
  · rw [Set.image_id]
    show (d.renameA σ).del (σ o) = d.del o
    simp only [DomDesc.del, hact]
  · rw [Set.image_id]; rfl
  · rw [Set.image_id]; rfl
  · simpa using toTaskNetwork_renameA (σ := σ) hσ0 q.tnI
  · ext m
    simp only [problem_methods, Set.mem_setOf_eq, DomDesc.renameA_methods, List.mem_map,
      Set.mem_image]
    constructor
    · rintro ⟨e, ⟨e0, he0, rfl⟩, rfl⟩
      refine ⟨e0.toMethod, ⟨e0, he0, rfl⟩, ?_⟩
      refine method_ext rfl ?_
      exact (toTaskNetwork_renameA (σ := σ) hσ0 e0.2).symm
    · rintro ⟨m0, ⟨e0, he0, rfl⟩, rfl⟩
      refine ⟨e0.renameA σ, ⟨e0, he0, rfl⟩, ?_⟩
      refine method_ext rfl ?_
      exact toTaskNetwork_renameA (σ := σ) hσ0 e0.2

/-! ### The action names a domain description mentions -/

namespace TnDesc

/-- The action names listed in the label list of a described network — including the labels of
identifiers the network does not list. -/
def lblActNames (t : TnDesc) : List ℕ :=
  t.lbl.filterMap fun l => if l.2.1 then none else some l.2.2

theorem mem_lblActNames {t : TnDesc} {a : ℕ} :
    a ∈ t.lblActNames ↔ ∃ l ∈ t.lbl, l.2.1 = false ∧ l.2.2 = a := by
  simp only [lblActNames, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, hle⟩
    rcases hb : l.2.1 with _ | _
    · rw [hb] at hle
      exact ⟨l, hl, hb, by simpa using hle⟩
    · rw [hb] at hle; simp at hle
  · rintro ⟨l, hl, hb, ha⟩
    exact ⟨l, hl, by simp [hb, ha]⟩

/-- Renaming along a map that fixes every listed action name changes nothing. -/
theorem renameA_eq_self {t : TnDesc} (h : ∀ a ∈ t.lblActNames, σ a = a) :
    t.renameA σ = t := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  show t.lbl.map (fun l => (l.1, l.2.1, if l.2.1 then l.2.2 else σ l.2.2)) = t.lbl
  have hmap : t.lbl.map (fun l => (l.1, l.2.1, if l.2.1 then l.2.2 else σ l.2.2)) =
      t.lbl.map _root_.id := by
    refine List.map_congr_left fun l hl => ?_
    rcases hb : l.2.1 with _ | _
    · have hfix : σ l.2.2 = l.2.2 := h _ (mem_lblActNames.2 ⟨l, hl, hb, rfl⟩)
      simp only [_root_.id, Bool.false_eq_true, if_false, hfix]
      rw [← hb]
    · simp only [_root_.id, if_true]
      rw [← hb]
  rw [hmap, List.map_id]

end TnDesc

namespace DomDesc

/-- **The action names a domain description mentions**: the names of its described actions and
the primitive labels of the bodies of its methods. -/
def allActNames (d : DomDesc) : List ℕ :=
  d.actNames ++ d.methods.flatMap fun m => m.2.lblActNames

theorem mem_allActNames_of_action {d : DomDesc} {a : ActionDesc} (ha : a ∈ d.actions) :
    a.1 ∈ d.allActNames :=
  List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩)

theorem mem_allActNames_of_method {d : DomDesc} {m : MethodDesc} (hm : m ∈ d.methods) {a : ℕ}
    (ha : a ∈ m.2.lblActNames) : a ∈ d.allActNames :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨m, hm, ha⟩)

end DomDesc

/-- **A renaming that fixes every action name a domain description mentions leaves the
description unchanged.** -/
theorem renameA_dom_eq_self {d : DomDesc} (h : ∀ a ∈ d.allActNames, σ a = a) :
    d.renameA σ = d := by
  refine Prod.ext ?_ ?_
  · show d.actions.map (ActionDesc.renameA σ) = d.actions
    have hmap : d.actions.map (ActionDesc.renameA σ) = d.actions.map _root_.id := by
      refine List.map_congr_left fun a ha => ?_
      have hfix : σ a.1 = a.1 := h _ (DomDesc.mem_allActNames_of_action ha)
      simp [ActionDesc.renameA, hfix]
    rw [hmap, List.map_id]
  · show d.methods.map (MethodDesc.renameA σ) = d.methods
    have hmap : d.methods.map (MethodDesc.renameA σ) = d.methods.map _root_.id := by
      refine List.map_congr_left fun m hm => ?_
      have hfix : ∀ a ∈ m.2.lblActNames, σ a = a := fun a ha =>
        h a (DomDesc.mem_allActNames_of_method hm ha)
      show (m.1, m.2.renameA σ) = _root_.id m
      rw [TnDesc.renameA_eq_self hfix]
      rfl
    rw [hmap, List.map_id]

/-- **A renaming of the action names a domain description does not mention is invisible to
it.** -/
theorem solvable_renameA_congr (hσ : Function.Injective σ) (hσ0 : σ 0 = 0) {d : DomDesc}
    (hfix : ∀ a ∈ d.allActNames, σ a = a) (q : InstDesc) :
    Solvable d (q.renameA σ) ↔ Solvable d q := by
  have h := solvable_renameA_iff (σ := σ) hσ hσ0 d q
  rwa [renameA_dom_eq_self hfix] at h

end Syn

end HTN
