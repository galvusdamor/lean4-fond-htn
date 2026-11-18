import HtnPlanning.Computable.Syntax
import HtnPlanning.Core.Transfer
/-!
# Renaming the names of a description

A description (`HtnPlanning/Computable/Syntax.lean`) mentions facts, action names,
compound task names and task identifiers, all of them natural numbers.  Nothing in the
semantics depends on *which* numbers these are — only on which of them coincide.  This file
makes that precise:

* `HTN.Syn.TnDesc.rename`, `HTN.Syn.ActionDesc.rename`, `HTN.Syn.MethodDesc.rename`,
  `HTN.Syn.DomDesc.rename`, `HTN.Syn.InstDesc.rename` — the image of a description under a
  map `σ : ℕ → ℕ` of names, applied uniformly to all four kinds of name;
* `HTN.Syn.DomDesc.size_rename`, `HTN.Syn.InstDesc.size_rename` — renaming does not change the
  syntactic size (it renames symbols, it does not add any);
* `HTN.Syn.solvable_rename_iff` — **the equivariance theorem**: for a permutation `π` of `ℕ`
  that fixes `0`, the renamed pair of descriptions is solvable exactly when the original pair
  is.

Two remarks on the hypotheses.

* A *permutation* rather than an injection: the task identifiers of the semantics are
  relabelled along a bijection (`HTN.TaskNetwork.relabel`), and every renaming used in practice
  moves only finitely many names, so this costs nothing.
* `π 0 = 0`: an identifier that the label list of a description does not mention denotes the
  action `0` (`HTN.Syn.TnDesc.label`), so the name `0` carries meaning and a renaming has to
  preserve it.

The use of this file is a *counting* one: it says that the solvability behaviour of a
description depends only on its shape and on the coincidences between its names and the names
of the instances it is applied to, which is what bounds the number of behaviours a description
of bounded size can have.
-/

namespace HTN

namespace Syn

/-! ### Renaming -/

namespace TnDesc

/-- The image of a described task network under a renaming of names. -/
def rename (σ : ℕ → ℕ) (t : TnDesc) : TnDesc :=
  (t.ids.map σ, t.ordList.map (fun p => (σ p.1, σ p.2)),
    t.lbl.map (fun l => (σ l.1, l.2.1, σ l.2.2)))

@[simp] lemma rename_ids (σ : ℕ → ℕ) (t : TnDesc) : (t.rename σ).ids = t.ids.map σ := rfl

@[simp] lemma rename_ordList (σ : ℕ → ℕ) (t : TnDesc) :
    (t.rename σ).ordList = t.ordList.map (fun p => (σ p.1, σ p.2)) := rfl

@[simp] lemma rename_lbl (σ : ℕ → ℕ) (t : TnDesc) :
    (t.rename σ).lbl = t.lbl.map (fun l => (σ l.1, l.2.1, σ l.2.2)) := rfl

@[simp] lemma size_rename (σ : ℕ → ℕ) (t : TnDesc) : (t.rename σ).size = t.size := by
  simp [size]

end TnDesc

namespace ActionDesc

/-- The image of a described action under a renaming of names. -/
def rename (σ : ℕ → ℕ) (a : ActionDesc) : ActionDesc :=
  (σ a.1, a.2.1.map σ, a.2.2.1.map σ, a.2.2.2.map σ)

@[simp] lemma rename_fst (σ : ℕ → ℕ) (a : ActionDesc) : (a.rename σ).1 = σ a.1 := rfl

@[simp] lemma size_rename (σ : ℕ → ℕ) (a : ActionDesc) : (a.rename σ).size = a.size := by
  simp [size, rename]

end ActionDesc

namespace MethodDesc

/-- The image of a described method under a renaming of names. -/
def rename (σ : ℕ → ℕ) (m : MethodDesc) : MethodDesc := (σ m.1, m.2.rename σ)

@[simp] lemma rename_fst (σ : ℕ → ℕ) (m : MethodDesc) : (m.rename σ).1 = σ m.1 := rfl

@[simp] lemma rename_snd (σ : ℕ → ℕ) (m : MethodDesc) : (m.rename σ).2 = m.2.rename σ := rfl

@[simp] lemma size_rename (σ : ℕ → ℕ) (m : MethodDesc) : (m.rename σ).size = m.size := by
  simp [size, rename]

end MethodDesc

namespace DomDesc

/-- The image of a domain description under a renaming of names. -/
def rename (σ : ℕ → ℕ) (d : DomDesc) : DomDesc :=
  (d.actions.map (ActionDesc.rename σ), d.methods.map (MethodDesc.rename σ))

@[simp] lemma rename_actions (σ : ℕ → ℕ) (d : DomDesc) :
    (d.rename σ).actions = d.actions.map (ActionDesc.rename σ) := rfl

@[simp] lemma rename_methods (σ : ℕ → ℕ) (d : DomDesc) :
    (d.rename σ).methods = d.methods.map (MethodDesc.rename σ) := rfl

@[simp] lemma size_rename (σ : ℕ → ℕ) (d : DomDesc) : (d.rename σ).size = d.size := by
  simp [size, List.map_map, Function.comp_def]

end DomDesc

namespace InstDesc

/-- The image of an instance description under a renaming of names. -/
def rename (σ : ℕ → ℕ) (q : InstDesc) : InstDesc :=
  (q.initList.map σ, q.goalList.map σ, q.tnI.rename σ)

@[simp] lemma rename_initList (σ : ℕ → ℕ) (q : InstDesc) :
    (q.rename σ).initList = q.initList.map σ := rfl

@[simp] lemma rename_goalList (σ : ℕ → ℕ) (q : InstDesc) :
    (q.rename σ).goalList = q.goalList.map σ := rfl

@[simp] lemma rename_tnI (σ : ℕ → ℕ) (q : InstDesc) : (q.rename σ).tnI = q.tnI.rename σ := rfl

@[simp] lemma size_rename (σ : ℕ → ℕ) (q : InstDesc) : (q.rename σ).size = q.size := by
  simp [size]

end InstDesc

/-! ### Equivariance -/

variable {π : Equiv.Perm ℕ}

/-- Two task networks with the same identifiers, ordering and labelling are equal. -/
lemma taskNetwork_ext {tn₁ tn₂ : TaskNetwork ℕ ℕ ℕ} (hT : tn₁.T = tn₂.T)
    (hord : tn₁.ord = tn₂.ord) (hα : tn₁.α = tn₂.α) : tn₁ = tn₂ := by
  cases tn₁; cases tn₂; simp_all

/-- Two methods with the same head and the same subtask network are equal. -/
lemma method_ext {m₁ m₂ : Method ℕ ℕ ℕ} (ha : m₁.abstractTask = m₂.abstractTask)
    (hs : m₁.subtasks = m₂.subtasks) : m₁ = m₂ := by
  cases m₁; cases m₂; simp_all

/-- Looking an action up in a renamed action list. -/
lemma lookup_map_rename_actions (hπ : Function.Injective π) (l : List ActionDesc) (a : ℕ) :
    (l.map (ActionDesc.rename π)).lookup (π a) =
      (l.lookup a).map (fun x => (x.1.map π, x.2.1.map π, x.2.2.map π)) := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨n, pre, add, del⟩ := e
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    by_cases h : a = n
    · subst h
      simp [ActionDesc.rename]
    · have h1 : (π a == (ActionDesc.rename π (n, pre, add, del)).1) = false := by
        simp only [ActionDesc.rename, beq_eq_false_iff_ne, ne_eq]
        exact fun hc => h (hπ hc)
      have h2 : (a == n) = false := by simpa using h
      rw [h1, h2]
      exact ih

/-- The described action model of a renamed domain description. -/
lemma lookup_rename_actions (hπ : Function.Injective π) (d : DomDesc) (a : ℕ) :
    (d.rename π).actions.lookup (π a) =
      (d.actions.lookup a).map (fun x => (x.1.map π, x.2.1.map π, x.2.2.map π)) :=
  lookup_map_rename_actions hπ d.actions a

lemma prec_rename (hπ : Function.Injective π) (d : DomDesc) (a : ℕ) :
    (d.rename π).prec (π a) = π '' d.prec a := by
  ext f
  simp only [DomDesc.prec, Set.mem_setOf_eq, Set.mem_image, lookup_rename_actions hπ]
  rcases h : d.actions.lookup a with _ | ⟨pre, add, del⟩
  · simp
  · simp only [Option.map_some, Option.elim]
    constructor
    · intro hf
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact List.mem_map_of_mem hx

lemma add_rename (hπ : Function.Injective π) (d : DomDesc) (a : ℕ) :
    (d.rename π).add (π a) = π '' d.add a := by
  ext f
  simp only [DomDesc.add, Set.mem_setOf_eq, Set.mem_image, lookup_rename_actions hπ]
  rcases h : d.actions.lookup a with _ | ⟨pre, add, del⟩
  · simp
  · simp only [Option.map_some, Option.elim]
    constructor
    · intro hf
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact List.mem_map_of_mem hx

lemma del_rename (hπ : Function.Injective π) (d : DomDesc) (a : ℕ) :
    (d.rename π).del (π a) = π '' d.del a := by
  ext f
  simp only [DomDesc.del, Set.mem_setOf_eq, Set.mem_image, lookup_rename_actions hπ]
  rcases h : d.actions.lookup a with _ | ⟨pre, add, del⟩
  · simp
  · simp only [Option.map_some, Option.elim]
    constructor
    · intro hf
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact List.mem_map_of_mem hx

/-- Looking an identifier up in a renamed label list. -/
lemma lookup_map_rename_lbl (hπ : Function.Injective π) (l : List (ℕ × Bool × ℕ)) (i : ℕ) :
    (l.map (fun x => (π x.1, x.2.1, π x.2.2))).lookup (π i) =
      (l.lookup i).map (fun x => (x.1, π x.2)) := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨j, b, n⟩ := e
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    by_cases h : i = j
    · subst h
      simp
    · have h1 : (π i == π j) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hc => h (hπ hc)
      have h2 : (i == j) = false := by simpa using h
      rw [h1, h2]
      exact ih

/-- The label list of a renamed description, looked up at a renamed identifier. -/
lemma lookup_rename_lbl (hπ : Function.Injective π) (t : TnDesc) (i : ℕ) :
    (t.rename π).lbl.lookup (π i) = (t.lbl.lookup i).map (fun x => (x.1, π x.2)) :=
  lookup_map_rename_lbl hπ t.lbl i

/-- **The label of a renamed description** at a renamed identifier is the renamed label. -/
lemma label_rename (hπ : Function.Injective π) (h0 : π 0 = 0) (t : TnDesc) (i : ℕ) :
    (t.rename π).label (π i) = Sum.map π π (t.label i) := by
  rw [TnDesc.label, TnDesc.label, lookup_rename_lbl hπ]
  rcases t.lbl.lookup i with _ | ⟨b, n⟩
  · simp [h0]
  · cases b <;> simp

/-- Renaming transports the listed ordering relation. -/
lemma listRel_rename (hπ : Function.Injective π) (t : TnDesc) (a b : ℕ) :
    (t.rename π).listRel (π a) (π b) ↔ t.listRel a b := by
  simp only [TnDesc.listRel, TnDesc.rename_ordList, List.mem_map]
  constructor
  · rintro ⟨p, hp, hpe⟩
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hpe
    have : p = (a, b) := Prod.ext (hπ h1.symm).symm (hπ h2.symm).symm
    exact this ▸ hp
  · intro h
    exact ⟨(a, b), h, rfl⟩

lemma preOrd_rename (hπ : Function.Injective π) (t : TnDesc) (a b : ℕ) :
    (t.rename π).preOrd (π a) (π b) ↔ t.preOrd a b := by
  constructor
  · intro h
    -- transport along the inverse
    have key : ∀ x y : ℕ, Relation.TransGen (t.rename π).listRel x y →
        Relation.TransGen t.listRel (π.symm x) (π.symm y) := by
      intro x y hxy
      induction hxy with
      | single hst =>
        refine Relation.TransGen.single ?_
        have := (listRel_rename hπ t (π.symm x) (π.symm _)).1 (by simpa using hst)
        exact this
      | tail _ hst ih =>
        refine ih.tail ?_
        have := (listRel_rename hπ t (π.symm _) (π.symm _)).1 (by simpa using hst)
        exact this
    have := key _ _ h
    simpa using this
  · intro h
    have key : ∀ x y : ℕ, Relation.TransGen t.listRel x y →
        Relation.TransGen (t.rename π).listRel (π x) (π y) := by
      intro x y hxy
      induction hxy with
      | single hst => exact Relation.TransGen.single ((listRel_rename hπ t _ _).2 hst)
      | tail _ hst ih => exact ih.tail ((listRel_rename hπ t _ _).2 hst)
    exact key _ _ h

/-- **The described network of a renamed description** is the relabelling of the described
network. -/
lemma toTaskNetwork_rename (hπ : Function.Injective π) (h0 : π 0 = 0) (t : TnDesc) :
    (t.rename π).toTaskNetwork =
      TaskNetwork.relabel (⇑π) (⇑π) (π : ℕ ≃ ℕ) t.toTaskNetwork := by
  refine taskNetwork_ext ?_ ?_ ?_
  · simp only [TnDesc.toTaskNetwork, TaskNetwork.relabel, TnDesc.rename_ids]
    ext x
    simp
  · funext x y
    simp only [TnDesc.toTaskNetwork, TaskNetwork.relabel, eq_iff_iff, TnDesc.ordOf]
    rw [show x = π (π.symm x) by simp, show y = π (π.symm y) by simp]
    simp only [Equiv.symm_apply_apply]
    rw [preOrd_rename hπ, preOrd_rename hπ]
    simp only [TnDesc.rename_ids, List.mem_map]
    constructor
    · rintro ⟨⟨u, hu, hue⟩, ⟨v, hv, hve⟩, h1, h2⟩
      exact ⟨by rwa [hπ hue] at hu, by rwa [hπ hve] at hv, h1, h2⟩
    · rintro ⟨hx, hy, h1, h2⟩
      exact ⟨⟨_, hx, rfl⟩, ⟨_, hy, rfl⟩, h1, h2⟩
  · funext x
    simp only [TnDesc.toTaskNetwork, TaskNetwork.relabel]
    rw [show x = π (π.symm x) by simp, label_rename hπ h0]
    simp

/-- **Equivariance of the semantics**: renaming the names of a pair of descriptions along a
permutation of `ℕ` that fixes `0` does not change solvability. -/
theorem solvable_rename_iff (hπ : Function.Injective π) (h0 : π 0 = 0)
    (d : DomDesc) (q : InstDesc) :
    Solvable (d.rename π) (q.rename π) ↔ Solvable d q := by
  refine Problem.solvable_relabel_iff (eF := ⇑π) (eA := ⇑π) (eC := ⇑π) (eI := (π : ℕ ≃ ℕ))
    hπ hπ hπ (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ (problem_wf d q).tnI ?_ ?_
  · exact prec_rename hπ d o
  · exact add_rename hπ d o
  · exact del_rename hπ d o
  · ext f
    simp only [problem_init, Set.mem_setOf_eq, InstDesc.rename_initList, List.mem_map,
      Set.mem_image]
  · ext f
    simp only [problem_goal, Set.mem_setOf_eq, InstDesc.rename_goalList, List.mem_map,
      Set.mem_image]
  · simp only [problem_tnI, InstDesc.rename_tnI]
    exact toTaskNetwork_rename hπ h0 _
  · ext m
    simp only [problem_methods, Set.mem_setOf_eq, DomDesc.rename_methods, List.mem_map,
      Set.mem_image]
    constructor
    · rintro ⟨e, ⟨e0, he0, rfl⟩, rfl⟩
      refine ⟨e0.toMethod, ⟨e0, he0, rfl⟩, ?_⟩
      refine method_ext rfl ?_
      exact (toTaskNetwork_rename hπ h0 e0.2).symm
    · rintro ⟨m0, ⟨e0, he0, rfl⟩, rfl⟩
      refine ⟨e0.rename π, ⟨e0, he0, rfl⟩, ?_⟩
      refine method_ext rfl ?_
      exact toTaskNetwork_rename hπ h0 e0.2

end Syn

end HTN
