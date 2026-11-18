import HtnPlanning.Computable.Rename
/-!
# The names a description mentions

`HtnPlanning/Computable/Rename.lean` renames the names of a description.  This file
collects the list of names a description mentions — facts, action names, compound task names
and task identifiers alike, since all four are natural numbers — and the three facts about it
that a counting argument needs:

* `HTN.Syn.DomDesc.names_rename`, `HTN.Syn.InstDesc.names_rename` — renaming a description
  renames its list of names;
* `HTN.Syn.DomDesc.length_names_le`, `HTN.Syn.InstDesc.length_names_le` — a description of
  size `s` mentions at most `2 * s` names;
* `HTN.Syn.DomDesc.rename_eq_self`, `HTN.Syn.InstDesc.rename_eq_self` — a renaming that fixes
  every name of a description leaves the description unchanged.
-/

namespace HTN

namespace Syn

/-- A map that fixes every entry of a list leaves the list unchanged. -/
lemma map_eq_self_of_mem {α : Type} {σ : α → α} : ∀ {l : List α}, (∀ x ∈ l, σ x = x) →
    l.map σ = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.map_cons, h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

namespace TnDesc

/-- The names a described task network mentions: its identifiers, the identifiers of its
ordering pairs and, for each label, the labelled identifier and the name it carries. -/
def names (t : TnDesc) : List ℕ :=
  t.ids ++ t.ordList.flatMap (fun p => [p.1, p.2]) ++ t.lbl.flatMap (fun l => [l.1, l.2.2])

lemma ids_subset_names (t : TnDesc) : ∀ x ∈ t.ids, x ∈ t.names := by
  intro x hx
  simp [names, hx]

lemma ordList_subset_names (t : TnDesc) : ∀ p ∈ t.ordList, p.1 ∈ t.names ∧ p.2 ∈ t.names := by
  intro p hp
  constructor <;> simp only [names, List.mem_append, List.mem_flatMap] <;>
    exact Or.inl (Or.inr ⟨p, hp, by simp⟩)

lemma lbl_subset_names (t : TnDesc) :
    ∀ l ∈ t.lbl, l.1 ∈ t.names ∧ l.2.2 ∈ t.names := by
  intro l hl
  constructor <;> simp only [names, List.mem_append, List.mem_flatMap] <;>
    exact Or.inr ⟨l, hl, by simp⟩

@[simp] lemma names_rename (σ : ℕ → ℕ) (t : TnDesc) : (t.rename σ).names = t.names.map σ := by
  simp only [names, rename_ids, rename_ordList, rename_lbl, List.map_append, List.map_flatMap,
    List.flatMap_map]
  rfl

lemma length_names_le (t : TnDesc) : t.names.length ≤ 2 * t.size := by
  have h1 : (t.ordList.flatMap (fun p => [p.1, p.2])).length ≤ t.ordList.length * 2 :=
    length_flatMap_le _ _ 2 (by intro x _; simp)
  have h2 : (t.lbl.flatMap (fun l => [l.1, l.2.2])).length ≤ t.lbl.length * 2 :=
    length_flatMap_le _ _ 2 (by intro x _; simp)
  simp only [names, List.length_append, size]
  omega

lemma rename_eq_self {σ : ℕ → ℕ} {t : TnDesc} (h : ∀ x ∈ t.names, σ x = x) :
    t.rename σ = t := by
  have hids : t.ids.map σ = t.ids :=
    map_eq_self_of_mem fun x hx => h x (t.ids_subset_names x hx)
  have hord : t.ordList.map (fun p => (σ p.1, σ p.2)) = t.ordList := by
    refine map_eq_self_of_mem fun p hp => ?_
    obtain ⟨h1, h2⟩ := t.ordList_subset_names p hp
    rw [h _ h1, h _ h2]
  have hlbl : t.lbl.map (fun l => (σ l.1, l.2.1, σ l.2.2)) = t.lbl := by
    refine map_eq_self_of_mem fun l hl => ?_
    obtain ⟨h1, h2⟩ := t.lbl_subset_names l hl
    rw [h _ h1, h _ h2]
  simp only [rename, hids, hord, hlbl]
  rfl

end TnDesc

namespace ActionDesc

/-- The names a described action mentions. -/
def names (a : ActionDesc) : List ℕ := a.1 :: (a.2.1 ++ a.2.2.1 ++ a.2.2.2)

@[simp] lemma names_rename (σ : ℕ → ℕ) (a : ActionDesc) : (a.rename σ).names = a.names.map σ := by
  simp [names, rename]

lemma rename_eq_self {σ : ℕ → ℕ} {a : ActionDesc} (h : ∀ x ∈ a.names, σ x = x) :
    a.rename σ = a := by
  have h1 : σ a.1 = a.1 := h _ (by simp [names])
  have hpre : a.2.1.map σ = a.2.1 := map_eq_self_of_mem fun x hx => h x (by simp [names, hx])
  have hadd : a.2.2.1.map σ = a.2.2.1 := map_eq_self_of_mem fun x hx => h x (by simp [names, hx])
  have hdel : a.2.2.2.map σ = a.2.2.2 := map_eq_self_of_mem fun x hx => h x (by simp [names, hx])
  simp only [rename, h1, hpre, hadd, hdel]

lemma length_names_le (a : ActionDesc) : a.names.length ≤ 2 * a.size := by
  simp only [names, size, List.length_cons, List.length_append]
  omega

end ActionDesc

namespace MethodDesc

/-- The names a described method mentions. -/
def names (m : MethodDesc) : List ℕ := m.1 :: m.2.names

@[simp] lemma names_rename (σ : ℕ → ℕ) (m : MethodDesc) : (m.rename σ).names = m.names.map σ := by
  simp [names, rename]

lemma rename_eq_self {σ : ℕ → ℕ} {m : MethodDesc} (h : ∀ x ∈ m.names, σ x = x) :
    m.rename σ = m := by
  have h1 : σ m.1 = m.1 := h _ (by simp [names])
  have h2 : m.2.rename σ = m.2 :=
    TnDesc.rename_eq_self fun x hx => h x (by simp [names, hx])
  simp only [rename, h1, h2]

lemma length_names_le (m : MethodDesc) : m.names.length ≤ 2 * m.size := by
  have := m.2.length_names_le
  simp only [names, size, List.length_cons]
  omega

end MethodDesc

namespace DomDesc

/-- The names a domain description mentions. -/
def names (d : DomDesc) : List ℕ :=
  d.actions.flatMap ActionDesc.names ++ d.methods.flatMap MethodDesc.names

lemma action_names_subset {d : DomDesc} {a : ActionDesc} (ha : a ∈ d.actions) :
    ∀ x ∈ a.names, x ∈ d.names := by
  intro x hx
  simp only [names, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨a, ha, hx⟩

lemma method_names_subset {d : DomDesc} {m : MethodDesc} (hm : m ∈ d.methods) :
    ∀ x ∈ m.names, x ∈ d.names := by
  intro x hx
  simp only [names, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨m, hm, hx⟩

@[simp] lemma names_rename (σ : ℕ → ℕ) (d : DomDesc) : (d.rename σ).names = d.names.map σ := by
  simp only [names, rename_actions, rename_methods, List.map_append, List.map_flatMap,
    List.flatMap_map, ActionDesc.names_rename, MethodDesc.names_rename]

lemma length_names_le (d : DomDesc) : d.names.length ≤ 2 * d.size := by
  have hact : (d.actions.flatMap ActionDesc.names).length ≤
      2 * (d.actions.map ActionDesc.size).sum := by
    rw [List.length_flatMap, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun a _ => a.length_names_le
  have hmet : (d.methods.flatMap MethodDesc.names).length ≤
      2 * (d.methods.map MethodDesc.size).sum := by
    rw [List.length_flatMap, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun m _ => m.length_names_le
  simp only [names, List.length_append, size]
  omega

lemma rename_eq_self {σ : ℕ → ℕ} {d : DomDesc} (h : ∀ x ∈ d.names, σ x = x) :
    d.rename σ = d := by
  have hact : d.actions.map (ActionDesc.rename σ) = d.actions := by
    refine map_eq_self_of_mem fun a ha => ?_
    exact ActionDesc.rename_eq_self fun x hx => h x (action_names_subset ha x hx)
  have hmet : d.methods.map (MethodDesc.rename σ) = d.methods := by
    refine map_eq_self_of_mem fun m hm => ?_
    exact MethodDesc.rename_eq_self fun x hx => h x (method_names_subset hm x hx)
  simp only [rename, hact, hmet]
  rfl

end DomDesc

namespace InstDesc

/-- The names an instance description mentions. -/
def names (q : InstDesc) : List ℕ := q.initList ++ q.goalList ++ q.tnI.names

@[simp] lemma names_rename (σ : ℕ → ℕ) (q : InstDesc) : (q.rename σ).names = q.names.map σ := by
  simp only [names, rename_initList, rename_goalList, rename_tnI, List.map_append,
    TnDesc.names_rename]

lemma length_names_le (q : InstDesc) : q.names.length ≤ 2 * q.size := by
  have := q.tnI.length_names_le
  simp only [names, size, List.length_append]
  omega

lemma rename_eq_self {σ : ℕ → ℕ} {q : InstDesc} (h : ∀ x ∈ q.names, σ x = x) :
    q.rename σ = q := by
  have hinit : q.initList.map σ = q.initList :=
    map_eq_self_of_mem fun x hx => h x (by simp [names, hx])
  have hgoal : q.goalList.map σ = q.goalList :=
    map_eq_self_of_mem fun x hx => h x (by simp [names, hx])
  have htn : q.tnI.rename σ = q.tnI :=
    TnDesc.rename_eq_self fun x hx => h x (by simp [names, hx])
  simp only [rename, hinit, hgoal, htn]
  rfl

end InstDesc

end Syn

end HTN
