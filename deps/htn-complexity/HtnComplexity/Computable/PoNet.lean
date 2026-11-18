import HtnPlanning.Computable.Linearise
import HtnPlanning.Progression.Progression
/-!
# Search networks on descriptions: progression and decomposition, computably

Deciding plan existence for a *partially ordered* class of the compilability table means
searching the progression space of `HtnPlanning/Progression/Progression.lean`: the nodes of that
space are task networks, which are semantic objects with an arbitrary identifier type, an
arbitrary ordering relation and, at every decomposition step, a *fresh copy* of the subtask
network of the applied method.  This file supplies the computable counterpart:

* `HTN.Syn.PNet` — a **search network**, a finite list of items `(i, ℓ, b, D)`: the identifier
  `i`, its label `ℓ` (`(true, c)` a compound name, `(false, a)` an action, as in `TnDesc`), the
  flag `b` telling whether the task is still to be processed, and the list `D` of identifiers
  that must be processed before it.  An item is never deleted — only its flag is cleared —
  because the *labels* of processed tasks are still part of the semantic task network
  (`TaskNetwork.α` is a total function).
* `HTN.Syn.PNet.toTN` — the task network a search network denotes: its tasks are the items
  still flagged, `a ≺ b` iff `a` is listed among the predecessors of `b`, and `α` is the label
  list.
* `HTN.Syn.PNet.Ok` — the invariant: identifiers are distinct, cleared items have no
  predecessors, every predecessor is a task of the network, and the predecessor lists are
  irreflexive and transitively closed.  It is exactly what makes `toTN` well formed
  (`HTN.Syn.PNet.toTN_wf`).
* the two operations, `HTN.Syn.PNet.finish` (progression of an unconstrained primitive task)
  and `HTN.Syn.PNet.expand` (decomposition of an unconstrained compound task by a listed
  method), together with the theorems that they denote *exactly* the two operations of the
  semantics,

      toTN (p.finish i) = (toTN p).progress i
      toTN (p.expand i e) = decomposeWith (toTN p) i ((e.2.shift p.freshOff).toTaskNetwork)

  and that they preserve the invariant.

The copy of the subtask network that `expand` inserts is the **shift** `TnDesc.shift off t` of
the method's description by an offset larger than every identifier used so far, which is what
makes the inserted identifiers fresh while keeping the copy isomorphic to the method's subtask
network (`HTN.Syn.TnDesc.shift_iso`).
-/

namespace HTN

namespace Syn

/-! ### Deciding the ordering of a described task network -/

namespace TnDesc

/-- The label of an identifier as a pair, in the format of a label list: `TnDesc.label` written
so that it can be stored in a search network. -/
def lblPair (t : TnDesc) (i : ℕ) : Bool × ℕ :=
  match t.lbl.lookup i with
  | some (b, n) => (b, n)
  | none => (false, 0)

/-- The label of an identifier, from its pair. -/
def ofPair (b : Bool × ℕ) : ℕ ⊕ ℕ := if b.1 = true then Sum.inr b.2 else Sum.inl b.2

@[simp] theorem ofPair_lblPair (t : TnDesc) (i : ℕ) : ofPair (t.lblPair i) = t.label i := by
  simp only [lblPair, label, ofPair]
  rcases h : t.lbl.lookup i with _ | ⟨b, n⟩
  · simp
  · cases b <;> simp

theorem ofPair_eq_inl_iff {b : Bool × ℕ} {a : ℕ} : ofPair b = Sum.inl a ↔ b = (false, a) := by
  rcases b with ⟨bb, m⟩
  cases bb <;> simp [ofPair]

theorem ofPair_eq_inr_iff {b : Bool × ℕ} {c : ℕ} : ofPair b = Sum.inr c ↔ b = (true, c) := by
  rcases b with ⟨bb, m⟩
  cases bb <;> simp [ofPair]

theorem ordB_eq_false_iff {t : TnDesc} {a b : ℕ} :
    t.ordB a b = false ↔ ¬ t.toTaskNetwork.ord a b := by
  rw [← ordB_iff]
  cases t.ordB a b <;> simp

/-! ### Shifting a description -/

/-- The description with every identifier shifted by `off`. -/
def shift (off : ℕ) (t : TnDesc) : TnDesc :=
  (t.ids.map (fun x => off + x), t.ordList.map (fun q => (off + q.1, off + q.2)),
    t.lbl.map (fun q => (off + q.1, q.2)))

@[simp] theorem shift_ids (off : ℕ) (t : TnDesc) : (shift off t).ids = t.ids.map (off + ·) := rfl

@[simp] theorem shift_ordList (off : ℕ) (t : TnDesc) :
    (shift off t).ordList = t.ordList.map (fun q => (off + q.1, off + q.2)) := rfl

@[simp] theorem shift_lbl (off : ℕ) (t : TnDesc) :
    (shift off t).lbl = t.lbl.map (fun q => (off + q.1, q.2)) := rfl

theorem mem_shift_ids {off : ℕ} {t : TnDesc} {x : ℕ} :
    x ∈ (shift off t).ids ↔ ∃ y ∈ t.ids, x = off + y := by
  simp only [shift_ids, List.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

theorem shift_listRel {off : ℕ} {t : TnDesc} {a b : ℕ} :
    (shift off t).listRel (off + a) (off + b) ↔ t.listRel a b := by
  simp only [listRel, shift_ordList, List.mem_map, Prod.ext_iff]
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    have : q = (a, b) := Prod.ext (Nat.add_left_cancel h1) (Nat.add_left_cancel h2)
    exact this ▸ hq
  · intro h
    exact ⟨(a, b), h, rfl, rfl⟩

theorem shift_preOrd_left {off : ℕ} {t : TnDesc} {a b : ℕ} (h : (shift off t).preOrd a b) :
    ∃ a' b', a = off + a' ∧ b = off + b' ∧ t.preOrd a' b' := by
  induction h with
  | single hab =>
    obtain ⟨q, hq, hqa⟩ := List.mem_map.1 hab
    refine ⟨q.1, q.2, by simpa using congrArg Prod.fst hqa.symm,
      by simpa using congrArg Prod.snd hqa.symm, Relation.TransGen.single ?_⟩
    simpa [listRel] using hq
  | tail hbc hcd ih =>
    obtain ⟨a', c', rfl, rfl, hac⟩ := ih
    obtain ⟨q, hq, hqa⟩ := List.mem_map.1 hcd
    have h1 : off + q.1 = off + c' := congrArg Prod.fst hqa
    have h2 : off + q.2 = _ := congrArg Prod.snd hqa
    refine ⟨a', q.2, rfl, h2.symm, hac.tail ?_⟩
    have : q.1 = c' := Nat.add_left_cancel h1
    simpa [listRel, ← this] using hq

theorem shift_preOrd {off : ℕ} {t : TnDesc} {a b : ℕ} :
    (shift off t).preOrd (off + a) (off + b) ↔ t.preOrd a b := by
  constructor
  · intro h
    obtain ⟨a', b', ha, hb, hab⟩ := shift_preOrd_left h
    rwa [Nat.add_left_cancel ha, Nat.add_left_cancel hb]
  · intro h
    induction h with
    | single hab => exact Relation.TransGen.single (shift_listRel.2 hab)
    | tail hbc hcd ih => exact ih.tail (shift_listRel.2 hcd)

theorem shift_lookup {off : ℕ} {t : TnDesc} {x : ℕ} :
    (shift off t).lbl.lookup (off + x) = t.lbl.lookup x := by
  simp only [shift_lbl]
  induction t.lbl with
  | nil => rfl
  | cons q qs ih =>
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    by_cases h : q.1 = x
    · subst h
      simp
    · have h1 : (x == q.1) = false := by simp [Ne.symm h]
      have h2 : (off + x == off + q.1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      simp only [h1, h2, ih]

theorem shift_label {off : ℕ} {t : TnDesc} {x : ℕ} :
    (shift off t).label (off + x) = t.label x := by
  simp only [label, shift_lookup]

theorem shift_ord {off : ℕ} {t : TnDesc} {a b : ℕ} :
    (shift off t).toTaskNetwork.ord (off + a) (off + b) ↔ t.toTaskNetwork.ord a b := by
  simp only [toTaskNetwork_ord, shift_preOrd, mem_shift_ids]
  constructor
  · rintro ⟨⟨a', ha', hae⟩, ⟨b', hb', hbe⟩, hab, hba⟩
    exact ⟨by simpa using (Nat.add_left_cancel hae) ▸ ha', by
      simpa using (Nat.add_left_cancel hbe) ▸ hb', hab, hba⟩
  · rintro ⟨ha, hb, hab, hba⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hab, hba⟩

theorem shift_ord_mem {off : ℕ} {t : TnDesc} {a b : ℕ}
    (h : (shift off t).toTaskNetwork.ord a b) : ∃ a' b', a = off + a' ∧ b = off + b' := by
  obtain ⟨ha, hb, -, -⟩ := h
  obtain ⟨a', -, rfl⟩ := mem_shift_ids.1 ha
  obtain ⟨b', -, rfl⟩ := mem_shift_ids.1 hb
  exact ⟨a', b', rfl, rfl⟩

/-- **The shifted description denotes an isomorphic task network.** -/
theorem shift_iso (off : ℕ) (t : TnDesc) :
    (shift off t).toTaskNetwork.Iso t.toTaskNetwork := by
  refine ⟨fun n => n - off, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [toTaskNetwork_T, Finset.mem_coe, List.mem_toFinset] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := mem_shift_ids.1 hx
    simpa using hy
  · intro x hx y hy hxy
    simp only [toTaskNetwork_T, Finset.mem_coe, List.mem_toFinset] at hx hy
    obtain ⟨x', -, rfl⟩ := mem_shift_ids.1 hx
    obtain ⟨y', -, rfl⟩ := mem_shift_ids.1 hy
    simp only [Nat.add_sub_cancel_left] at hxy
    rw [hxy]
  · intro y hy
    simp only [toTaskNetwork_T, Finset.mem_coe, List.mem_toFinset] at hy
    refine ⟨off + y, ?_, by simp⟩
    simp only [toTaskNetwork_T, Finset.mem_coe, List.mem_toFinset]
    exact mem_shift_ids.2 ⟨y, hy, rfl⟩
  · intro x hx y hy
    simp only [toTaskNetwork_T, List.mem_toFinset] at hx hy
    obtain ⟨x', -, rfl⟩ := mem_shift_ids.1 hx
    obtain ⟨y', -, rfl⟩ := mem_shift_ids.1 hy
    simpa using shift_ord
  · intro x hx
    simp only [toTaskNetwork_T, List.mem_toFinset] at hx
    obtain ⟨x', -, rfl⟩ := mem_shift_ids.1 hx
    simpa using shift_label

end TnDesc

/-! ### Search networks -/

/-- An **item** of a search network: the identifier, its label (`(true, c)` for the compound
name `c`, `(false, a)` for the action `a`), the flag telling whether the task still has to be
processed, and the identifiers that have to be processed before it. -/
abbrev PItem : Type := ℕ × (Bool × ℕ) × Bool × List ℕ

/-- A **search network**: a list of items. -/
abbrev PNet : Type := List PItem

namespace PNet

/-- The identifiers of the tasks still to be processed. -/
def ids (p : PNet) : List ℕ := (p.filter (fun x => x.2.2.1)).map (fun x => x.1)

/-- All identifiers the search network mentions, processed or not. -/
def allIds (p : PNet) : List ℕ := p.map (fun x => x.1)

/-- The label of an identifier — the label of its first item, defaulting to the action `0`, as
`TnDesc.label` does. -/
def label (p : PNet) (i : ℕ) : ℕ ⊕ ℕ :=
  p.foldr (fun x r => if x.1 = i then TnDesc.ofPair x.2.1 else r) (Sum.inl 0)

/-- The identifiers that have to be processed before the given one. -/
def deps (p : PNet) (i : ℕ) : List ℕ :=
  p.foldr (fun x r => if x.1 = i then x.2.2.2 else r) []

/-- **The task network a search network denotes.** -/
def toTN (p : PNet) : TaskNetwork ℕ ℕ ℕ where
  T := p.ids.toFinset
  ord := fun a b => a ∈ p.deps b
  α := p.label

@[simp] theorem toTN_T (p : PNet) : (toTN p).T = p.ids.toFinset := rfl

@[simp] theorem toTN_ord (p : PNet) (a b : ℕ) : (toTN p).ord a b ↔ a ∈ p.deps b := Iff.rfl

@[simp] theorem toTN_α (p : PNet) (i : ℕ) : (toTN p).α i = p.label i := rfl

theorem mem_ids {p : PNet} {i : ℕ} :
    i ∈ p.ids ↔ ∃ x ∈ p, x.1 = i ∧ x.2.2.1 = true := by
  simp only [ids, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hpres⟩, rfl⟩
    exact ⟨x, hx, rfl, by simpa using hpres⟩
  · rintro ⟨x, hx, rfl, hpres⟩
    exact ⟨x, ⟨hx, by simpa using hpres⟩, rfl⟩

theorem mem_allIds_of_mem_ids {p : PNet} {i : ℕ} (h : i ∈ p.ids) : i ∈ p.allIds := by
  obtain ⟨x, hx, rfl, -⟩ := mem_ids.1 h
  exact List.mem_map_of_mem hx

theorem deps_eq_nil_of_not_mem {p : PNet} {i : ℕ} (h : i ∉ p.allIds) : p.deps i = [] := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.1 ≠ i := fun hxi => h (by simp [allIds, hxi])
    have hxs : i ∉ PNet.allIds xs := fun hm => h (by
      simp only [allIds, List.map_cons, List.mem_cons]
      exact Or.inr hm)
    simp only [deps, List.foldr_cons, if_neg hx]
    exact ih hxs

/-- A `foldr` looking an item up by its identifier finds that item, if the identifiers are
distinct. -/
theorem foldr_eq_of_mem {β : Type} (f : PItem → β) (b₀ : β) {p : PNet} {x : PItem}
    (hx : x ∈ p) (hnd : p.allIds.Nodup) :
    p.foldr (fun y r => if y.1 = x.1 then f y else r) b₀ = f x := by
  induction p with
  | nil => simp at hx
  | cons y ys ih =>
    have hnd0 : (y.1 :: PNet.allIds ys).Nodup := hnd
    have hy : y.1 ∉ PNet.allIds ys := (List.nodup_cons.1 hnd0).1
    have hnd' : (PNet.allIds ys).Nodup := (List.nodup_cons.1 hnd0).2
    rcases List.mem_cons.1 hx with rfl | hxs
    · simp
    · have hne : y.1 ≠ x.1 := by
        intro he
        exact hy (he ▸ List.mem_map_of_mem hxs)
      rw [List.foldr_cons, if_neg hne]
      exact ih hxs hnd'

theorem label_eq_of_head {p : PNet} {x : PItem} {i : ℕ} (hx : x ∈ p) (hi : x.1 = i)
    (hnd : p.allIds.Nodup) : p.label i = TnDesc.ofPair x.2.1 := by
  subst hi
  exact foldr_eq_of_mem (fun y => TnDesc.ofPair y.2.1) _ hx hnd

theorem deps_eq_of_mem {p : PNet} {x : PItem} (hx : x ∈ p) (hnd : p.allIds.Nodup) :
    p.deps x.1 = x.2.2.2 :=
  foldr_eq_of_mem (fun y => y.2.2.2) _ hx hnd

/-- **The invariant of a search network.** -/
structure Ok (p : PNet) : Prop where
  /-- The identifiers are pairwise distinct. -/
  nodup : p.allIds.Nodup
  /-- A processed task has no predecessors left. -/
  absent : ∀ x ∈ p, x.2.2.1 = false → x.2.2.2 = []
  /-- Every predecessor is a task still to be processed. -/
  deps_sub : ∀ x ∈ p, ∀ j ∈ x.2.2.2, j ∈ p.ids
  /-- No task precedes itself. -/
  irrefl : ∀ x ∈ p, x.1 ∉ x.2.2.2
  /-- The predecessor lists are transitively closed. -/
  trans : ∀ x ∈ p, ∀ j ∈ x.2.2.2, ∀ k ∈ p.deps j, k ∈ x.2.2.2

/-- The item an identifier that has predecessors belongs to. -/
theorem exists_item_of_mem_deps {p : PNet} {i j : ℕ} (hj : j ∈ p.deps i) :
    ∃ x ∈ p, x.1 = i ∧ j ∈ x.2.2.2 := by
  induction p with
  | nil => simp [deps] at hj
  | cons y ys ih =>
    by_cases hy : y.1 = i
    · refine ⟨y, List.mem_cons_self, hy, ?_⟩
      rw [show PNet.deps (y :: ys) i = y.2.2.2 by simp [deps, hy]] at hj
      exact hj
    · rw [show PNet.deps (y :: ys) i = PNet.deps ys i by simp [deps, hy]] at hj
      obtain ⟨x, hx, hxi, hjx⟩ := ih hj
      exact ⟨x, List.mem_cons_of_mem _ hx, hxi, hjx⟩

theorem mem_ids_of_mem_deps {p : PNet} (h : Ok p) {i j : ℕ} (hj : j ∈ p.deps i) : j ∈ p.ids := by
  obtain ⟨x, hx, -, hjx⟩ := exists_item_of_mem_deps hj
  exact h.deps_sub x hx j hjx

theorem mem_ids_of_deps_ne_nil {p : PNet} (h : Ok p) {i : ℕ} {j : ℕ} (hj : j ∈ p.deps i) :
    i ∈ p.ids := by
  obtain ⟨x, hx, hxi, hjx⟩ := exists_item_of_mem_deps hj
  refine mem_ids.2 ⟨x, hx, hxi, ?_⟩
  by_contra hpres
  have : x.2.2.1 = false := by
    cases hp : x.2.2.1 with
    | false => rfl
    | true => exact absurd hp hpres
  rw [h.absent x hx this] at hjx
  simp at hjx

/-- **The denoted task network is well formed.** -/
theorem toTN_wf {p : PNet} (h : Ok p) : (toTN p).WF where
  mem_left := fun hab => List.mem_toFinset.2 (mem_ids_of_mem_deps h hab)
  mem_right := fun hab => List.mem_toFinset.2 (mem_ids_of_deps_ne_nil h hab)
  irrefl := by
    intro i hi
    have hi' : i ∈ p.deps i := hi
    have := mem_ids_of_deps_ne_nil h hi'
    obtain ⟨x, hx, rfl, -⟩ := mem_ids.1 this
    exact h.irrefl x hx (by rwa [deps_eq_of_mem hx h.nodup] at hi')
  trans := by
    intro a b c hab hbc
    have hab' : a ∈ p.deps b := hab
    have hbc' : b ∈ p.deps c := hbc
    have hc := mem_ids_of_deps_ne_nil h hbc'
    obtain ⟨x, hx, hxc, -⟩ := mem_ids.1 hc
    subst hxc
    show a ∈ p.deps x.1
    rw [deps_eq_of_mem hx h.nodup] at hbc' ⊢
    exact h.trans x hx b hbc' a hab'

@[simp] theorem deps_cons (x : PItem) (xs : PNet) (j : ℕ) :
    PNet.deps (x :: xs) j = if x.1 = j then x.2.2.2 else PNet.deps xs j := rfl

@[simp] theorem label_cons (x : PItem) (xs : PNet) (j : ℕ) :
    PNet.label (x :: xs) j =
      if x.1 = j then TnDesc.ofPair x.2.1 else PNet.label xs j := rfl

@[simp] theorem allIds_cons (x : PItem) (xs : PNet) :
    PNet.allIds (x :: xs) = x.1 :: PNet.allIds xs := rfl

theorem allIds_append (p q : PNet) : (p ++ q).allIds = p.allIds ++ q.allIds := by
  simp [allIds]

theorem deps_append (p q : PNet) (j : ℕ) :
    PNet.deps (p ++ q) j = if j ∈ p.allIds then p.deps j else q.deps j := by
  induction p with
  | nil => simp [allIds]
  | cons x xs ih =>
    rw [List.cons_append, deps_cons, deps_cons, ih]
    by_cases hx : x.1 = j
    · simp [hx]
    · by_cases hj : j ∈ PNet.allIds xs <;> simp [hx, hj, Ne.symm hx]

theorem label_append (p q : PNet) (j : ℕ) :
    PNet.label (p ++ q) j = if j ∈ p.allIds then p.label j else q.label j := by
  induction p with
  | nil => simp [allIds]
  | cons x xs ih =>
    rw [List.cons_append, label_cons, label_cons, ih]
    by_cases hx : x.1 = j
    · simp [hx]
    · by_cases hj : j ∈ PNet.allIds xs <;> simp [hx, hj, Ne.symm hx]

theorem mem_ids_append {p q : PNet} {j : ℕ} :
    j ∈ (p ++ q).ids ↔ j ∈ p.ids ∨ j ∈ q.ids := by
  simp only [ids, List.filter_append, List.map_append, List.mem_append]

theorem allIds_map {p : PNet} {f : PItem → PItem} (hf : ∀ x, (f x).1 = x.1) :
    PNet.allIds (p.map f) = p.allIds := by
  simp only [allIds, List.map_map]
  exact List.map_congr_left fun x _ => hf x

theorem label_eq_default_of_not_mem {p : PNet} {i : ℕ} (h : i ∉ p.allIds) :
    p.label i = Sum.inl 0 := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.1 ≠ i := fun hxi => h (by simp [allIds, hxi])
    have hxs : i ∉ PNet.allIds xs := fun hm => h (by
      simp only [allIds, List.map_cons, List.mem_cons]
      exact Or.inr hm)
    simp only [label, List.foldr_cons, if_neg hx]
    exact ih hxs

/-! ### The initial search network -/

/-- Every identifier a described task network mentions, as a task or as the subject of a
label. -/
def keysOf (t : TnDesc) : List ℕ := (t.ids ++ t.lbl.map (fun q => q.1)).dedup

theorem mem_keysOf_of_mem_ids {t : TnDesc} {x : ℕ} (h : x ∈ t.ids) : x ∈ keysOf t := by
  simp [keysOf, h]

theorem label_eq_default_of_not_mem_keysOf {t : TnDesc} {x : ℕ} (h : x ∉ keysOf t) :
    t.label x = Sum.inl 0 := by
  have hx : x ∉ t.lbl.map (fun q => q.1) := fun hm => h (by simp [keysOf, hm])
  have : t.lbl.lookup x = none := by
    rcases hl : t.lbl.lookup x with _ | v
    · rfl
    · exact absurd (List.mem_map_of_mem (mem_of_lookup_eq_some hl)) hx
  simp [TnDesc.label, this]

/-- The search network a described task network starts the search with. -/
def ofTnDesc (t : TnDesc) : PNet :=
  (keysOf t).map (fun x =>
    (x, t.lblPair x, memB t.ids x, t.ids.dedup.filter (fun y => t.ordB y x)))

@[simp] theorem allIds_ofTnDesc (t : TnDesc) : (ofTnDesc t).allIds = keysOf t := by
  simp [allIds, ofTnDesc, List.map_map, Function.comp_def]

theorem nodup_ofTnDesc (t : TnDesc) : (ofTnDesc t).allIds.Nodup := by
  rw [allIds_ofTnDesc]
  exact List.nodup_dedup _

theorem mem_ids_ofTnDesc {t : TnDesc} {x : ℕ} : x ∈ (ofTnDesc t).ids ↔ x ∈ t.ids := by
  constructor
  · intro h
    obtain ⟨y, hy, hy1, hpres⟩ := mem_ids.1 h
    simp only [ofTnDesc, List.mem_map] at hy
    obtain ⟨z, -, rfl⟩ := hy
    simp only at hy1 hpres
    subst hy1
    simpa using hpres
  · intro h
    refine mem_ids.2 ⟨(x, t.lblPair x, memB t.ids x, t.ids.dedup.filter (fun y => t.ordB y x)),
      ?_, rfl, by simpa using h⟩
    exact List.mem_map_of_mem (mem_keysOf_of_mem_ids h)

theorem deps_ofTnDesc (t : TnDesc) (x : ℕ) :
    (ofTnDesc t).deps x = t.ids.dedup.filter (fun y => t.ordB y x) := by
  by_cases hx : x ∈ keysOf t
  · have hmem : (x, t.lblPair x, memB t.ids x, t.ids.dedup.filter (fun y => t.ordB y x))
        ∈ ofTnDesc t := List.mem_map_of_mem hx
    exact deps_eq_of_mem hmem (nodup_ofTnDesc t)
  · have hnil : (ofTnDesc t).deps x = [] :=
      deps_eq_nil_of_not_mem (by rwa [allIds_ofTnDesc])
    have hx' : x ∉ t.ids := fun hm => hx (mem_keysOf_of_mem_ids hm)
    rw [hnil]
    symm
    rw [List.filter_eq_nil_iff]
    intro y hy hord
    exact hx' ((TnDesc.ordB_iff.1 hord).2.1)

theorem label_ofTnDesc (t : TnDesc) (x : ℕ) : (ofTnDesc t).label x = t.label x := by
  by_cases hx : x ∈ keysOf t
  · have hmem : (x, t.lblPair x, memB t.ids x, t.ids.dedup.filter (fun y => t.ordB y x))
        ∈ ofTnDesc t := List.mem_map_of_mem hx
    rw [label_eq_of_head hmem rfl (nodup_ofTnDesc t)]
    exact TnDesc.ofPair_lblPair t x
  · rw [label_eq_default_of_not_mem (by rwa [allIds_ofTnDesc]),
      label_eq_default_of_not_mem_keysOf hx]

theorem ofTnDesc_ok (t : TnDesc) : Ok (ofTnDesc t) where
  nodup := nodup_ofTnDesc t
  absent := by
    intro x hx hpres
    simp only [ofTnDesc, List.mem_map] at hx
    obtain ⟨z, -, rfl⟩ := hx
    simp only at hpres ⊢
    rw [List.filter_eq_nil_iff]
    intro y hy hord
    have hz : z ∉ t.ids := by
      intro hm
      rw [memB_iff.2 hm] at hpres
      exact Bool.noConfusion hpres
    exact absurd ((TnDesc.ordB_iff.1 hord).2.1) hz
  deps_sub := by
    intro x hx j hj
    simp only [ofTnDesc, List.mem_map] at hx
    obtain ⟨z, -, rfl⟩ := hx
    simp only [List.mem_filter, List.mem_dedup] at hj
    exact mem_ids_ofTnDesc.2 hj.1
  irrefl := by
    intro x hx
    simp only [ofTnDesc, List.mem_map] at hx
    obtain ⟨z, -, rfl⟩ := hx
    intro hmem
    exact (t.toTaskNetwork_wf).irrefl z
      (TnDesc.ordB_iff.1 (List.mem_filter.1 hmem).2)
  trans := by
    intro x hx j hj k hk
    simp only [ofTnDesc, List.mem_map] at hx
    obtain ⟨z, -, rfl⟩ := hx
    simp only [List.mem_filter, List.mem_dedup] at hj ⊢
    rw [deps_ofTnDesc] at hk
    simp only [List.mem_filter, List.mem_dedup] at hk
    refine ⟨hk.1, ?_⟩
    exact TnDesc.ordB_iff.2 ((t.toTaskNetwork_wf).trans (TnDesc.ordB_iff.1 hk.2)
      (TnDesc.ordB_iff.1 hj.2))

/-- **The initial search network denotes the described task network.** -/
theorem toTN_ofTnDesc (t : TnDesc) : toTN (ofTnDesc t) = t.toTaskNetwork := by
  refine TaskNetwork.ext' ?_ ?_ ?_
  · ext x
    simp only [toTN_T, List.mem_toFinset, TnDesc.toTaskNetwork_T]
    exact mem_ids_ofTnDesc
  · funext a b
    apply propext
    rw [show (toTN (ofTnDesc t)).ord a b ↔ a ∈ (ofTnDesc t).deps b from Iff.rfl,
      deps_ofTnDesc]
    simp only [List.mem_filter, List.mem_dedup, TnDesc.ordB_iff]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨h.1, h⟩
  · funext x
    exact label_ofTnDesc t x

/-! ### Progression -/

/-- **Progression**: the task `i` is processed. -/
def finish (p : PNet) (i : ℕ) : PNet :=
  p.map (fun x => if x.1 = i then (x.1, x.2.1, false, ([] : List ℕ))
    else (x.1, x.2.1, x.2.2.1, x.2.2.2.filter (fun y => y ≠ i)))

@[simp] theorem allIds_finish (p : PNet) (i : ℕ) : (p.finish i).allIds = p.allIds := by
  simp only [finish, allIds, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  by_cases h : x.1 = i <;> simp [h]

theorem deps_finish (p : PNet) (i j : ℕ) :
    (p.finish i).deps j = if j = i then [] else (p.deps j).filter (fun y => y ≠ i) := by
  induction p with
  | nil =>
    by_cases h : j = i <;> simp [finish, deps, h]
  | cons x xs ih =>
    have hmap : PNet.finish (x :: xs) i =
        (if x.1 = i then (x.1, x.2.1, false, ([] : List ℕ))
          else (x.1, x.2.1, x.2.2.1, x.2.2.2.filter (fun y => y ≠ i))) :: PNet.finish xs i := rfl
    rw [hmap]
    by_cases hxi : x.1 = i
    · rw [if_pos hxi, deps_cons, deps_cons, ih]
      simp only
      by_cases hxj : x.1 = j
      · have hji : j = i := hxj ▸ hxi
        simp [hxj, hji]
      · simp [hxj]
    · rw [if_neg hxi, deps_cons, deps_cons, ih]
      simp only
      by_cases hxj : x.1 = j
      · subst hxj
        simp [hxi]
      · simp [hxj]

theorem label_finish (p : PNet) (i j : ℕ) : (p.finish i).label j = p.label j := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    have hmap : PNet.finish (x :: xs) i =
        (if x.1 = i then (x.1, x.2.1, false, ([] : List ℕ))
          else (x.1, x.2.1, x.2.2.1, x.2.2.2.filter (fun y => y ≠ i))) :: PNet.finish xs i := rfl
    rw [hmap, label_cons, label_cons, ih]
    by_cases hxi : x.1 = i <;> simp [hxi]

theorem mem_ids_finish {p : PNet} {i j : ℕ} : j ∈ (p.finish i).ids ↔ j ∈ p.ids ∧ j ≠ i := by
  constructor
  · intro hj
    obtain ⟨y, hy, hy1, hpres⟩ := mem_ids.1 hj
    simp only [finish, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    by_cases hzi : z.1 = i
    · rw [if_pos hzi] at hpres
      exact absurd hpres (by simp)
    · rw [if_neg hzi] at hy1 hpres
      simp only at hy1 hpres
      subst hy1
      exact ⟨mem_ids.2 ⟨z, hz, rfl, hpres⟩, hzi⟩
  · rintro ⟨hj, hji⟩
    obtain ⟨z, hz, rfl, hpres⟩ := mem_ids.1 hj
    refine mem_ids.2 ⟨(z.1, z.2.1, z.2.2.1, z.2.2.2.filter (fun y => y ≠ i)), ?_, rfl, hpres⟩
    have : (fun x : PItem => if x.1 = i then (x.1, x.2.1, false, ([] : List ℕ))
        else (x.1, x.2.1, x.2.2.1, x.2.2.2.filter (fun y => y ≠ i))) z =
        (z.1, z.2.1, z.2.2.1, z.2.2.2.filter (fun y => y ≠ i)) := by
      simp [hji]
    exact this ▸ List.mem_map_of_mem hz

theorem finish_ok {p : PNet} (h : Ok p) (i : ℕ) : Ok (p.finish i) where
  nodup := by rw [allIds_finish]; exact h.nodup
  absent := by
    intro x hx hpres
    simp only [finish, List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    by_cases hzi : z.1 = i
    · simp [hzi]
    · rw [if_neg hzi] at hpres ⊢
      simp only at hpres ⊢
      rw [h.absent z hz hpres]
      rfl
  deps_sub := by
    intro x hx j hj
    simp only [finish, List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    by_cases hzi : z.1 = i
    · rw [if_pos hzi] at hj
      simp at hj
    · rw [if_neg hzi] at hj
      simp only [List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at hj
      exact mem_ids_finish.2 ⟨h.deps_sub z hz j hj.1, hj.2⟩
  irrefl := by
    intro x hx
    simp only [finish, List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    by_cases hzi : z.1 = i
    · simp [hzi]
    · rw [if_neg hzi]
      simp only
      intro hmem
      exact h.irrefl z hz (List.mem_filter.1 hmem).1
  trans := by
    intro x hx j hj k hk
    simp only [finish, List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    by_cases hzi : z.1 = i
    · rw [if_pos hzi] at hj
      simp at hj
    · rw [if_neg hzi] at hj ⊢
      simp only [List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at hj ⊢
      rw [deps_finish] at hk
      by_cases hji : j = i
      · exact absurd hji hj.2
      · rw [if_neg hji] at hk
        simp only [List.mem_filter, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not] at hk
        exact ⟨h.trans z hz j hj.1 k hk.1, hk.2⟩

/-- **Progression denotes progression.** -/
theorem toTN_finish {p : PNet} {i : ℕ} (hd : p.deps i = []) :
    toTN (p.finish i) = (toTN p).progress i := by
  refine TaskNetwork.ext' ?_ ?_ ?_
  · ext x
    simp only [toTN_T, List.mem_toFinset, TaskNetwork.progress_T, Finset.mem_erase]
    rw [mem_ids_finish]
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  · funext a b
    apply propext
    show a ∈ (p.finish i).deps b ↔ (a ∈ p.deps b ∧ a ≠ i)
    rw [deps_finish]
    by_cases hbi : b = i
    · subst hbi
      rw [if_pos rfl, hd]
      simp
    · rw [if_neg hbi]
      simp
  · funext x
    exact label_finish p i x

/-! ### Decomposition -/

/-- An offset larger than every identifier the search network mentions. -/
def freshOff (p : PNet) : ℕ := p.allIds.foldr Nat.max 0 + 1

theorem lt_freshOff {p : PNet} {i : ℕ} (h : i ∈ p.allIds) : i < p.freshOff := by
  have hle : ∀ (l : List ℕ), i ∈ l → i ≤ l.foldr Nat.max 0 := by
    intro l
    induction l with
    | nil => simp
    | cons y ys ih =>
      intro hm
      have hstep : (y :: ys).foldr Nat.max 0 = Nat.max y (ys.foldr Nat.max 0) := rfl
      rcases List.mem_cons.1 hm with rfl | hys
      · rw [hstep]
        exact Nat.le_max_left _ _
      · rw [hstep]
        exact le_trans (ih hys) (Nat.le_max_right _ _)
  have := hle p.allIds h
  simp only [freshOff]
  omega

/-- The identifiers the decomposition by `e` introduces. -/
def newIds (p : PNet) (e : MethodDesc) : List ℕ := e.2.ids.dedup.map (fun x => p.freshOff + x)

/-- Replacing an identifier by a list of identifiers in a list of predecessors. -/
def substDep (i : ℕ) (new : List ℕ) (l : List ℕ) : List ℕ :=
  l.flatMap (fun y => if y = i then new else [y])

theorem mem_substDep {i : ℕ} {new l : List ℕ} {y : ℕ} :
    y ∈ substDep i new l ↔ (y ∈ l ∧ y ≠ i) ∨ (i ∈ l ∧ y ∈ new) := by
  simp only [substDep, List.mem_flatMap]
  constructor
  · rintro ⟨z, hz, hy⟩
    by_cases hzi : z = i
    · subst hzi
      simp only at hy
      exact Or.inr ⟨hz, hy⟩
    · rw [if_neg hzi] at hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact Or.inl ⟨hz, hzi⟩
  · rintro (⟨hy, hyi⟩ | ⟨hi, hy⟩)
    · exact ⟨y, hy, by simp [hyi]⟩
    · exact ⟨i, hi, by simp [hy]⟩

/-- The items the decomposition by `e` introduces. -/
def newItems (p : PNet) (i : ℕ) (e : MethodDesc) : PNet :=
  e.2.ids.dedup.map (fun x =>
    (p.freshOff + x, e.2.lblPair x, true,
      p.deps i ++ (e.2.ids.dedup.filter (fun y => e.2.ordB y x)).map (fun y => p.freshOff + y)))

/-- The old items after a decomposition: the decomposed task is cleared, and every reference to
it is replaced by the identifiers the decomposition introduces. -/
def oldItems (p : PNet) (i : ℕ) (e : MethodDesc) : PNet :=
  p.map (fun x => if x.1 = i then (x.1, x.2.1, false, ([] : List ℕ))
    else (x.1, x.2.1, x.2.2.1, substDep i (p.newIds e) x.2.2.2))

/-- **Decomposition**: the compound task `i` is replaced by a fresh copy of the subtask network
of the method `e`. -/
def expand (p : PNet) (i : ℕ) (e : MethodDesc) : PNet := p.oldItems i e ++ p.newItems i e

/-! #### The identifiers a decomposition introduces -/

theorem mem_newIds {p : PNet} {e : MethodDesc} {j : ℕ} :
    j ∈ p.newIds e ↔ ∃ y ∈ e.2.ids, j = p.freshOff + y := by
  simp only [newIds, List.mem_map, List.mem_dedup]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

theorem freshOff_le_of_mem_newIds {p : PNet} {e : MethodDesc} {j : ℕ} (h : j ∈ p.newIds e) :
    p.freshOff ≤ j := by
  obtain ⟨y, -, rfl⟩ := mem_newIds.1 h
  omega

theorem not_mem_allIds_of_mem_newIds {p : PNet} {e : MethodDesc} {j : ℕ}
    (h : j ∈ p.newIds e) : j ∉ p.allIds := by
  intro hj
  have := lt_freshOff hj
  have := freshOff_le_of_mem_newIds h
  omega

theorem nodup_newIds (p : PNet) (e : MethodDesc) : (p.newIds e).Nodup := by
  refine (List.nodup_dedup _).map ?_
  intro a b hab
  simp only at hab
  omega

/-! #### The old items -/

theorem exists_item_of_mem_allIds {p : PNet} {j : ℕ} (h : j ∈ p.allIds) :
    ∃ x ∈ p, x.1 = j := by
  simpa [allIds, eq_comm] using List.mem_map.1 h

theorem deps_map_of_mem {q : PNet} {F : PItem → PItem} (hF : ∀ x, (F x).1 = x.1)
    (hnd : q.allIds.Nodup) {x : PItem} (hx : x ∈ q) :
    PNet.deps (q.map F) x.1 = (F x).2.2.2 := by
  have h1 : F x ∈ q.map F := List.mem_map_of_mem hx
  have h2 : PNet.allIds (q.map F) = q.allIds := allIds_map hF
  have h3 := deps_eq_of_mem h1 (by rw [h2]; exact hnd)
  rwa [hF x] at h3

theorem label_map_of_mem {q : PNet} {F : PItem → PItem} (hF : ∀ x, (F x).1 = x.1)
    (hnd : q.allIds.Nodup) {x : PItem} (hx : x ∈ q) :
    PNet.label (q.map F) x.1 = TnDesc.ofPair (F x).2.1 := by
  have h1 : F x ∈ q.map F := List.mem_map_of_mem hx
  have h2 : PNet.allIds (q.map F) = q.allIds := allIds_map hF
  exact label_eq_of_head h1 (hF x) (by rw [h2]; exact hnd)

theorem oldItems_fun_id (p : PNet) (i : ℕ) (e : MethodDesc) (x : PItem) :
    ((if x.1 = i then ((x.1, x.2.1, false, ([] : List ℕ)) : PItem)
      else (x.1, x.2.1, x.2.2.1, substDep i (p.newIds e) x.2.2.2))).1 = x.1 := by
  by_cases hx : x.1 = i <;> simp [hx]

@[simp] theorem allIds_oldItems (p : PNet) (i : ℕ) (e : MethodDesc) :
    (p.oldItems i e).allIds = p.allIds :=
  allIds_map (oldItems_fun_id p i e)

theorem deps_oldItems {p : PNet} (h : Ok p) (i : ℕ) (e : MethodDesc) (j : ℕ) :
    (p.oldItems i e).deps j =
      if j = i then [] else substDep i (p.newIds e) (p.deps j) := by
  by_cases hj : j ∈ p.allIds
  · obtain ⟨x, hx, rfl⟩ := exists_item_of_mem_allIds hj
    rw [oldItems, deps_map_of_mem (oldItems_fun_id p i e) h.nodup hx, deps_eq_of_mem hx h.nodup]
    by_cases hxi : x.1 = i <;> simp [hxi]
  · have h1 : (p.oldItems i e).deps j = [] :=
      deps_eq_nil_of_not_mem (by rwa [allIds_oldItems])
    have h2 : p.deps j = [] := deps_eq_nil_of_not_mem hj
    rw [h1, h2]
    by_cases hji : j = i <;> simp [hji, substDep]

theorem label_oldItems {p : PNet} (h : Ok p) (i : ℕ) (e : MethodDesc) (j : ℕ) :
    (p.oldItems i e).label j = p.label j := by
  by_cases hj : j ∈ p.allIds
  · obtain ⟨x, hx, rfl⟩ := exists_item_of_mem_allIds hj
    rw [oldItems, label_map_of_mem (oldItems_fun_id p i e) h.nodup hx,
      label_eq_of_head hx rfl h.nodup]
    by_cases hxi : x.1 = i <;> simp [hxi]
  · rw [label_eq_default_of_not_mem (by rwa [allIds_oldItems]),
      label_eq_default_of_not_mem hj]

theorem mem_ids_oldItems {p : PNet} {i j : ℕ} {e : MethodDesc} :
    j ∈ (p.oldItems i e).ids ↔ j ∈ p.ids ∧ j ≠ i := by
  constructor
  · intro hj
    obtain ⟨y, hy, hy1, hpres⟩ := mem_ids.1 hj
    simp only [oldItems, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    by_cases hzi : z.1 = i
    · rw [if_pos hzi] at hpres
      exact absurd hpres (by simp)
    · rw [if_neg hzi] at hy1 hpres
      simp only at hy1 hpres
      subst hy1
      exact ⟨mem_ids.2 ⟨z, hz, rfl, hpres⟩, hzi⟩
  · rintro ⟨hj, hji⟩
    obtain ⟨z, hz, rfl, hpres⟩ := mem_ids.1 hj
    refine mem_ids.2 ⟨(z.1, z.2.1, z.2.2.1, substDep i (p.newIds e) z.2.2.2), ?_, rfl, hpres⟩
    have hz' : (fun x : PItem => if x.1 = i then ((x.1, x.2.1, false, ([] : List ℕ)) : PItem)
        else (x.1, x.2.1, x.2.2.1, substDep i (p.newIds e) x.2.2.2)) z =
        (z.1, z.2.1, z.2.2.1, substDep i (p.newIds e) z.2.2.2) := by
      simp [hji]
    exact hz' ▸ List.mem_map_of_mem hz

/-! #### The new items -/

@[simp] theorem allIds_newItems (p : PNet) (i : ℕ) (e : MethodDesc) :
    (p.newItems i e).allIds = p.newIds e := by
  simp [allIds, newItems, newIds, List.map_map, Function.comp_def]

theorem mem_ids_newItems {p : PNet} {i j : ℕ} {e : MethodDesc} :
    j ∈ (p.newItems i e).ids ↔ j ∈ p.newIds e := by
  constructor
  · intro hj
    obtain ⟨y, hy, hy1, -⟩ := mem_ids.1 hj
    rw [← hy1]
    have : y.1 ∈ (p.newItems i e).allIds := List.mem_map_of_mem hy
    rwa [allIds_newItems] at this
  · intro hj
    obtain ⟨y, hy, rfl⟩ := mem_newIds.1 hj
    have hy' : y ∈ e.2.ids.dedup := List.mem_dedup.2 hy
    exact mem_ids.2 ⟨_, List.mem_map_of_mem hy', rfl, rfl⟩

theorem deps_newItems {p : PNet} {i : ℕ} {e : MethodDesc} {x : ℕ} (hx : x ∈ e.2.ids.dedup) :
    (p.newItems i e).deps (p.freshOff + x) =
      p.deps i ++ (e.2.ids.dedup.filter (fun y => e.2.ordB y x)).map (fun y => p.freshOff + y) := by
  have hmem : ((p.freshOff + x, e.2.lblPair x, true,
      p.deps i ++ (e.2.ids.dedup.filter (fun y => e.2.ordB y x)).map
        (fun y => p.freshOff + y)) : PItem) ∈ p.newItems i e := List.mem_map_of_mem hx
  exact deps_eq_of_mem hmem (by rw [allIds_newItems]; exact nodup_newIds p e)

theorem label_newItems {p : PNet} {i : ℕ} {e : MethodDesc} {x : ℕ} (hx : x ∈ e.2.ids.dedup) :
    (p.newItems i e).label (p.freshOff + x) = e.2.label x := by
  have hmem : ((p.freshOff + x, e.2.lblPair x, true,
      p.deps i ++ (e.2.ids.dedup.filter (fun y => e.2.ordB y x)).map
        (fun y => p.freshOff + y)) : PItem) ∈ p.newItems i e := List.mem_map_of_mem hx
  rw [label_eq_of_head hmem rfl (by rw [allIds_newItems]; exact nodup_newIds p e)]
  exact TnDesc.ofPair_lblPair e.2 x

theorem mem_newIds_of_mem_filter {p : PNet} {e : MethodDesc} {x : ℕ} {j : ℕ}
    (h : j ∈ (e.2.ids.dedup.filter (fun y => e.2.ordB y x)).map (fun y => p.freshOff + y)) :
    j ∈ p.newIds e := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
  exact mem_newIds.2 ⟨y, List.mem_dedup.1 (List.mem_filter.1 hy).1, rfl⟩

/-! #### Decomposition preserves the invariant -/

theorem expand_ok {p : PNet} (h : Ok p) {i : ℕ} (hi : i ∈ p.ids) (e : MethodDesc) :
    Ok (p.expand i e) := by
  have hiAll : i ∈ p.allIds := mem_allIds_of_mem_ids hi
  obtain ⟨zi, hzi, hzi1⟩ := exists_item_of_mem_allIds hiAll
  have hdepsI : p.deps i = zi.2.2.2 := by rw [← hzi1]; exact deps_eq_of_mem hzi h.nodup
  have hi_not : i ∉ p.deps i := by
    rw [hdepsI, ← hzi1] at *
    exact h.irrefl zi hzi
  have hdepsAll : ∀ j, ∀ k ∈ p.deps j, k ∈ p.ids := fun j k hk => mem_ids_of_mem_deps h hk
  have hdepsNe : ∀ k ∈ p.deps i, k ≠ i := by
    intro k hk hki
    exact hi_not (hki ▸ hk)
  have htransI : ∀ j ∈ p.deps i, ∀ k ∈ p.deps j, k ∈ p.deps i := by
    intro j hj k hk
    rw [hdepsI] at hj ⊢
    exact h.trans zi hzi j hj k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [expand, allIds_append, allIds_oldItems, allIds_newItems]
    refine List.Nodup.append h.nodup (nodup_newIds p e) ?_
    intro a ha hb
    exact absurd ha (not_mem_allIds_of_mem_newIds hb)
  · intro x hx hpres
    rcases List.mem_append.1 hx with hx | hx
    · simp only [oldItems, List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      by_cases hzi2 : z.1 = i
      · simp [hzi2]
      · rw [if_neg hzi2] at hpres ⊢
        simp only at hpres ⊢
        rw [h.absent z hz hpres]
        rfl
    · simp only [newItems, List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      simp at hpres
  · intro x hx j hj
    rcases List.mem_append.1 hx with hx | hx
    · simp only [oldItems, List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      by_cases hzi2 : z.1 = i
      · rw [if_pos hzi2] at hj
        simp at hj
      · rw [if_neg hzi2] at hj
        simp only at hj
        rcases mem_substDep.1 hj with ⟨hjz, hji⟩ | ⟨-, hjn⟩
        · exact mem_ids_append.2 (Or.inl (mem_ids_oldItems.2 ⟨h.deps_sub z hz j hjz, hji⟩))
        · exact mem_ids_append.2 (Or.inr (mem_ids_newItems.2 hjn))
    · simp only [newItems, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only at hj
      rcases List.mem_append.1 hj with hj | hj
      · exact mem_ids_append.2 (Or.inl (mem_ids_oldItems.2 ⟨hdepsAll i j hj, hdepsNe j hj⟩))
      · exact mem_ids_append.2 (Or.inr (mem_ids_newItems.2 (mem_newIds_of_mem_filter hj)))
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · simp only [oldItems, List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      by_cases hzi2 : z.1 = i
      · simp [hzi2]
      · rw [if_neg hzi2]
        simp only
        intro hmem
        rcases mem_substDep.1 hmem with ⟨hz1, -⟩ | ⟨-, hz1⟩
        · exact h.irrefl z hz hz1
        · exact not_mem_allIds_of_mem_newIds hz1 (List.mem_map_of_mem hz)
    · simp only [newItems, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only
      intro hmem
      rcases List.mem_append.1 hmem with hm | hm
      · have h1 : p.freshOff + y ∈ p.ids := hdepsAll i _ hm
        have := lt_freshOff (mem_allIds_of_mem_ids h1)
        omega
      · obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hm
        have hwy : w = y := by omega
        subst hwy
        exact (e.2.toTaskNetwork_wf).irrefl w (TnDesc.ordB_iff.1 (List.mem_filter.1 hw).2)
  · intro x hx j hj k hk
    have hdepsExp : ∀ j : ℕ, (p.expand i e).deps j =
        if j ∈ p.allIds then (p.oldItems i e).deps j else (p.newItems i e).deps j := by
      intro j
      rw [expand, deps_append, allIds_oldItems]
    rcases List.mem_append.1 hx with hx | hx
    · simp only [oldItems, List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      by_cases hzi2 : z.1 = i
      · rw [if_pos hzi2] at hj
        simp at hj
      · rw [if_neg hzi2] at hj ⊢
        simp only at hj ⊢
        rcases mem_substDep.1 hj with ⟨hjz, hji⟩ | ⟨hiz, hjn⟩
        · have hjAll : j ∈ p.allIds :=
            mem_allIds_of_mem_ids (h.deps_sub z hz j hjz)
          rw [hdepsExp, if_pos hjAll, deps_oldItems h, if_neg hji] at hk
          rcases mem_substDep.1 hk with ⟨hkj, hki⟩ | ⟨hij, hkn⟩
          · exact mem_substDep.2 (Or.inl ⟨h.trans z hz j hjz k hkj, hki⟩)
          · exact mem_substDep.2 (Or.inr ⟨h.trans z hz j hjz i hij, hkn⟩)
        · have hjAll : j ∉ p.allIds := not_mem_allIds_of_mem_newIds hjn
          obtain ⟨y, hy, rfl⟩ := mem_newIds.1 hjn
          rw [hdepsExp, if_neg hjAll, deps_newItems (List.mem_dedup.2 hy)] at hk
          rcases List.mem_append.1 hk with hk | hk
          · exact mem_substDep.2 (Or.inl ⟨h.trans z hz i hiz k hk, hdepsNe k hk⟩)
          · exact mem_substDep.2 (Or.inr ⟨hiz, mem_newIds_of_mem_filter hk⟩)
    · simp only [newItems, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only at hj ⊢
      rcases List.mem_append.1 hj with hj | hj
      · have hjAll : j ∈ p.allIds := mem_allIds_of_mem_ids (hdepsAll i j hj)
        rw [hdepsExp, if_pos hjAll, deps_oldItems h, if_neg (hdepsNe j hj)] at hk
        rcases mem_substDep.1 hk with ⟨hkj, -⟩ | ⟨hij, -⟩
        · exact List.mem_append.2 (Or.inl (htransI j hj k hkj))
        · exact absurd (htransI j hj i hij) hi_not
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hj
        have hwd : w ∈ e.2.ids.dedup := (List.mem_filter.1 hw).1
        rw [hdepsExp, if_neg (not_mem_allIds_of_mem_newIds
          (mem_newIds.2 ⟨w, List.mem_dedup.1 hwd, rfl⟩)), deps_newItems hwd] at hk
        rcases List.mem_append.1 hk with hk | hk
        · exact List.mem_append.2 (Or.inl hk)
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
          refine List.mem_append.2 (Or.inr (List.mem_map_of_mem ?_))
          refine List.mem_filter.2 ⟨(List.mem_filter.1 hv).1, ?_⟩
          exact TnDesc.ordB_iff.2 ((e.2.toTaskNetwork_wf).trans
            (TnDesc.ordB_iff.1 (List.mem_filter.1 hv).2)
            (TnDesc.ordB_iff.1 (List.mem_filter.1 hw).2))

/-- The inserted copy is fresh. -/
theorem disjoint_shift (p : PNet) (e : MethodDesc) :
    Disjoint (toTN p).T ((TnDesc.shift p.freshOff e.2).toTaskNetwork).T := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [toTN_T, List.mem_toFinset] at ha
  simp only [TnDesc.toTaskNetwork_T, List.mem_toFinset] at hb
  obtain ⟨y, -, rfl⟩ := TnDesc.mem_shift_ids.1 hb
  have := lt_freshOff (mem_allIds_of_mem_ids ha)
  omega

theorem mem_shift_T_iff {p : PNet} {e : MethodDesc} {a : ℕ} :
    a ∈ ((TnDesc.shift p.freshOff e.2).toTaskNetwork).T ↔ a ∈ p.newIds e := by
  simp only [TnDesc.toTaskNetwork_T, List.mem_toFinset]
  rw [TnDesc.mem_shift_ids, mem_newIds]

/-- **Decomposition denotes decomposition** — with the shift of the method's description by
`freshOff p` as the fresh copy of its subtask network. -/
theorem toTN_expand {p : PNet} (h : Ok p) {i : ℕ} (hi : i ∈ p.ids) (e : MethodDesc) :
    toTN (p.expand i e) =
      decomposeWith (toTN p) i ((TnDesc.shift p.freshOff e.2).toTaskNetwork) := by
  have hiAll : i ∈ p.allIds := mem_allIds_of_mem_ids hi
  have hi_not : i ∉ p.deps i := by
    obtain ⟨zi, hzi, hzi1⟩ := exists_item_of_mem_allIds hiAll
    have : p.deps i = zi.2.2.2 := by rw [← hzi1]; exact deps_eq_of_mem hzi h.nodup
    rw [this, ← hzi1]
    exact h.irrefl zi hzi
  have hdepsExp : ∀ j : ℕ, (p.expand i e).deps j =
      if j ∈ p.allIds then (p.oldItems i e).deps j else (p.newItems i e).deps j := by
    intro j
    rw [expand, deps_append, allIds_oldItems]
  refine TaskNetwork.ext' ?_ ?_ ?_
  · ext a
    simp only [toTN_T, List.mem_toFinset, decomposeWith_T, Finset.mem_union, Finset.mem_erase]
    rw [show a ∈ (p.expand i e).ids ↔ _ from mem_ids_append]
    rw [mem_ids_oldItems, mem_ids_newItems, mem_shift_T_iff]
    exact ⟨fun hx => hx.imp (fun hy => ⟨hy.2, hy.1⟩) id,
      fun hx => hx.imp (fun hy => ⟨hy.2, hy.1⟩) id⟩
  · funext a b
    apply propext
    show a ∈ (p.expand i e).deps b ↔ _
    rw [decomposeWith_ord_iff]
    by_cases hbnew : b ∈ p.newIds e
    · obtain ⟨y, hy, rfl⟩ := mem_newIds.1 hbnew
      rw [hdepsExp, if_neg (not_mem_allIds_of_mem_newIds hbnew),
        deps_newItems (List.mem_dedup.2 hy)]
      have hbT : (p.freshOff + y) ∈ ((TnDesc.shift p.freshOff e.2).toTaskNetwork).T :=
        mem_shift_T_iff.2 hbnew
      have hbold : p.deps (p.freshOff + y) = [] :=
        deps_eq_nil_of_not_mem (not_mem_allIds_of_mem_newIds hbnew)
      constructor
      · intro hmem
        rcases List.mem_append.1 hmem with hm | hm
        · exact Or.inr (Or.inl ⟨hm, hbT⟩)
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
          refine Or.inl ?_
          exact TnDesc.shift_ord.2 (TnDesc.ordB_iff.1 (List.mem_filter.1 hw).2)
      · rintro (hord | ⟨ha, -⟩ | ⟨hib, -⟩ | ⟨hab, -, -⟩)
        · obtain ⟨a', b', rfl, hb'⟩ := TnDesc.shift_ord_mem hord
          have hby : b' = y := by omega
          subst hby
          refine List.mem_append.2 (Or.inr (List.mem_map_of_mem ?_))
          have hord' : e.2.toTaskNetwork.ord a' b' := TnDesc.shift_ord.1 hord
          exact List.mem_filter.2 ⟨List.mem_dedup.2 hord'.1, TnDesc.ordB_iff.2 hord'⟩
        · exact List.mem_append.2 (Or.inl ha)
        · have hib' : i ∈ p.deps (p.freshOff + y) := hib
          rw [hbold] at hib'
          simp at hib'
        · have hab' : a ∈ p.deps (p.freshOff + y) := hab
          rw [hbold] at hab'
          simp at hab'
    · have hbT : b ∉ ((TnDesc.shift p.freshOff e.2).toTaskNetwork).T := fun hb =>
        hbnew (mem_shift_T_iff.1 hb)
      by_cases hbold : b ∈ p.allIds
      · rw [hdepsExp, if_pos hbold, deps_oldItems h]
        by_cases hbi : b = i
        · subst hbi
          rw [if_pos rfl]
          refine iff_of_false (by simp) ?_
          rintro (hord | ⟨-, hb⟩ | ⟨hbb, -⟩ | ⟨-, -, hne⟩)
          · exact hbT ((TnDesc.toTaskNetwork_wf _).mem_right hord)
          · exact hbT hb
          · exact hi_not hbb
          · exact hne rfl
        · rw [if_neg hbi]
          constructor
          · intro hmem
            rcases mem_substDep.1 hmem with ⟨hab, hai⟩ | ⟨hib, han⟩
            · exact Or.inr (Or.inr (Or.inr ⟨hab, hai, hbi⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨hib, mem_shift_T_iff.2 han⟩))
          · rintro (hord | ⟨-, hb⟩ | ⟨hib, ha⟩ | ⟨hab, hai, -⟩)
            · exact absurd ((TnDesc.toTaskNetwork_wf _).mem_right hord) hbT
            · exact absurd hb hbT
            · exact mem_substDep.2 (Or.inr ⟨hib, mem_shift_T_iff.1 ha⟩)
            · exact mem_substDep.2 (Or.inl ⟨hab, hai⟩)
      · have hbnil : p.deps b = [] := deps_eq_nil_of_not_mem hbold
        rw [hdepsExp, if_neg hbold]
        have hnew : (p.newItems i e).deps b = [] :=
          deps_eq_nil_of_not_mem (by rw [allIds_newItems]; exact hbnew)
        rw [hnew]
        refine iff_of_false (by simp) ?_
        rintro (hord | ⟨-, hb⟩ | ⟨hib, -⟩ | ⟨hab, -, -⟩)
        · exact hbT ((TnDesc.toTaskNetwork_wf _).mem_right hord)
        · exact hbT hb
        · have hib' : i ∈ p.deps b := hib
          rw [hbnil] at hib'
          simp at hib'
        · have hab' : a ∈ p.deps b := hab
          rw [hbnil] at hab'
          simp at hab'
  · funext x
    show (p.expand i e).label x = _
    rw [decomposeWith_α, expand, label_append, allIds_oldItems]
    by_cases hx : x ∈ p.allIds
    · rw [if_pos hx, label_oldItems h]
      have : x ∉ ((TnDesc.shift p.freshOff e.2).toTaskNetwork).T := by
        intro hmem
        have := lt_freshOff hx
        have := freshOff_le_of_mem_newIds (mem_shift_T_iff.1 hmem)
        omega
      rw [if_neg this]
      rfl
    · rw [if_neg hx]
      by_cases hxnew : x ∈ p.newIds e
      · obtain ⟨y, hy, rfl⟩ := mem_newIds.1 hxnew
        rw [if_pos (mem_shift_T_iff.2 hxnew), label_newItems (List.mem_dedup.2 hy)]
        exact (TnDesc.shift_label).symm
      · rw [if_neg (fun hmem => hxnew (mem_shift_T_iff.1 hmem)),
          label_eq_default_of_not_mem (by rw [allIds_newItems]; exact hxnew)]
        exact (label_eq_default_of_not_mem hx).symm

end PNet

end Syn

end HTN
