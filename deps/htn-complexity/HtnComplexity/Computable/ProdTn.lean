import HtnComplexity.Computable.ChainTn
import HtnComplexity.Computable.TokSource
import HtnComplexity.Regular.RegularYield
/-!
# Appending a trailing compound task to a described task network

The rooting of a *chain* of initial tasks inside a **regular** class cannot add a method whose
body is the chain — such a body has more than one compound task.  It has to fold the remaining
chain into the compound *names* instead, and the one place where a task is created is the body
of a method that leaves no compound task open: there the next task of the chain has to be
appended.

This file provides the two operations on descriptions that the product construction performs on
a method body, together with their effect on the *blocks* of the body
(`HTN.Method.HasBlock`, read off a description by `HTN.Syn.TnDesc.hasBlock_iff`):

* `HTN.Syn.TnDesc.freshId` — an identifier that the description does not mention;
* `HTN.Syn.TnDesc.appendTask t c` — the description `t` with one further task, labelled by the
  compound name `c` and ordered after every task of `t`.  Its blocks are those of `t` followed
  by the new compound task (`HTN.Syn.TnDesc.hasBlock_appendTask`);
* `HTN.Syn.TnDesc.setTail t c` — the description `t` with the name of its compound task
  replaced by `c`.  Its blocks are those of `t` with the trailing name renamed
  (`HTN.Syn.TnDesc.hasBlock_setTail`).

Both operations leave the primitive part of the body — its identifiers, its ordering and its
actions — untouched, which is why the blocks are those of `t` up to the trailing name.
-/

namespace HTN

namespace Syn

namespace TnDesc

/-- A bound on the numbers a description mentions. -/
def bound (t : TnDesc) : ℕ :=
  max (t.ids.foldr max 0)
    (max ((t.ordList.map fun p => max p.1 p.2).foldr max 0) ((t.lbl.map Prod.fst).foldr max 0))

/-- **An identifier the description does not mention.** -/
def freshId (t : TnDesc) : ℕ := t.bound + 1

theorem mem_le_foldr_max {α : Type} {f : α → ℕ} :
    ∀ {l : List α} {x : α}, x ∈ l → f x ≤ (l.map f).foldr max 0
  | [], _, hx => by simp at hx
  | y :: ys, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp
    · exact le_trans (mem_le_foldr_max (f := f) hx') (by simp)

theorem le_bound_of_mem_ids {t : TnDesc} {i : ℕ} (hi : i ∈ t.ids) : i ≤ t.bound := by
  have h : i ≤ (t.ids.foldr max 0) := by
    have := mem_le_foldr_max (f := fun x : ℕ => x) hi
    simpa using this
  exact le_trans h (le_max_left _ _)

theorem le_bound_of_mem_ordList {t : TnDesc} {p : ℕ × ℕ} (hp : p ∈ t.ordList) :
    max p.1 p.2 ≤ t.bound :=
  le_trans (mem_le_foldr_max (f := fun q : ℕ × ℕ => max q.1 q.2) hp)
    (le_trans (le_max_left _ _) (le_max_right _ _))

theorem le_bound_of_mem_lbl {t : TnDesc} {p : ℕ × Bool × ℕ} (hp : p ∈ t.lbl) : p.1 ≤ t.bound :=
  le_trans (mem_le_foldr_max (f := fun q : ℕ × Bool × ℕ => q.1) hp)
    (le_trans (le_max_right _ _) (le_max_right _ _))

theorem freshId_notMem_ids (t : TnDesc) : t.freshId ∉ t.ids := fun h => by
  have := le_bound_of_mem_ids h
  simp only [freshId] at this
  omega

theorem freshId_notMem_ordList (t : TnDesc) {p : ℕ × ℕ} (hp : p ∈ t.ordList) :
    p.1 ≠ t.freshId ∧ p.2 ≠ t.freshId := by
  have := le_bound_of_mem_ordList hp
  simp only [freshId]
  omega

theorem lookup_lbl_freshId (t : TnDesc) : t.lbl.lookup t.freshId = none := by
  rcases h : t.lbl.lookup t.freshId with _ | v
  · rfl
  · exact absurd (le_bound_of_mem_lbl (mem_of_lookup_eq_some h)) (by simp only [freshId]; omega)

/-- **The description `t` with one further task, labelled `c` and ordered last.** -/
def appendTask (t : TnDesc) (c : ℕ) : TnDesc :=
  (t.ids ++ [t.freshId], t.ordList ++ t.ids.map (fun i => (i, t.freshId)),
    t.lbl ++ [(t.freshId, true, c)])

@[simp] lemma appendTask_ids (t : TnDesc) (c : ℕ) :
    (t.appendTask c).ids = t.ids ++ [t.freshId] := rfl

@[simp] lemma appendTask_ordList (t : TnDesc) (c : ℕ) :
    (t.appendTask c).ordList = t.ordList ++ t.ids.map (fun i => (i, t.freshId)) := rfl

@[simp] lemma appendTask_lbl (t : TnDesc) (c : ℕ) :
    (t.appendTask c).lbl = t.lbl ++ [(t.freshId, true, c)] := rfl

/-- The label of an old identifier is unchanged. -/
theorem appendTask_label_of_mem {t : TnDesc} {c : ℕ} {i : ℕ} (hi : i ≠ t.freshId) :
    (t.appendTask c).label i = t.label i := by
  have hlk : (t.lbl ++ [(t.freshId, true, c)]).lookup i = t.lbl.lookup i := by
    induction t.lbl with
    | nil =>
      have hb : (i == t.freshId) = false := by simpa using hi
      simp [List.lookup_cons, hb]
    | cons p ps ih =>
      rw [List.cons_append, List.lookup_cons, List.lookup_cons]
      by_cases h : i = p.1
      · simp [h]
      · have hb : (i == p.1) = false := by simpa using h
        rw [hb]
        simpa using ih
  rw [label, label, appendTask_lbl, hlk]

/-- The label of the new identifier is the new compound name. -/
theorem appendTask_label_freshId (t : TnDesc) (c : ℕ) :
    (t.appendTask c).label t.freshId = Sum.inr c := by
  have hlk : (t.lbl ++ [(t.freshId, true, c)]).lookup t.freshId = some (true, c) := by
    rw [List.lookup_append, lookup_lbl_freshId]
    simp
  rw [label, appendTask_lbl, hlk]

/-- The first element of a nonempty list is one of its elements. -/
theorem headI_mem_of_ne_nil {l : List ℕ} (h : l ≠ []) : l.headI ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => simp

/-! ### The ordering of an extended description -/

theorem appendTask_listRel {t : TnDesc} {c a b : ℕ} :
    (t.appendTask c).listRel a b ↔ t.listRel a b ∨ (a ∈ t.ids ∧ b = t.freshId) := by
  simp only [listRel, appendTask_ordList, List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hi, rfl⟩
  · rintro (h | ⟨ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, rfl, rfl⟩

/-- The listed ordering of a description never starts at the fresh identifier. -/
theorem freshId_not_listRel {t : TnDesc} {x : ℕ} : ¬ t.listRel t.freshId x := fun h =>
  (freshId_notMem_ordList t h).1 rfl

/-- The transitive closure of the extended description agrees with the original one below the
fresh identifier. -/
theorem appendTask_preOrd_of_ne {t : TnDesc} {c : ℕ} :
    ∀ {a b : ℕ}, (t.appendTask c).preOrd a b → b ≠ t.freshId → t.preOrd a b := by
  intro a b h
  induction h with
  | single hr =>
      intro hb
      rcases appendTask_listRel.1 hr with h' | ⟨-, rfl⟩
      · exact Relation.TransGen.single h'
      · exact absurd rfl hb
  | tail hab hbc ih =>
      intro hc
      rcases appendTask_listRel.1 hbc with h' | ⟨-, rfl⟩
      · exact (ih (fun hcon => (freshId_notMem_ordList t h').1 hcon)).tail h'
      · exact absurd rfl hc

/-- The transitive closure only grows when a task is appended. -/
theorem preOrd_appendTask_of_preOrd {t : TnDesc} {c a b : ℕ} (h : t.preOrd a b) :
    (t.appendTask c).preOrd a b :=
  Relation.TransGen.mono (fun _ _ hr => appendTask_listRel.2 (Or.inl hr)) h

/-- Nothing follows the fresh identifier. -/
theorem appendTask_not_preOrd_freshId {t : TnDesc} {c x : ℕ} :
    ¬ (t.appendTask c).preOrd t.freshId x := by
  intro h
  obtain ⟨y, hy, -⟩ := Relation.TransGen.head'_iff.1 h
  rcases appendTask_listRel.1 hy with h' | ⟨hmem, -⟩
  · exact (freshId_notMem_ordList t h').1 rfl
  · exact freshId_notMem_ids t hmem

/-- **The ordering of the old tasks is unchanged.** -/
theorem appendTask_ord_iff {t : TnDesc} {c a b : ℕ} (ha : a ≠ t.freshId) (hb : b ≠ t.freshId) :
    (t.appendTask c).toTaskNetwork.ord a b ↔ t.toTaskNetwork.ord a b := by
  simp only [toTaskNetwork_ord, appendTask_ids, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hae, hbe, hab, hba⟩
    exact ⟨hae.resolve_right ha, hbe.resolve_right hb, appendTask_preOrd_of_ne hab hb,
      fun hc => hba (preOrd_appendTask_of_preOrd hc)⟩
  · rintro ⟨hae, hbe, hab, hba⟩
    exact ⟨Or.inl hae, Or.inl hbe, preOrd_appendTask_of_preOrd hab,
      fun hc => hba (appendTask_preOrd_of_ne hc ha)⟩

/-- **The new task comes last.** -/
theorem appendTask_ord_freshId {t : TnDesc} {c a : ℕ} (ha : a ∈ t.ids) :
    (t.appendTask c).toTaskNetwork.ord a t.freshId :=
  ⟨by simp [ha], by simp, Relation.TransGen.single (appendTask_listRel.2 (Or.inr ⟨ha, rfl⟩)),
    appendTask_not_preOrd_freshId⟩

/-! ### The primitive part of an extended description -/

theorem mem_ids_of_mem_appendTask_ids {t : TnDesc} {c x : ℕ}
    (hx : x ∈ (t.appendTask c).ids) (hne : x ≠ t.freshId) : x ∈ t.ids := by
  rw [appendTask_ids, List.mem_append] at hx
  exact hx.resolve_right (by simpa using hne)

theorem ne_freshId_of_mem_primIds_appendTask {t : TnDesc} {c x : ℕ}
    (hx : x ∈ primIds (t.appendTask c)) : x ≠ t.freshId := by
  rintro rfl
  obtain ⟨-, a, ha⟩ := mem_primIds.1 hx
  rw [appendTask_label_freshId] at ha
  exact absurd ha (by simp)

@[simp] theorem mem_primIds_appendTask {t : TnDesc} {c x : ℕ} :
    x ∈ primIds (t.appendTask c) ↔ x ∈ primIds t := by
  constructor
  · intro hx
    have hne : x ≠ t.freshId := ne_freshId_of_mem_primIds_appendTask hx
    obtain ⟨hmem, a, ha⟩ := mem_primIds.1 hx
    rw [appendTask_label_of_mem hne] at ha
    exact mem_primIds.2 ⟨mem_ids_of_mem_appendTask_ids hmem hne, a, ha⟩
  · intro hx
    obtain ⟨hmem, a, ha⟩ := mem_primIds.1 hx
    have hne : x ≠ t.freshId := fun hcon => freshId_notMem_ids t (hcon ▸ hmem)
    refine mem_primIds.2 ⟨by simp [hmem], a, ?_⟩
    rw [appendTask_label_of_mem hne]
    exact ha

theorem actOf_appendTask {t : TnDesc} {c x : ℕ} (hx : x ∈ primIds t) :
    actOf (t.appendTask c) x = actOf t x := by
  have hne : x ≠ t.freshId := fun hcon => freshId_notMem_ids t (hcon ▸ (mem_primIds.1 hx).1)
  exact actOf_eq (by rw [appendTask_label_of_mem hne]; exact label_actOf hx)

/-- The appended task is a compound task of the extended description. -/
theorem hasNextB_appendTask (t : TnDesc) (c : ℕ) : hasNextB (t.appendTask c) = true := by
  have hmem : c ∈ (t.appendTask c).compoundNames :=
    mem_compoundNames.2 ⟨t.freshId, by simp, appendTask_label_freshId t c⟩
  have hne : (t.appendTask c).compoundNames ≠ [] := by
    intro hcon
    rw [hcon] at hmem
    simp at hmem
  simp [hasNextB, hne]

/-- If the original description has no compound task, the appended one is its compound task. -/
theorem nextName_appendTask {t : TnDesc} (hnext : hasNextB t = false) (c : ℕ) :
    nextName (t.appendTask c) = c := by
  have hne : (t.appendTask c).compoundNames ≠ [] := by
    intro hcon
    have := hasNextB_appendTask t c
    rw [hasNextB, hcon] at this
    simp at this
  have hmem : nextName (t.appendTask c) ∈ (t.appendTask c).compoundNames :=
    headI_mem_of_ne_nil hne
  obtain ⟨i, hi, hlab⟩ := mem_compoundNames.1 hmem
  by_cases hif : i = t.freshId
  · subst hif
    rw [appendTask_label_freshId] at hlab
    exact (Sum.inr_injective hlab).symm
  · rw [appendTask_label_of_mem hif] at hlab
    exact absurd hlab (not_compound hnext (mem_ids_of_mem_appendTask_ids hi hif))

theorem tailName_appendTask {t : TnDesc} (hnext : hasNextB t = false) (c : ℕ) :
    tailName (t.appendTask c) = some c := by
  rw [tailName, hasNextB_appendTask, if_pos rfl, nextName_appendTask hnext]

/-- **An extended primitive description is regular**: the appended task is its only compound
task and it comes last. -/
theorem isRegular_appendTask {t : TnDesc} (hnext : hasNextB t = false) (c : ℕ) :
    (t.appendTask c).toTaskNetwork.IsRegular := by
  have habs : ∀ x ∈ (t.appendTask c).ids, (t.appendTask c).toTaskNetwork.IsAbstractId x →
      x = t.freshId := by
    intro x hx hax
    by_contra hne
    obtain ⟨cc, hcc⟩ := hax
    rw [show (t.appendTask c).toTaskNetwork.α x = (t.appendTask c).label x from rfl,
      appendTask_label_of_mem hne] at hcc
    exact (not_compound hnext (mem_ids_of_mem_appendTask_ids hx hne)) hcc
  constructor
  · intro x hx y hy hax hay
    rw [habs x (List.mem_toFinset.1 hx) hax, habs y (List.mem_toFinset.1 hy) hay]
  · intro x hx hax y hy hne
    rw [habs x (List.mem_toFinset.1 hx) hax] at hne ⊢
    exact appendTask_ord_freshId (mem_ids_of_mem_appendTask_ids (List.mem_toFinset.1 hy) hne)

/-! ### Renaming the compound task of a description -/

/-- **The description `t` with the name of its compound task replaced by `c`.** -/
def setTail (t : TnDesc) (c : ℕ) : TnDesc :=
  (t.ids, t.ordList, t.lbl.map fun p => (p.1, p.2.1, if p.2.1 then c else p.2.2))

@[simp] lemma setTail_ids (t : TnDesc) (c : ℕ) : (t.setTail c).ids = t.ids := rfl

@[simp] lemma setTail_ordList (t : TnDesc) (c : ℕ) : (t.setTail c).ordList = t.ordList := rfl

@[simp] lemma setTail_lbl (t : TnDesc) (c : ℕ) :
    (t.setTail c).lbl = t.lbl.map fun p => (p.1, p.2.1, if p.2.1 then c else p.2.2) := rfl

theorem lookup_setTail_lbl (l : List (ℕ × Bool × ℕ)) (c i : ℕ) :
    (l.map fun p => (p.1, p.2.1, if p.2.1 then c else p.2.2)).lookup i =
      (l.lookup i).map (fun v => (v.1, if v.1 then c else v.2)) := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨n, b, m⟩ := p
      rw [List.map_cons, List.lookup_cons, List.lookup_cons]
      by_cases h : i = n
      · subst h
        simp
      · have hb : (i == n) = false := by simpa using h
        rw [hb]
        exact ih

/-- **The labels of a renamed description**: the primitive ones are untouched, the compound one
is the new name. -/
theorem setTail_label (t : TnDesc) (c i : ℕ) :
    (t.setTail c).label i = match t.label i with
      | Sum.inl a => Sum.inl a
      | Sum.inr _ => Sum.inr c := by
  rw [label, setTail_lbl, lookup_setTail_lbl]
  rcases h : t.lbl.lookup i with _ | ⟨b, m⟩
  · simp [label, h]
  · cases b <;> simp [label, h]

theorem setTail_label_inl {t : TnDesc} {c i a : ℕ} (h : t.label i = Sum.inl a) :
    (t.setTail c).label i = Sum.inl a := by rw [setTail_label, h]

theorem setTail_label_inr {t : TnDesc} {c i c' : ℕ} (h : t.label i = Sum.inr c') :
    (t.setTail c).label i = Sum.inr c := by rw [setTail_label, h]

theorem setTail_ord (t : TnDesc) (c : ℕ) {a b : ℕ} :
    (t.setTail c).toTaskNetwork.ord a b ↔ t.toTaskNetwork.ord a b := Iff.rfl

@[simp] theorem mem_primIds_setTail {t : TnDesc} {c x : ℕ} :
    x ∈ primIds (t.setTail c) ↔ x ∈ primIds t := by
  rw [mem_primIds, mem_primIds, setTail_ids]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    rcases hcase : t.label x with a' | c'
    · exact ⟨a', rfl⟩
    · rw [setTail_label, hcase] at ha
      exact absurd ha (by simp)
  · rintro ⟨a, ha⟩
    exact ⟨a, setTail_label_inl ha⟩

theorem actOf_setTail {t : TnDesc} {c x : ℕ} (hx : x ∈ primIds t) :
    actOf (t.setTail c) x = actOf t x :=
  actOf_eq (setTail_label_inl (label_actOf hx))

theorem hasNextB_setTail (t : TnDesc) (c : ℕ) : hasNextB (t.setTail c) = hasNextB t := by
  have key : ∀ s : TnDesc, hasNextB s = true ↔ ∃ x, x ∈ s.compoundNames := by
    intro s
    simp only [hasNextB, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    constructor
    · intro h
      rcases hc : s.compoundNames with _ | ⟨a, l⟩
      · exact absurd hc (by simpa using h)
      · exact ⟨a, by simp⟩
    · rintro ⟨x, hx⟩ hcon
      rw [hcon] at hx
      simp at hx
  rcases hcase : hasNextB t with _ | _
  · rcases hcase' : hasNextB (t.setTail c) with _ | _
    · rfl
    · obtain ⟨x, hx⟩ := (key _).1 hcase'
      obtain ⟨i, hi, hlab⟩ := mem_compoundNames.1 hx
      rcases hl : t.label i with a | c'
      · rw [setTail_label, hl] at hlab
        exact absurd hlab (by simp)
      · exact absurd hl (not_compound hcase (by simpa using hi))
  · rcases hcase' : hasNextB (t.setTail c) with _ | _
    · obtain ⟨x, hx⟩ := (key _).1 hcase
      obtain ⟨i, hi, hlab⟩ := mem_compoundNames.1 hx
      have : c ∈ (t.setTail c).compoundNames :=
        mem_compoundNames.2 ⟨i, by simpa using hi, setTail_label_inr hlab⟩
      have hne : (t.setTail c).compoundNames ≠ [] := by
        intro hcon
        rw [hcon] at this
        simp at this
      exact absurd hcase' (by simp [hasNextB, List.isEmpty_iff, hne])
    · rfl

theorem nextName_setTail {t : TnDesc} (hnext : hasNextB t = true) (c : ℕ) :
    nextName (t.setTail c) = c := by
  have hnext' : hasNextB (t.setTail c) = true := by rw [hasNextB_setTail, hnext]
  have hne : (t.setTail c).compoundNames ≠ [] := by
    simpa [hasNextB, List.isEmpty_iff] using hnext'
  have hmem : nextName (t.setTail c) ∈ (t.setTail c).compoundNames := headI_mem_of_ne_nil hne
  obtain ⟨i, hi, hlab⟩ := mem_compoundNames.1 hmem
  rcases hl : t.label i with a | c'
  · rw [setTail_label, hl] at hlab
    exact absurd hlab (by simp)
  · rw [setTail_label_inr hl] at hlab
    exact (Sum.inr_injective hlab).symm

theorem tailName_setTail {t : TnDesc} (hnext : hasNextB t = true) (c : ℕ) :
    tailName (t.setTail c) = some c := by
  rw [tailName, hasNextB_setTail, hnext, if_pos rfl, nextName_setTail hnext]

/-- **Renaming the compound task preserves regularity.** -/
theorem isRegular_setTail {t : TnDesc} (hreg : t.toTaskNetwork.IsRegular) (c : ℕ) :
    (t.setTail c).toTaskNetwork.IsRegular := by
  have habs : ∀ x : ℕ, (t.setTail c).toTaskNetwork.IsAbstractId x ↔
      t.toTaskNetwork.IsAbstractId x := by
    intro x
    constructor
    · rintro ⟨cc, hcc⟩
      rcases hl : t.label x with a | c'
      · rw [show (t.setTail c).toTaskNetwork.α x = (t.setTail c).label x from rfl,
          setTail_label, hl] at hcc
        exact absurd hcc (by simp)
      · exact ⟨c', hl⟩
    · rintro ⟨c', hc'⟩
      exact ⟨c, setTail_label_inr hc'⟩
  constructor
  · intro x hx y hy hax hay
    exact hreg.1 x (by simpa using hx) y (by simpa using hy) ((habs x).1 hax) ((habs y).1 hay)
  · intro x hx hax y hy hne
    exact hreg.2 x (by simpa using hx) ((habs x).1 hax) y (by simpa using hy) hne

/-! ### The blocks of a modified body -/

/-- **The enumerations of the primitive part only depend on the primitive part.** -/
theorem primLin_congr {t t' : TnDesc} {xs : List ℕ}
    (hmem : ∀ x, x ∈ primIds t' ↔ x ∈ primIds t)
    (hord : ∀ a ∈ primIds t, ∀ b ∈ primIds t,
      (t'.toTaskNetwork.ord a b ↔ t.toTaskNetwork.ord a b)) :
    PrimLin t' xs ↔ PrimLin t xs := by
  constructor
  · rintro ⟨hnd, hmm, hp⟩
    refine ⟨hnd, fun x => (hmm x).trans (hmem x), hp.imp_of_mem ?_⟩
    intro a b ha hb hab
    exact fun hcon => hab ((hord b ((hmem b).1 ((hmm b).1 hb)) a
      ((hmem a).1 ((hmm a).1 ha))).2 hcon)
  · rintro ⟨hnd, hmm, hp⟩
    refine ⟨hnd, fun x => (hmm x).trans (hmem x).symm, hp.imp_of_mem ?_⟩
    intro a b ha hb hab
    exact fun hcon => hab ((hord b ((hmm b).1 hb) a ((hmm a).1 ha)).1 hcon)

theorem primLin_setTail {t : TnDesc} {c : ℕ} {xs : List ℕ} :
    PrimLin (t.setTail c) xs ↔ PrimLin t xs :=
  primLin_congr (fun _ => mem_primIds_setTail) (fun _ _ _ _ => setTail_ord t c)

theorem primLin_appendTask {t : TnDesc} {c : ℕ} {xs : List ℕ} :
    PrimLin (t.appendTask c) xs ↔ PrimLin t xs :=
  primLin_congr (fun _ => mem_primIds_appendTask) fun _ ha _ hb =>
    appendTask_ord_iff
      (fun hcon => freshId_notMem_ids t (hcon ▸ (mem_primIds.1 ha).1))
      (fun hcon => freshId_notMem_ids t (hcon ▸ (mem_primIds.1 hb).1))

theorem map_actOf_setTail {t : TnDesc} {c : ℕ} {xs : List ℕ} (hxs : PrimLin t xs) :
    xs.map (actOf (t.setTail c)) = xs.map (actOf t) :=
  List.map_congr_left fun x hx => actOf_setTail ((hxs.2.1 x).1 hx)

theorem map_actOf_appendTask {t : TnDesc} {c : ℕ} {xs : List ℕ} (hxs : PrimLin t xs) :
    xs.map (actOf (t.appendTask c)) = xs.map (actOf t) :=
  List.map_congr_left fun x hx => actOf_appendTask ((hxs.2.1 x).1 hx)

/-- **The blocks of a body whose compound task has been renamed.** -/
theorem hasBlock_setTail {t : TnDesc} (hreg : t.toTaskNetwork.IsRegular)
    (hnext : hasNextB t = true) (c head : ℕ) {os : List ℕ} {next : Option ℕ} :
    (MethodDesc.toMethod (head, t.setTail c)).HasBlock os next ↔
      ∃ xs : List ℕ, PrimLin t xs ∧ os = xs.map (actOf t) ∧ next = some c := by
  rw [hasBlock_iff (isRegular_setTail hreg c) head]
  constructor
  · rintro ⟨xs, hxs, hos, hnx⟩
    refine ⟨xs, primLin_setTail.1 hxs, ?_, by rw [hnx, tailName_setTail hnext]⟩
    rw [hos, map_actOf_setTail (primLin_setTail.1 hxs)]
  · rintro ⟨xs, hxs, hos, hnx⟩
    refine ⟨xs, primLin_setTail.2 hxs, ?_, by rw [hnx, tailName_setTail hnext]⟩
    rw [hos, map_actOf_setTail hxs]

/-- **The blocks of a body with a trailing compound task appended.** -/
theorem hasBlock_appendTask {t : TnDesc} (hnext : hasNextB t = false) (c head : ℕ)
    {os : List ℕ} {next : Option ℕ} :
    (MethodDesc.toMethod (head, t.appendTask c)).HasBlock os next ↔
      ∃ xs : List ℕ, PrimLin t xs ∧ os = xs.map (actOf t) ∧ next = some c := by
  rw [hasBlock_iff (isRegular_appendTask hnext c) head]
  constructor
  · rintro ⟨xs, hxs, hos, hnx⟩
    refine ⟨xs, primLin_appendTask.1 hxs, ?_, by rw [hnx, tailName_appendTask hnext]⟩
    rw [hos, map_actOf_appendTask (primLin_appendTask.1 hxs)]
  · rintro ⟨xs, hxs, hos, hnx⟩
    refine ⟨xs, primLin_appendTask.2 hxs, ?_, by rw [hnx, tailName_appendTask hnext]⟩
    rw [hos, map_actOf_appendTask hxs]

/-! ### The empty body -/

@[simp] theorem primIds_nil : primIds nil = [] := rfl

theorem primLin_nil_iff {xs : List ℕ} : PrimLin nil xs ↔ xs = [] := by
  constructor
  · rintro ⟨-, hmm, -⟩
    refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
    have := (hmm x).1 hx
    simp at this
  · rintro rfl
    exact ⟨List.nodup_nil, by simp, List.Pairwise.nil⟩

theorem isRegular_nil : (nil : TnDesc).toTaskNetwork.IsRegular := by
  refine TaskNetwork.IsPrimitive.isRegular ?_
  intro x hx
  rw [nil_toTaskNetwork_T] at hx
  simp at hx

@[simp] theorem tailName_nil : tailName nil = none := rfl

/-- **The blocks of the empty body**: no actions and no compound task. -/
theorem hasBlock_nil {head : ℕ} {os : List ℕ} {next : Option ℕ} :
    (MethodDesc.toMethod (head, nil)).HasBlock os next ↔ os = [] ∧ next = none := by
  rw [hasBlock_iff isRegular_nil head]
  constructor
  · rintro ⟨xs, hxs, hos, hnx⟩
    rw [primLin_nil_iff] at hxs
    subst hxs
    exact ⟨by simpa using hos, by rw [hnx, tailName_nil]⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨[], primLin_nil_iff.2 rfl, rfl, tailName_nil.symm⟩

end TnDesc

end Syn

end HTN
