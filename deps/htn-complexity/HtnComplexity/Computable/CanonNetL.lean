import HtnComplexity.Computable.CanonNet
/-!
# The canonical form of a described task network, with the labels kept

`HtnComplexity/Computable/CanonNet.lean` renames the identifiers of a described task
network down to their positions, but the canonical form it produces (`HTN.Syn.TnDesc.canon`) is
built from `HTN.Syn.netTn`, which labels every task with a *compound* name; that is why
`HTN.Syn.TnDesc.canon_iso` has to assume `HTN.Syn.TnDesc.AllCompound`.

This file removes the assumption.  `HTN.Syn.netTnL ls ord` is the described network of a list of
**labels** — `(true, c)` a compound name, `(false, a)` an action — and
`HTN.Syn.TnDesc.canonL t` is the canonical form of `t` built from it.  The isomorphism
`HTN.Syn.TnDesc.canonL_iso` holds for *every* description.
-/

namespace HTN

namespace Syn

/-! ### The described network of a list of labels -/

/-- **The described task network of the labels `ls` and the ordering pairs `ord`**: one task per
entry of `ls`, identified by its position. -/
def netTnL (ls : List (Bool × ℕ)) (ord : List (ℕ × ℕ)) : TnDesc :=
  (List.range ls.length, ord, (List.range ls.length).map fun i => (i, ls.getD i (false, 0)))

@[simp] lemma netTnL_ids (ls : List (Bool × ℕ)) (ord : List (ℕ × ℕ)) :
    (netTnL ls ord).ids = List.range ls.length := rfl

@[simp] lemma netTnL_ordList (ls : List (Bool × ℕ)) (ord : List (ℕ × ℕ)) :
    (netTnL ls ord).ordList = ord := rfl

@[simp] lemma netTnL_lbl (ls : List (Bool × ℕ)) (ord : List (ℕ × ℕ)) :
    (netTnL ls ord).lbl = (List.range ls.length).map fun i => (i, ls.getD i (false, 0)) := rfl

/-- The label of a task of a described network of labelled tasks. -/
theorem netTnL_label {ls : List (Bool × ℕ)} {ord : List (ℕ × ℕ)} {i : ℕ} (hi : i < ls.length) :
    (netTnL ls ord).label i =
      (if (ls.getD i (false, 0)).1 then Sum.inr (ls.getD i (false, 0)).2
        else Sum.inl (ls.getD i (false, 0)).2) := by
  have hmem : i ∈ List.range ls.length := by simpa using hi
  have hlk : ((List.range ls.length).map fun j => (j, ls.getD j (false, 0))).lookup i =
      some (ls.getD i (false, 0)) := lookup_map_self (fun j => ls.getD j (false, 0)) hmem
  show (match (netTnL ls ord).lbl.lookup i with
    | some (true, n) => Sum.inr n
    | some (false, n) => Sum.inl n
    | none => Sum.inl 0) = _
  rw [netTnL_lbl, hlk]
  rcases h : ls.getD i (false, 0) with ⟨b, n⟩
  cases b <;> rfl

/-- The size of a described network of labelled tasks. -/
theorem size_netTnL_le (ls : List (Bool × ℕ)) (ord : List (ℕ × ℕ)) :
    (netTnL ls ord).size ≤ 2 * ls.length + ord.length := by
  rw [TnDesc.size, netTnL_ids, netTnL_lbl, netTnL_ordList]
  simp only [List.length_range, List.length_map]
  omega

namespace TnDesc

variable {t : TnDesc}

/-! ### The canonical form -/

/-- The labels of the tasks, listed by position. -/
def canonLabels (t : TnDesc) : List (Bool × ℕ) := t.ids.dedup.map (nrmPair t)

@[simp] theorem length_canonLabels (t : TnDesc) : (canonLabels t).length = t.width := by
  simp [canonLabels, width]

theorem getD_canonLabels {j : ℕ} (hj : j < t.width) :
    (canonLabels t).getD j (false, 0) = nrmPair t (t.idAt j) := by
  have hlen : j < (canonLabels t).length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hlen]
  show (t.ids.dedup.map (nrmPair t))[j]'hlen = _
  rw [List.getElem_map]
  congr 1
  rw [idAt, List.getD_eq_getElem _ _ hj]

/-- **The canonical form of a described task network**: the tasks identified by their positions,
the labels listed in that order, the ordering listed canonically. -/
def canonL (t : TnDesc) : TnDesc := netTnL (canonLabels t) (canonOrd t)

@[simp] theorem canonL_ids (t : TnDesc) : (canonL t).ids = List.range t.width := by
  simp [canonL]

@[simp] theorem canonL_ordList (t : TnDesc) : (canonL t).ordList = canonOrd t := rfl

/-- The listed relation of the canonical form is the ordering of the network, read through the
positions. -/
theorem canonL_listRel {x y : ℕ} :
    (canonL t).listRel x y ↔
      x < t.width ∧ y < t.width ∧ t.toTaskNetwork.ord (t.idAt x) (t.idAt y) := by
  show (x, y) ∈ canonOrd t ↔ _
  rw [canonOrd, List.mem_filter, mem_posPairs]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, ordB_iff.1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, ordB_iff.2 h3⟩

theorem canonL_preOrd {x y : ℕ} :
    (canonL t).preOrd x y ↔
      x < t.width ∧ y < t.width ∧ t.toTaskNetwork.ord (t.idAt x) (t.idAt y) := by
  constructor
  · intro h
    induction h with
    | single hxy => exact canonL_listRel.1 hxy
    | tail _ hcy ih =>
      obtain ⟨hx, -, hord⟩ := ih
      obtain ⟨-, hy, hord'⟩ := canonL_listRel.1 hcy
      exact ⟨hx, hy, t.toTaskNetwork_wf.trans hord hord'⟩
  · intro h
    exact Relation.TransGen.single (canonL_listRel.2 h)

/-- **The canonical form denotes the same ordering**, read through the positions. -/
theorem canonL_ord {a b : ℕ} (ha : a ∈ t.ids) (hb : b ∈ t.ids) :
    (canonL t).toTaskNetwork.ord (t.pos a) (t.pos b) ↔ t.toTaskNetwork.ord a b := by
  rw [toTaskNetwork_ord]
  constructor
  · rintro ⟨-, -, h, -⟩
    rw [canonL_preOrd, idAt_pos ha, idAt_pos hb] at h
    exact h.2.2
  · intro h
    have hpa : t.pos a < t.width := pos_lt ha
    have hpb : t.pos b < t.width := pos_lt hb
    refine ⟨by simpa using hpa, by simpa using hpb, ?_, fun hc => ?_⟩
    · rw [canonL_preOrd, idAt_pos ha, idAt_pos hb]
      exact ⟨hpa, hpb, h⟩
    · rw [canonL_preOrd, idAt_pos ha, idAt_pos hb] at hc
      exact t.toTaskNetwork_wf.irrefl a (t.toTaskNetwork_wf.trans h hc.2.2)

/-- **The canonical form denotes the same labels**, read through the positions — with no
hypothesis on the labels. -/
theorem canonL_label {i : ℕ} (hi : i ∈ t.ids) : (canonL t).label (t.pos i) = t.label i := by
  have hpi : t.pos i < t.width := pos_lt hi
  rw [canonL, netTnL_label (by simpa using hpi), getD_canonLabels hpi, idAt_pos hi]
  rcases h : t.label i with a | c <;> simp [nrmPair, h]

/-- The canonical form carries one label per task. -/
@[simp] theorem canonL_lbl_length (t : TnDesc) : (canonL t).lbl.length = t.width := by
  have h : (canonL t).lbl =
      (List.range (canonLabels t).length).map fun j => (j, (canonLabels t).getD j (false, 0)) :=
    rfl
  rw [h]
  simp

/-- The label list of the canonical form contains the label of every task, at its position. -/
theorem mem_canonL_lbl {i : ℕ} (hi : i ∈ t.ids) : (t.pos i, nrmPair t i) ∈ (canonL t).lbl := by
  have hpi : t.pos i < t.width := pos_lt hi
  show (t.pos i, nrmPair t i) ∈
    (List.range (canonLabels t).length).map fun j => (j, (canonLabels t).getD j (false, 0))
  refine List.mem_map.2 ⟨t.pos i, ?_, ?_⟩
  · rw [List.mem_range, length_canonLabels]
    exact hpi
  · rw [getD_canonLabels hpi, idAt_pos hi]

/-- **Every description denotes a network isomorphic to the one its canonical form denotes.** -/
theorem canonL_iso (t : TnDesc) : t.toTaskNetwork.Iso (canonL t).toTaskNetwork := by
  refine ⟨t.pos, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ t.ids := by simpa using hx
    show t.pos x ∈ ((canonL t).ids.toFinset : Set ℕ)
    simp only [canonL_ids]
    simpa using pos_lt hx'
  · intro x hx y hy hxy
    have hx' : x ∈ t.ids := by simpa using hx
    have hy' : y ∈ t.ids := by simpa using hy
    rw [← idAt_pos hx', ← idAt_pos hy', hxy]
  · intro y hy
    have hy' : y ∈ (canonL t).ids := by simpa using hy
    have hlt : y < t.width := by simpa using hy'
    exact ⟨t.idAt y, by simpa using idAt_mem hlt, pos_idAt hlt⟩
  · intro a ha b hb
    exact (canonL_ord (by simpa using ha) (by simpa using hb)).symm
  · intro a ha
    exact (canonL_label (by simpa using ha)).symm

end TnDesc

end Syn

end HTN
