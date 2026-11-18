import HtnPlanning.Computable.Linearise
import HtnComplexity.Computable.NetTn
import HtnComplexity.Complexity.ChainDesc
/-!
# Normalising a described task network

A description may list its ordering pairs through identifiers that are *not* tasks of the
network, may repeat an identifier, and may carry labels for identifiers it never lists.  None of
that is visible in the network it denotes (`HTN.Syn.TnDesc.toTaskNetwork`), and this file makes
the invisibility explicit by producing, for every description, a **normal form** denoting an
isomorphic network:

* `HTN.Syn.TnDesc.nrm t` — the identifiers listed once each, the ordering listed explicitly (one
  pair for each ordered pair of tasks), and exactly one label per identifier;
* `HTN.Syn.TnDesc.nrm_iso` — the normal form denotes the *same* network, up to the identity
  isomorphism;
* `HTN.Syn.TnDesc.canon t` — the normal form with the identifiers renamed down to
  `0, 1, …, m - 1`, `m` the number of distinct tasks, and `HTN.Syn.TnDesc.canon_iso`.

`canon` is what makes a *bounded* initial task network a finite amount of information: a network
of at most `k` tasks over a fixed vocabulary has only finitely many canonical forms.  That is
used in `HtnCompilability/Computable/BoundedNetCells.lean`.
-/

namespace HTN

namespace Syn

namespace TnDesc

/-! ### All ordered pairs of a list -/

/-- All ordered pairs of entries of a list. -/
def selfPairs (l : List ℕ) : List (ℕ × ℕ) := l.flatMap fun a => l.map fun b => (a, b)

theorem mem_selfPairs {l : List ℕ} {p : ℕ × ℕ} : p ∈ selfPairs l ↔ p.1 ∈ l ∧ p.2 ∈ l := by
  simp only [selfPairs, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.1, h1, p.2, h2, rfl⟩

theorem selfPairs_range (n : ℕ) : selfPairs (List.range n) = posPairs n := rfl

/-- Renaming both components of all ordered pairs is taking all ordered pairs of the renamed
list. -/
theorem selfPairs_map (f : ℕ → ℕ) (l : List ℕ) :
    (selfPairs l).map (fun p => (f p.1, f p.2)) = selfPairs (l.map f) := by
  simp [selfPairs, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-! ### The normal form -/

/-- The label of `i` in the normal form, as a pair `(kind, name)`. -/
def nrmPair (t : TnDesc) (i : ℕ) : Bool × ℕ :=
  match t.label i with
  | Sum.inr c => (true, c)
  | Sum.inl a => (false, a)

/-- **The normal form of a described task network**: each identifier listed once, the ordering
listed explicitly, one label per identifier. -/
def nrm (t : TnDesc) : TnDesc :=
  (t.ids.dedup,
    (selfPairs t.ids.dedup).filter fun p => ordB t p.1 p.2,
    t.ids.dedup.map fun i => (i, nrmPair t i))

@[simp] lemma nrm_ids (t : TnDesc) : (nrm t).ids = t.ids.dedup := rfl

@[simp] lemma nrm_ordList (t : TnDesc) :
    (nrm t).ordList = (selfPairs t.ids.dedup).filter fun p => ordB t p.1 p.2 := rfl

@[simp] lemma nrm_lbl (t : TnDesc) :
    (nrm t).lbl = t.ids.dedup.map fun i => (i, nrmPair t i) := rfl

variable {t : TnDesc}

theorem mem_nrm_ids {i : ℕ} : i ∈ (nrm t).ids ↔ i ∈ t.ids := by
  simp

theorem nodup_nrm_ids : (nrm t).ids.Nodup := t.ids.nodup_dedup

/-- The listed relation of the normal form is the ordering of the network. -/
theorem nrm_listRel {a b : ℕ} : (nrm t).listRel a b ↔ t.toTaskNetwork.ord a b := by
  show (a, b) ∈ (nrm t).ordList ↔ _
  rw [nrm_ordList, List.mem_filter, mem_selfPairs]
  constructor
  · rintro ⟨-, h⟩
    exact ordB_iff.1 h
  · intro h
    have hb := ordB_iff.2 h
    exact ⟨⟨by simpa using h.1, by simpa using h.2.1⟩, hb⟩

/-- The transitive closure adds nothing: the ordering of a network is transitive. -/
theorem nrm_preOrd {a b : ℕ} : (nrm t).preOrd a b ↔ t.toTaskNetwork.ord a b := by
  constructor
  · intro h
    induction h with
    | single hab => exact nrm_listRel.1 hab
    | tail _ hcb ih => exact t.toTaskNetwork_wf.trans ih (nrm_listRel.1 hcb)
  · intro h
    exact Relation.TransGen.single (nrm_listRel.2 h)

/-- **The normal form denotes the same ordering.** -/
theorem nrm_ord {a b : ℕ} : (nrm t).toTaskNetwork.ord a b ↔ t.toTaskNetwork.ord a b := by
  rw [toTaskNetwork_ord]
  constructor
  · rintro ⟨-, -, h, -⟩
    exact nrm_preOrd.1 h
  · intro h
    refine ⟨by simpa using h.1, by simpa using h.2.1, nrm_preOrd.2 h, fun hc => ?_⟩
    exact t.toTaskNetwork_wf.irrefl a (t.toTaskNetwork_wf.trans h (nrm_preOrd.1 hc))

/-- **The normal form denotes the same labels** on the tasks of the network. -/
theorem nrm_label {i : ℕ} (hi : i ∈ t.ids) : (nrm t).label i = t.label i := by
  have hd : i ∈ t.ids.dedup := by simpa using hi
  have hlk : (nrm t).lbl.lookup i = some (nrmPair t i) := lookup_map_self (nrmPair t) hd
  have key : ∀ b : Bool, ∀ n : ℕ, (nrm t).lbl.lookup i = some (b, n) →
      (nrm t).label i = (if b then Sum.inr n else Sum.inl n) := by
    intro b n hb
    simp only [label, hb]
    cases b <;> rfl
  rw [key (nrmPair t i).1 (nrmPair t i).2 (by simpa using hlk)]
  rcases h : t.label i with a | c <;> simp [nrmPair, h]

/-- **A description and its normal form denote the same network**, via the identity. -/
theorem nrm_iso (t : TnDesc) : t.toTaskNetwork.Iso (nrm t).toTaskNetwork := by
  refine ⟨id, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simpa using (by simpa using hx : x ∈ t.ids)
  · intro x _ y _ h
    exact h
  · intro y hy
    exact ⟨y, by simpa using (by simpa using hy : y ∈ t.ids), rfl⟩
  · intro a _ b _
    exact nrm_ord.symm
  · intro a ha
    exact (nrm_label (by simpa using ha)).symm

/-- Every listed pair of the normal form joins two of its identifiers. -/
theorem nrm_hord : ∀ p ∈ (nrm t).ordList, p.1 ∈ (nrm t).ids ∧ p.2 ∈ (nrm t).ids := by
  intro p hp
  rw [nrm_ordList, List.mem_filter, mem_selfPairs] at hp
  exact hp.1

/-- Every label of the normal form is attached to one of its identifiers. -/
theorem nrm_hlbl : ∀ l ∈ (nrm t).lbl, l.1 ∈ (nrm t).ids := by
  intro l hl
  rw [nrm_lbl, List.mem_map] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  exact hi

/-! ### The canonical form of a network of compound tasks -/

end TnDesc

/-- The label of a task of a described network of compound tasks. -/
theorem netTn_label_getD (ws : List ℕ) (ord : List (ℕ × ℕ)) {i : ℕ} (hi : i < ws.length) :
    (netTn ws ord).label i = Sum.inr (ws.getD i 0) := by
  have hmem : i ∈ List.range ws.length := by simpa using hi
  have hlk := lookup_map_self (fun j => ((true, ws.getD j 0) : Bool × ℕ)) hmem
  show (match (netTn ws ord).lbl.lookup i with
    | some (true, n) => Sum.inr n
    | some (false, n) => Sum.inl n
    | none => Sum.inl 0) = _
  rw [netTn_lbl, hlk]

namespace TnDesc

variable {t : TnDesc}

/-- **Every task of the described network is compound.** -/
def AllCompound (t : TnDesc) : Prop := ∀ i ∈ t.ids, ∃ c, t.label i = Sum.inr c

/-- The number of tasks of the described network. -/
def width (t : TnDesc) : ℕ := t.ids.dedup.length

/-- The position of a task identifier among the distinct identifiers of the description. -/
def pos (t : TnDesc) (i : ℕ) : ℕ := t.ids.dedup.idxOf i

/-- The identifier at a given position. -/
def idAt (t : TnDesc) (j : ℕ) : ℕ := t.ids.dedup.getD j 0

theorem pos_lt {i : ℕ} (hi : i ∈ t.ids) : t.pos i < t.width :=
  List.idxOf_lt_length_iff.2 (by simpa using hi)

theorem idAt_pos {i : ℕ} (hi : i ∈ t.ids) : t.idAt (t.pos i) = i := by
  have hd : i ∈ t.ids.dedup := by simpa using hi
  have hlt : t.pos i < t.ids.dedup.length := List.idxOf_lt_length_iff.2 hd
  rw [idAt, List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

theorem idAt_mem {j : ℕ} (hj : j < t.width) : t.idAt j ∈ t.ids := by
  have h : t.idAt j = t.ids.dedup[j] := by rw [idAt, List.getD_eq_getElem _ _ hj]
  rw [h]
  exact List.mem_dedup.1 (List.getElem_mem hj)

theorem pos_idAt {j : ℕ} (hj : j < t.width) : t.pos (t.idAt j) = j := by
  rw [idAt, List.getD_eq_getElem _ _ hj]
  exact List.Nodup.idxOf_getElem t.ids.nodup_dedup j hj

/-- The compound name of a task, read off the label list. -/
def canonName (t : TnDesc) (i : ℕ) : ℕ := (labelList true t.lbl i).getD 0 0

/-- The label list of a compound task is the singleton of its name. -/
theorem labelList_true_of_label {i c : ℕ} (h : t.label i = Sum.inr c) :
    labelList true t.lbl i = [c] := by
  rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
  · rw [show t.label i = Sum.inl 0 by simp only [label, hl]] at h
    exact absurd h (by simp)
  · cases b
    · rw [show t.label i = Sum.inl n by simp only [label, hl]] at h
      exact absurd h (by simp)
    · have hn : n = c := by
        rw [show t.label i = Sum.inr n by simp only [label, hl]] at h
        exact Sum.inr.inj h
      subst hn
      rw [labelList_eq, hl]
      simp

theorem canonName_eq {i c : ℕ} (h : t.label i = Sum.inr c) : canonName t i = c := by
  rw [canonName, labelList_true_of_label h]
  rfl

/-- The names of the tasks, listed by position. -/
def canonNames (t : TnDesc) : List ℕ := t.ids.dedup.map (canonName t)

@[simp] theorem length_canonNames (t : TnDesc) : (canonNames t).length = t.width := by
  simp [canonNames, width]

theorem getD_canonNames {j : ℕ} (hj : j < t.width) :
    (canonNames t).getD j 0 = canonName t (t.idAt j) := by
  have hlen : j < (canonNames t).length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hlen]
  show (t.ids.dedup.map (canonName t))[j]'hlen = _
  rw [List.getElem_map]
  congr 1
  rw [idAt, List.getD_eq_getElem _ _ hj]

/-- The ordering of the tasks, listed by position. -/
def canonOrd (t : TnDesc) : List (ℕ × ℕ) :=
  (posPairs t.width).filter fun p => ordB t (t.idAt p.1) (t.idAt p.2)

theorem canonOrd_sublist (t : TnDesc) : (canonOrd t).Sublist (posPairs t.width) :=
  List.filter_sublist

/-- **The canonical form of a described network of compound tasks**: the tasks identified by
their positions, the names listed in that order, the ordering listed canonically. -/
def canon (t : TnDesc) : TnDesc := netTn (canonNames t) (canonOrd t)

@[simp] theorem canon_ids (t : TnDesc) : (canon t).ids = List.range t.width := by
  simp [canon]

@[simp] theorem canon_ordList (t : TnDesc) : (canon t).ordList = canonOrd t := rfl

@[simp] theorem canon_compoundNames (t : TnDesc) : (canon t).compoundNames = canonNames t :=
  netTn_compoundNames _ _

/-- The listed relation of the canonical form is the ordering of the network, read through the
positions. -/
theorem canon_listRel {x y : ℕ} :
    (canon t).listRel x y ↔
      x < t.width ∧ y < t.width ∧ t.toTaskNetwork.ord (t.idAt x) (t.idAt y) := by
  show (x, y) ∈ canonOrd t ↔ _
  rw [canonOrd, List.mem_filter, mem_posPairs]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, ordB_iff.1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, ordB_iff.2 h3⟩

theorem canon_preOrd {x y : ℕ} :
    (canon t).preOrd x y ↔
      x < t.width ∧ y < t.width ∧ t.toTaskNetwork.ord (t.idAt x) (t.idAt y) := by
  constructor
  · intro h
    induction h with
    | single hxy => exact canon_listRel.1 hxy
    | tail _ hcy ih =>
      obtain ⟨hx, -, hord⟩ := ih
      obtain ⟨-, hy, hord'⟩ := canon_listRel.1 hcy
      exact ⟨hx, hy, t.toTaskNetwork_wf.trans hord hord'⟩
  · intro h
    exact Relation.TransGen.single (canon_listRel.2 h)

/-- **The canonical form denotes the same ordering**, read through the positions. -/
theorem canon_ord {a b : ℕ} (ha : a ∈ t.ids) (hb : b ∈ t.ids) :
    (canon t).toTaskNetwork.ord (t.pos a) (t.pos b) ↔ t.toTaskNetwork.ord a b := by
  rw [toTaskNetwork_ord]
  constructor
  · rintro ⟨-, -, h, -⟩
    rw [canon_preOrd, idAt_pos ha, idAt_pos hb] at h
    exact h.2.2
  · intro h
    have hpa : t.pos a < t.width := pos_lt ha
    have hpb : t.pos b < t.width := pos_lt hb
    refine ⟨by simpa using hpa, by simpa using hpb, ?_, fun hc => ?_⟩
    · rw [canon_preOrd, idAt_pos ha, idAt_pos hb]
      exact ⟨hpa, hpb, h⟩
    · rw [canon_preOrd, idAt_pos ha, idAt_pos hb] at hc
      exact t.toTaskNetwork_wf.irrefl a (t.toTaskNetwork_wf.trans h hc.2.2)

/-- **The canonical form denotes the same labels**, read through the positions. -/
theorem canon_label (hc : AllCompound t) {i : ℕ} (hi : i ∈ t.ids) :
    (canon t).label (t.pos i) = t.label i := by
  have hpi : t.pos i < t.width := pos_lt hi
  rw [canon, netTn_label_getD _ _ (by simpa using hpi), getD_canonNames hpi, idAt_pos hi]
  obtain ⟨c, hcc⟩ := hc i hi
  rw [canonName_eq hcc, hcc]

/-- **A description of a network of compound tasks and its canonical form denote isomorphic
networks.** -/
theorem canon_iso (hc : AllCompound t) : t.toTaskNetwork.Iso (canon t).toTaskNetwork := by
  refine ⟨t.pos, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ t.ids := by simpa using hx
    show t.pos x ∈ ((canon t).ids.toFinset : Set ℕ)
    simp only [canon_ids]
    simpa using pos_lt hx'
  · intro x hx y hy hxy
    have hx' : x ∈ t.ids := by simpa using hx
    have hy' : y ∈ t.ids := by simpa using hy
    rw [← idAt_pos hx', ← idAt_pos hy', hxy]
  · intro y hy
    have hy' : y ∈ (canon t).ids := by simpa using hy
    have hlt : y < t.width := by simpa using hy'
    exact ⟨t.idAt y, by simpa using idAt_mem hlt, pos_idAt hlt⟩
  · intro a ha b hb
    exact (canon_ord (by simpa using ha) (by simpa using hb)).symm
  · intro a ha
    exact (canon_label hc (by simpa using ha)).symm

end TnDesc

end Syn

end HTN
