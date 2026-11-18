import HtnComplexity.Space.SeqGadget
import HtnPlanning.Computable.Linearise
/-!
# Rank witnesses for a totally ordered initial task network

The sequencing gadget of `HtnComplexity/Space/SeqGadget.lean` needs the initial task
network of the instance as a *sequence*: the task of rank `0`, the task of rank `1`, …  The
machine of step A3 of `TABLE4-PLAN.md` cannot compute the ranks conveniently, so it guesses them
and checks the guess.  This file fixes what the check has to establish, and proves that it is
enough and that it can always be met.

A **witness** is a list `ws` of pairs `(p, a)` — "node `a` has value `p`".  The nodes are the
identifiers of the network and the endpoints of the listed ordering pairs.  The conditions
(`HTN.Syn.SeqG.WitOk`) are all *local*: each mentions at most two entries of the witness and one
entry of the network description, which is what a test of Cobham's class can quantify over.

* every identifier and every endpoint of a listed pair has a value, and a node has one value;
* two identifiers with the same value are equal, and the values of the identifiers are
  downward closed (value `p + 1` taken ⇒ value `p` taken by an identifier);
* along every listed pair the value does not decrease.

The values of the non-identifiers are needed because the order of the network is the transitive
closure of the listed pairs, which may pass through nodes that are not identifiers; weak
monotonicity along the listed pairs, together with injectivity on the identifiers, gives strict
monotonicity along the order.

* `HTN.Syn.SeqG.exists_seqNet_of_witOk` — **soundness**: a witness of a totally ordered network
  yields the sequence network of its identifiers listed by value, the values of the identifiers
  being exactly their positions;
* `HTN.Syn.SeqG.witOk_canonWit` — **completeness**: every totally ordered network has a witness,
  `HTN.Syn.SeqG.canonWit`, with values bounded by the number of identifiers.
-/

namespace HTN

namespace Syn

namespace SeqG

/-- **The conditions on a rank witness** `ws` for the described task network `t`. -/
structure WitOk (t : TnDesc) (ws : List (ℕ × ℕ)) : Prop where
  total : ∀ i ∈ t.ids, ∃ p, (p, i) ∈ ws
  endp : ∀ e ∈ t.ordList, (∃ p, (p, e.1) ∈ ws) ∧ (∃ p, (p, e.2) ∈ ws)
  func : ∀ p p' a, (p, a) ∈ ws → (p', a) ∈ ws → p = p'
  inj : ∀ p i j, i ∈ t.ids → j ∈ t.ids → (p, i) ∈ ws → (p, j) ∈ ws → i = j
  down : ∀ p i, i ∈ t.ids → (p + 1, i) ∈ ws → ∃ j ∈ t.ids, (p, j) ∈ ws
  mono : ∀ e ∈ t.ordList, ∀ p p', (p, e.1) ∈ ws → (p', e.2) ∈ ws → p ≤ p'

/-! ### Soundness -/

section Sound

variable {t : TnDesc} {ws : List (ℕ × ℕ)}

/-- Along the order of the network, the value does not decrease. -/
theorem WitOk.le_of_preOrd (h : WitOk t ws) {a b : ℕ} (hab : t.preOrd a b) :
    ∀ p p', (p, a) ∈ ws → (p', b) ∈ ws → p ≤ p' := by
  induction hab with
  | single hab => exact h.mono _ hab
  | @tail b c _ hbc ih =>
    intro p p' hpa hpc
    obtain ⟨q, hq⟩ := (h.endp _ hbc).1
    exact (ih p q hpa hq).trans (h.mono _ hbc q p' hq hpc)

open Classical in
/-- The value of a node. -/
noncomputable def wpos (ws : List (ℕ × ℕ)) (a : ℕ) : ℕ :=
  if h : ∃ p, (p, a) ∈ ws then h.choose else 0

theorem mem_wpos {a : ℕ} (ha : ∃ p, (p, a) ∈ ws) : (wpos ws a, a) ∈ ws := by
  rw [wpos, dif_pos ha]
  exact ha.choose_spec

theorem WitOk.mem_iff (h : WitOk t ws) {i : ℕ} (hi : i ∈ t.ids) {p : ℕ} :
    (p, i) ∈ ws ↔ p = wpos ws i := by
  constructor
  · intro hp
    exact h.func _ _ _ hp (mem_wpos (h.total i hi))
  · rintro rfl
    exact mem_wpos (h.total i hi)

theorem WitOk.wpos_inj (h : WitOk t ws) {i j : ℕ} (hi : i ∈ t.ids) (hj : j ∈ t.ids)
    (heq : wpos ws i = wpos ws j) : i = j :=
  h.inj _ _ _ hi hj (mem_wpos (h.total i hi)) (heq ▸ mem_wpos (h.total j hj))

/-- Along the order of the network, the value increases. -/
theorem WitOk.lt_of_ordOf (h : WitOk t ws) {i j : ℕ} (hij : t.ordOf i j) :
    wpos ws i < wpos ws j := by
  obtain ⟨hi, hj, hp, hnp⟩ := hij
  have hne : i ≠ j := by
    rintro rfl
    exact hnp hp
  have hle := h.le_of_preOrd hp _ _ (mem_wpos (h.total i hi)) (mem_wpos (h.total j hj))
  exact lt_of_le_of_ne hle fun heq => hne (h.wpos_inj hi hj heq)

/-- The values of the identifiers. -/
noncomputable def wvals (t : TnDesc) (ws : List (ℕ × ℕ)) : Finset ℕ :=
  t.ids.toFinset.image (wpos ws)

theorem WitOk.card_wvals (h : WitOk t ws) : (wvals t ws).card = t.ids.toFinset.card :=
  Finset.card_image_of_injOn fun i hi j hj heq =>
    h.wpos_inj (List.mem_toFinset.1 hi) (List.mem_toFinset.1 hj) heq

theorem WitOk.down_wvals (h : WitOk t ws) {m : ℕ} (hm : m + 1 ∈ wvals t ws) :
    m ∈ wvals t ws := by
  obtain ⟨i, hi, hm⟩ := Finset.mem_image.1 hm
  have hi' := List.mem_toFinset.1 hi
  obtain ⟨j, hj, hjm⟩ := h.down m i hi' ((h.mem_iff hi').2 hm.symm)
  exact Finset.mem_image.2 ⟨j, List.mem_toFinset.2 hj, ((h.mem_iff hj).1 hjm).symm⟩

theorem WitOk.mem_wvals_iff (h : WitOk t ws) {m : ℕ} :
    m ∈ wvals t ws ↔ m < t.ids.toFinset.card := by
  have hdown : ∀ m, m ∈ wvals t ws → ∀ m' ≤ m, m' ∈ wvals t ws := by
    intro m hm m' hm'
    induction m with
    | zero => rwa [Nat.le_zero.1 hm']
    | succ m ih =>
      rcases Nat.lt_or_eq_of_le hm' with hlt | rfl
      · exact ih (h.down_wvals hm) (Nat.lt_succ_iff.1 hlt)
      · exact hm
  have hsub : wvals t ws ⊆ Finset.range t.ids.toFinset.card := by
    intro m hm
    have hr : Finset.range (m + 1) ⊆ wvals t ws := fun m' hm' =>
      hdown m hm m' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm'))
    have := Finset.card_le_card hr
    rw [Finset.card_range, h.card_wvals] at this
    exact Finset.mem_range.2 this
  have heq : wvals t ws = Finset.range t.ids.toFinset.card :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, h.card_wvals])
  rw [heq, Finset.mem_range]

open Classical in
/-- The identifier of value `p`. -/
noncomputable def wnode (t : TnDesc) (ws : List (ℕ × ℕ)) (p : ℕ) : ℕ :=
  if h : ∃ i ∈ t.ids, wpos ws i = p then h.choose else 0

theorem WitOk.wnode_spec (h : WitOk t ws) {p : ℕ} (hp : p < t.ids.toFinset.card) :
    wnode t ws p ∈ t.ids ∧ wpos ws (wnode t ws p) = p := by
  have hex : ∃ i ∈ t.ids, wpos ws i = p := by
    obtain ⟨i, hi, hip⟩ := Finset.mem_image.1 (h.mem_wvals_iff.2 hp)
    exact ⟨i, List.mem_toFinset.1 hi, hip⟩
  rw [wnode, dif_pos hex]
  exact hex.choose_spec

theorem WitOk.wnode_wpos (h : WitOk t ws) {i : ℕ} (hi : i ∈ t.ids) :
    wnode t ws (wpos ws i) = i := by
  have hlt : wpos ws i < t.ids.toFinset.card :=
    h.mem_wvals_iff.1 (Finset.mem_image.2 ⟨i, List.mem_toFinset.2 hi, rfl⟩)
  obtain ⟨h1, h2⟩ := h.wnode_spec hlt
  exact h.wpos_inj h1 hi h2

/-- The identifiers listed by value. -/
noncomputable def wlist (t : TnDesc) (ws : List (ℕ × ℕ)) : List ℕ :=
  (List.range t.ids.toFinset.card).map (wnode t ws)

theorem WitOk.wpos_lt (h : WitOk t ws) {i : ℕ} (hi : i ∈ t.ids) :
    wpos ws i < t.ids.toFinset.card :=
  h.mem_wvals_iff.1 (Finset.mem_image.2 ⟨i, List.mem_toFinset.2 hi, rfl⟩)

theorem WitOk.getElem?_wlist (h : WitOk t ws) {i : ℕ} (hi : i ∈ t.ids) {p : ℕ} :
    (wlist t ws)[p]? = some i ↔ p = wpos ws i := by
  rw [wlist, List.getElem?_map]
  by_cases hp : p < t.ids.toFinset.card
  · rw [List.getElem?_range hp, Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl
      exact (h.wnode_spec hp).2.symm
    · rintro rfl
      exact h.wnode_wpos hi
  · rw [List.getElem?_eq_none (by simpa using hp)]
    simp only [Option.map_none, reduceCtorEq, false_iff]
    rintro rfl
    exact hp (h.wpos_lt hi)

theorem WitOk.mem_wlist (h : WitOk t ws) {x : ℕ} : x ∈ wlist t ws ↔ x ∈ t.ids := by
  simp only [wlist, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (h.wnode_spec hp).1
  · intro hx
    exact ⟨_, h.wpos_lt hx, h.wnode_wpos hx⟩

theorem WitOk.nodup_wlist (h : WitOk t ws) : (wlist t ws).Nodup := by
  refine List.Nodup.map_on (fun x hx y hy heq => ?_) List.nodup_range
  rw [← (h.wnode_spec (List.mem_range.1 hx)).2, ← (h.wnode_spec (List.mem_range.1 hy)).2, heq]

theorem WitOk.idxOf_wlist (h : WitOk t ws) {x : ℕ} (hx : x ∈ t.ids) :
    (wlist t ws).idxOf x = wpos ws x := by
  have hlt : wpos ws x < (wlist t ws).length := by
    simpa [wlist] using h.wpos_lt hx
  have hget : (wlist t ws)[wpos ws x] = x := by
    simp [wlist, h.wnode_wpos hx]
  conv_lhs => rw [← hget]
  exact List.Nodup.idxOf_getElem h.nodup_wlist _ hlt

/-- **Soundness of rank witnesses.** -/
theorem exists_seqNet_of_witOk (hTO : t.toTaskNetwork.IsTotallyOrdered) (h : WitOk t ws) :
    ∃ l : List ℕ, t.toTaskNetwork.IsSeqNet l (l.map t.label) ∧
      ∀ p i, i ∈ t.ids → ((p, i) ∈ ws ↔ l[p]? = some i) := by
  refine ⟨wlist t ws, ⟨h.nodup_wlist, fun x => ?_, rfl, fun x y => ?_⟩,
    fun p i hi => by rw [h.mem_iff hi, h.getElem?_wlist hi]⟩
  · rw [TnDesc.toTaskNetwork_T, List.mem_toFinset, h.mem_wlist]
  · rw [h.mem_wlist, h.mem_wlist]
    constructor
    · intro hxy
      have hxy' : t.ordOf x y := hxy
      have hx := hxy'.1
      have hy := hxy'.2.1
      rw [h.idxOf_wlist hx, h.idxOf_wlist hy]
      exact ⟨hx, hy, h.lt_of_ordOf hxy'⟩
    · rintro ⟨hx, hy, hlt⟩
      rw [h.idxOf_wlist hx, h.idxOf_wlist hy] at hlt
      have hne : x ≠ y := by
        rintro rfl
        exact lt_irrefl _ hlt
      rcases hTO x (by simpa using hx) y (by simpa using hy) hne with hxy | hyx
      · exact hxy
      · exact absurd (h.lt_of_ordOf hyx) (not_lt.2 hlt.le)

end Sound

/-! ### Completeness -/

section Complete

variable {t : TnDesc}

open Classical

/-- The position of an identifier in the linearisation. -/
def lpos (t : TnDesc) (i : ℕ) : ℕ := t.lin.idxOf i

/-- The value of a node: the largest position of an identifier at or before it. -/
noncomputable def rval (t : TnDesc) (a : ℕ) : ℕ :=
  (t.ids.toFinset.filter fun i => i = a ∨ t.preOrd i a).sup (lpos t)

/-- The nodes: the identifiers and the endpoints of the listed pairs. -/
def wnodes (t : TnDesc) : List ℕ := t.ids ++ t.ordList.flatMap fun e => [e.1, e.2]

/-- **The canonical witness.** -/
noncomputable def canonWit (t : TnDesc) : List (ℕ × ℕ) := (wnodes t).map fun a => (rval t a, a)

theorem mem_lin_iff (hTO : t.toTaskNetwork.IsTotallyOrdered) {i : ℕ} : i ∈ t.lin ↔ i ∈ t.ids := by
  rw [(TnDesc.isLinearization_lin hTO).2.1 i, TnDesc.toTaskNetwork_T, List.mem_toFinset]

theorem lpos_le_of_preOrd (hTO : t.toTaskNetwork.IsTotallyOrdered) {i j : ℕ} (hi : i ∈ t.ids)
    (hj : j ∈ t.ids) (hij : i = j ∨ t.preOrd i j) : lpos t i ≤ lpos t j := by
  rcases hij with rfl | hij
  · exact le_rfl
  by_cases hne : i = j
  · rw [hne]
  rcases hTO i (by simpa using hi) j (by simpa using hj) hne with h | h
  · exact ((((TnDesc.isSeqNet_lin hTO).ord i j).1 h).2.2).le
  · exact absurd hij h.2.2.2

theorem rval_of_mem (hTO : t.toTaskNetwork.IsTotallyOrdered) {i : ℕ} (hi : i ∈ t.ids) :
    rval t i = lpos t i := by
  refine le_antisymm (Finset.sup_le fun j hj => ?_) (Finset.le_sup ?_)
  · rw [Finset.mem_filter, List.mem_toFinset] at hj
    exact lpos_le_of_preOrd hTO hj.1 hi hj.2
  · rw [Finset.mem_filter, List.mem_toFinset]
    exact ⟨hi, Or.inl rfl⟩

theorem rval_le (hTO : t.toTaskNetwork.IsTotallyOrdered) (a : ℕ) : rval t a ≤ t.ids.length := by
  refine Finset.sup_le fun j hj => ?_
  rw [Finset.mem_filter, List.mem_toFinset] at hj
  have h1 : lpos t j < t.lin.length := List.idxOf_lt_length_of_mem ((mem_lin_iff hTO).2 hj.1)
  have h2 := TnDesc.length_lin_le t
  omega

theorem mem_canonWit {p a : ℕ} : (p, a) ∈ canonWit t ↔ a ∈ wnodes t ∧ p = rval t a := by
  simp only [canonWit, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨hb, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

/-- **Completeness of rank witnesses**: the canonical witness of a totally ordered network meets
the conditions, and its values are bounded by the number of identifiers. -/
theorem witOk_canonWit (hTO : t.toTaskNetwork.IsTotallyOrdered) : WitOk t (canonWit t) where
  total i hi := ⟨_, mem_canonWit.2 ⟨List.mem_append_left _ hi, rfl⟩⟩
  endp e he :=
    ⟨⟨_, mem_canonWit.2 ⟨List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, by simp⟩), rfl⟩⟩,
      ⟨_, mem_canonWit.2 ⟨List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, by simp⟩), rfl⟩⟩⟩
  func p p' a hp hp' := by
    rw [(mem_canonWit.1 hp).2, (mem_canonWit.1 hp').2]
  inj p i j hi hj hpi hpj := by
    have h := (mem_canonWit.1 hpi).2.symm.trans (mem_canonWit.1 hpj).2
    rw [rval_of_mem hTO hi, rval_of_mem hTO hj] at h
    exact (List.idxOf_inj ((mem_lin_iff hTO).2 hi)).1 h
  down p i hi hpi := by
    have h := (mem_canonWit.1 hpi).2
    rw [rval_of_mem hTO hi] at h
    have hlt : p < t.lin.length := by
      have := List.idxOf_lt_length_of_mem ((mem_lin_iff hTO).2 hi)
      unfold lpos at h
      omega
    have hj : t.lin[p] ∈ t.ids := (mem_lin_iff hTO).1 (List.getElem_mem hlt)
    refine ⟨t.lin[p], hj, mem_canonWit.2 ⟨List.mem_append_left _ hj, ?_⟩⟩
    rw [rval_of_mem hTO hj, lpos, List.Nodup.idxOf_getElem (TnDesc.nodup_lin t)]
  mono e he p p' hp hp' := by
    rw [(mem_canonWit.1 hp).2, (mem_canonWit.1 hp').2]
    refine Finset.sup_mono fun i hi => ?_
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, Or.inr ?_⟩
    rcases hi.2 with rfl | h
    · exact Relation.TransGen.single he
    · exact h.tail he

theorem canonWit_le (hTO : t.toTaskNetwork.IsTotallyOrdered) :
    ∀ e ∈ canonWit t, e.1 ≤ t.ids.length := by
  rintro ⟨p, a⟩ he
  rw [(mem_canonWit.1 he).2]
  exact rval_le hTO a

end Complete

end SeqG

end Syn

end HTN
