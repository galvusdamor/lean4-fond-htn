import HtnComplexity.Space.SeqWitness
/-!
# Node numberings for a partially ordered initial task network

The planner P-REG (`NOTES.md` §64–65) numbers the **nodes** of the initial task network — its
identifiers and the endpoints of its listed ordering pairs — by a guessed witness `ws` of pairs
`(p, a)` ("node `a` has number `p`").  Unlike the rank witnesses of
`HtnComplexity/Space/SeqWitness.lean` there is no monotonicity condition (the network is
only partially ordered); instead the numbering is **injective on all nodes** and its numbers are
downward closed, so that the identifiers get the numbers `0, …, k - 1` and the other nodes the
numbers `k, …, m - 1`.

* `HTN.Syn.SeqG.WitR` — the local conditions;
* `HTN.Syn.SeqG.WitR.wpos_lt` / `WitR.wnode_spec` — the identifiers are numbered `0 … k - 1`;
* `HTN.Syn.SeqG.WitR.lt_nodes` — every number is below the number of nodes;
* `HTN.Syn.SeqG.witR_canonR` — the canonical numbering satisfies the conditions.
-/

namespace HTN

namespace Syn

namespace SeqG

/-- **The conditions on a node numbering** `ws` of the described task network `t`. -/
structure WitR (t : TnDesc) (ws : List (ℕ × ℕ)) : Prop where
  total : ∀ i ∈ t.ids, ∃ p, (p, i) ∈ ws
  endp : ∀ e ∈ t.ordList, (∃ p, (p, e.1) ∈ ws) ∧ (∃ p, (p, e.2) ∈ ws)
  node : ∀ p a, (p, a) ∈ ws → a ∈ wnodes t
  func : ∀ p p' a, (p, a) ∈ ws → (p', a) ∈ ws → p = p'
  inj : ∀ p a b, (p, a) ∈ ws → (p, b) ∈ ws → a = b
  down : ∀ p i, i ∈ t.ids → (p + 1, i) ∈ ws → ∃ j ∈ t.ids, (p, j) ∈ ws
  downAll : ∀ p a, (p + 1, a) ∈ ws → ∃ b, (p, b) ∈ ws

section WitR

variable {t : TnDesc} {ws : List (ℕ × ℕ)}

theorem WitR.congr (h : WitR t ws) {ws' : List (ℕ × ℕ)} (hw : ∀ w, w ∈ ws' ↔ w ∈ ws) :
    WitR t ws' where
  total i hi := by simpa only [hw] using h.total i hi
  endp e he := by simpa only [hw] using h.endp e he
  node p a := by simpa only [hw] using h.node p a
  func p p' a := by simpa only [hw] using h.func p p' a
  inj p a b := by simpa only [hw] using h.inj p a b
  down p i := by simpa only [hw] using h.down p i
  downAll p a := by simpa only [hw] using h.downAll p a

theorem WitR.mem_iff' (h : WitR t ws) {a : ℕ} (ha : ∃ p, (p, a) ∈ ws) {p : ℕ} :
    (p, a) ∈ ws ↔ p = wpos ws a := by
  constructor
  · intro hp
    exact h.func _ _ _ hp (mem_wpos ha)
  · rintro rfl
    exact mem_wpos ha

theorem WitR.mem_iff (h : WitR t ws) {i : ℕ} (hi : i ∈ t.ids) {p : ℕ} :
    (p, i) ∈ ws ↔ p = wpos ws i := h.mem_iff' (h.total i hi)

theorem WitR.wpos_inj (h : WitR t ws) {a b : ℕ} (ha : ∃ p, (p, a) ∈ ws) (hb : ∃ p, (p, b) ∈ ws)
    (heq : wpos ws a = wpos ws b) : a = b :=
  h.inj _ _ _ (mem_wpos ha) (heq ▸ mem_wpos hb)

theorem WitR.card_wvals (h : WitR t ws) : (wvals t ws).card = t.ids.toFinset.card :=
  Finset.card_image_of_injOn fun i hi j hj heq =>
    h.wpos_inj (h.total i (List.mem_toFinset.1 hi)) (h.total j (List.mem_toFinset.1 hj)) heq

theorem WitR.down_wvals (h : WitR t ws) {m : ℕ} (hm : m + 1 ∈ wvals t ws) :
    m ∈ wvals t ws := by
  obtain ⟨i, hi, hm⟩ := Finset.mem_image.1 hm
  have hi' := List.mem_toFinset.1 hi
  obtain ⟨j, hj, hjm⟩ := h.down m i hi' ((h.mem_iff hi').2 hm.symm)
  exact Finset.mem_image.2 ⟨j, List.mem_toFinset.2 hj, ((h.mem_iff hj).1 hjm).symm⟩

/-- A downward closed finite set of numbers is an initial segment. -/
theorem eq_range_of_down {s : Finset ℕ} (hdown : ∀ m, m + 1 ∈ s → m ∈ s) :
    s = Finset.range s.card := by
  have hd : ∀ m, m ∈ s → ∀ m' ≤ m, m' ∈ s := by
    intro m hm m' hm'
    induction m with
    | zero => rwa [Nat.le_zero.1 hm']
    | succ m ih =>
      rcases Nat.lt_or_eq_of_le hm' with hlt | rfl
      · exact ih (hdown m hm) (Nat.lt_succ_iff.1 hlt)
      · exact hm
  have hsub : s ⊆ Finset.range s.card := by
    intro m hm
    have hr : Finset.range (m + 1) ⊆ s := fun m' hm' =>
      hd m hm m' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm'))
    have := Finset.card_le_card hr
    rw [Finset.card_range] at this
    exact Finset.mem_range.2 this
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range])

theorem WitR.mem_wvals_iff (h : WitR t ws) {m : ℕ} :
    m ∈ wvals t ws ↔ m < t.ids.toFinset.card := by
  rw [eq_range_of_down (fun m hm => h.down_wvals hm), Finset.mem_range, h.card_wvals]

theorem WitR.wnode_spec (h : WitR t ws) {p : ℕ} (hp : p < t.ids.toFinset.card) :
    wnode t ws p ∈ t.ids ∧ wpos ws (wnode t ws p) = p := by
  have hex : ∃ i ∈ t.ids, wpos ws i = p := by
    obtain ⟨i, hi, hip⟩ := Finset.mem_image.1 (h.mem_wvals_iff.2 hp)
    exact ⟨i, List.mem_toFinset.1 hi, hip⟩
  rw [wnode, dif_pos hex]
  exact hex.choose_spec

theorem WitR.wpos_lt (h : WitR t ws) {i : ℕ} (hi : i ∈ t.ids) :
    wpos ws i < t.ids.toFinset.card :=
  h.mem_wvals_iff.1 (Finset.mem_image.2 ⟨i, List.mem_toFinset.2 hi, rfl⟩)

theorem WitR.wnode_wpos (h : WitR t ws) {i : ℕ} (hi : i ∈ t.ids) :
    wnode t ws (wpos ws i) = i := by
  obtain ⟨h1, h2⟩ := h.wnode_spec (h.wpos_lt hi)
  exact h.wpos_inj (h.total _ h1) (h.total i hi) h2

/-- The node numbered `p` below the number of identifiers is an identifier. -/
theorem WitR.mem_ids_of_lt (h : WitR t ws) {p a : ℕ} (hpa : (p, a) ∈ ws)
    (hp : p < t.ids.toFinset.card) : a ∈ t.ids := by
  obtain ⟨h1, h2⟩ := h.wnode_spec hp
  have := h.inj _ _ _ hpa (h2 ▸ mem_wpos (h.total _ h1))
  rw [this]
  exact h1

theorem WitR.exists_id_iff (h : WitR t ws) {p : ℕ} :
    (∃ i ∈ t.ids, (p, i) ∈ ws) ↔ p < t.ids.toFinset.card := by
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [(h.mem_iff hi).1 hp]
    exact h.wpos_lt hi
  · intro hp
    obtain ⟨h1, h2⟩ := h.wnode_spec hp
    exact ⟨_, h1, (h.mem_iff h1).2 h2.symm⟩

/-- The numbers used by the numbering. -/
def wnums (ws : List (ℕ × ℕ)) : Finset ℕ := (ws.map Prod.fst).toFinset

theorem mem_wnums {p : ℕ} : p ∈ wnums ws ↔ ∃ a, (p, a) ∈ ws := by
  simp [wnums]

open Classical in
/-- The node with number `q`. -/
noncomputable def wnode' (ws : List (ℕ × ℕ)) (q : ℕ) : ℕ :=
  if h : ∃ a, (q, a) ∈ ws then h.choose else 0

theorem wnode'_spec {q : ℕ} (h : ∃ a, (q, a) ∈ ws) : (q, wnode' ws q) ∈ ws := by
  rw [wnode', dif_pos h]
  exact h.choose_spec

/-- **Every number is below the number of nodes.** -/
theorem WitR.lt_nodes (h : WitR t ws) {p a : ℕ} (hpa : (p, a) ∈ ws) :
    p < (wnodes t).toFinset.card := by
  have hr := eq_range_of_down (s := wnums ws) fun m hm => by
    obtain ⟨b, hb⟩ := mem_wnums.1 hm
    exact mem_wnums.2 (h.downAll m b hb)
  have hp : p ∈ wnums ws := mem_wnums.2 ⟨a, hpa⟩
  rw [hr, Finset.mem_range] at hp
  refine lt_of_lt_of_le hp ?_
  classical
  have hmaps : ∀ q ∈ wnums ws, wnode' ws q ∈ (wnodes t).toFinset := fun q hq =>
    List.mem_toFinset.2 (h.node _ _ (wnode'_spec (mem_wnums.1 hq)))
  refine Finset.card_le_card_of_injOn (wnode' ws) (fun q hq => hmaps q hq) ?_
  intro q hq q' hq' heq
  exact h.func _ _ _ (wnode'_spec (mem_wnums.1 hq))
    (heq ▸ wnode'_spec (mem_wnums.1 hq'))

end WitR

/-! ### The canonical numbering -/

section Canon

variable (t : TnDesc)

/-- The nodes, identifiers first, without repetitions. -/
def allL : List ℕ := t.ids.dedup ++ ((wnodes t).dedup.filter (· ∉ t.ids))

/-- **The canonical numbering**: a node is numbered by its position in `allL`. -/
def canonR : List (ℕ × ℕ) :=
  (List.range (allL t).length).filterMap fun p => (allL t)[p]?.map (p, ·)

variable {t}

theorem mem_canonR {p a : ℕ} : (p, a) ∈ canonR t ↔ (allL t)[p]? = some a := by
  simp only [canonR, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨q, -, b, hb, rfl, rfl⟩
    exact hb
  · intro h
    exact ⟨p, (List.getElem?_eq_some_iff.1 h).1, a, h, rfl, rfl⟩

theorem nodup_allL : (allL t).Nodup := by
  refine List.Nodup.append (List.nodup_dedup _) ((List.nodup_dedup _).filter _) ?_
  intro a ha hb
  simp only [List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 (List.mem_dedup.1 ha)

theorem mem_allL {a : ℕ} : a ∈ allL t ↔ a ∈ wnodes t := by
  simp only [allL, List.mem_append, List.mem_dedup, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact List.mem_append_left _ h
    · exact h
  · intro h
    by_cases hi : a ∈ t.ids
    · exact Or.inl hi
    · exact Or.inr ⟨h, hi⟩

theorem length_allL_le : (allL t).length ≤ (wnodes t).length := by
  have h1 := nodup_allL (t := t)
  have : (allL t).toFinset ⊆ (wnodes t).toFinset := fun a ha =>
    List.mem_toFinset.2 (mem_allL.1 (List.mem_toFinset.1 ha))
  rw [← List.toFinset_card_of_nodup h1]
  exact (Finset.card_le_card this).trans (List.toFinset_card_le _)

theorem getElem?_allL_of_lt {p : ℕ} (hp : p < t.ids.dedup.length) :
    (allL t)[p]? = t.ids.dedup[p]? := by
  rw [allL, List.getElem?_append_left hp]

theorem lt_of_getElem?_allL {p i : ℕ} (h : (allL t)[p]? = some i) (hi : i ∈ t.ids) :
    p < t.ids.dedup.length := by
  by_contra hp
  rw [allL, List.getElem?_append_right (by omega)] at h
  have := List.mem_of_getElem? h
  simp only [List.mem_filter, decide_eq_true_eq] at this
  exact this.2 hi

theorem witR_canonR : WitR t (canonR t) where
  total i hi := by
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 (mem_allL.2 (List.mem_append_left _ hi))
    exact ⟨p, mem_canonR.2 hp⟩
  endp e he := by
    have h1 : e.1 ∈ wnodes t := List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, by simp⟩)
    have h2 : e.2 ∈ wnodes t := List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, by simp⟩)
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 (mem_allL.2 h1)
    obtain ⟨p', hp'⟩ := List.mem_iff_getElem?.1 (mem_allL.2 h2)
    exact ⟨⟨p, mem_canonR.2 hp⟩, ⟨p', mem_canonR.2 hp'⟩⟩
  node p a h := mem_allL.1 (List.mem_of_getElem? (mem_canonR.1 h))
  func p p' a h h' := by
    have h1 := mem_canonR.1 h
    have h2 := mem_canonR.1 h'
    obtain ⟨hp, e1⟩ := List.getElem?_eq_some_iff.1 h1
    obtain ⟨hp', e2⟩ := List.getElem?_eq_some_iff.1 h2
    exact (List.Nodup.getElem_inj_iff nodup_allL).1 (e1.trans e2.symm)
  inj p a b h h' := by
    have h1 := mem_canonR.1 h
    have h2 := mem_canonR.1 h'
    rw [h1] at h2
    exact Option.some.inj h2
  down p i hi h := by
    have h1 := mem_canonR.1 h
    have hlt := lt_of_getElem?_allL h1 hi
    have hp : p < t.ids.dedup.length := by omega
    refine ⟨t.ids.dedup[p], List.mem_dedup.1 (List.getElem_mem hp), mem_canonR.2 ?_⟩
    rw [getElem?_allL_of_lt hp, List.getElem?_eq_getElem hp]
  downAll p a h := by
    have h1 := mem_canonR.1 h
    have hp : p < (allL t).length := by
      have := (List.getElem?_eq_some_iff.1 h1).1
      omega
    exact ⟨_, mem_canonR.2 (List.getElem?_eq_getElem hp)⟩

theorem card_ids_eq_length_dedup : t.ids.toFinset.card = t.ids.dedup.length :=
  List.card_toFinset _

/-- In the canonical numbering, every number is below the number of nodes listed. -/
theorem lt_of_mem_canonR {p a : ℕ} (h : (p, a) ∈ canonR t) : p < (wnodes t).length :=
  lt_of_lt_of_le (List.getElem?_eq_some_iff.1 (mem_canonR.1 h)).1 length_allL_le

end Canon

end SeqG

end Syn

end HTN
