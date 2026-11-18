import ComplexityTheory.UODecide.Tree
/-!
# Derivation trees: a decomposition with polynomial height

`ComplexityTheory/UODecide/Tree.lean` writes every derivation tree as a base tree of height at
most `|K|·2^|K|` plus small pumps (`HTN.CTree.decomp`).  The exponential height comes from keeping
the *label set of every subtree* fixed.  For the polynomial-space bound only the label set of the
*whole tree* has to be kept, and then a quadratic height suffices:

* `HTN.CTree.exists_removable_poly` — a tree of height at least `(|K|+1)²` whose labels lie in
  `K` has a nonempty pump whose removal keeps the label set of the whole tree.  Cut a long chain
  of nested subtrees into `|K|+1` segments of length `|K|+1`; each contains a pump; if every pump
  carried a label occurring nowhere else, these labels would be pairwise distinct;
* `HTN.CTree.decompP` — the decomposition theorem with base height `pH K = (|K|+1)² - 1`, for any
  size bound `g` of trees in terms of their height;
* `HTN.CTree.DT.size_le_lin` — trees of a *linear* grammar (at most one nonterminal per body) have
  size linear in their height.
-/

namespace HTN

namespace CTree

variable {N T : Type} [DecidableEq N] {R : N → Multiset (N ⊕ T) → Prop}

/-- The polynomial height bound `(|K|+1)² - 1`. -/
def pH (K : Finset N) : ℕ := K.card * K.card + 2 * K.card

theorem root_mem_labels_of_root {s : DT N T} {X : N} (h : s.root = Sum.inl X) : X ∈ s.labels := by
  cases s with
  | leaf => simp at h
  | node Y ts =>
    simp only [DT.root_node, Sum.inl.injEq] at h
    subst h
    exact DT.root_mem_labels

/-- **A high tree contains a pump whose removal keeps the label set of the whole tree.** -/
theorem exists_removable_poly (K : Finset N) {t : DT N T} (hK : t.labels ⊆ K)
    (hh : pH K + 1 ≤ t.height) :
    ∃ (A B : Ctx N T) (s : DT N T), t = A.plug (B.plug s) ∧ B ≠ Ctx.hole ∧
      (∃ c, s.root = Sum.inl c) ∧ B.rootC s.root = s.root ∧
      (A.plug s).labels = (A.plug (B.plug s)).labels := by
  classical
  set k := K.card with hk
  obtain ⟨f, hf1, hf2⟩ := exists_chain (pH K) t hh
  have hpH : pH K = k * (k + 1) + k := by simp only [pH, ← hk]; ring
  -- labels of the chain
  have hsubK : ∀ j ≤ pH K, (f j).2.labels ⊆ K := by
    intro j hj Y hY
    apply hK
    rw [(hf1 j hj).1, Ctx.labels_plug]
    exact Finset.mem_union_right _ hY
  have hrootK : ∀ j ≤ pH K, (f j).2.root ∈ K.image (Sum.inl : N → N ⊕ T) := by
    intro j hj
    obtain ⟨X, hX⟩ := (hf1 j hj).2
    rw [hX]
    exact Finset.mem_image_of_mem _ (hsubK j hj (root_mem_labels_of_root hX))
  -- one pump per segment
  have seg : ∀ r, r ≤ k → ∃ i j, r * (k + 1) ≤ i ∧ i < j ∧ j ≤ r * (k + 1) + k ∧
      (f i).2.root = (f j).2.root := by
    intro r hr
    have hmaps : ∀ p ∈ Finset.range (k + 1), (fun p => (f (r * (k + 1) + p)).2.root) p ∈
        K.image (Sum.inl : N → N ⊕ T) := by
      intro p hp
      have : p ≤ k := by have := Finset.mem_range.1 hp; omega
      refine hrootK _ ?_
      rw [hpH]
      nlinarith
    have hcard : (K.image (Sum.inl : N → N ⊕ T)).card < (Finset.range (k + 1)).card := by
      rw [Finset.card_range]
      have := Finset.card_image_le (s := K) (f := (Sum.inl : N → N ⊕ T))
      omega
    obtain ⟨p, hp, q, hq, hpq, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    have hp' : p ≤ k := by have := Finset.mem_range.1 hp; omega
    have hq' : q ≤ k := by have := Finset.mem_range.1 hq; omega
    rcases lt_or_gt_of_ne hpq with h | h
    · exact ⟨_, _, by omega, by omega, by omega, heq⟩
    · exact ⟨_, _, by omega, by omega, by omega, heq.symm⟩
  choose! I J hIJ using seg
  have hJle : ∀ r, r ≤ k → J r ≤ pH K := by
    intro r hr
    have := (hIJ r hr).2.2.1
    rw [hpH]
    nlinarith
  have hpump : ∀ r, r ≤ k → ∃ B : Ctx N T, B ≠ Ctx.hole ∧ (f (I r)).2 = B.plug (f (J r)).2 :=
    fun r hr => hf2 _ _ (hIJ r hr).2.1 (hJle r hr)
  haveI : Nonempty (Ctx N T) := ⟨Ctx.hole⟩
  obtain ⟨X₀, -⟩ := (hf1 0 (Nat.zero_le _)).2
  haveI : Nonempty N := ⟨X₀⟩
  choose! Bf hBf using hpump
  -- some pump carries no new label
  obtain ⟨r, hr, hgood⟩ : ∃ r, r ≤ k ∧
      (Bf r).labelsC ⊆ (f (I r)).1.labelsC ∪ (f (J r)).2.labels := by
    by_contra hno
    push_neg at hno
    have hX : ∀ r, r ≤ k → ∃ X ∈ (Bf r).labelsC,
        X ∉ (f (I r)).1.labelsC ∪ (f (J r)).2.labels := by
      intro r hr
      exact Finset.not_subset.1 (hno r hr)
    choose! X hXmem hXnot using hX
    -- the new labels are in `K`
    have hXK : ∀ r ∈ Finset.range (k + 1), X r ∈ K := by
      intro r hr
      have hr' : r ≤ k := by have := Finset.mem_range.1 hr; omega
      apply hsubK (I r) (by have := hJle r hr'; have := (hIJ r hr').2.1; omega)
      rw [(hBf r hr').2, Ctx.labels_plug]
      exact Finset.mem_union_left _ (hXmem r hr')
    -- and pairwise distinct
    have hinj : Set.InjOn X (Finset.range (k + 1)) := by
      intro r₁ hr₁ r₂ hr₂ heq
      by_contra hne
      have h₁ : r₁ ≤ k := by have := Finset.mem_range.1 hr₁; omega
      have h₂ : r₂ ≤ k := by have := Finset.mem_range.1 hr₂; omega
      have key : ∀ a b, a ≤ k → b ≤ k → a < b → X a ≠ X b := by
        intro a b ha hb hab hXab
        have hJI : J a < I b := by
          have := (hIJ a ha).2.2.1
          have := (hIJ b hb).1
          nlinarith
        obtain ⟨C, -, hC⟩ := hf2 _ _ hJI (by have := hJle b hb; have := (hIJ b hb).2.1; omega)
        have hmem : X b ∈ (f (J a)).2.labels := by
          rw [hC, Ctx.labels_plug, (hBf b hb).2, Ctx.labels_plug]
          exact Finset.mem_union_right _ (Finset.mem_union_left _ (hXmem b hb))
        exact hXnot a ha (Finset.mem_union_right _ (hXab ▸ hmem))
      rcases lt_or_gt_of_ne hne with h | h
      · exact key r₁ r₂ h₁ h₂ h heq
      · exact key r₂ r₁ h₂ h₁ h heq.symm
    have := Finset.card_le_card_of_injOn X (fun r hr => hXK r hr) hinj
    rw [Finset.card_range] at this
    omega
  refine ⟨(f (I r)).1, Bf r, (f (J r)).2, ?_, (hBf r hr).1, (hf1 _ (hJle r hr)).2, ?_, ?_⟩
  · rw [← (hBf r hr).2]
    exact (hf1 _ (by have := hJle r hr; have := (hIJ r hr).2.1; omega)).1
  · rw [← Ctx.root_plug, ← (hBf r hr).2]
    exact (hIJ r hr).2.2.2
  · rw [Ctx.labels_plug, Ctx.labels_plug, Ctx.labels_plug]
    ext Y
    simp only [Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h
      · rcases Finset.mem_union.1 (hgood h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact Or.inr h

/-- **Reduction** (polynomial height): a tree is a tree of height at most `pH K` plus pumps of size at most its
own size, the heads of the pumps among its labels. -/
theorem reduceP (K : Finset N) : ∀ (n : ℕ) (t : DT N T), t.size = n → t.Valid R →
    t.labels ⊆ K →
    ∃ (t₀ : DT N T) (ps : List (N × Ctx N T)), t₀.Valid R ∧ t₀.root = t.root ∧
      t₀.labels = t.labels ∧ t₀.height ≤ pH K ∧ t₀.height ≤ t.height ∧
      (∀ p ∈ ps, IsPump R p.1 p.2 ∧ p.1 ∈ t.labels ∧ p.2.size ≤ t.size) ∧
      t.yield = t₀.yield + (ps.map (fun p => p.2.yieldC)).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hn ht hK
    by_cases hh : t.height ≤ pH K
    · exact ⟨t, [], ht, rfl, rfl, hh, le_rfl, by simp, by simp⟩
    push_neg at hh
    obtain ⟨A, B, s, rfl, hB, ⟨c, hc⟩, hroot, hlab⟩ := exists_removable_poly K hK hh
    obtain ⟨hA, hBs⟩ := Ctx.valid_plug.1 ht
    obtain ⟨hBv, hs⟩ := Ctx.valid_plug.1 hBs
    have hAs : (A.plug s).Valid R := by
      refine Ctx.valid_plug.2 ⟨?_, hs⟩
      rw [Ctx.root_plug, hroot] at hA
      exact hA
    have hlabs : (A.plug s).labels = (A.plug (B.plug s)).labels := hlab
    have hsize : (A.plug (B.plug s)).size = (A.plug s).size + B.size := by
      rw [Ctx.size_plug, Ctx.size_plug, Ctx.size_plug]
      ring
    have hBpos := Ctx.size_pos_of_ne_hole hB
    obtain ⟨t₀, ps, h₀, hr₀, hl₀, hh₀, hh₀', hps, hy₀⟩ :=
      ih (A.plug s).size (by omega) (A.plug s) rfl hAs (hlabs ▸ hK)
    have hheight : (A.plug s).height ≤ (A.plug (B.plug s)).height :=
      Ctx.height_plug_mono A (Ctx.height_le_plug B s)
    refine ⟨t₀, (c, B) :: ps, h₀, ?_, hl₀.trans hlabs, hh₀, hh₀'.trans hheight, ?_, ?_⟩
    · rw [hr₀, Ctx.root_plug, Ctx.root_plug, Ctx.root_plug, hroot]
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨⟨hc ▸ hBv, hc ▸ hroot⟩, ?_, by show B.size ≤ _; omega⟩
        rw [Ctx.labels_plug, Ctx.labels_plug]
        refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
        cases s with
        | leaf => simp at hc
        | node Y ts =>
          simp only [DT.root_node, Sum.inl.injEq] at hc
          subst hc
          exact DT.root_mem_labels
      · obtain ⟨h1, h2, h3⟩ := hps p hp
        exact ⟨h1, hlabs ▸ h2, by omega⟩
    · have h1 : (A.plug (B.plug s)).yield = (A.plug s).yield + B.yieldC := by
        rw [Ctx.yield_plug, Ctx.yield_plug, Ctx.yield_plug]
        abel
      rw [h1, hy₀]
      simp only [List.map_cons, List.sum_cons]
      abel

/-- **The decomposition theorem, polynomial-height form.**  Let the labels of a derivation tree
`t` lie in `K`, and let `g` bound the size of valid trees with labels in `K` in terms of their
height.  Then `t` is a tree `t₀` of height at most `pH K = (|K|+1)² - 1`, with the same root and
the same labels, plus a list of pumps, each of size at most `g (pH K + 1)` and with its head among
the labels of `t₀`. -/
theorem decompP (K : Finset N) (g : ℕ → ℕ) (hgm : Monotone g)
    (hg : ∀ t : DT N T, t.Valid R → t.labels ⊆ K → t.size ≤ g t.height) :
    ∀ (n : ℕ) (t : DT N T), t.size = n → t.Valid R → t.labels ⊆ K →
    ∃ (t₀ : DT N T) (ps : List (N × Ctx N T)), t₀.Valid R ∧ t₀.root = t.root ∧
      t₀.labels = t.labels ∧ t₀.height ≤ pH K ∧
      (∀ p ∈ ps, IsPump R p.1 p.2 ∧ p.1 ∈ t₀.labels ∧
        p.2.size ≤ g (pH K + 1)) ∧
      t.yield = t₀.yield + (ps.map (fun p => p.2.yieldC)).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hn ht hK
    cases t with
    | leaf a => exact ⟨DT.leaf a, [], ht, rfl, rfl, by simp, by simp, by simp⟩
    | node X ts =>
      obtain ⟨hR, hch⟩ := DT.Valid.children ht
      let P : DT N T → DT N T × List (N × Ctx N T) → Prop := fun u v =>
        v.1.Valid R ∧ v.1.root = u.root ∧ v.1.labels = u.labels ∧
        v.1.height ≤ pH K ∧
        (∀ p ∈ v.2, IsPump R p.1 p.2 ∧ p.1 ∈ v.1.labels ∧
          p.2.size ≤ g (pH K + 1)) ∧
        u.yield = v.1.yield + (v.2.map (fun p => p.2.yieldC)).sum
      obtain ⟨vs, hvs⟩ := exists_forall₂ (P := P) ts (fun u hu => by
        obtain ⟨t₀, ps, h⟩ := ih u.size (hn ▸ DT.size_lt_of_mem hu) u rfl (hch u hu)
          ((DT.labels_subset_of_mem hu).trans hK)
        exact ⟨(t₀, ps), h⟩)
      let t₁ : DT N T := DT.node X (vs.map Prod.fst)
      have hroots : (vs.map Prod.fst).map DT.root = ts.map DT.root := by
        rw [List.map_map]
        exact (forall₂_map_eq (fun u v (h : P u v) => h.2.1.symm) hvs).symm
      have hlabs : (vs.map Prod.fst).map DT.labels = ts.map DT.labels := by
        rw [List.map_map]
        exact (forall₂_map_eq (fun u v (h : P u v) => h.2.2.1.symm) hvs).symm
      have hyields : ts.map DT.yield =
          vs.map (fun v => v.1.yield + (v.2.map (fun p => p.2.yieldC)).sum) :=
        forall₂_map_eq (fun u v (h : P u v) => h.2.2.2.2.2) hvs
      have ht₁ : t₁.Valid R := by
        refine DT.Valid.node X _ (by rw [hroots]; exact hR) ?_
        intro w hw
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
        obtain ⟨u, -, huv⟩ := forall₂_mem_right hvs v hv
        exact huv.1
      have hl₁ : t₁.labels = (DT.node X ts).labels := by
        simp only [t₁, DT.labels_node, hlabs]
      have hh₁ : t₁.height ≤ pH K + 1 := by
        simp only [t₁, DT.height_node]
        have : ((vs.map Prod.fst).map DT.height).foldr max 0 ≤ pH K := by
          refine (foldr_max_le_iff DT.height _ _).2 ?_
          intro w hw
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
          obtain ⟨u, -, huv⟩ := forall₂_mem_right hvs v hv
          exact huv.2.2.2.1
        omega
      let qs : List (N × Ctx N T) := vs.flatMap Prod.snd
      have hy₁ : (DT.node X ts).yield = t₁.yield + (qs.map (fun p => p.2.yieldC)).sum := by
        simp only [DT.yield_node, hyields, t₁, qs, sum_flatMap_map, List.map_map]
        rw [← List.sum_map_add]
        rfl
      obtain ⟨t₀, ps, h₀, hr₀, hl₀, hh₀, -, hps, hy₀⟩ :=
        reduceP K t₁.size t₁ rfl ht₁ (hl₁ ▸ hK)
      have hsize₁ : t₁.size ≤ g (pH K + 1) :=
        (hg t₁ ht₁ (hl₁ ▸ hK)).trans (hgm hh₁)
      refine ⟨t₀, qs ++ ps, h₀, hr₀, hl₀.trans hl₁, hh₀, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨v, hv, hpv⟩ := List.mem_flatMap.1 hp
          obtain ⟨u, -, huv⟩ := forall₂_mem_right hvs v hv
          obtain ⟨h1, h2, h3⟩ := huv.2.2.2.2.1 p hpv
          refine ⟨h1, ?_, h3⟩
          rw [hl₀]
          exact DT.mem_labels_node.2 (Or.inr ⟨v.1, List.mem_map_of_mem hv, h2⟩)
        · obtain ⟨h1, h2, h3⟩ := hps p hp
          exact ⟨h1, hl₀ ▸ h2, h3.trans hsize₁⟩
      · rw [hy₁, hy₀, List.map_append, List.sum_append]
        abel


/-! ### Linear grammars -/

omit [DecidableEq N] in
theorem sum_size_le_lin_aux (c : ℕ) : ∀ ts : List (DT N T),
    (∀ u ∈ ts, u.root.isLeft = false → u.size = 1) → (∀ u ∈ ts, u.size ≤ c) →
    (ts.filter (fun u => u.root.isLeft)).length ≤ 1 → (ts.map DT.size).sum ≤ ts.length + c
  | [], _, _, _ => by simp
  | u :: ts, h1, hc, hf => by
    have h1' : ∀ v ∈ ts, v.root.isLeft = false → v.size = 1 :=
      fun v hv => h1 v (List.mem_cons_of_mem _ hv)
    have hc' : ∀ v ∈ ts, v.size ≤ c := fun v hv => hc v (List.mem_cons_of_mem _ hv)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    cases hu : u.root.isLeft with
    | true =>
      rw [List.filter_cons_of_pos (p := fun u : DT N T => u.root.isLeft) hu,
        List.length_cons] at hf
      have hnil : ts.filter (fun u => u.root.isLeft) = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hall : ∀ v ∈ ts, v.size = 1 := by
        intro v hv
        refine h1' v hv ?_
        by_contra hne
        have : v ∈ ts.filter (fun u => u.root.isLeft) :=
          List.mem_filter.2 ⟨hv, by simpa using hne⟩
        rw [hnil] at this
        simp at this
      have : (ts.map DT.size).sum = ts.length := by
        rw [List.map_congr_left hall]
        simp
      have := hc u (by simp)
      omega
    | false =>
      rw [List.filter_cons_of_neg (p := fun u : DT N T => u.root.isLeft) (by simp [hu])] at hf
      have := sum_size_le_lin_aux c ts h1' hc' hf
      have := h1 u (by simp) hu
      omega

/-- **Trees of a linear grammar are small**: if every rule body for a nonterminal in `K` has at
most `M` symbols, at most one of them a nonterminal, then a valid tree with labels in `K` has at
most `(M+1)·(height+1)` nodes. -/
theorem DT.size_le_lin (K : Finset N) {M : ℕ} (hM : ∀ X ∈ K, ∀ β, R X β → Multiset.card β ≤ M)
    (h1 : ∀ X ∈ K, ∀ β, R X β → (β.filter fun x => x.isLeft = true).card ≤ 1) {t : DT N T}
    (ht : t.Valid R) (hK : t.labels ⊆ K) : t.size ≤ (M + 1) * (t.height + 1) := by
  induction ht with
  | leaf x => simp
  | node X ts hR hch ih =>
    have hX : X ∈ K := hK DT.root_mem_labels
    set hc := (ts.map DT.height).foldr max 0 with hhc
    have hlen : ts.length ≤ M := by simpa using hM X hX _ hR
    have hfil : (ts.filter (fun u => u.root.isLeft)).length ≤ 1 := by
      have := h1 X hX _ hR
      rw [Multiset.filter_coe, Multiset.coe_card, List.filter_map] at this
      simpa [Function.comp_def] using this
    have hleaf : ∀ u ∈ ts, u.root.isLeft = false → u.size = 1 := by
      intro u _ hu
      cases u with
      | leaf => simp
      | node => simp at hu
    have hbound : ∀ u ∈ ts, u.size ≤ (M + 1) * (hc + 1) := by
      intro u hu
      have := ih u hu ((DT.labels_subset_of_mem hu).trans hK)
      have hle : u.height ≤ hc := le_foldr_max DT.height hu
      calc u.size ≤ (M + 1) * (u.height + 1) := this
        _ ≤ (M + 1) * (hc + 1) := Nat.mul_le_mul_left _ (by omega)
    have := sum_size_le_lin_aux _ ts hleaf hbound hfil
    rw [DT.size_node, DT.height_node, ← hhc]
    nlinarith

end CTree

end HTN
