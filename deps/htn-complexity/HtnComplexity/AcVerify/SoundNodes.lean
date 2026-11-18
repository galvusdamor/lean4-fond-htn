import HtnComplexity.AcVerify.Complete
/-!
# Soundness of path witnesses, part 1: the nodes of the tree

A path witness `W` (`HTN.Syn.AcVer.PathOK`) describes a decomposition tree.  Its **nodes**
(`HTN.Syn.AcVer.IsNode`) are the nonempty prefixes of the paths of its entries, the dummy last step
of an empty leaf excluded.  This file collects what the construction of the decomposition sequence
(`HtnComplexity/AcVerify/Sound.lean`) needs about them: every node is a well-formed path,
the tree is consistent (all entries through a node continue with the same method,
`HTN.Syn.AcVer.methOf`), complete (every task of that method is a child node), the roots are the
tasks of the initial task network, and the primitive nodes are exactly the action leaves.
-/

namespace HTN

namespace Syn

namespace AcVer

variable {d : DomDesc} {q : InstDesc} {W : List Entry}

/-! ### Pairs of entries -/

theorem PairOK.path_ne {u v : Entry} (h : PairOK d q u v) : u.1 ≠ v.1 := by
  obtain ⟨x, y, hd, -, -⟩ := h
  intro he
  exact not_prefix_of_divAt hd (he ▸ List.prefix_refl _)

theorem pairwise_or {R : Entry → Entry → Prop} :
    ∀ {l : List Entry}, l.Pairwise R → ∀ {u v : Entry}, u ∈ l → v ∈ l → u ≠ v → R u v ∨ R v u
  | [], _, _, _, hu, _, _ => absurd hu List.not_mem_nil
  | a :: l, h, u, v, hu, hv, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hu with rfl | hu' <;> rcases List.mem_cons.1 hv with rfl | hv'
    · exact absurd rfl hne
    · exact Or.inl (h.1 v hv')
    · exact Or.inr (h.1 u hu')
    · exact pairwise_or h.2 hu' hv' hne

theorem PathOK.pair (hW : PathOK d q W) {u v : Entry} (hu : u ∈ W) (hv : v ∈ W) (hne : u ≠ v) :
    PairOK d q u v ∨ PairOK d q v u :=
  pairwise_or hW.pairs hu hv hne

/-- Distinct entries have distinct paths. -/
theorem PathOK.path_inj (hW : PathOK d q W) {u v : Entry} (hu : u ∈ W) (hv : v ∈ W)
    (h : u.1 = v.1) : u = v := by
  by_contra hne
  rcases hW.pair hu hv hne with h' | h'
  · exact h'.path_ne h
  · exact h'.path_ne h.symm

/-- **Consistency**: two entries through the same node continue with the same method. -/
theorem PathOK.consistent (hW : PathOK d q W) {u v : Entry} (hu : u ∈ W) (hv : v ∈ W)
    {N : List PStep} {y y' : PStep} {s s' : List PStep} (hus : u.1 = N ++ y :: s)
    (hvs : v.1 = N ++ y' :: s') : y.1 = y'.1 := by
  by_cases hyy : y = y'
  · rw [hyy]
  have hd : DivAt u.1 v.1 y y' := ⟨N, s, s', hus, hvs, hyy⟩
  have hne : u ≠ v := by
    rintro rfl
    exact not_prefix_of_divAt hd (List.prefix_refl _)
  rcases hW.pair hu hv hne with ⟨x, z, hd', hxz, -⟩ | ⟨x, z, hd', hxz, -⟩
  · obtain ⟨rfl, rfl⟩ := divAt_unique hd hd'
    exact hxz
  · obtain ⟨rfl, rfl⟩ := divAt_unique (divAt_symm hd) hd'
    exact hxz.symm

/-! ### Entries are chains -/

theorem EntryOK.isChain {u : Entry} (h : EntryOK d q u) : u.1.IsChain (Link d q) := by
  unfold EntryOK at h
  split_ifs at h
  · obtain ⟨-, -, -, -, -, hc, -⟩ := h
    exact hc
  · exact h.1.2.1

theorem link_of_append {p N : List PStep} {y : PStep} {s : List PStep}
    (hc : p.IsChain (Link d q)) (hp : p = N ++ y :: s) :
    ∀ x ∈ N.getLast?, Link d q x y := by
  subst hp
  have := (List.isChain_append.1 hc).2.2
  intro x hx
  exact this x hx y (by simp)

theorem NodeOK.of_prefix {p N : List PStep} (h : NodeOK d q p) (hN : N ≠ []) (hpre : N <+: p) :
    NodeOK d q N := by
  obtain ⟨⟨i, s, rfl⟩, hc, hin⟩ := h
  obtain ⟨r, hr⟩ := hpre
  refine ⟨?_, ?_, fun x hx => hin x (hpre_mem hr hx)⟩
  · rcases N with _ | ⟨z, N⟩
    · exact absurd rfl hN
    · simp only [List.cons_append, List.cons.injEq] at hr
      exact ⟨i, N, by rw [hr.1]⟩
  · rw [← hr] at hc
    exact (List.isChain_append.1 hc).1
where
  hpre_mem {N r p : List PStep} (hr : N ++ r = p) {x : PStep} (hx : x ∈ N) : x ∈ p := by
    rw [← hr]; exact List.mem_append_left _ hx

/-! ### Nodes -/

/-- **A node of the tree** described by a path witness: a nonempty prefix of the path of an
entry, the dummy last step of an empty leaf excluded. -/
def IsNode (W : List Entry) (N : List PStep) : Prop :=
  N ≠ [] ∧ ∃ u ∈ W, N <+: u.1 ∧ (u.2 = true → N ≠ u.1)

/-- A node path of an entry is well formed. -/
theorem PathOK.nodeOK (hW : PathOK d q W) {N : List PStep} (hN : IsNode W N) : NodeOK d q N := by
  obtain ⟨hne, u, hu, hpre, heps⟩ := hN
  have he := hW.entries u hu
  unfold EntryOK at he
  split_ifs at he with h2
  · obtain ⟨p, y, hpy, -, hp, -, -⟩ := he
    have hNp : N <+: p := by
      rw [hpy] at hpre
      rcases List.prefix_concat_iff.1 hpre with h | h
      · exact absurd (h.trans hpy.symm) (heps h2)
      · exact h
    exact hp.of_prefix hne hNp
  · exact he.1.of_prefix hne hpre

theorem IsNode.of_prefix {N M : List PStep} (hN : IsNode W N) (hM : M ≠ [])
    (hpre : M <+: N) : IsNode W M := by
  obtain ⟨-, u, hu, hNu, heps⟩ := hN
  refine ⟨hM, u, hu, hpre.trans hNu, fun h2 hMu => heps h2 ?_⟩
  rw [hMu] at hpre
  exact List.IsPrefix.eq_of_length hNu (le_antisymm hNu.length_le hpre.length_le)

theorem PathOK.entry_ne_nil (hW : PathOK d q W) {u : Entry} (hu : u ∈ W) : u.1 ≠ [] := by
  have he := hW.entries u hu
  unfold EntryOK at he
  split_ifs at he
  · obtain ⟨p, y, hpy, -⟩ := he
    rw [hpy]; simp
  · exact he.1.ne_nil

/-- The path of an action leaf is a node. -/
theorem PathOK.isNode_leaf (hW : PathOK d q W) {u : Entry} (hu : u ∈ W) (h2 : u.2 = false) :
    IsNode W u.1 :=
  ⟨hW.entry_ne_nil hu, u, hu, List.prefix_refl _, fun h => absurd (h2.symm.trans h) (by simp)⟩

/-- A compound node is continued by some entry. -/
theorem PathOK.compound_ext (hW : PathOK d q W) {N : List PStep} (hN : IsNode W N) {c : ℕ}
    (hc : lastLabel d q N = Sum.inr c) : ∃ u ∈ W, ∃ y s, u.1 = N ++ y :: s := by
  obtain ⟨-, u, hu, ⟨r, hr⟩, heps⟩ := hN
  rcases r with _ | ⟨y, s⟩
  · simp only [List.append_nil] at hr
    have he := hW.entries u hu
    unfold EntryOK at he
    split_ifs at he with h2
    · exact absurd hr (heps h2)
    · obtain ⟨a, ha⟩ := he.2
      rw [← hr, hc] at ha
      cases ha
  · exact ⟨u, hu, y, s, hr.symm⟩

/-- A primitive node is the path of an action leaf. -/
theorem PathOK.prim_entry (hW : PathOK d q W) {N : List PStep} (hN : IsNode W N) {a : ℕ}
    (ha : lastLabel d q N = Sum.inl a) : ∃ u ∈ W, u.1 = N ∧ u.2 = false := by
  obtain ⟨hne, u, hu, ⟨r, hr⟩, heps⟩ := hN
  rcases r with _ | ⟨y, s⟩
  · simp only [List.append_nil] at hr
    refine ⟨u, hu, hr.symm, ?_⟩
    cases h2 : u.2
    · rfl
    · exact absurd hr (heps h2)
  · have hl := link_of_append (hW.entries u hu).isChain hr.symm
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (by simpa using hne : N.getLast? ≠ none)
    obtain ⟨-, -, hlab⟩ := hl x hx
    rw [lastLabel_eq_of_getLast? hx, hlab] at ha
    cases ha

/-- What a child node tells about its parent. -/
theorem PathOK.child (hW : PathOK d q W) {N : List PStep} {z : PStep} (hN : IsNode W (N ++ [z]))
    (hne : N ≠ []) :
    (∃ u ∈ W, ∃ s, u.1 = N ++ z :: s) ∧ (∀ x ∈ N.getLast?, Link d q x z) ∧ StepIn d q z ∧
      IsNode W N := by
  have hnode := hW.nodeOK hN
  obtain ⟨-, u, hu, ⟨r, hr⟩, heps⟩ := hN
  have hus : u.1 = N ++ z :: r := by rw [← hr]; simp
  refine ⟨⟨u, hu, r, hus⟩, link_of_append (hW.entries u hu).isChain hus,
    hnode.2.2 z (by simp), hne, u, hu, ⟨z :: r, hus.symm⟩, fun _ h => ?_⟩
  rw [h] at hus
  simp at hus

/-- The node `N` is compound when it has a child. -/
theorem PathOK.parent_compound (hW : PathOK d q W) {N : List PStep} {z : PStep}
    (hN : IsNode W (N ++ [z])) (hne : N ≠ []) : ∃ c, lastLabel d q N = Sum.inr c := by
  obtain ⟨-, hl, -, -⟩ := hW.child hN hne
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (by simpa using hne : N.getLast? ≠ none)
  obtain ⟨-, -, hlab⟩ := hl x hx
  exact ⟨_, by rw [lastLabel_eq_of_getLast? hx, hlab]⟩

open Classical in
/-- **The method chosen at a node**: the network index of the step following the node in the
entries through it (they all agree, `HTN.Syn.AcVer.PathOK.consistent`). -/
noncomputable def methOf (W : List Entry) (N : List PStep) : ℕ :=
  if h : ∃ y : PStep, ∃ u ∈ W, ∃ s, u.1 = N ++ y :: s then (Classical.choose h).1 else 0

theorem PathOK.methOf_eq (hW : PathOK d q W) {N : List PStep} {u : Entry} (hu : u ∈ W)
    {y : PStep} {s : List PStep} (hus : u.1 = N ++ y :: s) : methOf W N = y.1 := by
  have h : ∃ y : PStep, ∃ u ∈ W, ∃ s, u.1 = N ++ y :: s := ⟨y, u, hu, s, hus⟩
  rw [methOf, dif_pos h]
  obtain ⟨v, hv, s', hvs⟩ := Classical.choose_spec h
  exact hW.consistent hv hu hvs hus

/-- **Completeness**: every task of the chosen method is a child node. -/
theorem PathOK.child_node (hW : PathOK d q W) {N : List PStep} (hne : N ≠ []) {u : Entry}
    (hu : u ∈ W) {y : PStep} {s : List PStep} (hus : u.1 = N ++ y :: s) {j : ℕ}
    (hj : j ∈ (netOf d q y.1).ids) : IsNode W (N ++ [(y.1, j)]) := by
  obtain ⟨P, x, rfl⟩ : ∃ P x, N = P ++ [x] :=
    ⟨N.dropLast, N.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨v, hv, s', hvs⟩ := hW.children u hu P x y s (by simp [hus]) j hj
  refine ⟨by simp, v, hv, ⟨s', by simp [hvs]⟩, fun h2 heq => ?_⟩
  have he := hW.entries v hv
  simp only [EntryOK, h2, if_true] at he
  obtain ⟨p, y', hpy, -, -, -, hnil⟩ := he
  rw [← heq] at hpy
  obtain ⟨-, hy'⟩ := List.append_inj' hpy rfl
  simp only [List.cons.injEq, and_true] at hy'
  subst hy'
  rw [hnil] at hj
  simp at hj

/-- The tasks of the initial task network are nodes. -/
theorem PathOK.root_node (hW : PathOK d q W) {i : ℕ} (hi : i ∈ q.tnI.ids) :
    IsNode W [(0, i)] := by
  obtain ⟨u, hu, s, hus⟩ := hW.roots i hi
  refine ⟨by simp, u, hu, ⟨s, by simp [hus]⟩, fun h2 heq => ?_⟩
  have he := hW.entries u hu
  simp only [EntryOK, h2, if_true] at he
  obtain ⟨p, y', hpy, hp, -⟩ := he
  rw [← heq] at hpy
  have := congrArg List.length hpy
  simp only [List.length_singleton, List.length_append] at this
  have : p.length ≠ 0 := by simpa using hp
  omega

/-- The nodes of length one are the tasks of the initial task network. -/
theorem PathOK.root_of_node (hW : PathOK d q W) {N : List PStep} (hN : IsNode W N)
    (h1 : N.length = 1) : ∃ i ∈ q.tnI.ids, N = [(0, i)] := by
  obtain ⟨⟨i, s, rfl⟩, -, hin⟩ := hW.nodeOK hN
  have hs : s = [] := by simpa using h1
  subst hs
  have := hin (0, i) (by simp)
  simp only [StepIn, netOf_zero] at this
  exact ⟨i, this, rfl⟩

end AcVer

end Syn

end HTN
