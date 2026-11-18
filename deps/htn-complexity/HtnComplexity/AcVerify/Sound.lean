import HtnComplexity.AcVerify.SoundNodes
/-!
# Soundness of path witnesses: a path witness yields a solution

`HTN.Syn.AcVer.solvable_of_pathOK` — if the described problem `(d, q)` has a path witness, it is
solvable.

The decomposition tree described by the witness is expanded node by node.  After expanding a set
`X` of compound nodes that is closed under taking prefixes (`HTN.Syn.AcVer.Closed`), the current
task network represents the **frontier** of `X` (`HTN.Syn.AcVer.Front`): its tasks are the
identifiers `HTN.Syn.AcVer.idOf` of the frontier nodes, ordered by the inherited order of their
paths and labelled by the labels of their last steps (`HTN.Syn.AcVer.Rep`).  Expanding a node of
maximal length is one decomposition step.  When every compound node is expanded the frontier is
the set of action leaves, and the order of the witness is an executable linearisation.
-/

namespace HTN

namespace Syn

namespace AcVer

open Classical

variable {d : DomDesc} {q : InstDesc} {W : List Entry}

/-! ### Identifiers of nodes -/

/-- A bound above all identifiers of the initial task network. -/
def idBase (q : InstDesc) : ℕ := q.tnI.ids.sum + 1

/-- **The identifier of a node**: a root keeps its identifier from the initial task network, every
other node gets a fresh identifier above `idBase q` from an injective coding of its path. -/
def idOf (q : InstDesc) (p : List PStep) : ℕ :=
  if p.length = 1 then (p.headD (0, 0)).2 else idBase q + Encodable.encode p

theorem idOf_root (i : ℕ) : idOf q [((0 : ℕ), i)] = i := by simp [idOf]

theorem idOf_of_two_le {p : List PStep} (h : 2 ≤ p.length) :
    idOf q p = idBase q + Encodable.encode p := by
  simp [idOf, show p.length ≠ 1 by omega]

theorem PathOK.idOf_inj (hW : PathOK d q W) {a b : List PStep} (ha : IsNode W a)
    (hb : IsNode W b) (h : idOf q a = idOf q b) : a = b := by
  have hlen : ∀ {p : List PStep}, IsNode W p → p.length = 1 ∨ 2 ≤ p.length := by
    intro p hp
    have : p.length ≠ 0 := by simpa using hp.1
    omega
  have hroot : ∀ {p : List PStep}, IsNode W p → p.length = 1 → idOf q p < idBase q := by
    intro p hp h1
    obtain ⟨i, hi, rfl⟩ := hW.root_of_node hp h1
    rw [idOf_root, idBase]
    have := List.le_sum_of_mem hi
    omega
  rcases hlen ha with ha1 | ha2 <;> rcases hlen hb with hb1 | hb2
  · obtain ⟨i, -, rfl⟩ := hW.root_of_node ha ha1
    obtain ⟨i', -, rfl⟩ := hW.root_of_node hb hb1
    rw [idOf_root, idOf_root] at h
    rw [h]
  · have := hroot ha ha1
    rw [h, idOf_of_two_le hb2] at this
    omega
  · have := hroot hb hb1
    rw [← h, idOf_of_two_le ha2] at this
    omega
  · rw [idOf_of_two_le ha2, idOf_of_two_le hb2] at h
    exact Encodable.encode_injective (by omega)

/-! ### The copy of a method's subtask network -/

/-- The subtask network `t` with its identifiers renamed by `g`. -/
noncomputable def copyNet (g : ℕ → ℕ) (t : TnDesc) : TaskNetwork ℕ ℕ ℕ where
  T := t.ids.toFinset.image g
  ord := fun a b => ∃ j j', a = g j ∧ b = g j' ∧ t.ordOf j j'
  α := fun a => t.label (Function.invFun g a)

section Copy

variable {g : ℕ → ℕ} (hg : Function.Injective g) (t : TnDesc)
include hg

theorem copyNet_ord_iff (j j' : ℕ) : (copyNet g t).ord (g j) (g j') ↔ t.ordOf j j' := by
  constructor
  · rintro ⟨i, i', h1, h2, h⟩
    rw [hg h1, hg h2]; exact h
  · exact fun h => ⟨j, j', rfl, rfl, h⟩

theorem copyNet_α (j : ℕ) : (copyNet g t).α (g j) = t.label j := by
  simp only [copyNet, Function.leftInverse_invFun hg j]

theorem copyNet_wf : (copyNet g t).WF where
  mem_left := by
    rintro _ _ ⟨j, j', rfl, rfl, h⟩
    exact Finset.mem_image_of_mem g (List.mem_toFinset.2 h.1)
  mem_right := by
    rintro _ _ ⟨j, j', rfl, rfl, h⟩
    exact Finset.mem_image_of_mem g (List.mem_toFinset.2 h.2.1)
  irrefl := by
    rintro _ ⟨j, j', h1, h2, h⟩
    rw [h1] at h2
    rw [hg h2] at h
    exact (TnDesc.toTaskNetwork_wf t).irrefl _ h
  trans := by
    rintro _ _ _ ⟨j, j', rfl, h2, h⟩ ⟨i, i', h3, rfl, h'⟩
    rw [h2] at h3
    rw [hg h3] at h
    exact ⟨j, i', rfl, rfl, (TnDesc.toTaskNetwork_wf t).trans h h'⟩

theorem copyNet_iso : (copyNet g t).Iso t.toTaskNetwork := by
  refine ⟨Function.invFun g, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro _ ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
    rw [Function.leftInverse_invFun hg j]
    exact Finset.mem_coe.2 hj
  · rintro _ ha _ hb h
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    rw [Function.leftInverse_invFun hg j, Function.leftInverse_invFun hg j'] at h
    rw [h]
  · intro j hj
    exact ⟨g j, Finset.mem_coe.2 (Finset.mem_image_of_mem g (Finset.mem_coe.1 hj)),
      Function.leftInverse_invFun hg j⟩
  · intro a ha b hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hb
    rw [copyNet_ord_iff hg, Function.leftInverse_invFun hg j, Function.leftInverse_invFun hg j']
    rfl
  · intro a ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    rw [copyNet_α hg, Function.leftInverse_invFun hg j]
    rfl

end Copy

/-! ### Closed sets of expanded nodes and their frontier -/

/-- **A set of expanded nodes**: compound nodes, closed under taking nonempty prefixes. -/
structure Closed (d : DomDesc) (q : InstDesc) (W : List Entry) (X : Finset (List PStep)) :
    Prop where
  compound : ∀ N ∈ X, IsNode W N ∧ ∃ c, lastLabel d q N = Sum.inr c
  pre : ∀ N ∈ X, ∀ M, M ≠ [] → M <+: N → M ≠ N → M ∈ X

/-- **The frontier** of a set of expanded nodes: the nodes that are not expanded but whose parent
is (or which are roots). -/
def Front (W : List Entry) (X : Finset (List PStep)) (N : List PStep) : Prop :=
  IsNode W N ∧ N ∉ X ∧ (N.length = 1 ∨ N.dropLast ∈ X)

/-- All prefixes of the paths of the entries. -/
def nodeSet (W : List Entry) : Finset (List PStep) := (W.flatMap fun u => u.1.inits).toFinset

theorem mem_nodeSet {N : List PStep} (h : IsNode W N) : N ∈ nodeSet W := by
  obtain ⟨-, u, hu, hpre, -⟩ := h
  simp only [nodeSet, List.mem_toFinset, List.mem_flatMap, List.mem_inits]
  exact ⟨u, hu, hpre⟩

/-- The frontier, as a finite set. -/
noncomputable def frontFin (W : List Entry) (X : Finset (List PStep)) : Finset (List PStep) :=
  (nodeSet W).filter (Front W X)

theorem mem_frontFin {X : Finset (List PStep)} {N : List PStep} :
    N ∈ frontFin W X ↔ Front W X N := by
  simp only [frontFin, Finset.mem_filter, and_iff_right_iff_imp]
  exact fun h => mem_nodeSet h.1

theorem prefix_dropLast_of_ne {a b : List PStep} (h : a <+: b) (hne : a ≠ b) :
    a <+: b.dropLast := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ [] := by rintro rfl; simp at hne
  rw [List.dropLast_append_of_ne_nil hr]
  exact List.prefix_append _ _

/-- Distinct frontier nodes diverge. -/
theorem Closed.front_div {X : Finset (List PStep)} (hX : Closed d q W X) {a b : List PStep}
    (ha : Front W X a) (hb : Front W X b) (hne : a ≠ b) : ∃ x y, DivAt a b x y := by
  have key : ∀ {a b : List PStep}, Front W X a → Front W X b → a ≠ b → ¬ a <+: b := by
    intro a b ha hb hne hpre
    have hlt : a.length < b.length := by
      rcases Nat.lt_or_eq_of_le hpre.length_le with h | h
      · exact h
      · exact absurd (hpre.eq_of_length h) hne
    have ha0 : a ≠ [] := ha.1.1
    have ha1 : 1 ≤ a.length := by
      rcases a with _ | ⟨z, a⟩
      · exact absurd rfl ha0
      · simp
    rcases hb.2.2 with hb1 | hb2
    · omega
    · have hpre' := prefix_dropLast_of_ne hpre hne
      by_cases heq : a = b.dropLast
      · exact ha.2.1 (heq ▸ hb2)
      · exact ha.2.1 (hX.pre _ hb2 a ha0 hpre' heq)
  exact exists_divAt (key ha hb hne) (key hb ha (Ne.symm hne))

/-! ### The represented networks -/

/-- **The network `tn` represents the frontier of `X`.** -/
structure Rep (d : DomDesc) (q : InstDesc) (W : List Entry) (X : Finset (List PStep))
    (tn : TaskNetwork ℕ ℕ ℕ) : Prop where
  T : tn.T = (frontFin W X).image (idOf q)
  ord : ∀ a b, Front W X a → Front W X b → (tn.ord (idOf q a) (idOf q b) ↔ DivOrd d q a b)
  lbl : ∀ a, Front W X a → tn.α (idOf q a) = lastLabel d q a

theorem front_empty_iff (hW : PathOK d q W) {N : List PStep} :
    Front W ∅ N ↔ ∃ i ∈ q.tnI.ids, N = [(0, i)] := by
  constructor
  · rintro ⟨hN, -, h1 | h2⟩
    · exact hW.root_of_node hN h1
    · simp at h2
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hW.root_node hi, by simp, Or.inl rfl⟩

/-- The initial task network represents the frontier of the empty set: the roots. -/
theorem rep_empty (hW : PathOK d q W) : Rep d q W ∅ q.tnI.toTaskNetwork where
  T := by
    ext i
    simp only [TnDesc.toTaskNetwork, List.mem_toFinset, Finset.mem_image, mem_frontFin,
      front_empty_iff hW]
    constructor
    · intro hi
      exact ⟨[(0, i)], ⟨i, hi, rfl⟩, idOf_root i⟩
    · rintro ⟨_, ⟨i', hi', rfl⟩, h⟩
      rw [idOf_root] at h
      exact h ▸ hi'
  ord := by
    intro a b ha hb
    obtain ⟨i, -, rfl⟩ := (front_empty_iff hW).1 ha
    obtain ⟨i', -, rfl⟩ := (front_empty_iff hW).1 hb
    rw [idOf_root, idOf_root, TnDesc.toTaskNetwork_ord]
    constructor
    · intro h
      have hne : i ≠ i' := by
        rintro rfl
        exact h.2.2.2 h.2.2.1
      exact ⟨(0, i), (0, i'), divAt_single.2 ⟨rfl, rfl, hne⟩, rfl, by
        simpa [netOf_zero, TnDesc.ordOf] using h⟩
    · rintro ⟨x, y, hd, -, ho⟩
      obtain ⟨rfl, rfl, -⟩ := divAt_single.1 hd
      simpa [netOf_zero, TnDesc.ordOf] using ho
  lbl := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := (front_empty_iff hW).1 ha
    rw [idOf_root]
    simp [lastLabel, stepLabel, netOf_zero]

/-! ### One expansion step -/

theorem closed_erase {X : Finset (List PStep)} (hX : Closed d q W X) {N : List PStep}
    (hN : N ∈ X) (hmax : ∀ M ∈ X, M.length ≤ N.length) : Closed d q W (X.erase N) where
  compound := fun M hM => hX.compound M (Finset.mem_of_mem_erase hM)
  pre := by
    intro M hM M' hM' hpre hne
    have hMX := Finset.mem_of_mem_erase hM
    refine Finset.mem_erase.2 ⟨?_, hX.pre M hMX M' hM' hpre hne⟩
    rintro rfl
    have hlt : M'.length < M.length := by
      rcases Nat.lt_or_eq_of_le hpre.length_le with h | h
      · exact h
      · exact absurd (hpre.eq_of_length h) hne
    have := hmax M hMX
    omega

theorem exists_getLast? {N : List PStep} (h : N ≠ []) : ∃ x, N.getLast? = some x :=
  Option.ne_none_iff_exists'.1 (by simpa using h)

/-- **Expanding a node of maximal length is a decomposition step.** -/
theorem rep_step (hW : PathOK d q W) {X : Finset (List PStep)} (hX : Closed d q W X)
    {N : List PStep} (hN : N ∈ X) (hmax : ∀ M ∈ X, M.length ≤ N.length)
    {tn : TaskNetwork ℕ ℕ ℕ} (hwf : tn.WF) (hR : Rep d q W (X.erase N) tn) :
    ∃ tn₂, DecompStep' (problem d q).methods tn tn₂ ∧ Rep d q W X tn₂ := by
  obtain ⟨hNnode, c, hc⟩ := hX.compound N hN
  have hNne : N ≠ [] := hNnode.1
  obtain ⟨u, hu, y, s, hus⟩ := hW.compound_ext hNnode hc
  obtain ⟨x, hx⟩ := exists_getLast? hNne
  obtain ⟨hk1, hklen, hlab⟩ := link_of_append (hW.entries u hu).isChain hus x hx
  set e := methodAt d y.1 with he_def
  have he : e ∈ d.methods := by
    obtain ⟨i, hi⟩ : ∃ i, y.1 = i + 1 := ⟨y.1 - 1, by omega⟩
    have hilt : i < d.methods.length := by rw [hi] at hklen; simpa using hklen
    rw [he_def, hi, methodAt_succ hilt]
    exact List.getElem_mem _
  have hcN : lastLabel d q N = Sum.inr e.1 := by
    rw [lastLabel_eq_of_getLast? hx]; exact hlab
  have hnk : netOf d q y.1 = e.2 := by rw [netOf, if_neg (by omega)]
  have hNlen : 1 ≤ N.length := by
    rcases N with _ | ⟨z, N⟩
    · exact absurd rfl hNne
    · simp
  -- the identifiers of the children
  let g : ℕ → ℕ := fun j => idOf q (N ++ [(y.1, j)])
  have hg_eq : ∀ j, g j = idBase q + Encodable.encode (N ++ [(y.1, j)]) := fun j =>
    idOf_of_two_le (by simp; omega)
  have hg : Function.Injective g := by
    intro j j' h
    rw [hg_eq, hg_eq] at h
    have := Encodable.encode_injective (by omega : Encodable.encode (N ++ [(y.1, j)]) =
      Encodable.encode (N ++ [(y.1, j')]))
    simpa using this
  set X' := X.erase N with hX'_def
  have hX' : Closed d q W X' := closed_erase hX hN hmax
  have hNX' : N ∉ X' := by simp [hX'_def]
  have hNfront : Front W X' N := by
    refine ⟨hNnode, hNX', ?_⟩
    rcases Nat.lt_or_eq_of_le hNlen with h | h
    · right
      have hpre : N.dropLast <+: N := List.dropLast_prefix N
      have hne : N.dropLast ≠ N := by
        intro h'
        have := congrArg List.length h'
        simp at this
        omega
      have hne' : N.dropLast ≠ [] := by
        intro h'
        have := congrArg List.length h'
        simp at this
        omega
      exact Finset.mem_erase.2 ⟨hne, hX.pre N hN _ hne' hpre hne⟩
    · exact Or.inl h.symm
  have hchild_node : ∀ j ∈ e.2.ids, IsNode W (N ++ [(y.1, j)]) := fun j hj =>
    hW.child_node hNne hu hus (by rw [hnk]; exact hj)
  -- the frontier after the expansion
  have hfront : ∀ M, Front W X M ↔ (Front W X' M ∧ M ≠ N) ∨ ∃ j ∈ e.2.ids, M = N ++ [(y.1, j)] := by
    intro M
    constructor
    · rintro ⟨hM, hMX, h1 | h2⟩
      · exact Or.inl ⟨⟨hM, fun h => hMX (Finset.mem_of_mem_erase h), Or.inl h1⟩,
          fun h => hMX (h ▸ hN)⟩
      · by_cases hdl : M.dropLast = N
        · right
          have hMne : M ≠ [] := hM.1
          have hMeq : M = N ++ [M.getLast hMne] := by
            rw [← hdl]; exact (List.dropLast_append_getLast hMne).symm
          set z := M.getLast hMne
          rw [hMeq] at hM
          obtain ⟨⟨v, hv, s', hvs⟩, -, hz, -⟩ := hW.child hM hNne
          have hz1 : z.1 = y.1 := (hW.methOf_eq hv hvs).symm.trans (hW.methOf_eq hu hus)
          refine ⟨z.2, ?_, ?_⟩
          · have : z.2 ∈ (netOf d q z.1).ids := hz
            rwa [hz1, hnk] at this
          · rw [hMeq, ← hz1]
        · exact Or.inl ⟨⟨hM, fun h => hMX (Finset.mem_of_mem_erase h),
            Or.inr (Finset.mem_erase.2 ⟨hdl, h2⟩)⟩, fun h => hMX (h ▸ hN)⟩
    · rintro (⟨⟨hM, hMX', hpar⟩, hne⟩ | ⟨j, hj, rfl⟩)
      · refine ⟨hM, fun h => hMX' (Finset.mem_erase.2 ⟨hne, h⟩), ?_⟩
        rcases hpar with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_of_mem_erase h)
      · refine ⟨hchild_node j hj, fun h => ?_, Or.inr (by simpa using hN)⟩
        have := hmax _ h
        simp at this
  -- membership in the two networks
  have hT : ∀ a, Front W X' a → idOf q a ∈ tn.T := fun a ha => by
    rw [hR.T]; exact Finset.mem_image_of_mem _ (mem_frontFin.2 ha)
  have hT' : ∀ j ∈ e.2.ids, g j ∈ (copyNet g e.2).T := fun j hj =>
    Finset.mem_image_of_mem g (List.mem_toFinset.2 hj)
  have hnotT' : ∀ a, Front W X' a → idOf q a ∉ (copyNet g e.2).T := by
    intro a ha h
    obtain ⟨j, hj, hja⟩ := Finset.mem_image.1 h
    have hj' := List.mem_toFinset.1 hj
    have : a = N ++ [(y.1, j)] := hW.idOf_inj ha.1 (hchild_node j hj') hja.symm
    rcases ha.2.2 with h1 | h2
    · rw [this, List.length_append, List.length_singleton] at h1; omega
    · rw [this] at h2; simp at h2; exact hNX' h2
  have hnotT : ∀ j ∈ e.2.ids, g j ∉ tn.T := by
    intro j hj h
    rw [hR.T] at h
    obtain ⟨a, ha, hja⟩ := Finset.mem_image.1 h
    exact hnotT' a (mem_frontFin.1 ha) (hja ▸ hT' j hj)
  have hdisj : Disjoint tn.T (copyNet g e.2).T := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [hR.T] at hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
    exact hnotT' a (mem_frontFin.1 ha) hv'
  have hmemT' : ∀ v, v ∈ (copyNet g e.2).T → ∃ j ∈ e.2.ids, v = g j := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨j, List.mem_toFinset.1 hj, rfl⟩
  have hwf' := copyNet_wf hg e.2
  have hL := @TaskNetwork.WF.mem_left _ _ _ _ hwf
  have hR' := @TaskNetwork.WF.mem_right _ _ _ _ hwf
  have hL' := @TaskNetwork.WF.mem_left _ _ _ _ hwf'
  have hRR' := @TaskNetwork.WF.mem_right _ _ _ _ hwf'
  have hidN : ∀ a, Front W X' a → a ≠ N → idOf q a ≠ idOf q N := fun a ha hne h =>
    hne (hW.idOf_inj ha.1 hNnode h)
  refine ⟨decomposeWith tn (idOf q N) (copyNet g e.2), ⟨idOf q N, e.toMethod, ?_⟩, ?_⟩
  · refine ⟨⟨e, he, rfl⟩, hT N hNfront, ?_, copyNet g e.2, hwf', copyNet_iso hg _, hdisj, rfl⟩
    rw [hR.lbl N hNfront, hcN]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- T
    ext v
    simp only [decomposeWith, Finset.mem_union, Finset.mem_erase, Finset.mem_image,
      mem_frontFin]
    constructor
    · rintro (⟨hvN, hv⟩ | hv)
      · rw [hR.T] at hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
        have ha' := mem_frontFin.1 ha
        exact ⟨a, (hfront a).2 (Or.inl ⟨ha', fun h => hvN (h ▸ rfl)⟩), rfl⟩
      · obtain ⟨j, hj, rfl⟩ := hmemT' v hv
        exact ⟨_, (hfront _).2 (Or.inr ⟨j, hj, rfl⟩), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rcases (hfront a).1 ha with ⟨ha', hne⟩ | ⟨j, hj, rfl⟩
      · exact Or.inl ⟨hidN a ha' hne, hT a ha'⟩
      · exact Or.inr (hT' j hj)
  · -- ord
    intro a b ha hb
    simp only [decomposeWith]
    rcases (hfront a).1 ha with ⟨ha', hane⟩ | ⟨j, hj, rfl⟩ <;>
      rcases (hfront b).1 hb with ⟨hb', hbne⟩ | ⟨j', hj', rfl⟩
    · -- old, old
      have e1 : ((copyNet g e.2).ord (idOf q a) (idOf q b) ∨
          tn.ord (idOf q a) (idOf q N) ∧ idOf q b ∈ (copyNet g e.2).T ∨
          tn.ord (idOf q N) (idOf q b) ∧ idOf q a ∈ (copyNet g e.2).T ∨
          tn.ord (idOf q a) (idOf q b) ∧ idOf q a ≠ idOf q N ∧ idOf q b ≠ idOf q N) ↔
          tn.ord (idOf q a) (idOf q b) := by
        constructor
        · rintro (h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd (hL' h) (hnotT' a ha')
          · exact absurd h (hnotT' b hb')
          · exact absurd h (hnotT' a ha')
          · exact h
        · exact fun h => Or.inr (Or.inr (Or.inr ⟨h, hidN a ha' hane, hidN b hb' hbne⟩))
      rw [e1]
      exact hR.ord a b ha' hb'
    · -- old, new
      have e1 : ((copyNet g e.2).ord (idOf q a) (g j') ∨
          tn.ord (idOf q a) (idOf q N) ∧ g j' ∈ (copyNet g e.2).T ∨
          tn.ord (idOf q N) (g j') ∧ idOf q a ∈ (copyNet g e.2).T ∨
          tn.ord (idOf q a) (g j') ∧ idOf q a ≠ idOf q N ∧ g j' ≠ idOf q N) ↔
          tn.ord (idOf q a) (idOf q N) := by
        constructor
        · rintro (h | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd (hL' h) (hnotT' a ha')
          · exact h
          · exact absurd h (hnotT' a ha')
          · exact absurd (hR' h) (hnotT j' hj')
        · exact fun h => Or.inr (Or.inl ⟨h, hT' j' hj'⟩)
      change _ ↔ DivOrd d q a (N ++ [(y.1, j')])
      rw [e1, hR.ord a N ha' hNfront]
      obtain ⟨x', y', hd⟩ := hX'.front_div ha' hNfront hane
      have := divOrd_append_iff (d := d) (q := q) hd [] [(y.1, j')]
      simp only [List.append_nil] at this
      exact this.symm
    · -- new, old
      have e1 : ((copyNet g e.2).ord (g j) (idOf q b) ∨
          tn.ord (g j) (idOf q N) ∧ idOf q b ∈ (copyNet g e.2).T ∨
          tn.ord (idOf q N) (idOf q b) ∧ g j ∈ (copyNet g e.2).T ∨
          tn.ord (g j) (idOf q b) ∧ g j ≠ idOf q N ∧ idOf q b ≠ idOf q N) ↔
          tn.ord (idOf q N) (idOf q b) := by
        constructor
        · rintro (h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
          · exact absurd (hRR' h) (hnotT' b hb')
          · exact absurd h (hnotT' b hb')
          · exact h
          · exact absurd (hL h) (hnotT j hj)
        · exact fun h => Or.inr (Or.inr (Or.inl ⟨h, hT' j hj⟩))
      change _ ↔ DivOrd d q (N ++ [(y.1, j)]) b
      rw [e1, hR.ord N b hNfront hb']
      obtain ⟨x', y', hd⟩ := hX'.front_div hNfront hb' (Ne.symm hbne)
      have := divOrd_append_iff (d := d) (q := q) hd [(y.1, j)] []
      simp only [List.append_nil] at this
      exact this.symm
    · -- new, new
      have e1 : ((copyNet g e.2).ord (g j) (g j') ∨
          tn.ord (g j) (idOf q N) ∧ g j' ∈ (copyNet g e.2).T ∨
          tn.ord (idOf q N) (g j') ∧ g j ∈ (copyNet g e.2).T ∨
          tn.ord (g j) (g j') ∧ g j ≠ idOf q N ∧ g j' ≠ idOf q N) ↔
          (copyNet g e.2).ord (g j) (g j') := by
        constructor
        · rintro (h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
          · exact h
          · exact absurd (hL h) (hnotT j hj)
          · exact absurd (hR' h) (hnotT j' hj')
          · exact absurd (hL h) (hnotT j hj)
        · exact Or.inl
      change _ ↔ DivOrd d q (N ++ [(y.1, j)]) (N ++ [(y.1, j')])
      rw [e1, copyNet_ord_iff hg]
      by_cases hjj : j = j'
      · subst hjj
        constructor
        · intro h
          exact absurd h ((TnDesc.toTaskNetwork_wf _).irrefl _)
        · rintro ⟨x', y', hd, -, -⟩
          exact absurd (List.prefix_refl _) (not_prefix_of_divAt hd)
      · have hd : DivAt (N ++ [(y.1, j)]) (N ++ [(y.1, j')]) (y.1, j) (y.1, j') :=
          divAt_snoc N (by simpa using hjj) [] []
        constructor
        · intro h
          exact ⟨_, _, hd, rfl, by rw [hnk]; exact h⟩
        · rintro ⟨x', y', hd', -, ho⟩
          obtain ⟨rfl, rfl⟩ := divAt_unique hd hd'
          rw [hnk] at ho
          exact ho
  · -- lbl
    intro a ha
    simp only [decomposeWith]
    rcases (hfront a).1 ha with ⟨ha', -⟩ | ⟨j, hj, rfl⟩
    · rw [if_neg (hnotT' a ha')]
      exact hR.lbl a ha'
    · change (if g j ∈ (copyNet g e.2).T then _ else _) = _
      rw [if_pos (hT' j hj), copyNet_α hg, lastLabel_snoc, stepLabel, hnk]

/-! ### Expanding every compound node -/

/-- **Every closed set of compound nodes can be expanded by a decomposition sequence.** -/
theorem exists_rep (hW : PathOK d q W) : ∀ (n : ℕ) (X : Finset (List PStep)), X.card = n →
    Closed d q W X → ∃ tn, (problem d q).DecomposesTo (problem d q).tnI tn ∧ Rep d q W X tn := by
  intro n
  induction n with
  | zero =>
    intro X hX _
    rw [Finset.card_eq_zero] at hX
    subst hX
    exact ⟨_, Relation.ReflTransGen.refl, rep_empty hW⟩
  | succ n ih =>
    intro X hcard hX
    have hne : X.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨N, hN, hmax⟩ := Finset.exists_max_image X List.length hne
    obtain ⟨tn, hreach, hR⟩ :=
      ih (X.erase N) (by rw [Finset.card_erase_of_mem hN]; omega) (closed_erase hX hN hmax)
    have hwf : tn.WF := DecomposesTo.wf hreach (TnDesc.toTaskNetwork_wf _)
    obtain ⟨tn₂, hstep, hR₂⟩ := rep_step hW hX hN hmax hwf hR
    exact ⟨tn₂, Relation.ReflTransGen.tail hreach hstep, hR₂⟩

theorem exists_snoc_prefix {M N : List PStep} (hpre : M <+: N) (hne : M ≠ N) :
    ∃ z, M ++ [z] <+: N := by
  obtain ⟨r, rfl⟩ := hpre
  rcases r with _ | ⟨z, r⟩
  · simp at hne
  · exact ⟨z, r, by simp⟩

/-- The set of all compound nodes. -/
noncomputable def compNodes (d : DomDesc) (q : InstDesc) (W : List Entry) :
    Finset (List PStep) :=
  (nodeSet W).filter fun N => IsNode W N ∧ ∃ c, lastLabel d q N = Sum.inr c

theorem closed_compNodes (hW : PathOK d q W) : Closed d q W (compNodes d q W) where
  compound := fun N hN => (Finset.mem_filter.1 hN).2
  pre := by
    intro N hN M hM hpre hne
    have hNn := (Finset.mem_filter.1 hN).2.1
    obtain ⟨z, hz⟩ := exists_snoc_prefix hpre hne
    have hMz := hNn.of_prefix (by simp) hz
    have hMn := hNn.of_prefix hM hpre
    exact Finset.mem_filter.2 ⟨mem_nodeSet hMn, hMn, hW.parent_compound hMz hM⟩

/-- The frontier of the set of all compound nodes: the primitive nodes. -/
theorem front_compNodes_iff (hW : PathOK d q W) {N : List PStep} :
    Front W (compNodes d q W) N ↔ IsNode W N ∧ ∃ a, lastLabel d q N = Sum.inl a := by
  constructor
  · rintro ⟨hN, hNX, -⟩
    refine ⟨hN, ?_⟩
    rcases h : lastLabel d q N with a | c
    · exact ⟨a, rfl⟩
    · exact absurd (Finset.mem_filter.2 ⟨mem_nodeSet hN, hN, c, h⟩) hNX
  · rintro ⟨hN, a, ha⟩
    refine ⟨hN, fun h => ?_, ?_⟩
    · obtain ⟨-, -, c, hc⟩ := Finset.mem_filter.1 h
      rw [ha] at hc
      cases hc
    · have hlen : N.length ≠ 0 := by simpa using hN.1
      rcases Nat.lt_or_ge N.length 2 with h | h
      · left; omega
      · right
        have hNe : N ≠ [] := hN.1
        have hdl : N.dropLast ≠ [] := by
          intro h'
          have := congrArg List.length h'
          simp at this
          omega
        have hNeq : N.dropLast ++ [N.getLast hNe] = N := List.dropLast_append_getLast hNe
        have hc : IsNode W (N.dropLast ++ [N.getLast hNe]) := by rw [hNeq]; exact hN
        obtain ⟨-, -, -, hpar⟩ := hW.child hc hdl
        exact Finset.mem_filter.2 ⟨mem_nodeSet hpar, hpar, hW.parent_compound hc hdl⟩

/-- **Soundness: a described problem with a path witness is solvable.** -/
theorem solvable_of_pathOK (hW : PathOK d q W) : Solvable d q := by
  obtain ⟨tn, hreach, hR⟩ := exists_rep hW _ (compNodes d q W) rfl (closed_compNodes hW)
  set A := W.filter fun u => !u.2 with hA
  have hAW : ∀ u ∈ A, u ∈ W ∧ u.2 = false := by
    intro u hu
    simpa [hA] using hu
  have hfrontA : ∀ u ∈ A, Front W (compNodes d q W) u.1 := by
    intro u hu
    obtain ⟨huW, h2⟩ := hAW u hu
    have he := hW.entries u huW
    simp only [EntryOK, h2, Bool.false_eq_true, if_false] at he
    exact (front_compNodes_iff hW).2 ⟨hW.isNode_leaf huW h2, he.2⟩
  have hTA : ∀ t, t ∈ tn.T ↔ ∃ u ∈ A, idOf q u.1 = t := by
    intro t
    rw [hR.T, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨hn, b, hb⟩ := (front_compNodes_iff hW).1 (mem_frontFin.1 ha)
      obtain ⟨u, hu, rfl, h2⟩ := hW.prim_entry hn hb
      exact ⟨u, by simp [hA, hu, h2], rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.1, mem_frontFin.2 (hfrontA u hu), rfl⟩
  have hlblA : ∀ u ∈ A, tn.α (idOf q u.1) = Sum.inl (leafAct d q u.1) := by
    intro u hu
    rw [hR.lbl _ (hfrontA u hu)]
    obtain ⟨-, a, ha⟩ := (front_compNodes_iff hW).1 (hfrontA u hu)
    rw [leafAct_eq, ha]
    rfl
  have hpwA : A.Pairwise (PairOK d q) := hW.pairs.sublist List.filter_sublist
  refine ⟨tn, hreach, ?_, A.map (fun u => idOf q u.1), actsOf d q W, ⟨?_, ?_, ?_⟩, ?_,
    hW.exec.1, hW.exec.2⟩
  · -- primitive
    intro t ht
    obtain ⟨u, hu, rfl⟩ := (hTA t).1 ht
    exact ⟨_, hlblA u hu⟩
  · -- nodup
    rw [List.Nodup, List.pairwise_map]
    refine hpwA.imp_of_mem ?_
    intro u v hu hv h hid
    exact h.path_ne (hW.idOf_inj (hfrontA u hu).1 (hfrontA v hv).1 hid)
  · -- membership
    intro t
    rw [hTA, List.mem_map]
  · -- order
    rw [List.pairwise_map]
    refine hpwA.imp_of_mem ?_
    intro u v hu hv ⟨x, y, hd, hxy, hno⟩ hord
    rw [hR.ord _ _ (hfrontA v hv) (hfrontA u hu)] at hord
    obtain ⟨x', y', hd', hxy', ho⟩ := hord
    obtain ⟨rfl, rfl⟩ := divAt_unique (divAt_symm hd) hd'
    exact hno (hAW u hu).2 (hAW v hv).2 (by rw [hxy]; exact ho)
  · -- action sequence
    unfold TaskNetwork.IsActionSeq actsOf
    rw [← hA, List.map_map, List.map_map]
    exact List.map_congr_left fun u hu => hlblA u hu

/-- **Path witnesses characterise plan existence.** -/
theorem solvable_iff_exists_pathOK : Solvable d q ↔ ∃ W, PathOK d q W :=
  ⟨exists_pathOK_of_solvable, fun ⟨_, hW⟩ => solvable_of_pathOK hW⟩

end AcVer

end Syn

end HTN
