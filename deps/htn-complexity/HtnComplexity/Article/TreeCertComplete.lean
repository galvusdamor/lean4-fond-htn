import HtnComplexity.Article.TreeCert
/-!
# Completeness of tree certificates

`HTN.Article.exists_certB`: valid decomposition trees for the initial task network whose yields
merge into a plan give a tree certificate passing the check (`HTN.Article.certB`), with as many
nodes as the trees have, and all of whose numbers come from the problem or are node indices.

The trees are laid out in post-order, one *block* of consecutive nodes per tree
(`HTN.Article.BlockSpec`), children before their parent.
-/

namespace HTN

namespace Article

open Syn Syn.PolyInst

/-- The raw label of the root of a tree. -/
def rawLbl : DTree ℕ ℕ ℕ → Bool × ℕ
  | .leaf a => (false, a)
  | .node c _ _ => (true, c)

theorem toSum_inj {l l' : Bool × ℕ} (h : toSum l = toSum l') : l = l' := by
  obtain ⟨_ | _, n⟩ := l <;> obtain ⟨_ | _, n'⟩ := l' <;> simp_all [toSum]

theorem toSum_rawLbl {M : Set (Method ℕ ℕ ℕ)} {dt : DTree ℕ ℕ ℕ} {s : ℕ ⊕ ℕ} (h : dt.Valid M s) :
    toSum (rawLbl dt) = s := by
  cases h with
  | leaf a => rfl
  | node _ _ _ => rfl

/-- The numbers of the task networks and methods of a description. -/
def tnNums (t : TnDesc) : List ℕ := t.ids ++ t.lbl.map fun q => q.2.2

/-- The numbers a tree certificate may take from a description. -/
def numsOf (p : ProbDesc) : List ℕ := tnNums p.tnI ++ p.methods.flatMap fun m => m.1 :: tnNums m.2

/-- **A block of nodes laid out at offset `o`**: every node of the block passes the check in any
node list that agrees with the block on its positions. -/
def BlockOK (p : ProbDesc) (L : List NodeC) (o : ℕ) : Prop :=
  ∀ nodes : List NodeC, (∀ i < L.length, nodes.getI (o + i) = L.getI i) →
    ∀ i < L.length, nodeB p nodes (o + i) = true

/-- The numbers of a node come from the description or are node indices below `N`, and its
yield and witness are not longer than `Y`. -/
def NodeNums (p : ProbDesc) (N Y : ℕ) (v : NodeC) : Prop :=
  v.lbl.2 ∈ numsOf p ∧ v.mi < p.methods.length + 1 ∧
    (∀ e ∈ v.kids, e.1 ∈ numsOf p ∧ e.2 < N) ∧ v.kids.length ≤ (numsOf p).length ∧
    (∀ a ∈ v.ys, a ∈ numsOf p) ∧ (∀ e ∈ v.w, e.1 ∈ numsOf p ∧ e.2 ∈ numsOf p) ∧
    v.ys.length ≤ Y ∧ v.w.length ≤ Y

/-- **The block of a tree** at offset `o`, with yield `ys`. -/
structure BlockSpec (p : ProbDesc) (dt : DTree ℕ ℕ ℕ) (ys : List ℕ) (o : ℕ) (L : List NodeC) :
    Prop where
  len : L.length = dt.size
  root_lbl : (L.getI (L.length - 1)).lbl = rawLbl dt
  root_ys : (L.getI (L.length - 1)).ys = ys
  ok : BlockOK p L o
  nums : ∀ v ∈ L, NodeNums p (o + L.length) ys.length v

theorem dtree_size_pos (dt : DTree ℕ ℕ ℕ) : 0 < dt.size := by
  cases dt <;> simp [DTree.size]

/-- The block of a leaf. -/
theorem block_leaf (p : ProbDesc) (a : ℕ) (ha : a ∈ numsOf p) (o : ℕ) :
    BlockSpec p (.leaf a) [a] o [((false, a), 0, [], [a], [])] := by
  refine ⟨rfl, rfl, rfl, fun nodes hn i hi => ?_, fun v hv => ?_⟩
  · have hi0 : i = 0 := by simpa using hi
    subst hi0
    have := hn 0 (by simp)
    simp only [Nat.add_zero, List.getI_cons_zero] at this
    unfold nodeB
    rw [Nat.add_zero, this]
    simp [NodeC.lbl, NodeC.ys]
  · simp only [List.mem_singleton] at hv
    subst hv
    exact ⟨ha, by simp [NodeC.mi], by simp [NodeC.kids], by simp [NodeC.kids], by simp [NodeC.ys, ha],
      by simp [NodeC.w], by simp [NodeC.ys], by simp [NodeC.w]⟩

theorem NodeNums.mono {p : ProbDesc} {N N' Y Y' : ℕ} {v : NodeC} (h : NodeNums p N Y v)
    (hN : N ≤ N') (hY : Y ≤ Y') : NodeNums p N' Y' v :=
  ⟨h.1, h.2.1, fun e he => ⟨(h.2.2.1 e he).1, by have := (h.2.2.1 e he).2; omega⟩, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, by have := h.2.2.2.2.2.2.1; omega, by have := h.2.2.2.2.2.2.2; omega⟩

theorem blockOK_append {p : ProbDesc} {L₁ L₂ : List NodeC} {o : ℕ} (h₁ : BlockOK p L₁ o)
    (h₂ : BlockOK p L₂ (o + L₁.length)) : BlockOK p (L₁ ++ L₂) o := by
  intro nodes hn i hi
  rw [List.length_append] at hi
  by_cases hi1 : i < L₁.length
  · refine h₁ nodes (fun j hj => ?_) i hi1
    rw [hn j (by rw [List.length_append]; omega), List.getI_append _ _ _ hj]
  · have := h₂ nodes (fun j hj => ?_) (i - L₁.length) (by omega)
    · rwa [show o + L₁.length + (i - L₁.length) = o + i by omega] at this
    · rw [show o + L₁.length + j = o + (L₁.length + j) by omega,
        hn (L₁.length + j) (by rw [List.length_append]; omega),
        List.getI_append_right _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- **Blocks for a list of trees**, laid out one after the other. -/
theorem exists_seqBlocks (p : ProbDesc) (f : ℕ → DTree ℕ ℕ ℕ) (yf : ℕ → List ℕ) (Y : ℕ) :
    ∀ xs : List ℕ, xs.Nodup → (∀ x ∈ xs, (yf x).length ≤ Y) →
      (∀ x ∈ xs, ∀ o, ∃ L, BlockSpec p (f x) (yf x) o L) →
      ∀ o, ∃ (LL : List NodeC) (pos : ℕ → ℕ), LL.length = (xs.map fun x => (f x).size).sum ∧
        BlockOK p LL o ∧
        (∀ x ∈ xs, o ≤ pos x ∧ pos x < o + LL.length ∧ (LL.getI (pos x - o)).lbl = rawLbl (f x) ∧
          (LL.getI (pos x - o)).ys = yf x) ∧
        ∀ v ∈ LL, NodeNums p (o + LL.length) Y v := by
  intro xs
  induction xs with
  | nil =>
    intro _ _ _ o
    exact ⟨[], fun _ => 0, by simp, fun _ _ i hi => by simp at hi, by simp, by simp⟩
  | cons x xs ih =>
    intro hnd hY hb o
    rw [List.nodup_cons] at hnd
    obtain ⟨L, hL⟩ := hb x (by simp) o
    obtain ⟨LL, pos, hlen, hok, hpos, hnums⟩ := ih hnd.2 (fun y hy => hY y (by simp [hy]))
      (fun y hy => hb y (by simp [hy])) (o + L.length)
    have hLpos : 0 < L.length := by rw [hL.len]; exact dtree_size_pos _
    refine ⟨L ++ LL, fun y => if y = x then o + L.length - 1 else pos y, ?_, blockOK_append hL.ok hok,
      fun y hy => ?_, fun v hv => ?_⟩
    · simp [hlen, hL.len]
    · rcases List.mem_cons.1 hy with rfl | hy
      · simp only [if_true]
        refine ⟨by omega, by simp; omega, ?_, ?_⟩
        · rw [show o + L.length - 1 - o = L.length - 1 by omega, List.getI_append _ _ _ (by omega)]
          exact hL.root_lbl
        · rw [show o + L.length - 1 - o = L.length - 1 by omega, List.getI_append _ _ _ (by omega)]
          exact hL.root_ys
      · have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
        simp only [hne, if_false]
        obtain ⟨h1, h2, h3, h4⟩ := hpos y hy
        refine ⟨by omega, by simp; omega, ?_, ?_⟩
        · rw [List.getI_append_right _ _ _ (by omega), show pos y - o - L.length = pos y - (o + L.length)
            by omega]
          exact h3
        · rw [List.getI_append_right _ _ _ (by omega), show pos y - o - L.length = pos y - (o + L.length)
            by omega]
          exact h4
    · rcases List.mem_append.1 hv with hv | hv
      · exact (hL.nums v hv).mono (by rw [List.length_append]; omega) (hY x (by simp))
      · exact (hnums v hv).mono (by rw [List.length_append]; omega) le_rfl

theorem lookup_map_pair (f : ℕ → ℕ) {x : ℕ} : ∀ {l : List ℕ}, x ∈ l →
    (l.map fun y => (y, f y)).lookup x = some (f x)
  | [], h => by simp at h
  | y :: l, h => by
    by_cases hxy : x = y
    · subst hxy; simp
    · have := lookup_map_pair f (l := l) (by simpa [hxy] using h)
      rw [List.map_cons, List.lookup, show (x == y) = false by simpa using hxy]
      exact this

theorem kidOf_map_pair (f : ℕ → ℕ) {x : ℕ} {l : List ℕ} (h : x ∈ l) :
    kidOf (l.map fun y => (y, f y)) x = f x := by
  unfold kidOf; rw [lookup_map_pair f h]; rfl

theorem lblOf_mem {prim : ℕ → Prop} {t : TnDesc} (ht : TnValid prim t) {x : ℕ} (hx : x ∈ t.ids) :
    (lblOf t x).2 ∈ t.lbl.map fun q => q.2.2 := by
  have hx' : x ∈ t.lbl.map Prod.fst := ht.lbl_perm.symm.subset hx
  unfold lblOf
  rcases h : t.lbl.lookup x with _ | q
  · exfalso
    obtain ⟨⟨y, q⟩, hm, rfl⟩ := List.mem_map.1 hx'
    rw [List.lookup_eq_none_iff] at h
    exact absurd (h _ hm) (by simp)
  · exact List.mem_map.2 ⟨(x, q), mem_of_lookup_eq_some h, rfl⟩

theorem mem_numsOf_tnI {p : ProbDesc} {a : ℕ} (h : a ∈ tnNums p.tnI) : a ∈ numsOf p :=
  List.mem_append_left _ h

theorem mem_numsOf_method {p : ProbDesc} {e : MethodDesc} (he : e ∈ p.methods) {a : ℕ}
    (h : a ∈ e.1 :: tnNums e.2) : a ∈ numsOf p :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, h⟩)

theorem getI_concat_length (L : List NodeC) (v : NodeC) : (L ++ [v]).getI L.length = v := by
  rw [List.getI_append_right _ _ _ le_rfl, Nat.sub_self]; rfl

/-- **The block of a valid tree**, laid out in post-order. -/
theorem exists_block {p : ProbDesc} (hp : p.Valid) : ∀ (dt : DTree ℕ ℕ ℕ) (s : ℕ ⊕ ℕ)
    (ys : List ℕ), dt.Valid p.toProblem.methods s → dt.Yield ys →
    (∀ a, s = Sum.inl a → a ∈ numsOf p) → ∀ o, ∃ L, BlockSpec p dt ys o L := by
  intro dt
  induction dt with
  | leaf a =>
    intro s ys hv hy hs o
    cases hv; cases hy
    exact ⟨_, block_leaf p a (hs a rfl) o⟩
  | node c m ch ih =>
    intro s ys hv hy _ o
    cases hv with
    | node hm hc hch =>
    cases hy with
    | node yf hych hmerge =>
    obtain ⟨e, he, rfl⟩ := hm
    have hval : TnValid p.Declared e.2 := hp.methods e he
    have hT : ∀ x, x ∈ (MethodDesc.toMethod e).subtasks.T ↔ x ∈ e.2.ids := fun x => by
      simp [MethodDesc.toMethod, TnDesc.toTaskNetwork]
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ := hmerge
    have hylen : ∀ x ∈ e.2.ids, (yf x).length ≤ ys.length := by
      intro x hx
      rw [← hw3 x ((hT x).2 hx), ← hw1, List.length_map, List.length_map]
      exact List.length_filter_le _ _
    have hleafc : ∀ x ∈ e.2.ids, ∀ a, e.2.label x = Sum.inl a → a ∈ numsOf p := by
      intro x hx a ha
      rw [label_eq_toSum] at ha
      have h2 : (lblOf e.2 x).2 = a := by
        unfold toSum at ha
        split at ha
        · cases ha
        · exact Sum.inl.inj ha
      refine mem_numsOf_method he (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))
      rw [← h2]; exact lblOf_mem hval hx
    have hidsN : ∀ x ∈ e.2.ids, x ∈ numsOf p := fun x hx =>
      mem_numsOf_method he (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
    obtain ⟨LL, pos, hlen, hok, hpos, hnums⟩ := exists_seqBlocks p ch yf ys.length e.2.ids hval.nodup
      hylen (fun x hx o' => ih x _ _ (hch x ((hT x).2 hx)) (hych x ((hT x).2 hx))
        (hleafc x hx) o') o
    have hgetLL : ∀ x ∈ e.2.ids, LL.getI (pos x - o) ∈ LL := fun x hx => by
      obtain ⟨h1, h2, -, -⟩ := hpos x hx
      rw [List.getI_eq_getElem _ (by omega)]; exact List.getElem_mem _
    have hysN : ∀ x ∈ e.2.ids, ∀ a ∈ yf x, a ∈ numsOf p := fun x hx a ha => by
      rw [← (hpos x hx).2.2.2] at ha
      exact (hnums _ (hgetLL x hx)).2.2.2.2.1 a ha
    have hwN : ∀ q ∈ w, q.1 ∈ e.2.ids ∧ q.2 ∈ numsOf p := fun q hq => by
      have h1 : q.1 ∈ e.2.ids := (hT _).1 (hw2 q hq)
      refine ⟨h1, hysN q.1 h1 q.2 ?_⟩
      rw [← hw3 q.1 (hw2 q hq)]
      exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simp⟩, rfl⟩
    obtain ⟨i, hi, hie⟩ : ∃ i < p.methods.length, p.methods.getI i = e := by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      exact ⟨i, hi, List.getI_eq_getElem _ hi⟩
    let v : NodeC := ((true, c), i, e.2.ids.map fun x => (x, pos x), ys, w)
    have hlast : (LL ++ [v]).length - 1 = LL.length := by simp
    refine ⟨LL ++ [v], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, hlen, DTree.size]
      rw [show (MethodDesc.toMethod e).subtasks.T = e.2.ids.toFinset from rfl,
        List.sum_toFinset _ hval.nodup]
      omega
    · rw [hlast, getI_concat_length]; rfl
    · rw [hlast, getI_concat_length]; rfl
    · intro nodes hn j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < LL.length
      · exact hok nodes (fun k hk => by
          rw [hn k (by simp; omega), List.getI_append _ _ _ hk]) j hjl
      have hj' : j = LL.length := by omega
      subst hj'
      have hv : nodes.getI (o + LL.length) = v := by
        rw [hn _ (by simp), getI_concat_length]
      have hchn : ∀ x ∈ e.2.ids, nodes.getI (pos x) = LL.getI (pos x - o) := fun x hx => by
        obtain ⟨h1, h2, -, -⟩ := hpos x hx
        have := hn (pos x - o) (by simp; omega)
        rwa [show o + (pos x - o) = pos x by omega, List.getI_append _ _ _ (by omega)] at this
      unfold nodeB
      simp only [hv, v, NodeC.lbl, NodeC.mi, NodeC.kids, NodeC.ys, NodeC.w, ↓reduceIte,
        Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hie]
      refine ⟨⟨⟨hi, hc⟩, ?_⟩, ?_⟩
      · unfold kidsB
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.map_map]
        refine ⟨fun x hx => by simpa using hx, fun q hq => ?_⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
        obtain ⟨h1, h2, h3, -⟩ := hpos x hx
        refine ⟨by omega, ?_⟩
        rw [hchn x hx, h3]
        apply toSum_inj
        rw [toSum_rawLbl (hch x ((hT x).2 hx)), ← label_eq_toSum]
        rfl
      · unfold mergeB
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
        refine ⟨⟨⟨hw1, fun q hq => (hwN q hq).1⟩, fun x hx => ?_⟩, ?_⟩
        · rw [kidOf_map_pair _ hx, hchn x hx]
          change _ = (LL.getI (pos x - o)).ys
          rw [(hpos x hx).2.2.2, ← hw3 x ((hT x).2 hx)]
          congr 1
        · refine (pairwiseB_iff _ _).2 (hw4.imp fun {q q'} h => ?_)
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]
          exact fun h' => h ((hval.ordOf_iff).2 h')
    · intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact (hnums u hu).mono (by simp) le_rfl
      · rw [List.mem_singleton] at hu
        subst hu
        refine ⟨?_, show i < _ by omega, fun q hq => ?_, ?_, fun a ha => ?_,
          fun q hq => ⟨hidsN _ (hwN q hq).1, (hwN q hq).2⟩, le_rfl, ?_⟩
        · show c ∈ numsOf p
          rw [← hc]; exact mem_numsOf_method he (List.mem_cons_self ..)
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
          obtain ⟨h1, h2, -, -⟩ := hpos x hx
          exact ⟨hidsN x hx, by simp; omega⟩
        · show (e.2.ids.map _).length ≤ _
          rw [List.length_map]
          exact (hval.nodup.subperm fun x hx => hidsN x hx).length_le
        · show a ∈ numsOf p
          change a ∈ ys at ha
          rw [← hw1] at ha
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
          exact (hwN q hq).2
        · show w.length ≤ ys.length
          rw [← hw1, List.length_map]

/-- **Completeness of tree certificates**: valid trees for `tn_I` whose yields merge into `π` give
a certificate for `π` passing the check, with one node per tree node, whose numbers come from the
description or are node indices. -/
theorem exists_certB {p : ProbDesc} (hp : p.Valid) {trees : ℕ → DTree ℕ ℕ ℕ} {π : List ℕ}
    (h : TreesYield p.toProblem.methods p.toProblem.tnI trees π) :
    ∃ c : TCert, certB p c = true ∧ c.2.2.1 = π ∧
      c.1.length = (p.tnI.ids.map fun x => (trees x).size).sum ∧
      (∀ v ∈ c.1, NodeNums p c.1.length π.length v) ∧
      (∀ q ∈ c.2.1, q.1 ∈ numsOf p ∧ q.2 < c.1.length) ∧ c.2.1.length ≤ (numsOf p).length ∧
      (∀ q ∈ c.2.2.2, q.1 ∈ numsOf p ∧ q.2 ∈ numsOf p) ∧ c.2.2.2.length = π.length ∧
      ∀ a ∈ π, a ∈ numsOf p := by
  obtain ⟨hv, yf, hy, w, hw1, hw2, hw3, hw4⟩ := h
  have hval := hp.tnI
  have hT : ∀ x, x ∈ p.toProblem.tnI.T ↔ x ∈ p.tnI.ids := fun x => by
    simp [ProbDesc.toProblem, TnDesc.toTaskNetwork]
  have hylen : ∀ x ∈ p.tnI.ids, (yf x).length ≤ π.length := by
    intro x hx
    rw [← hw3 x ((hT x).2 hx), ← hw1, List.length_map, List.length_map]
    exact List.length_filter_le _ _
  have hleafc : ∀ x ∈ p.tnI.ids, ∀ a, p.tnI.label x = Sum.inl a → a ∈ numsOf p := by
    intro x hx a ha
    rw [label_eq_toSum] at ha
    have h2 : (lblOf p.tnI x).2 = a := by
      unfold toSum at ha
      split at ha
      · cases ha
      · exact Sum.inl.inj ha
    refine mem_numsOf_tnI (List.mem_append_right _ ?_)
    rw [← h2]; exact lblOf_mem hval hx
  have hidsN : ∀ x ∈ p.tnI.ids, x ∈ numsOf p := fun x hx =>
    mem_numsOf_tnI (List.mem_append_left _ hx)
  obtain ⟨LL, pos, hlen, hok, hpos, hnums⟩ := exists_seqBlocks p trees yf π.length p.tnI.ids
    hval.nodup hylen (fun x hx o' => exists_block hp _ _ _ (hv x ((hT x).2 hx)) (hy x ((hT x).2 hx))
      (hleafc x hx) o') 0
  simp only [zero_add, Nat.sub_zero, Nat.zero_le, true_and] at hpos hnums
  have hgetLL : ∀ x ∈ p.tnI.ids, LL.getI (pos x) ∈ LL := fun x hx => by
    rw [List.getI_eq_getElem _ (hpos x hx).1]; exact List.getElem_mem _
  have hysN : ∀ x ∈ p.tnI.ids, ∀ a ∈ yf x, a ∈ numsOf p := fun x hx a ha => by
    rw [← (hpos x hx).2.2] at ha
    exact (hnums _ (hgetLL x hx)).2.2.2.2.1 a ha
  have hwN : ∀ q ∈ w, q.1 ∈ p.tnI.ids ∧ q.2 ∈ numsOf p := fun q hq => by
    have h1 : q.1 ∈ p.tnI.ids := (hT _).1 (hw2 q hq)
    refine ⟨h1, hysN q.1 h1 q.2 ?_⟩
    rw [← hw3 q.1 (hw2 q hq)]
    exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simp⟩, rfl⟩
  refine ⟨(LL, p.tnI.ids.map fun x => (x, pos x), π, w), ?_, rfl, hlen, hnums, fun q hq => ?_, ?_,
    fun q hq => ⟨hidsN _ (hwN q hq).1, (hwN q hq).2⟩, by rw [← hw1, List.length_map], fun a ha => ?_⟩
  · unfold certB
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨⟨fun j hj => ?_, ?_⟩, ?_⟩
    · have := hok LL (fun i _ => by rw [zero_add]) j hj
      rwa [zero_add] at this
    · unfold kidsB
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.map_map]
      refine ⟨fun x hx => by simpa using hx, fun q hq => ?_⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h3, -⟩ := hpos x hx
      refine ⟨h1, ?_⟩
      change (LL.getI (pos x)).lbl = _
      rw [h3]
      apply toSum_inj
      rw [toSum_rawLbl (hv x ((hT x).2 hx)), ← label_eq_toSum]
      rfl
    · unfold mergeB
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨hw1, fun q hq => (hwN q hq).1⟩, fun x hx => ?_⟩, ?_⟩
      · rw [kidOf_map_pair _ hx]
        rw [(hpos x hx).2.2, ← hw3 x ((hT x).2 hx)]
        congr 1
      · refine (pairwiseB_iff _ _).2 (hw4.imp fun {q q'} h => ?_)
        simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        exact fun h' => h ((hval.ordOf_iff).2 h')
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
    exact ⟨hidsN x hx, (hpos x hx).1⟩
  · show (p.tnI.ids.map _).length ≤ _
    rw [List.length_map]
    exact (hval.nodup.subperm fun x hx => hidsN x hx).length_le
  · rw [← hw1] at ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    exact (hwN q hq).2

end Article

end HTN
