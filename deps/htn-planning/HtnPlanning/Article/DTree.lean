import HtnPlanning.Interleave.NetYield
import HtnPlanning.Core.DecompPersist
import HtnPlanning.Article.Bridge
/-!
# Decomposition trees (Defs. 2.8–2.10)

A **decomposition tree** records which method decomposed which task: a primitive task is a leaf,
a compound task `c` decomposed by the method `m` is a node whose children are the trees of the
tasks of `m`'s network.  Here the trees are an inductive type whose children are indexed by the
task ids of the method (`HTN.Article.DTree`), so no global identifiers or isomorphisms are
needed: the isomorphism `β` of Def. 2.8 is implicit in the indexing.

The **yield** of a tree (Def. 2.10) is described by the action sequences it can be executed as:
`HTN.Article.DTree.Yield dt π` — the yields of the children, interleaved in an order compatible
with the method's ordering constraints (`HTN.Article.OrdMerge`).

The main results are

* `HTN.Article.netYield_iff_trees` (**Prop. 2.2.1** for primitive yields) — a task network can be
  decomposed into a primitive network one of whose linearisations is the action sequence `π`
  iff its tasks have valid decomposition trees whose yields merge into `π`;
* `HTN.Article.DTree.yield_sublist_of_sub` — the yield of a subtree is a subsequence of a yield
  of the tree (used for pruning cycles in TIHTN planning).
-/

namespace HTN

namespace Article

universe v w x

variable {A : Type v} {C : Type w} {I : Type x}

/-- **A decomposition tree.** -/
inductive DTree (I : Type x) (A : Type v) (C : Type w) : Type (max x v w)
  /-- A primitive task. -/
  | leaf (a : A) : DTree I A C
  /-- A compound task `c` decomposed by the method `m`; `ch t` is the tree of the task `t` of
  `m`'s network. -/
  | node (c : C) (m : Method I A C) (ch : I → DTree I A C) : DTree I A C

/-- **Ordered merge**: `π` interleaves the sequences `ys t` of the tasks `t` of `tn`, all of
`ys t` before all of `ys t'` whenever `t ≺ t'`.  The witness `w` labels each action with its
task. -/
def OrdMerge [DecidableEq I] (tn : TaskNetwork I A C) (ys : I → List A) (π : List A) : Prop :=
  ∃ w : List (I × A), w.map Prod.snd = π ∧ (∀ x ∈ w, x.1 ∈ tn.T) ∧
    (∀ t ∈ tn.T, (w.filter fun x => decide (x.1 = t)).map Prod.snd = ys t) ∧
    w.Pairwise fun x y => ¬ tn.ord y.1 x.1

namespace DTree

variable [DecidableEq I]

/-- **Validity (Def. 2.9)**: every node is decomposed by a method of `M` for its task name, and
every leaf is the primitive task it stands for. -/
inductive Valid (M : Set (Method I A C)) : DTree I A C → (A ⊕ C) → Prop
  | leaf (a : A) : Valid M (leaf a) (Sum.inl a)
  | node {c : C} {m : Method I A C} {ch : I → DTree I A C} (hm : m ∈ M)
      (hc : m.abstractTask = c) (hch : ∀ t ∈ m.subtasks.T, Valid M (ch t) (m.subtasks.α t)) :
      Valid M (node c m ch) (Sum.inr c)

/-- **The yield (Def. 2.10)**, as the action sequences the tree can be executed as. -/
inductive Yield : DTree I A C → List A → Prop
  | leaf (a : A) : Yield (leaf a) [a]
  | node {c : C} {m : Method I A C} {ch : I → DTree I A C} {π : List A} (ys : I → List A)
      (hch : ∀ t ∈ m.subtasks.T, Yield (ch t) (ys t)) (hm : OrdMerge m.subtasks ys π) :
      Yield (node c m ch) π

end DTree

/-- The trees `trees t` for the tasks `t` of `tn` are valid, and their yields merge into `π`. -/
def TreesYield [DecidableEq I] (M : Set (Method I A C)) (tn : TaskNetwork I A C)
    (trees : I → DTree I A C) (π : List A) : Prop :=
  (∀ t ∈ tn.T, (trees t).Valid M (tn.α t)) ∧
    ∃ ys : I → List A, (∀ t ∈ tn.T, (trees t).Yield (ys t)) ∧ OrdMerge tn ys π

end Article

end HTN

/-! ### From decompositions to trees -/

namespace HTN

namespace Article

universe v' w' x'

variable {A : Type v'} {C : Type w'} {I : Type x'} [DecidableEq I]

open Classical in
/-- **Collapsing a decomposition step.**  If `tn₁` arises from `tn` by decomposing `t₀` with the
method `m` (inserted as the fresh copy `tn''`, isomorphic to `m`'s network by `σ`), then trees for
the tasks of `tn₁` give trees for the tasks of `tn`, with the same merged yield. -/
theorem treesYield_of_step {M : Set (Method I A C)} {tn tn'' : TaskNetwork I A C} {t₀ : I}
    {m : Method I A C} (hwf : tn.WF) (hwf'' : tn''.WF) (hm : m ∈ M) (ht₀ : t₀ ∈ tn.T)
    (hα : tn.α t₀ = Sum.inr m.abstractTask) (hiso : tn''.Iso m.subtasks)
    (hdisj : Disjoint tn.T tn''.T) {trees₁ : I → DTree I A C} {π : List A}
    (h : TreesYield M (decomposeWith tn t₀ tn'') trees₁ π) :
    ∃ trees, TreesYield M tn trees π := by
  obtain ⟨σ, hbij, hord, hlab⟩ := hiso
  set tn₁ := decomposeWith tn t₀ tn''
  obtain ⟨hval, ys₁, hys₁, w₁, hmap, hmem, hfil, hpw⟩ := h
  have hnew : ∀ x, x ∈ tn''.T → x ∈ tn₁.T := fun x hx => mem_decomposeWith_T.2 (Or.inr hx)
  have hold : ∀ x, x ∈ tn.T → x ≠ t₀ → x ∈ tn₁.T := fun x hx hne =>
    mem_decomposeWith_T.2 (Or.inl ⟨hx, hne⟩)
  have ht₀'' : t₀ ∉ tn''.T := fun h => Finset.disjoint_left.1 hdisj ht₀ h
  have ht₀₁ : t₀ ∉ tn₁.T := by
    intro h
    rcases mem_decomposeWith_T.1 h with ⟨-, h⟩ | h
    · exact h rfl
    · exact ht₀'' h
  -- the inverse of the isomorphism
  haveI : Nonempty I := ⟨t₀⟩
  let τ : I → I := Function.invFunOn σ tn''.T
  have hτ : ∀ u ∈ m.subtasks.T, τ u ∈ tn''.T ∧ σ (τ u) = u := fun u hu =>
    ⟨Function.invFunOn_mem (hbij.surjOn hu), Function.invFunOn_eq (hbij.surjOn hu)⟩
  have hστ : ∀ x ∈ tn''.T, τ (σ x) = x := fun x hx =>
    hbij.injOn (Function.invFunOn_mem (hbij.surjOn (hbij.mapsTo hx))) hx
      (Function.invFunOn_eq (hbij.surjOn (hbij.mapsTo hx)))
  -- the tree and the yield of the decomposed task
  let f : I × A → I × A := fun x => if x.1 ∈ tn''.T then (t₀, x.2) else x
  let w₀ : List (I × A) := (w₁.filter fun x => decide (x.1 ∈ tn''.T)).map fun x => (σ x.1, x.2)
  let trees : I → DTree I A C := fun t =>
    if t = t₀ then DTree.node m.abstractTask m (fun u => trees₁ (τ u)) else trees₁ t
  let ys : I → List A := fun t =>
    if t = t₀ then w₀.map Prod.snd else ys₁ t
  refine ⟨trees, ⟨fun t ht => ?_, ys, fun t ht => ?_, w₁.map f, ?_, ?_, fun t ht => ?_, ?_⟩⟩
  · -- validity
    by_cases htt : t = t₀
    · subst htt
      simp only [trees, if_true]
      rw [hα]
      refine DTree.Valid.node hm rfl fun u hu => ?_
      obtain ⟨hτu, hστu⟩ := hτ u hu
      have := hval (τ u) (hnew _ hτu)
      rwa [decomposeWith_α, if_pos hτu, hlab _ hτu, hστu] at this
    · simp only [trees, htt, if_false]
      have := hval t (hold t ht htt)
      have hnt : t ∉ tn''.T := fun h => Finset.disjoint_left.1 hdisj ht h
      rwa [decomposeWith_α, if_neg hnt] at this
  · -- yields
    by_cases htt : t = t₀
    · subst htt
      simp only [trees, ys, if_true]
      refine DTree.Yield.node (fun u => ys₁ (τ u)) (fun u hu => hys₁ _ (hnew _ (hτ u hu).1))
        ⟨w₀, rfl, ?_, fun u hu => ?_, ?_⟩
      · intro x hx
        simp only [w₀, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
        obtain ⟨y, ⟨-, hy⟩, rfl⟩ := hx
        exact hbij.mapsTo hy
      · obtain ⟨hτu, hστu⟩ := hτ u hu
        show _ = ys₁ (τ u)
        rw [← hfil (τ u) (hnew _ hτu)]
        simp only [w₀, List.filter_map, List.map_map, List.filter_filter]
        congr 1
        refine List.filter_congr fun x _ => ?_
        rw [Bool.eq_iff_iff]
        simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨rfl, hx⟩; exact (hστ x.1 hx).symm
        · intro h; rw [h]; exact ⟨hστu, hτu⟩
      · simp only [w₀]
        rw [List.pairwise_map]
        refine (List.Pairwise.filter _ hpw).imp_of_mem fun {x y} hx hy hxy => ?_
        simp only [List.mem_filter, decide_eq_true_eq] at hx hy
        rw [← hord _ hy.2 _ hx.2]
        rwa [decomposeWith_ord_new_new hwf hdisj hy.2 hx.2] at hxy
    · simp only [trees, ys, htt, if_false]
      exact hys₁ t (hold t ht htt)
  · rw [List.map_map, ← hmap]
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, f]; split_ifs <;> rfl
  · have hw : ∀ y ∈ w₁, y.1 ∉ tn''.T → y.1 ∈ tn.T ∧ y.1 ≠ t₀ := fun y hy hn => by
      rcases mem_decomposeWith_T.1 (hmem y hy) with h | h
      · exact h
      · exact absurd h hn
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [f]
    split_ifs with h
    · exact ht₀
    · exact (hw y hy h).1
  · have hw : ∀ y ∈ w₁, y.1 ∉ tn''.T → y.1 ∈ tn.T ∧ y.1 ≠ t₀ := fun y hy hn => by
      rcases mem_decomposeWith_T.1 (hmem y hy) with h | h
      · exact h
      · exact absurd h hn
    rw [List.filter_map, List.map_map]
    by_cases htt : t = t₀
    · subst htt
      simp only [ys, if_true, w₀, List.map_map]
      have e1 : ∀ y ∈ w₁, ((fun x : I × A => decide (x.1 = t)) ∘ f) y =
          decide (y.1 ∈ tn''.T) := fun y hy => by
        simp only [Function.comp_apply, f]; split_ifs with h
        · simp [h]
        · simp [h, (hw y hy h).2]
      rw [List.filter_congr e1]
      refine List.map_congr_left fun y _ => ?_
      simp only [Function.comp_apply, f]; split_ifs <;> rfl
    · simp only [ys, htt, if_false]
      rw [← hfil t (hold t ht htt)]
      have e1 : ∀ y ∈ w₁, ((fun x : I × A => decide (x.1 = t)) ∘ f) y =
          decide (y.1 = t) := fun y hy => by
        simp only [Function.comp_apply, f]; split_ifs with h
        · have : y.1 ≠ t := fun e => Finset.disjoint_left.1 hdisj ht (e ▸ h)
          simp [this, Ne.symm htt]
        · rfl
      rw [List.filter_congr e1]
      refine List.map_congr_left fun y _ => ?_
      simp only [Function.comp_apply, f]; split_ifs <;> rfl
  · have hw : ∀ y ∈ w₁, y.1 ∉ tn''.T → y.1 ∈ tn.T ∧ y.1 ≠ t₀ := fun y hy hn => by
      rcases mem_decomposeWith_T.1 (hmem y hy) with h | h
      · exact h
      · exact absurd h hn
    rw [List.pairwise_map]
    refine hpw.imp_of_mem fun {x y} hx hy hxy => ?_
    simp only [f]
    by_cases hx'' : x.1 ∈ tn''.T <;> by_cases hy'' : y.1 ∈ tn''.T <;>
      simp only [hx'', hy'', if_true, if_false]
    · exact hwf.irrefl t₀
    · intro h
      exact hxy ((decomposeWith_ord_old_new hwf hwf'' hdisj (hw y hy hy'').1 hx'').2 h)
    · intro h
      exact hxy ((decomposeWith_ord_new_old hwf hwf'' hdisj hy'' (hw x hx hx'').1).2 h)
    · intro h
      exact hxy ((decomposeWith_ord_old_old hwf'' hdisj (hw y hy hy'').1 (hw y hy hy'').2
        (hw x hx hx'').1 (hw x hx hx'').2).2 h)

/-- A primitive network has leaf trees whose yields merge into its action sequences. -/
theorem treesYield_of_primitive [Nonempty A] {M : Set (Method I A C)} {tn : TaskNetwork I A C}
    (hp : tn.IsPrimitive) {l : List I} {π : List A} (hl : tn.IsLinearization l)
    (has : tn.IsActionSeq l π) : ∃ trees, TreesYield M tn trees π := by
  obtain ⟨hnd, hmemL, hpw⟩ := hl
  let g : A ⊕ C → A := Sum.elim id fun _ => Classical.arbitrary A
  refine ⟨fun t => DTree.leaf (g (tn.α t)), ?_, fun t => [g (tn.α t)], ?_, ?_⟩
  · intro t ht
    obtain ⟨a, ha⟩ := hp t ht
    simp only [ha, g, Sum.elim_inl, id]
    exact DTree.Valid.leaf a
  · intro t _; exact DTree.Yield.leaf _
  refine ⟨l.map fun t => (t, g (tn.α t)), ?_, ?_, ?_, ?_⟩
  · have := congrArg (List.map g) has
    simp only [List.map_map] at this
    simpa [List.map_map, Function.comp_def, g] using this
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact (hmemL t).1 ht
  · intro t ht
    rw [List.filter_map, List.map_map]
    have hf : l.filter ((fun x : I × A => decide (x.1 = t)) ∘ fun t => (t, g (tn.α t))) = [t] := by
      have e : ((fun x : I × A => decide (x.1 = t)) ∘ fun t => (t, g (tn.α t))) =
          fun x => decide (x = t) := rfl
      rw [e, List.filter_eq, List.count_eq_one_of_mem hnd ((hmemL t).2 ht)]
      rfl
    rw [hf]; rfl
  · rw [List.pairwise_map]; exact hpw

/-- **From decompositions to trees.** -/
theorem treesYield_of_decomposesTo [Nonempty A] {M : Set (Method I A C)}
    {tn tn' : TaskNetwork I A C} (hwf : tn.WF) (hdec : DecomposesTo M tn tn')
    (hp : tn'.IsPrimitive) {l : List I} {π : List A} (hl : tn'.IsLinearization l)
    (has : tn'.IsActionSeq l π) : ∃ trees, TreesYield M tn trees π := by
  induction hdec using Relation.ReflTransGen.head_induction_on with
  | refl => exact treesYield_of_primitive hp hl has
  | head hstep _ ih =>
    obtain ⟨t₀, m, hm, ht₀, hα, tn'', hwf'', hiso, hdisj, rfl⟩ := hstep
    obtain ⟨trees₁, h₁⟩ := ih (decomposeWith_wf hwf hwf'' hdisj)
    exact treesYield_of_step hwf hwf'' hm ht₀ hα hiso hdisj h₁

/-! ### From trees to decompositions -/

namespace DTree

/-- The number of nodes and leaves of a tree. -/
def size : DTree I A C → ℕ
  | leaf _ => 1
  | node _ m ch => 1 + ∑ t ∈ m.subtasks.T, (ch t).size

theorem Valid.leaf_inv {M : Set (Method I A C)} {a : A} {s : A ⊕ C}
    (h : (DTree.leaf a : DTree I A C).Valid M s) : s = Sum.inl a := by
  cases h; rfl

theorem Valid.node_inv {M : Set (Method I A C)} {c : C} {m : Method I A C} {ch : I → DTree I A C}
    {s : A ⊕ C} (h : (DTree.node c m ch).Valid M s) :
    s = Sum.inr c ∧ m ∈ M ∧ m.abstractTask = c ∧
      ∀ t ∈ m.subtasks.T, (ch t).Valid M (m.subtasks.α t) := by
  cases h with
  | node hm hc hch => exact ⟨rfl, hm, hc, hch⟩

theorem Yield.leaf_inv {a : A} {π : List A} (h : (DTree.leaf a : DTree I A C).Yield π) : π = [a] := by
  cases h; rfl

theorem Yield.node_inv {c : C} {m : Method I A C} {ch : I → DTree I A C} {π : List A}
    (h : (DTree.node c m ch).Yield π) :
    ∃ ys : I → List A, (∀ t ∈ m.subtasks.T, (ch t).Yield (ys t)) ∧ OrdMerge m.subtasks ys π := by
  cases h with
  | node ys hch hm => exact ⟨ys, hch, hm⟩

end DTree

/-- **Expanding a witness**: the entries of the task `t₀` in `w` are replaced, in order, by the
entries of `v`. -/
def expandW (t₀ : I) : List (I × A) → List (I × A) → List (I × A)
  | [], _ => []
  | x :: w, [] => if x.1 = t₀ then expandW t₀ w [] else x :: expandW t₀ w []
  | x :: w, y :: v => if x.1 = t₀ then y :: expandW t₀ w v else x :: expandW t₀ w (y :: v)

theorem mem_expandW {t₀ : I} {w v : List (I × A)} {y : I × A} (h : y ∈ expandW t₀ w v) :
    (y ∈ w ∧ y.1 ≠ t₀) ∨ (y ∈ v ∧ ∃ z ∈ w, z.1 = t₀) := by
  induction w generalizing v with
  | nil => simp [expandW] at h
  | cons x w ih =>
    cases v with
    | nil =>
      by_cases hx : x.1 = t₀
      · simp only [expandW, hx, if_true] at h
        rcases ih h with ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · simp at h1
      · simp only [expandW, hx, if_false, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl ⟨List.mem_cons_self .., hx⟩
        rcases ih h with ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · simp at h1
    | cons y₀ v =>
      by_cases hx : x.1 = t₀
      · simp only [expandW, hx, if_true, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inr ⟨List.mem_cons_self .., x, List.mem_cons_self .., hx⟩
        rcases ih h with ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, x, List.mem_cons_self .., hx⟩
      · simp only [expandW, hx, if_false, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl ⟨List.mem_cons_self .., hx⟩
        rcases ih h with ⟨h1, h2⟩ | ⟨h1, z, hz, hz'⟩
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · exact Or.inr ⟨h1, z, List.mem_cons_of_mem _ hz, hz'⟩

theorem map_snd_expandW {t₀ : I} {w v : List (I × A)}
    (h : (w.filter fun x => decide (x.1 = t₀)).map Prod.snd = v.map Prod.snd) :
    (expandW t₀ w v).map Prod.snd = w.map Prod.snd := by
  induction w generalizing v with
  | nil => simp [expandW]
  | cons x w ih =>
    by_cases hx : x.1 = t₀
    · rw [List.filter_cons_of_pos (by simpa using hx)] at h
      cases v with
      | nil => simp at h
      | cons y₀ v =>
        simp only [List.map_cons, List.cons.injEq] at h
        simp only [expandW, hx, if_true, List.map_cons, h.1, ih h.2]
    · rw [List.filter_cons_of_neg (by simpa using hx)] at h
      cases v with
      | nil => simp only [expandW, hx, if_false, List.map_cons, ih h]
      | cons y₀ v => simp only [expandW, hx, if_false, List.map_cons, ih h]

theorem filter_expandW_old {t₀ : I} {w v : List (I × A)} (p : I × A → Bool)
    (hv : ∀ y ∈ v, p y = false) (ht : ∀ x : I × A, x.1 = t₀ → p x = false) :
    (expandW t₀ w v).filter p = w.filter p := by
  induction w generalizing v with
  | nil => simp [expandW]
  | cons x w ih =>
    by_cases hx : x.1 = t₀
    · cases v with
      | nil => simp only [expandW, hx, if_true, List.filter_cons, ht x hx, ih hv]; rfl
      | cons y₀ v =>
        simp only [expandW, hx, if_true, List.filter_cons, ht x hx,
          hv y₀ (List.mem_cons_self ..), ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
        rfl
    · cases v with
      | nil => simp only [expandW, hx, if_false, List.filter_cons, ih hv]
      | cons y₀ v => simp only [expandW, hx, if_false, List.filter_cons, ih hv]

theorem filter_expandW_new {t₀ : I} {w v : List (I × A)} (p : I × A → Bool)
    (hw : ∀ x ∈ w, x.1 ≠ t₀ → p x = false)
    (hlen : (w.filter fun x => decide (x.1 = t₀)).length = v.length) :
    (expandW t₀ w v).filter p = v.filter p := by
  induction w generalizing v with
  | nil => cases v <;> simp_all [expandW]
  | cons x w ih =>
    have hw' : ∀ x ∈ w, x.1 ≠ t₀ → p x = false := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    by_cases hx : x.1 = t₀
    · rw [List.filter_cons_of_pos (by simpa using hx)] at hlen
      cases v with
      | nil => simp at hlen
      | cons y₀ v =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [expandW, hx, if_true, List.filter_cons, ih hw' hlen]
    · rw [List.filter_cons_of_neg (by simpa using hx)] at hlen
      cases v with
      | nil => simp only [expandW, hx, if_false, List.filter_cons, hw x (List.mem_cons_self ..) hx,
          ih hw' hlen]; rfl
      | cons y₀ v => simp only [expandW, hx, if_false, List.filter_cons,
          hw x (List.mem_cons_self ..) hx, ih hw' hlen]; rfl

theorem pairwise_expandW {t₀ : I} {w v : List (I × A)} {Q P R : I × A → I × A → Prop}
    (hQ : w.Pairwise Q) (hP : v.Pairwise P)
    (h1 : ∀ x ∈ w, ∀ y ∈ w, x.1 ≠ t₀ → y.1 ≠ t₀ → Q x y → R x y)
    (h2 : ∀ x ∈ w, ∀ z ∈ w, ∀ y ∈ v, x.1 ≠ t₀ → z.1 = t₀ → Q x z → R x y)
    (h3 : ∀ z ∈ w, ∀ y ∈ w, ∀ x ∈ v, y.1 ≠ t₀ → z.1 = t₀ → Q z y → R x y)
    (h4 : ∀ x ∈ v, ∀ y ∈ v, P x y → R x y) :
    (expandW t₀ w v).Pairwise R := by
  induction w generalizing v with
  | nil => simp [expandW]
  | cons x w ih =>
    rw [List.pairwise_cons] at hQ
    have m1 : ∀ {y}, y ∈ w → y ∈ x :: w := List.mem_cons_of_mem _
    have h1' : ∀ x ∈ w, ∀ y ∈ w, x.1 ≠ t₀ → y.1 ≠ t₀ → Q x y → R x y :=
      fun a ha b hb => h1 a (m1 ha) b (m1 hb)
    cases v with
    | nil =>
      have ih' := ih hQ.2 List.Pairwise.nil h1' (by simp) (by simp) (by simp)
      by_cases hx : x.1 = t₀
      · simpa only [expandW, hx, if_true] using ih'
      · simp only [expandW, hx, if_false]
        refine List.Pairwise.cons (fun y hy => ?_) ih'
        rcases mem_expandW hy with ⟨hy1, hy2⟩ | ⟨hy1, -⟩
        · exact h1 x (List.mem_cons_self ..) y (m1 hy1) hx hy2 (hQ.1 y hy1)
        · simp at hy1
    | cons y₀ v =>
      rw [List.pairwise_cons] at hP
      have m2 : ∀ {y}, y ∈ v → y ∈ y₀ :: v := List.mem_cons_of_mem _
      by_cases hx : x.1 = t₀
      · simp only [expandW, hx, if_true]
        refine List.Pairwise.cons (fun y hy => ?_) (ih hQ.2 hP.2 h1'
          (fun a ha z hz b hb => h2 a (m1 ha) z (m1 hz) b (m2 hb))
          (fun z hz b hb a ha => h3 z (m1 hz) b (m1 hb) a (m2 ha))
          (fun a ha b hb => h4 a (m2 ha) b (m2 hb)))
        rcases mem_expandW hy with ⟨hy1, hy2⟩ | ⟨hy1, -⟩
        · exact h3 x (List.mem_cons_self ..) y (m1 hy1) y₀ (List.mem_cons_self ..) hy2 hx
            (hQ.1 y hy1)
        · exact h4 y₀ (List.mem_cons_self ..) y (m2 hy1) (hP.1 y hy1)
      · simp only [expandW, hx, if_false]
        refine List.Pairwise.cons (fun y hy => ?_) (ih hQ.2 (List.pairwise_cons.2 hP) h1'
          (fun a ha z hz b hb => h2 a (m1 ha) z (m1 hz) b hb)
          (fun z hz b hb a ha => h3 z (m1 hz) b (m1 hb) a ha) h4)
        rcases mem_expandW hy with ⟨hy1, hy2⟩ | ⟨hy1, z, hz, hz'⟩
        · exact h1 x (List.mem_cons_self ..) y (m1 hy1) hx hy2 (hQ.1 y hy1)
        · exact h2 x (List.mem_cons_self ..) z (m1 hz) y hy1 hx hz' (hQ.1 z hz)

/-- A network all of whose trees are leaves is primitive, and the witness of the merge is a
linearisation inducing `π`. -/
theorem primitive_of_treesYield_leaves {M : Set (Method I A C)} {tn : TaskNetwork I A C}
    {trees : I → DTree I A C} {π : List A} (h : TreesYield M tn trees π)
    (hl : ∀ t ∈ tn.T, ∀ c m ch, trees t ≠ DTree.node c m ch) :
    tn.IsPrimitive ∧ ∃ l, tn.IsLinearization l ∧ tn.IsActionSeq l π := by
  obtain ⟨hval, ys, hys, w, hmap, hmem, hfil, hpw⟩ := h
  have hleaf : ∀ t ∈ tn.T, ∃ a, tn.α t = Sum.inl a ∧ ys t = [a] := by
    intro t ht
    have hv := hval t ht
    have hy := hys t ht
    cases htr : trees t with
    | leaf a =>
      rw [htr] at hv hy
      exact ⟨a, hv.leaf_inv, hy.leaf_inv⟩
    | node c m ch => exact absurd htr (hl t ht c m ch)
  have hlen : ∀ t ∈ tn.T, (w.filter fun x => decide (x.1 = t)).length = 1 := by
    intro t ht
    obtain ⟨a, -, hya⟩ := hleaf t ht
    have := congrArg List.length (hfil t ht)
    rw [List.length_map, hya] at this
    exact this
  refine ⟨fun t ht => ⟨_, (hleaf t ht).choose_spec.1⟩, w.map Prod.fst, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [List.nodup_iff_count_le_one]
    intro t
    rw [List.count, List.countP_map, List.countP_eq_length_filter]
    have e : ((fun x : I => x == t) ∘ Prod.fst : I × A → Bool) = fun x => decide (x.1 = t) := by
      funext x; by_cases h : x.1 = t <;> simp [h]
    rw [e]
    by_cases ht : t ∈ tn.T
    · rw [hlen t ht]
    · have : (w.filter fun x => decide (x.1 = t)) = [] := List.filter_eq_nil_iff.2 fun x hx => by
        have := hmem x hx
        simp only [decide_eq_true_eq]
        rintro rfl; exact ht this
      rw [this]; simp
  · intro t
    refine ⟨fun h => ?_, fun ht => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact hmem x hx
    · have hpos : 0 < (w.filter fun x => decide (x.1 = t)).length := by rw [hlen t ht]; omega
      obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
      obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
      exact List.mem_map.2 ⟨x, hx1, by simpa using hx2⟩
  · exact List.pairwise_map.2 hpw
  · unfold TaskNetwork.IsActionSeq
    rw [← hmap, List.map_map, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨a, ha, hya⟩ := hleaf x.1 (hmem x hx)
    have hx' : x.2 ∈ (w.filter fun y => decide (y.1 = x.1)).map Prod.snd :=
      List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simp⟩, rfl⟩
    rw [hfil x.1 (hmem x hx), hya, List.mem_singleton] at hx'
    simp only [Function.comp_apply, ha, hx']

open Classical in
/-- **One decomposition step along the trees.**  If the tree of `t₀` is a node with method `m`,
then decomposing `t₀` with a fresh copy `tn''` of `m`'s network gives trees for the new network
(the subtrees of the node for the inserted tasks), with the same merged yield and a smaller total
size. -/
theorem treesYield_decomp {M : Set (Method I A C)} {tn tn'' : TaskNetwork I A C}
    {trees : I → DTree I A C} {π : List A} (hwf : tn.WF) (hwf'' : tn''.WF)
    (hdisj : Disjoint tn.T tn''.T) (h : TreesYield M tn trees π) {t₀ : I} (ht₀ : t₀ ∈ tn.T)
    {c : C} {m : Method I A C} {ch : I → DTree I A C} (hnode : trees t₀ = DTree.node c m ch)
    (hiso : tn''.Iso m.subtasks) :
    m ∈ M ∧ tn.α t₀ = Sum.inr m.abstractTask ∧
      ∃ trees₁ : I → DTree I A C, TreesYield M (decomposeWith tn t₀ tn'') trees₁ π ∧
        ∑ t ∈ (decomposeWith tn t₀ tn'').T, (trees₁ t).size < ∑ t ∈ tn.T, (trees t).size ∧
        (∀ x ∈ tn''.T, ∃ u ∈ m.subtasks.T, trees₁ x = ch u) ∧
        (∀ x, x ∉ tn''.T → trees₁ x = trees x) := by
  obtain ⟨hval, ys, hys, w, hmap, hmem, hfil, hpw⟩ := h
  have hv := hval t₀ ht₀
  rw [hnode] at hv
  obtain ⟨hα, hmM, hc, hchv⟩ := hv.node_inv
  have hy := hys t₀ ht₀
  rw [hnode] at hy
  obtain ⟨ysm, hysm, wm, hwm_map, hwm_mem, hwm_fil, hwm_pw⟩ := hy.node_inv
  have hiso' := hiso
  obtain ⟨σ, hbij, hord, hlab⟩ := hiso'
  haveI : Nonempty I := ⟨t₀⟩
  let τ : I → I := Function.invFunOn σ tn''.T
  have hτ : ∀ u ∈ m.subtasks.T, τ u ∈ tn''.T ∧ σ (τ u) = u := fun u hu =>
    ⟨Function.invFunOn_mem (hbij.surjOn hu), Function.invFunOn_eq (hbij.surjOn hu)⟩
  have hστ : ∀ x ∈ tn''.T, τ (σ x) = x := fun x hx =>
    hbij.injOn (Function.invFunOn_mem (hbij.surjOn (hbij.mapsTo hx))) hx
      (Function.invFunOn_eq (hbij.surjOn (hbij.mapsTo hx)))
  have hold'' : ∀ x ∈ tn.T, x ∉ tn''.T := fun x hx => Finset.disjoint_left.1 hdisj hx
  set tn₁ := decomposeWith tn t₀ tn'' with htn₁
  let trees₁ : I → DTree I A C := fun x => if x ∈ tn''.T then ch (σ x) else trees x
  let ys₁ : I → List A := fun x => if x ∈ tn''.T then ysm (σ x) else ys x
  let v : List (I × A) := wm.map fun y => (τ y.1, y.2)
  have hvmem : ∀ y ∈ v, y.1 ∈ tn''.T := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact (hτ z.1 (hwm_mem z hz)).1
  have hvsnd : v.map Prod.snd = ys t₀ := by
    rw [← hwm_map, List.map_map]; rfl
  have hwt₀ : (w.filter fun x => decide (x.1 = t₀)).map Prod.snd = v.map Prod.snd := by
    rw [hfil t₀ ht₀, hvsnd]
  have hTY : TreesYield M tn₁ trees₁ π := by
    refine ⟨fun x hx => ?_, ys₁, fun x hx => ?_, expandW t₀ w v, ?_, ?_, fun s hs => ?_, ?_⟩
    · rcases mem_decomposeWith_T.1 hx with ⟨hx, -⟩ | hx
      · simp only [trees₁, htn₁, decomposeWith_α, hold'' x hx, if_false]
        exact hval x hx
      · simp only [trees₁, htn₁, decomposeWith_α, hx, if_true, hlab x hx]
        exact hchv (σ x) (hbij.mapsTo hx)
    · rcases mem_decomposeWith_T.1 hx with ⟨hx, -⟩ | hx
      · simp only [trees₁, ys₁, hold'' x hx, if_false]
        exact hys x hx
      · simp only [trees₁, ys₁, hx, if_true]
        exact hysm (σ x) (hbij.mapsTo hx)
    · rw [map_snd_expandW hwt₀, hmap]
    · intro x hx
      rcases mem_expandW hx with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact mem_decomposeWith_T.2 (Or.inl ⟨hmem x h1, h2⟩)
      · exact mem_decomposeWith_T.2 (Or.inr (hvmem x h1))
    · rcases mem_decomposeWith_T.1 hs with ⟨hs, hst⟩ | hs
      · rw [filter_expandW_old _ (fun y hy => by
            simp only [decide_eq_false_iff_not]
            intro e; exact hold'' s hs (e ▸ hvmem y hy))
          (fun x hx => by simp only [decide_eq_false_iff_not]; rw [hx]; exact Ne.symm hst)]
        simp only [ys₁, hold'' s hs, if_false]
        exact hfil s hs
      · have hlen : (w.filter fun x => decide (x.1 = t₀)).length = v.length := by
          have := congrArg List.length hwt₀
          simpa only [List.length_map] using this
        rw [filter_expandW_new _ (fun x hx _ => by
            simp only [decide_eq_false_iff_not]
            intro e; exact hold'' x.1 (hmem x hx) (e ▸ hs)) hlen]
        simp only [ys₁, hs, if_true, v, List.filter_map, List.map_map]
        rw [← hwm_fil (σ s) (hbij.mapsTo hs)]
        have e1 : ∀ y ∈ wm, ((fun x : I × A => decide (x.1 = s)) ∘ fun y => (τ y.1, y.2)) y =
            decide (y.1 = σ s) := fun y hy => by
          simp only [Function.comp_apply, decide_eq_decide]
          constructor
          · rintro rfl; exact ((hτ y.1 (hwm_mem y hy)).2).symm
          · rintro e; rw [e]; exact hστ s hs
        rw [List.filter_congr e1]
        rfl
    · have hPv : v.Pairwise fun x y => ¬ tn''.ord y.1 x.1 := by
        rw [List.pairwise_map]
        refine hwm_pw.imp_of_mem fun {a b} ha hb hab hord'' => hab ?_
        have := (hord (τ b.1) (hτ b.1 (hwm_mem b hb)).1 (τ a.1) (hτ a.1 (hwm_mem a ha)).1).1 hord''
        rwa [(hτ b.1 (hwm_mem b hb)).2, (hτ a.1 (hwm_mem a ha)).2] at this
      refine pairwise_expandW hpw hPv ?_ ?_ ?_ ?_
      · intro x hx y hy hx' hy' hq hr
        exact hq ((decomposeWith_ord_old_old hwf'' hdisj (hmem y hy) hy' (hmem x hx) hx').1 hr)
      · intro x hx z hz y hy hx' hz' hq hr
        rw [decomposeWith_ord_new_old hwf hwf'' hdisj (hvmem y hy) (hmem x hx)] at hr
        exact hq (hz' ▸ hr)
      · intro z hz y hy x hx hy' hz' hq hr
        rw [decomposeWith_ord_old_new hwf hwf'' hdisj (hmem y hy) (hvmem x hx)] at hr
        exact hq (hz' ▸ hr)
      · intro x hx y hy hp hr
        exact hp ((decomposeWith_ord_new_new hwf hdisj (hvmem y hy) (hvmem x hx)).1 hr)
  have hlt : ∑ t ∈ tn₁.T, (trees₁ t).size < ∑ t ∈ tn.T, (trees t).size := by
    rw [← Finset.add_sum_erase _ _ ht₀, hnode]
    have hT₁ : tn₁.T = tn.T.erase t₀ ∪ tn''.T := rfl
    have hd : Disjoint (tn.T.erase t₀) tn''.T :=
      Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
    rw [hT₁, Finset.sum_union hd]
    have e1 : ∑ x ∈ tn.T.erase t₀, (trees₁ x).size = ∑ x ∈ tn.T.erase t₀, (trees x).size :=
      Finset.sum_congr rfl fun x hx => by
        simp only [trees₁, hold'' x (Finset.mem_of_mem_erase hx), if_false]
    have e2 : ∑ x ∈ tn''.T, (trees₁ x).size = ∑ u ∈ m.subtasks.T, (ch u).size :=
      Finset.sum_nbij σ (fun x hx => hbij.mapsTo hx) hbij.injOn hbij.surjOn fun x hx => by
        simp only [trees₁, hx, if_true]
    rw [e1, e2, DTree.size]
    omega
  refine ⟨hmM, by rw [hc]; exact hα, trees₁, hTY, hlt, fun x hx => ⟨σ x, hbij.mapsTo hx, ?_⟩,
    fun x hx => ?_⟩
  · simp only [trees₁, hx, if_true]
  · simp only [trees₁, hx, if_false]

open Classical in
/-- **From trees to decompositions** (by induction on the total size of the trees: the root of a
node is decomposed with its method, and its subtrees become the trees of the inserted copy). -/
theorem decomposesTo_of_treesYield [Infinite I] {M : Set (Method I A C)}
    (hM : ∀ m ∈ M, m.subtasks.WF) {tn : TaskNetwork I A C} (hwf : tn.WF)
    {trees : I → DTree I A C} {π : List A} (h : TreesYield M tn trees π) :
    ∃ tn', DecomposesTo M tn tn' ∧ tn'.IsPrimitive ∧
      ∃ l, tn'.IsLinearization l ∧ tn'.IsActionSeq l π := by
  suffices H : ∀ n, ∀ (tn : TaskNetwork I A C) (trees : I → DTree I A C) (π : List A), tn.WF →
      TreesYield M tn trees π → ∑ t ∈ tn.T, (trees t).size = n →
      ∃ tn', DecomposesTo M tn tn' ∧ tn'.IsPrimitive ∧
        ∃ l, tn'.IsLinearization l ∧ tn'.IsActionSeq l π from H _ tn trees π hwf h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro tn trees π hwf h hn
  by_cases hex : ∃ t₀ ∈ tn.T, ∃ c m ch, trees t₀ = DTree.node c m ch
  swap
  · push_neg at hex
    exact ⟨tn, Relation.ReflTransGen.refl, primitive_of_treesYield_leaves h hex⟩
  obtain ⟨t₀, ht₀, c, m, ch, hnode⟩ := hex
  have hv := h.1 t₀ ht₀
  rw [hnode] at hv
  have hmM := hv.node_inv.2.1
  obtain ⟨tn'', hwf'', hiso, hdisj⟩ := TaskNetwork.exists_fresh_iso_copy m.subtasks (hM m hmM) tn.T
  obtain ⟨hmM, hα, trees₁, hTY, hlt, -, -⟩ := treesYield_decomp hwf hwf'' hdisj h ht₀ hnode hiso
  have hstep : DecompStep' M tn (decomposeWith tn t₀ tn'') :=
    ⟨t₀, m, hmM, ht₀, hα, tn'', hwf'', hiso, hdisj, rfl⟩
  obtain ⟨tn', hd, hp, l, hl, has⟩ :=
    ih _ (hn ▸ hlt) _ trees₁ π (decomposeWith_wf hwf hwf'' hdisj) hTY rfl
  exact ⟨tn', Relation.ReflTransGen.head hstep hd, hp, l, hl, has⟩

/-! ### Shrinking yields -/

/-- Sublists of the per-task subsequences of a labelled sequence are realised by a sublist. -/
theorem exists_sublist_filters : ∀ (w : List (I × A)) (ys' : I → List A),
    (∀ t, (ys' t).Sublist ((w.filter fun x => decide (x.1 = t)).map Prod.snd)) →
    ∃ w' : List (I × A), w'.Sublist w ∧
      ∀ t, (w'.filter fun x => decide (x.1 = t)).map Prod.snd = ys' t
  | [], ys', h => ⟨[], List.Sublist.slnil, fun t => by
      have := h t; simp only [List.filter_nil, List.map_nil, List.sublist_nil] at this
      simp [this]⟩
  | x :: w, ys', h => by
    have hne : ∀ t, t ≠ x.1 → (ys' t).Sublist ((w.filter fun x => decide (x.1 = t)).map Prod.snd) :=
      fun t ht => by
        have := h t
        rwa [List.filter_cons_of_neg (by simpa using Ne.symm ht)] at this
    have hx := h x.1
    rw [List.filter_cons_of_pos (by simp), List.map_cons] at hx
    rcases List.sublist_cons_iff.1 hx with hs | ⟨r, hr, hs⟩
    · obtain ⟨w', h1, h2⟩ := exists_sublist_filters w ys' fun t => by
        by_cases ht : t = x.1
        · subst ht; exact hs
        · exact hne t ht
      exact ⟨w', h1.cons x, h2⟩
    · obtain ⟨w', h1, h2⟩ := exists_sublist_filters w (Function.update ys' x.1 r) fun t => by
        by_cases ht : t = x.1
        · subst ht; simpa using hs
        · rw [Function.update_of_ne ht]; exact hne t ht
      refine ⟨x :: w', h1.cons₂ x, fun t => ?_⟩
      by_cases ht : t = x.1
      · subst ht
        rw [List.filter_cons_of_pos (by simp), List.map_cons, h2, hr]
        simp
      · rw [List.filter_cons_of_neg (by simpa using Ne.symm ht), h2, Function.update_of_ne ht]

/-- **Shrinking a merge**: if every part shrinks to a subsequence, the merge shrinks to a
subsequence. -/
theorem OrdMerge.sublist {tn : TaskNetwork I A C} {ys : I → List A} {π : List A}
    (hm : OrdMerge tn ys π) (ys' : I → List A) (h : ∀ t ∈ tn.T, (ys' t).Sublist (ys t)) :
    ∃ π' : List A, π'.Sublist π ∧ OrdMerge tn ys' π' := by
  classical
  obtain ⟨w, hmap, hmem, hfil, hpw⟩ := hm
  obtain ⟨w', h1, h2⟩ := exists_sublist_filters w (fun t => if t ∈ tn.T then ys' t else [])
    fun t => by
      by_cases ht : t ∈ tn.T
      · simp only [ht, if_true, hfil t ht]; exact h t ht
      · simp only [ht, if_false]; exact List.nil_sublist _
  refine ⟨w'.map Prod.snd, hmap ▸ h1.map _, w', rfl, fun x hx => hmem x (h1.subset hx),
    fun t ht => by rw [h2]; simp [ht], hpw.sublist h1⟩

/-- Each part of a merge is a subsequence of it. -/
theorem OrdMerge.sublist_of_mem {tn : TaskNetwork I A C} {ys : I → List A} {π : List A}
    (hm : OrdMerge tn ys π) {t : I} (ht : t ∈ tn.T) : (ys t).Sublist π := by
  obtain ⟨w, hmap, -, hfil, -⟩ := hm
  rw [← hfil t ht, ← hmap]
  exact (List.filter_sublist).map _

/-! ### Pruning cycles -/

namespace DTree

/-- `Occurs c dt`: some node of `dt` is labelled with the compound task name `c`. -/
inductive Occurs (c : C) : DTree I A C → Prop
  | root {m : Method I A C} {ch : I → DTree I A C} : Occurs c (node c m ch)
  | child {c' : C} {m : Method I A C} {ch : I → DTree I A C} {t : I} (ht : t ∈ m.subtasks.T)
      (h : Occurs c (ch t)) : Occurs c (node c' m ch)

/-- **Acyclic trees**: no compound task name occurs twice on a path from the root. -/
inductive Acyc : DTree I A C → Prop
  | leaf (a : A) : Acyc (leaf a)
  | node {c : C} {m : Method I A C} {ch : I → DTree I A C}
      (h : ∀ t ∈ m.subtasks.T, Acyc (ch t)) (hn : ∀ t ∈ m.subtasks.T, ¬ Occurs c (ch t)) :
      Acyc (node c m ch)

/-- A node labelled `c` gives a valid tree for `c`, acyclic if the tree is, with a subsequence
of the yield. -/
theorem exists_sub_of_occurs {M : Set (Method I A C)} {c : C} {dt : DTree I A C}
    (hocc : Occurs c dt) : ∀ {s : A ⊕ C} {π : List A}, dt.Valid M s → dt.Yield π → dt.Acyc →
      ∃ (sub : DTree I A C) (π' : List A), sub.Valid M (Sum.inr c) ∧ sub.Yield π' ∧
        π'.Sublist π ∧ sub.Acyc := by
  induction hocc with
  | root =>
    intro s π hv hy ha
    obtain ⟨rfl, -⟩ := hv.node_inv
    exact ⟨_, π, hv, hy, List.Sublist.refl _, ha⟩
  | @child c' m ch t ht _ ih =>
    intro s π hv hy ha
    obtain ⟨-, -, -, hch⟩ := hv.node_inv
    obtain ⟨ys, hys, hm⟩ := hy.node_inv
    have ha' : (ch t).Acyc := by cases ha with | node h _ => exact h t ht
    obtain ⟨sub, π', h1, h2, h3, h4⟩ := ih (hch t ht) (hys t ht) ha'
    exact ⟨sub, π', h1, h2, h3.trans (hm.sublist_of_mem ht), h4⟩

/-- A valid tree for a compound task is a node for it. -/
theorem Valid.eq_node_of_inr {M : Set (Method I A C)} {dt : DTree I A C} {c : C}
    (h : dt.Valid M (Sum.inr c)) : ∃ m ch, dt = DTree.node c m ch := by
  cases h with
  | node _ _ _ => exact ⟨_, _, rfl⟩

/-- A valid tree for a primitive task is a leaf for it. -/
theorem Valid.eq_leaf_of_inl {M : Set (Method I A C)} {dt : DTree I A C} {a : A}
    (h : dt.Valid M (Sum.inl a)) : dt = DTree.leaf a := by
  cases h; rfl

/-- The names `S` do not occur in `dt`, except possibly as its root. -/
def AncGood (S : Set C) (dt : DTree I A C) : Prop :=
  ∀ c ∈ S, ¬ Occurs c dt ∨ ∃ m ch, dt = node c m ch

open Classical in
/-- **Pruning**: every valid tree can be replaced by a valid *acyclic* tree for the same task
whose yield is a subsequence of the original yield. -/
theorem exists_acyc {M : Set (Method I A C)} (dt : DTree I A C) :
    ∀ {s : A ⊕ C} {π : List A}, dt.Valid M s → dt.Yield π →
      ∃ (dt' : DTree I A C) (π' : List A), dt'.Valid M s ∧ dt'.Yield π' ∧ π'.Sublist π ∧
        dt'.Acyc := by
  induction dt with
  | leaf a =>
    intro s π hv hy
    exact ⟨_, π, hv, hy, List.Sublist.refl _, Acyc.leaf a⟩
  | node c m ch ih =>
    intro s π hv hy
    obtain ⟨rfl, hmM, hc, hch⟩ := hv.node_inv
    obtain ⟨ys, hys, hm⟩ := hy.node_inv
    have H : ∀ t, ∃ (dt' : DTree I A C) (π' : List A), t ∈ m.subtasks.T →
        dt'.Valid M (m.subtasks.α t) ∧ dt'.Yield π' ∧ π'.Sublist (ys t) ∧ dt'.Acyc := by
      intro t
      by_cases ht : t ∈ m.subtasks.T
      · obtain ⟨dt', π', h⟩ := ih t (hch t ht) (hys t ht)
        exact ⟨dt', π', fun _ => h⟩
      · exact ⟨ch t, [], fun h => absurd h ht⟩
    choose ch' ys' hspec using H
    obtain ⟨π'', hsub, hm'⟩ := hm.sublist ys' fun t ht => (hspec t ht).2.2.1
    have hv' : (node c m ch').Valid M (Sum.inr c) :=
      Valid.node hmM hc fun t ht => (hspec t ht).1
    have hy' : (node c m ch').Yield π'' := Yield.node ys' (fun t ht => (hspec t ht).2.1) hm'
    by_cases hocc : ∃ t ∈ m.subtasks.T, Occurs c (ch' t)
    · obtain ⟨t, ht, ho⟩ := hocc
      obtain ⟨sub, π', h1, h2, h3, h4⟩ := exists_sub_of_occurs ho (hspec t ht).1 (hspec t ht).2.1
        (hspec t ht).2.2.2
      exact ⟨sub, π', h1, h2,
        h3.trans (((hspec t ht).2.2.1).trans (hm.sublist_of_mem ht)), h4⟩
    · push_neg at hocc
      exact ⟨_, π'', hv', hy', hsub, Acyc.node (fun t ht => (hspec t ht).2.2.2) hocc⟩

end DTree

/-- **Proposition 2.2.1** (for primitive yields): a task network can be decomposed into a
primitive network one of whose linearisations induces `π` iff it has valid decomposition trees
whose yields merge into `π`. -/
theorem netYield_iff_trees [Infinite I] [Nonempty A] {M : Set (Method I A C)}
    (hM : ∀ m ∈ M, m.subtasks.WF) {tn : TaskNetwork I A C} (hwf : tn.WF) {π : List A} :
    (∃ tn', DecomposesTo M tn tn' ∧ tn'.IsPrimitive ∧
      ∃ l, tn'.IsLinearization l ∧ tn'.IsActionSeq l π) ↔ ∃ trees, TreesYield M tn trees π :=
  ⟨fun ⟨_, hd, hp, _, hl, has⟩ => treesYield_of_decomposesTo hwf hd hp hl has,
    fun ⟨_, h⟩ => decomposesTo_of_treesYield hM hwf h⟩

namespace Problem

universe u'

variable {F : Type u'} (P : Problem F A C I)

/-- **Plan existence via decompositions**: `P` has a solution iff its initial task network
decomposes into a primitive network with a linearisation that runs from the initial state into
a goal state (ordering insertion only serves to rule out the other linearisations). -/
theorem solvable_iff_decomp (hP : P.WF) :
    P.Solvable ↔ ∃ tn, DecomposesTo P.methods P.tnI tn ∧ tn.IsPrimitive ∧
      ∃ l as s, tn.IsLinearization l ∧ tn.IsActionSeq l as ∧ P.Run as P.init s ∧
        P.GoalState s := by
  constructor
  · rintro ⟨tnS, hex, hgoal, tn, hdec, hoi⟩
    have hprim := hex.1
    have hwf : tn.WF := hdec.wf hP.tnI
    have hwfS : tnS.WF := hoi.wf hwf
    obtain ⟨l, as, hl, has⟩ := TaskNetwork.exists_linearization_actionSeq hwfS hprim
    obtain ⟨s', hrun⟩ := hex.2 l as hl has
    have hg := hgoal s' ⟨l, as, hl, has, hrun⟩
    refine ⟨tn, hdec, ?_, l, as, s', hoi.isLinearization hl, ?_, hrun, hg⟩
    · intro t ht
      obtain ⟨a, ha⟩ := hprim t (by rw [hoi.T]; exact ht)
      exact ⟨a, by rw [← hoi.α]; exact ha⟩
    · unfold TaskNetwork.IsActionSeq at has ⊢
      rw [← hoi.α]; exact has
  · rintro ⟨tn, hreach, hprim, l, as, s, hl, has, hrun, hgoal⟩
    have hwf : tn.WF := HTN.DecomposesTo.wf hreach hP.tnI
    obtain ⟨tn', -, hoi, hwf', hT, hα, huniq⟩ := exists_oiReach_unique_lin hwf hprim hl
    have hprim' : tn'.IsPrimitive := by
      intro t ht; rw [hT] at ht; obtain ⟨a, ha⟩ := hprim t ht; exact ⟨a, by rw [hα]; exact ha⟩
    have has' : tn'.IsActionSeq l as := by
      unfold TaskNetwork.IsActionSeq at has ⊢; rw [hα]; exact has
    have key : ∀ l' as', tn'.IsLinearization l' → tn'.IsActionSeq l' as' → l' = l ∧ as' = as := by
      intro l' as' hl' has''
      obtain rfl := huniq l' hl'
      exact ⟨rfl, TaskNetwork.isActionSeq_unique has'' has'⟩
    have hdet : ∀ {bs : List A} {s₀ s₁ s₂ : Set F}, P.Run bs s₀ s₁ → P.Run bs s₀ s₂ → s₁ = s₂ := by
      intro bs
      induction bs with
      | nil => intro s₀ s₁ s₂ h₁ h₂; exact h₁.trans h₂.symm
      | cons b bs ih => intro s₀ s₁ s₂ h₁ h₂; exact ih h₁.2 h₂.2
    refine ⟨tn', ⟨hprim', fun l' as' hl' has'' => ?_⟩, fun s' ⟨l', as', hl', has'', hrun'⟩ => ?_,
      tn, hreach, hoi⟩
    · obtain ⟨rfl, rfl⟩ := key l' as' hl' has''
      exact ⟨s, hrun⟩
    · obtain ⟨rfl, rfl⟩ := key l' as' hl' has''
      rw [hdet hrun' hrun]; exact hgoal

/-- **Plan existence via decomposition trees** (Prop. 2.2.1 applied to Def. 2.7): `P` has a
solution iff its initial tasks have valid decomposition trees whose yields merge into an action
sequence running from the initial state into a goal state. -/
theorem solvable_iff_trees [Infinite I] [Nonempty A] (hP : P.WF) :
    P.Solvable ↔ ∃ (trees : I → DTree I A C) (π : List A) (s : Set F),
      TreesYield P.methods P.tnI trees π ∧ P.Run π P.init s ∧ P.GoalState s := by
  rw [solvable_iff_decomp P hP]
  constructor
  · rintro ⟨tn, hd, hp, l, as, s, hl, has, hrun, hg⟩
    obtain ⟨trees, ht⟩ := treesYield_of_decomposesTo hP.tnI hd hp hl has
    exact ⟨trees, as, s, ht, hrun, hg⟩
  · rintro ⟨trees, π, s, ht, hrun, hg⟩
    obtain ⟨tn, hd, hp, l, hl, has⟩ := decomposesTo_of_treesYield hP.methods hP.tnI ht
    exact ⟨tn, hd, hp, l, π, s, hl, has, hrun, hg⟩

end Problem

end Article

end HTN
