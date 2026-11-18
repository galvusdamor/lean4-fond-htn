import HtnComplexity.Article.TOSem
/-!
# Induction over refinements, and sequence networks

Tools for hardness proofs with totally ordered problems:

* `HTN.Article.refT_induction` — **induction over refinements** (`HTN.Article.RefT`): a property
  holding for actions and closed under the methods (along the linearisation, with the property for
  every link) holds for every refinement;
* `HTN.Article.seqTn` — the **sequence network** of a list of labels: ids `0, …, n - 1`, totally
  ordered by `<`; it is well-formed, totally ordered, and its linearisation is `0, …, n - 1`
  (`HTN.Article.lin_seqTn`), so refinement along it is refinement of the list of labels one after
  the other (`HTN.Article.chainR_seqTn_iff`, with `HTN.Article.ChainL`).
-/

namespace HTN

namespace Article

open Syn

/-! ### Chains -/

/-- The tasks `l`, labelled by `lab`, are related by `R` one after the other. -/
inductive ChainR (R : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop) (lab : ℕ → ℕ ⊕ ℕ) :
    List ℕ → Set ℕ → Set ℕ → Prop
  | nil (s : Set ℕ) : ChainR R lab [] s s
  | cons {x : ℕ} {l : List ℕ} {s s₁ s' : Set ℕ} (h₁ : R (lab x) s s₁)
      (h₂ : ChainR R lab l s₁ s') : ChainR R lab (x :: l) s s'

/-- The task names `l` are related by `R` one after the other. -/
inductive ChainL (R : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop) : List (ℕ ⊕ ℕ) → Set ℕ → Set ℕ → Prop
  | nil (s : Set ℕ) : ChainL R [] s s
  | cons {n : ℕ ⊕ ℕ} {l : List (ℕ ⊕ ℕ)} {s s₁ s' : Set ℕ} (h₁ : R n s s₁)
      (h₂ : ChainL R l s₁ s') : ChainL R (n :: l) s s'

theorem chainR_iff_chainL {R : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop} {lab : ℕ → ℕ ⊕ ℕ} :
    ∀ {l : List ℕ} {s s' : Set ℕ}, ChainR R lab l s s' ↔ ChainL R (l.map lab) s s' := by
  intro l
  induction l with
  | nil =>
    intro s s'
    exact ⟨fun h => by cases h; exact .nil _, fun h => by cases h; exact .nil _⟩
  | cons x l ih =>
    intro s s'
    constructor
    · intro h; cases h with | cons h₁ h₂ => exact .cons h₁ (ih.1 h₂)
    · intro h; cases h with | cons h₁ h₂ => exact .cons h₁ (ih.2 h₂)

theorem chainL_nil_iff {R : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop} {s s' : Set ℕ} :
    ChainL R [] s s' ↔ s' = s :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .nil _⟩

theorem chainL_cons_iff {R : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop} {n : ℕ ⊕ ℕ} {l : List (ℕ ⊕ ℕ)}
    {s s' : Set ℕ} : ChainL R (n :: l) s s' ↔ ∃ s₁, R n s s₁ ∧ ChainL R l s₁ s' :=
  ⟨fun h => by cases h with | cons h₁ h₂ => exact ⟨_, h₁, h₂⟩, fun ⟨_, h₁, h₂⟩ => .cons h₁ h₂⟩

theorem chainL_append_iff {R : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop} :
    ∀ {l₁ l₂ : List (ℕ ⊕ ℕ)} {s s' : Set ℕ},
      ChainL R (l₁ ++ l₂) s s' ↔ ∃ s₁, ChainL R l₁ s s₁ ∧ ChainL R l₂ s₁ s' := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ s s'
    simp only [List.nil_append, chainL_nil_iff]
    exact ⟨fun h => ⟨s, rfl, h⟩, fun ⟨s₁, h₁, h₂⟩ => h₁ ▸ h₂⟩
  | cons n l ih =>
    intro l₂ s s'
    simp only [List.cons_append, chainL_cons_iff, ih]
    exact ⟨fun ⟨s₁, h₁, s₂, h₂, h₃⟩ => ⟨s₂, ⟨s₁, h₁, h₂⟩, h₃⟩,
      fun ⟨s₂, ⟨s₁, h₁, h₂⟩, h₃⟩ => ⟨s₁, h₁, s₂, h₂, h₃⟩⟩

theorem chainT_iff_chainR {p : ProbDesc} {lab : ℕ → ℕ ⊕ ℕ} :
    ∀ {l : List ℕ} {s s' : Set ℕ}, ChainT p lab l s s' ↔ ChainR (RefT p) lab l s s' := by
  intro l
  induction l with
  | nil =>
    intro s s'
    exact ⟨fun h => by cases h; exact .nil _, fun h => by cases h; exact .nil _⟩
  | cons x l ih =>
    intro s s'
    constructor
    · intro h; cases h with | cons h₁ h₂ => exact .cons h₁ (ih.1 h₂)
    · intro h; cases h with | cons h₁ h₂ => exact .cons h₁ (ih.2 h₂)

/-! ### Induction over refinements -/

/-- **Induction over refinements** in a problem whose methods are totally ordered. -/
theorem refT_induction {p : ProbDesc} (P : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop)
    (hto : ∀ e ∈ p.methods, e.2.toTaskNetwork.IsTotallyOrdered)
    (hprim : ∀ a s, (p.toProblem.δ a).Applicable s → P (Sum.inl a) s ((p.toProblem.δ a).apply s))
    (hcomp : ∀ e ∈ p.methods, ∀ s s',
      ChainR (fun n s s' => RefT p n s s' ∧ P n s s') e.2.label (TnDesc.lin e.2) s s' →
        P (Sum.inr e.1) s s') :
    ∀ {n : ℕ ⊕ ℕ} {s s' : Set ℕ}, RefT p n s s' → P n s s' := by
  intro n s s' h
  obtain ⟨dt, ys, hv, hy, hr⟩ := h
  induction dt generalizing n ys s s' with
  | leaf a =>
    obtain rfl := hv.leaf_inv
    obtain rfl := hy.leaf_inv
    obtain ⟨happ, hr⟩ := hr
    cases hr
    exact hprim a s happ
  | node c m ch ih =>
    obtain ⟨rfl, ⟨e, he, rfl⟩, hc, hch⟩ := hv.node_inv
    subst hc
    obtain ⟨ys', hys, hm⟩ := hy.node_inv
    have hto' := hto e he
    have hl := TnDesc.isLinearization_lin hto'
    rw [(ordMerge_lin_iff (TnDesc.toTaskNetwork_wf _) hto' hl).1 hm] at hr
    have key : ∀ l : List ℕ, (∀ x ∈ l, x ∈ e.toMethod.subtasks.T) → ∀ s s',
        p.toProblem.Run (l.map ys').flatten s s' →
          ChainR (fun n s s' => RefT p n s s' ∧ P n s s') e.2.label l s s' := by
      intro l
      induction l with
      | nil => intro _ s s' h; cases h; exact .nil _
      | cons x l ihl =>
        intro hmem s s' h
        rw [List.map_cons, List.flatten_cons, run_append] at h
        obtain ⟨s₁, h1, h2⟩ := h
        have hx := hmem x (by simp)
        exact .cons ⟨⟨ch x, ys' x, hch x hx, hys x hx, h1⟩, ih x (n := _) (ys := ys' x) (s := s) (s' := s₁) (hch x hx) (hys x hx) h1⟩
          (ihl (fun y hy => hmem y (by simp [hy])) _ _ h2)
    exact hcomp e he s s' (key _ (fun x hx => (hl.2.1 x).1 hx) s s' hr)

/-! ### Sequence networks -/

/-- The task name of a label `(b, c)`: compound iff `b`. -/
def toLab (q : Bool × ℕ) : ℕ ⊕ ℕ := if q.1 then Sum.inr q.2 else Sum.inl q.2

/-- **The sequence network** of a list of labels. -/
def seqTn (ls : List (Bool × ℕ)) : TnDesc :=
  (List.range ls.length,
    (List.range ls.length).flatMap (fun i => ((List.range ls.length).filter fun j => decide (i < j)).map
      fun j => (i, j)),
    (List.range ls.length).map fun i => (i, ls.getI i))

theorem seqTn_ids (ls : List (Bool × ℕ)) : (seqTn ls).ids = List.range ls.length := rfl

theorem mem_ordList_seqTn {ls : List (Bool × ℕ)} {a b : ℕ} :
    (a, b) ∈ (seqTn ls).ordList ↔ a < b ∧ b < ls.length := by
  simp only [seqTn, TnDesc.ordList, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, -, j, ⟨hj, hij⟩, rfl, rfl⟩; exact ⟨hij, hj⟩
  · rintro ⟨hab, hb⟩; exact ⟨a, by omega, b, ⟨hb, hab⟩, rfl, rfl⟩

theorem lookup_seqTn {ls : List (Bool × ℕ)} {i : ℕ} (hi : i < ls.length) :
    (seqTn ls).lbl.lookup i = some (ls.getI i) := by
  simp only [seqTn, TnDesc.lbl]
  have : ∀ (l : List ℕ), i ∈ l → l.Nodup →
      (l.map fun j => (j, ls.getI j)).lookup i = some (ls.getI i) := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons a l ih =>
      intro h hnd
      rw [List.map_cons, List.lookup_cons]
      by_cases ha : i = a
      · subst ha; simp
      · rw [List.mem_cons] at h
        have : (i == a) = false := by simp [ha]
        rw [this]
        exact ih (h.resolve_left ha) (List.nodup_cons.1 hnd).2
  exact this _ (List.mem_range.2 hi) (List.nodup_range)

theorem label_seqTn {ls : List (Bool × ℕ)} {i : ℕ} (hi : i < ls.length) :
    (seqTn ls).label i = toLab (ls.getI i) := by
  unfold TnDesc.label
  rw [lookup_seqTn hi]
  rcases ls.getI i with ⟨_ | _, c⟩ <;> rfl

theorem seqTn_valid {prim : ℕ → Prop} {ls : List (Bool × ℕ)}
    (hprim : ∀ q ∈ ls, q.1 = false → prim q.2) : TnValid prim (seqTn ls) := by
  refine ⟨List.nodup_range, fun q hq => ?_, fun a h => ?_, fun a b c h1 h2 => ?_, ?_, fun q hq hf => ?_⟩
  · obtain ⟨a, b⟩ := q
    have := mem_ordList_seqTn.1 hq
    simp only [seqTn_ids, List.mem_range]
    omega
  · have := mem_ordList_seqTn.1 h; omega
  · have h1 := mem_ordList_seqTn.1 h1
    have h2 := mem_ordList_seqTn.1 h2
    exact mem_ordList_seqTn.2 ⟨by omega, h2.2⟩
  · simp [seqTn, TnDesc.lbl, TnDesc.ids, List.map_map, Function.comp_def]
  · simp only [seqTn, TnDesc.lbl, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    apply hprim _ _ hf
    rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

theorem ord_seqTn_iff {ls : List (Bool × ℕ)} {a b : ℕ} :
    (seqTn ls).toTaskNetwork.ord a b ↔ a < b ∧ b < ls.length := by
  have hv : TnValid (fun _ => True) (seqTn ls) := seqTn_valid fun _ _ _ => trivial
  rw [TnDesc.toTaskNetwork_ord]
  unfold TnDesc.preOrd
  rw [hv.transGen_iff, hv.transGen_iff, mem_ordList_seqTn, mem_ordList_seqTn, seqTn_ids,
    List.mem_range, List.mem_range]
  omega

theorem seqTn_isTO (ls : List (Bool × ℕ)) : (seqTn ls).toTaskNetwork.IsTotallyOrdered := by
  intro a ha b hb hne
  have ha' : a < ls.length := by simpa [TnDesc.toTaskNetwork, seqTn_ids] using ha
  have hb' : b < ls.length := by simpa [TnDesc.toTaskNetwork, seqTn_ids] using hb
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact Or.inl (ord_seqTn_iff.2 ⟨h, hb'⟩)
  · exact Or.inr (ord_seqTn_iff.2 ⟨h, ha'⟩)

theorem length_filter_range_lt (i : ℕ) : ∀ n, i ≤ n →
    ((List.range n).filter fun j => decide (j < i)).length = i := by
  intro n
  induction n with
  | zero => intro h; simp; omega
  | succ n ih =>
    intro h
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hn : i ≤ n
    · rw [ih hn]; simp; omega
    · have : i = n + 1 := by omega
      subst this
      have h2 : ((List.range n).filter fun j => decide (j < n + 1)).length = n := by
        rw [List.filter_eq_self.2 (fun j hj => by simp at hj ⊢; omega)]; simp
      rw [h2]; simp

theorem rank_seqTn {ls : List (Bool × ℕ)} {i : ℕ} (hi : i < ls.length) :
    TnDesc.rank (seqTn ls) i = i := by
  unfold TnDesc.rank
  rw [seqTn_ids]
  have : ((List.range ls.length).filter fun j => TnDesc.ordB (seqTn ls) j i) =
      ((List.range ls.length).filter fun j => decide (j < i)) := by
    refine List.filter_congr fun j hj => ?_
    rw [Bool.eq_iff_iff, TnDesc.ordB_iff, ord_seqTn_iff, decide_eq_true_eq]
    omega
  rw [this, length_filter_range_lt i _ hi.le]

/-- **The linearisation of a sequence network.** -/
theorem lin_seqTn (ls : List (Bool × ℕ)) : TnDesc.lin (seqTn ls) = List.range ls.length := by
  have hTO := seqTn_isTO ls
  have hmem : ∀ x, x ∈ TnDesc.lin (seqTn ls) ↔ x ∈ List.range ls.length := fun x => by
    rw [TnDesc.mem_lin hTO, seqTn_ids]
  have hperm : (TnDesc.lin (seqTn ls)).Perm (List.range ls.length) :=
    (List.perm_ext_iff_of_nodup (TnDesc.nodup_lin _) List.nodup_range).2 hmem
  have hs : (TnDesc.lin (seqTn ls)).Pairwise (· ≤ ·) := by
    refine (TnDesc.pairwise_lin (seqTn ls)).imp_of_mem ?_
    intro a b ha hb h
    rw [rank_seqTn (List.mem_range.1 ((hmem a).1 ha)),
      rank_seqTn (List.mem_range.1 ((hmem b).1 hb))] at h
    exact h.le
  exact List.eq_of_perm_of_sorted (fun a b _ _ h1 h2 => le_antisymm h1 h2) hs
    List.pairwise_le_range hperm

theorem map_label_range_seqTn (ls : List (Bool × ℕ)) :
    (List.range ls.length).map (seqTn ls).label = ls.map toLab := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < ls.length := by simpa using h1
    rw [label_seqTn hi, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hi]

/-- **Refinement along a sequence network** is refinement of its labels one after the other. -/
theorem chainR_seqTn_iff {R : ℕ ⊕ ℕ → Set ℕ → Set ℕ → Prop} {ls : List (Bool × ℕ)}
    {s s' : Set ℕ} :
    ChainR R (seqTn ls).label (TnDesc.lin (seqTn ls)) s s' ↔ ChainL R (ls.map toLab) s s' := by
  rw [lin_seqTn, chainR_iff_chainL, map_label_range_seqTn]

end Article

end HTN
