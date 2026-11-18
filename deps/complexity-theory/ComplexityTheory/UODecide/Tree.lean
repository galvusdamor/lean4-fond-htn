import Mathlib

/-!
# Derivation trees of commutative grammars: pumping that preserves the label set

A *commutative grammar* over nonterminals `N` and terminals `T` is a relation
`R : N → Multiset (N ⊕ T) → Prop` (a rule rewrites a nonterminal into a multiset of symbols).
This file develops its derivation trees and the decomposition that the small-solution bound of
unordered HTN planning rests on:

* `HTN.CTree.DT` — trees, `DT.Valid R` — derivation trees of `R`, with their `root`, `size`,
  `height`, `yield` (multiset of terminal leaves) and `labels` (finite set of nonterminals);
* `HTN.CTree.Ctx` — one-hole contexts and `Ctx.plug`;
* `HTN.CTree.IsPump R c B` — a *pump* for `c`: a valid context with root `c` and hole `c`,
  i.e. a derivation `c ⇒* c + Δ`;
* `HTN.CTree.exists_removable` — a tree that is higher than `k·2^k`, `k` a bound on its labels,
  contains a pump whose removal does not change the label set (pigeonhole on the pairs
  *(root, label set)* of nested subtrees);
* `HTN.CTree.decomp` — **every derivation tree is a low base tree plus a list of small pumps
  whose heads occur in the base tree**, with the same root and label set;
* `HTN.CTree.insert_pumps` — conversely pumps whose heads occur in a tree can be inserted.
-/

namespace HTN

namespace CTree

/-- Trees with nonterminal-labelled inner nodes and terminal leaves. -/
inductive DT (N T : Type) where
  | leaf : T → DT N T
  | node : N → List (DT N T) → DT N T

variable {N T : Type}

namespace DT

/-- The symbol at the root. -/
def root : DT N T → N ⊕ T
  | leaf t => Sum.inr t
  | node X _ => Sum.inl X

/-- The number of nodes. -/
def size : DT N T → ℕ
  | leaf _ => 1
  | node _ ts => 1 + (ts.map size).sum

/-- The height (a leaf has height `0`). -/
def height : DT N T → ℕ
  | leaf _ => 0
  | node _ ts => 1 + (ts.map height).foldr max 0

/-- The multiset of terminal leaves. -/
def yield : DT N T → Multiset T
  | leaf t => {t}
  | node _ ts => (ts.map yield).sum

variable [DecidableEq N]

/-- The set of nonterminals occurring in the tree. -/
def labels : DT N T → Finset N
  | leaf _ => ∅
  | node X ts => insert X ((ts.map labels).foldr (· ∪ ·) ∅)

end DT

/-- Derivation trees of a commutative grammar. -/
inductive DT.Valid (R : N → Multiset (N ⊕ T) → Prop) : DT N T → Prop
  | leaf (t : T) : DT.Valid R (DT.leaf t)
  | node (X : N) (ts : List (DT N T)) : R X ↑(ts.map DT.root) → (∀ u ∈ ts, DT.Valid R u) →
      DT.Valid R (DT.node X ts)

/-! ### Basic facts about lists of trees -/

theorem foldr_max_le_iff {α : Type*} (f : α → ℕ) (b : ℕ) :
    ∀ l : List α, (l.map f).foldr max 0 ≤ b ↔ ∀ x ∈ l, f x ≤ b
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    rw [max_le_iff, foldr_max_le_iff f b l]

theorem le_foldr_max {α : Type*} (f : α → ℕ) {l : List α} {x : α} (hx : x ∈ l) :
    f x ≤ (l.map f).foldr max 0 :=
  (foldr_max_le_iff f _ l).1 le_rfl x hx

theorem mem_foldr_union {α : Type*} [DecidableEq N] (f : α → Finset N) (y : N) :
    ∀ l : List α, y ∈ (l.map f).foldr (· ∪ ·) ∅ ↔ ∃ x ∈ l, y ∈ f x
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_cons,
      exists_eq_or_imp]
    rw [mem_foldr_union f y l]

theorem sum_le_length_mul {α : Type*} (f : α → ℕ) (b : ℕ) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ b) → (l.map f).sum ≤ l.length * b
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := sum_le_length_mul f b l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    nlinarith

theorem forall₂_map_eq {α β γ : Type*} {P : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, P a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → l₁.map f = l₂.map g
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h hs => by
    simp only [List.map_cons, hfg _ _ h, forall₂_map_eq hfg hs]

theorem exists_forall₂ {α β : Type*} {P : α → β → Prop} :
    ∀ l : List α, (∀ a ∈ l, ∃ b, P a b) → ∃ l' : List β, List.Forall₂ P l l'
  | [], _ => ⟨[], List.Forall₂.nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨l', hl'⟩ := exists_forall₂ l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: l', List.Forall₂.cons hb hl'⟩

theorem forall₂_mem_right {α β : Type*} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, P a b
  | _, _, List.Forall₂.nil => by simp
  | _, _, List.Forall₂.cons h hs => by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_mem_right hs b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

namespace DT

@[simp] theorem root_leaf (t : T) : (leaf t : DT N T).root = Sum.inr t := rfl
@[simp] theorem root_node (X : N) (ts : List (DT N T)) : (node X ts).root = Sum.inl X := rfl
@[simp] theorem size_leaf (t : T) : (leaf t : DT N T).size = 1 := by simp [size]
@[simp] theorem size_node (X : N) (ts : List (DT N T)) :
    (node X ts).size = 1 + (ts.map size).sum := by simp [size]
@[simp] theorem height_leaf (t : T) : (leaf t : DT N T).height = 0 := by simp [height]
@[simp] theorem height_node (X : N) (ts : List (DT N T)) :
    (node X ts).height = 1 + (ts.map height).foldr max 0 := by simp [height]
@[simp] theorem yield_leaf (t : T) : (leaf t : DT N T).yield = {t} := by simp [yield]
@[simp] theorem yield_node (X : N) (ts : List (DT N T)) :
    (node X ts).yield = (ts.map yield).sum := by simp [yield]

theorem size_pos (t : DT N T) : 0 < t.size := by
  cases t <;> simp

theorem size_lt_of_mem {X : N} {ts : List (DT N T)} {u : DT N T} (hu : u ∈ ts) :
    u.size < (node X ts).size := by
  rw [size_node]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := size) hu)
  omega

theorem height_lt_of_mem {X : N} {ts : List (DT N T)} {u : DT N T} (hu : u ∈ ts) :
    u.height < (node X ts).height := by
  rw [height_node]
  have := le_foldr_max height hu
  omega

variable [DecidableEq N]

@[simp] theorem labels_leaf (t : T) : (leaf t : DT N T).labels = ∅ := by simp [labels]
@[simp] theorem labels_node (X : N) (ts : List (DT N T)) :
    (node X ts).labels = insert X ((ts.map labels).foldr (· ∪ ·) ∅) := by simp [labels]

theorem mem_labels_node {X Y : N} {ts : List (DT N T)} :
    Y ∈ (node X ts).labels ↔ Y = X ∨ ∃ u ∈ ts, Y ∈ u.labels := by
  rw [labels_node, Finset.mem_insert, mem_foldr_union]

theorem labels_subset_of_mem {X : N} {ts : List (DT N T)} {u : DT N T} (hu : u ∈ ts) :
    u.labels ⊆ (node X ts).labels :=
  fun _ hY => mem_labels_node.2 (Or.inr ⟨u, hu, hY⟩)

theorem root_mem_labels {X : N} {ts : List (DT N T)} : X ∈ (node X ts).labels :=
  mem_labels_node.2 (Or.inl rfl)

omit [DecidableEq N] in
theorem Valid.children {R : N → Multiset (N ⊕ T) → Prop} {X : N} {ts : List (DT N T)}
    (h : Valid R (DT.node X ts)) : R X ↑(ts.map root) ∧ ∀ u ∈ ts, Valid R u := by
  cases h with
  | node _ _ hR hch => exact ⟨hR, hch⟩

omit [DecidableEq N] in
/-- **Valid trees of a grammar with bodies of at most `M` symbols are small.** -/
theorem size_le_pow {R : N → Multiset (N ⊕ T) → Prop} {M : ℕ}
    (hM : ∀ X β, R X β → Multiset.card β ≤ M) {t : DT N T} (ht : Valid R t) :
    t.size ≤ (M + 1) ^ (t.height + 1) := by
  induction ht with
  | leaf t => simp
  | node X ts hR _ ih =>
    rw [size_node, height_node]
    set h := (ts.map height).foldr max 0 with hh
    have hlen : ts.length ≤ M := by
      have := hM X _ hR
      simpa using this
    have hch : ∀ u ∈ ts, u.size ≤ (M + 1) ^ (h + 1) := by
      intro u hu
      calc u.size ≤ (M + 1) ^ (u.height + 1) := ih u hu
        _ ≤ (M + 1) ^ (h + 1) :=
            Nat.pow_le_pow_right (by omega) (by have := le_foldr_max height hu; omega)
    have hsum := sum_le_length_mul size _ ts hch
    calc 1 + (ts.map size).sum ≤ 1 + M * (M + 1) ^ (h + 1) := by
          have := Nat.mul_le_mul_right ((M + 1) ^ (h + 1)) hlen
          omega
      _ ≤ (M + 1) ^ (1 + h + 1) := by
          have e : (M + 1) ^ (1 + h + 1) = (M + 1) ^ (h + 1) * (M + 1) := by ring
          rw [e]
          have : 1 ≤ (M + 1) ^ (h + 1) := Nat.one_le_pow _ _ (by omega)
          nlinarith

/-- The labels of a valid tree stay inside a set that is closed under the rules. -/
theorem labels_subset_of_closed {R : N → Multiset (N ⊕ T) → Prop} {K : Finset N}
    (hK : ∀ X β, X ∈ K → R X β → ∀ Y, Sum.inl Y ∈ β → Y ∈ K) {t : DT N T} (ht : Valid R t) :
    ∀ X, t.root = Sum.inl X → X ∈ K → t.labels ⊆ K := by
  induction ht with
  | leaf t => intro X h; simp at h
  | node X ts hR _ ih =>
    intro Y hY hYK
    simp only [root_node, Sum.inl.injEq] at hY
    subst hY
    intro Z hZ
    rcases mem_labels_node.1 hZ with rfl | ⟨u, hu, hZu⟩
    · exact hYK
    · cases hur : u.root with
      | inr t =>
        cases u with
        | leaf t' => simp at hZu
        | node W _ => simp at hur
      | inl W =>
        have hW : W ∈ K := by
          refine hK _ _ hYK hR W ?_
          rw [Multiset.mem_coe]
          exact hur ▸ List.mem_map_of_mem hu
        exact ih u hu W hur hW hZu

end DT

/-! ### Contexts -/

/-- One-hole contexts: a path from the root to the hole, with the siblings on either side. -/
inductive Ctx (N T : Type) where
  | hole : Ctx N T
  | node : N → List (DT N T) → Ctx N T → List (DT N T) → Ctx N T

namespace Ctx

/-- Fill the hole. -/
def plug : Ctx N T → DT N T → DT N T
  | hole, s => s
  | node X l C r, s => DT.node X (l ++ plug C s :: r)

/-- The root symbol of a context whose hole is filled by a tree with root `h`. -/
def rootC : Ctx N T → N ⊕ T → N ⊕ T
  | hole, h => h
  | node X _ _ _, _ => Sum.inl X

/-- The number of nodes outside the hole. -/
def size : Ctx N T → ℕ
  | hole => 0
  | node _ l C r => 1 + (l.map DT.size).sum + C.size + (r.map DT.size).sum

/-- The terminal leaves outside the hole. -/
def yieldC : Ctx N T → Multiset T
  | hole => 0
  | node _ l C r => (l.map DT.yield).sum + C.yieldC + (r.map DT.yield).sum

/-- Composition of contexts. -/
def comp : Ctx N T → Ctx N T → Ctx N T
  | hole, D => D
  | node X l C r, D => node X l (comp C D) r

@[simp] theorem plug_hole (s : DT N T) : plug hole s = s := rfl

theorem plug_comp (C D : Ctx N T) (s : DT N T) : plug (comp C D) s = plug C (plug D s) := by
  induction C with
  | hole => rfl
  | node X l C r ih => simp [comp, plug, ih]

theorem rootC_comp (C D : Ctx N T) (h : N ⊕ T) : (comp C D).rootC h = C.rootC (D.rootC h) := by
  cases C <;> rfl

theorem root_plug (C : Ctx N T) (s : DT N T) : (plug C s).root = C.rootC s.root := by
  cases C <;> rfl

theorem size_plug (C : Ctx N T) (s : DT N T) : (plug C s).size = C.size + s.size := by
  induction C with
  | hole => simp [size]
  | node X l C r ih =>
    simp only [plug, DT.size_node, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, size, ih]
    ring

theorem yield_plug (C : Ctx N T) (s : DT N T) : (plug C s).yield = C.yieldC + s.yield := by
  induction C with
  | hole => simp [yieldC]
  | node X l C r ih =>
    simp only [plug, DT.yield_node, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, yieldC, ih]
    abel

theorem size_pos_of_ne_hole {C : Ctx N T} (h : C ≠ hole) : 0 < C.size := by
  cases C with
  | hole => exact absurd rfl h
  | node => simp only [size]; omega

theorem comp_ne_hole_left {C D : Ctx N T} (h : C ≠ hole) : comp C D ≠ hole := by
  cases C with
  | hole => exact absurd rfl h
  | node => simp [comp]

theorem height_le_plug (C : Ctx N T) (s : DT N T) : s.height ≤ (plug C s).height := by
  induction C with
  | hole => exact le_rfl
  | node X l C r ih =>
    simp only [plug, DT.height_node]
    have := le_foldr_max DT.height (List.mem_append_right l (List.mem_cons_self (a := plug C s)
      (l := r)))
    omega

theorem height_plug_mono (C : Ctx N T) {s s' : DT N T} (h : s.height ≤ s'.height) :
    (plug C s).height ≤ (plug C s').height := by
  induction C with
  | hole => exact h
  | node X l C r ih =>
    simp only [plug, DT.height_node]
    have key : ∀ x ∈ l ++ plug C s :: r,
        x.height ≤ ((l ++ plug C s' :: r).map DT.height).foldr max 0 := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact le_foldr_max DT.height (List.mem_append_left _ hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ih.trans (le_foldr_max DT.height (List.mem_append_right l List.mem_cons_self))
        · exact le_foldr_max DT.height (List.mem_append_right l (List.mem_cons_of_mem _ hx))
    have := (foldr_max_le_iff DT.height _ _).2 key
    omega

variable [DecidableEq N]

/-- The nonterminals outside the hole. -/
def labelsC : Ctx N T → Finset N
  | hole => ∅
  | node X l C r => insert X ((l.map DT.labels).foldr (· ∪ ·) ∅ ∪ C.labelsC ∪
      (r.map DT.labels).foldr (· ∪ ·) ∅)

theorem labels_plug (C : Ctx N T) (s : DT N T) : (plug C s).labels = C.labelsC ∪ s.labels := by
  induction C with
  | hole => simp [labelsC]
  | node X l C r ih =>
    ext Y
    simp only [plug, DT.mem_labels_node, labelsC, Finset.mem_union, Finset.mem_insert,
      mem_foldr_union, List.mem_append, List.mem_cons]
    constructor
    · rintro (h | ⟨u, hu, hY⟩)
      · exact Or.inl (Or.inl h)
      · rcases hu with hu | rfl | hu
        · exact Or.inl (Or.inr (Or.inl (Or.inl ⟨u, hu, hY⟩)))
        · rw [ih, Finset.mem_union] at hY
          rcases hY with hY | hY
          · exact Or.inl (Or.inr (Or.inl (Or.inr hY)))
          · exact Or.inr hY
        · exact Or.inl (Or.inr (Or.inr ⟨u, hu, hY⟩))
    · rintro ((h | (⟨u, hu, hY⟩ | hY) | ⟨u, hu, hY⟩) | hY)
      · exact Or.inl h
      · exact Or.inr ⟨u, Or.inl hu, hY⟩
      · exact Or.inr ⟨plug C s, Or.inr (Or.inl rfl), by rw [ih]; exact Finset.mem_union_left _ hY⟩
      · exact Or.inr ⟨u, Or.inr (Or.inr hu), hY⟩
      · exact Or.inr ⟨plug C s, Or.inr (Or.inl rfl), by rw [ih]; exact Finset.mem_union_right _ hY⟩

end Ctx

/-- Valid contexts: every node outside the hole is the left-hand side of a rule, the hole being
filled by a tree with root `h`. -/
inductive Ctx.Valid (R : N → Multiset (N ⊕ T) → Prop) : Ctx N T → N ⊕ T → Prop
  | hole (h : N ⊕ T) : Ctx.Valid R Ctx.hole h
  | node (X : N) (l : List (DT N T)) (C : Ctx N T) (r : List (DT N T)) (h : N ⊕ T) :
      R X ↑(l.map DT.root ++ C.rootC h :: r.map DT.root) → (∀ u ∈ l, DT.Valid R u) →
      (∀ u ∈ r, DT.Valid R u) → Ctx.Valid R C h → Ctx.Valid R (Ctx.node X l C r) h

namespace Ctx

variable {R : N → Multiset (N ⊕ T) → Prop}

theorem valid_plug {C : Ctx N T} {s : DT N T} :
    DT.Valid R (plug C s) ↔ C.Valid R s.root ∧ DT.Valid R s := by
  induction C with
  | hole => exact ⟨fun h => ⟨Valid.hole _, h⟩, fun h => h.2⟩
  | node X l C r ih =>
    constructor
    · intro h
      obtain ⟨hR, hch⟩ := DT.Valid.children h
      have hC := ih.1 (hch _ (List.mem_append_right l List.mem_cons_self))
      refine ⟨Valid.node X l C r _ ?_ (fun u hu => hch u (List.mem_append_left _ hu))
        (fun u hu => hch u (List.mem_append_right l (List.mem_cons_of_mem _ hu))) hC.1, hC.2⟩
      simpa [root_plug] using hR
    · rintro ⟨hv, hs⟩
      cases hv with
      | node _ _ _ _ _ hR hl hr hC =>
        refine DT.Valid.node X _ ?_ ?_
        · simpa [plug, root_plug] using hR
        · intro u hu
          rcases List.mem_append.1 hu with hu | hu
          · exact hl u hu
          · rcases List.mem_cons.1 hu with rfl | hu
            · exact ih.2 ⟨hC, hs⟩
            · exact hr u hu

theorem valid_comp {C D : Ctx N T} {h : N ⊕ T} (hC : C.Valid R (D.rootC h)) (hD : D.Valid R h) :
    (comp C D).Valid R h := by
  induction C with
  | hole => exact hD
  | node X l C r ih =>
    cases hC with
    | node _ _ _ _ _ hR hl hr hC' =>
      refine Valid.node X l (comp C D) r h ?_ hl hr (ih hC')
      rwa [rootC_comp]

end Ctx

/-! ### Pumps -/

/-- A **pump** for the nonterminal `c`: a valid context with root `c` whose hole is a `c`, i.e. a
derivation `c ⇒* c + Δ` with `Δ = B.yieldC`. -/
def IsPump (R : N → Multiset (N ⊕ T) → Prop) (c : N) (B : Ctx N T) : Prop :=
  B.Valid R (Sum.inl c) ∧ B.rootC (Sum.inl c) = Sum.inl c

variable [DecidableEq N]

/-- A nonterminal occurring in a tree is the root of a subtree. -/
theorem exists_plug_of_mem_labels {c : N} : ∀ (n : ℕ) {t : DT N T}, t.size = n →
    c ∈ t.labels → ∃ (A : Ctx N T) (u : DT N T), t = A.plug u ∧ u.root = Sum.inl c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hn h
    cases t with
    | leaf t => simp at h
    | node X ts =>
      rcases DT.mem_labels_node.1 h with rfl | ⟨u, hu, hcu⟩
      · exact ⟨Ctx.hole, _, rfl, rfl⟩
      · obtain ⟨A, v, rfl, hv⟩ := ih _ (hn ▸ DT.size_lt_of_mem hu) rfl hcu
        obtain ⟨l, r, rfl⟩ := List.append_of_mem hu
        exact ⟨Ctx.node X l A r, v, rfl, hv⟩

variable {R : N → Multiset (N ⊕ T) → Prop}

/-- **Inserting one pump** at an occurrence of its head. -/
theorem insert_pump {t : DT N T} (ht : t.Valid R) {c : N} (hc : c ∈ t.labels) {B : Ctx N T}
    (hB : IsPump R c B) :
    ∃ t' : DT N T, t'.Valid R ∧ t'.root = t.root ∧ t'.yield = t.yield + B.yieldC ∧
      t'.size = t.size + B.size ∧ t.labels ⊆ t'.labels := by
  obtain ⟨A, u, rfl, hu⟩ := exists_plug_of_mem_labels _ rfl hc
  refine ⟨A.plug (B.plug u), ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hA, hu'⟩ := Ctx.valid_plug.1 ht
    refine Ctx.valid_plug.2 ⟨?_, Ctx.valid_plug.2 ⟨hu ▸ hB.1, hu'⟩⟩
    rw [Ctx.root_plug, hu, hB.2]
    rwa [hu] at hA
  · rw [Ctx.root_plug, Ctx.root_plug, Ctx.root_plug, hu, hB.2]
  · rw [Ctx.yield_plug, Ctx.yield_plug, Ctx.yield_plug]
    abel
  · rw [Ctx.size_plug, Ctx.size_plug, Ctx.size_plug]
    ring
  · rw [Ctx.labels_plug, Ctx.labels_plug, Ctx.labels_plug]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)

/-- **Inserting a list of pumps** whose heads occur in the tree. -/
theorem insert_pumps : ∀ (ps : List (N × Ctx N T)) {t : DT N T}, t.Valid R →
    (∀ p ∈ ps, IsPump R p.1 p.2 ∧ p.1 ∈ t.labels) →
    ∃ t' : DT N T, t'.Valid R ∧ t'.root = t.root ∧
      t'.yield = t.yield + (ps.map (fun p => p.2.yieldC)).sum ∧
      t'.size = t.size + (ps.map (fun p => p.2.size)).sum
  | [], t, ht, _ => ⟨t, ht, rfl, by simp, by simp⟩
  | p :: ps, t, ht, hps => by
    obtain ⟨t₁, ht₁, hr₁, hy₁, hs₁, hl₁⟩ := insert_pump ht (hps p (by simp)).2 (hps p (by simp)).1
    obtain ⟨t', ht', hr', hy', hs'⟩ := insert_pumps ps ht₁ (fun q hq =>
      ⟨(hps q (List.mem_cons_of_mem _ hq)).1, hl₁ (hps q (List.mem_cons_of_mem _ hq)).2⟩)
    refine ⟨t', ht', hr'.trans hr₁, ?_, ?_⟩
    · rw [hy', hy₁]
      simp only [List.map_cons, List.sum_cons]
      abel
    · rw [hs', hs₁]
      simp only [List.map_cons, List.sum_cons]
      ring

/-! ### Finding a removable pump -/

omit [DecidableEq N] in
/-- A descending chain of nested subtrees, all of them inner nodes. -/
theorem exists_chain : ∀ (h : ℕ) (t : DT N T), h + 1 ≤ t.height →
    ∃ f : ℕ → Ctx N T × DT N T,
      (∀ j ≤ h, t = (f j).1.plug (f j).2 ∧ ∃ X, (f j).2.root = Sum.inl X) ∧
      ∀ i j, i < j → j ≤ h → ∃ B : Ctx N T, B ≠ Ctx.hole ∧ (f i).2 = B.plug (f j).2
  | 0, t, ht => by
    cases t with
    | leaf => simp at ht
    | node X ts =>
      refine ⟨fun _ => (Ctx.hole, DT.node X ts), ?_, ?_⟩
      · intro j _
        exact ⟨rfl, X, rfl⟩
      · intro i j hij hj
        omega
  | h + 1, t, ht => by
    cases t with
    | leaf => simp at ht
    | node X ts =>
      -- a child of height at least `h + 1`
      have : ∃ u ∈ ts, h + 1 ≤ u.height := by
        by_contra hno
        push_neg at hno
        have := (foldr_max_le_iff DT.height h ts).2 (fun u hu => by have := hno u hu; omega)
        simp only [DT.height_node] at ht
        omega
      obtain ⟨u, hu, hhu⟩ := this
      obtain ⟨l, r, rfl⟩ := List.append_of_mem hu
      obtain ⟨g, hg1, hg2⟩ := exists_chain h u hhu
      let P : Ctx N T := Ctx.node X l Ctx.hole r
      refine ⟨fun j => if j = 0 then (Ctx.hole, DT.node X (l ++ u :: r))
        else (Ctx.comp P (g (j - 1)).1, (g (j - 1)).2), ?_, ?_⟩
      · intro j hj
        by_cases hj0 : j = 0
        · simp only [hj0, if_true]
          exact ⟨rfl, X, rfl⟩
        · simp only [hj0, if_false]
          obtain ⟨hgj, hX⟩ := hg1 (j - 1) (by omega)
          refine ⟨?_, hX⟩
          rw [Ctx.plug_comp, ← hgj]
          rfl
      · intro i j hij hj
        have hj0 : j ≠ 0 := by omega
        by_cases hi0 : i = 0
        · simp only [hi0, if_true, hj0, if_false]
          refine ⟨Ctx.comp P (g (j - 1)).1, Ctx.comp_ne_hole_left (by simp [P]), ?_⟩
          rw [Ctx.plug_comp, ← (hg1 (j - 1) (by omega)).1]
          rfl
        · simp only [hi0, hj0, if_false]
          exact hg2 (i - 1) (j - 1) (by omega) (by omega)

/-- **A high tree contains a pump whose removal keeps the label set.**  If the labels of `t`
lie in `K` and `t` is higher than `|K|·2^|K|`, then `t = A[B[s]]` with `B` a nonempty context,
`B[s]` and `s` having the same root and the same labels. -/
theorem exists_removable (K : Finset N) {t : DT N T} (hK : t.labels ⊆ K)
    (hh : K.card * 2 ^ K.card + 1 ≤ t.height) :
    ∃ (A B : Ctx N T) (s : DT N T), t = A.plug (B.plug s) ∧ B ≠ Ctx.hole ∧
      (∃ c, s.root = Sum.inl c) ∧ B.rootC s.root = s.root ∧ (B.plug s).labels = s.labels := by
  classical
  obtain ⟨f, hf1, hf2⟩ := exists_chain (K.card * 2 ^ K.card) t hh
  -- the key of a subtree: its label set and its root
  let key : ℕ → Finset N × (N ⊕ T) := fun j => ((f j).2.labels, (f j).2.root)
  let target : Finset (Finset N × (N ⊕ T)) := K.powerset ×ˢ K.image (Sum.inl : N → N ⊕ T)
  have hmaps : ∀ j ∈ Finset.range (K.card * 2 ^ K.card + 1), key j ∈ target := by
    intro j hj
    have hj' : j ≤ K.card * 2 ^ K.card := by have := Finset.mem_range.1 hj; omega
    obtain ⟨hplug, X, hX⟩ := hf1 j hj'
    have hsub : (f j).2.labels ⊆ K := by
      intro Y hY
      apply hK
      rw [hplug, Ctx.labels_plug]
      exact Finset.mem_union_right _ hY
    refine Finset.mem_product.2 ⟨Finset.mem_powerset.2 hsub, ?_⟩
    show (f j).2.root ∈ K.image Sum.inl
    rw [hX]
    refine Finset.mem_image_of_mem _ (hsub ?_)
    cases hfj : (f j).2 with
    | leaf => rw [hfj] at hX; simp at hX
    | node Y ts =>
      rw [hfj] at hX
      simp only [DT.root_node, Sum.inl.injEq] at hX
      subst hX
      exact DT.root_mem_labels
  have hcard : target.card < (Finset.range (K.card * 2 ^ K.card + 1)).card := by
    rw [Finset.card_range, Finset.card_product, Finset.card_powerset]
    have := Finset.card_image_le (s := K) (f := (Sum.inl : N → N ⊕ T))
    have : 2 ^ K.card * (K.image (Sum.inl : N → N ⊕ T)).card ≤ K.card * 2 ^ K.card := by
      rw [mul_comm]
      exact Nat.mul_le_mul_right _ this
    omega
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have main : ∀ i j, i < j → j ≤ K.card * 2 ^ K.card → key i = key j →
      ∃ (A B : Ctx N T) (s : DT N T), t = A.plug (B.plug s) ∧ B ≠ Ctx.hole ∧
        (∃ c, s.root = Sum.inl c) ∧ B.rootC s.root = s.root ∧ (B.plug s).labels = s.labels := by
    intro i j hij hj hk
    obtain ⟨B, hB, hBij⟩ := hf2 i j hij hj
    obtain ⟨hplug, -⟩ := hf1 i (by omega)
    obtain ⟨-, X, hX⟩ := hf1 j hj
    simp only [key, Prod.mk.injEq] at hk
    refine ⟨(f i).1, B, (f j).2, by rw [← hBij]; exact hplug, hB, ⟨X, hX⟩, ?_, ?_⟩
    · rw [← Ctx.root_plug, ← hBij]
      exact hk.2
    · rw [← hBij]
      exact hk.1
  rcases lt_or_gt_of_ne hij with h | h
  · exact main i j h (by have := Finset.mem_range.1 hj; omega) heq
  · exact main j i h (by have := Finset.mem_range.1 hi; omega) heq.symm

/-! ### The decomposition -/

/-- **Reduction**: a tree is a tree of height at most `|K|·2^|K|` plus pumps of size at most its
own size, the heads of the pumps among its labels. -/
theorem reduce (K : Finset N) : ∀ (n : ℕ) (t : DT N T), t.size = n → t.Valid R →
    t.labels ⊆ K →
    ∃ (t₀ : DT N T) (ps : List (N × Ctx N T)), t₀.Valid R ∧ t₀.root = t.root ∧
      t₀.labels = t.labels ∧ t₀.height ≤ K.card * 2 ^ K.card ∧ t₀.height ≤ t.height ∧
      (∀ p ∈ ps, IsPump R p.1 p.2 ∧ p.1 ∈ t.labels ∧ p.2.size ≤ t.size) ∧
      t.yield = t₀.yield + (ps.map (fun p => p.2.yieldC)).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hn ht hK
    by_cases hh : t.height ≤ K.card * 2 ^ K.card
    · exact ⟨t, [], ht, rfl, rfl, hh, le_rfl, by simp, by simp⟩
    push_neg at hh
    obtain ⟨A, B, s, rfl, hB, ⟨c, hc⟩, hroot, hlab⟩ := exists_removable K hK hh
    obtain ⟨hA, hBs⟩ := Ctx.valid_plug.1 ht
    obtain ⟨hBv, hs⟩ := Ctx.valid_plug.1 hBs
    have hAs : (A.plug s).Valid R := by
      refine Ctx.valid_plug.2 ⟨?_, hs⟩
      rw [Ctx.root_plug, hroot] at hA
      exact hA
    have hlabs : (A.plug s).labels = (A.plug (B.plug s)).labels := by
      rw [Ctx.labels_plug, Ctx.labels_plug, hlab]
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

theorem sum_flatMap_map {α β γ : Type*} [AddCommMonoid γ] (g : α → List β) (h : β → γ) :
    ∀ vs : List α, ((vs.flatMap g).map h).sum = (vs.map (fun v => ((g v).map h).sum)).sum
  | [] => by simp
  | v :: vs => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_flatMap_map g h vs]

/-- **The decomposition theorem.**  Let the labels of a derivation tree `t` lie in `K` and let
every rule body have at most `M` symbols.  Then `t` is a tree `t₀` of height at most
`|K|·2^|K|`, with the same root and the same labels, plus a list of pumps, each of size at most
`(M+1)^(|K|·2^|K| + 2)` and with its head among the labels of `t₀`. -/
theorem decomp (K : Finset N) {M : ℕ} (hM : ∀ X β, R X β → Multiset.card β ≤ M) :
    ∀ (n : ℕ) (t : DT N T), t.size = n → t.Valid R → t.labels ⊆ K →
    ∃ (t₀ : DT N T) (ps : List (N × Ctx N T)), t₀.Valid R ∧ t₀.root = t.root ∧
      t₀.labels = t.labels ∧ t₀.height ≤ K.card * 2 ^ K.card ∧
      (∀ p ∈ ps, IsPump R p.1 p.2 ∧ p.1 ∈ t₀.labels ∧
        p.2.size ≤ (M + 1) ^ (K.card * 2 ^ K.card + 2)) ∧
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
        v.1.height ≤ K.card * 2 ^ K.card ∧
        (∀ p ∈ v.2, IsPump R p.1 p.2 ∧ p.1 ∈ v.1.labels ∧
          p.2.size ≤ (M + 1) ^ (K.card * 2 ^ K.card + 2)) ∧
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
      have hh₁ : t₁.height ≤ K.card * 2 ^ K.card + 1 := by
        simp only [t₁, DT.height_node]
        have : ((vs.map Prod.fst).map DT.height).foldr max 0 ≤ K.card * 2 ^ K.card := by
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
        reduce K t₁.size t₁ rfl ht₁ (hl₁ ▸ hK)
      have hsize₁ : t₁.size ≤ (M + 1) ^ (K.card * 2 ^ K.card + 2) :=
        (DT.size_le_pow hM ht₁).trans (Nat.pow_le_pow_right (by omega) (by omega))
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

/-! ### Further facts used by the bound -/

theorem card_list_sum : ∀ l : List (Multiset T),
    Multiset.card l.sum = (l.map Multiset.card).sum
  | [] => by simp
  | x :: l => by simp [card_list_sum l]

theorem mem_list_sum {x : T} : ∀ l : List (Multiset T), x ∈ l.sum ↔ ∃ m ∈ l, x ∈ m
  | [] => by simp
  | y :: l => by
    simp only [List.sum_cons, Multiset.mem_add, List.mem_cons, exists_eq_or_imp]
    rw [mem_list_sum l]

omit [DecidableEq N] in
theorem sum_map_card_yield_le (l : List (DT N T)) (h : ∀ u ∈ l, Multiset.card u.yield ≤ u.size) :
    Multiset.card (l.map DT.yield).sum ≤ (l.map DT.size).sum := by
  rw [card_list_sum, List.map_map]
  exact List.sum_le_sum (fun u hu => h u hu)

omit [DecidableEq N] in
theorem DT.card_yield_le : ∀ (n : ℕ) (t : DT N T), t.size = n →
    Multiset.card t.yield ≤ t.size := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hn
    cases t with
    | leaf t => simp
    | node X ts =>
      simp only [DT.yield_node, DT.size_node]
      have := sum_map_card_yield_le ts (fun u hu => ih _ (hn ▸ DT.size_lt_of_mem hu) u rfl)
      omega

omit [DecidableEq N] in
theorem Ctx.card_yieldC_le (C : Ctx N T) : Multiset.card C.yieldC ≤ C.size := by
  induction C with
  | hole => simp [Ctx.yieldC, Ctx.size]
  | node X l C r ih =>
    simp only [Ctx.yieldC, Ctx.size, Multiset.card_add]
    have hl := sum_map_card_yield_le l (fun u _ => DT.card_yield_le _ u rfl)
    have hr := sum_map_card_yield_le r (fun u _ => DT.card_yield_le _ u rfl)
    omega

omit [DecidableEq N] in
/-- The terminals of a valid tree are among those the rules can produce. -/
theorem DT.yield_mem_of_rules {Q : T → Prop} (hQ : ∀ X β, R X β → ∀ x, Sum.inr x ∈ β → Q x)
    {t : DT N T} (ht : t.Valid R) (hroot : ∀ x, t.root = Sum.inr x → Q x) :
    ∀ x ∈ t.yield, Q x := by
  induction ht with
  | leaf a =>
    intro x hx
    simp only [DT.yield_leaf, Multiset.mem_singleton] at hx
    exact hroot x (by simp [hx])
  | node X ts hR _ ih =>
    intro x hx
    simp only [DT.yield_node] at hx
    obtain ⟨y, hy, hxy⟩ := (mem_list_sum _).1 hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
    refine ih u hu (fun z hz => hQ X _ hR z ?_) x hxy
    rw [Multiset.mem_coe, ← hz]
    exact List.mem_map_of_mem hu

omit [DecidableEq N] in
/-- The terminals of a valid context are among those the rules can produce. -/
theorem Ctx.yieldC_mem_of_rules {Q : T → Prop} (hQ : ∀ X β, R X β → ∀ x, Sum.inr x ∈ β → Q x)
    {C : Ctx N T} {h : N ⊕ T} (hC : C.Valid R h) : ∀ x ∈ C.yieldC, Q x := by
  induction hC with
  | hole => simp [Ctx.yieldC]
  | node X l C r h hR hl hr _ ih =>
    intro x hx
    simp only [Ctx.yieldC, Multiset.mem_add] at hx
    have hsib : ∀ u, u ∈ l ∨ u ∈ r → ∀ x ∈ u.yield, Q x := by
      intro u hu
      refine DT.yield_mem_of_rules hQ (hu.elim (hl u) (hr u)) (fun z hz => hQ X _ hR z ?_)
      rw [Multiset.mem_coe, ← hz]
      rcases hu with hu | hu
      · exact List.mem_append_left _ (List.mem_map_of_mem hu)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hu))
    rcases hx with (hx | hx) | hx
    · obtain ⟨y, hy, hxy⟩ := (mem_list_sum _).1 hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
      exact hsib u (Or.inl hu) x hxy
    · exact ih x hx
    · obtain ⟨y, hy, hxy⟩ := (mem_list_sum _).1 hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
      exact hsib u (Or.inr hu) x hxy

/-- Splitting a list along a decomposition of the multiset of its images. -/
theorem exists_split {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ (L : List α) (A B : Multiset β), (↑(L.map f) : Multiset β) = A + B →
      ∃ L₁ L₂ : List α, L.Perm (L₁ ++ L₂) ∧ (↑(L₁.map f) : Multiset β) = A ∧
        (↑(L₂.map f) : Multiset β) = B
  | [], A, B, h => by
    have h' : A + B = 0 := by simpa using h.symm
    rw [add_eq_zero] at h'
    exact ⟨[], [], by simp, by simp [h'.1], by simp [h'.2]⟩
  | x :: L, A, B, h => by
    have hx : f x ∈ A + B := by rw [← h]; simp
    rcases Multiset.mem_add.1 hx with hA | hB
    · have h' : (↑(L.map f) : Multiset β) = A.erase (f x) + B := by
        rw [← Multiset.erase_add_left_pos B hA, ← h]
        simp
      obtain ⟨L₁, L₂, hp, h₁, h₂⟩ := exists_split f L _ _ h'
      refine ⟨x :: L₁, L₂, hp.cons x, ?_, h₂⟩
      rw [List.map_cons, ← Multiset.cons_coe, h₁, Multiset.cons_erase hA]
    · have h' : (↑(L.map f) : Multiset β) = A + B.erase (f x) := by
        rw [← Multiset.erase_add_right_pos A hB, ← h]
        simp
      obtain ⟨L₁, L₂, hp, h₁, h₂⟩ := exists_split f L _ _ h'
      refine ⟨L₁, x :: L₂, (hp.cons x).trans List.perm_middle.symm, h₁, ?_⟩
      rw [List.map_cons, ← Multiset.cons_coe, h₂, Multiset.cons_erase hB]

end CTree

end HTN
