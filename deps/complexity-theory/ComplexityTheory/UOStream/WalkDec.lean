import Mathlib

/-!
# Walks in a finite graph: a short skeleton plus short cycles

A labelled graph is a relation `R : α → β → α → Prop` (`R s b u`: an edge from `s` to `u` with
label `b`).  A walk is a list of steps `(label, target)`.

* `HTN.UOStream.walk_decomp` — every walk from `s` to `t` inside a closed set of `N` nodes is a walk
  `skel` from `s` to `t` of length at most `(N + 1) · N` that visits every node of the original
  walk, together with closed walks of length at most `N`, each starting at a node of `skel`; the
  label multiset of the original walk is that of `skel` plus those of the closed walks.
* `HTN.UOStream.walk_insert` — conversely, closed walks at nodes of a walk can be inserted any
  number of times.

The cycle that is cut out is found as follows (`extract`): walk along, keeping the set `S` of
nodes already seen.  If the next `N` steps all go to seen nodes, two of the `N + 1` nodes are equal
and the closed walk between them only visits seen nodes, so cutting it out keeps the set of visited
nodes.  Otherwise a new node is reached within `N` steps; this can happen at most `N` times.
-/

namespace HTN

namespace UOStream

variable {α β : Type} (R : α → β → α → Prop)

/-- Walks: lists of steps `(label, target)`. -/
inductive IsWalk : α → List (β × α) → α → Prop
  | nil (s : α) : IsWalk s [] s
  | cons {s u t : α} {b : β} {w : List (β × α)} : R s b u → IsWalk u w t →
      IsWalk s ((b, u) :: w) t

/-- The nodes visited by a walk from `s`. -/
def nodesOf (s : α) (w : List (β × α)) : List α := s :: w.map Prod.snd

/-- The label multiset of a walk. -/
def par (w : List (β × α)) : Multiset β := (w.map Prod.fst : Multiset β)

variable {R}

theorem isWalk_append {s t : α} {w₁ w₂ : List (β × α)} :
    IsWalk R s (w₁ ++ w₂) t ↔ ∃ m, IsWalk R s w₁ m ∧ IsWalk R m w₂ t := by
  induction w₁ generalizing s with
  | nil =>
    constructor
    · exact fun h => ⟨s, .nil s, h⟩
    · rintro ⟨m, hm, h⟩; cases hm; exact h
  | cons p w₁ ih =>
    obtain ⟨b, u⟩ := p
    constructor
    · intro h
      cases h with
      | cons hR hw =>
        obtain ⟨m, h1, h2⟩ := ih.1 hw
        exact ⟨m, .cons hR h1, h2⟩
    · rintro ⟨m, h1, h2⟩
      cases h1 with
      | cons hR hw => exact .cons hR (ih.2 ⟨m, hw, h2⟩)

theorem par_append (w₁ w₂ : List (β × α)) : par (w₁ ++ w₂) = par w₁ + par w₂ := by
  simp [par]

theorem nodesOf_getD_zero (s : α) (w : List (β × α)) : (nodesOf s w).getD 0 s = s := rfl

theorem getD_default_irrel {γ : Type} (l : List γ) {p : ℕ} (hp : p < l.length) (d d' : γ) :
    l.getD p d = l.getD p d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]

/-- Splitting a walk at position `p`. -/
theorem isWalk_split {s t : α} {w : List (β × α)} (h : IsWalk R s w t) :
    ∀ p ≤ w.length, IsWalk R s (w.take p) ((nodesOf s w).getD p s) ∧
      IsWalk R ((nodesOf s w).getD p s) (w.drop p) t := by
  induction h with
  | nil s => intro p hp; simp at hp; subst hp; exact ⟨.nil s, .nil s⟩
  | @cons s u t b w hR hw ih =>
    intro p hp
    cases p with
    | zero => exact ⟨.nil s, .cons hR hw⟩
    | succ p =>
      have hp' : p ≤ w.length := by simpa using hp
      obtain ⟨h1, h2⟩ := ih p hp'
      have e : (nodesOf s ((b, u) :: w)).getD (p + 1) s = (nodesOf u w).getD p u := by
        simp only [nodesOf, List.map_cons, List.getD_cons_succ]
        exact getD_default_irrel _ (by simp; omega) _ _
      rw [e]
      exact ⟨.cons hR h1, h2⟩

/-- A node of a walk splits it. -/
theorem split_at_node {s t u : α} {w : List (β × α)} (h : IsWalk R s w t)
    (hu : u ∈ nodesOf s w) : ∃ w₁ w₂, w = w₁ ++ w₂ ∧ IsWalk R s w₁ u ∧ IsWalk R u w₂ t := by
  induction h with
  | nil s =>
    simp only [nodesOf, List.map_nil, List.mem_singleton] at hu
    subst hu; exact ⟨[], [], rfl, .nil _, .nil _⟩
  | @cons s v t b w hR hw ih =>
    simp only [nodesOf, List.map_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨[], _, rfl, .nil _, .cons hR hw⟩
    · obtain ⟨w₁, w₂, rfl, h1, h2⟩ := ih (by simp only [nodesOf, List.mem_cons]; exact hu)
      exact ⟨(b, v) :: w₁, w₂, rfl, .cons hR h1, h2⟩

/-- A closed walk repeated `k` times. -/
def rep (c : List (β × α)) (k : ℕ) : List (β × α) := (List.replicate k c).flatten

theorem isWalk_rep {v : α} {c : List (β × α)} (h : IsWalk R v c v) : ∀ k, IsWalk R v (rep c k) v
  | 0 => .nil v
  | k + 1 => by
    rw [rep, List.replicate_succ, List.flatten_cons]
    exact isWalk_append.2 ⟨v, h, isWalk_rep h k⟩

theorem par_rep (c : List (β × α)) : ∀ k, par (rep c k) = k • par c
  | 0 => by simp [rep, par]
  | k + 1 => by
    rw [rep, List.replicate_succ, List.flatten_cons, par_append, ← rep, par_rep c k, succ_nsmul,
      add_comm]

/-- **Inserting closed walks.** -/
theorem walk_insert {s t : α} :
    ∀ (cs : List (α × List (β × α) × ℕ)) {skel : List (β × α)}, IsWalk R s skel t →
      (∀ p ∈ cs, IsWalk R p.1 p.2.1 p.1 ∧ p.1 ∈ nodesOf s skel) →
      ∃ w, IsWalk R s w t ∧ (∀ u ∈ nodesOf s skel, u ∈ nodesOf s w) ∧
        par w = par skel + (cs.map fun p => p.2.2 • par p.2.1).sum := by
  intro cs
  induction cs with
  | nil => intro skel h _; exact ⟨skel, h, fun _ h => h, by simp⟩
  | cons p cs ih =>
    intro skel h hcs
    obtain ⟨v, c, k⟩ := p
    obtain ⟨hc, hv⟩ := hcs _ (List.mem_cons_self ..)
    obtain ⟨w₁, w₂, rfl, h1, h2⟩ := split_at_node h hv
    have hw : IsWalk R s (w₁ ++ rep c k ++ w₂) t :=
      isWalk_append.2 ⟨v, isWalk_append.2 ⟨v, h1, isWalk_rep hc k⟩, h2⟩
    have hsub : ∀ u ∈ nodesOf s (w₁ ++ w₂), u ∈ nodesOf s (w₁ ++ rep c k ++ w₂) := by
      intro u hu
      simp only [nodesOf, List.map_append, List.mem_cons, List.mem_append] at hu ⊢
      tauto
    obtain ⟨w, hw', hsub', hpar⟩ := ih hw fun q hq => by
      obtain ⟨h1, h2⟩ := hcs q (List.mem_cons_of_mem _ hq)
      exact ⟨h1, hsub _ h2⟩
    refine ⟨w, hw', fun u hu => hsub' u (hsub u hu), ?_⟩
    rw [hpar, par_append, par_append, par_append, par_rep, List.map_cons, List.sum_cons]
    abel

/-! ### Cutting out cycles -/

/-- The first step leaving a set. -/
theorem exists_first_not {γ : Type} (P : γ → Prop) :
    ∀ (l : List γ), (∃ y ∈ l, ¬ P y) → ∃ l₁ y l₂, l = l₁ ++ y :: l₂ ∧ ¬ P y ∧ ∀ z ∈ l₁, P z
  | [], ⟨_, h, _⟩ => absurd h (List.not_mem_nil)
  | y :: l, ⟨z, hz, hnz⟩ => by
    by_cases hy : P y
    · have : ∃ y ∈ l, ¬ P y := by
        rcases List.mem_cons.1 hz with rfl | hz
        · exact absurd hy hnz
        · exact ⟨z, hz, hnz⟩
      obtain ⟨l₁, y', l₂, rfl, h1, h2⟩ := exists_first_not P l this
      refine ⟨y :: l₁, y', l₂, rfl, h1, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact h2 z hz
    · exact ⟨[], y, l, rfl, hy, by simp⟩

variable [DecidableEq α] {V : Finset α}

/-- Walks from a node of a closed set stay in it. -/
theorem nodes_mem (hV : ∀ s b u, R s b u → s ∈ V → u ∈ V) {s t : α} {w : List (β × α)}
    (h : IsWalk R s w t) (hs : s ∈ V) : ∀ u ∈ nodesOf s w, u ∈ V := by
  induction h with
  | nil s => intro u hu; simp [nodesOf] at hu; exact hu ▸ hs
  | @cons s v t b w hR hw ih =>
    intro u hu
    simp only [nodesOf, List.map_cons, List.mem_cons] at hu
    rcases hu with rfl | rfl | hu
    · exact hs
    · exact hV _ _ _ hR hs
    · exact ih (hV _ _ _ hR hs) u (List.mem_cons_of_mem _ hu)

/-- **Cutting out a cycle that only visits seen nodes.** -/
theorem extract (hV : ∀ s b u, R s b u → s ∈ V → u ∈ V) :
    ∀ (n : ℕ) (S : Finset α) (v t : α) (w : List (β × α)), S ⊆ V →
    V.card + 1 - S.card = n → IsWalk R v w t → v ∈ S →
      (V.card + 1) * n < w.length →
      ∃ w₁ c w₂ x, w = w₁ ++ c ++ w₂ ∧ IsWalk R v w₁ x ∧ IsWalk R x c x ∧ IsWalk R x w₂ t ∧
        c ≠ [] ∧ c.length ≤ V.card ∧
        ∀ u ∈ c.map Prod.snd, u ∈ S ∨ u ∈ w₁.map Prod.snd := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S v t w hSV hn hw hv hlen
    set N := V.card
    have hSN : S.card ≤ N := Finset.card_le_card hSV
    have hnodes := nodes_mem hV hw (hSV hv)
    by_cases hall : ∀ y ∈ w.take N, y.2 ∈ S
    · -- two of the first `N + 1` nodes coincide
      have hwN : N < w.length := by
        have : 1 ≤ n := by omega
        nlinarith
      let f : Fin (N + 1) → α := fun i => (nodesOf v w).getD i v
      have hfV : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))), f i ∈ V := by
        intro i _
        simp only [f]
        by_cases hi : (i : ℕ) < (nodesOf v w).length
        · rw [List.getD_eq_getElem _ _ hi]; exact hnodes _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (not_lt.1 hi)]; exact hSV hv
      obtain ⟨i, -, j, -, hij, hfij⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.univ) (t := V) (f := f)
          (by simp [N]) (fun i _ => hfV i (Finset.mem_univ _))
      wlog hlt : i < j generalizing i j
      · exact this j i hij.symm hfij.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
      set p : ℕ := (i : ℕ)
      set q : ℕ := (j : ℕ)
      have hpq : p < q := hlt
      have hqN : q ≤ N := Nat.lt_succ_iff.1 j.2
      have hqw : q ≤ w.length := by omega
      obtain ⟨h1, h2⟩ := isWalk_split hw p (by omega)
      obtain ⟨h3, h4⟩ := isWalk_split hw q hqw
      set x := (nodesOf v w).getD p v
      have hxq : (nodesOf v w).getD q v = x := hfij.symm
      rw [hxq] at h3 h4
      -- the middle part
      have hmid : w.drop p = (w.drop p).take (q - p) ++ w.drop q := by
        conv_lhs => rw [← List.take_append_drop (q - p) (w.drop p)]
        rw [List.drop_drop]; congr 2; omega
      rw [hmid] at h2
      obtain ⟨y, hc, hrest⟩ := isWalk_append.1 h2
      -- `y = x` by the walk to position `q`
      have htq : w.take q = w.take p ++ (w.drop p).take (q - p) := by
        rw [List.take_drop, show p + (q - p) = q by omega]
        conv_lhs => rw [← List.take_append_drop p (w.take q)]
        rw [List.take_take, min_eq_left hpq.le]
      have hyx : y = x := by
        rw [htq] at h3
        obtain ⟨m, hm1, hm2⟩ := isWalk_append.1 h3
        have : m = x := by
          have := isWalk_split hw p (by omega)
          exact walk_target_unique hm1 h1
        subst this
        exact walk_target_unique hc hm2
      subst hyx
      refine ⟨w.take p, (w.drop p).take (q - p), w.drop q, x, ?_, h1, hc, h4, ?_, ?_, ?_⟩
      · rw [List.append_assoc, ← hmid, List.take_append_drop]
      · intro h
        have : ((w.drop p).take (q - p)).length = q - p := by
          rw [List.length_take, List.length_drop]; omega
        rw [h] at this; simp at this; omega
      · rw [List.length_take]; omega
      · intro u hu
        left
        have hmem : u ∈ (w.take N).map Prod.snd := by
          have hsub : List.Sublist ((w.drop p).take (q - p)) (w.take N) := by
            rw [List.take_drop, show p + (q - p) = q by omega]
            exact (List.drop_sublist _ _).trans (List.take_sublist_take_left hqN)
          exact (hsub.map Prod.snd).subset hu
        obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hmem
        exact hall y' hy'
    · -- a new node is reached within `N` steps
      push_neg at hall
      obtain ⟨y₀, hy₀, hy₀S⟩ := hall
      obtain ⟨pre, ⟨b, u⟩, rest, hsplit, huS, hpre⟩ :=
        exists_first_not (fun y : β × α => y.2 ∈ S) w ⟨y₀, List.mem_of_mem_take hy₀, hy₀S⟩
      have hpreN : pre.length < N := by
        by_contra hge
        push_neg at hge
        apply hy₀S
        have : List.Sublist (w.take N) pre := by
          rw [hsplit, List.take_append_of_le_length hge]; exact List.take_sublist _ _
        exact hpre y₀ (this.subset hy₀)
      have huV : u ∈ V := hnodes u (by
        rw [hsplit]; simp [nodesOf])
      have hSlt : S.card < N := by
        have : S ⊆ V.erase u := fun z hz => Finset.mem_erase.2
          ⟨fun h => huS (h ▸ hz), hSV hz⟩
        have := Finset.card_le_card this
        rw [Finset.card_erase_of_mem huV] at this
        omega
      rw [hsplit] at hw
      obtain ⟨m, hwpre, hwrest⟩ := isWalk_append.1 hw
      cases hwrest with
      | cons hR hrest =>
        have hlen' : (N + 1) * (n - 1) < rest.length := by
          have : w.length = pre.length + 1 + rest.length := by
            rw [hsplit]; simp; omega
          have hn2 : 1 ≤ n := by omega
          have : (N + 1) * n = (N + 1) * (n - 1) + (N + 1) := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega
        obtain ⟨w₁, c, w₂, x, hrest_eq, h1, h2, h3, h4, h5, h6⟩ :=
          ih (n - 1) (by omega) (insert u S) u t rest (Finset.insert_subset huV hSV)
            (by rw [Finset.card_insert_of_notMem huS]; omega) hrest
            (Finset.mem_insert_self _ _) hlen'
        refine ⟨pre ++ (b, u) :: w₁, c, w₂, x, ?_, ?_, h2, h3, h4, h5, ?_⟩
        · rw [hsplit, hrest_eq]; simp
        · exact isWalk_append.2 ⟨m, hwpre, .cons hR h1⟩
        · intro z hz
          rcases h6 z hz with hz' | hz'
          · rcases Finset.mem_insert.1 hz' with rfl | hz'
            · right; simp
            · left; exact hz'
          · right; simp [hz']
where
  walk_target_unique {s t t' : α} {w : List (β × α)} (h : IsWalk R s w t)
      (h' : IsWalk R s w t') : t = t' := by
    induction h generalizing t' with
    | nil => cases h'; rfl
    | cons _ _ ih => cases h' with | cons _ h'' => exact ih h''

/-- **A walk is a short skeleton plus short cycles at its nodes.** -/
theorem walk_decomp (hV : ∀ s b u, R s b u → s ∈ V → u ∈ V) {s t : α} (hs : s ∈ V) :
    ∀ (L : ℕ) (w : List (β × α)), w.length = L → IsWalk R s w t →
      ∃ skel, IsWalk R s skel t ∧ skel.length ≤ (V.card + 1) * V.card ∧
        (∀ u ∈ nodesOf s w, u ∈ nodesOf s skel) ∧
        ∃ cs : List (α × List (β × α)),
          (∀ p ∈ cs, IsWalk R p.1 p.2 p.1 ∧ p.2.length ≤ V.card ∧ p.1 ∈ nodesOf s skel) ∧
          par w = par skel + (cs.map fun p => par p.2).sum := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro w hL hw
    by_cases hshort : w.length ≤ (V.card + 1) * V.card
    · exact ⟨w, hw, hshort, fun _ h => h, [], by simp, by simp⟩
    · push_neg at hshort
      have hcard : ({s} : Finset α).card = 1 := Finset.card_singleton s
      obtain ⟨w₁, c, w₂, x, rfl, h1, h2, h3, h4, h5, h6⟩ :=
        extract hV V.card {s} s t w (Finset.singleton_subset_iff.2 hs) (by rw [hcard]; omega) hw
          (Finset.mem_singleton_self s) hshort
      have hw' : IsWalk R s (w₁ ++ w₂) t := isWalk_append.2 ⟨x, h1, h3⟩
      have hlt : (w₁ ++ w₂).length < L := by
        rw [← hL]; simp only [List.length_append]
        have : 0 < c.length := List.length_pos_iff.2 h4
        omega
      obtain ⟨skel, hsk, hsklen, hsknodes, cs, hcs, hpar⟩ := ih _ hlt _ rfl hw'
      have hnodes : ∀ u ∈ nodesOf s (w₁ ++ c ++ w₂), u ∈ nodesOf s (w₁ ++ w₂) := by
        intro u hu
        simp only [nodesOf, List.map_append, List.mem_cons, List.mem_append] at hu ⊢
        rcases hu with hu | (hu | hu) | hu
        · exact Or.inl hu
        · exact Or.inr (Or.inl hu)
        · rcases h6 u hu with hu' | hu'
          · exact Or.inl (Finset.mem_singleton.1 hu')
          · exact Or.inr (Or.inl hu')
        · exact Or.inr (Or.inr hu)
      have hx : x ∈ nodesOf s (w₁ ++ w₂) := by
        obtain ⟨w₁', w₂', _, _, _⟩ := (⟨w₁, w₂, rfl, h1, h3⟩ :
          ∃ a b, w₁ ++ w₂ = a ++ b ∧ IsWalk R s a x ∧ IsWalk R x b t)
        -- `x` is the end of `w₁`
        cases w₁ with
        | nil => cases h1; simp [nodesOf]
        | cons p w₁ =>
          have : x ∈ (p :: w₁).map Prod.snd := last_mem_of_walk h1
          simp only [nodesOf, List.map_append, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl this)
      refine ⟨skel, hsk, hsklen, fun u hu => hsknodes u (hnodes u hu),
        (x, c) :: cs, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨h2, h5, hsknodes x hx⟩
        · exact hcs p hp
      · rw [par_append, par_append, List.map_cons, List.sum_cons]
        rw [par_append] at hpar
        rw [show par w₁ + par c + par w₂ = (par w₁ + par w₂) + par c by abel, hpar]
        abel
where
  last_mem_of_walk {s x : α} {p : β × α} {w : List (β × α)} (h : IsWalk R s (p :: w) x) :
      x ∈ (p :: w).map Prod.snd := by
    induction w generalizing s p with
    | nil => cases h with | cons _ h' => cases h'; simp
    | cons p' w ih =>
      cases h with
      | cons _ h' =>
        have := ih h'
        simp only [List.map_cons, List.mem_cons] at this ⊢
        exact Or.inr this

end UOStream

end HTN
