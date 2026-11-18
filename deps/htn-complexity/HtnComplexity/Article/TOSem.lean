import HtnComplexity.Article.MostlyAcycPT
import HtnPlanning.Computable.Linearise
/-!
# Totally ordered problems: refinement along the linearisation

The algorithm of Thm. 4.2.1 tabulates, for task names `n` and states `s, s'`, whether `n` has a
primitive refinement executable from `s` and ending in `s'` (`HTN.Article.RefT`, through
decomposition trees).  In a totally ordered network the ordered merge of the yields of its tasks
is their concatenation along the (unique) linearisation (`HTN.Article.ordMerge_lin_iff`), so:

* `HTN.Article.refT_inl_iff` — a primitive task refines by its action;
* `HTN.Article.refT_of_chain` / `HTN.Article.chain_of_refT` — a compound task refines iff some
  method of it has its tasks, in the order of `HTN.Syn.TnDesc.lin`, refining one after the other
  (`HTN.Article.ChainT`) — the second direction for methods with a totally ordered network;
* **`HTN.Article.solvable_iff_chain`** — a well-formed totally ordered description is solvable iff
  the tasks of `tn_I` refine one after the other from `s_I` into a goal state.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-! ### Ordered merges in totally ordered networks -/

theorem eq_filter_append_filter {β : Type} (P : β → Bool) :
    ∀ w : List β, w.Pairwise (fun x y => P y = true → P x = true) →
      w = w.filter P ++ w.filter (fun x => !P x)
  | [], _ => rfl
  | a :: w, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : P a = true
    · simp only [List.filter_cons, ha, if_true, Bool.not_true, Bool.false_eq_true, if_false,
        List.cons_append]
      exact congrArg _ (eq_filter_append_filter P w h.2)
    · have hall : ∀ y ∈ w, P y = false := fun y hy => by
        by_contra hy'
        exact ha (h.1 y hy (by simpa using hy'))
      have h1 : w.filter P = [] := List.filter_eq_nil_iff.2 fun y hy => by simp [hall y hy]
      have h2 : w.filter (fun x => !P x) = w := List.filter_eq_self.2 fun y hy => by simp [hall y hy]
      simp only [List.filter_cons, ha, Bool.false_eq_true, if_false, Bool.not_false, if_true, h1, h2,
        List.nil_append]

/-- **A list sorted by the position of its keys in `l` is grouped along `l`.** -/
theorem eq_flatMap_filter {β : Type} : ∀ (l : List ℕ) (w : List (ℕ × β)), l.Nodup →
    (∀ e ∈ w, e.1 ∈ l) → w.Pairwise (fun x y => l.idxOf x.1 ≤ l.idxOf y.1) →
      w = l.flatMap fun t => w.filter fun e => decide (e.1 = t)
  | [], w, _, hk, _ => by
    cases w with
    | nil => rfl
    | cons e w => exact absurd (hk e (by simp)) (by simp)
  | t :: l, w, hnd, hk, hp => by
    rw [List.nodup_cons] at hnd
    have hidx : ∀ k ∈ l, (t :: l).idxOf k = l.idxOf k + 1 := fun k hk' =>
      List.idxOf_cons_ne _ (fun e => hnd.1 (e ▸ hk'))
    have hsplit := eq_filter_append_filter (fun e : ℕ × β => decide (e.1 = t)) w
      (hp.imp_of_mem fun {x y} hx _ hxy hy => by
        simp only [decide_eq_true_eq] at hy ⊢
        rw [hy, List.idxOf_cons_self] at hxy
        rcases List.mem_cons.1 (hk x hx) with h | h
        · exact h
        · rw [hidx _ h] at hxy; omega)
    set B := w.filter fun e => !decide (e.1 = t) with hBdef
    have hBk : ∀ e ∈ B, e.1 ∈ l := fun e he => by
      obtain ⟨he, hne⟩ := List.mem_filter.1 he
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hne
      exact (List.mem_cons.1 (hk e he)).resolve_left hne
    have hBp : B.Pairwise (fun x y => l.idxOf x.1 ≤ l.idxOf y.1) :=
      (hp.sublist List.filter_sublist).imp_of_mem fun {x y} hx hy hxy => by
        rw [hidx _ (hBk x hx), hidx _ (hBk y hy)] at hxy; omega
    have hB := eq_flatMap_filter l B hnd.2 hBk hBp
    rw [List.flatMap_cons]
    refine hsplit.trans (congrArg _ (hB.trans (List.flatMap_congr fun u hu => ?_)))
    rw [hBdef, List.filter_filter]
    refine List.filter_congr fun e _ => ?_
    have hut : u ≠ t := fun e' => hnd.1 (e' ▸ hu)
    by_cases heu : e.1 = u
    · simp [heu, hut]
    · simp [heu]

theorem flatMap_ite_eq {β : Type} (f : ℕ → List β) {t : ℕ} :
    ∀ {l : List ℕ}, l.Nodup → t ∈ l → (l.flatMap fun u => if u = t then f u else []) = f t
  | [], _, h => by simp at h
  | u :: l, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons]
    by_cases hut : u = t
    · subst hut
      have : (l.flatMap fun v => if v = u then f v else []) = [] :=
        List.flatMap_eq_nil_iff.2 fun v hv => by rw [if_neg (fun (e : v = u) => hnd.1 (e ▸ hv))]
      simp [this]
    · rw [if_neg hut, List.nil_append]
      exact flatMap_ite_eq f hnd.2 ((List.mem_cons.1 h).resolve_left (Ne.symm hut))

theorem idxOf_lt_of_ordL {tn : TaskNetwork ℕ ℕ ℕ} (hwf : tn.WF) {l : List ℕ}
    (hl : tn.IsLinearization l) {a b : ℕ} (h : tn.ord a b) : l.idxOf a < l.idxOf b := by
  have ha : a ∈ l := (hl.2.1 a).2 (hwf.mem_left h)
  have hb : b ∈ l := (hl.2.1 b).2 (hwf.mem_right h)
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  by_contra hn
  rcases Nat.lt_or_ge (l.idxOf b) (l.idxOf a) with hlt | hge
  · have := List.pairwise_iff_getElem.1 hl.2.2 _ _ hib hia hlt
    rw [List.getElem_idxOf, List.getElem_idxOf] at this
    exact this h
  · have : l.idxOf a = l.idxOf b := by omega
    have hab : a = b := by
      rw [← List.getElem_idxOf hia, ← List.getElem_idxOf hib]; simp only [this]
    subst hab
    exact hwf.irrefl a h

/-- **Ordered merges in a totally ordered network are concatenations along the
linearisation.** -/
theorem ordMerge_lin_iff {tn : TaskNetwork ℕ ℕ ℕ} (hwf : tn.WF) (hto : tn.IsTotallyOrdered)
    {l : List ℕ} (hl : tn.IsLinearization l) {ys : ℕ → List ℕ} {π : List ℕ} :
    OrdMerge tn ys π ↔ π = (l.map ys).flatten := by
  constructor
  · rintro ⟨w, h1, h2, h3, h4⟩
    have hk : ∀ e ∈ w, e.1 ∈ l := fun e he => (hl.2.1 _).2 (h2 e he)
    have hp : w.Pairwise (fun x y => l.idxOf x.1 ≤ l.idxOf y.1) :=
      h4.imp_of_mem fun {x y} hx hy hxy => by
        by_cases he : x.1 = y.1
        · rw [he]
        · rcases hto x.1 (h2 x hx) y.1 (h2 y hy) he with h | h
          · exact (idxOf_lt_of_ordL hwf hl h).le
          · exact absurd h hxy
    rw [← h1, eq_flatMap_filter l w hl.1 hk hp, List.map_flatMap, List.flatten_eq_flatMap,
      List.flatMap_map]
    refine List.flatMap_congr fun t ht => ?_
    rw [← h3 t ((hl.2.1 t).1 ht)]
    congr 1
  · intro hπ
    refine ⟨l.flatMap fun t => (ys t).map fun a => (t, a), ?_, fun e he => ?_, fun t ht => ?_, ?_⟩
    · rw [hπ, List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_map]
      simp [List.map_map, Function.comp_def]
    · obtain ⟨u, hu, he⟩ := List.mem_flatMap.1 he
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 he
      exact (hl.2.1 u).1 hu
    · have htl : t ∈ l := (hl.2.1 t).2 ht
      rw [List.filter_flatMap]
      have : ∀ u, ((ys u).map fun a => (u, a)).filter (fun x => decide (x.1 = t)) =
          if u = t then (ys u).map fun a => (u, a) else [] := by
        intro u
        by_cases hu : u = t
        · rw [if_pos hu]; exact List.filter_eq_self.2 fun x hx => by
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; simp [hu]
        · rw [if_neg hu]; exact List.filter_eq_nil_iff.2 fun x hx => by
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; simp [hu]
      simp only [this]
      rw [flatMap_ite_eq (fun u => (ys u).map fun a => (u, a)) hl.1 htl]
      simp [List.map_map, Function.comp_def]
    · rw [List.pairwise_flatMap]
      refine ⟨fun u _ => ?_, hl.2.2.imp fun {u v} huv x hx y hy => ?_⟩
      · rw [List.pairwise_map]
        exact List.pairwise_of_forall fun _ _ => hwf.irrefl u
      · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
        exact huv

/-! ### Refinement -/

/-- **`n` refines from `s` to `s'`**: some valid tree for `n` has a yield running from `s` to `s'`. -/
def RefT (p : ProbDesc) (n : ℕ ⊕ ℕ) (s s' : Set ℕ) : Prop :=
  ∃ (dt : DTree ℕ ℕ ℕ) (ys : List ℕ), dt.Valid p.toProblem.methods n ∧ dt.Yield ys ∧
    p.toProblem.Run ys s s'

/-- The tasks `l`, labelled by `lab`, refine one after the other. -/
inductive ChainT (p : ProbDesc) (lab : ℕ → ℕ ⊕ ℕ) : List ℕ → Set ℕ → Set ℕ → Prop
  | nil (s : Set ℕ) : ChainT p lab [] s s
  | cons {x : ℕ} {l : List ℕ} {s s₁ s' : Set ℕ} (h₁ : RefT p (lab x) s s₁)
      (h₂ : ChainT p lab l s₁ s') : ChainT p lab (x :: l) s s'

theorem chainT_of_trees {p : ProbDesc} {lab : ℕ → ℕ ⊕ ℕ} {ch : ℕ → DTree ℕ ℕ ℕ}
    {ys : ℕ → List ℕ} : ∀ (l : List ℕ) {s s' : Set ℕ},
    (∀ x ∈ l, (ch x).Valid p.toProblem.methods (lab x) ∧ (ch x).Yield (ys x)) →
    p.toProblem.Run (l.map ys).flatten s s' → ChainT p lab l s s'
  | [], s, s', _, h => by cases h; exact .nil _
  | x :: l, s, s', hc, h => by
    rw [List.map_cons, List.flatten_cons, run_append] at h
    obtain ⟨m, h1, h2⟩ := h
    exact .cons ⟨ch x, ys x, (hc x (by simp)).1, (hc x (by simp)).2, h1⟩
      (chainT_of_trees l (fun y hy => hc y (by simp [hy])) h2)

theorem trees_of_chainT {p : ProbDesc} {lab : ℕ → ℕ ⊕ ℕ} {l : List ℕ} {s s' : Set ℕ}
    (h : ChainT p lab l s s') (hnd : l.Nodup) : ∃ (ch : ℕ → DTree ℕ ℕ ℕ) (ys : ℕ → List ℕ),
      (∀ x ∈ l, (ch x).Valid p.toProblem.methods (lab x) ∧ (ch x).Yield (ys x)) ∧
      p.toProblem.Run (l.map ys).flatten s s' := by
  induction h with
  | nil s => exact ⟨fun _ => .leaf 0, fun _ => [], fun x hx => by simp at hx, rfl⟩
  | @cons x l s s₁ s' h₁ _ ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨ch, ys, hc, hr⟩ := ih hnd.2
    obtain ⟨dt, ys₀, hv, hyd, hr₀⟩ := h₁
    have hne : ∀ y ∈ l, y ≠ x := fun y hy e => hnd.1 (e ▸ hy)
    refine ⟨Function.update ch x dt, Function.update ys x ys₀, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · simp [hv, hyd]
      · simp only [Function.update_of_ne (hne y hy)]; exact hc y hy
    · rw [List.map_cons, List.flatten_cons, run_append]
      refine ⟨s₁, by simpa using hr₀, ?_⟩
      rwa [List.map_congr_left fun y hy => Function.update_of_ne (hne y hy) _ _]

theorem refT_inl_iff {p : ProbDesc} {a : ℕ} {s s' : Set ℕ} :
    RefT p (Sum.inl a) s s' ↔ (p.toProblem.δ a).Applicable s ∧ s' = (p.toProblem.δ a).apply s := by
  constructor
  · rintro ⟨dt, ys, hv, hy, hr⟩
    obtain rfl := hv.eq_leaf_of_inl
    obtain rfl := hy.leaf_inv
    obtain ⟨happ, hr⟩ := hr
    cases hr
    exact ⟨happ, rfl⟩
  · rintro ⟨happ, rfl⟩
    exact ⟨.leaf a, [a], .leaf a, .leaf a, happ, rfl⟩

/-- **A method whose tasks refine one after the other refines its name.** -/
theorem refT_of_chain {p : ProbDesc} {e : MethodDesc} (he : e ∈ p.methods)
    (hto : e.2.toTaskNetwork.IsTotallyOrdered) {s s' : Set ℕ}
    (h : ChainT p e.2.label (TnDesc.lin e.2) s s') : RefT p (Sum.inr e.1) s s' := by
  have hl := TnDesc.isLinearization_lin hto
  obtain ⟨ch, ys, hc, hr⟩ := trees_of_chainT h hl.1
  refine ⟨.node e.1 e.toMethod ch, _, .node ⟨e, he, rfl⟩ rfl fun t ht => (hc t ((hl.2.1 t).2 ht)).1,
    .node ys (fun t ht => (hc t ((hl.2.1 t).2 ht)).2)
      ((ordMerge_lin_iff (TnDesc.toTaskNetwork_wf _) hto hl).2 rfl), hr⟩

/-- **A refinement of a compound name by a totally ordered method is a chain.** -/
theorem chain_of_refT {p : ProbDesc} {c : ℕ} {s s' : Set ℕ} (h : RefT p (Sum.inr c) s s')
    (hto : ∀ e ∈ p.methods, e.1 = c → e.2.toTaskNetwork.IsTotallyOrdered) :
    ∃ e ∈ p.methods, e.1 = c ∧ ChainT p e.2.label (TnDesc.lin e.2) s s' := by
  obtain ⟨dt, π, hv, hy, hr⟩ := h
  obtain ⟨m, ch, rfl⟩ := hv.eq_node_of_inr
  obtain ⟨-, ⟨e, he, rfl⟩, hc, hch⟩ := hv.node_inv
  obtain ⟨ys, hys, hm⟩ := hy.node_inv
  have hto' := hto e he hc
  have hl := TnDesc.isLinearization_lin hto'
  rw [(ordMerge_lin_iff (TnDesc.toTaskNetwork_wf _) hto' hl).1 hm] at hr
  exact ⟨e, he, hc, chainT_of_trees _ (fun x hx => ⟨hch x ((hl.2.1 x).1 hx),
    hys x ((hl.2.1 x).1 hx)⟩) hr⟩

/-- **Plan existence of a totally ordered description as a chain of refinements.** -/
theorem solvable_iff_chain {p : ProbDesc} (hp : p.Valid)
    (hto : p.tnI.toTaskNetwork.IsTotallyOrdered) :
    p.toProblem.Solvable ↔ ∃ s', ChainT p p.tnI.label (TnDesc.lin p.tnI) p.toProblem.init s' ∧
      p.toProblem.GoalState s' := by
  have hl := TnDesc.isLinearization_lin hto
  have hm : ∀ {ys : ℕ → List ℕ} {π : List ℕ}, OrdMerge p.tnI.toTaskNetwork ys π ↔
      π = ((TnDesc.lin p.tnI).map ys).flatten :=
    fun {_ _} => ordMerge_lin_iff (TnDesc.toTaskNetwork_wf p.tnI) hto hl
  rw [Problem.solvable_iff_trees p.toProblem (wf_toProblem p)]
  constructor
  · rintro ⟨trees, π, s, ⟨hv, ys, hy, hmg⟩, hr, hg⟩
    rw [hm.1 hmg] at hr
    exact ⟨s, chainT_of_trees _ (fun x hx => ⟨hv x ((hl.2.1 x).1 hx), hy x ((hl.2.1 x).1 hx)⟩) hr,
      hg⟩
  · rintro ⟨s', hc, hg⟩
    obtain ⟨ch, ys, hc', hr⟩ := trees_of_chainT hc hl.1
    exact ⟨ch, _, s', ⟨fun t ht => (hc' t ((hl.2.1 t).2 ht)).1, ys,
      fun t ht => (hc' t ((hl.2.1 t).2 ht)).2, hm.2 rfl⟩, hr, hg⟩

end Article

end HTN
