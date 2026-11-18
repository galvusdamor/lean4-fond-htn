import HtnPlanning.Article.DTree
import HtnPlanning.Classes.Basic
/-!
# TIHTN planning: plan existence

Task insertion (`HTN.Article.TIStep`) adds primitive tasks without ordering constraints; ordering
insertion then fixes a linearisation.  Hence a TIHTN problem is solvable iff its initial task
network decomposes into a primitive network one of whose linearisations induces a *subsequence*
of an action sequence that runs from the initial state into a goal state:

* `HTN.Article.Problem.solvableTI_iff_decomp`;
* `HTN.Article.Problem.solvableTI_iff_trees` — the same with decomposition trees (Prop. 2.2.1).
-/

namespace HTN

namespace Article

universe u v w x

variable {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

section TI

variable {tn tn' : TaskNetwork I A C}

theorem TIReach.T_sub (h : TIReach tn tn') : tn.T ⊆ tn'.T := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hs ih =>
    obtain ⟨t, a, -, rfl⟩ := hs
    exact ih.trans (Finset.subset_insert _ _)

theorem TIReach.ord (h : TIReach tn tn') : tn'.ord = tn.ord := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨t, a, -, rfl⟩ := hs
    exact ih

theorem TIReach.α_old (h : TIReach tn tn') : ∀ t ∈ tn.T, tn'.α t = tn.α t := by
  induction h with
  | refl => exact fun _ _ => rfl
  | tail h₀ hs ih =>
    obtain ⟨t', a, ht', rfl⟩ := hs
    intro t ht
    have hne : t ≠ t' := fun e => ht' (e ▸ TIReach.T_sub h₀ ht)
    simp only [taskInsert, Function.update_of_ne hne]
    exact ih t ht

theorem TIReach.new_prim (h : TIReach tn tn') :
    ∀ t ∈ tn'.T, t ∉ tn.T → tn'.IsPrimitiveId t := by
  induction h with
  | refl => exact fun t h h' => absurd h h'
  | tail h₀ hs ih =>
    obtain ⟨t', a, ht', rfl⟩ := hs
    intro t ht hn
    by_cases e : t = t'
    · subst e; exact ⟨a, by simp [taskInsert]⟩
    · have ht₁ : t ∈ _ := (Finset.mem_insert.1 ht).resolve_left e
      obtain ⟨b, hb⟩ := ih t ht₁ hn
      exact ⟨b, by simp only [taskInsert, Function.update_of_ne e]; exact hb⟩

theorem TIReach.wf (h : TIReach tn tn') (hwf : tn.WF) : tn'.WF := by
  have hT := h.T_sub
  exact ⟨fun hab => hT (hwf.mem_left (h.ord ▸ hab)), fun hab => hT (hwf.mem_right (h.ord ▸ hab)),
    fun t hab => hwf.irrefl t (h.ord ▸ hab), fun hab hbc => h.ord ▸ hwf.trans (h.ord ▸ hab)
      (h.ord ▸ hbc)⟩

end TI

/-! ### Weaving fresh tasks into a linearisation -/

/-- Labelled ids of a linearisation are labelled as in the network. -/
theorem α_of_mem_zip {α : I → A ⊕ C} :
    ∀ {l : List I} {as : List A}, l.map α = as.map Sum.inl → ∀ p ∈ l.zip as, α p.1 = Sum.inl p.2
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], h, _, _ => by simp at h
  | t :: l, a :: as, h, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact α_of_mem_zip h.2 p hp

/-- **Weaving.** If `as` is a subsequence of `π` and `l` lists ids for `as`, then `π` can be
labelled with ids extending `l` by fresh ids `f j`, `j ≥ k`, so that the order `ord` (living on
`T`) is still respected. -/
theorem exists_weave {T : Finset I} {ord : I → I → Prop} (hord : ∀ a b, ord a b → a ∈ T ∧ b ∈ T)
    (f : ℕ → I) (hf : Function.Injective f) (hfT : ∀ j, f j ∉ T) {as π : List A}
    (h : as.Sublist π) : ∀ (l : List I) (k : ℕ), l.length = as.length → l.Nodup →
      (∀ t ∈ l, t ∈ T) → l.Pairwise (fun a b => ¬ ord b a) →
      ∃ w : List (I × A), w.map Prod.snd = π ∧ (l.zip as).Sublist w ∧ (w.map Prod.fst).Nodup ∧
        (∀ x ∈ w, x ∈ l.zip as ∨ ∃ j ≥ k, x.1 = f j) ∧
        w.Pairwise (fun x y => ¬ ord y.1 x.1) := by
  induction h with
  | slnil =>
    intro l k hl _ _ _
    rw [List.length_nil, List.length_eq_zero_iff] at hl
    subst hl
    exact ⟨[], rfl, by simp, by simp, by simp, by simp⟩
  | @cons l₁ l₂ a h ih =>
    intro l k hl hnd hT hpw
    obtain ⟨w, h1, h2, h3, h4, h5⟩ := ih l (k + 1) hl hnd hT hpw
    have hnew : ∀ x ∈ w, x.1 ≠ f k := by
      intro x hx e
      rcases h4 x hx with hx | ⟨j, hj, hj'⟩
      · exact hfT k (e ▸ hT _ (List.of_mem_zip hx).1)
      · have := hf (e.symm.trans hj'); omega
    refine ⟨(f k, a) :: w, by simp [h1], h2.cons _, ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hm => ?_, h3⟩
      obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
      exact hnew x hx e
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr ⟨k, le_rfl, rfl⟩
      · rcases h4 x hx with h | ⟨j, hj, hj'⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, hj'⟩
    · exact List.Pairwise.cons (fun y _ hy => hfT k (hord _ _ hy).2) h5
  | @cons₂ l₁ l₂ a h ih =>
    intro l k hl hnd hT hpw
    cases l with
    | nil => simp at hl
    | cons t l₀ =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have hT₀ : ∀ t ∈ l₀, t ∈ T := fun t' ht' => hT t' (List.mem_cons_of_mem _ ht')
    obtain ⟨w, h1, h2, h3, h4, h5⟩ := ih l₀ k hl hnd.2 hT₀ hpw.2
    have htT : t ∈ T := hT t (List.mem_cons_self ..)
    refine ⟨(t, a) :: w, by simp [h1], by simpa using h2.cons₂ (t, a), ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hm => ?_, h3⟩
      obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
      rcases h4 x hx with hx | ⟨j, -, hj'⟩
      · exact hnd.1 (by rw [← show x.1 = t from e]; exact (List.of_mem_zip hx).1)
      · exact hfT j (by rw [← hj', show x.1 = t from e]; exact htT)
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl (by simp)
      · rcases h4 x hx with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h
    · refine List.Pairwise.cons (fun y hy hyo => ?_) h5
      rcases h4 y hy with hy | ⟨j, -, hj'⟩
      · exact hpw.1 _ (List.of_mem_zip hy).1 hyo
      · exact hfT j (hj' ▸ (hord _ _ hyo).1)

/-- Inserting the primitive tasks `xs` one after the other. -/
def insertAll (tn : TaskNetwork I A C) : List (I × A) → TaskNetwork I A C
  | [] => tn
  | x :: xs => insertAll (taskInsert tn x.1 x.2) xs

theorem tiReach_insertAll : ∀ {tn : TaskNetwork I A C} {xs : List (I × A)},
    (xs.map Prod.fst).Nodup → (∀ x ∈ xs, x.1 ∉ tn.T) → TIReach tn (insertAll tn xs)
  | _, [], _, _ => Relation.ReflTransGen.refl
  | tn, x :: xs, hnd, hfr => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine Relation.ReflTransGen.head ⟨x.1, x.2, hfr x (List.mem_cons_self ..), rfl⟩
      (tiReach_insertAll hnd.2 fun y hy => ?_)
    simp only [taskInsert, Finset.mem_insert, not_or]
    exact ⟨fun e => hnd.1 (List.mem_map.2 ⟨y, hy, e⟩), hfr y (List.mem_cons_of_mem _ hy)⟩

theorem mem_insertAll_T : ∀ {tn : TaskNetwork I A C} {xs : List (I × A)} {t : I},
    t ∈ (insertAll tn xs).T ↔ t ∈ tn.T ∨ ∃ x ∈ xs, x.1 = t
  | _, [], _ => by simp [insertAll]
  | tn, x :: xs, t => by
    rw [insertAll, mem_insertAll_T]
    simp only [taskInsert, Finset.mem_insert, List.mem_cons, exists_eq_or_imp]
    tauto

theorem insertAll_α_of_not_mem : ∀ {tn : TaskNetwork I A C} {xs : List (I × A)} {t : I},
    (∀ x ∈ xs, x.1 ≠ t) → (insertAll tn xs).α t = tn.α t
  | _, [], _, _ => rfl
  | tn, x :: xs, t, h => by
    rw [insertAll, insertAll_α_of_not_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]
    simp only [taskInsert]
    exact Function.update_of_ne (h x (List.mem_cons_self ..)).symm _ _

theorem insertAll_α_of_mem : ∀ {tn : TaskNetwork I A C} {xs : List (I × A)},
    (xs.map Prod.fst).Nodup → ∀ x ∈ xs, (insertAll tn xs).α x.1 = Sum.inl x.2
  | _, [], _, _, hx => by simp at hx
  | tn, y :: xs, hnd, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [insertAll]
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [insertAll_α_of_not_mem fun z hz e => hnd.1 (List.mem_map.2 ⟨z, hz, e⟩)]
      simp [taskInsert]
    · exact insertAll_α_of_mem hnd.2 x hx

namespace Problem

universe u'

variable {F : Type u'} (P : Problem F A C I)

/-- A primitive network with a linearisation running into a goal state can be ordered into a
network that is executable and all of whose generated states are goal states. -/
theorem exists_exec_of_lin {tn : TaskNetwork I A C} (hwf : tn.WF) (hprim : tn.IsPrimitive)
    {l : List I} {π : List A} {s : Set F} (hl : tn.IsLinearization l) (has : tn.IsActionSeq l π)
    (hrun : P.Run π P.init s) (hgoal : P.GoalState s) :
    ∃ tnS, OIReach tn tnS ∧ P.ExecutableIn tnS P.init ∧
      (∀ s', P.Generates tnS P.init s' → P.GoalState s') ∧ tnS.IsTotallyOrdered ∧
      tnS.IsLinearization l ∧ tnS.IsActionSeq l π := by
  obtain ⟨tn', htn', hoi, -, hT, hα, huniq⟩ := exists_oiReach_unique_lin hwf hprim hl
  have hprim' : tn'.IsPrimitive := by
    intro t ht; rw [hT] at ht; obtain ⟨a, ha⟩ := hprim t ht; exact ⟨a, by rw [hα]; exact ha⟩
  have has' : tn'.IsActionSeq l π := by
    unfold TaskNetwork.IsActionSeq at has ⊢; rw [hα]; exact has
  have key : ∀ l' as', tn'.IsLinearization l' → tn'.IsActionSeq l' as' → l' = l ∧ as' = π := by
    intro l' as' hl' has''
    obtain rfl := huniq l' hl'
    exact ⟨rfl, TaskNetwork.isActionSeq_unique has'' has'⟩
  have hdet : ∀ {bs : List A} {s₀ s₁ s₂ : Set F}, P.Run bs s₀ s₁ → P.Run bs s₀ s₂ → s₁ = s₂ := by
    intro bs
    induction bs with
    | nil => intro s₀ s₁ s₂ h₁ h₂; exact h₁.trans h₂.symm
    | cons b bs ih => intro s₀ s₁ s₂ h₁ h₂; exact ih h₁.2 h₂.2
  have hlS : tn'.IsLinearization l := by
    subst htn'
    refine ⟨hl.1, fun t => by rw [hT]; exact hl.2.1 t, ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij hc
    have := idxOf_lt_of_ordExt_chain hwf hl hc
    rw [List.idxOf_getElem hl.1, List.idxOf_getElem hl.1] at this
    omega
  refine ⟨tn', hoi, ⟨hprim', fun l' as' hl' has'' => ?_⟩, fun s' ⟨l', as', hl', has'', hrun'⟩ => ?_,
    ?_, hlS, has'⟩
  · obtain ⟨rfl, rfl⟩ := key l' as' hl' has''
    exact ⟨s, hrun⟩
  · obtain ⟨rfl, rfl⟩ := key l' as' hl' has''
    rw [hdet hrun' hrun]; exact hgoal
  · subst htn'
    intro a ha b hb hab
    rw [hT] at ha hb
    have ha' := (hl.2.1 a).2 ha
    have hb' := (hl.2.1 b).2 hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
    have hij : i ≠ j := fun h => hab (by subst h; rfl)
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact Or.inl (Relation.TransGen.mono (fun x y hxy => Or.inr hxy) (transGen_chain hi hj h))
    · exact Or.inr (Relation.TransGen.mono (fun x y hxy => Or.inr hxy) (transGen_chain hj hi h))

/-- Restricting a linearisation to a subset of the ids gives a subsequence of the actions. -/
theorem exists_sublist_filter {α : I → A ⊕ C} (p : I → Bool) :
    ∀ {l : List I} {π : List A}, l.map α = π.map Sum.inl →
      ∃ as : List A, (l.filter p).map α = as.map Sum.inl ∧ as.Sublist π
  | [], π, h => by
    rw [List.map_nil, eq_comm, List.map_eq_nil_iff] at h
    exact ⟨[], rfl, h ▸ List.Sublist.slnil⟩
  | _ :: _, [], h => by simp at h
  | t :: l, a :: π, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨as, h1, h2⟩ := exists_sublist_filter p h.2
    by_cases hp : p t
    · refine ⟨a :: as, ?_, h2.cons₂ a⟩
      rw [List.filter_cons_of_pos hp, List.map_cons, h.1, h1, List.map_cons]
    · exact ⟨as, by rw [List.filter_cons_of_neg hp, h1], h2.cons a⟩

/-- **From a decomposition with a weaving to a totally ordered TIHTN solution.** -/
theorem exists_solTI_of_decomp [Infinite I] (hP : P.WF) {tn : TaskNetwork I A C}
    (hdec : DecomposesTo P.methods P.tnI tn) (hprim : tn.IsPrimitive) {l : List I} {as π : List A}
    {s : Set F} (hl : tn.IsLinearization l) (has : tn.IsActionSeq l as) (hsub : as.Sublist π)
    (hrun : P.Run π P.init s) (hg : P.GoalState s) :
    ∃ tnS ∈ P.SolTI, tnS.IsTotallyOrdered ∧ ∃ l', tnS.IsLinearization l' ∧ tnS.IsActionSeq l' π := by
  have hwf : tn.WF := hdec.wf hP.tnI
  -- fresh ids
  let e := Infinite.natEmbedding I
  obtain ⟨N, hN⟩ := (tn.T.finite_toSet.preimage e.injective.injOn).bddAbove
  let f : ℕ → I := fun j => e (j + N + 1)
  have hf : Function.Injective f := fun a b h => by have := e.injective h; omega
  have hfT : ∀ j, f j ∉ tn.T := fun j hj => by
    have := hN (show j + N + 1 ∈ e ⁻¹' (tn.T : Set I) from hj); omega
  have hlen : l.length = as.length := by
    have := congrArg List.length has; simpa using this
  obtain ⟨w, h1, h2, h3, h4, h5⟩ := exists_weave (T := tn.T) (ord := tn.ord)
    (fun a b h => ⟨hwf.mem_left h, hwf.mem_right h⟩) f hf hfT hsub l 0 hlen hl.1
    (fun t ht => (hl.2.1 t).1 ht) hl.2.2
  let ins := w.filter fun x => decide (x.1 ∉ tn.T)
  have hins_nd : (ins.map Prod.fst).Nodup := h3.sublist (List.filter_sublist.map _)
  have hti : TIReach tn (insertAll tn ins) := tiReach_insertAll hins_nd fun x hx => by
    simpa using (List.mem_filter.1 hx).2
  set tn' := insertAll tn ins
  have hwf' := hti.wf hwf
  have hold : ∀ x ∈ w, x.1 ∈ tn.T → x ∈ l.zip as := fun x hx hxT => by
    rcases h4 x hx with h | ⟨j, -, hj⟩
    · exact h
    · exact absurd (hj ▸ hxT) (hfT j)
  have hαw : ∀ x ∈ w, tn'.α x.1 = Sum.inl x.2 := fun x hx => by
    by_cases hxT : x.1 ∈ tn.T
    · rw [hti.α_old _ hxT]; exact α_of_mem_zip has x (hold x hx hxT)
    · exact insertAll_α_of_mem hins_nd x (List.mem_filter.2 ⟨hx, by simpa using hxT⟩)
  have hl' : tn'.IsLinearization (w.map Prod.fst) := by
    refine ⟨h3, fun t => ⟨fun ht => ?_, fun ht => ?_⟩, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
      by_cases hxT : x.1 ∈ tn.T
      · exact hti.T_sub hxT
      · exact mem_insertAll_T.2 (Or.inr ⟨x, List.mem_filter.2 ⟨hx, by simpa using hxT⟩, rfl⟩)
    · rcases mem_insertAll_T.1 ht with ht | ⟨x, hx, rfl⟩
      · have hsl : l.Sublist (w.map Prod.fst) := by
          have := h2.map Prod.fst
          rwa [List.map_fst_zip hlen.le] at this
        exact hsl.subset ((hl.2.1 t).2 ht)
      · exact List.mem_map.2 ⟨x, (List.mem_filter.1 hx).1, rfl⟩
    · rw [List.pairwise_map, hti.ord]; exact h5
  have has' : tn'.IsActionSeq (w.map Prod.fst) π := by
    unfold TaskNetwork.IsActionSeq
    rw [← h1, List.map_map, List.map_map]
    exact List.map_congr_left fun x hx => hαw x hx
  have hprim' : tn'.IsPrimitive := fun t ht => by
    by_cases htT : t ∈ tn.T
    · obtain ⟨a, ha⟩ := hprim t htT; exact ⟨a, by rw [hti.α_old t htT]; exact ha⟩
    · exact hti.new_prim t ht htT
  obtain ⟨tnS, hoi, hex, hgoal, htot, hlS, hasS⟩ := P.exists_exec_of_lin hwf' hprim' hl' has' hrun hg
  exact ⟨tnS, ⟨hex, hgoal, tn, tn', hdec, hti, hoi⟩, htot, _, hlS, hasS⟩

/-- **TIHTN plan existence via decompositions.** -/
theorem solvableTI_iff_decomp [Infinite I] (hP : P.WF) :
    P.SolvableTI ↔ ∃ tn, DecomposesTo P.methods P.tnI tn ∧ tn.IsPrimitive ∧
      ∃ l as π s, tn.IsLinearization l ∧ tn.IsActionSeq l as ∧ as.Sublist π ∧
        P.Run π P.init s ∧ P.GoalState s := by
  constructor
  · rintro ⟨tnS, hex, hgoal, tn, tn', hdec, hti, hoi⟩
    have hwf : tn.WF := hdec.wf hP.tnI
    have hwf' : tn'.WF := hti.wf hwf
    have hwfS : tnS.WF := hoi.wf hwf'
    obtain ⟨l, π, hl, has⟩ := TaskNetwork.exists_linearization_actionSeq hwfS hex.1
    obtain ⟨s, hrun⟩ := hex.2 l π hl has
    have hg := hgoal s ⟨l, π, hl, has, hrun⟩
    have hl' := hoi.isLinearization hl
    have has' : tn'.IsActionSeq l π := by
      unfold TaskNetwork.IsActionSeq at has ⊢; rw [← hoi.α]; exact has
    have hprim' : tn'.IsPrimitive := fun t ht => by
      obtain ⟨a, ha⟩ := hex.1 t (by rw [hoi.T]; exact ht)
      exact ⟨a, by rw [← hoi.α]; exact ha⟩
    obtain ⟨as, has₀, hsub⟩ := exists_sublist_filter (fun t => decide (t ∈ tn.T)) has'
    refine ⟨tn, hdec, fun t ht => ?_, l.filter (fun t => decide (t ∈ tn.T)), as, π, s,
      ⟨hl'.1.filter _, fun t => ?_, ?_⟩, ?_, hsub, hrun, hg⟩
    · obtain ⟨a, ha⟩ := hprim' t (hti.T_sub ht)
      exact ⟨a, by rw [← hti.α_old t ht]; exact ha⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hl'.2.1 t).2 (hti.T_sub h), h⟩⟩
    · exact (hl'.2.2.filter _).imp fun h hab => h (by rw [hti.ord]; exact hab)
    · unfold TaskNetwork.IsActionSeq
      rw [← has₀]
      refine List.map_congr_left fun t ht => ?_
      exact (hti.α_old t (by simpa using (List.mem_filter.1 ht).2)).symm
  · rintro ⟨tn, hdec, hprim, l, as, π, s, hl, has, hsub, hrun, hg⟩
    obtain ⟨tnS, hS, -⟩ := P.exists_solTI_of_decomp hP hdec hprim hl has hsub hrun hg
    exact ⟨tnS, hS⟩

/-- **TIHTN plan existence via decomposition trees.** -/
theorem solvableTI_iff_trees [Infinite I] [Nonempty A] (hP : P.WF) :
    P.SolvableTI ↔ ∃ (trees : I → DTree I A C) (as π : List A) (s : Set F),
      TreesYield P.methods P.tnI trees as ∧ as.Sublist π ∧ P.Run π P.init s ∧ P.GoalState s := by
  rw [solvableTI_iff_decomp P hP]
  constructor
  · rintro ⟨tn, hd, hp, l, as, π, s, hl, has, hsub, hrun, hg⟩
    obtain ⟨trees, ht⟩ := treesYield_of_decomposesTo hP.tnI hd hp hl has
    exact ⟨trees, as, π, s, ht, hsub, hrun, hg⟩
  · rintro ⟨trees, as, π, s, ht, hsub, hrun, hg⟩
    obtain ⟨tn, hd, hp, l, hl, has⟩ := decomposesTo_of_treesYield hP.methods hP.tnI ht
    exact ⟨tn, hd, hp, l, as, π, s, hl, has, hsub, hrun, hg⟩

open Classical in
/-- **Cyclic decompositions can be avoided in TIHTN planning** (the lemma referenced as `??` in
the draft; Geier & Bercher 2011): a TIHTN problem is solvable iff it is solvable with *acyclic*
decomposition trees — no compound task name repeats on a path.  A repeated name is cut out by
replacing the upper subtree with the lower one; the yield shrinks to a subsequence, and the
missing actions are inserted again by task insertion. -/
theorem solvableTI_iff_acyc_trees [Infinite I] [Nonempty A] (hP : P.WF) :
    P.SolvableTI ↔ ∃ (trees : I → DTree I A C) (as π : List A) (s : Set F),
      TreesYield P.methods P.tnI trees as ∧ (∀ t ∈ P.tnI.T, (trees t).Acyc) ∧ as.Sublist π ∧
        P.Run π P.init s ∧ P.GoalState s := by
  rw [solvableTI_iff_trees P hP]
  constructor
  · rintro ⟨trees, as, π, s, ⟨hval, ys, hys, hm⟩, hsub, hrun, hg⟩
    have H : ∀ t, ∃ (dt' : DTree I A C) (π' : List A), t ∈ P.tnI.T →
        dt'.Valid P.methods (P.tnI.α t) ∧ dt'.Yield π' ∧ π'.Sublist (ys t) ∧ dt'.Acyc := by
      intro t
      by_cases ht : t ∈ P.tnI.T
      · obtain ⟨dt', π', h⟩ := (trees t).exists_acyc (hval t ht) (hys t ht)
        exact ⟨dt', π', fun _ => h⟩
      · exact ⟨trees t, [], fun h => absurd h ht⟩
    choose trees' ys' hspec using H
    obtain ⟨as', hsub', hm'⟩ := hm.sublist ys' fun t ht => (hspec t ht).2.2.1
    exact ⟨trees', as', π, s, ⟨fun t ht => (hspec t ht).1, ys', fun t ht => (hspec t ht).2.1, hm'⟩,
      fun t ht => (hspec t ht).2.2.2, hsub'.trans hsub, hrun, hg⟩
  · rintro ⟨trees, as, π, s, ht, -, hsub, hrun, hg⟩
    exact ⟨trees, as, π, s, ht, hsub, hrun, hg⟩

/-- The decomposition behind a TIHTN solution with a given linearisation. -/
theorem decomp_of_solTI (hP : P.WF) {tnS : TaskNetwork I A C} (hS : tnS ∈ P.SolTI) {l : List I}
    {π : List A} (hl : tnS.IsLinearization l) (has : tnS.IsActionSeq l π) :
    ∃ tn, DecomposesTo P.methods P.tnI tn ∧ tn.IsPrimitive ∧
      ∃ l₀ as s, tn.IsLinearization l₀ ∧ tn.IsActionSeq l₀ as ∧ as.Sublist π ∧
        P.Run π P.init s ∧ P.GoalState s := by
  obtain ⟨hex, hgoal, tn, tn', hdec, hti, hoi⟩ := hS
  obtain ⟨s, hrun⟩ := hex.2 l π hl has
  have hg := hgoal s ⟨l, π, hl, has, hrun⟩
  have hl' := hoi.isLinearization hl
  have has' : tn'.IsActionSeq l π := by
    unfold TaskNetwork.IsActionSeq at has ⊢; rw [← hoi.α]; exact has
  have hprim' : tn'.IsPrimitive := fun t ht => by
    obtain ⟨a, ha⟩ := hex.1 t (by rw [hoi.T]; exact ht)
    exact ⟨a, by rw [← hoi.α]; exact ha⟩
  obtain ⟨as, has₀, hsub⟩ := exists_sublist_filter (fun t => decide (t ∈ tn.T)) has'
  refine ⟨tn, hdec, fun t ht => ?_, l.filter (fun t => decide (t ∈ tn.T)), as, s,
    ⟨hl'.1.filter _, fun t => ?_, ?_⟩, ?_, hsub, hrun, hg⟩
  · obtain ⟨a, ha⟩ := hprim' t (hti.T_sub ht)
    exact ⟨a, by rw [← hti.α_old t ht]; exact ha⟩
  · simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hl'.2.1 t).2 (hti.T_sub h), h⟩⟩
  · exact (hl'.2.2.filter _).imp fun h hab => h (by rw [hti.ord]; exact hab)
  · unfold TaskNetwork.IsActionSeq
    rw [← has₀]
    refine List.map_congr_left fun t ht => ?_
    exact (hti.α_old t (by simpa using (List.mem_filter.1 ht).2)).symm

end Problem

open Classical in
/-- Valid trees can be pruned to acyclic ones, the merged yield shrinking to a subsequence. -/
theorem treesYield_acyc {M : Set (Method I A C)} {tn : TaskNetwork I A C}
    {trees : I → DTree I A C} {as : List A} (h : TreesYield M tn trees as) :
    ∃ (trees' : I → DTree I A C) (as' : List A), TreesYield M tn trees' as' ∧
      (∀ t ∈ tn.T, (trees' t).Acyc) ∧ as'.Sublist as := by
  obtain ⟨hval, ys, hys, hm⟩ := h
  have H : ∀ t, ∃ (dt' : DTree I A C) (π' : List A), t ∈ tn.T →
      dt'.Valid M (tn.α t) ∧ dt'.Yield π' ∧ π'.Sublist (ys t) ∧ dt'.Acyc := by
    intro t
    by_cases ht : t ∈ tn.T
    · obtain ⟨dt', π', h⟩ := (trees t).exists_acyc (hval t ht) (hys t ht)
      exact ⟨dt', π', fun _ => h⟩
    · exact ⟨trees t, [], fun h => absurd h ht⟩
  choose trees' ys' hspec using H
  obtain ⟨as', hsub', hm'⟩ := hm.sublist ys' fun t ht => (hspec t ht).2.2.1
  exact ⟨trees', as', ⟨fun t ht => (hspec t ht).1, ys', fun t ht => (hspec t ht).2.1, hm'⟩,
    fun t ht => (hspec t ht).2.2.2, hsub'⟩

end Article

end HTN
