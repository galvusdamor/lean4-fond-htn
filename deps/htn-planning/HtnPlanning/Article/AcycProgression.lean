import HtnPlanning.Article.TIHTN
import HtnPlanning.Progression.Progression
/-!
# Acyclic progression (Def. 4.2, Thm. 4.2.12 — the TIHTN part)

**Acyclic progression** (Alford et al. 2015) progresses a state, a task network and an
*ancestor* function `a` (the compound task names whose decomposition introduced a task):

* a compound task `t` without predecessors is decomposed with a method none of whose task names
  is an ancestor of `t`; the inserted tasks get the ancestors `a(t) ∪ {α(t)}`;
* a primitive task without predecessors that is applicable is applied and removed;
* an arbitrary applicable action is applied (task insertion).

Initially `a(t) = {α(t)}` for the compound tasks of `tn_I` (`∅` for the primitive ones).

* `HTN.Article.Problem.AProgStep`, `AProgReach`, `AGoalNode`;
* **`HTN.Article.Problem.thm_4_2_12_tihtn`** — a TIHTN problem is solvable iff some acyclic
  progression of `(s_I, tn_I, a_I)` reaches the empty task network in a goal state.

The proof goes through decomposition trees: soundness by collapsing the decompositions of a
progression into trees (`treesYield_of_step`), completeness by progressing along *acyclic* trees
(`solvableTI_iff_acyc_trees`).

*Remark on the definition.*  As in the article, the inserted tasks get `a(t) ∪ {α(t)}`, not their
own names; hence a compound name may occur twice in a row on a path (`c → d → d`), but no name
occurs on a path again after a different one.  This does not affect the theorem.
-/

namespace HTN

namespace Article

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- A node of acyclic progression: state, task network, ancestors, actions applied so far. -/
structure APNode (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The state. -/
  state : Set F
  /-- The remaining task network. -/
  net : TaskNetwork I A C
  /-- The ancestors of the tasks. -/
  anc : I → Set C
  /-- The actions applied so far. -/
  plan : List A

namespace Problem

variable [DecidableEq I] (P : Problem F A C I)

/-- **Definition 4.2 (acyclic progression).** -/
inductive AProgStep : APNode F A C I → APNode F A C I → Prop
  /-- A primitive task without predecessors, applicable in the state, is applied. -/
  | prog {s : Set F} {tn : TaskNetwork I A C} {an : I → Set C} {π : List A} {t : I} {a : A}
      (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s) :
      AProgStep ⟨s, tn, an, π⟩ ⟨(P.δ a).apply s, tn.progress t, an, π ++ [a]⟩
  /-- A compound task without predecessors is decomposed by a method none of whose task names
  is an ancestor of it. -/
  | decomp {s : Set F} {tn tn'' : TaskNetwork I A C} {an : I → Set C} {π : List A} {t : I}
      {m : Method I A C} (hu : tn.Unconstrained t) (hm : m ∈ P.methods)
      (hα : tn.α t = Sum.inr m.abstractTask) (hwf'' : tn''.WF) (hiso : tn''.Iso m.subtasks)
      (hdisj : Disjoint tn.T tn''.T)
      (hanc : ∀ u ∈ m.subtasks.T, ∀ c, m.subtasks.α u = Sum.inr c → c ∉ an t) :
      AProgStep ⟨s, tn, an, π⟩ ⟨s, decomposeWith tn t tn'',
        fun x => if x ∈ tn''.T then insert m.abstractTask (an t) else an x, π⟩
  /-- An applicable action is inserted and applied. -/
  | insert {s : Set F} {tn : TaskNetwork I A C} {an : I → Set C} {π : List A} {a : A}
      (happ : (P.δ a).Applicable s) :
      AProgStep ⟨s, tn, an, π⟩ ⟨(P.δ a).apply s, tn, an, π ++ [a]⟩

/-- The initial node `(s_I, tn_I, {(t, {α_I(t)}) | α_I(t) ∈ N_C})`. -/
def initANode : APNode F A C I := ⟨P.init, P.tnI, fun t => {c | P.tnI.α t = Sum.inr c}, []⟩

/-- `(s_I, tn_I, a_I) →*_AP n`. -/
def AProgReach (n : APNode F A C I) : Prop := Relation.ReflTransGen P.AProgStep P.initANode n

/-- A goal node: the empty task network in a goal state. -/
def AGoalNode (n : APNode F A C I) : Prop := n.net.T = ∅ ∧ P.GoalState n.state

/-! ### Soundness -/

/-- **Soundness**: if acyclic progression leads from `n` to a goal node, the network of `n` has
valid trees whose merged yield is a subsequence of the actions applied on the way. -/
theorem aprog_sound [Nonempty A] {n n' : APNode F A C I}
    (h : Relation.ReflTransGen P.AProgStep n n') (hg : P.AGoalNode n') :
    n.net.WF → ∃ (trees : I → DTree I A C) (as ρ : List A),
      TreesYield P.methods n.net trees as ∧ as.Sublist ρ ∧ P.Run ρ n.state n'.state ∧
        n'.plan = n.plan ++ ρ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    have hT := hg.1
    refine ⟨fun _ => DTree.leaf (Classical.arbitrary A), [], [], ⟨fun t ht => by simp [hT] at ht,
      fun _ => [], fun t ht => by simp [hT] at ht, [], rfl, by simp, fun t ht => by simp [hT] at ht,
      List.Pairwise.nil⟩, List.Sublist.slnil, rfl, by simp⟩
  | head hstep _ ih =>
    intro hwf
    cases hstep with
    | @prog s tn an π t a hu hα happ =>
      obtain ⟨trees₂, as₂, ρ₂, ⟨hval, ys, hys, w, hmap, hmem, hfil, hpw⟩, hsub, hrun, hplan⟩ :=
        ih (TaskNetwork.progress_wf hwf hu)
      have hwt : ∀ x ∈ w, x.1 ≠ t := fun x hx => (TaskNetwork.mem_progress_T.1 (hmem x hx)).1
      refine ⟨Function.update trees₂ t (DTree.leaf a), a :: as₂, a :: ρ₂,
        ⟨fun x hx => ?_, Function.update ys t [a], fun x hx => ?_, (t, a) :: w, by simp [hmap],
          fun x hx => ?_, fun x hx => ?_, ?_⟩, hsub.cons₂ a, ⟨happ, hrun⟩, by simp [hplan]⟩
      · by_cases e : x = t
        · subst e; simp only [Function.update_self, hα]; exact DTree.Valid.leaf a
        · rw [Function.update_of_ne e]
          exact hval x (TaskNetwork.mem_progress_T.2 ⟨e, hx⟩)
      · by_cases e : x = t
        · subst e; simp only [Function.update_self]; exact DTree.Yield.leaf a
        · rw [Function.update_of_ne e, Function.update_of_ne e]
          exact hys x (TaskNetwork.mem_progress_T.2 ⟨e, hx⟩)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hu.1
        · exact (TaskNetwork.mem_progress_T.1 (hmem x hx)).2
      · by_cases e : x = t
        · subst e
          rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.2 fun y hy => by
            simpa using hwt y hy]
          simp
        · rw [List.filter_cons_of_neg (by simpa using Ne.symm e), Function.update_of_ne e]
          exact hfil x (TaskNetwork.mem_progress_T.2 ⟨e, hx⟩)
      · refine List.Pairwise.cons (fun y hy => hu.2 y.1 (TaskNetwork.mem_progress_T.1 (hmem y hy)).2)
          (hpw.imp_of_mem fun {x y} _ hy h h' => h ⟨h', hwt y hy⟩)
    | @decomp s tn tn'' an π t m hu hm hα hwf'' hiso hdisj hanc =>
      obtain ⟨trees₁, as, ρ, h, hsub, hrun, hplan⟩ := ih (decomposeWith_wf hwf hwf'' hdisj)
      obtain ⟨trees, h'⟩ := treesYield_of_step hwf hwf'' hm hu.1 hα hiso hdisj h
      exact ⟨trees, as, ρ, h', hsub, hrun, hplan⟩
    | @insert s tn an π a happ =>
      obtain ⟨trees, as, ρ, h, hsub, hrun, hplan⟩ := ih hwf
      exact ⟨trees, as, a :: ρ, h, hsub.cons a, ⟨happ, hrun⟩, by simp [hplan]⟩

/-! ### Completeness -/

/-- **Completeness**: from a node whose tasks have acyclic trees respecting the ancestors, whose
merged yield is a subsequence of an action sequence leading into a goal state, acyclic
progression reaches a goal node. -/
theorem aprog_complete [Infinite I] (hM : ∀ m ∈ P.methods, m.subtasks.WF) :
    ∀ (N : ℕ) (n : APNode F A C I) (trees : I → DTree I A C) (as ρ : List A) (sf : Set F),
      N = ∑ t ∈ n.net.T, (trees t).size + ρ.length → n.net.WF →
      TreesYield P.methods n.net trees as →
      (∀ x ∈ n.net.T, (trees x).Acyc ∧ (trees x).AncGood (n.anc x)) →
      as.Sublist ρ → P.Run ρ n.state sf → P.GoalState sf →
      ∃ n', Relation.ReflTransGen P.AProgStep n n' ∧ P.AGoalNode n' ∧ n'.plan = n.plan ++ ρ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rintro ⟨s, tn, an, π⟩ trees as ρ sf hN hwf hTY hinv hsub hrun hgoal
  simp only at hN hwf hTY hinv hrun
  by_cases hA : ∃ x, tn.Unconstrained x ∧ ∃ c, tn.α x = Sum.inr c
  · -- decompose an unconstrained compound task along its tree
    obtain ⟨x, hu, c, hc⟩ := hA
    have hv := hTY.1 x hu.1
    rw [hc] at hv
    obtain ⟨m, ch, hnode⟩ := hv.eq_node_of_inr
    rw [hnode] at hv
    obtain ⟨-, hmM, hmc, hch⟩ := hv.node_inv
    obtain ⟨tn'', hwf'', hiso, hdisj⟩ :=
      TaskNetwork.exists_fresh_iso_copy m.subtasks (hM m hmM) tn.T
    obtain ⟨-, hα, trees₁, hTY₁, hlt, hnew, hold⟩ :=
      treesYield_decomp hwf hwf'' hdisj hTY hu.1 hnode hiso
    obtain ⟨hacyc, hgood⟩ := hinv x hu.1
    rw [hnode] at hacyc hgood
    have hacyc' : ∀ u ∈ m.subtasks.T, (ch u).Acyc ∧ ¬ DTree.Occurs c (ch u) := by
      cases hacyc with | node h1 h2 => exact fun u hu => ⟨h1 u hu, h2 u hu⟩
    have hanc : ∀ u ∈ m.subtasks.T, ∀ d, m.subtasks.α u = Sum.inr d → d ∉ an x := by
      intro u hu' d hd hdx
      have hvu := hch u hu'
      rw [hd] at hvu
      obtain ⟨m', ch', hn'⟩ := hvu.eq_node_of_inr
      have hocc : DTree.Occurs d (ch u) := hn' ▸ DTree.Occurs.root
      rcases hgood d hdx with h | ⟨m₀, ch₀, h⟩
      · exact h (DTree.Occurs.child hu' hocc)
      · have : c = d := by injection h
        exact (hacyc' u hu').2 (this ▸ hocc)
    have hstep := AProgStep.decomp (P := P) (s := s) (π := π) hu hmM hα hwf'' hiso hdisj hanc
    have hinv₁ : ∀ y ∈ (decomposeWith tn x tn'').T, (trees₁ y).Acyc ∧
        (trees₁ y).AncGood (if y ∈ tn''.T then insert m.abstractTask (an x) else an y) := by
      intro y hy
      by_cases hy'' : y ∈ tn''.T
      · obtain ⟨u, hu', e⟩ := hnew y hy''
        simp only [hy'', if_true]
        rw [e]
        refine ⟨(hacyc' u hu').1, fun c' hc' => ?_⟩
        rcases Set.mem_insert_iff.1 hc' with rfl | hc'
        · left; rw [hmc]; exact (hacyc' u hu').2
        · rcases hgood c' hc' with h | ⟨m₀, ch₀, h⟩
          · exact Or.inl fun ho => h (DTree.Occurs.child hu' ho)
          · have : c = c' := by injection h
            subst this
            exact Or.inl (hacyc' u hu').2
      · have hyT : y ∈ tn.T := by
          rcases mem_decomposeWith_T.1 hy with ⟨h, -⟩ | h
          · exact h
          · exact absurd h hy''
        simp only [hy'', if_false]
        rw [hold y hy'']
        exact hinv y hyT
    obtain ⟨n', h1, h2, h3⟩ := ih (∑ t ∈ (decomposeWith tn x tn'').T, (trees₁ t).size + ρ.length)
      (by omega) ⟨s, decomposeWith tn x tn'',
        fun y => if y ∈ tn''.T then insert m.abstractTask (an x) else an y, π⟩ trees₁ as ρ sf rfl
      (decomposeWith_wf hwf hwf'' hdisj) hTY₁ hinv₁ hsub hrun hgoal
    exact ⟨n', Relation.ReflTransGen.head hstep h1, h2, h3⟩
  push_neg at hA
  have hTY0 := hTY
  obtain ⟨hval, ys, hys, w, hmap, hmem, hfil, hpw⟩ := hTY
  have hprimU : ∀ x, tn.Unconstrained x →
      ∃ a, tn.α x = Sum.inl a ∧ trees x = DTree.leaf a ∧ ys x = [a] := by
    intro x hu
    cases hαx : tn.α x with
    | inr c => exact absurd hαx (hA x hu c)
    | inl a =>
      have hv := hval x hu.1
      rw [hαx] at hv
      have e := hv.eq_leaf_of_inl
      have hy := hys x hu.1
      rw [e] at hy
      exact ⟨a, rfl, e, hy.leaf_inv⟩
  by_cases hT : tn.T = ∅
  · -- only inserted actions remain
    have hw : w = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by
      have := hmem x hx; simp [hT] at this
    subst hw
    have has : as = [] := by rw [← hmap]; rfl
    subst has
    cases ρ with
    | nil =>
      have : sf = s := hrun
      subst this
      exact ⟨_, Relation.ReflTransGen.refl, ⟨hT, hgoal⟩, by simp⟩
    | cons b ρ' =>
      obtain ⟨happ, hrun'⟩ := hrun
      obtain ⟨n', h1, h2, h3⟩ := ih (∑ t ∈ tn.T, (trees t).size + ρ'.length)
        (by simp only [List.length_cons] at hN; omega) ⟨(P.δ b).apply s, tn, an, π ++ [b]⟩ trees
        [] ρ' sf rfl hwf hTY0 hinv (List.nil_sublist _) hrun' hgoal
      exact ⟨n', Relation.ReflTransGen.head (AProgStep.insert happ) h1, h2, by simp [h3]⟩
  obtain ⟨x₀, hx₀⟩ := TaskNetwork.exists_unconstrained hwf (Finset.nonempty_iff_ne_empty.2 hT)
  cases w with
  | nil =>
    obtain ⟨a, -, -, hy⟩ := hprimU x₀ hx₀
    have := hfil x₀ hx₀.1
    rw [hy] at this
    simp at this
  | cons e w' =>
  obtain ⟨x, a₀⟩ := e
  have hxT : x ∈ tn.T := hmem (x, a₀) (List.mem_cons_self ..)
  have hxu : tn.Unconstrained x := by
    refine ⟨hxT, fun y _ hyx => ?_⟩
    obtain ⟨y', hy'u, hy'x⟩ := TaskNetwork.exists_unconstrained_pred hwf hyx
    obtain ⟨b, -, -, hyb⟩ := hprimU y' hy'u
    have hne : (((x, a₀) :: w').filter fun z => decide (z.1 = y')) ≠ [] := by
      intro h
      have := hfil y' hy'u.1
      rw [h, hyb] at this
      simp at this
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hz1, hz2⟩ := List.mem_filter.1 hz
    have hz2' : z.1 = y' := by simpa using hz2
    rcases List.mem_cons.1 hz1 with rfl | hz'
    · have : x = y' := hz2'
      subst this
      exact hwf.irrefl _ hy'x
    · exact (List.pairwise_cons.1 hpw).1 z hz' (by rw [hz2']; exact hy'x)
  obtain ⟨a, hαx, htx, hyx⟩ := hprimU x hxu
  have hfx := hfil x hxT
  rw [List.filter_cons_of_pos (by simp), List.map_cons, hyx, List.cons.injEq] at hfx
  obtain ⟨rfl, hfx'⟩ := hfx
  have hnx : ∀ y ∈ w', y.1 ≠ x := by
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hfx'
    intro y hy; simpa using hfx' y hy
  have has : as = a₀ :: w'.map Prod.snd := by rw [← hmap]; rfl
  subst has
  have hTY' : TreesYield P.methods (tn.progress x) trees (w'.map Prod.snd) := by
    refine ⟨fun y hy => hval y (TaskNetwork.mem_progress_T.1 hy).2, ys,
      fun y hy => hys y (TaskNetwork.mem_progress_T.1 hy).2, w', rfl,
      fun y hy => TaskNetwork.mem_progress_T.2 ⟨hnx y hy, hmem y (List.mem_cons_of_mem _ hy)⟩,
      fun t ht => ?_, (List.pairwise_cons.1 hpw).2.imp fun h h' => h h'.1⟩
    have := hfil t (TaskNetwork.mem_progress_T.1 ht).2
    rwa [List.filter_cons_of_neg (by simpa using Ne.symm (TaskNetwork.mem_progress_T.1 ht).1)]
      at this
  have hsize : ∑ t ∈ (tn.progress x).T, (trees t).size + 1 = ∑ t ∈ tn.T, (trees t).size := by
    rw [TaskNetwork.progress_T, ← Finset.add_sum_erase _ _ hxT, htx, DTree.size]
    omega
  have hinv' : ∀ y ∈ (tn.progress x).T, (trees y).Acyc ∧ (trees y).AncGood (an y) :=
    fun y hy => hinv y (TaskNetwork.mem_progress_T.1 hy).2
  cases ρ with
  | nil => simp at hsub
  | cons b ρ' =>
    obtain ⟨happ, hrun'⟩ := hrun
    simp only [List.length_cons] at hN
    rcases List.sublist_cons_iff.1 hsub with hs | ⟨r, hr, hs⟩
    · obtain ⟨n', h1, h2, h3⟩ := ih (∑ t ∈ tn.T, (trees t).size + ρ'.length) (by omega)
        ⟨(P.δ b).apply s, tn, an, π ++ [b]⟩ trees _ ρ' sf
        rfl hwf hTY0 hinv hs hrun' hgoal
      exact ⟨n', Relation.ReflTransGen.head (AProgStep.insert happ) h1, h2, by simp [h3]⟩
    · rw [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨n', h1, h2, h3⟩ := ih (∑ t ∈ (tn.progress x).T, (trees t).size + ρ'.length)
        (by omega) ⟨(P.δ a₀).apply s, tn.progress x, an, π ++ [a₀]⟩
        trees _ ρ' sf rfl (TaskNetwork.progress_wf hwf hxu) hTY' hinv' hs hrun' hgoal
      exact ⟨n', Relation.ReflTransGen.head (AProgStep.prog hxu hαx happ) h1, h2, by simp [h3]⟩

/-- The initial ancestors are respected by acyclic trees for the initial tasks. -/
theorem init_inv {trees : I → DTree I A C} {as : List A}
    (hTY : TreesYield P.methods P.tnI trees as) (hacyc : ∀ t ∈ P.tnI.T, (trees t).Acyc) :
    ∀ x ∈ P.initANode.net.T, (trees x).Acyc ∧ (trees x).AncGood (P.initANode.anc x) := by
  intro x hx
  refine ⟨hacyc x hx, fun c hc => Or.inr ?_⟩
  have hv := hTY.1 x hx
  have hc' : P.tnI.α x = Sum.inr c := hc
  rw [hc'] at hv
  exact hv.eq_node_of_inr

/-- **Theorem 4.2.12 (TIHTN part).** A TIHTN problem is solvable iff some acyclic progression of
`(s_I, tn_I, {(t, {α_I(t)}) | α_I(t) ∈ N_C})` reaches the empty task network in a state
satisfying the goal. -/
theorem thm_4_2_12_tihtn [Infinite I] [Nonempty A] (hP : P.WF) :
    P.SolvableTI ↔ ∃ n, P.AProgReach n ∧ P.AGoalNode n := by
  constructor
  · intro h
    obtain ⟨trees, as, π, s, hTY, hacyc, hsub, hrun, hg⟩ := (solvableTI_iff_acyc_trees P hP).1 h
    obtain ⟨n, h1, h2, -⟩ := aprog_complete P hP.methods _ P.initANode trees as π s rfl hP.tnI hTY
      (P.init_inv hTY hacyc) hsub hrun hg
    exact ⟨n, h1, h2⟩
  · rintro ⟨n, hn, hg⟩
    obtain ⟨trees, as, ρ, hTY, hsub, hrun, -⟩ := P.aprog_sound hn hg hP.tnI
    exact (solvableTI_iff_trees P hP).2 ⟨trees, as, ρ, n.state, hTY, hsub, hrun, hg.2⟩

/-- **Corollary 4.2.13 (TIHTN part).** The action sequences of goal nodes reached by acyclic
progression are exactly the action sequences of the totally ordered TIHTN solutions. -/
theorem cor_4_2_13_tihtn [Infinite I] [Nonempty A] (hP : P.WF) (π : List A) :
    (∃ n, P.AProgReach n ∧ P.AGoalNode n ∧ n.plan = π) ↔
      ∃ tn ∈ P.SolTI, tn.IsTotallyOrdered ∧ ∃ l, tn.IsLinearization l ∧ tn.IsActionSeq l π := by
  constructor
  · rintro ⟨n, hn, hg, rfl⟩
    obtain ⟨trees, as, ρ, hTY, hsub, hrun, hplan⟩ := P.aprog_sound hn hg hP.tnI
    obtain ⟨tn, hd, hp, l, hl, has⟩ := decomposesTo_of_treesYield hP.methods hP.tnI hTY
    have : ρ = n.plan := by rw [hplan]; rfl
    subst this
    exact P.exists_solTI_of_decomp hP hd hp hl has hsub hrun hg.2
  · rintro ⟨tnS, hS, -, l, hl, has⟩
    obtain ⟨tn, hd, hp, l₀, as, s, hl₀, has₀, hsub, hrun, hg⟩ := P.decomp_of_solTI hP hS hl has
    obtain ⟨trees, hTY⟩ := treesYield_of_decomposesTo hP.tnI hd hp hl₀ has₀
    obtain ⟨trees', as', hTY', hacyc, hsub'⟩ := treesYield_acyc hTY
    obtain ⟨n, h1, h2, h3⟩ := aprog_complete P hP.methods _ P.initANode trees' as' π s rfl hP.tnI
      hTY' (P.init_inv hTY' hacyc) (hsub'.trans hsub) hrun hg
    exact ⟨n, h1, h2, by rw [h3]; rfl⟩

end Problem

end Article

end HTN
