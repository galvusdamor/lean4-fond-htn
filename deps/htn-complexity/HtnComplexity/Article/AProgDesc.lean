import HtnComplexity.Article.ProgCors
/-!
# Acyclic progression on descriptions (TIHTN)

A configuration of acyclic progression (`HTN.Article.ACfg`) adds to a configuration of
progression the **ancestors** of the tasks: for each id the list of the compound names whose
decomposition introduced it (Def. 4.2, acyclic progression).  `HTN.Article.asuccs` lists the
successors: progressing a primitive task, decomposing a compound task by a method none of whose
compound names is an ancestor (the new tasks get the ancestors and the decomposed name), and
inserting an applicable *declared* action (undeclared actions do nothing).

* **`HTN.Article.solvableTI_iff_acfg`** — a well-formed description has a TIHTN solution iff a
  configuration with no tasks and a goal state is reachable (with Thm. 4.2.12, TIHTN part).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- A configuration of acyclic progression: a configuration and the ancestors of the ids. -/
abbrev ACfg : Type := PCfg × List (ℕ × List ℕ)

/-- The ancestors of an id. -/
def ancOf (l : List (ℕ × List ℕ)) (x : ℕ) : List ℕ := (l.lookup x).getD []

/-- No compound name of the method `e` is among `an`. -/
def ancOK (e : MethodDesc) (an : List ℕ) : Bool :=
  e.2.ids.all fun y => !(lblOf e.2 y).1 || !decide ((lblOf e.2 y).2 ∈ an)

/-- The successors at the id `x`: progression or decomposition. -/
def asuccsAt (p : ProbDesc) (c : ACfg) (x : ℕ) : List ACfg :=
  if c.1.2.ordList.all (fun q => q.2 != x) then
    if (lblOf c.1.2 x).1 then
      (p.methods.filter fun e => e.1 == (lblOf c.1.2 x).2 && ancOK e (ancOf c.2 x)).map fun e =>
        ((c.1.1, decDesc c.1.2 x e), (c.2.filter fun q => decide (q.1 ≠ x)) ++
          (freshIds c.1.2.ids e.2.ids.length).map fun n => (n, ((lblOf c.1.2 x).2 :: ancOf c.2 x).dedup))
    else if (runStep p (true, c.1.1) (lblOf c.1.2 x).2).1 then
      [(((runStep p (true, c.1.1) (lblOf c.1.2 x).2).2.dedup, progDesc c.1.2 x),
        c.2.filter fun q => decide (q.1 ≠ x))]
    else []
  else []

/-- The insertions of declared actions. -/
def ainserts (p : ProbDesc) (c : ACfg) : List ACfg :=
  p.actions.flatMap fun a => if (runStep p (true, c.1.1) a.1).1 then
    [(((runStep p (true, c.1.1) a.1).2.dedup, c.1.2), c.2)] else []

/-- **The successors of a configuration of acyclic progression.** -/
def asuccs (p : ProbDesc) (c : ACfg) : List ACfg :=
  c.1.2.ids.flatMap (asuccsAt p c) ++ ainserts p c

/-- The initial configuration: every compound task of `tn_I` is its own ancestor. -/
def initACfg (p : ProbDesc) : ACfg :=
  (initCfg p, p.tnI.ids.map fun x => (x, if (lblOf p.tnI x).1 then [(lblOf p.tnI x).2] else []))

/-- The invariant of the ancestors. -/
structure AncInv (c : ACfg) : Prop where
  keys_mem : ∀ q ∈ c.2, q.1 ∈ c.1.2.ids
  keys_nodup : (c.2.map Prod.fst).Nodup
  vals_nodup : ∀ q ∈ c.2, q.2.Nodup

theorem lookup_map_self {β : Type} {l : List ℕ} {g : ℕ → β} {x : ℕ} (hx : x ∈ l) :
    (l.map fun y => (y, g y)).lookup x = some (g x) :=
  lookup_map_ren (f := id) (fun _ _ _ _ h => h) hx

theorem ancOf_filter_ne {l : List (ℕ × List ℕ)} {x y : ℕ} (h : y ≠ x) :
    ancOf (l.filter fun q => decide (q.1 ≠ x)) y = ancOf l y := by
  unfold ancOf; rw [lookup_filter_ne _ h]

theorem mem_asuccs {p : ProbDesc} {c c' : ACfg} : c' ∈ asuccs p c ↔
    (∃ x ∈ c.1.2.ids, (∀ q ∈ c.1.2.ordList, q.2 ≠ x) ∧
      ((∃ e ∈ p.methods, lblOf c.1.2 x = (true, e.1) ∧ ancOK e (ancOf c.2 x) = true ∧
          c' = ((c.1.1, decDesc c.1.2 x e), (c.2.filter fun q => decide (q.1 ≠ x)) ++
            (freshIds c.1.2.ids e.2.ids.length).map fun n => (n, (e.1 :: ancOf c.2 x).dedup))) ∨
        (∃ a, lblOf c.1.2 x = (false, a) ∧ (runStep p (true, c.1.1) a).1 = true ∧
          c' = (((runStep p (true, c.1.1) a).2.dedup, progDesc c.1.2 x),
            c.2.filter fun q => decide (q.1 ≠ x))))) ∨
    (∃ a ∈ p.actions, (runStep p (true, c.1.1) a.1).1 = true ∧
      c' = (((runStep p (true, c.1.1) a.1).2.dedup, c.1.2), c.2)) := by
  have hall : ∀ x, (c.1.2.ordList.all fun q => q.2 != x) = true ↔ ∀ q ∈ c.1.2.ordList, q.2 ≠ x := by
    intro x; simp [List.all_eq_true]
  unfold asuccs
  rw [List.mem_append]
  refine or_congr ?_ ?_
  · constructor
    · intro h
      obtain ⟨x, hx, hc'⟩ := List.mem_flatMap.1 h
      unfold asuccsAt at hc'
      split_ifs at hc' with hu hb hr
      · obtain ⟨e, hef, rfl⟩ := List.mem_map.1 hc'
        obtain ⟨he, he1⟩ := List.mem_filter.1 hef
        simp only [Bool.and_eq_true, beq_iff_eq] at he1
        have hl : lblOf c.1.2 x = (true, e.1) := Prod.ext hb he1.1.symm
        refine ⟨x, hx, (hall x).1 hu, Or.inl ⟨e, he, hl, he1.2, ?_⟩⟩
        rw [he1.1]
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact ⟨x, hx, (hall x).1 hu, Or.inr ⟨(lblOf c.1.2 x).2, Prod.ext (by simpa using hb) rfl,
          hr, rfl⟩⟩
      · simp at hc'
      · simp at hc'
    · rintro ⟨x, hx, hu, ⟨e, he, hl, hok, rfl⟩ | ⟨a, hl, hr, rfl⟩⟩
      · refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
        unfold asuccsAt
        rw [if_pos ((hall x).2 hu), hl]
        simp only [↓reduceIte]
        exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp [hok]⟩, rfl⟩
      · refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
        unfold asuccsAt
        rw [if_pos ((hall x).2 hu), hl]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_pos hr]
        exact List.mem_singleton.2 rfl
  · unfold ainserts
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨a, ha, hc'⟩
      split_ifs at hc' with hr
      · exact ⟨a, ha, hr, List.mem_singleton.1 hc'⟩
      · simp at hc'
    · rintro ⟨a, ha, hr, rfl⟩
      exact ⟨a, ha, by rw [if_pos hr]; exact List.mem_singleton.2 rfl⟩

/-! ### Invariants -/

theorem ancInv_init (p : ProbDesc) (hp : p.Valid) : AncInv (initACfg p) := by
  refine ⟨fun q hq => ?_, ?_, fun q hq => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq; exact hx
  · simpa [initACfg, List.map_map, Function.comp_def] using hp.tnI.nodup
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
    split_ifs <;> simp

theorem ancInv_dec {s : List ℕ} {d : TnDesc} {l : List (ℕ × List ℕ)} {x : ℕ} {e : MethodDesc}
    (hc : AncInv ((s, d), l)) (L : List ℕ) (hL : L.Nodup) :
    AncInv ((s, decDesc d x e), (l.filter fun q => decide (q.1 ≠ x)) ++
      (freshIds d.ids e.2.ids.length).map fun n => (n, L)) := by
  have hfrd : ∀ y ∈ freshIds d.ids e.2.ids.length, y ∉ d.ids := fun y hy => not_mem_of_mem_freshIds hy
  refine ⟨fun q hq => ?_, ?_, fun q hq => ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨hq, hqx⟩ := List.mem_filter.1 hq
      exact List.mem_append_left _ (List.mem_filter.2 ⟨hc.keys_mem q hq, hqx⟩)
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hq
      exact List.mem_append_right _ hn
  · rw [List.map_append, List.map_map]
    refine List.nodup_append.2 ⟨hc.keys_nodup.sublist (List.filter_sublist.map _), ?_,
      fun a ha b hb e' => ?_⟩
    · rw [show (Prod.fst ∘ fun n => (n, L)) = id from rfl, List.map_id]
      exact freshIds_nodup d.ids e.2.ids.length
    · obtain ⟨qa, hqa, rfl⟩ := List.mem_map.1 ha
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hb
      have e'' : qa.1 = n := e'
      exact hfrd _ hn (by rw [← e'']; exact hc.keys_mem qa (List.mem_filter.1 hqa).1)
  · rcases List.mem_append.1 hq with hq | hq
    · exact hc.vals_nodup q (List.mem_filter.1 hq).1
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hq
      exact hL

theorem ancInv_prog {s s' : List ℕ} {d : TnDesc} {l : List (ℕ × List ℕ)} {x : ℕ}
    (hc : AncInv ((s, d), l)) : AncInv ((s', progDesc d x), l.filter fun q => decide (q.1 ≠ x)) := by
  refine ⟨fun q hq => ?_, hc.keys_nodup.sublist (List.filter_sublist.map _),
    fun q hq => hc.vals_nodup q (List.mem_filter.1 hq).1⟩
  obtain ⟨hq, hqx⟩ := List.mem_filter.1 hq
  exact List.mem_filter.2 ⟨hc.keys_mem q hq, hqx⟩

/-! ### Simulation -/

/-- The ancestor sets of a configuration. -/
def cfgAnc (l : List (ℕ × List ℕ)) (x : ℕ) : Set ℕ := {c | c ∈ ancOf l x}

theorem actions_declared {p : ProbDesc} {a : ActDesc} (ha : a ∈ p.actions) : p.Declared a.1 :=
  List.mem_map.2 ⟨a, ha, rfl⟩

/-- **Soundness of a step.** -/
theorem asuccs_sound {p : ProbDesc} (hp : p.Valid) {c c' : ACfg} (hc : CfgInv c.1) (hca : AncInv c)
    (h : c' ∈ asuccs p c) (π : List ℕ) : CfgInv c'.1 ∧ AncInv c' ∧ ∃ π' tn' an',
      p.toProblem.AProgStep ⟨{f | f ∈ c.1.1}, cfgNet c.1.2, cfgAnc c.2, π⟩
        ⟨{f | f ∈ c'.1.1}, tn', an', π'⟩ ∧ tn'.Agree (cfgNet c'.1.2) ∧
        ∀ y ∈ tn'.T, an' y = cfgAnc c'.2 y := by
  rcases mem_asuccs.1 h with ⟨x, hx, hu, ⟨e, he, hl, hok, rfl⟩ | ⟨a, hl, hr, rfl⟩⟩ |
    ⟨a, ha, hr, rfl⟩
  · have hev := hp.methods e he
    set fr := freshIds c.1.2.ids e.2.ids.length with hfr
    refine ⟨inv_decDesc hc hev, ancInv_dec hca _ (List.nodup_dedup _), π, _, _,
      .decomp (unconstrained_cfgNet hx hu) ⟨e, he, rfl⟩ (by rw [cfgNet_label, hl]; rfl)
        (wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _))
        (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso.symm
        (disjoint_copy _) (fun y hy c' hc' => ?_),
      agree_decDesc ⟨hc.ids_nodup, hc.lbl_mem, hc.lbl_nodup, hc.ord_nodup, List.nodup_nil, hc.wf⟩
        hev, fun y hy => ?_⟩
    · have hy' : y ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hy
      have hlb := label_eq_inr.1 hc'
      have := List.all_eq_true.1 hok y hy'
      rw [hlb] at this
      simpa [cfgAnc] using this
    · show (if y ∈ (cfgNet (copyDesc e.2 fr)).T then Insert.insert (MethodDesc.toMethod e).abstractTask
        (cfgAnc c.2 x) else cfgAnc c.2 y) = cfgAnc _ y
      split_ifs with hyf
      · have hyf' : y ∈ fr := by simpa [cfgNet, copyDesc] using hyf
        have hyd : y ∉ c.1.2.ids := not_mem_of_mem_freshIds hyf'
        ext c'
        simp only [cfgAnc, ancOf, Set.mem_insert_iff, Set.mem_setOf_eq]
        rw [lookup_append', lookup_none_of_not_mem (l := c.2.filter fun q => decide (q.1 ≠ x))
          fun q hq e' => hyd (by rw [← e']; exact hca.keys_mem q (List.mem_filter.1 hq).1),
          lookup_map_self hyf']
        simp [MethodDesc.toMethod]
      · have hyx : y ≠ x := by
          rcases mem_decomposeWith_T.1 hy with ⟨-, h⟩ | h
          · exact h
          · exact absurd h hyf
        have hyf' : y ∉ fr := by simpa [cfgNet, copyDesc] using hyf
        ext c'
        simp only [cfgAnc, ancOf, Set.mem_setOf_eq]
        rw [lookup_append', lookup_filter_ne _ hyx]
        rw [lookup_none_of_not_mem (l := fr.map fun n => (n, (e.1 :: (c.2.lookup x).getD []).dedup))
          fun q hq e' => hyf' (by obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hq; rw [← e']; exact hn)]
        cases c.2.lookup y <;> rfl
  · have hst : (p.toProblem.δ a).apply {f | f ∈ c.1.1} =
        {f | f ∈ (runStep p (true, c.1.1) a).2.dedup} := by
      rw [← runStep_state p true c.1.1 a]; ext f; simp
    refine ⟨inv_progDesc hc hx hu (List.nodup_dedup _), ancInv_prog hca, π ++ [a], _, cfgAnc c.2, ?_,
      agree_progDesc hu, fun y hy => ?_⟩
    · rw [← hst]
      exact .prog (unconstrained_cfgNet hx hu) (by rw [cfgNet_label, hl]; rfl)
        ((runStep_flag p true c.1.1 a).1 hr).2
    · have hyx : y ≠ x := (Finset.mem_erase.1 hy).1
      ext c'
      simp only [cfgAnc, Set.mem_setOf_eq]
      rw [ancOf_filter_ne hyx]
  · have hst : (p.toProblem.δ a.1).apply {f | f ∈ c.1.1} =
        {f | f ∈ (runStep p (true, c.1.1) a.1).2.dedup} := by
      rw [← runStep_state p true c.1.1 a.1]; ext f; simp
    refine ⟨⟨hc.ids_nodup, hc.lbl_mem, hc.lbl_nodup, hc.ord_nodup, List.nodup_dedup _, hc.wf⟩,
      ⟨hca.keys_mem, hca.keys_nodup, hca.vals_nodup⟩,
      π ++ [a.1], _, cfgAnc c.2, ?_, TaskNetwork.Agree.refl _, fun y _ => rfl⟩
    rw [← hst]
    exact .insert ((runStep_flag p true c.1.1 a.1).1 hr).2

/-- **Completeness of a step** (an insertion of an undeclared action is matched by no step). -/
theorem asuccs_complete {p : ProbDesc} (hp : p.Valid) {c : ACfg} (hc : CfgInv c.1) (hca : AncInv c)
    {nd nd' : APNode ℕ ℕ ℕ ℕ} (hstep : p.toProblem.AProgStep nd nd')
    (hst : nd.state = {f | f ∈ c.1.1}) {σ : ℕ → ℕ} (hσ : IsoVia σ nd.net (cfgNet c.1.2))
    (hwf : nd.net.WF) (han : ∀ t ∈ nd.net.T, nd.anc t = cfgAnc c.2 (σ t)) :
    ∃ c', (c' = c ∨ c' ∈ asuccs p c) ∧ nd'.state = {f | f ∈ c'.1.1} ∧ ∃ σ',
      IsoVia σ' nd'.net (cfgNet c'.1.2) ∧ ∀ t ∈ nd'.net.T, nd'.anc t = cfgAnc c'.2 (σ' t) := by
  have hunc : ∀ {x : ℕ}, (cfgNet c.1.2).Unconstrained x → ∀ q ∈ c.1.2.ordList, q.2 ≠ x := by
    intro x hu q hq e
    have h1 : (cfgNet c.1.2).ord q.1 x := by rw [← e]; exact hq
    exact hu.2 q.1 (hc.wf.mem_left h1) h1
  cases hstep with
  | @prog s tn an π t a hu hα happ =>
    dsimp only at hst hσ hwf han ⊢
    have hu' := hσ.unconstrained hu
    have hx : σ t ∈ c.1.2.ids := List.mem_toFinset.1 hu'.1
    have hl : lblOf c.1.2 (σ t) = (false, a) := by
      rw [← toSum_eq_inl, ← cfgNet_label, ← hσ.2.2 t hu.1, hα]
    have hr : (runStep p (true, c.1.1) a).1 = true :=
      (runStep_flag p true c.1.1 a).2 ⟨rfl, hst ▸ happ⟩
    refine ⟨_, Or.inr (mem_asuccs.2 (Or.inl ⟨σ t, hx, hunc hu', Or.inr ⟨a, hl, hr, rfl⟩⟩)), ?_, σ,
      (hσ.progress hu.1).of_agree (agree_progDesc (hunc hu')), fun y hy => ?_⟩
    · rw [hst, ← runStep_state p true c.1.1 a]; ext f; simp
    · obtain ⟨hyt, hy⟩ := TaskNetwork.mem_progress_T.1 hy
      have hne : σ y ≠ σ t := fun e => hyt (hσ.inj hy hu.1 e)
      rw [han y hy]
      ext c'
      simp only [cfgAnc, Set.mem_setOf_eq]
      rw [ancOf_filter_ne hne]
  | @decomp s tn tn'' an π t m hu hm hαt hwf'' hiso hdisj hanc =>
    dsimp only at hst hσ hwf han ⊢
    obtain ⟨e, he, rfl⟩ := hm
    have hev := hp.methods e he
    have hu' := hσ.unconstrained hu
    have hx : σ t ∈ c.1.2.ids := List.mem_toFinset.1 hu'.1
    have hl : lblOf c.1.2 (σ t) = (true, e.1) := by
      rw [← toSum_eq_inr, ← cfgNet_label, ← hσ.2.2 t hu.1, hαt]; rfl
    have hok : ancOK e (ancOf c.2 (σ t)) = true := by
      unfold ancOK
      rw [List.all_eq_true]
      intro y hy
      rcases hly : lblOf e.2 y with ⟨_ | _, n⟩
      · rfl
      · have hyT : y ∈ (MethodDesc.toMethod e).subtasks.T := by
          simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hy
        have := hanc y hyT n (label_eq_inr.2 hly)
        rw [han t hu.1] at this
        simpa [cfgAnc] using this
    set fr := freshIds c.1.2.ids e.2.ids.length with hfr
    obtain ⟨σ', hσ', hnew, hold⟩ := hσ.decomposeWith hwf hc.wf hu.1 hwf''
      (wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _))
      (hiso.trans (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso) hdisj
      (disjoint_copy _)
    refine ⟨_, Or.inr (mem_asuccs.2 (Or.inl ⟨σ t, hx, hunc hu', Or.inl ⟨e, he, hl, hok, rfl⟩⟩)),
      hst, σ', hσ'.of_agree (agree_decDesc ⟨hc.ids_nodup, hc.lbl_mem, hc.lbl_nodup, hc.ord_nodup,
        List.nodup_nil, hc.wf⟩ hev), fun y hy => ?_⟩
    show (if y ∈ tn''.T then Insert.insert (MethodDesc.toMethod e).abstractTask (an t) else an y) = _
    split_ifs with hy''
    · have hyf : σ' y ∈ fr := by simpa [cfgNet, copyDesc] using hnew y hy''
      have hyd : σ' y ∉ c.1.2.ids := not_mem_of_mem_freshIds hyf
      rw [han t hu.1]
      ext c'
      simp only [cfgAnc, ancOf, Set.mem_insert_iff, Set.mem_setOf_eq]
      rw [lookup_append', lookup_none_of_not_mem (l := c.2.filter fun q => decide (q.1 ≠ σ t))
        fun q hq e' => hyd (by rw [← e']; exact hca.keys_mem q (List.mem_filter.1 hq).1),
        lookup_map_self hyf]
      simp [MethodDesc.toMethod, ancOf]
    · have hy' : y ∈ tn.T ∧ y ≠ t := by
        rcases mem_decomposeWith_T.1 hy with h | h
        · exact h
        · exact absurd h hy''
      rw [hold y hy'.1, han y hy'.1]
      have hne : σ y ≠ σ t := fun e' => hy'.2 (hσ.inj hy'.1 hu.1 e')
      have hσy : σ y ∈ c.1.2.ids := List.mem_toFinset.1 (hσ.mem hy'.1)
      have hyf : σ y ∉ fr := fun h => not_mem_of_mem_freshIds h hσy
      ext c'
      simp only [cfgAnc, ancOf, Set.mem_setOf_eq]
      rw [lookup_append', lookup_filter_ne _ hne,
        lookup_none_of_not_mem (l := fr.map fun n => (n, (e.1 :: (c.2.lookup (σ t)).getD []).dedup))
          fun q hq e' => hyf (by obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hq; rw [← e']; exact hn)]
      cases c.2.lookup (σ y) <;> rfl
  | @insert s tn an π a happ =>
    dsimp only at hst hσ hwf han ⊢
    by_cases hd : p.Declared a
    · obtain ⟨x, hxa, rfl⟩ := List.mem_map.1 hd
      have hr : (runStep p (true, c.1.1) x.1).1 = true :=
        (runStep_flag p true c.1.1 x.1).2 ⟨rfl, hst ▸ happ⟩
      refine ⟨_, Or.inr (mem_asuccs.2 (Or.inr ⟨x, hxa, hr, rfl⟩)), ?_, σ, hσ, han⟩
      show (p.toProblem.δ x.1).apply s = _
      rw [hst, ← runStep_state p true c.1.1 x.1]; ext f; simp
    · have hδ : p.toProblem.δ a = ⟨∅, ∅, ∅, ∅⟩ := δ_undeclared hd
      refine ⟨c, Or.inl rfl, ?_, σ, hσ, han⟩
      rw [hδ]; simp [Action.apply, hst]

/-! ### Solutions -/

theorem ancInv_insert {c : ACfg} (h : AncInv c) (s : List ℕ) : AncInv ((s, c.1.2), c.2) :=
  ⟨h.keys_mem, h.keys_nodup, h.vals_nodup⟩

theorem init_anc (p : ProbDesc) {x : ℕ} (hx : x ∈ p.tnI.ids) :
    p.toProblem.initANode.anc x = cfgAnc (initACfg p).2 x := by
  ext c'
  simp only [Problem.initANode, cfgAnc, ancOf, initACfg, Set.mem_setOf_eq]
  rw [lookup_map_self hx]
  show p.tnI.label x = Sum.inr c' ↔ _
  rw [label_eq_inr]
  rcases hl : lblOf p.tnI x with ⟨_ | _, n⟩ <;> simp [eq_comm]

/-- **Reachable configurations stand for nodes reached by acyclic progression.** -/
theorem acfgReach_sound {p : ProbDesc} (hp : p.Valid) {c : ACfg}
    (hrc : Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c) (initACfg p) c) :
    CfgInv c.1 ∧ AncInv c ∧ ∃ nd, p.toProblem.AProgReach nd ∧ nd.state = {f | f ∈ c.1.1} ∧
      nd.net.Agree (cfgNet c.1.2) ∧ ∀ x ∈ nd.net.T, nd.anc x = cfgAnc c.2 x := by
  induction hrc with
  | refl =>
    refine ⟨inv_initCfg hp, ancInv_init p hp, _, .refl, ?_, agree_initCfg hp, fun x hx => ?_⟩
    · ext f; simp [initACfg, initCfg, Problem.initANode, ProbDesc.toProblem]
    · exact init_anc p (by simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork, Problem.initANode]
        using hx)
  | @tail c₁ c₂ _ hs ih =>
    obtain ⟨hc, hca, nd, hnd, hst, hag, han⟩ := ih
    obtain ⟨hc', hca', π', tn', an', hstep, hag', han'⟩ := asuccs_sound hp hc hca hs nd.plan
    obtain ⟨B', an'', hstep', hagB, hanB⟩ := Problem.AProgStep.agree p.toProblem hstep hag.symm
      (an := nd.anc) (fun x hx => (han x (hag.1 ▸ hx)).symm)
    refine ⟨hc', hca', ⟨{f | f ∈ c₂.1.1}, B', an'', π'⟩, hnd.tail ?_, rfl, hagB.symm.trans hag',
      fun x hx => ?_⟩
    · have : nd = ⟨{f | f ∈ c₁.1.1}, nd.net, nd.anc, nd.plan⟩ := by rw [← hst]
      rw [this]
      exact hstep'
    · have hx' : x ∈ tn'.T := hagB.1 ▸ hx
      exact (hanB x hx').symm.trans (han' x hx')

/-- **TIHTN plan existence via acyclic progression on descriptions.** -/
theorem solvableTI_iff_acfg {p : ProbDesc} (hp : p.Valid) :
    p.toProblem.SolvableTI ↔ ∃ c, Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c)
      (initACfg p) c ∧ c.1.2.ids = [] ∧ goalB p c.1.1 = true := by
  rw [Problem.thm_4_2_12_tihtn p.toProblem (wf_toProblem p)]
  constructor
  · rintro ⟨nd, hr, hg⟩
    have key : ∀ nd, p.toProblem.AProgReach nd → ∃ c σ, Relation.ReflTransGen
        (fun c c' => c' ∈ asuccs p c) (initACfg p) c ∧ CfgInv c.1 ∧ AncInv c ∧
        nd.state = {f | f ∈ c.1.1} ∧ IsoVia σ nd.net (cfgNet c.1.2) ∧ nd.net.WF ∧
        ∀ t ∈ nd.net.T, nd.anc t = cfgAnc c.2 (σ t) := by
      intro nd hr
      induction hr with
      | refl =>
        refine ⟨initACfg p, id, .refl, inv_initCfg hp, ancInv_init p hp, ?_,
          isoVia_id_of_agree (agree_initCfg hp), (wf_toProblem p).tnI, fun x hx => ?_⟩
        · ext f; simp [initACfg, initCfg, Problem.initANode, ProbDesc.toProblem]
        · exact init_anc p (by simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork, Problem.initANode]
            using hx)
      | @tail n₁ n₂ _ hs ih =>
        obtain ⟨c, σ, hrc, hc, hca, hst, hσ, hwf, han⟩ := ih
        obtain ⟨c', hc', hst', σ', hσ', han'⟩ := asuccs_complete hp hc hca hs hst hσ hwf han
        have hwf' : n₂.net.WF := by
          cases hs with
          | prog hu _ _ => exact TaskNetwork.progress_wf hwf hu
          | decomp hu hm hα hwf'' _ hdisj _ => exact decomposeWith_wf hwf hwf'' hdisj
          | insert _ => exact hwf
        rcases hc' with rfl | hc'
        · exact ⟨c', σ', hrc, hc, hca, hst', hσ', hwf', han'⟩
        · obtain ⟨hci, hcai, -⟩ := asuccs_sound hp hc hca hc' []
          exact ⟨c', σ', hrc.tail hc', hci, hcai, hst', hσ', hwf', han'⟩
    obtain ⟨c, σ, hrc, -, -, hst, hσ, -, -⟩ := key nd hr
    refine ⟨c, hrc, ?_, (goalB_iff p c.1.1).2 (hst ▸ hg.2)⟩
    have hT : (cfgNet c.1.2).T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨a, ha, -⟩ := hσ.surj hy
      rw [hg.1] at ha
      simp at ha
    simpa [cfgNet] using hT
  · rintro ⟨c, hrc, hids, hgoal⟩
    obtain ⟨-, -, nd, hnd, hst, hag, -⟩ := acfgReach_sound hp hrc
    refine ⟨nd, hnd, ?_, hst ▸ (goalB_iff p c.1.1).1 hgoal⟩
    rw [hag.1]
    simp [cfgNet, hids]

end Article

end HTN
