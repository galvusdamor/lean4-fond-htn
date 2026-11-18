import HtnComplexity.Article.TODPPT
import HtnPlanning.Article.OfSyn
import HtnPlanning.Computable.ClassesSound
/-!
# From positive descriptions to well-formed descriptions of the article

`HTN.Article.ofSyn` reads a pair of descriptions of the rest of the development as a description
of the article's model, but a description of the article is well formed (`HTN.Article.ProbDesc.Valid`)
only if every task network lists its strict order itself, not a generating set of it.

* `HTN.Article.normTn` — the **normal form** of a described task network: the same ids and
  labels, and as ordering pairs all pairs `(a, b)` of ids with `a ≺ b` in the described
  ordering.  It denotes the same task network (`HTN.Article.toTaskNetwork_normTn`) and is well
  formed whenever its ids are distinct and labelled once (`HTN.Article.tnValid_normTn`);
* `HTN.Article.artOf` — `HTN.Article.ofSyn` with every network in normal form: it describes the
  same problem (`HTN.Article.toProblem_artOf`), so it is solvable iff the positive description is
  (`HTN.Article.solvable_artOf_iff`), and the classes of the positive problem carry over
  (`HTN.Article.isTailREC_artOf`, `HTN.Article.isACYC_artOf`, `HTN.Article.isTO_tnI_artOf`);
* `HTN.Article.pt_artOf` — it is computed in polynomial time.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime

/-! ### The normal form of a network -/

/-- **The normal form**: all ordered pairs of ids. -/
def normTn (t : TnDesc) : TnDesc :=
  (t.ids, t.ids.flatMap (fun a => (t.ids.filter fun b => TnDesc.ordB t a b).map fun b => (a, b)),
    t.lbl)

theorem mem_ordList_normTn {t : TnDesc} {a b : ℕ} :
    (a, b) ∈ (normTn t).ordList ↔ t.toTaskNetwork.ord a b := by
  simp only [normTn, TnDesc.ordList, List.mem_flatMap, List.mem_map, List.mem_filter,
    Prod.mk.injEq, TnDesc.ordB_iff]
  constructor
  · rintro ⟨a', -, b', ⟨-, h⟩, rfl, rfl⟩; exact h
  · intro h
    exact ⟨a, h.1, b, ⟨h.2.1, h⟩, rfl, rfl⟩

theorem preOrd_normTn {t : TnDesc} {a b : ℕ} : (normTn t).preOrd a b ↔ t.toTaskNetwork.ord a b := by
  constructor
  · intro h
    induction h with
    | single h => exact mem_ordList_normTn.1 h
    | tail _ h ih => exact (TnDesc.toTaskNetwork_wf t).trans ih (mem_ordList_normTn.1 h)
  · exact fun h => .single (mem_ordList_normTn.2 h)

/-- **The normal form denotes the same task network.** -/
theorem toTaskNetwork_normTn (t : TnDesc) : (normTn t).toTaskNetwork = t.toTaskNetwork := by
  refine TaskNetwork.ext' rfl ?_ rfl
  funext a b
  apply propext
  show (normTn t).ordOf a b ↔ t.ordOf a b
  unfold TnDesc.ordOf
  rw [preOrd_normTn, preOrd_normTn]
  have hwf := TnDesc.toTaskNetwork_wf t
  constructor
  · rintro ⟨-, -, h, -⟩; exact h
  · intro h
    exact ⟨h.1, h.2.1, h, fun h' => hwf.irrefl a (hwf.trans h h')⟩

/-- **The normal form is well formed** if the ids are distinct and labelled once each. -/
theorem tnValid_normTn {prim : ℕ → Prop} {t : TnDesc} (hnd : t.ids.Nodup)
    (hperm : (t.lbl.map Prod.fst).Perm t.ids) (hprim : ∀ q ∈ t.lbl, q.2.1 = false → prim q.2.2) :
    TnValid prim (normTn t) := by
  have hwf := TnDesc.toTaskNetwork_wf t
  refine ⟨hnd, fun q hq => ?_, fun a h => ?_, fun a b c h1 h2 => ?_, hperm, hprim⟩
  · obtain ⟨a, b⟩ := q
    have h := mem_ordList_normTn.1 hq
    exact ⟨h.1, h.2.1⟩
  · exact hwf.irrefl a (mem_ordList_normTn.1 h)
  · exact mem_ordList_normTn.2 (hwf.trans (mem_ordList_normTn.1 h1) (mem_ordList_normTn.1 h2))

variable {α : Type} [BEnc α]

theorem pt_normTn {t : α → TnDesc} (ht : PT t) : PT fun a => normTn (t a) := by
  unfold normTn
  have hids : PT fun a => (t a).ids := PT.fst.comp ht
  refine PT.pair hids (PT.pair ?_ (PT.snd.comp (PT.snd.comp ht)))
  exact PT.flatMap hids (PT.map (PT.filter (hids.comp PT.fst)
    (pt_ordB (ht.comp (PT.fst.comp PT.fst)) (PT.snd.comp PT.fst) PT.snd))
    (PT.pair (PT.snd.comp PT.fst) PT.snd))

/-! ### The normal form of a description -/

/-- **A positive description pair as a well-formed description of the article.** -/
def artOf (d : DomDesc) (q : InstDesc) : ProbDesc :=
  ((d.actions.map ofSynAct, d.methods.map fun e => (e.1, normTn e.2)),
    (q.initList, normTn q.tnI, q.goalList, []))

theorem toProblem_artOf (d : DomDesc) (q : InstDesc) :
    (artOf d q).toProblem = (ofSyn d q).toProblem := by
  have hm : {m | ∃ e ∈ (artOf d q).methods, e.toMethod = m} =
      {m | ∃ e ∈ (ofSyn d q).methods, e.toMethod = m} := by
    ext m
    simp only [Set.mem_setOf_eq, ProbDesc.methods, artOf, ofSyn, List.mem_map]
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, by simp [MethodDesc.toMethod, toTaskNetwork_normTn]⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, by simp [MethodDesc.toMethod, toTaskNetwork_normTn]⟩
  have ht : (normTn q.tnI).toTaskNetwork = q.tnI.toTaskNetwork := toTaskNetwork_normTn _
  unfold ProbDesc.toProblem
  congr 1
  congr 1

/-- **The normal form is solvable iff the positive description is.** -/
theorem solvable_artOf_iff (d : DomDesc) (q : InstDesc) :
    (artOf d q).toProblem.Solvable ↔ Syn.Solvable d q := by
  rw [toProblem_artOf]; exact solvable_ofSyn_iff d q

/-! ### Classes -/

section Transfer

universe u u'

variable {F : Type u} {F' : Type u'} {P : HTN.Problem F ℕ ℕ ℕ} {P' : HTN.Problem F' ℕ ℕ ℕ}

theorem reachableName_congr (hm : P'.methods = P.methods) (ht : P'.tnI = P.tnI) {c : ℕ} :
    P'.ReachableName c → P.ReachableName c := by
  intro h
  induction h with
  | tnI ht' hc => exact .tnI (ht ▸ ht') (by rw [← ht]; exact hc)
  | method hm' _ ht' hc ih => exact .method (hm ▸ hm') ih ht' hc

theorem reachableMethod_congr (hm : P'.methods = P.methods) (ht : P'.tnI = P.tnI)
    {m : Method ℕ ℕ ℕ} (h : P'.ReachableMethod m) : P.ReachableMethod m :=
  ⟨hm ▸ h.1, reachableName_congr hm ht h.2⟩

theorem isTailRecursive_congr (hm : P'.methods = P.methods) (ht : P'.tnI = P.tnI)
    (h : P.IsTailRecursive) : P'.IsTailRecursive := by
  obtain ⟨le, hle⟩ := h
  have hr := fun {c} => reachableName_congr hm ht (c := c)
  exact ⟨le, ⟨⟨fun c hc => hle.strat.refl c (hr hc),
    fun c₁ c₂ c₃ h₁ h₂ h₃ => hle.strat.trans c₁ c₂ c₃ (hr h₁) (hr h₂) (hr h₃),
    fun c₁ c₂ h₁ h₂ => hle.strat.total c₁ c₂ (hr h₁) (hr h₂)⟩,
    fun m h => hle.last m (reachableMethod_congr hm ht h),
    fun m h => hle.nonlast m (reachableMethod_congr hm ht h)⟩⟩

theorem isAcyclic_congr (hm : P'.methods = P.methods) (ht : P'.tnI = P.tnI)
    (h : P.IsAcyclic) : P'.IsAcyclic := by
  obtain ⟨le, hle⟩ := h
  have hr := fun {c} => reachableName_congr hm ht (c := c)
  exact ⟨le, ⟨⟨fun c hc => hle.strat.refl c (hr hc),
    fun c₁ c₂ c₃ h₁ h₂ h₃ => hle.strat.trans c₁ c₂ c₃ (hr h₁) (hr h₂) (hr h₃),
    fun c₁ c₂ h₁ h₂ => hle.strat.total c₁ c₂ (hr h₁) (hr h₂)⟩,
    fun c₁ c₂ h₁ h₂ => hle.antisymm c₁ c₂ (hr h₁) (hr h₂),
    fun m h => hle.decreasing m (reachableMethod_congr hm ht h)⟩⟩

end Transfer

theorem toPos_artOf_methods (d : DomDesc) (q : InstDesc) :
    (artOf d q).toProblem.toPos.methods = (Syn.problem d q).methods := by
  rw [toProblem_artOf, toProblem_ofSyn]; rfl

theorem toPos_artOf_tnI (d : DomDesc) (q : InstDesc) :
    (artOf d q).toProblem.toPos.tnI = (Syn.problem d q).tnI := by
  rw [toProblem_artOf, toProblem_ofSyn]; rfl

theorem isTailREC_artOf {d : DomDesc} (q : InstDesc) (hd : d.IsTailRec) :
    (artOf d q).toProblem.IsTailREC :=
  isTailRecursive_congr (toPos_artOf_methods d q) (toPos_artOf_tnI d q) (isTailRecursive_problem hd)

theorem isACYC_artOf {d : DomDesc} (q : InstDesc) (hd : d.IsAcyclic) :
    (artOf d q).toProblem.IsACYC :=
  isAcyclic_congr (toPos_artOf_methods d q) (toPos_artOf_tnI d q) (isAcyclic_problem hd)

theorem isTO_tnI_artOf (d : DomDesc) {q : InstDesc} (hq : q.IsTO) :
    (artOf d q).toProblem.IsTO_tnI := by
  show (artOf d q).toProblem.toPos.tnI.IsTotallyOrdered
  rw [toPos_artOf_tnI]
  exact hq

/-! ### Well-formedness -/

/-- **The normal form is well formed** when the actions have distinct names, every network has
distinct ids labelled once each, and every primitive label is a declared action. -/
theorem valid_artOf {d : DomDesc} {q : InstDesc} (h₁ : (d.actions.map Prod.fst).Nodup)
    (h₂ : q.tnI.ids.Nodup ∧ (q.tnI.lbl.map Prod.fst).Perm q.tnI.ids ∧
      ∀ r ∈ q.tnI.lbl, r.2.1 = false → r.2.2 ∈ d.actions.map Prod.fst)
    (h₃ : ∀ m ∈ d.methods, m.2.ids.Nodup ∧ (m.2.lbl.map Prod.fst).Perm m.2.ids ∧
      ∀ r ∈ m.2.lbl, r.2.1 = false → r.2.2 ∈ d.actions.map Prod.fst) : (artOf d q).Valid := by
  have hnames : (artOf d q).actions.map ActDesc.name = d.actions.map Prod.fst := by
    simp [artOf, ProbDesc.actions, ofSynAct, ActDesc.name, Function.comp_def]
  refine ⟨by rw [hnames]; exact h₁, ?_, ?_⟩
  · unfold ProbDesc.Declared; rw [hnames]
    exact tnValid_normTn h₂.1 h₂.2.1 h₂.2.2
  · intro m hm
    unfold ProbDesc.Declared; rw [hnames]
    simp only [ProbDesc.methods, artOf, List.mem_map] at hm
    obtain ⟨e, he, rfl⟩ := hm
    obtain ⟨a, b, c⟩ := h₃ e he
    exact tnValid_normTn a b c

/-! ### Polynomial time -/

theorem pt_ofSynAct : PT ofSynAct := by
  unfold ofSynAct
  exact PT.pair PT.fst (PT.pair (PT.fst.comp PT.snd) (PT.pair PT.nil
    (PT.pair (PT.fst.comp (PT.snd.comp PT.snd)) (PT.snd.comp (PT.snd.comp PT.snd)))))

theorem pt_artOf {d : α → DomDesc} {q : α → InstDesc} (hd : PT d) (hq : PT q) :
    PT fun a => artOf (d a) (q a) := by
  unfold artOf
  exact PT.pair (PT.pair (PT.map (PT.fst.comp hd) (pt_ofSynAct.comp PT.snd))
    (PT.map (PT.snd.comp hd) (PT.pair (PT.fst.comp PT.snd) (pt_normTn (PT.snd.comp PT.snd)))))
    (PT.pair (PT.fst.comp hq) (PT.pair (pt_normTn (PT.snd.comp (PT.snd.comp hq)))
      (PT.pair (PT.fst.comp (PT.snd.comp hq)) PT.nil)))

end Article

end HTN
