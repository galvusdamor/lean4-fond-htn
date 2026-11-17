import FondHtn.MPStrong.Prog
import FondHtn.Lang.Desc
import FondHtn.Transfer.DetDesc
import FondHtn.Alt.ExpTime
import HtnComplexity.Article.ProgDescSize
/-!
# The progression game on descriptions

The progression game `FOND.Problem.MPProg` (`FondHtn/MPStrong/Prog.lean`) played on
*descriptions*: a node is a tag and a configuration `HTN.Article.PCfg` (a state as a list of
facts and a network description, as in the deterministic progression search of
`HtnComplexity/Article/ProgDesc*.lean`).

* existential nodes `((false, 0), c)`: the successors are the decompositions of an unconstrained
  compound task (with the same fresh-id convention `HTN.Article.decDesc` as the deterministic
  search) and the *choices* `((true, x), c)` of an unconstrained applicable primitive task `x`;
* universal nodes `((true, x), c)`: the successors are the configurations after executing `x`,
  one per effect of its action (`FOND.MPS.outs`);
* accepting nodes: existential nodes with no task left.

The network component only moves as in the deterministic progression search on the *skeleton*
description `FOND.MPS.skDesc p` (same methods and initial network, actions without preconditions
and effects), so the size bound `HTN.Article.sz_cfg_le` for progression bounds applies verbatim
to every reachable network; states are duplicate-free lists of facts of the description.

* `FOND.MPS.sound` / `FOND.MPS.complete` — winning reachable nodes are exactly the nodes won in
  the semantic progression game;
* **`FOND.MPS.inExpTime_planExMP_strong`** — for a class `Y` with polynomial certificates checked
  in polynomial time and polynomial progression bounds (of the skeleton), strong method-based
  plan existence `PlanExMP .strong Y` is in `EXPTIME` (via the AND-OR game theorem
  `HTN.Syn.PolyDom.inExpTime_codeLang_of_andOr`, i.e. `APSPACE ⊆ EXPTIME`).
-/

namespace FOND

namespace MPS

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime

/-! ## The skeleton description -/

/-- The skeleton action of an action description: no preconditions, no effects. -/
def skAct (a : FActDesc) : ActDesc := (a.1, [], [], [], [])

/-- **The skeleton description**: the methods and the initial task network of `p`, every action
without preconditions and effects, empty initial state and goal. -/
def skDesc (p : FProbDesc) : ProbDesc := ((p.actions.map skAct, p.methods), ([], p.tnI, [], []))

theorem skDesc_names (p : FProbDesc) :
    (skDesc p).actions.map ActDesc.name = p.actions.map FActDesc.name := by
  simp [skDesc, ProbDesc.actions, skAct, ActDesc.name, FActDesc.name]

theorem skDesc_declared (p : FProbDesc) (n : ℕ) : (skDesc p).Declared n ↔ p.Declared n := by
  unfold ProbDesc.Declared FProbDesc.Declared; rw [skDesc_names]

theorem skDesc_valid {p : FProbDesc} (hp : p.Valid) : (skDesc p).Valid where
  names_nodup := by rw [skDesc_names]; exact hp.names_nodup
  tnI := hp.tnI.mono fun n hn => (skDesc_declared p n).2 hn
  methods := fun m hm => (hp.methods m hm).mono fun n hn => (skDesc_declared p n).2 hn

theorem actDescOf_skDesc (p : FProbDesc) (a : ℕ) : (actDescOf (skDesc p) a).2 = ([], [], [], []) := by
  unfold actDescOf
  cases h : (skDesc p).actions.filter (fun x => x.1 == a) with
  | nil => rfl
  | cons x l =>
    have hx : x ∈ (skDesc p).actions := (List.mem_filter.1 (h ▸ List.mem_cons_self)).1
    simp only [skDesc, ProbDesc.actions, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rfl

theorem runStep_skDesc (p : FProbDesc) (a : ℕ) : runStep (skDesc p) (true, []) a = (true, []) := by
  simp [runStep, actDescOf_skDesc]

theorem sz_skAct_le (a : FActDesc) : sz (skAct a) ≤ sz a + 1 := by
  obtain ⟨n, l₁, l₂, l₃⟩ := a
  simp only [skAct, sz_prod, sz_nil]
  have h1 : 1 ≤ sz l₁ := by cases l₁ <;> simp [sz_nil, sz_cons]
  have h2 : 1 ≤ sz l₂ := by cases l₂ <;> simp [sz_nil, sz_cons]
  have h3 : 1 ≤ sz l₃ := by cases l₃ <;> simp [sz_nil, sz_cons]
  omega

theorem sz_map_skAct_le (l : List FActDesc) : sz (l.map skAct) ≤ 2 * sz l := by
  induction l with
  | nil => simp [sz_nil]
  | cons a l ih =>
    rw [List.map_cons, sz_cons, sz_cons]
    have := sz_skAct_le a
    omega

theorem sz_skDesc_le (p : FProbDesc) : sz (skDesc p) ≤ 2 * sz p := by
  obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
  simp only [skDesc, FProbDesc.actions, FProbDesc.methods, FProbDesc.tnI, sz_prod, sz_nil]
  have := sz_map_skAct_le acts
  have h1 : 1 ≤ sz init := by cases init <;> simp [sz_nil, sz_cons]
  have h2 : 1 ≤ sz ms := by cases ms <;> simp [sz_nil, sz_cons]
  have h3 : 1 ≤ sz tn := by
    obtain ⟨i, o, l⟩ := tn
    rw [sz_prod]; cases i <;> simp [sz_nil, sz_cons]; omega
  omega

/-! ## Actions of FOND descriptions -/

/-- The description of the action named `a` (the convention of `FOND.FProbDesc.δ` for undeclared
names: the no-op with one empty effect). -/
def fActOf (p : FProbDesc) (a : ℕ) : FActDesc :=
  ((p.actions.filter fun x : FActDesc => x.1 == a) ++ [(a, [], [], [([], [])])]).headI

theorem headI_filter_append {α : Type} [Inhabited α] (L : List α) (f : α → Bool) (d : α) :
    ((L.filter f) ++ [d]).headI = match L.find? f with
      | some x => x
      | none => d := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases hx : f x = true
    · simp [hx]
    · simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      exact ih

theorem toAction_fActOf (p : FProbDesc) (a : ℕ) : (fActOf p a).toAction = p.δ a := by
  unfold fActOf FProbDesc.δ
  rw [headI_filter_append]
  have hf : (fun x : FActDesc => x.1 == a) = (fun x : FActDesc => x.name == a) := rfl
  rw [hf]
  cases p.actions.find? (fun x => x.name == a) with
  | some x => rfl
  | none =>
    refine Action.ext' ?_ ?_ ?_
    · ext f; simp [FActDesc.toAction]
    · ext f; simp [FActDesc.toAction]
    · ext e; simp [FActDesc.toAction, FActDesc.effs]

/-- Applicability of the action named `a` in the state `s`. -/
def fApp (p : FProbDesc) (a : ℕ) (s : List ℕ) : Bool :=
  (fActOf p a).2.1.all (fun f => decide (f ∈ s)) && (fActOf p a).2.2.1.all (fun f => !decide (f ∈ s))

theorem fApp_iff (p : FProbDesc) (a : ℕ) (s : List ℕ) :
    fApp p a s = true ↔ (p.δ a).Applicable {f | f ∈ s} := by
  rw [← toAction_fActOf]
  simp only [fApp, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, Action.Applicable, FActDesc.toAction]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => h1 f hf, Set.disjoint_left.2 fun f hf => h2 f hf⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => h1 hf, fun f hf => Set.disjoint_left.1 h2 hf⟩

/-- The successor states after executing the action named `a` in `s`, one per effect. -/
def outs (p : FProbDesc) (a : ℕ) (s : List ℕ) : List (List ℕ) :=
  (fActOf p a).2.2.2.map fun y => (s.filter (fun f => !decide (f ∈ y.2)) ++ y.1).dedup

theorem outs_sound {p : FProbDesc} {a : ℕ} {s s' : List ℕ} (h : s' ∈ outs p a s) :
    {f | f ∈ s'} ∈ (p.δ a).outcomes {f | f ∈ s} := by
  rw [← toAction_fActOf]
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
  refine ⟨({f | f ∈ y.1}, {f | f ∈ y.2}), ⟨y, hy, rfl⟩, ?_⟩
  ext f
  simp [Action.applyEff]

theorem outs_complete {p : FProbDesc} {a : ℕ} {s : List ℕ} {S' : Set ℕ}
    (h : S' ∈ (p.δ a).outcomes {f | f ∈ s}) : ∃ s' ∈ outs p a s, {f | f ∈ s'} = S' := by
  rw [← toAction_fActOf] at h
  obtain ⟨e, ⟨y, hy, rfl⟩, rfl⟩ := h
  refine ⟨_, List.mem_map.2 ⟨y, hy, rfl⟩, ?_⟩
  ext f
  simp [Action.applyEff]

theorem nodup_of_mem_outs {p : FProbDesc} {a : ℕ} {s s' : List ℕ} (h : s' ∈ outs p a s) :
    s'.Nodup := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
  exact List.nodup_dedup _

/-! ## The game -/

/-- A node: a tag (`(false, 0)` existential, `(true, x)` universal after choosing the primitive
task `x`) and a configuration. -/
abbrev GNode : Type := (Bool × ℕ) × PCfg

/-- `x` has no predecessor in the listed order. -/
def unc (d : TnDesc) (x : ℕ) : Bool := d.ordList.all fun q => q.2 != x

theorem unc_iff (d : TnDesc) (x : ℕ) : unc d x = true ↔ ∀ q ∈ d.ordList, q.2 ≠ x := by
  simp [unc, List.all_eq_true]

/-- The decompositions of the task `x`. -/
def decSuccsAt (p : FProbDesc) (d : TnDesc) (x : ℕ) : List TnDesc :=
  if unc d x && (lblOf d x).1 then
    (p.methods.filter fun e => e.1 == (lblOf d x).2).map fun e => decDesc d x e
  else []

/-- `x` is an unconstrained primitive task whose action is applicable. -/
def primOk (p : FProbDesc) (c : PCfg) (x : ℕ) : Bool :=
  unc c.2 x && !(lblOf c.2 x).1 && fApp p (lblOf c.2 x).2 c.1

/-- **The successors of a node.** -/
def nodeSuccs (p : FProbDesc) (g : GNode) : List GNode :=
  if g.1.1 then
    (outs p (lblOf g.2.2 g.1.2).2 g.2.1).map fun s' => ((false, 0), (s', progDesc g.2.2 g.1.2))
  else
    (g.2.2.ids.flatMap (decSuccsAt p g.2.2)).map (fun d' => ((false, 0), (g.2.1, d'))) ++
      (g.2.2.ids.filter (primOk p g.2)).map fun x => ((true, x), g.2)

theorem mem_nodeSuccs_out {p : FProbDesc} {x : ℕ} {c : PCfg} {s' : List ℕ}
    (h : s' ∈ outs p (lblOf c.2 x).2 c.1) :
    ((false, 0), (s', progDesc c.2 x)) ∈ nodeSuccs p ((true, x), c) := by
  simp only [nodeSuccs, ↓reduceIte]
  exact List.mem_map.2 ⟨s', h, rfl⟩

theorem mem_nodeSuccs_dec {p : FProbDesc} {c : PCfg} {x : ℕ} (hx : x ∈ c.2.ids)
    (hu : unc c.2 x = true) {e : MethodDesc} (he : e ∈ p.methods) (hl : lblOf c.2 x = (true, e.1)) :
    ((false, 0), (c.1, decDesc c.2 x e)) ∈ nodeSuccs p ((false, 0), c) := by
  simp only [nodeSuccs, Bool.false_eq_true, ↓reduceIte]
  refine List.mem_append_left _ (List.mem_map.2 ⟨decDesc c.2 x e, List.mem_flatMap.2 ⟨x, hx, ?_⟩,
    rfl⟩)
  simp only [decSuccsAt, hu, hl, Bool.and_self, ↓reduceIte]
  exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp⟩, rfl⟩

theorem mem_nodeSuccs_prim {p : FProbDesc} {c : PCfg} {x : ℕ} (hx : x ∈ c.2.ids)
    (h : primOk p c x = true) : ((true, x), c) ∈ nodeSuccs p ((false, 0), c) := by
  simp only [nodeSuccs, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_right _ (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, h⟩, rfl⟩)

theorem nodeSuccs_univ {p : FProbDesc} {x : ℕ} {c : PCfg} {g' : GNode}
    (h : g' ∈ nodeSuccs p ((true, x), c)) :
    ∃ s' ∈ outs p (lblOf c.2 x).2 c.1, g' = ((false, 0), (s', progDesc c.2 x)) := by
  simp only [nodeSuccs, ↓reduceIte] at h
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 h
  exact ⟨s', hs', rfl⟩

theorem nodeSuccs_ex {p : FProbDesc} {y : ℕ} {c : PCfg} {g' : GNode}
    (h : g' ∈ nodeSuccs p ((false, y), c)) :
    (∃ x ∈ c.2.ids, unc c.2 x = true ∧ ∃ e ∈ p.methods, lblOf c.2 x = (true, e.1) ∧
      g' = ((false, 0), (c.1, decDesc c.2 x e))) ∨
    (∃ x ∈ c.2.ids, primOk p c x = true ∧ g' = ((true, x), c)) := by
  simp only [nodeSuccs, Bool.false_eq_true, ↓reduceIte] at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 h
    obtain ⟨x, hx, hd'⟩ := List.mem_flatMap.1 hd'
    unfold decSuccsAt at hd'
    split_ifs at hd' with hc
    · simp only [Bool.and_eq_true] at hc
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd'
      obtain ⟨he, he1⟩ := List.mem_filter.1 he
      refine Or.inl ⟨x, hx, hc.1, e, he, Prod.ext hc.2 (beq_iff_eq.1 he1).symm, rfl⟩
    · simp at hd'
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    obtain ⟨hx, hok⟩ := List.mem_filter.1 hx
    exact Or.inr ⟨x, hx, hok, rfl⟩

/-! ## Reachable nodes -/

section Reach

set_option linter.unusedSectionVars false

instance decEqTnDescG : DecidableEq TnDesc := inferInstance
instance decEqPCfgG : DecidableEq PCfg := inferInstance
instance decEqGNode : DecidableEq GNode := inferInstance

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

/-- The initial configuration: the initial state and network. -/
def initF (p : FProbDesc) : PCfg := (p.init.dedup, (p.tnI.ids, p.tnI.ordList.dedup, p.tnI.lbl))

theorem initCfg_skDesc (p : FProbDesc) : initCfg (skDesc p) = ([], (initF p).2) := by
  simp [initCfg, initF, skDesc, ProbDesc.init, ProbDesc.tnI, FProbDesc.tnI]

/-- The initial test: well formed, certified with a certificate of size at most `R p`, and the
initial node. -/
def gInit (cB : FProbDesc × β → Bool) (R : FProbDesc → ℕ) (x : FProbDesc × (β × GNode)) : Bool :=
  FProbDesc.validB x.1 && cB (x.1, x.2.1) && decide (sz x.2.1 ≤ R x.1) &&
    decide (x.2.2 = ((false, 0), initF x.1))

/-- Accepting nodes: existential, no task left. -/
def gAcc (x : FProbDesc × (β × GNode)) : Bool := !x.2.2.1.1 && x.2.2.2.2.ids.isEmpty

/-- Universal nodes. -/
def gUni (x : FProbDesc × (β × GNode)) : Bool := x.2.2.1.1

/-- A step: the certificate is kept, the node moves to a successor. -/
def gStep (x : FProbDesc × (β × GNode) × (β × GNode)) : Bool :=
  decide (x.2.2.1 = x.2.1.1) && decide (x.2.2.2 ∈ nodeSuccs x.1 x.2.1.2)

/-- The nodes reachable from the initial node with the certificate `b`. -/
def GReach (p : FProbDesc) (b : β) (g : β × GNode) : Prop :=
  Relation.ReflTransGen (fun g g' => gStep (p, g, g') = true) (b, ((false, 0), initF p)) g

/-- The facts of a description: the initial state and the added facts. -/
def ffacts (p : FProbDesc) : List ℕ := p.init ++ p.actions.flatMap fun a => a.effs.flatMap Prod.fst

/-- **The invariant of reachable nodes.** -/
structure GInv (p : FProbDesc) (b : β) (g : β × GNode) : Prop where
  cert : g.1 = b
  inv : CfgInv g.2.2
  tagT : g.2.1.1 = true → g.2.1.2 ∈ g.2.2.2.ids ∧ primOk p g.2.2 g.2.1.2 = true
  tagF : g.2.1.1 = false → g.2.1.2 = 0
  skel : Relation.ReflTransGen (fun c c' => c' ∈ succs (skDesc p) c) (initCfg (skDesc p))
    ([], g.2.2.2)
  facts : ∀ f ∈ g.2.2.1, f ∈ ffacts p

theorem headI_mem_of_ne_nil {α : Type} [Inhabited α] {l : List α} (h : l ≠ []) : l.headI ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => simp

theorem mem_ffacts_of_effect {p : FProbDesc} {a : ℕ} {y : List ℕ × List ℕ}
    (hy : y ∈ (fActOf p a).2.2.2) {f : ℕ} (hf : f ∈ y.1) : f ∈ ffacts p := by
  have hm := headI_mem_of_ne_nil (l := (p.actions.filter fun x : FActDesc => x.1 == a) ++
    [(a, [], [], [([], [])])]) (by simp)
  rcases List.mem_append.1 hm with hm | hm
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨_, (List.mem_filter.1 hm).1, ?_⟩)
    exact List.mem_flatMap.2 ⟨y, hy, hf⟩
  · rw [List.mem_singleton] at hm
    have hy' : y ∈ (fActOf p a).2.2.2 := hy
    unfold fActOf at hy'
    rw [hm] at hy'
    simp only [List.mem_singleton] at hy'
    subst hy'
    simp at hf

theorem lbl_false_of_primOk {p : FProbDesc} {c : PCfg} {x : ℕ} (h : primOk p c x = true) :
    lblOf c.2 x = (false, (lblOf c.2 x).2) ∧ unc c.2 x = true ∧
      fApp p (lblOf c.2 x).2 c.1 = true := by
  simp only [primOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨Prod.ext h.1.2 rfl, h.1.1, h.2⟩

theorem gInv_init {p : FProbDesc} (hp : p.Valid) (b : β) :
    GInv p b (b, ((false, 0), initF p)) := by
  have h0 := inv_initCfg (skDesc_valid hp)
  rw [initCfg_skDesc] at h0
  refine ⟨rfl, ⟨h0.ids_nodup, h0.lbl_mem, h0.lbl_nodup, h0.ord_nodup, List.nodup_dedup _, h0.wf⟩,
    fun h => absurd h (by simp), fun _ => rfl, ?_, fun f hf => ?_⟩
  · rw [initCfg_skDesc]
  · exact List.mem_append_left _ (List.mem_dedup.1 hf)

theorem gInv_step {p : FProbDesc} (hp : p.Valid) {b : β} {g g' : β × GNode} (hg : GInv p b g)
    (hs : gStep (p, g, g') = true) : GInv p b g' := by
  obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
  obtain ⟨hcert, hinv, htT, htF, hsk, hfa⟩ := hg
  simp only at hcert hinv htT htF hsk hfa
  subst hcert
  simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨hb, hmem⟩ := hs
  obtain ⟨b', g'⟩ := g'
  simp only at hb hmem
  subst hb
  cases tg with
  | true =>
    obtain ⟨hx, hok⟩ := htT rfl
    obtain ⟨hl, hu, -⟩ := lbl_false_of_primOk hok
    obtain ⟨s', hs', rfl⟩ := nodeSuccs_univ hmem
    have hu' := (unc_iff _ _).1 hu
    refine ⟨rfl, inv_progDesc hinv hx hu' (nodup_of_mem_outs hs'), fun h => absurd h (by simp),
      fun _ => rfl, hsk.tail ?_, fun f hf => ?_⟩
    · refine mem_succs.2 ⟨y, hx, hu', Or.inr ⟨(lblOf d y).2, hl, ?_, ?_⟩⟩
      · rw [runStep_skDesc]
      · rw [runStep_skDesc]; rfl
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs'
      rcases List.mem_append.1 (List.mem_dedup.1 hf) with hf | hf
      · exact hfa f (List.mem_filter.1 hf).1
      · exact mem_ffacts_of_effect hz hf
  | false =>
    rcases nodeSuccs_ex hmem with ⟨x, hx, hu, e, he, hl, rfl⟩ | ⟨x, hx, hok, rfl⟩
    · refine ⟨rfl, inv_decDesc hinv (hp.methods e he), fun h => absurd h (by simp), fun _ => rfl,
        hsk.tail ?_, hfa⟩
      exact mem_succs.2 ⟨x, hx, (unc_iff _ _).1 hu, Or.inl ⟨e, he, hl, rfl⟩⟩
    · exact ⟨rfl, hinv, fun _ => ⟨hx, hok⟩, fun h => absurd h (by simp), hsk, hfa⟩

theorem gInv_of_reach {p : FProbDesc} (hp : p.Valid) {b : β} {g : β × GNode}
    (h : GReach p b g) : GInv p b g := by
  induction h with
  | refl => exact gInv_init hp b
  | tail _ hs ih => exact gInv_step hp ih hs

/-! ### Sizes -/

theorem length_flatMap_le {α γ : Type} [BEnc α] (l : List α) (g : α → List γ)
    (h : ∀ a ∈ l, (g a).length ≤ sz a) : (l.flatMap g).length ≤ sz l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, sz_cons]
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    omega

theorem sz_le_of_mem_ffacts {p : FProbDesc} {f : ℕ} (h : f ∈ ffacts p) : sz f ≤ sz p := by
  obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
  have hp : sz (((acts, ms), (init, tn)) : FProbDesc) = sz acts + sz ms + sz init + sz tn := by
    simp only [sz_prod]; ring
  rw [hp]
  simp only [ffacts, FProbDesc.init, FProbDesc.actions, List.mem_append, List.mem_flatMap] at h
  rcases h with h | ⟨a, ha, y, hy, hf⟩
  · have := sz_le_of_mem h; omega
  · have h1 := sz_le_of_mem hf
    have h2 : sz y.1 ≤ sz y := by rw [show sz y = sz y.1 + sz y.2 from sz_prod _ _]; omega
    have h3 := sz_le_of_mem hy
    have h4 : sz a.effs ≤ sz a := by
      obtain ⟨n, l₁, l₂, l₃⟩ := a
      simp only [FActDesc.effs, sz_prod]; omega
    have h5 := sz_le_of_mem ha
    omega

theorem length_ffacts_le (p : FProbDesc) : (ffacts p).length ≤ sz p := by
  obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
  have hp : sz (((acts, ms), (init, tn)) : FProbDesc) = sz acts + sz ms + sz init + sz tn := by
    simp only [sz_prod]; ring
  rw [hp]
  simp only [ffacts, FProbDesc.init, FProbDesc.actions, List.length_append]
  have h1 := length_le_sz init
  have h2 := length_flatMap_le acts (fun a => a.effs.flatMap Prod.fst) fun a _ => by
    show (a.effs.flatMap Prod.fst).length ≤ sz a
    have h3 := length_flatMap_le a.effs Prod.fst fun y _ => by
      have := length_le_sz y.1
      rw [show sz y = sz y.1 + sz y.2 from sz_prod _ _]; omega
    have h4 : sz a.effs ≤ sz a := by
      obtain ⟨n, l₁, l₂, l₃⟩ := a
      simp only [FActDesc.effs, sz_prod]; omega
    omega
  omega

theorem sz_state_le {p : FProbDesc} {s : List ℕ} (hnd : s.Nodup) (hf : ∀ f ∈ s, f ∈ ffacts p) :
    sz s ≤ sz p * (2 * sz p + 2) + 1 := by
  have h1 := sz_list_le (l := s) (K := sz p) fun f hf' => sz_le_of_mem_ffacts (hf f hf')
  have h2 : s.length ≤ sz p := (length_le_of_nodup_sub hnd hf).trans (length_ffacts_le p)
  have h3 : s.length * (2 * sz p + 2) ≤ sz p * (2 * sz p + 2) := Nat.mul_le_mul_right _ h2
  omega

/-- The size of a node with the invariant. -/
def nodeBound (n S : ℕ) : ℕ := 2 + sz (0 : ℕ) + 2 * (40 * (n + 2 * S + 1) ^ 3) + (S * (2 * S + 2) + 1)

/-- **The size of a reachable node**: certificate plus a polynomial in the progression bound and
the size of the description. -/
theorem sz_le_of_gInv {p : FProbDesc} (hp : p.Valid) {n : ℕ}
    (hb : (skDesc p).toProblem.IsHTNProgBound n) {b : β} {g : β × GNode} (h : GInv p b g) :
    sz g ≤ sz b + nodeBound n (sz p) := by
  obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
  obtain ⟨hcert, hinv, htT, htF, hsk, hfa⟩ := h
  simp only at hcert hinv htT htF hsk hfa
  subst hcert
  have hcfg : sz (([] : List ℕ), d) ≤ 40 * (n + sz (skDesc p) + 1) ^ 3 :=
    sz_cfg_le (skDesc_valid hp) hb hsk
  have hd : sz d ≤ 40 * (n + sz (skDesc p) + 1) ^ 3 := by
    rw [sz_prod, sz_nil] at hcfg; omega
  have hq := sz_skDesc_le p
  have hpow : (n + sz (skDesc p) + 1) ^ 3 ≤ (n + 2 * sz p + 1) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hst : sz s ≤ sz p * (2 * sz p + 2) + 1 := sz_state_le hinv.st_nodup hfa
  have htag : sz (tg, y) ≤ 1 + sz d + sz (0 : ℕ) := by
    rw [sz_prod, sz_bool]
    cases tg with
    | true =>
      have h1 : sz y ≤ sz d.ids := sz_le_of_mem (htT rfl).1
      have h2 : sz d.ids ≤ sz d := by rw [sz_tnDesc]; omega
      omega
    | false => rw [htF rfl]; omega
  have hsz : sz ((b₀, ((tg, y), (s, d))) : β × GNode) = sz b₀ + sz (tg, y) + sz s + sz d := by
    simp only [sz_prod]; ring
  rw [hsz]
  unfold nodeBound
  omega

end Reach

/-! ## Soundness and completeness -/

section Correct

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

theorem isoVia_art {σ : ℕ → ℕ} {tn u : TaskNetwork ℕ ℕ ℕ} (h : HTN.Article.IsoVia σ tn u) :
    HTN.TaskNetwork.IsoVia σ tn u := h

theorem isoVia_of_art {σ : ℕ → ℕ} {tn u : TaskNetwork ℕ ℕ ℕ} (h : HTN.TaskNetwork.IsoVia σ tn u) :
    HTN.Article.IsoVia σ tn u := h

theorem unc_of_isoVia {σ : ℕ → ℕ} {tn : TaskNetwork ℕ ℕ ℕ} {s : List ℕ} {d : TnDesc}
    (hinv : CfgInv (s, d)) (hσ : HTN.TaskNetwork.IsoVia σ tn (cfgNet d)) {t : ℕ}
    (hu : tn.Unconstrained t) : σ t ∈ d.ids ∧ ∀ q ∈ d.ordList, q.2 ≠ σ t := by
  have hu' := hσ.unconstrained hu
  refine ⟨List.mem_toFinset.1 hu'.1, fun q hq e => ?_⟩
  have h1 : (cfgNet d).ord q.1 (σ t) := by rw [← e]; exact hq
  exact hu'.2 q.1 (hinv.wf.mem_left h1) h1

/-- A decomposition on descriptions is a semantic decomposition step (up to agreement). -/
theorem mpProg_of_dec {p : FProbDesc} (hp : p.Valid) {s : List ℕ} {d : TnDesc} {x : ℕ}
    {e : MethodDesc} {S : Set ℕ} (hinv : CfgInv (s, d)) (hx : x ∈ d.ids)
    (hu : ∀ q ∈ d.ordList, q.2 ≠ x) (he : e ∈ p.methods) (hl : lblOf d x = (true, e.1))
    (h : p.toProblem.MPProg (cfgNet (decDesc d x e)) S) : p.toProblem.MPProg (cfgNet d) S := by
  have hev := hp.methods e he
  have hd : DecompStep p.toProblem.methods (cfgNet d) x e.toMethod
      (HTN.decomposeWith (cfgNet d) x (cfgNet (copyDesc e.2 (freshIds d.ids e.2.ids.length)))) :=
    ⟨⟨e, he, rfl⟩, List.mem_toFinset.2 hx, by rw [cfgNet_label, hl]; rfl,
      cfgNet (copyDesc e.2 (freshIds d.ids e.2.ids.length)),
      wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _),
      (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso.symm,
      disjoint_copy _, rfl⟩
  have hag := agree_decDesc ⟨hinv.ids_nodup, hinv.lbl_mem, hinv.lbl_nodup, hinv.ord_nodup,
    List.nodup_nil, hinv.wf⟩ hev (x := x)
  exact .decomp (unconstrained_cfgNet hx hu) hd
    (h.isoVia (inv_decDesc hinv hev).wf (hd.wf hinv.wf) (isoVia_art (isoVia_id_of_agree hag.symm)))

variable {p : FProbDesc} {b : β} {B : ℕ}

/-- **Soundness**: a winning reachable node is won in the semantic progression game. -/
theorem sound (hp : p.Valid) (hsz : ∀ g, GReach p b g → sz g ≤ B) {g : β × GNode}
    (hw : AOWin B gAcc gUni gStep p g) : GReach p b g →
      (g.2.1.1 = false → p.toProblem.MPProg (cfgNet g.2.2.2) {f | f ∈ g.2.2.1}) ∧
      (g.2.1.1 = true → ∀ S' ∈ (p.δ (lblOf g.2.2.2 g.2.1.2).2).outcomes {f | f ∈ g.2.2.1},
        p.toProblem.MPProg ((cfgNet g.2.2.2).progress g.2.1.2) S') := by
  induction hw with
  | @acc c _ ha =>
    intro _
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := c
    simp only [gAcc, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at ha
    obtain ⟨rfl, hids⟩ := ha
    refine ⟨fun _ => .empty ?_, fun h => absurd h (by simp)⟩
    simp [cfgNet, hids]
  | @ex c c' _ hu _ hs _ ih =>
    intro hr
    have hr' : GReach p b c' := hr.tail hs
    have ih' := ih hr'
    have hinv := (gInv_of_reach hp hr).inv
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := c
    simp only [gUni] at hu
    subst hu
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨b', g'⟩ := c'
    simp only at hs ih'
    rcases nodeSuccs_ex hs.2 with ⟨x, hx, hu, e, he, hl, rfl⟩ | ⟨x, hx, hok, rfl⟩
    · exact mpProg_of_dec hp hinv hx ((unc_iff _ _).1 hu) he hl (ih'.1 rfl)
    · obtain ⟨hl, hu, happ⟩ := lbl_false_of_primOk hok
      exact .prim (unconstrained_cfgNet hx ((unc_iff _ _).1 hu))
        (by rw [cfgNet_label, hl]; rfl) ((fApp_iff _ _ _).1 happ) (ih'.2 rfl)
  | @univ c _ hu _ ih =>
    intro hr
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, x⟩, s, d⟩ := c
    simp only [gUni] at hu
    subst hu
    obtain ⟨hx, hok⟩ := hgi.tagT rfl
    have hinv := hgi.inv
    simp only at hx hok hinv
    obtain ⟨-, hu, -⟩ := lbl_false_of_primOk hok
    have hu' := (unc_iff _ _).1 hu
    refine ⟨fun h => absurd h (by simp), fun _ S' hS' => ?_⟩
    obtain ⟨s', hs', rfl⟩ := outs_complete hS'
    have hst : gStep (p, (b₀, ((true, x), (s, d))), (b₀, ((false, 0), (s', progDesc d x)))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_out hs'
    have hr' := hr.tail hst
    have h := (ih _ (hsz _ hr') hst hr').1 rfl
    simp only at h
    exact h.isoVia (inv_progDesc hinv hx hu' (nodup_of_mem_outs hs')).wf
      (TaskNetwork.progress_wf hinv.wf (unconstrained_cfgNet hx hu'))
      (isoVia_art (isoVia_id_of_agree (agree_progDesc hu').symm))

/-- **Completeness**: a reachable existential node matching (up to isomorphism) a node won in
the semantic progression game is winning. -/
theorem complete (hp : p.Valid) (hsz : ∀ g, GReach p b g → sz g ≤ B) {tn : TaskNetwork ℕ ℕ ℕ}
    {S : Set ℕ} (h : p.toProblem.MPProg tn S) :
    ∀ {g : β × GNode} {σ : ℕ → ℕ}, GReach p b g → g.2.1.1 = false → S = {f | f ∈ g.2.2.1} →
      tn.WF → HTN.TaskNetwork.IsoVia σ tn (cfgNet g.2.2.2) → AOWin B gAcc gUni gStep p g := by
  induction h with
  | empty he =>
    intro g σ hr htag _ _ hσ
    refine AOWin.acc (hsz g hr) ?_
    have hT := hσ.empty he
    simp only [cfgNet, List.toFinset_eq_empty_iff] at hT
    simp [gAcc, htag, hT]
  | @prim tn S t a hu hα happ _ ih =>
    intro g σ hr htag hS hwf hσ
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    simp only at htag hS hσ
    subst htag hS
    have hy := hgi.tagF rfl
    have hinv := hgi.inv
    simp only at hy hinv
    subst hy
    obtain ⟨hx, hunc⟩ := unc_of_isoVia hinv hσ hu
    have hl : lblOf d (σ t) = (false, a) := by
      rw [← toSum_eq_inl, ← cfgNet_label, ← hσ.2.2 t hu.1, hα]
    have hok : primOk p (s, d) (σ t) = true := by
      simp only [primOk, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨(unc_iff _ _).2 hunc, by rw [hl]⟩, ?_⟩
      rw [hl]; exact (fApp_iff _ _ _).2 happ
    have hs₁ : gStep (p, (b₀, ((false, 0), (s, d))), (b₀, ((true, σ t), (s, d)))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_prim hx hok
    have hr₁ := hr.tail hs₁
    refine AOWin.ex (hsz _ hr) (by simp [gUni]) (hsz _ hr₁) hs₁
      (AOWin.univ (hsz _ hr₁) (by simp [gUni]) fun g' _ hs' => ?_)
    have hr' := hr₁.tail hs'
    obtain ⟨b', g''⟩ := g'
    simp only [gStep, Bool.and_eq_true, decide_eq_true_eq] at hs'
    obtain ⟨rfl, hs'⟩ := hs'
    obtain ⟨s', hs'', rfl⟩ := nodeSuccs_univ hs'
    simp only [hl] at hs''
    exact ih _ (outs_sound hs'') hr' rfl rfl (TaskNetwork.progress_wf hwf hu)
      (isoVia_art ((isoVia_of_art (hσ.progress hu.1)).of_agree (agree_progDesc hunc)))
  | @decomp tn tn' S t m hu hd _ ih =>
    intro g σ hr htag hS hwf hσ
    have hgi := gInv_of_reach hp hr
    obtain ⟨b₀, ⟨tg, y⟩, s, d⟩ := g
    simp only at htag hS hσ
    subst htag hS
    have hy := hgi.tagF rfl
    have hinv := hgi.inv
    simp only at hy hinv
    subst hy
    have hwf' := hd.wf hwf
    obtain ⟨⟨e, he, rfl⟩, ht, hαt, tn'', hwf'', hiso, hdisj, rfl⟩ := hd
    have hev := hp.methods e he
    obtain ⟨hx, hunc⟩ := unc_of_isoVia hinv hσ hu
    have hl : lblOf d (σ t) = (true, e.1) := by
      rw [← toSum_eq_inr, ← cfgNet_label, ← hσ.2.2 t ht, hαt]; rfl
    obtain ⟨σ', hσ', -, -⟩ := (isoVia_of_art hσ).decomposeWith hwf hinv.wf ht hwf''
      (wf_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _))
      (hiso.trans (isoVia_copyDesc hev (freshIds_nodup _ _) (length_freshIds _ _)).iso) hdisj
      (disjoint_copy _)
    have hs₁ : gStep (p, (b₀, ((false, 0), (s, d))),
        (b₀, ((false, 0), (s, decDesc d (σ t) e)))) = true := by
      simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, true_and]
      exact mem_nodeSuccs_dec hx ((unc_iff _ _).2 hunc) he hl
    have hr₁ := hr.tail hs₁
    exact AOWin.ex (hsz _ hr) (by simp [gUni]) (hsz _ hr₁) hs₁
      (ih hr₁ rfl rfl hwf' (isoVia_art (hσ'.of_agree (agree_decDesc ⟨hinv.ids_nodup, hinv.lbl_mem,
        hinv.lbl_nodup, hinv.ord_nodup, List.nodup_nil, hinv.wf⟩ hev))))

end Correct

/-! ## Polynomial time -/

section PTs

set_option linter.unusedSectionVars false

theorem pt_fActOf : PT fun x : FProbDesc × ℕ => fActOf x.1 x.2 := by
  unfold fActOf
  have hacts : PT fun x : FProbDesc × ℕ => x.1.actions := PT.fst.comp (PT.fst.comp PT.fst)
  have hf : PT fun x : FProbDesc × ℕ => x.1.actions.filter fun y : FActDesc => y.1 == x.2 :=
    PT.filter hacts (PT.beqL (PT.fst.comp PT.snd) (PT.snd.comp PT.fst))
  exact PT.headI (PT.append hf (PT.single (PT.pair PT.snd
    (PT.const ((([], [], [([], [])])) : List ℕ × List ℕ × List (List ℕ × List ℕ))))))

theorem pt_fApp : PT fun x : (FProbDesc × ℕ) × List ℕ => fApp x.1.1 x.1.2 x.2 := by
  have ha : PT fun x : (FProbDesc × ℕ) × List ℕ => fActOf x.1.1 x.1.2 := pt_fActOf.comp PT.fst
  unfold fApp
  exact PT.and (PT.all (PT.fst.comp (PT.snd.comp ha)) (PT.elem (PT.snd.comp PT.fst) PT.snd))
    (PT.all (PT.fst.comp (PT.snd.comp (PT.snd.comp ha)))
      (PT.not (PT.elem (PT.snd.comp PT.fst) PT.snd)))

theorem pt_outs : PT fun x : (FProbDesc × ℕ) × List ℕ => outs x.1.1 x.1.2 x.2 := by
  have ha : PT fun x : (FProbDesc × ℕ) × List ℕ => fActOf x.1.1 x.1.2 := pt_fActOf.comp PT.fst
  unfold outs
  exact PT.map (PT.snd.comp (PT.snd.comp (PT.snd.comp ha)))
    (PT.dedup (PT.append (PT.filter (PT.snd.comp PT.fst)
      (PT.not (PT.elem (PT.snd.comp (PT.snd.comp PT.fst)) PT.snd))) (PT.fst.comp PT.snd)))

theorem pt_unc : PT fun x : TnDesc × ℕ => unc x.1 x.2 := by
  unfold unc
  exact PT.all (PT.fst.comp (PT.snd.comp PT.fst))
    ((PT.not (PT.beqL (PT.snd.comp PT.snd) (PT.snd.comp PT.fst))).of_eq fun _ => rfl)

theorem pt_decSuccsAt : PT fun x : FProbDesc × TnDesc × ℕ => decSuccsAt x.1 x.2.1 x.2.2 := by
  have hd : PT fun x : FProbDesc × TnDesc × ℕ => x.2.1 := PT.fst.comp PT.snd
  have hx : PT fun x : FProbDesc × TnDesc × ℕ => x.2.2 := PT.snd.comp PT.snd
  have hl : PT fun x : FProbDesc × TnDesc × ℕ => lblOf x.2.1 x.2.2 := pt_lblOf hd hx
  have hm : PT fun x : FProbDesc × TnDesc × ℕ =>
      (x.1.methods.filter fun e => e.1 == (lblOf x.2.1 x.2.2).2).map fun e => decDesc x.2.1 x.2.2 e :=
    PT.map (PT.filter (p := fun (x : FProbDesc × TnDesc × ℕ) (e : MethodDesc) =>
      e.1 == (lblOf x.2.1 x.2.2).2)
      (PT.snd.comp (PT.fst.comp PT.fst)) (PT.beqL (PT.fst.comp PT.snd) (PT.snd.comp (hl.comp PT.fst))))
      (pt_decDesc.comp (PT.pair (hd.comp PT.fst) (PT.pair (hx.comp PT.fst) PT.snd)))
  exact (PT.cond (PT.and (pt_unc.comp (PT.pair hd hx)) (PT.fst.comp hl)) hm
    (PT.const ([] : List TnDesc))).of_eq fun x => by simp only [decSuccsAt, cond_eq_ite]

theorem pt_primOk : PT fun x : FProbDesc × PCfg × ℕ => primOk x.1 x.2.1 x.2.2 := by
  have hd : PT fun x : FProbDesc × PCfg × ℕ => x.2.1.2 := PT.snd.comp (PT.fst.comp PT.snd)
  have hx : PT fun x : FProbDesc × PCfg × ℕ => x.2.2 := PT.snd.comp PT.snd
  have hl : PT fun x : FProbDesc × PCfg × ℕ => lblOf x.2.1.2 x.2.2 := pt_lblOf hd hx
  unfold primOk
  exact PT.and (PT.and (pt_unc.comp (PT.pair hd hx)) (PT.not (PT.fst.comp hl)))
    (pt_fApp.comp (PT.pair (PT.pair PT.fst (PT.snd.comp hl)) (PT.fst.comp (PT.fst.comp PT.snd))))

theorem pt_nodeSuccs : PT fun x : FProbDesc × GNode => nodeSuccs x.1 x.2 := by
  have hp : PT fun x : FProbDesc × GNode => x.1 := PT.fst
  have hg : PT fun x : FProbDesc × GNode => x.2 := PT.snd
  have ht : PT fun x : FProbDesc × GNode => x.2.1.1 := PT.fst.comp (PT.fst.comp hg)
  have hy : PT fun x : FProbDesc × GNode => x.2.1.2 := PT.snd.comp (PT.fst.comp hg)
  have hc : PT fun x : FProbDesc × GNode => x.2.2 := PT.snd.comp hg
  have hs : PT fun x : FProbDesc × GNode => x.2.2.1 := PT.fst.comp hc
  have hd : PT fun x : FProbDesc × GNode => x.2.2.2 := PT.snd.comp hc
  have hl : PT fun x : FProbDesc × GNode => lblOf x.2.2.2 x.2.1.2 := pt_lblOf hd hy
  have h1 : PT fun x : FProbDesc × GNode =>
      (outs x.1 (lblOf x.2.2.2 x.2.1.2).2 x.2.2.1).map
        fun s' => (((false, 0), (s', progDesc x.2.2.2 x.2.1.2)) : GNode) :=
    PT.map (pt_outs.comp (PT.pair (PT.pair hp (PT.snd.comp hl)) hs))
      (PT.pair (PT.const _) (PT.pair PT.snd (pt_progDesc.comp (PT.pair (hd.comp PT.fst)
        (hy.comp PT.fst)))))
  have h2 : PT fun x : FProbDesc × GNode =>
      (x.2.2.2.ids.flatMap (decSuccsAt x.1 x.2.2.2)).map
        (fun d' => (((false, 0), (x.2.2.1, d')) : GNode)) :=
    PT.map (PT.flatMap (PT.fst.comp hd) (pt_decSuccsAt.comp (PT.pair (hp.comp PT.fst)
      (PT.pair (hd.comp PT.fst) PT.snd))))
      (PT.pair (PT.const _) (PT.pair (hs.comp PT.fst) PT.snd))
  have h3 : PT fun x : FProbDesc × GNode =>
      (x.2.2.2.ids.filter (primOk x.1 x.2.2)).map fun z => (((true, z), x.2.2) : GNode) :=
    PT.map (PT.filter (PT.fst.comp hd) (pt_primOk.comp (PT.pair (hp.comp PT.fst)
      (PT.pair (hc.comp PT.fst) PT.snd))))
      (PT.pair (PT.pair (PT.const true) PT.snd) (hc.comp PT.fst))
  exact (PT.cond ht h1 (PT.append h2 h3)).of_eq fun x => by
    simp only [nodeSuccs, cond_eq_ite]

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

theorem pt_gStep : PT (gStep (β := β)) := by
  have h1 : PT fun x : FProbDesc × (β × GNode) × (β × GNode) => decide (x.2.2.1 = x.2.1.1) :=
    PT.eq (PT.fst.comp (PT.snd.comp PT.snd)) (PT.fst.comp (PT.fst.comp PT.snd))
  have h2 : PT fun x : FProbDesc × (β × GNode) × (β × GNode) =>
      decide (x.2.2.2 ∈ nodeSuccs x.1 x.2.1.2) :=
    PT.elemL (pt_nodeSuccs.comp (PT.pair PT.fst (PT.snd.comp (PT.fst.comp PT.snd))))
      (PT.snd.comp (PT.snd.comp PT.snd))
  exact (PT.and h1 h2).of_eq fun _ => rfl

theorem pt_gAcc : PT (gAcc (β := β)) := by
  unfold gAcc
  exact PT.and (PT.not (PT.fst.comp (PT.fst.comp (PT.snd.comp PT.snd))))
    (PT.isEmpty (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))

theorem pt_gUni : PT (gUni (β := β)) := by
  unfold gUni
  exact PT.fst.comp (PT.fst.comp (PT.snd.comp PT.snd))

theorem pt_initF : PT initF := by
  unfold initF
  exact PT.pair (PT.dedup (PT.fst.comp PT.snd)) (PT.pair (PT.fst.comp (PT.snd.comp PT.snd))
    (PT.pair (PT.dedup (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))))
      (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))

theorem pt_sz : PT fun b : β => sz b := (PT.length BDec.pt_encL).of_eq fun _ => rfl

theorem pt_gInit {cB : FProbDesc × β → Bool} (hcB : PT cB) {R : FProbDesc → ℕ} (hR : PT R) :
    PT (gInit cB R) := by
  unfold gInit
  exact PT.and (PT.and (PT.and (FProbDesc.pt_validB.comp PT.fst)
    (hcB.comp (PT.pair PT.fst (PT.fst.comp PT.snd))))
    (PT.le (pt_sz.comp (PT.fst.comp PT.snd)) (hR.comp PT.fst)))
    (PT.eq (PT.snd.comp PT.snd) (PT.pair (PT.const _) (pt_initF.comp PT.fst)))

end PTs

/-! ## Membership in `EXPTIME` -/

section Main

set_option linter.unusedSectionVars false

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

theorem init_state (p : FProbDesc) : p.toProblem.init = {f | f ∈ (initF p).1} := by
  ext f; simp [initF, FProbDesc.toProblem]

theorem agree_initF {p : FProbDesc} (hp : p.Valid) :
    p.toProblem.tnI.Agree (cfgNet (initF p).2) := by
  have h := agree_initCfg (skDesc_valid hp)
  rw [initCfg_skDesc] at h
  exact h

/-- **Strong method-based plan existence by the alternating progression search is in
`EXPTIME`** for classes with polynomial certificates and polynomial progression bounds of the
skeleton. -/
theorem inExpTime_planExMP_strong {Y : FClass} {cB : FProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r : Polynomial ℕ)
    (hcomp : ∀ p : FProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ r.eval (sz p)) ∧ (skDesc p).toProblem.IsHTNProgBound (r.eval (sz p))) :
    Cx.EXPTIME (PlanExMP .strong Y) := by
  obtain ⟨gr, hgr, hgrlen⟩ := HTN.Syn.PolyDom.exists_pt_polyLen r
  have hR : PT fun p : FProbDesc => r.eval (sz p) :=
    (PT.length (hgr.comp (BDec.pt_encL (α := FProbDesc)))).of_eq fun p => by rw [hgrlen]; rfl
  let q : Polynomial ℕ := r + Polynomial.C (3 + sz (0 : ℕ)) +
    80 * (r + 2 * Polynomial.X + 1) ^ 3 + Polynomial.X * (2 * Polynomial.X + 2)
  have hq : ∀ n, q.eval n = r.eval n + nodeBound (r.eval n) n := fun n => by
    simp only [q, nodeBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    ring
  have hreach : ∀ p : FProbDesc, p.Valid → Y p.toProblem → ∀ b : β, sz b ≤ r.eval (sz p) →
      ∀ g, GReach p b g → sz g ≤ q.eval (sz p) := by
    intro p hp hY b hb g hg
    have := sz_le_of_gInv hp (hcomp p hp hY).2 (gInv_of_reach hp hg)
    rw [hq]
    omega
  refine inExpTime_codeLang_of_andOr (α := FProbDesc) (σ := β × GNode)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.MPStrongSolvable)
    (pt_gInit hcB hR) pt_gAcc pt_gUni pt_gStep q fun p => ?_
  constructor
  · rintro ⟨hp, hY, hsol⟩
    obtain ⟨⟨b, hb, hbs⟩, -⟩ := hcomp p hp hY
    have hsz := hreach p hp hY b hbs
    refine ⟨(b, ((false, 0), initF p)), hsz _ .refl, ?_, ?_⟩
    · simp [gInit, (FProbDesc.validB_iff p).2 hp, hb, hbs]
    · have h := (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).1 hsol
      exact complete hp hsz h .refl rfl (init_state p) (FProbDesc.toProblem_wf hp).tnI
        (isoVia_art (isoVia_id_of_agree (agree_initF hp)))
  · rintro ⟨⟨b, g⟩, -, hi, hw⟩
    simp only [gInit, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨hv, hb⟩, hbs⟩, rfl⟩ := hi
    have hp := (FProbDesc.validB_iff p).1 hv
    have hY := hsound p b hp hb
    have hsz := hreach p hp hY b hbs
    refine ⟨hp, hY, ?_⟩
    have h := (sound hp hsz hw .refl).1 rfl
    have hinv := (gInv_init hp b).inv
    rw [← init_state] at h
    exact (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).2
      (h.isoVia hinv.wf (FProbDesc.toProblem_wf hp).tnI
        (isoVia_art (isoVia_id_of_agree (agree_initF hp).symm)))

end Main

end MPS

end FOND
