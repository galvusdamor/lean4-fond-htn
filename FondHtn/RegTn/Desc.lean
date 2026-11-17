import FondHtn.Hardness.FromDet
import FondHtn.MP.Fair
import HtnComplexity.Article.StripsReg
/-!
# A regular encoding of STRIPS with the goal checked by an action

The inherited lower bounds (`FondHtn/Hardness/FromDet.lean`) append a goal-check task after
`tn_I`, which destroys regularity of `tn_I` ([CB21, Def. 3.3] / Erol et al., `FClass.REGtn`).  Here
the goal check is built into the methods instead.  For a STRIPS description `d` with a fresh
action name `g` (`FOND.RegTn.gName`):

* actions: the actions of `d` and `g = (g⁺, g⁻, ∅, ∅)` (precondition: the goal of `d`);
* one compound task `c = 0` with the methods `c → g` (`FOND.RegTn.gTn`) and `c → p c` for every
  action `p` (`HTN.Article.stepTn`);
* `tn_I = c` (`HTN.Article.rootTn`), `s_I = s_I(d)`, no state goal.

`FOND.RegTn.artReg d` is this problem in the deterministic article model (with the empty goal),
`FOND.RegTn.fondReg d` the FOND description (every action with its single effect).

* `FOND.RegTn.artReg_solvable_iff` — `artReg d` is solvable iff `d` has a plan;
* `FOND.RegTn.weakLD_iff` — `fondReg d` is weak LD solvable iff `d` has a plan;
* `FOND.RegTn.fondReg_class` — `fondReg d` is in `REGtn ∩ TO`;
* `FOND.RegTn.pt_fondReg` — polynomial time.
-/

namespace FOND

namespace RegTn

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-! ## The encoding -/

/-- The fresh name of the goal action. -/
def gName (d : StripsDesc) : ℕ := freshOf (d.actions.map ActDesc.name)

/-- The goal action. -/
def gAct (d : StripsDesc) : ActDesc := (gName d, d.goalPos, d.goalNeg, [], [])

/-- The network `g` of the terminal method. -/
def gTn (g : ℕ) : TnDesc := ([0], [], [(0, false, g)])

/-- The methods: `c → g` and `c → p c`. -/
def methodsOf (d : StripsDesc) : List MethodDesc :=
  (0, gTn (gName d)) :: d.actions.map fun a => (0, stepTn a.name)

/-- The actions. -/
def actsOf (d : StripsDesc) : List ActDesc := d.actions ++ [gAct d]

/-- **The encoding in the deterministic article model** (empty state goal). -/
def artReg (d : StripsDesc) : ProbDesc := ((actsOf d, methodsOf d), (d.init, rootTn, [], []))

/-- **The FOND encoding.** -/
def fondReg (d : StripsDesc) : FProbDesc :=
  (((actsOf d).map detAct, methodsOf d), (d.init, rootTn))

/-! ## Small networks -/

theorem gTn_T (g : ℕ) : (gTn g).toTaskNetwork.T = {0} := by
  simp [gTn, TnDesc.toTaskNetwork, TnDesc.ids]

theorem gTn_α0 (g : ℕ) : (gTn g).toTaskNetwork.α 0 = Sum.inl g := by
  simp [gTn, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl]

theorem gName_not_mem (d : StripsDesc) : gName d ∉ d.actions.map ActDesc.name := freshOf_not_mem _

/-! ## Solvability in the article model -/

variable (d : StripsDesc)

theorem artReg_methods_mem {m : MethodDesc} :
    m ∈ (artReg d).methods ↔ m = (0, gTn (gName d)) ∨ ∃ a ∈ d.actions, m = (0, stepTn a.name) := by
  simp only [ProbDesc.methods, artReg, methodsOf, List.mem_cons, List.mem_map]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, rfl⟩
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, rfl⟩

/-- Valid trees for `c` yield a sequence of actions of `d` followed by `g`. -/
theorem yield_of_tree : ∀ (dt : DTree ℕ ℕ ℕ) (π : List ℕ),
    dt.Valid (artReg d).toProblem.methods (Sum.inr 0) → dt.Yield π →
      ∃ π', π = π' ++ [gName d] ∧ ∀ a ∈ π', a ∈ d.actions.map ActDesc.name := by
  intro dt
  induction dt with
  | leaf a => intro π hv; exact absurd (DTree.Valid.leaf_inv hv) (by simp)
  | node c m ch ih =>
    intro π hv hy
    obtain ⟨-, ⟨e, he, rfl⟩, -, hch⟩ := hv.node_inv
    obtain ⟨ys, hys, hm⟩ := hy.node_inv
    rcases (artReg_methods_mem d).1 he with rfl | ⟨a, ha, rfl⟩
    · simp only [MethodDesc.toMethod] at hm hch hys
      rw [(ordMerge_single (TnDesc.toTaskNetwork_wf _) (gTn_T _)).1 hm]
      have h0 := hch 0 (by rw [gTn_T]; simp)
      rw [gTn_α0] at h0
      have hy0 := hys 0 (by rw [gTn_T]; simp)
      rw [DTree.Valid.eq_leaf_of_inl h0] at hy0
      rw [DTree.Yield.leaf_inv hy0]
      exact ⟨[], rfl, by simp⟩
    · simp only [MethodDesc.toMethod] at hm hch hys
      rw [(ordMerge_pair (TnDesc.toTaskNetwork_wf _) (stepTn_T _) (by decide) (stepTn_ord _)).1 hm]
      have h0 := hch 0 (by rw [stepTn_T]; simp)
      rw [stepTn_α0] at h0
      have h1 := hch 1 (by rw [stepTn_T]; simp)
      rw [stepTn_α1] at h1
      have hy0 := hys 0 (by rw [stepTn_T]; simp)
      rw [DTree.Valid.eq_leaf_of_inl h0] at hy0
      rw [DTree.Yield.leaf_inv hy0]
      obtain ⟨π', hπ', hdecl⟩ := ih 1 (ys 1) h1 (hys 1 (by rw [stepTn_T]; simp))
      refine ⟨a.name :: π', by rw [hπ']; rfl, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact List.mem_map.2 ⟨a, ha, rfl⟩
      · exact hdecl b hb

/-- Every sequence of actions of `d` followed by `g` is the yield of a valid tree for `c`. -/
theorem tree_of_yield : ∀ π : List ℕ, (∀ a ∈ π, a ∈ d.actions.map ActDesc.name) →
    ∃ dt : DTree ℕ ℕ ℕ, dt.Valid (artReg d).toProblem.methods (Sum.inr 0) ∧
      dt.Yield (π ++ [gName d]) := by
  intro π
  induction π with
  | nil =>
    intro _
    refine ⟨.node 0 (MethodDesc.toMethod (0, gTn (gName d))) (fun _ => .leaf (gName d)),
      .node ⟨(0, gTn (gName d)), (artReg_methods_mem d).2 (Or.inl rfl), rfl⟩ rfl
        (fun t ht => ?_), ?_⟩
    · simp only [MethodDesc.toMethod, gTn_T, Finset.mem_singleton] at ht
      subst ht
      simp only [MethodDesc.toMethod, gTn_α0]; exact .leaf _
    · refine .node (fun _ => [gName d]) (fun t ht => .leaf _) ?_
      simp only [MethodDesc.toMethod]
      rw [ordMerge_single (TnDesc.toTaskNetwork_wf _) (gTn_T _)]
      rfl
  | cons p π ih =>
    intro hdecl
    obtain ⟨dt, hv, hy⟩ := ih fun a ha => hdecl a (by simp [ha])
    obtain ⟨a, ha, hap⟩ := List.mem_map.1 (hdecl p (by simp))
    refine ⟨.node 0 (MethodDesc.toMethod (0, stepTn p)) (fun t => if t = 0 then .leaf p else dt),
      .node ⟨(0, stepTn p), (artReg_methods_mem d).2 (Or.inr ⟨a, ha, by rw [hap]⟩), rfl⟩ rfl
        (fun t ht => ?_), ?_⟩
    · simp only [MethodDesc.toMethod, stepTn_T, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · simp only [MethodDesc.toMethod, stepTn_α0, if_true]; exact .leaf p
      · simp only [MethodDesc.toMethod, stepTn_α1, one_ne_zero, if_false]; exact hv
    · refine .node (fun t => if t = 0 then [p] else π ++ [gName d]) (fun t ht => ?_) ?_
      · simp only [MethodDesc.toMethod, stepTn_T, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · simp only [if_true]; exact .leaf p
        · simp only [one_ne_zero, if_false]; exact hy
      · simp only [MethodDesc.toMethod]
        rw [ordMerge_pair (TnDesc.toTaskNetwork_wf _) (stepTn_T _) (by decide) (stepTn_ord _)]
        simp

theorem run_congr' {P Q : HTN.Article.Problem ℕ ℕ ℕ ℕ} : ∀ (π : List ℕ) (s s' : Set ℕ),
    (∀ a ∈ π, P.δ a = Q.δ a) → (P.Run π s s' ↔ Q.Run π s s') := by
  intro π
  induction π with
  | nil => intro s s' _; exact Iff.rfl
  | cons a π ih =>
    intro s s' h
    show _ ∧ _ ↔ _ ∧ _
    rw [h a List.mem_cons_self, ih _ _ fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem δ_decl {a : ℕ} (ha : a ∈ d.actions.map ActDesc.name) :
    (artReg d).toProblem.δ a = d.toProbDesc.toProblem.δ a := by
  show (artReg d).δ a = d.toProbDesc.δ a
  unfold ProbDesc.δ
  simp only [artReg, StripsDesc.toProbDesc, ProbDesc.actions, actsOf, List.find?_append]
  cases hf : d.actions.find? (fun x => x.name == a) with
  | some x => rfl
  | none =>
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact absurd (List.find?_eq_none.1 hf b hb) (by simp)

theorem δ_g : (artReg d).toProblem.δ (gName d) = (gAct d).toAction := by
  show (artReg d).δ (gName d) = _
  unfold ProbDesc.δ
  simp only [artReg, ProbDesc.actions, actsOf, List.find?_append]
  have : d.actions.find? (fun x => x.name == gName d) = none := by
    rw [List.find?_eq_none]
    intro x hx hxg
    exact gName_not_mem d (List.mem_map.2 ⟨x, hx, by simpa using hxg⟩)
  rw [this]
  simp [gAct, ActDesc.name]

/-- **The article encoding is solvable iff the STRIPS problem has a plan.** -/
theorem artReg_solvable_iff : (artReg d).toProblem.Solvable ↔ d.Solvable := by
  rw [Problem.solvable_iff_trees _ (toProblem_wf _)]
  have hT : (artReg d).toProblem.tnI.T = {0} := rootTn_T
  have hα : (artReg d).toProblem.tnI.α 0 = Sum.inr 0 := rootTn_α0
  have hwf : (artReg d).toProblem.tnI.WF := TnDesc.toTaskNetwork_wf _
  have hgoal : ∀ s, (artReg d).toProblem.GoalState s := fun s => by
    simp [HTN.Article.Problem.GoalState, ProbDesc.toProblem, artReg, ProbDesc.goalPos, ProbDesc.goalNeg]
  have hrun : ∀ π' (s : Set ℕ), (∀ a ∈ π', a ∈ d.actions.map ActDesc.name) →
      ((∃ s', (artReg d).toProblem.Run (π' ++ [gName d]) {f | f ∈ d.init} s') ↔
        ∃ s, d.toProbDesc.toProblem.Run π' {f | f ∈ d.init} s ∧
          d.toProbDesc.toProblem.GoalState s) := by
    intro π' _ hdecl
    simp only [run_append, run_congr' π' _ _ fun a ha => δ_decl d (hdecl a ha)]
    constructor
    · rintro ⟨s', m, h1, h2, -⟩
      rw [δ_g] at h2
      exact ⟨m, h1, h2⟩
    · rintro ⟨m, h1, h2⟩
      refine ⟨_, m, h1, ?_, rfl⟩
      rw [δ_g]; exact h2
  constructor
  · rintro ⟨trees, π, s, ⟨hval, ys, hys, hm⟩, hr, -⟩
    obtain rfl := (ordMerge_single hwf hT).1 hm
    have hv := hval 0 (by rw [hT]; simp)
    rw [hα] at hv
    obtain ⟨π', hπ', hdecl⟩ := yield_of_tree d (trees 0) (ys 0) hv (hys 0 (by rw [hT]; simp))
    rw [hπ'] at hr
    obtain ⟨s', h1, h2⟩ := (hrun π' s hdecl).1 ⟨s, hr⟩
    exact ⟨π', hdecl, s', h1, h2⟩
  · rintro ⟨π, hdecl, s, hr, hg⟩
    obtain ⟨dt, hv, hy⟩ := tree_of_yield d π hdecl
    obtain ⟨s', hs'⟩ := (hrun π s hdecl).2 ⟨s, hr, hg⟩
    refine ⟨fun _ => dt, π ++ [gName d], s', ⟨fun t ht => ?_, fun _ => π ++ [gName d],
      fun t ht => hy, (ordMerge_single hwf hT).2 rfl⟩, hs', hgoal _⟩
    rw [hT] at ht
    obtain rfl : t = 0 := by simpa using ht
    rw [hα]; exact hv

/-! ## The FOND encoding -/

theorem fond_δ (a : ℕ) :
    (fondReg d).toProblem.δ a = Action.ofDet ((artReg d).toProblem.δ a) := by
  show (fondReg d).δ a = Action.ofDet ((artReg d).δ a)
  unfold FProbDesc.δ ProbDesc.δ
  simp only [fondReg, artReg, FProbDesc.actions, ProbDesc.actions, List.find?_map]
  have hc : ((fun x : FActDesc => x.name == a) ∘ detAct) = fun x : ActDesc => x.name == a := rfl
  rw [hc]
  cases (actsOf d).find? (fun x => x.name == a) with
  | some x =>
    simp only [Option.map_some]
    apply Action.ext' <;> ext <;>
      simp [FActDesc.toAction, ActDesc.toAction, Action.ofDet, detAct, FActDesc.effs]
  | none =>
    simp only [Option.map_none]
    apply Action.ext' <;> simp [Action.ofDet]

theorem fond_isDeterministic : (fondReg d).toProblem.IsDeterministic := by
  intro a
  rw [fond_δ]
  exact ⟨_, rfl⟩

theorem weakExec_iff : ∀ (as : List ℕ) (s : Set ℕ),
    (fondReg d).toProblem.WeakExec as s ↔ ∃ s', (artReg d).toProblem.Run as s s' := by
  intro as
  induction as with
  | nil => intro s; simp [Problem.WeakExec, HTN.Article.Problem.Run]
  | cons a as ih =>
    intro s
    show (((fondReg d).toProblem.δ a).Applicable s ∧ ∃ s' ∈ ((fondReg d).toProblem.δ a).outcomes s,
      (fondReg d).toProblem.WeakExec as s') ↔ _
    rw [fond_δ, Action.ofDet_applicable, Action.ofDet_outcomes]
    simp only [Set.mem_singleton_iff, exists_eq_left, ih, HTN.Article.Problem.Run]
    constructor
    · rintro ⟨h1, s', h2⟩; exact ⟨s', h1, h2⟩
    · rintro ⟨s', h1, h2⟩; exact ⟨h1, s', h2⟩

/-- **Weak LD solvability of the FOND encoding is plan existence of `d`.** -/
theorem weakLD_iff : (fondReg d).toProblem.WeakLDSolvable ↔ d.Solvable := by
  rw [← artReg_solvable_iff, Problem.solvable_iff_decomp _ (toProblem_wf _)]
  have hgoal : ∀ s, (artReg d).toProblem.GoalState s := fun s => by
    simp [HTN.Article.Problem.GoalState, ProbDesc.toProblem, artReg, ProbDesc.goalPos, ProbDesc.goalNeg]
  constructor
  · rintro ⟨tn, l, ⟨hd, hp⟩, hl, as, has, hex⟩
    obtain ⟨s, hs⟩ := (weakExec_iff d as _).1 hex
    exact ⟨tn, hd, hp, l, as, s, hl, has, hs, hgoal s⟩
  · rintro ⟨tn, hd, hp, l, as, s, hl, has, hs, -⟩
    exact ⟨tn, l, ⟨hd, hp⟩, hl, as, has, (weakExec_iff d as _).2 ⟨s, hs⟩⟩

/-! ## Well-formedness -/

theorem names_fondReg :
    (fondReg d).actions.map FActDesc.name = d.actions.map ActDesc.name ++ [gName d] := by
  simp [fondReg, FProbDesc.actions, actsOf, List.map_append, detAct, FActDesc.name, ActDesc.name,
    gAct]

theorem declared_fondReg {n : ℕ} :
    (fondReg d).Declared n ↔ n ∈ d.actions.map ActDesc.name ∨ n = gName d := by
  unfold FProbDesc.Declared; rw [names_fondReg]; simp

theorem tnValid_rootTn {prim : ℕ → Prop} : TnValid prim rootTn :=
  ⟨by simp [rootTn, TnDesc.ids], by simp [rootTn, TnDesc.ordList],
    by simp [rootTn, TnDesc.ordList], by simp [rootTn, TnDesc.ordList],
    by simp [rootTn, TnDesc.lbl, TnDesc.ids], by simp [rootTn, TnDesc.lbl]⟩

theorem fondReg_valid_iff : (fondReg d).Valid ↔ d.Valid := by
  constructor
  · intro h
    have := h.names_nodup
    rw [names_fondReg] at this
    exact List.Nodup.of_append_left this
  · intro h
    refine ⟨?_, ?_, tnValid_rootTn, fun m hm => ?_⟩
    · rw [names_fondReg]
      exact List.nodup_append.2 ⟨h, List.nodup_singleton _, by
        intro x hx y hy; simp at hy; subst hy; exact fun e => gName_not_mem d (e ▸ hx)⟩
    · intro a ha
      simp only [fondReg, FProbDesc.actions, List.mem_map] at ha
      obtain ⟨b, -, rfl⟩ := ha
      simp [FActDesc.effs, detAct]
    · simp only [FProbDesc.methods, fondReg, methodsOf, List.mem_cons, List.mem_map] at hm
      rcases hm with rfl | ⟨a, ha, rfl⟩
      · refine ⟨by simp [gTn, TnDesc.ids], by simp [gTn, TnDesc.ordList],
          by simp [gTn, TnDesc.ordList], by simp [gTn, TnDesc.ordList],
          by simp [gTn, TnDesc.lbl, TnDesc.ids], ?_⟩
        intro q hq _
        simp only [gTn, TnDesc.lbl, List.mem_singleton] at hq
        subst hq
        exact (declared_fondReg d).2 (Or.inr rfl)
      · refine ⟨by simp [stepTn, TnDesc.ids], by simp [stepTn, TnDesc.ordList, TnDesc.ids],
          by simp [stepTn, TnDesc.ordList], ?_, ?_, ?_⟩
        · intro x y z h1 h2; simp [stepTn, TnDesc.ordList] at h1 h2; omega
        · simp only [stepTn, TnDesc.lbl, TnDesc.ids, List.map_cons, List.map_nil]
          exact List.Perm.refl _
        · intro q hq hf
          simp only [stepTn, TnDesc.lbl, List.mem_cons, List.mem_nil_iff, or_false] at hq
          rcases hq with rfl | rfl
          · exact (declared_fondReg d).2 (Or.inl (List.mem_map.2 ⟨a, ha, rfl⟩))
          · simp at hf

/-! ## The class -/

theorem fondReg_methods_cases {m : Method ℕ ℕ ℕ} (hm : m ∈ (fondReg d).toProblem.methods) :
    m = MethodDesc.toMethod (0, gTn (gName d)) ∨ ∃ p, m = MethodDesc.toMethod (0, stepTn p) := by
  obtain ⟨e, he, rfl⟩ := hm
  simp only [FProbDesc.methods, fondReg, methodsOf, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨a, -, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem gTn_regular (g : ℕ) : (gTn g).toTaskNetwork.IsRegular := by
  refine ⟨fun t ht t' ht' ha _ => ?_, fun t ht ha t' ht' hne => ?_⟩
  · rw [gTn_T] at ht ht'
    simp only [Finset.mem_singleton] at ht ht'
    rw [ht, ht']
  · rw [gTn_T] at ht
    simp only [Finset.mem_singleton] at ht
    subst ht
    obtain ⟨c, hc⟩ := ha
    rw [gTn_α0] at hc; cases hc

theorem rootTn_regular : rootTn.toTaskNetwork.IsRegular := by
  refine ⟨fun t ht t' ht' _ _ => ?_, fun t ht _ t' ht' hne => ?_⟩
  · rw [rootTn_T] at ht ht'
    simp only [Finset.mem_singleton] at ht ht'
    rw [ht, ht']
  · rw [rootTn_T] at ht ht'
    simp only [Finset.mem_singleton] at ht ht'
    exact absurd (ht'.trans ht.symm) hne

theorem fondReg_REG : FClass.REG (fondReg d).toProblem := by
  rintro m ⟨hm, -⟩
  rcases fondReg_methods_cases d hm with rfl | ⟨p, rfl⟩
  · exact gTn_regular _
  · exact stepTn_regular p

theorem fondReg_TO : FClass.TO (fondReg d).toProblem := by
  refine ⟨fun t ht t' ht' hne => ?_, fun m hm' => ?_⟩
  all_goals try (obtain ⟨hm, -⟩ := hm')
  · have hT : (fondReg d).toProblem.tnI.T = {0} := rootTn_T
    change t ∈ (fondReg d).toProblem.tnI.T at ht
    change t' ∈ (fondReg d).toProblem.tnI.T at ht'
    rw [hT] at ht ht'
    simp at ht ht'
    exact absurd (ht.trans ht'.symm) hne
  · rcases fondReg_methods_cases d hm with rfl | ⟨p, rfl⟩
    · intro t ht t' ht' hne
      simp only [MethodDesc.toMethod, gTn_T, Finset.mem_singleton] at ht ht'
      exact absurd (ht.trans ht'.symm) hne
    · intro t ht t' ht' hne
      simp only [MethodDesc.toMethod, stepTn_T, Finset.mem_insert, Finset.mem_singleton] at ht ht'
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl (stepTn_ord p)
      · exact Or.inr (stepTn_ord p)
      · exact absurd rfl hne

theorem fondReg_class : FClass.inter FClass.REGtn FClass.TO (fondReg d).toProblem :=
  ⟨⟨fondReg_REG d, rootTn_regular⟩, fondReg_TO d⟩

/-! ## Polynomial time -/

theorem pt_detAct : PT detAct := by
  unfold detAct
  exact PT.pair PT.fst (PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.fst.comp (PT.snd.comp PT.snd))
    (PT.single (PT.pair (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd)))
      (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))))

theorem pt_fondReg : PT fondReg := by
  have hacts : PT fun d : StripsDesc => d.actions := PT.fst
  have hg : PT gName := pt_freshOf (PT.map hacts (PT.fst.comp PT.snd))
  have hgA : PT gAct := by
    unfold gAct
    exact PT.pair hg (PT.pair (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.pair (PT.snd.comp (PT.snd.comp PT.snd)) (PT.const _)))
  have hA : PT actsOf := by unfold actsOf; exact PT.append hacts (PT.single hgA)
  have hgT : PT fun d : StripsDesc => gTn (gName d) := by
    unfold gTn
    exact PT.pair (PT.const _) (PT.pair (PT.const _) (PT.single (PT.pair (PT.const 0)
      (PT.pair (PT.const false) hg))))
  have hM : PT methodsOf := by
    unfold methodsOf
    exact PT.cons (PT.pair (PT.const 0) hgT) (PT.map hacts (PT.pair (PT.const 0)
      (pt_stepTn (PT.fst.comp PT.snd))))
  unfold fondReg
  exact PT.pair (PT.pair (PT.map hA (pt_detAct.comp PT.snd)) hM)
    (PT.pair (PT.fst.comp PT.snd) (PT.const _))

end RegTn

end FOND
