import HtnComplexity.Article.StripsHard
import HtnPlanning.Article.TIHTN
import HtnPlanning.Article.ToSyn
/-!
# Regular and tail-recursive problems are PSPACE-hard (Thm. 4.3.1, Cors. 4.3.2, 4.3.3)

The article's encoding of a STRIPS problem: one compound task `c` (here the name `0`) with the
methods `c → ε` and `c → p c` for every action `p`, and the initial task network `c`
(`HTN.Article.regOfStrips`).  The problem is totally ordered and regular; its decomposition trees
are exactly the chains of actions, so it has a solution iff the STRIPS problem has a plan
(`HTN.Article.regOfStrips_solvable_iff`).

* **`HTN.Article.thm_4_3_1`** — `PlanEx^{REG∩TO}`, `PlanEx^{REG∩TO-M}` and `PlanEx^{REG}` are
  PSPACE-hard;
* **`HTN.Article.cor_4_3_2`** — `PlanEx^{TAIL-REC∩TO}` and `PlanEx^{TAIL-REC∩TO-M}` are
  PSPACE-hard;
* **`HTN.Article.cor_4_3_3`** — `PlanEx^{TAIL-REC_h}` is PSPACE-hard for every fixed `h ≥ 1`.

Also: ordered merges of the yields over networks of at most two tasks
(`HTN.Article.ordMerge_single`, `HTN.Article.ordMerge_pair`), and the generic passage from a
polynomial-time encoding of STRIPS to PSPACE-hardness (`HTN.Article.pspaceHard_of_strips`).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-! ### Ordered merges over small networks -/

section Merge

variable {I A C : Type} [DecidableEq I]

theorem ordMerge_empty {tn : TaskNetwork I A C} (hT : tn.T = ∅) {ys : I → List A} {π : List A} :
    OrdMerge tn ys π ↔ π = [] := by
  constructor
  · rintro ⟨w, hw, hmem, -, -⟩
    cases w with
    | nil => exact hw.symm
    | cons x w => exact absurd (hmem x (by simp)) (by rw [hT]; simp)
  · rintro rfl
    exact ⟨[], rfl, by simp, by rw [hT]; simp, List.Pairwise.nil⟩

theorem ordMerge_single {tn : TaskNetwork I A C} {t : I} (hwf : tn.WF) (hT : tn.T = {t})
    {ys : I → List A} {π : List A} : OrdMerge tn ys π ↔ π = ys t := by
  constructor
  · rintro ⟨w, hw, hmem, hfil, -⟩
    have hall : w.filter (fun x => decide (x.1 = t)) = w :=
      List.filter_eq_self.2 fun x hx => by
        have := hmem x hx; rw [hT] at this; simpa using this
    rw [← hw, ← hall, hfil t (by rw [hT]; simp)]
  · rintro rfl
    refine ⟨(ys t).map fun a => (t, a), by simp, fun x hx => ?_, fun u hu => ?_, ?_⟩
    · simp only [List.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      rw [hT]; simp
    · rw [hT] at hu
      obtain rfl : u = t := by simpa using hu
      simp [List.filter_map, Function.comp_def]
    · exact List.pairwise_map.2 (List.pairwise_of_forall fun _ _ => hwf.irrefl t)

theorem map_snd_split {t t' : I} (htt : t ≠ t') {R : I → I → Prop} (hR : R t t') :
    ∀ w : List (I × A), (∀ x ∈ w, x.1 = t ∨ x.1 = t') →
      w.Pairwise (fun x y => ¬ R y.1 x.1) →
      w.map Prod.snd = (w.filter fun x => decide (x.1 = t)).map Prod.snd ++
        (w.filter fun x => decide (x.1 = t')).map Prod.snd := by
  intro w
  induction w with
  | nil => intro _ _; rfl
  | cons x w ih =>
    intro hmem hpw
    rw [List.pairwise_cons] at hpw
    have ih' := ih (fun y hy => hmem y (by simp [hy])) hpw.2
    rcases hmem x (by simp) with hx | hx
    · simp only [List.map_cons, List.filter_cons, hx, decide_true, ↓reduceIte, Ne.symm htt,
        decide_false, Bool.false_eq_true, List.cons_append, ih']
      simp [htt]
    · have hall : ∀ y ∈ w, y.1 = t' := by
        intro y hy
        rcases hmem y (by simp [hy]) with h | h
        · exact absurd (h ▸ hx ▸ hR) (hpw.1 y hy)
        · exact h
      have h1 : w.filter (fun x => decide (x.1 = t)) = [] :=
        List.filter_eq_nil_iff.2 fun y hy => by simp [hall y hy, Ne.symm htt]
      have h2 : w.filter (fun x => decide (x.1 = t')) = w :=
        List.filter_eq_self.2 fun y hy => by simp [hall y hy]
      simp [List.filter_cons, hx, Ne.symm htt, h1, h2]

theorem ordMerge_pair {tn : TaskNetwork I A C} {t t' : I} (hwf : tn.WF) (hT : tn.T = {t, t'})
    (htt : t ≠ t')
    (hord : tn.ord t t') {ys : I → List A} {π : List A} :
    OrdMerge tn ys π ↔ π = ys t ++ ys t' := by
  constructor
  · rintro ⟨w, hw, hmem, hfil, hpw⟩
    rw [← hw, ← hfil t (by rw [hT]; simp), ← hfil t' (by rw [hT]; simp)]
    exact map_snd_split htt hord w (fun x hx => by
      have := hmem x hx; rw [hT] at this; simpa using this) hpw
  · rintro rfl
    refine ⟨(ys t).map (fun a => (t, a)) ++ (ys t').map (fun a => (t', a)), by simp,
      fun x hx => ?_, fun u hu => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_map] at hx
      rcases hx with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩ <;> (rw [hT]; simp)
    · rw [hT] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · simp [List.filter_append, List.filter_map, Function.comp_def, htt]
        exact fun _ _ h => htt h.symm
      · simp [List.filter_append, List.filter_map, Function.comp_def, Ne.symm htt]
        exact fun _ _ h => htt h
    · refine List.pairwise_append.2 ⟨List.pairwise_map.2 (List.pairwise_of_forall fun _ _ =>
        hwf.irrefl t), List.pairwise_map.2 (List.pairwise_of_forall fun _ _ => hwf.irrefl t'), ?_⟩
      simp only [List.mem_map]
      rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ h
      exact hwf.irrefl t (hwf.trans hord h)

end Merge

/-! ### Small task network descriptions -/

/-- The network `p c` of a step method. -/
def stepTn (p : ℕ) : TnDesc := ([0, 1], [(0, 1)], [(0, false, p), (1, true, 0)])

/-- The empty network. -/
def emptyTnD : TnDesc := ([], [], [])

/-- The network of the single compound task `c = 0`. -/
def rootTn : TnDesc := ([0], [], [(0, true, 0)])

theorem stepTn_T (p : ℕ) : (stepTn p).toTaskNetwork.T = {0, 1} := by
  simp [stepTn, TnDesc.toTaskNetwork, TnDesc.ids]

theorem stepTn_ord (p : ℕ) : (stepTn p).toTaskNetwork.ord 0 1 := by
  refine ⟨by simp [stepTn, TnDesc.ids], by simp [stepTn, TnDesc.ids],
    .single (by simp [TnDesc.listRel, stepTn, TnDesc.ordList]), fun h => ?_⟩
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 h
  simp [TnDesc.listRel, stepTn, TnDesc.ordList] at hc

theorem stepTn_α0 (p : ℕ) : (stepTn p).toTaskNetwork.α 0 = Sum.inl p := by
  simp [stepTn, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]

theorem stepTn_α1 (p : ℕ) : (stepTn p).toTaskNetwork.α 1 = Sum.inr 0 := by
  simp [stepTn, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]

theorem emptyTnD_T : emptyTnD.toTaskNetwork.T = ∅ := by
  simp [emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids]

theorem rootTn_T : rootTn.toTaskNetwork.T = {0} := by
  simp [rootTn, TnDesc.toTaskNetwork, TnDesc.ids]

theorem rootTn_α0 : rootTn.toTaskNetwork.α 0 = Sum.inr 0 := by
  simp [rootTn, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]

/-! ### The encoding -/

/-- The methods of the encoding: `c → ε` and `c → p c` for every action `p`. -/
def regMethods (d : StripsDesc) : List MethodDesc :=
  (0, emptyTnD) :: d.actions.map fun a => (0, stepTn a.name)

/-- **The regular encoding of a STRIPS problem** (Thm. 4.3.1). -/
def regOfStrips (d : StripsDesc) : ProbDesc :=
  ((d.actions, regMethods d), (d.init, rootTn, d.goalPos, d.goalNeg))

theorem toProblem_wf (p : ProbDesc) : p.toProblem.WF :=
  ⟨TnDesc.toTaskNetwork_wf _, by rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _⟩

theorem run_congr {P Q : Problem ℕ ℕ ℕ ℕ} (h : P.δ = Q.δ) :
    ∀ (π : List ℕ) (s s' : Set ℕ), P.Run π s s' ↔ Q.Run π s s' := by
  intro π
  induction π with
  | nil => intro s s'; exact Iff.rfl
  | cons a π ih => intro s s'; show _ ∧ _ ↔ _ ∧ _; rw [h, ih]

theorem regOfStrips_δ (d : StripsDesc) : (regOfStrips d).toProblem.δ = d.toProbDesc.toProblem.δ := rfl

/-- Valid trees for `c` yield declared actions only. -/
theorem reg_yield (d : StripsDesc) : ∀ (dt : DTree ℕ ℕ ℕ) (π : List ℕ),
    dt.Valid (regOfStrips d).toProblem.methods (Sum.inr 0) → dt.Yield π →
      ∀ a ∈ π, a ∈ d.actions.map ActDesc.name := by
  intro dt
  induction dt with
  | leaf a => intro π hv; exact absurd (DTree.Valid.leaf_inv hv) (by simp)
  | node c m ch ih =>
    intro π hv hy
    obtain ⟨-, ⟨e, he, rfl⟩, -, hch⟩ := hv.node_inv
    obtain ⟨ys, hys, hm⟩ := hy.node_inv
    simp only [ProbDesc.toProblem, ProbDesc.methods, regOfStrips, regMethods, List.mem_cons,
      List.mem_map] at he
    rcases he with rfl | ⟨a, ha, rfl⟩
    · rw [(ordMerge_empty emptyTnD_T).1 hm]; simp
    · simp only [MethodDesc.toMethod] at hm hch hys
      rw [(ordMerge_pair (TnDesc.toTaskNetwork_wf _) (stepTn_T _) (by decide) (stepTn_ord _)).1 hm]
      have h0 := hch 0 (by rw [stepTn_T]; simp)
      rw [stepTn_α0] at h0
      have h1 := hch 1 (by rw [stepTn_T]; simp)
      rw [stepTn_α1] at h1
      have hy0 := hys 0 (by rw [stepTn_T]; simp)
      rw [DTree.Valid.eq_leaf_of_inl h0] at hy0
      rw [DTree.Yield.leaf_inv hy0]
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · simp at hb; subst hb; exact List.mem_map.2 ⟨a, ha, rfl⟩
      · exact ih 1 (ys 1) h1 (hys 1 (by rw [stepTn_T]; simp)) b hb

/-- Every sequence of declared actions is the yield of a valid tree for `c`. -/
theorem reg_tree (d : StripsDesc) : ∀ π : List ℕ, (∀ a ∈ π, a ∈ d.actions.map ActDesc.name) →
    ∃ dt : DTree ℕ ℕ ℕ, dt.Valid (regOfStrips d).toProblem.methods (Sum.inr 0) ∧ dt.Yield π := by
  intro π
  induction π with
  | nil =>
    intro _
    refine ⟨.node 0 (MethodDesc.toMethod (0, emptyTnD)) (fun _ => .leaf 0),
      .node ⟨(0, emptyTnD), by simp [ProbDesc.toProblem, ProbDesc.methods, regOfStrips, regMethods],
        rfl⟩ rfl (fun t ht => by
          simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht), ?_⟩
    exact .node (fun _ => []) (fun t ht => by
      simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht)
      ((ordMerge_empty emptyTnD_T).2 rfl)
  | cons p π ih =>
    intro hdecl
    obtain ⟨dt, hv, hy⟩ := ih fun a ha => hdecl a (by simp [ha])
    obtain ⟨a, ha, hap⟩ := List.mem_map.1 (hdecl p (by simp))
    refine ⟨.node 0 (MethodDesc.toMethod (0, stepTn p)) (fun t => if t = 0 then .leaf p else dt),
      .node ⟨(0, stepTn p), by
        simp only [ProbDesc.toProblem, ProbDesc.methods, regOfStrips, regMethods, List.mem_cons,
          List.mem_map]
        exact Or.inr ⟨a, ha, by rw [hap]⟩, rfl⟩ rfl (fun t ht => ?_), ?_⟩
    · simp only [MethodDesc.toMethod, stepTn_T, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · simp only [MethodDesc.toMethod, stepTn_α0, if_true]; exact .leaf p
      · simp only [MethodDesc.toMethod, stepTn_α1, one_ne_zero, if_false]; exact hv
    · refine .node (fun t => if t = 0 then [p] else π) (fun t ht => ?_) ?_
      · simp only [MethodDesc.toMethod, stepTn_T, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · simp only [if_true]; exact .leaf p
        · simp only [one_ne_zero, if_false]; exact hy
      · simp only [MethodDesc.toMethod]
        rw [ordMerge_pair (TnDesc.toTaskNetwork_wf _) (stepTn_T _) (by decide) (stepTn_ord _)]
        simp

/-- **The encoding has a solution iff the STRIPS problem has a plan.** -/
theorem regOfStrips_solvable_iff (d : StripsDesc) :
    (regOfStrips d).toProblem.Solvable ↔ d.Solvable := by
  rw [Problem.solvable_iff_trees _ (toProblem_wf _)]
  have hT : (regOfStrips d).toProblem.tnI.T = {0} := rootTn_T
  have hα : (regOfStrips d).toProblem.tnI.α 0 = Sum.inr 0 := rootTn_α0
  have hwf : (regOfStrips d).toProblem.tnI.WF := TnDesc.toTaskNetwork_wf _
  constructor
  · rintro ⟨trees, π, s, ⟨hval, ys, hys, hm⟩, hrun, hg⟩
    obtain rfl := (ordMerge_single hwf hT).1 hm
    have hv := hval 0 (by rw [hT]; simp)
    rw [hα] at hv
    have hdecl := reg_yield d (trees 0) (ys 0) hv (hys 0 (by rw [hT]; simp))
    exact ⟨ys 0, hdecl, s, (run_congr (regOfStrips_δ d) _ _ _).1 hrun, hg⟩
  · rintro ⟨π, hdecl, s, hrun, hg⟩
    obtain ⟨dt, hv, hy⟩ := reg_tree d π hdecl
    refine ⟨fun _ => dt, π, s, ⟨fun t ht => ?_, fun _ => π, fun t ht => hy, (ordMerge_single hwf hT).2 rfl⟩,
      (run_congr (regOfStrips_δ d) _ _ _).2 hrun, hg⟩
    rw [hT] at ht
    obtain rfl : t = 0 := by simpa using ht
    rw [hα]; exact hv

/-! ### The class of the encoding -/

theorem regOfStrips_methods_cases (d : StripsDesc) {m : Method ℕ ℕ ℕ}
    (hm : m ∈ (regOfStrips d).toProblem.methods) :
    m = MethodDesc.toMethod (0, emptyTnD) ∨ ∃ p, m = MethodDesc.toMethod (0, stepTn p) := by
  obtain ⟨e, he, rfl⟩ := hm
  simp only [ProbDesc.methods, regOfStrips, regMethods, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨a, -, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem stepTn_regular (p : ℕ) : (stepTn p).toTaskNetwork.IsRegular := by
  refine ⟨fun t ht t' ht' ha ha' => ?_, fun t ht ha t' ht' hne => ?_⟩
  · rw [stepTn_T] at ht ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ht'
    obtain ⟨c, hc⟩ := ha
    obtain ⟨c', hc'⟩ := ha'
    rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
    · rfl
    · rw [stepTn_α0] at hc; cases hc
    · rw [stepTn_α0] at hc'; cases hc'
    · rfl
  · rw [stepTn_T] at ht ht'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ht'
    obtain ⟨c, hc⟩ := ha
    rcases ht with rfl | rfl
    · rw [stepTn_α0] at hc; cases hc
    · rcases ht' with rfl | rfl
      · exact stepTn_ord p
      · exact absurd rfl hne

theorem regOfStrips_isREG (d : StripsDesc) : (regOfStrips d).toProblem.IsREG := by
  rintro m ⟨hm, -⟩
  rcases regOfStrips_methods_cases d hm with rfl | ⟨p, rfl⟩
  · constructor <;> intro t ht <;>
      simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht
  · exact stepTn_regular p

theorem regOfStrips_isTO (d : StripsDesc) : (regOfStrips d).toProblem.IsTO := by
  refine ⟨fun t ht t' ht' hne => ?_, fun m hm' => ?_⟩
  all_goals try (obtain ⟨hm, -⟩ := hm')
  · have hT : (regOfStrips d).toProblem.toPos.tnI.T = {0} := rootTn_T
    rw [hT] at ht ht'
    simp at ht ht'
    exact absurd (ht.trans ht'.symm) hne
  · rcases regOfStrips_methods_cases d hm with rfl | ⟨p, rfl⟩
    · intro t ht; simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht
    · intro t ht t' ht' hne
      simp only [MethodDesc.toMethod, stepTn_T, Finset.mem_insert, Finset.mem_singleton] at ht ht'
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl (stepTn_ord p)
      · exact Or.inr (stepTn_ord p)
      · exact absurd rfl hne

/-! ### Well-formedness and polynomial time -/

theorem regOfStrips_valid_iff (d : StripsDesc) : (regOfStrips d).Valid ↔ d.Valid := by
  constructor
  · exact fun h => h.names_nodup
  · intro h
    refine ⟨h, ?_, fun m hm => ?_⟩
    · show TnValid _ rootTn
      exact ⟨by simp [rootTn, TnDesc.ids], by simp [rootTn, TnDesc.ordList],
        by simp [rootTn, TnDesc.ordList], by simp [rootTn, TnDesc.ordList],
        by simp [rootTn, TnDesc.lbl, TnDesc.ids], by simp [rootTn, TnDesc.lbl]⟩
    simp only [ProbDesc.methods, regOfStrips, regMethods, List.mem_cons, List.mem_map] at hm
    rcases hm with rfl | ⟨a, ha, rfl⟩
    · exact ⟨by simp [emptyTnD, TnDesc.ids], by simp [emptyTnD, TnDesc.ordList],
        by simp [emptyTnD, TnDesc.ordList], by simp [emptyTnD, TnDesc.ordList],
        by simp [emptyTnD, TnDesc.lbl, TnDesc.ids], by simp [emptyTnD, TnDesc.lbl]⟩
    · refine ⟨by simp [stepTn, TnDesc.ids], by simp [stepTn, TnDesc.ordList, TnDesc.ids],
        by simp [stepTn, TnDesc.ordList], ?_, ?_, ?_⟩
      · intro x y z h1 h2; simp [stepTn, TnDesc.ordList] at h1 h2; omega
      · simp only [stepTn, TnDesc.lbl, TnDesc.ids, List.map_cons, List.map_nil]; exact List.Perm.refl _
      · intro q hq hf
        simp only [stepTn, TnDesc.lbl, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl
        · exact List.mem_map.2 ⟨a, ha, rfl⟩
        · simp at hf

theorem pt_stepTn {α : Type} [BEnc α] {f : α → ℕ} (hf : PT f) : PT fun x => stepTn (f x) := by
  unfold stepTn
  exact PT.pair (PT.const _) (PT.pair (PT.const _) (PT.cons (PT.pair (PT.const 0)
    (PT.pair (PT.const false) hf)) (PT.const _)))

theorem pt_regOfStrips : PT regOfStrips := by
  unfold regOfStrips regMethods
  exact PT.pair (PT.pair PT.fst (PT.cons (PT.const _) (PT.map PT.fst
    (PT.pair (PT.const 0) (pt_stepTn (PT.fst.comp PT.snd))))))
    (PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.const _) (PT.snd.comp PT.snd)))

/-! ### The theorems -/

/-- An invalid description (two actions with the same name). -/
def badDesc : ProbDesc := (([(0, [], [], [], []), (0, [], [], [], [])], []), ([], ([], [], []), [], []))

theorem not_valid_badDesc : ¬ badDesc.Valid := by
  intro h
  have := h.names_nodup
  simp [badDesc, ProbDesc.actions, ActDesc.name] at this

/-- **PSPACE-hardness from a polynomial-time encoding of STRIPS.** -/
theorem pspaceHard_of_strips {Y : PClass} {f : StripsDesc → ProbDesc} (hf : PT f)
    (hvalid : ∀ d, (f d).Valid ↔ d.Valid) (hY : ∀ d, d.Valid → Y (f d).toProblem)
    (hsol : ∀ d, d.Valid → ((f d).toProblem.Solvable ↔ d.Solvable)) :
    Cx.Hard Cx.PSPACE (PlanEx Y) :=
  fun L hL => (strips_pspaceHard L hL).trans (redP_codeLang (α := StripsDesc) (β := ProbDesc)
    (R := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.Solvable) hf
    (fun d => ⟨fun h => ⟨(hvalid d).2 h.1, hY d h.1, (hsol d h.1).2 h.2⟩,
      fun h => ⟨(hvalid d).1 h.1, (hsol d ((hvalid d).1 h.1)).1 h.2.2⟩⟩)
    badDesc (fun h => not_valid_badDesc h.1))

/-- **Theorem 4.3.1.** `PlanEx^{REG∩TO}`, `PlanEx^{REG∩TO-M}` and `PlanEx^{REG}` are PSPACE-hard. -/
theorem thm_4_3_1 :
    Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsREG ∧ P.IsTO) ∧
      Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsREG ∧ P.IsTO_M) ∧
      Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsREG) :=
  ⟨pspaceHard_of_strips pt_regOfStrips regOfStrips_valid_iff
      (fun d _ => ⟨regOfStrips_isREG d, regOfStrips_isTO d⟩) (fun d _ => regOfStrips_solvable_iff d),
    pspaceHard_of_strips pt_regOfStrips regOfStrips_valid_iff
      (fun d _ => ⟨regOfStrips_isREG d, (regOfStrips_isTO d).2⟩) (fun d _ => regOfStrips_solvable_iff d),
    pspaceHard_of_strips pt_regOfStrips regOfStrips_valid_iff
      (fun d _ => regOfStrips_isREG d) (fun d _ => regOfStrips_solvable_iff d)⟩

theorem regOfStrips_tailRec_h (d : StripsDesc) {h : ℕ} (hh : 1 ≤ h) :
    (regOfStrips d).toProblem.IsTailREC_h h := by
  obtain ⟨le, hle, f, hf, hfle⟩ :=
    (Problem.thm_3_0_1 _ (toProblem_wf _)).1 (regOfStrips_isREG d)
  exact ⟨le, hle, f, fun c hc => lt_of_lt_of_le (hf c hc) hh, hfle⟩

/-- **Corollary 4.3.2.** `PlanEx^{TAIL-REC∩TO}` and `PlanEx^{TAIL-REC∩TO-M}` are PSPACE-hard. -/
theorem cor_4_3_2 :
    Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsTailREC ∧ P.IsTO) ∧
      Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsTailREC ∧ P.IsTO_M) :=
  ⟨pspaceHard_of_strips pt_regOfStrips regOfStrips_valid_iff
      (fun d _ => ⟨(regOfStrips_tailRec_h d le_rfl).isTailRecursive, regOfStrips_isTO d⟩)
      (fun d _ => regOfStrips_solvable_iff d),
    pspaceHard_of_strips pt_regOfStrips regOfStrips_valid_iff
      (fun d _ => ⟨(regOfStrips_tailRec_h d le_rfl).isTailRecursive, (regOfStrips_isTO d).2⟩)
      (fun d _ => regOfStrips_solvable_iff d)⟩

/-- **Corollary 4.3.3.** `PlanEx^{TAIL-REC_h}` is PSPACE-hard for every fixed `h ≥ 1`. -/
theorem cor_4_3_3 {h : ℕ} (hh : 1 ≤ h) : Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsTailREC_h h) :=
  pspaceHard_of_strips pt_regOfStrips regOfStrips_valid_iff
    (fun d _ => regOfStrips_tailRec_h d hh) (fun d _ => regOfStrips_solvable_iff d)

end Article

end HTN
