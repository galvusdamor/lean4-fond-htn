import FondHtn.Prim.WeakMem
import FondHtn.FixedMethodsLemmas
import FondHtn.Alt.Depth
import HtnComplexity.Article.ProgDescPT
/-!
# Strong OD solvability as an AND-OR game on descriptions

A game configuration (`FOND.SOD.GCfg`) is `(tag, x, s, d)`: a tag, a task id, a state (a list of
facts) and a task network description `d` (with its *listed* order, `HTN.Article.cfgNet`).

* tag `0` — *existential play* position: the player chooses an unconstrained primitive task `x`
  of `d` whose action is applicable in `s`; accepting iff `d` has no tasks;
* tag `1` — *universal* position after choosing `x`: every effect `e` of the action of `x` leads
  to `(0, 0, s[e], d ∖ x)` (`HTN.Article.progDesc`);
* tag `2` (and larger) — *decomposition* position (existential): decompose some compound task of
  `d` by some method of its name (`HTN.Article.decDesc`), or, if `d` is primitive, start playing.

`FOND.SOD.gsuccs`, `FOND.SOD.gacc`, `FOND.SOD.guni` are polynomial time.  The play positions
evaluate exactly the solvable belief states of [DB25] (`FOND.SOD.gameVal_play_iff`): for a
configuration satisfying the invariant `HTN.Article.CfgInv`, with budget at least twice the
number of tasks, the game is won iff `(cfgNet d, s)` is a solvable belief state.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

/-- A game configuration: tag, task id, state, network. -/
abbrev GCfg : Type := ℕ × ℕ × List ℕ × TnDesc

instance instDecEqGCfg : DecidableEq GCfg :=
  @instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _ inferInstance (inferInstanceAs (DecidableEq TnDesc))))

/-- Applicability of the action `a` in the list state `s`. -/
def appB (p : FProbDesc) (a : ℕ) (s : List ℕ) : Bool :=
  (actL p a).1.all (fun f => decide (f ∈ s)) && (actL p a).2.1.all (fun f => !decide (f ∈ s))

/-- `x` has no predecessor in the listed order. -/
def readyB (d : TnDesc) (x : ℕ) : Bool := d.ordList.all fun q => q.2 != x

/-- The existential play moves. -/
def playMoves (p : FProbDesc) (s : List ℕ) (d : TnDesc) : List GCfg :=
  (d.ids.filter fun x => readyB d x && !(lblOf d x).1 && appB p (lblOf d x).2 s).map
    fun x => (1, x, s, d)

/-- The outcomes of executing `x`. -/
def outMoves (p : FProbDesc) (x : ℕ) (s : List ℕ) (d : TnDesc) : List GCfg :=
  (actL p (lblOf d x).2).2.2.map fun e => (0, 0, (nextL s e).dedup, progDesc d x)

/-- The decomposition moves (and the start of the play once `d` is primitive). -/
def decMoves (p : FProbDesc) (s : List ℕ) (d : TnDesc) : List GCfg :=
  (d.ids.flatMap fun x => bif (lblOf d x).1 then
      (p.methods.filter fun e => e.1 == (lblOf d x).2).map fun e => (2, 0, s, decDesc d x e)
    else []) ++
  (bif d.ids.all (fun x => !(lblOf d x).1) then [(0, 0, s, d)] else [])

/-- **The successors.** -/
def gsuccs (y : FProbDesc × GCfg) : List GCfg :=
  bif y.2.1 == 0 then playMoves y.1 y.2.2.2.1 y.2.2.2.2
  else bif y.2.1 == 1 then outMoves y.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2
  else decMoves y.1 y.2.2.2.1 y.2.2.2.2

/-- Accepting: a play position with no tasks left. -/
def gacc (y : FProbDesc × GCfg) : Bool := y.2.1 == 0 && y.2.2.2.2.ids.isEmpty

/-- Universal: the positions after choosing a task. -/
def guni (y : FProbDesc × GCfg) : Bool := y.2.1 == 1

/-! ## Polynomial time -/

theorem pt_appB {P : α → FProbDesc} {A : α → ℕ} {S : α → List ℕ} [BEnc α] (hP : PT P) (hA : PT A)
    (hS : PT S) : PT fun z => appB (P z) (A z) (S z) := by
  have hL : PT fun z => actL (P z) (A z) := pt_actL.comp (PT.pair hP hA)
  unfold appB
  exact PT.and (PT.all (PT.fst.comp hL) (PT.elem (hS.comp PT.fst) PT.snd))
    (PT.all (PT.fst.comp (PT.snd.comp hL)) (PT.not (PT.elem (hS.comp PT.fst) PT.snd)))

theorem pt_gsuccs : PT gsuccs := by
  have hp : PT fun y : FProbDesc × GCfg => y.1 := PT.fst
  have hx : PT fun y : FProbDesc × GCfg => y.2.2.1 := PT.fst.comp (PT.snd.comp PT.snd)
  have hs : PT fun y : FProbDesc × GCfg => y.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hd : PT fun y : FProbDesc × GCfg => y.2.2.2.2 :=
    PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hids : PT fun y : FProbDesc × GCfg => y.2.2.2.2.ids := PT.fst.comp hd
  have hplay : PT fun y : FProbDesc × GCfg => playMoves y.1 y.2.2.2.1 y.2.2.2.2 := by
    unfold playMoves readyB
    have hl : PT fun z : (FProbDesc × GCfg) × ℕ => lblOf z.1.2.2.2.2 z.2 :=
      pt_lblOf (hd.comp PT.fst) PT.snd
    exact PT.map (PT.filter hids (PT.and (PT.and
      (PT.all (PT.fst.comp (PT.snd.comp (hd.comp PT.fst)))
        (PT.not (PT.beq (PT.snd.comp PT.snd) (PT.snd.comp PT.fst))))
      (PT.not (PT.fst.comp hl))) (pt_appB (hp.comp PT.fst) (PT.snd.comp hl) (hs.comp PT.fst))))
      (PT.pair (PT.const 1) (PT.pair PT.snd (PT.pair (hs.comp PT.fst) (hd.comp PT.fst))))
  have hout : PT fun y : FProbDesc × GCfg => outMoves y.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 := by
    unfold outMoves
    have hl : PT fun y : FProbDesc × GCfg => lblOf y.2.2.2.2 y.2.2.1 := pt_lblOf hd hx
    exact PT.map (PT.snd.comp (PT.snd.comp (pt_actL.comp (PT.pair hp (PT.snd.comp hl)))))
      (PT.pair (PT.const 0) (PT.pair (PT.const 0) (PT.pair
        (PT.dedup (PT.append (PT.filter (hs.comp PT.fst)
          (PT.not (PT.elem (PT.snd.comp (PT.snd.comp PT.fst)) PT.snd))) (PT.fst.comp PT.snd)))
        (pt_progDesc.comp (PT.pair (hd.comp PT.fst) (hx.comp PT.fst))))))
  have hdec : PT fun y : FProbDesc × GCfg => decMoves y.1 y.2.2.2.1 y.2.2.2.2 := by
    unfold decMoves
    have hl : PT fun z : (FProbDesc × GCfg) × ℕ => lblOf z.1.2.2.2.2 z.2 :=
      pt_lblOf (hd.comp PT.fst) PT.snd
    refine PT.append (PT.flatMap hids (PT.cond (PT.fst.comp hl)
      (PT.map (PT.filter (PT.snd.comp (PT.fst.comp (hp.comp PT.fst)))
        (PT.beq (PT.fst.comp PT.snd) (PT.snd.comp (hl.comp PT.fst))))
        (PT.pair (PT.const 2) (PT.pair (PT.const 0) (PT.pair (hs.comp (PT.fst.comp PT.fst))
          (pt_decDesc.comp (PT.pair (hd.comp (PT.fst.comp PT.fst))
            (PT.pair (PT.snd.comp PT.fst) PT.snd)))))))
      PT.nil))
      (PT.cond (PT.all hids (PT.not (PT.fst.comp hl)))
        (PT.single (PT.pair (PT.const 0) (PT.pair (PT.const 0) (PT.pair hs hd)))) PT.nil)
  unfold gsuccs
  exact PT.cond (PT.beq (PT.fst.comp PT.snd) (PT.const 0)) hplay
    (PT.cond (PT.beq (PT.fst.comp PT.snd) (PT.const 1)) hout hdec)

theorem pt_gacc : PT gacc :=
  PT.and (PT.beq (PT.fst.comp PT.snd) (PT.const 0))
    (PT.isEmpty (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))

theorem pt_guni : PT guni := PT.beq (PT.fst.comp PT.snd) (PT.const 1)

/-! ## Semantics of the play positions -/

section Sem

variable {p : FProbDesc}

theorem gameVal_zero' (c : GCfg) : gameVal gacc guni gsuccs p 0 c = gacc (p, c) := rfl

theorem gameVal_succ' (k : ℕ) (c : GCfg) : gameVal gacc guni gsuccs p (k + 1) c =
    (gacc (p, c) || bif guni (p, c) then (gsuccs (p, c)).all (gameVal gacc guni gsuccs p k)
      else (gsuccs (p, c)).any (gameVal gacc guni gsuccs p k)) := rfl

theorem appB_iff (a : ℕ) (s : List ℕ) :
    appB p a s = true ↔ (p.δ a).Applicable {f | f ∈ s} := by
  rw [δ_eq_actL]
  simp [appB, Action.Applicable, FActDesc.toAction, Set.subset_def, Set.disjoint_left]

theorem mem_outcomes_iff (a : ℕ) (s : List ℕ) (S' : Set ℕ) :
    S' ∈ (p.δ a).outcomes {f | f ∈ s} ↔ ∃ e ∈ (actL p a).2.2, S' = {f | f ∈ nextL s e} := by
  rw [δ_eq_actL, Action.mem_outcomes]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, (nextL_eq s e).symm⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, nextL_eq s e⟩

theorem setOf_mem_dedup (l : List ℕ) : {f | f ∈ l.dedup} = {f | f ∈ l} := by
  ext f; simp

theorem sameOn_of_agree {tn tn' : TaskNetwork ℕ ℕ ℕ} (h : tn.Agree tn') :
    FOND.TaskNetwork.SameOn tn tn' :=
  ⟨h.1, fun a _ b _ => by rw [h.2.1], h.2.2⟩

theorem sameOn_trans {tn tn' tn'' : TaskNetwork ℕ ℕ ℕ} (h : FOND.TaskNetwork.SameOn tn tn')
    (h' : FOND.TaskNetwork.SameOn tn' tn'') : FOND.TaskNetwork.SameOn tn tn'' := by
  obtain ⟨hT, ho, hα⟩ := h
  obtain ⟨hT', ho', hα'⟩ := h'
  refine ⟨hT.trans hT', fun a ha b hb => (ho a ha b hb).trans (ho' a (hT ▸ ha) b (hT ▸ hb)),
    fun a ha => (hα a ha).trans (hα' a (hT ▸ ha))⟩

theorem readyB_iff (d : TnDesc) (x : ℕ) : readyB d x = true ↔ ∀ q ∈ d.ordList, q.2 ≠ x := by
  simp [readyB]

theorem unconstrained_iff {s : List ℕ} {d : TnDesc} (hc : CfgInv (s, d)) (x : ℕ) :
    (cfgNet d).Unconstrained x ↔ x ∈ d.ids ∧ readyB d x = true := by
  rw [readyB_iff]
  constructor
  · rintro ⟨hx, hu⟩
    refine ⟨by simpa [cfgNet] using hx, fun q hq hqx => ?_⟩
    obtain ⟨a, b⟩ := q
    simp only at hqx
    subst hqx
    exact hu a (hc.wf.mem_left (t' := b) hq) hq
  · rintro ⟨hx, hu⟩
    exact unconstrained_cfgNet hx hu

theorem lblOf_eq_of_α {d : TnDesc} {x a : ℕ} (h : (cfgNet d).α x = Sum.inl a) :
    lblOf d x = (false, a) := by
  rw [cfgNet_label] at h
  exact toSum_eq_inl.1 h

theorem cfgNet_α_of_lbl {d : TnDesc} {x : ℕ} (h : (lblOf d x).1 = false) :
    (cfgNet d).α x = Sum.inl (lblOf d x).2 := by
  rw [cfgNet_label, toSum, h]; rfl

theorem length_progDesc_ids {d : TnDesc} (hn : d.ids.Nodup) {x : ℕ} (hx : x ∈ d.ids) :
    (progDesc d x).ids.length + 1 = d.ids.length := by
  show (d.ids.filter fun y => decide (y ≠ x)).length + 1 = d.ids.length
  have h2 : (d.ids.filter fun y => decide (y ≠ x)) = d.ids.erase x := by
    rw [hn.erase_eq_filter]; congr 1; funext y; by_cases h : y = x <;> simp [h]
  rw [h2, List.length_erase_of_mem hx]
  have := List.length_pos_of_mem hx
  omega

/-- **Soundness of the play positions.** -/
theorem play_sound : ∀ k y s d, CfgInv (s, d) →
    gameVal gacc guni gsuccs p k (0, y, s, d) = true →
      p.toProblem.BeliefSolvable (cfgNet d) {f | f ∈ s} := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro y s d hc hw
    by_cases hd : d.ids = []
    · exact .empty (by simp [cfgNet, hd])
    have hacc : gacc (p, ((0 : ℕ), y, s, d)) = false := by simp [gacc, hd]
    rcases k with _ | k
    · rw [gameVal_zero', hacc] at hw; cases hw
    rw [gameVal_succ', hacc] at hw
    simp only [guni, gsuccs, Bool.false_or, beq_self_eq_true, cond_true,
      show ((0 : ℕ) == 1) = false from rfl, cond_false, List.any_eq_true] at hw
    obtain ⟨c, hcm, hw⟩ := hw
    simp only [playMoves, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hcm
    obtain ⟨x, ⟨hx, ⟨hr, hprim⟩, happ⟩, rfl⟩ := hcm
    rcases k with _ | k
    · rw [gameVal_zero'] at hw; simp [gacc] at hw
    rw [gameVal_succ'] at hw
    simp only [gacc, guni, gsuccs, show ((1 : ℕ) == 0) = false from rfl, Bool.false_and,
      Bool.false_or, cond_false, beq_self_eq_true, cond_true, List.all_eq_true] at hw
    have hu := (unconstrained_iff hc x).2 ⟨hx, hr⟩
    have hr' := (readyB_iff d x).1 hr
    refine .step hu (cfgNet_α_of_lbl hprim) ((appB_iff _ _).1 happ) fun S' hS' => ?_
    obtain ⟨e, he, rfl⟩ := (mem_outcomes_iff _ _ _).1 hS'
    have h := ih k (by omega) 0 _ _ (inv_progDesc hc hx hr' (List.nodup_dedup _))
      (hw _ (List.mem_map.2 ⟨e, he, rfl⟩))
    rw [setOf_mem_dedup] at h
    exact FOND.Problem.BeliefSolvable.congr _ h (sameOn_of_agree (agree_progDesc hr').symm)

/-- **Completeness of the play positions.** -/
theorem play_complete {tn : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ}
    (h : p.toProblem.BeliefSolvable tn S) : ∀ k y s d, FOND.TaskNetwork.SameOn tn (cfgNet d) →
      S = {f | f ∈ s} → CfgInv (s, d) → 2 * d.ids.length ≤ k →
        gameVal gacc guni gsuccs p k (0, y, s, d) = true := by
  induction h with
  | empty hT =>
    intro k y s d hS _ _ _
    have hd : d.ids = [] := by
      have := hS.1 ▸ hT
      simpa [cfgNet] using this
    exact gameVal_of_acc (acc := gacc) (uni := guni) (succs := gsuccs) (a := p)
      (c := ((0 : ℕ), y, s, d)) (by simp [gacc, hd]) k
  | @step tn S t a hu hα happ _ ih =>
    intro k y s d hS hSs hc hk
    subst hSs
    have hu' := (unconstrained_iff hc t).1 (hS.unconstrained hu)
    have hα' : (cfgNet d).α t = Sum.inl a := (hS.2.2 t hu.1).symm.trans hα
    have hl := lblOf_eq_of_α hα'
    have hlen := List.length_pos_of_mem hu'.1
    have hk' : 2 * d.ids.length ≤ k := hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    rw [gameVal_succ']
    simp only [guni, gsuccs, Bool.or_eq_true, beq_self_eq_true, cond_true,
      show ((0 : ℕ) == 1) = false from rfl, cond_false, List.any_eq_true]
    refine Or.inr ⟨(1, t, s, d), ?_, ?_⟩
    · simp only [playMoves, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨t, ⟨hu'.1, ⟨hu'.2, by rw [hl]⟩, by rw [hl]; exact (appB_iff _ _).2 happ⟩, rfl⟩
    rw [gameVal_succ']
    simp only [gacc, guni, gsuccs, show ((1 : ℕ) == 0) = false from rfl, Bool.false_and,
      Bool.false_or, cond_false, beq_self_eq_true, cond_true, List.all_eq_true, outMoves, hl,
      List.mem_map]
    rintro _ ⟨e, he, rfl⟩
    have hr' := (readyB_iff d t).1 hu'.2
    have hlen' := length_progDesc_ids (d := d) hc.ids_nodup hu'.1
    refine ih {f | f ∈ nextL s e} ((mem_outcomes_iff _ _ _).2 ⟨e, he, rfl⟩) k 0 _ _
      (sameOn_trans (hS.progress t) (sameOn_of_agree (agree_progDesc hr')))
      (setOf_mem_dedup _).symm (inv_progDesc hc hu'.1 hr' (List.nodup_dedup _)) (by omega)

end Sem

end SOD

end FOND
