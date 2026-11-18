import HtnComplexity.Computable.PoNet
import HtnComplexity.Computable.StripsDecide
import HtnPlanning.Progression.ProgressionSound
import HtnPlanning.Core.DecompositionIso
import HtnPlanning.Progression.ProgressionSplit
/-!
# Progression search on descriptions

`HtnComplexity/Computable/PoNet.lean` supplies the search networks and their two
operations.  This file turns them into a **search space of descriptions** and proves it sound
and complete for the semantic progression search of `HtnPlanning/Progression/Progression.lean`:

* `HTN.Syn.PConfig` — a search configuration: the current state, as a list of facts, and the
  search network;
* `HTN.Syn.succsOf d c` — the *list* of successors of a configuration: every unconstrained task
  of the network is either executed (if it is primitive and applicable) or decomposed by every
  listed method for its compound name;
* `HTN.Syn.PReach d` — reachability in that space, and `HTN.Syn.isGoalB q` the goal test;
* `HTN.Syn.solvable_iff_exists_pReach` — **the described problem is solvable exactly when a
  goal configuration is reachable**.

Soundness is a direct simulation, using `HTN.Syn.PNet.toTN_finish` and
`HTN.Syn.PNet.toTN_expand`: a successor of `c` denotes a `HTN.Problem.Step` of the described
problem.  Completeness needs the converse *up to isomorphism*, since a semantic decomposition
step inserts an arbitrary fresh copy of the method's subtask network while `PNet.expand`
inserts one particular copy; `HTN.decomposeWith_iso_congr` and `HTN.TaskNetwork.iso_progress`
are what transport the search along an isomorphism.
-/

namespace HTN

namespace Syn

/-- A **search configuration**: the current state, as a list of facts, and the search
network. -/
abbrev PConfig : Type := List ℕ × PNet

/-- The items of a search network that are still to be processed and have no predecessor
left. -/
def readyItems (p : PNet) : PNet := p.filter (fun x => x.2.2.1 && x.2.2.2.isEmpty)

theorem mem_readyItems {p : PNet} {x : PItem} :
    x ∈ readyItems p ↔ x ∈ p ∧ x.2.2.1 = true ∧ x.2.2.2 = [] := by
  simp only [readyItems, List.mem_filter, Bool.and_eq_true, List.isEmpty_iff]

/-- **The successors of a search configuration.** -/
def succsOf (d : DomDesc) (c : PConfig) : List PConfig :=
  (readyItems c.2).flatMap (fun x =>
    if x.2.1.1 then
      (d.methods.filter (fun e => e.1 = x.2.1.2)).map (fun e => (c.1, PNet.expand c.2 x.1 e))
    else if applB d c.1 x.2.1.2 then [(stepL d c.1 x.2.1.2, PNet.finish c.2 x.1)] else [])

/-- One step of the search space of descriptions. -/
def PStep (d : DomDesc) (c c' : PConfig) : Prop := c' ∈ succsOf d c

/-- Reachability in the search space of descriptions. -/
def PReach (d : DomDesc) : PConfig → PConfig → Prop := Relation.ReflTransGen (PStep d)

/-- The initial configuration of a described problem. -/
def initConfig (q : InstDesc) : PConfig := (q.initList, PNet.ofTnDesc q.tnI)

/-- The goal test: nothing left to process, and the goal holds. -/
def isGoalB (q : InstDesc) (c : PConfig) : Bool :=
  c.2.ids.isEmpty && q.goalList.all (fun f => memB c.1 f)

theorem mem_succsOf_iff {d : DomDesc} {c c' : PConfig} :
    c' ∈ succsOf d c ↔ ∃ x ∈ readyItems c.2,
      ((∃ e ∈ d.methods, x.2.1.1 = true ∧ e.1 = x.2.1.2 ∧
          c' = (c.1, PNet.expand c.2 x.1 e)) ∨
        (x.2.1.1 = false ∧ applB d c.1 x.2.1.2 = true ∧
          c' = (stepL d c.1 x.2.1.2, PNet.finish c.2 x.1))) := by
  simp only [succsOf, List.mem_flatMap]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  by_cases hk : x.2.1.1 = true
  · rw [if_pos hk]
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨e, ⟨he, hename⟩, rfl⟩
      exact Or.inl ⟨e, he, hk, hename, rfl⟩
    · rintro (⟨e, he, -, hename, rfl⟩ | ⟨hk', -, -⟩)
      · exact ⟨e, ⟨he, hename⟩, rfl⟩
      · rw [hk] at hk'
        exact absurd hk' (by simp)
  · have hk' : x.2.1.1 = false := by simpa using hk
    rw [if_neg hk]
    by_cases happ : applB d c.1 x.2.1.2 = true
    · rw [if_pos happ]
      simp only [List.mem_singleton]
      constructor
      · intro h
        exact Or.inr ⟨hk', happ, h⟩
      · rintro (⟨e, -, hk'', -, -⟩ | ⟨-, -, h⟩)
        · rw [hk'] at hk''
          exact absurd hk'' (by simp)
        · exact h
    · rw [if_neg happ]
      refine iff_of_false (by simp) ?_
      rintro (⟨e, -, hk'', -, -⟩ | ⟨-, happ', -⟩)
      · rw [hk'] at hk''
        exact absurd hk'' (by simp)
      · exact happ happ'

/-! ### The invariant is preserved -/

theorem ok_of_pStep {d : DomDesc} {c c' : PConfig} (hOk : PNet.Ok c.2) (h : PStep d c c') :
    PNet.Ok c'.2 := by
  obtain ⟨x, hx, hcase⟩ := mem_succsOf_iff.1 h
  obtain ⟨hxm, hpres, -⟩ := mem_readyItems.1 hx
  have hids : x.1 ∈ c.2.ids := PNet.mem_ids.2 ⟨x, hxm, rfl, hpres⟩
  rcases hcase with ⟨e, -, -, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact PNet.expand_ok hOk hids e
  · exact PNet.finish_ok hOk x.1

theorem ok_of_pReach {d : DomDesc} {c c' : PConfig} (hOk : PNet.Ok c.2) (h : PReach d c c') :
    PNet.Ok c'.2 := by
  induction h with
  | refl => exact hOk
  | tail _ hstep ih => exact ok_of_pStep ih hstep

/-! ### Soundness: a successor is a step of the semantic search -/

theorem unconstrained_of_ready {p : PNet} (hOk : PNet.Ok p) {x : PItem} (hx : x ∈ readyItems p) :
    (PNet.toTN p).Unconstrained x.1 := by
  obtain ⟨hxm, hpres, hdeps⟩ := mem_readyItems.1 hx
  refine ⟨List.mem_toFinset.2 (PNet.mem_ids.2 ⟨x, hxm, rfl, hpres⟩), ?_⟩
  intro t' _
  show t' ∉ p.deps x.1
  rw [PNet.deps_eq_of_mem hxm hOk.nodup, hdeps]
  simp

theorem step_of_pStep {d : DomDesc} {q : InstDesc} {c c' : PConfig} (hOk : PNet.Ok c.2)
    (h : PStep d c c') (π : List ℕ) :
    ∃ π', (problem d q).Step ⟨{f | f ∈ c.1}, PNet.toTN c.2, π⟩
      ⟨{f | f ∈ c'.1}, PNet.toTN c'.2, π'⟩ := by
  obtain ⟨x, hx, hcase⟩ := mem_succsOf_iff.1 h
  obtain ⟨hxm, hpres, hdeps⟩ := mem_readyItems.1 hx
  have hids : x.1 ∈ c.2.ids := PNet.mem_ids.2 ⟨x, hxm, rfl, hpres⟩
  have hunc : (PNet.toTN c.2).Unconstrained x.1 := unconstrained_of_ready hOk hx
  have hdepsnil : c.2.deps x.1 = [] := by rw [PNet.deps_eq_of_mem hxm hOk.nodup, hdeps]
  have hlbl : (PNet.toTN c.2).α x.1 = TnDesc.ofPair x.2.1 :=
    PNet.label_eq_of_head hxm rfl hOk.nodup
  rcases hcase with ⟨e, he, hk, hename, rfl⟩ | ⟨hk, happ, rfl⟩
  · refine ⟨π, Problem.Step.decomp (m := e.toMethod) hunc ?_⟩
    refine ⟨⟨e, he, rfl⟩, hunc.1, ?_, (TnDesc.shift c.2.freshOff e.2).toTaskNetwork,
      TnDesc.toTaskNetwork_wf _, TnDesc.shift_iso _ _, PNet.disjoint_shift c.2 e, ?_⟩
    · rw [hlbl]
      simp only [TnDesc.ofPair, hk, MethodDesc.toMethod_abstractTask, hename]
      simp
    · exact PNet.toTN_expand hOk hids e
  · refine ⟨π ++ [x.2.1.2], ?_⟩
    have hα : (PNet.toTN c.2).α x.1 = Sum.inl x.2.1.2 := by
      rw [hlbl]
      simp [TnDesc.ofPair, hk]
    have happ' : (problem d q).Applicable x.2.1.2 {f | f ∈ c.1} := by
      have := applB_iff.1 happ
      exact this
    have hstep := Problem.Step.prog (P := problem d q) (π := π) hunc hα happ'
    have hstate : (problem d q).transition x.2.1.2 {f | f ∈ c.1} = {f | f ∈ stepL d c.1 x.2.1.2} :=
      (mem_stepL d c.1 x.2.1.2).symm
    rw [hstate, ← PNet.toTN_finish hdepsnil] at hstep
    exact hstep

/-! ### Completeness: a semantic step can be replayed -/

/-- The item of a search network that an isomorphism sends to a given unconstrained task. -/
theorem exists_ready_item {p : PNet} (hOk : PNet.Ok p) {tn : TaskNetwork ℕ ℕ ℕ} {σ : ℕ → ℕ}
    (hσbij : Set.BijOn σ ((PNet.toTN p).T : Set ℕ) (tn.T : Set ℕ))
    (hσord : ∀ x ∈ (PNet.toTN p).T, ∀ y ∈ (PNet.toTN p).T,
      ((PNet.toTN p).ord x y ↔ tn.ord (σ x) (σ y)))
    {t : ℕ} (hu : tn.Unconstrained t) :
    ∃ x ∈ readyItems p, σ x.1 = t ∧ x.1 ∈ (PNet.toTN p).T := by
  obtain ⟨i, hi, hit⟩ := hσbij.surjOn (by simpa using hu.1)
  have hiT : i ∈ (PNet.toTN p).T := by simpa using hi
  have hids : i ∈ p.ids := by simpa using hiT
  obtain ⟨x, hxm, hx1, hpres⟩ := PNet.mem_ids.1 hids
  have hdeps : x.2.2.2 = [] := by
    rw [← PNet.deps_eq_of_mem hxm hOk.nodup, hx1]
    rcases hd : p.deps i with _ | ⟨j, js⟩
    · rfl
    · exfalso
      have hj : j ∈ p.deps i := by rw [hd]; simp
      have hjids : j ∈ p.ids := PNet.mem_ids_of_mem_deps hOk hj
      have hjT : j ∈ (PNet.toTN p).T := by simpa using hjids
      have hord : (PNet.toTN p).ord j i := hj
      have := (hσord j hjT i hiT).1 hord
      rw [hit] at this
      exact hu.2 (σ j) (by simpa using hσbij.mapsTo (by simpa using hjT)) this
  exact ⟨x, mem_readyItems.2 ⟨hxm, hpres, hdeps⟩, by rw [hx1]; exact hit, by rw [hx1]; exact hiT⟩

theorem exists_pStep_of_step {d : DomDesc} {q : InstDesc} {c : PConfig}
    {n n' : SearchNode ℕ ℕ ℕ ℕ} (hOk : PNet.Ok c.2)
    (hstate : {f | f ∈ c.1} = n.state) (hiso : (PNet.toTN c.2).Iso n.net) (hwf : n.net.WF)
    (hstep : (problem d q).Step n n') :
    ∃ c', PStep d c c' ∧ {f | f ∈ c'.1} = n'.state ∧ (PNet.toTN c'.2).Iso n'.net := by
  obtain ⟨σ, hσbij, hσord, hσα⟩ := hiso
  cases hstep with
  | @prog s tn π t a hu hα happ =>
    simp only at hstate hσbij hσord hσα hwf ⊢
    obtain ⟨x, hx, hxt, hxT⟩ := exists_ready_item hOk hσbij hσord hu
    obtain ⟨hxm, hpres, hdeps⟩ := mem_readyItems.1 hx
    have hlbl : (PNet.toTN c.2).α x.1 = Sum.inl a := by
      rw [hσα x.1 hxT, hxt]
      exact hα
    have hpair : x.2.1 = (false, a) := by
      refine TnDesc.ofPair_eq_inl_iff.1 ?_
      rw [← PNet.label_eq_of_head hxm rfl hOk.nodup]
      exact hlbl
    have happ' : applB d c.1 x.2.1.2 = true := by
      rw [hpair]
      refine applB_iff.2 ?_
      rw [hstate]
      exact happ
    have hdepsnil : c.2.deps x.1 = [] := by rw [PNet.deps_eq_of_mem hxm hOk.nodup, hdeps]
    refine ⟨(stepL d c.1 x.2.1.2, PNet.finish c.2 x.1), mem_succsOf_iff.2
      ⟨x, hx, Or.inr ⟨by rw [hpair], happ', rfl⟩⟩, ?_, ?_⟩
    · rw [hpair]
      simp only
      rw [← hstate]
      exact mem_stepL d c.1 a
    · rw [PNet.toTN_finish hdepsnil]
      have := TaskNetwork.iso_progress hσbij hσord hσα hxT
      rwa [hxt] at this
  | @decomp s tn tn₂ π t m hu hdstep =>
    simp only at hstate hσbij hσord hσα hwf ⊢
    obtain ⟨hmM, htT, hαt, u, huwf, huiso, hdisj, rfl⟩ := hdstep
    obtain ⟨e, he, rfl⟩ := hmM
    obtain ⟨x, hx, hxt, hxT⟩ := exists_ready_item hOk hσbij hσord hu
    obtain ⟨hxm, hpres, hdeps⟩ := mem_readyItems.1 hx
    have hlbl : (PNet.toTN c.2).α x.1 = Sum.inr e.1 := by
      rw [hσα x.1 hxT, hxt]
      exact hαt
    have hpair : x.2.1 = (true, e.1) := by
      refine TnDesc.ofPair_eq_inr_iff.1 ?_
      rw [← PNet.label_eq_of_head hxm rfl hOk.nodup]
      exact hlbl
    have hids : x.1 ∈ c.2.ids := by simpa using hxT
    -- the copy the search inserts, and its isomorphism with the copy of the semantic step
    have hcopyiso : (TnDesc.shift c.2.freshOff e.2).toTaskNetwork.Iso u :=
      (TnDesc.shift_iso _ _).trans huiso.symm
    obtain ⟨ρ, hρbij, hρord, hρα⟩ := hcopyiso
    refine ⟨(c.1, PNet.expand c.2 x.1 e), mem_succsOf_iff.2
      ⟨x, hx, Or.inl ⟨e, he, by rw [hpair], by rw [hpair], rfl⟩⟩, hstate, ?_⟩
    simp only
    rw [PNet.toTN_expand hOk hids e]
    have hcong := decomposeWith_iso_congr (t := x.1) (σ := σ) (ρ := ρ) (PNet.toTN_wf hOk) hwf
      (TnDesc.toTaskNetwork_wf _) huwf (PNet.disjoint_shift c.2 e) hdisj hxT hσbij hσord hσα
      hρbij hρord hρα
    rwa [hxt] at hcong

/-! ### The two halves -/

theorem toTN_initConfig (q : InstDesc) :
    PNet.toTN (initConfig q).2 = q.tnI.toTaskNetwork := PNet.toTN_ofTnDesc q.tnI

theorem ok_initConfig (q : InstDesc) : PNet.Ok (initConfig q).2 := PNet.ofTnDesc_ok q.tnI

theorem solvable_of_pReach {d : DomDesc} {q : InstDesc} {c : PConfig}
    (h : PReach d (initConfig q) c) (hg : isGoalB q c = true) : Solvable d q := by
  have key : ∀ c' : PConfig, PReach d (initConfig q) c' → ∃ π : List ℕ,
      (problem d q).ReachableNode ⟨{f | f ∈ c'.1}, PNet.toTN c'.2, π⟩ := by
    intro c' hc'
    induction hc' with
    | refl =>
      refine ⟨[], ?_⟩
      have hnode : (⟨{f | f ∈ (initConfig q).1}, PNet.toTN (initConfig q).2, []⟩ :
          SearchNode ℕ ℕ ℕ ℕ) = (problem d q).initNode := by
        rw [toTN_initConfig]
        rfl
      rw [hnode]
      exact Problem.ReachableNode.refl _
    | @tail b c'' hr hstep ih =>
      obtain ⟨π, hπ⟩ := ih
      obtain ⟨π', hstep'⟩ := step_of_pStep (q := q) (ok_of_pReach (ok_initConfig q) hr) hstep π
      exact ⟨π', hπ.tail hstep'⟩
  obtain ⟨π, hπ⟩ := key c h
  rw [Solvable, Problem.solvable_iff_exists_goalNode (problem_wf d q)]
  refine ⟨_, hπ, ?_, ?_⟩
  · simp only [isGoalB, Bool.and_eq_true, List.isEmpty_iff] at hg
    show (PNet.toTN c.2).T = ∅
    rw [PNet.toTN_T, hg.1]
    rfl
  · simp only [isGoalB, Bool.and_eq_true, List.all_eq_true] at hg
    intro f hf
    have := hg.2 f (by simpa using hf)
    simpa using memB_iff.1 this

theorem exists_pReach_of_solvable {d : DomDesc} {q : InstDesc} (h : Solvable d q) :
    ∃ c, PReach d (initConfig q) c ∧ isGoalB q c = true := by
  rw [Solvable, Problem.solvable_iff_exists_goalNode (problem_wf d q)] at h
  obtain ⟨n, hr, hgT, hgs⟩ := h
  have key : ∀ n : SearchNode ℕ ℕ ℕ ℕ, (problem d q).ReachableNode n → ∃ c : PConfig,
      PReach d (initConfig q) c ∧ {f | f ∈ c.1} = n.state ∧ (PNet.toTN c.2).Iso n.net := by
    intro n hn
    induction hn with
    | refl =>
      refine ⟨initConfig q, Relation.ReflTransGen.refl, rfl, ?_⟩
      rw [toTN_initConfig]
      exact TaskNetwork.Iso.refl _
    | @tail b c'' hr hstep ih =>
      obtain ⟨c, hc, hst, hiso⟩ := ih
      have hwf : b.net.WF := (Problem.ReachableNode.wf (problem_wf d q) hr)
      obtain ⟨c', hstep', hst', hiso'⟩ :=
        exists_pStep_of_step (ok_of_pReach (ok_initConfig q) hc) hst hiso hwf hstep
      exact ⟨c', hc.tail hstep', hst', hiso'⟩
  obtain ⟨c, hc, hst, hiso⟩ := key n hr
  refine ⟨c, hc, ?_⟩
  have hTempty : (PNet.toTN c.2).T = ∅ := by
    have hcard := hiso.card_eq
    rw [hgT] at hcard
    exact Finset.card_eq_zero.1 (by simpa using hcard)
  simp only [isGoalB, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff]
  constructor
  · have h0 : c.2.ids.toFinset = (∅ : Finset ℕ) := hTempty
    refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
    have hmem : x ∈ c.2.ids.toFinset := List.mem_toFinset.2 hx
    rw [h0] at hmem
    simp at hmem
  · intro f hf
    refine memB_iff.2 ?_
    have hmem : f ∈ n.state := hgs (by simpa using hf)
    rw [← hst] at hmem
    exact hmem

/-- **The search space of descriptions is sound and complete.** -/
theorem solvable_iff_exists_pReach {d : DomDesc} {q : InstDesc} :
    Solvable d q ↔ ∃ c, PReach d (initConfig q) c ∧ isGoalB q c = true :=
  ⟨exists_pReach_of_solvable, fun ⟨_, hr, hg⟩ => solvable_of_pReach hr hg⟩

end Syn

end HTN
