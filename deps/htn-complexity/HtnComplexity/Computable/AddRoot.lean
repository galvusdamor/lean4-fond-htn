import HtnPlanning.Computable.Classes
import HtnPlanning.Core.MethodRestrict
import HtnPlanning.Interleave.NetYield
/-!
# Rooting the *target* of a compilation

The draft paper defines an HTN planning problem as a triple `(s_I, g_I, t_I)` whose last
component is a **single compound task**.  A compilation between classes of the table is
therefore expected to produce a problem of that shape as well, and the source problem it starts
from has that shape too (`HTN.Syn.InstDesc.IsRooted`).

The compilations of this development mostly produce rooted instances already — a `STRIPS`
instance description carries the single compound task `0` by definition.  The one exception is
the compilation of totally ordered problems into acyclic ones, whose compiled instance carries
a *fixed* three-task chain.  This file supplies the generic step that roots such a compiled
instance:

* `HTN.Syn.addRootDom r b d` — the domain description `d` with one further method decomposing
  the fresh compound name `r` into the described network `b`;
* `HTN.Syn.addRootInst r q` — the instance description `q` with the single compound task `r`
  as its initial task network;
* `HTN.Syn.solvable_addRoot_iff` — for a name `r` that neither `d` nor `b` mentions, the rooted
  problem is solvable exactly when the original one is.

The translation is *modular*: the body `b` is a parameter, and in the application it is a
constant (the initial task network the compilation produces for every instance), so the domain
translation still does not read the instance.  Contrast
`HtnComplexity/Computable/Rooting.lean`, where the body is the initial task network of the
instance and the construction is therefore available only to a decision procedure.

Unlike `HTN.Syn.solvable_root_iff`, the theorem here does not assume that the domain is totally
ordered: it is proved from the decomposition calculus (`HTN.Domain.netYieldN_single_comp`) and
from the fact that only the reachable methods matter
(`HTN.Problem.solvable_withMethods_iff`), both of which hold for partially ordered hierarchies.
-/

namespace HTN

namespace Syn

/-! ### The construction -/

/-- The described task network consisting of the single compound task `r`. -/
def singleTn (r : ℕ) : TnDesc := ([0], [], [(0, true, r)])

/-- The domain description `d`, extended by a method that decomposes `r` into `b`. -/
def addRootDom (r : ℕ) (b : TnDesc) (d : DomDesc) : DomDesc :=
  (d.actions, d.methods ++ [(r, b)])

/-- The instance description `q`, with the single compound task `r` as initial task network. -/
def addRootInst (r : ℕ) (q : InstDesc) : InstDesc := (q.initList, q.goalList, singleTn r)

variable {d : DomDesc} {q : InstDesc} {r : ℕ} {b : TnDesc}

@[simp] lemma addRootDom_actions : (addRootDom r b d).actions = d.actions := rfl

@[simp] lemma addRootDom_methods :
    (addRootDom r b d).methods = d.methods ++ [(r, b)] := rfl

@[simp] lemma addRootDom_prec : (addRootDom r b d).prec = d.prec := rfl

@[simp] lemma addRootDom_add : (addRootDom r b d).add = d.add := rfl

@[simp] lemma addRootDom_del : (addRootDom r b d).del = d.del := rfl

@[simp] lemma addRootInst_initList : (addRootInst r q).initList = q.initList := rfl

@[simp] lemma addRootInst_goalList : (addRootInst r q).goalList = q.goalList := rfl

@[simp] lemma addRootInst_tnI : (addRootInst r q).tnI = singleTn r := rfl

lemma singleTn_toTaskNetwork_T : (singleTn r).toTaskNetwork.T = {0} := by
  simp [singleTn, TnDesc.toTaskNetwork, TnDesc.ids]

lemma singleTn_toTaskNetwork_α : (singleTn r).toTaskNetwork.α 0 = Sum.inr r := by
  simp [singleTn, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl]

/-- The single-task network is a one-task network in the sense of `TaskNetwork.IsSingle`. -/
theorem isSingle_singleTn : TaskNetwork.IsSingle (singleTn r).toTaskNetwork 0 where
  memT := fun x => by
    rw [singleTn_toTaskNetwork_T]
    simp
  ord := fun a c hac => by
    have h := hac.2.2.1
    induction h with
    | single hab => simp [TnDesc.listRel, singleTn, TnDesc.ordList] at hab
    | tail _ hbc _ => simp [TnDesc.listRel, singleTn, TnDesc.ordList] at hbc

/-! ### The added method is the only one for `r` -/

/-- The methods of the extended description: those of `d`, and the new one. -/
theorem mem_addRootDom_methods_iff {e : MethodDesc} :
    e ∈ (addRootDom r b d).methods ↔ e ∈ d.methods ∨ e = (r, b) := by
  rw [addRootDom_methods, List.mem_append]
  simp

/-- If `r` heads no method of `d`, then a method of the extension decomposing `r` is the new
one. -/
theorem eq_of_mem_addRootDom_head (hhead : ∀ e ∈ d.methods, e.1 ≠ r) {e : MethodDesc}
    (he : e ∈ (addRootDom r b d).methods) (h1 : e.1 = r) : e = (r, b) := by
  rcases mem_addRootDom_methods_iff.1 he with h | h
  · exact absurd h1 (hhead e h)
  · exact h

/-! ### The extra method is unreachable from a network without `r` -/

/-- A compound name reachable in the extended problem from an instance whose initial task
network does not mention `r`, and whose domain mentions `r` in no body, is never `r`. -/
theorem ne_of_reachableName (hhead : ∀ e ∈ d.methods, e.1 ≠ r)
    (hbodies : ∀ e ∈ d.methods, r ∉ e.2.compoundNames) (htn : r ∉ q.tnI.compoundNames)
    {c : ℕ} (hc : (problem (addRootDom r b d) q).ReachableName c) : c ≠ r := by
  induction hc with
  | @tnI t c ht hlab =>
    have ht' : t ∈ q.tnI.ids := by
      have h : t ∈ q.tnI.toTaskNetwork.T := ht
      rwa [TnDesc.toTaskNetwork_T, List.mem_toFinset] at h
    have hlab' : q.tnI.label t = Sum.inr c := by
      have h : q.tnI.toTaskNetwork.α t = Sum.inr c := hlab
      rwa [TnDesc.toTaskNetwork_α] at h
    rintro rfl
    exact htn (TnDesc.mem_compoundNames.2 ⟨t, ht', hlab'⟩)
  | @method m t c hm _ ht hlab ih =>
    obtain ⟨e, he, rfl⟩ := hm
    have hne : e.1 ≠ r := by simpa using ih
    have hed : e ∈ d.methods := by
      rcases mem_addRootDom_methods_iff.1 he with h | h
      · exact h
      · exact absurd (by rw [h]) hne
    have ht' : t ∈ e.2.ids := by
      have h : t ∈ e.2.toTaskNetwork.T := ht
      rwa [TnDesc.toTaskNetwork_T, List.mem_toFinset] at h
    have hlab' : e.2.label t = Sum.inr c := by
      have h : e.2.toTaskNetwork.α t = Sum.inr c := hlab
      rwa [TnDesc.toTaskNetwork_α] at h
    rintro rfl
    exact hbodies e hed (TnDesc.mem_compoundNames.2 ⟨t, ht', hlab'⟩)

/-- **The extra method may be dropped**: with an initial task network that does not mention `r`,
the extended description is solvable exactly when `d` is. -/
theorem solvable_addRootDom_iff (hhead : ∀ e ∈ d.methods, e.1 ≠ r)
    (hbodies : ∀ e ∈ d.methods, r ∉ e.2.compoundNames) (htn : r ∉ q.tnI.compoundNames) :
    Solvable (addRootDom r b d) q ↔ Solvable d q := by
  have hsub : {m : Method ℕ ℕ ℕ | ∃ e ∈ d.methods, e.toMethod = m} ⊆
      (problem (addRootDom r b d) q).methods := by
    rintro m ⟨e, he, rfl⟩
    exact ⟨e, mem_addRootDom_methods_iff.2 (Or.inl he), rfl⟩
  have hreach : ∀ m, (problem (addRootDom r b d) q).ReachableMethod m →
      m ∈ {m : Method ℕ ℕ ℕ | ∃ e ∈ d.methods, e.toMethod = m} := by
    rintro m ⟨⟨e, he, rfl⟩, hrn⟩
    have hne : e.1 ≠ r := by simpa using ne_of_reachableName hhead hbodies htn hrn
    rcases mem_addRootDom_methods_iff.1 he with h | h
    · exact ⟨e, h, rfl⟩
    · exact absurd (by rw [h]) hne
  have h := Problem.solvable_withMethods_iff (P := problem (addRootDom r b d) q) hsub hreach
  have hp : (problem (addRootDom r b d) q).withMethods
      {m : Method ℕ ℕ ℕ | ∃ e ∈ d.methods, e.toMethod = m} = problem d q := rfl
  show (problem (addRootDom r b d) q).Solvable ↔ (problem d q).Solvable
  rw [← hp]
  exact h.symm

/-! ### Solvability of the rooted instance -/

/-- Every method of a described domain has a well-formed subtask network. -/
private lemma methods_wf' (d : DomDesc) : ∀ m ∈ d.toDomain.methods, m.subtasks.WF := by
  rintro m ⟨e, -, rfl⟩
  exact e.2.toTaskNetwork_wf

/-- **Refinements of the single fresh task are the refinements of its body.** -/
theorem netYield_singleTn_iff (hhead : ∀ e ∈ d.methods, e.1 ≠ r) {as : List ℕ} :
    (addRootDom r b d).toDomain.NetYield (singleTn r).toTaskNetwork as ↔
      (addRootDom r b d).toDomain.NetYield b.toTaskNetwork as := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨k, m, -, hm, hmt, hk⟩ :=
      (Domain.netYieldN_single_comp (D := (addRootDom r b d).toDomain) isSingle_singleTn
        singleTn_toTaskNetwork_α (methods_wf' _)).1 hn
    obtain ⟨e, he, rfl⟩ := hm
    have : e = (r, b) := eq_of_mem_addRootDom_head hhead he (by simpa using hmt)
    subst this
    exact ⟨k, hk⟩
  · rintro ⟨n, hn⟩
    have hmem : ((r, b) : MethodDesc) ∈ (addRootDom r b d).methods :=
      mem_addRootDom_methods_iff.2 (Or.inr rfl)
    refine ⟨n + 1, (Domain.netYieldN_single_comp (D := (addRootDom r b d).toDomain)
      isSingle_singleTn singleTn_toTaskNetwork_α (methods_wf' _)).2
      ⟨n, MethodDesc.toMethod (r, b), rfl, ⟨(r, b), hmem, rfl⟩, rfl, hn⟩⟩

/-- **Rooting the instance**: replacing the initial task network `b` by a single fresh compound
task `r` decomposed by one new method into `b` preserves and reflects solvability. -/
theorem solvable_addRootInst_iff (hhead : ∀ e ∈ d.methods, e.1 ≠ r) :
    Solvable (addRootDom r b d) (addRootInst r q) ↔
      Solvable (addRootDom r b d) (q.initList, q.goalList, b) := by
  rw [Solvable, Solvable, Problem.solvable_iff_netYield, Problem.solvable_iff_netYield]
  exact exists_congr fun as => and_congr_left' (netYield_singleTn_iff hhead)

/-- **The rooting theorem**: for a compound name `r` that the domain description mentions
nowhere and that does not occur in the body `b`, the rooted problem is solvable exactly when
the problem whose initial task network is `b` is. -/
theorem solvable_addRoot_iff (hhead : ∀ e ∈ d.methods, e.1 ≠ r)
    (hbodies : ∀ e ∈ d.methods, r ∉ e.2.compoundNames) (hb : r ∉ b.compoundNames) :
    Solvable (addRootDom r b d) (addRootInst r q) ↔
      Solvable d (q.initList, q.goalList, b) := by
  rw [solvable_addRootInst_iff hhead]
  exact solvable_addRootDom_iff hhead hbodies (q := (q.initList, q.goalList, b)) hb

end Syn

end HTN
