import HtnPlanning.Computable.Classes
/-!
# Only the facts a domain mentions matter

An action model changes, and tests, only the facts that occur in the descriptions of its
actions.  For a described domain `d` those are the facts of `HTN.Syn.DomDesc.domFacts d` — the
precondition, add and delete lists of the listed actions — and a fact outside that list is
**inert**: no plan can create or destroy it, and no plan can be blocked by it.

The consequences for a described problem are collected here.

* `HTN.ActionModel.MentionsOnly δ R` — the action model touches and tests only the facts of `R`;
  `HTN.Syn.mentionsOnly_domFacts` says a described domain mentions only `domFacts d`.
* `HTN.ActionModel.seqApplicable_congr`, `HTN.ActionModel.transitionSeq_congr`,
  `HTN.ActionModel.transitionSeq_sdiff` — two states that agree on `R` are indistinguishable,
  and outside `R` a plan changes nothing.
* `HTN.Syn.solvable_congr_state` — two instance descriptions with the same initial task network
  are equally solvable as soon as they impose the same condition on action sequences.
* `HTN.Syn.solvable_iff_restrict` — **the relevance theorem**: a described problem is solvable
  exactly when its goal facts outside `domFacts d` already hold initially and the problem with
  the initial state and goal cut down to `domFacts d` is solvable.  In particular the
  solvability of `(d, q)` depends on `q` only through its initial task network, the two
  intersections `initList q ∩ domFacts d`, `goalList q ∩ domFacts d`, and the single bit
  `goalList q \ domFacts d ⊆ initList q`: a fixed domain description reads only boundedly much
  of the state it is given.
-/

namespace HTN

namespace ActionModel

variable {F A : Type*} {δ : ActionModel F A} {R : Set F}

/-- **The action model mentions only the facts of `R`**: every precondition, add and delete list
is contained in `R`. -/
structure MentionsOnly (δ : ActionModel F A) (R : Set F) : Prop where
  /-- Preconditions are facts of `R`. -/
  prec : ∀ a, δ.prec a ⊆ R
  /-- Added facts are facts of `R`. -/
  add : ∀ a, δ.add a ⊆ R
  /-- Deleted facts are facts of `R`. -/
  del : ∀ a, δ.del a ⊆ R

/-- Outside `R` a single action changes nothing. -/
theorem transition_sdiff (h : MentionsOnly δ R) (a : A) (S : Set F) :
    δ.transition a S \ R = S \ R := by
  ext f
  simp only [transition, Set.mem_diff, Set.mem_union]
  constructor
  · rintro ⟨hf | hf, hR⟩
    · exact ⟨hf.1, hR⟩
    · exact absurd (h.add a hf) hR
  · rintro ⟨hf, hR⟩
    exact ⟨Or.inl ⟨hf, fun hd => hR (h.del a hd)⟩, hR⟩

/-- Outside `R` a plan changes nothing. -/
theorem transitionSeq_sdiff (h : MentionsOnly δ R) (as : List A) (S : Set F) :
    δ.transitionSeq as S \ R = S \ R := by
  induction as generalizing S with
  | nil => simp
  | cons a as ih => rw [transitionSeq_cons, ih, transition_sdiff h]

/-- On `R`, a single action acts the same on two states that agree on `R` — whatever the action
model does elsewhere. -/
theorem transition_inter (δ : ActionModel F A) (R : Set F) (a : A) {S S' : Set F}
    (hS : S ∩ R = S' ∩ R) :
    δ.transition a S ∩ R = δ.transition a S' ∩ R := by
  ext f
  simp only [transition, Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
  constructor <;> rintro ⟨hf | hf, hR⟩
  · refine ⟨Or.inl ⟨?_, hf.2⟩, hR⟩
    have : f ∈ S ∩ R := ⟨hf.1, hR⟩
    exact (hS ▸ this).1
  · exact ⟨Or.inr hf, hR⟩
  · refine ⟨Or.inl ⟨?_, hf.2⟩, hR⟩
    have : f ∈ S' ∩ R := ⟨hf.1, hR⟩
    exact (hS.symm ▸ this).1
  · exact ⟨Or.inr hf, hR⟩

/-- Two states that agree on `R` cannot be distinguished by a plan. -/
theorem transitionSeq_congr (δ : ActionModel F A) (R : Set F) (as : List A) {S S' : Set F}
    (hS : S ∩ R = S' ∩ R) : δ.transitionSeq as S ∩ R = δ.transitionSeq as S' ∩ R := by
  induction as generalizing S S' with
  | nil => simpa using hS
  | cons a as ih => exact ih (transition_inter δ R a hS)

/-- Applicability is decided on `R`. -/
theorem applicable_congr (h : MentionsOnly δ R) (a : A) {S S' : Set F} (hS : S ∩ R = S' ∩ R) :
    δ.Applicable a S ↔ δ.Applicable a S' := by
  constructor <;> intro happ f hf
  · have : f ∈ S ∩ R := ⟨happ hf, h.prec a hf⟩
    exact (hS ▸ this).1
  · have : f ∈ S' ∩ R := ⟨happ hf, h.prec a hf⟩
    exact (hS.symm ▸ this).1

/-- Executability is decided on `R`. -/
theorem seqApplicable_congr (h : MentionsOnly δ R) (as : List A) {S S' : Set F}
    (hS : S ∩ R = S' ∩ R) : δ.SeqApplicable as S ↔ δ.SeqApplicable as S' := by
  induction as generalizing S S' with
  | nil => simp
  | cons a as ih =>
    rw [seqApplicable_cons, seqApplicable_cons, applicable_congr h a hS,
      ih (transition_inter δ R a hS)]

end ActionModel

namespace Syn

/-! ### The facts a domain description mentions -/

/-- **Every fact a domain description mentions**: the preconditions, add and delete lists of its
listed actions. -/
def DomDesc.domFacts (d : DomDesc) : List ℕ :=
  d.actions.flatMap fun ad => ad.2.1 ++ ad.2.2.1 ++ ad.2.2.2

variable {d : DomDesc} {q : InstDesc}

theorem mem_domFacts_of_lookup {a : ℕ} {x : List ℕ × List ℕ × List ℕ} {f : ℕ}
    (h : d.actions.lookup a = some x) (hf : f ∈ x.1 ++ x.2.1 ++ x.2.2) : f ∈ d.domFacts :=
  List.mem_flatMap.2 ⟨(a, x), mem_of_lookup_eq_some h, hf⟩

/-- **A described domain mentions only the facts of `domFacts`.** -/
theorem mentionsOnly_domFacts (d : DomDesc) :
    ActionModel.MentionsOnly d.toDomain.toActionModel {f | f ∈ d.domFacts} := by
  refine ⟨fun a f hf => ?_, fun a f hf => ?_, fun a f hf => ?_⟩
  · rcases hx : d.actions.lookup a with - | x
    · rw [show d.toDomain.toActionModel.prec a = d.prec a from rfl, DomDesc.prec, hx] at hf
      simp at hf
    · rw [show d.toDomain.toActionModel.prec a = d.prec a from rfl, DomDesc.prec, hx] at hf
      exact mem_domFacts_of_lookup hx (by simp at hf ⊢; tauto)
  · rcases hx : d.actions.lookup a with - | x
    · rw [show d.toDomain.toActionModel.add a = d.add a from rfl, DomDesc.add, hx] at hf
      simp at hf
    · rw [show d.toDomain.toActionModel.add a = d.add a from rfl, DomDesc.add, hx] at hf
      exact mem_domFacts_of_lookup hx (by simp at hf ⊢; tauto)
  · rcases hx : d.actions.lookup a with - | x
    · rw [show d.toDomain.toActionModel.del a = d.del a from rfl, DomDesc.del, hx] at hf
      simp at hf
    · rw [show d.toDomain.toActionModel.del a = d.del a from rfl, DomDesc.del, hx] at hf
      exact mem_domFacts_of_lookup hx (by simp at hf ⊢; tauto)

/-! ### Solvability depends on the state only through the plan conditions -/

/-- Reachability only depends on the domain and on the initial task network. -/
theorem reachable_congr {q q' : InstDesc} (htn : q.tnI = q'.tnI) {tn : TaskNetwork ℕ ℕ ℕ} :
    (problem d q).Reachable tn ↔ (problem d q').Reachable tn := by
  show HTN.DecomposesTo (problem d q).methods (problem d q).tnI tn ↔
    HTN.DecomposesTo (problem d q').methods (problem d q').tnI tn
  rw [problem_methods, problem_methods, problem_tnI, problem_tnI, htn]

/-- **Two instance descriptions with the same initial task network are equally solvable** as soon
as they impose the same condition on action sequences. -/
theorem solvable_congr_state (d : DomDesc) (q q' : InstDesc) (htn : q.tnI = q'.tnI)
    (h : ∀ as : List ℕ,
      (d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
          {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList}) ↔
        (d.toDomain.SeqApplicable as {f | f ∈ q'.initList} ∧
          {f | f ∈ q'.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q'.initList})) :
    Solvable d q ↔ Solvable d q' := by
  simp only [Solvable, Problem.solvable_iff_exists_solutionPlan, Problem.IsSolutionPlan]
  constructor
  · rintro ⟨as, tn, l, hreach, hprim, hlin, hseq, happ, hgoal⟩
    exact ⟨as, tn, l, (reachable_congr htn).1 hreach, hprim, hlin, hseq,
      ((h as).1 ⟨happ, hgoal⟩).1, ((h as).1 ⟨happ, hgoal⟩).2⟩
  · rintro ⟨as, tn, l, hreach, hprim, hlin, hseq, happ, hgoal⟩
    exact ⟨as, tn, l, (reachable_congr htn).2 hreach, hprim, hlin, hseq,
      ((h as).2 ⟨happ, hgoal⟩).1, ((h as).2 ⟨happ, hgoal⟩).2⟩

/-! ### The relevance theorem -/

/-- The instance description with its initial state and goal cut down to the facts of `R`. -/
def InstDesc.restrict (R : List ℕ) (q : InstDesc) : InstDesc :=
  (q.initList.filter (fun f => memB R f), q.goalList.filter (fun f => memB R f), q.tnI)

@[simp] theorem restrict_tnI (R : List ℕ) (q : InstDesc) : (q.restrict R).tnI = q.tnI := rfl

@[simp] theorem mem_restrict_initList {R : List ℕ} {f : ℕ} :
    f ∈ (q.restrict R).initList ↔ f ∈ q.initList ∧ f ∈ R := by
  simp [InstDesc.restrict, InstDesc.initList]

@[simp] theorem mem_restrict_goalList {R : List ℕ} {f : ℕ} :
    f ∈ (q.restrict R).goalList ↔ f ∈ q.goalList ∧ f ∈ R := by
  simp [InstDesc.restrict, InstDesc.goalList]

/-- **The relevance theorem.**  A described problem is solvable exactly when the goal facts the
domain never mentions already hold in the initial state, and the problem whose initial state and
goal are cut down to the facts the domain mentions is solvable. -/
theorem solvable_iff_restrict (d : DomDesc) (q : InstDesc) :
    Solvable d q ↔
      ((∀ f ∈ q.goalList, f ∉ d.domFacts → f ∈ q.initList) ∧
        Solvable d (q.restrict d.domFacts)) := by
  classical
  set R : Set ℕ := {f | f ∈ d.domFacts} with hR
  have hM := mentionsOnly_domFacts d
  have hinter : {f | f ∈ (q.restrict d.domFacts).initList} ∩ R = {f | f ∈ q.initList} ∩ R := by
    ext f
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_restrict_initList, hR]
    tauto
  -- the two problems impose the same condition on action sequences
  have key : (∀ f ∈ q.goalList, f ∉ d.domFacts → f ∈ q.initList) → ∀ as : List ℕ,
      (d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
          {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList}) ↔
        (d.toDomain.SeqApplicable as {f | f ∈ (q.restrict d.domFacts).initList} ∧
          {f | f ∈ (q.restrict d.domFacts).goalList} ⊆
            d.toDomain.transitionSeq as {f | f ∈ (q.restrict d.domFacts).initList}) := by
    intro hout as
    have happ := ActionModel.seqApplicable_congr hM as hinter.symm
    have hseq := ActionModel.transitionSeq_congr d.toDomain.toActionModel R as hinter.symm
    have hsd := ActionModel.transitionSeq_sdiff hM as {f | f ∈ q.initList}
    constructor
    · rintro ⟨ha, hg⟩
      refine ⟨happ.1 ha, fun f hf => ?_⟩
      simp only [Set.mem_setOf_eq, mem_restrict_goalList] at hf
      have hfR : f ∈ R := hf.2
      have : f ∈ d.toDomain.transitionSeq as {f | f ∈ q.initList} ∩ R := ⟨hg hf.1, hfR⟩
      exact (hseq ▸ this).1
    · rintro ⟨ha, hg⟩
      refine ⟨happ.2 ha, fun f hf => ?_⟩
      by_cases hfR : f ∈ d.domFacts
      · have hmem : f ∈ {f | f ∈ (q.restrict d.domFacts).goalList} := by
          simp only [Set.mem_setOf_eq, mem_restrict_goalList]
          exact ⟨hf, hfR⟩
        have : f ∈ d.toDomain.transitionSeq as
            {f | f ∈ (q.restrict d.domFacts).initList} ∩ R := ⟨hg hmem, hfR⟩
        exact (hseq.symm ▸ this).1
      · have hinit : f ∈ {f | f ∈ q.initList} := hout f hf hfR
        have : f ∈ {f | f ∈ q.initList} \ R := ⟨hinit, hfR⟩
        exact ((hsd.symm ▸ this) : f ∈ d.toDomain.transitionSeq as {f | f ∈ q.initList} \ R).1
  constructor
  · intro hsolv
    have hout : ∀ f ∈ q.goalList, f ∉ d.domFacts → f ∈ q.initList := by
      obtain ⟨as, tn, l, -, -, -, -, -, hgoal⟩ :=
        Problem.solvable_iff_exists_solutionPlan.1 hsolv
      intro f hf hfR
      have hmem : f ∈ d.toDomain.transitionSeq as {f | f ∈ q.initList} := hgoal hf
      have hsd := ActionModel.transitionSeq_sdiff hM as {f | f ∈ q.initList}
      have : f ∈ d.toDomain.transitionSeq as {f | f ∈ q.initList} \ R := ⟨hmem, hfR⟩
      exact ((hsd ▸ this) : f ∈ {f | f ∈ q.initList} \ R).1
    exact ⟨hout, (solvable_congr_state d q (q.restrict d.domFacts) rfl (key hout)).1 hsolv⟩
  · rintro ⟨hout, hs⟩
    exact (solvable_congr_state d q (q.restrict d.domFacts) rfl (key hout)).2 hs

/-- A goal fact the domain never mentions is inert: it can only be reached by holding
initially. -/
theorem mem_initList_of_solvable (h : Solvable d q) {f : ℕ} (hf : f ∈ q.goalList)
    (hR : f ∉ d.domFacts) : f ∈ q.initList :=
  ((solvable_iff_restrict d q).1 h).1 f hf hR

/-- Instance descriptions with the same initial task network and the same initial state and goal
*as sets* are equally solvable. -/
theorem solvable_congr_sets (d : DomDesc) (q q' : InstDesc) (htn : q.tnI = q'.tnI)
    (hi : {f | f ∈ q.initList} = {f | f ∈ q'.initList})
    (hg : {f | f ∈ q.goalList} = {f | f ∈ q'.goalList}) : Solvable d q ↔ Solvable d q' :=
  solvable_congr_state d q q' htn fun as => by rw [hi, hg]

/-- **A fixed domain description reads only boundedly much of its instance.**  Two instance
descriptions with the same initial task network, the same initial state and goal *on the facts
the domain mentions*, and the same answer to the single question whether the remaining goal
facts already hold initially, are equally solvable. -/
theorem solvable_congr_domFacts (d : DomDesc) (q q' : InstDesc) (htn : q.tnI = q'.tnI)
    (hinit : ∀ f ∈ d.domFacts, (f ∈ q.initList ↔ f ∈ q'.initList))
    (hgoal : ∀ f ∈ d.domFacts, (f ∈ q.goalList ↔ f ∈ q'.goalList))
    (hout : (∀ f ∈ q.goalList, f ∉ d.domFacts → f ∈ q.initList) ↔
      (∀ f ∈ q'.goalList, f ∉ d.domFacts → f ∈ q'.initList)) :
    Solvable d q ↔ Solvable d q' := by
  rw [solvable_iff_restrict d q, solvable_iff_restrict d q']
  have hrestrict : Solvable d (q.restrict d.domFacts) ↔ Solvable d (q'.restrict d.domFacts) := by
    refine solvable_congr_sets d _ _ (by simp [htn]) ?_ ?_ <;> ext f
    · simp only [Set.mem_setOf_eq, mem_restrict_initList]
      exact and_congr_left fun hf => hinit f hf
    · simp only [Set.mem_setOf_eq, mem_restrict_goalList]
      exact and_congr_left fun hf => hgoal f hf
  rw [hrestrict, hout]

end Syn

end HTN
