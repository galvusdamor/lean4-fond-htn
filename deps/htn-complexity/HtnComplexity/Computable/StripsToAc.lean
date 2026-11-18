import HtnPlanning.Interleave.PlanLengthLocal
import HtnComplexity.Computable.AcTarget
import HtnComplexity.Computable.StripsSource
/-!
# The cell (`STRIPS`, `TO-HTN-AC`)

A described STRIPS problem is solvable exactly when a plan over the actions its hierarchy
offers reaches the goal (`HTN.Syn.solvable_isStrips_iff`), and such a plan can always be taken
of length less than `2 ^ K`, where `K` bounds the number of facts the offered actions can
change (`HTN.ClassicalProblem.exists_short_solution`).  The doubling hierarchy of
`HtnComplexity/Computable/AcTarget.lean` produces exactly the sequences of at most `2 ^ K`
offered actions, so it is a compilation:

* `HTN.Syn.stripsToAcDom d` — the doubling hierarchy of depth `K = |mutFacts d|` over the
  actions `d` offers, keeping the descriptions of those actions.  A domain description with no
  empty method body is unsolvable whatever the instance, and is sent to the *dead* domain
  description, which has no method at all;
* `HTN.Syn.stripsToAcInst q` — the same initial state and goal, with the initial task network
  of a STRIPS instance;
* `HTN.Syn.compSyn_STRIPS_to_TO_HTN_AC` — the cell.
-/

namespace HTN

namespace Syn

/-! ### The compiled descriptions -/

/-- The decision whether a domain description has a method with an empty body. -/
def hasEmptyMethodB (d : DomDesc) : Bool :=
  d.methods.foldr (fun e r => if e.2.ids = [] then true else r) false

theorem hasEmptyMethodB_iff {d : DomDesc} : hasEmptyMethodB d = true ↔ d.HasEmptyMethod := by
  simp only [hasEmptyMethodB, DomDesc.HasEmptyMethod]
  induction d.methods with
  | nil => simp
  | cons e es ih =>
    by_cases h : e.2.ids = []
    · simp [h]
    · rw [show (List.foldr (fun e r => if e.2.ids = [] then true else r) false (e :: es)) =
        List.foldr (fun e r => if e.2.ids = [] then true else r) false es by simp [h], ih]
      constructor
      · rintro ⟨f, hf, hfnil⟩
        exact ⟨f, List.mem_cons_of_mem _ hf, hfnil⟩
      · rintro ⟨f, hf, hfnil⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact absurd hfnil h
        · exact ⟨f, hf, hfnil⟩

/-- The descriptions of the actions the hierarchy of `d` offers. -/
def usableActions (d : DomDesc) : List ActionDesc :=
  d.actions.flatMap fun ad => bif memB d.stepActs ad.1 then [ad] else []

/-- The facts an offered action of `d` can change. -/
def mutFacts (d : DomDesc) : List ℕ :=
  (usableActions d).flatMap fun ad => ad.2.2.1 ++ ad.2.2.2

/-- The domain description with no method at all: no instance over it is solvable. -/
def deadDom : DomDesc := ([], [])

/-- **The compiled domain description**. -/
def stripsToAcDom (d : DomDesc) : DomDesc :=
  bif hasEmptyMethodB d then acDom (usableActions d) (mutFacts d).length d.stepActs else deadDom

/-- **The compiled instance description**. -/
def stripsToAcInst (q : InstDesc) : InstDesc := stripsInst q.initList q.goalList

/-! ### The offered actions are described unchanged -/

section Actions

variable {d : DomDesc}

theorem mem_usableActions {ad : ActionDesc} :
    ad ∈ usableActions d ↔ ad ∈ d.actions ∧ ad.1 ∈ d.stepActs := by
  simp only [usableActions, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hmem⟩
    rcases hb : memB d.stepActs x.1 with _ | _
    · rw [hb] at hmem; simp at hmem
    · rw [hb] at hmem
      simp only [cond_true, List.mem_singleton] at hmem
      subst hmem
      exact ⟨hx, memB_iff.1 hb⟩
  · rintro ⟨had, hstep⟩
    exact ⟨ad, had, by rw [show memB d.stepActs ad.1 = true from memB_iff.2 hstep]; simp⟩

/-- Looking up an offered action gives the description it has in `d`. -/
theorem lookup_usableActions {a : ℕ} (ha : a ∈ d.stepActs) :
    (usableActions d).lookup a = d.actions.lookup a := by
  simp only [usableActions]
  induction d.actions with
  | nil => rfl
  | cons ad ads ih =>
    obtain ⟨n, x⟩ := ad
    rw [List.flatMap_cons]
    by_cases h : n = a
    · subst h
      have hb : memB d.stepActs n = true := memB_iff.2 ha
      simp [hb]
    · have hne : (a == n) = false := by simp [Ne.symm h]
      rcases hb : memB d.stepActs n with _ | _
      · simp only [cond_false, List.nil_append, List.lookup_cons, hne]
        exact ih
      · simp only [cond_true, List.singleton_append, List.lookup_cons, hne]
        exact ih

variable (K : ℕ) (Acts : List ℕ)

theorem acDom_prec_eq {a : ℕ} (ha : a ∈ d.stepActs) :
    (acDom (usableActions d) K Acts).prec a = d.prec a := by
  show {f | f ∈ (((usableActions d).lookup a).elim [] fun x => x.1)} = _
  rw [lookup_usableActions ha]
  rfl

theorem acDom_add_eq {a : ℕ} (ha : a ∈ d.stepActs) :
    (acDom (usableActions d) K Acts).add a = d.add a := by
  show {f | f ∈ (((usableActions d).lookup a).elim [] fun x => x.2.1)} = _
  rw [lookup_usableActions ha]
  rfl

theorem acDom_del_eq {a : ℕ} (ha : a ∈ d.stepActs) :
    (acDom (usableActions d) K Acts).del a = d.del a := by
  show {f | f ∈ (((usableActions d).lookup a).elim [] fun x => x.2.2)} = _
  rw [lookup_usableActions ha]
  rfl

theorem acDom_transitionSeq_eq {as : List ℕ} (has : ∀ a ∈ as, a ∈ d.stepActs) (s : Set ℕ) :
    (acDom (usableActions d) K Acts).toDomain.transitionSeq as s =
      d.toDomain.transitionSeq as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    have hstep : (acDom (usableActions d) K Acts).toDomain.transition a s =
        d.toDomain.transition a s := by
      simp only [ActionModel.transition]
      rw [show (acDom (usableActions d) K Acts).toDomain.del a = d.del a from
          acDom_del_eq K Acts (has a (by simp)),
        show (acDom (usableActions d) K Acts).toDomain.add a = d.add a from
          acDom_add_eq K Acts (has a (by simp))]
      rfl
    rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_cons, hstep]
    exact ih (fun b hb => has b (by simp [hb])) _

theorem acDom_seqApplicable_iff {as : List ℕ} (has : ∀ a ∈ as, a ∈ d.stepActs) (s : Set ℕ) :
    (acDom (usableActions d) K Acts).toDomain.SeqApplicable as s ↔
      d.toDomain.SeqApplicable as s := by
  induction as generalizing s with
  | nil => exact Iff.rfl
  | cons a as ih =>
    have hstep : (acDom (usableActions d) K Acts).toDomain.transition a s =
        d.toDomain.transition a s := by
      simp only [ActionModel.transition]
      rw [show (acDom (usableActions d) K Acts).toDomain.del a = d.del a from
          acDom_del_eq K Acts (has a (by simp)),
        show (acDom (usableActions d) K Acts).toDomain.add a = d.add a from
          acDom_add_eq K Acts (has a (by simp))]
      rfl
    have hprec : (acDom (usableActions d) K Acts).toDomain.Applicable a s ↔
        d.toDomain.Applicable a s := by
      rw [ActionModel.Applicable, ActionModel.Applicable,
        show (acDom (usableActions d) K Acts).toDomain.prec a = d.toDomain.prec a from
          acDom_prec_eq K Acts (has a (by simp))]
    rw [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_cons, hstep, hprec]
    exact and_congr Iff.rfl (ih (fun b hb => has b (by simp [hb])) _)

/-- Every action the compiled domain mentions is an offered action. -/
theorem mem_stepActs_of_mem_actNames {a : ℕ}
    (ha : a ∈ (acDom (usableActions d) K Acts).actNames) : a ∈ d.stepActs := by
  obtain ⟨ad, had, rfl⟩ := List.mem_map.1 ha
  exact (mem_usableActions.1 had).2

/-! ### The offered actions change only the facts of `mutFacts` -/

theorem add_subset_mutFacts {a : ℕ} (ha : a ∈ d.stepActs) : d.add a ⊆ {f | f ∈ mutFacts d} := by
  intro f hf
  rcases h : d.actions.lookup a with _ | x
  · rw [show d.add a = {g | g ∈ ((d.actions.lookup a).elim [] fun y => y.2.1)} from rfl, h] at hf
    exact absurd hf (by simp)
  · rw [show d.add a = {g | g ∈ ((d.actions.lookup a).elim [] fun y => y.2.1)} from rfl, h] at hf
    have hmem : (a, x) ∈ usableActions d :=
      mem_usableActions.2 ⟨mem_of_lookup_eq_some h, ha⟩
    exact List.mem_flatMap.2 ⟨(a, x), hmem, List.mem_append_left _ hf⟩

theorem del_subset_mutFacts {a : ℕ} (ha : a ∈ d.stepActs) : d.del a ⊆ {f | f ∈ mutFacts d} := by
  intro f hf
  rcases h : d.actions.lookup a with _ | x
  · rw [show d.del a = {g | g ∈ ((d.actions.lookup a).elim [] fun y => y.2.2)} from rfl, h] at hf
    exact absurd hf (by simp)
  · rw [show d.del a = {g | g ∈ ((d.actions.lookup a).elim [] fun y => y.2.2)} from rfl, h] at hf
    have hmem : (a, x) ∈ usableActions d :=
      mem_usableActions.2 ⟨mem_of_lookup_eq_some h, ha⟩
    exact List.mem_flatMap.2 ⟨(a, x), hmem, List.mem_append_right _ hf⟩

end Actions

/-! ### The dead domain description -/

theorem deadDom_methodsTO : deadDom.MethodsTO := by
  intro e he
  exact absurd he (by simp [deadDom, DomDesc.methods])

theorem deadDom_isAcyclic : deadDom.IsAcyclic :=
  ⟨fun _ => 0, fun e he => absurd he (by simp [deadDom, DomDesc.methods])⟩

theorem not_solvable_deadDom (s g : List ℕ) : ¬ Solvable deadDom (stripsInst s g) := by
  rintro ⟨tn, hreach, hprim, -⟩
  obtain ⟨m, hm, -⟩ :=
    DecomposesTo.exists_method_nocompound (M := (problem deadDom (stripsInst s g)).methods)
      hreach ⟨0, by simp [initTn, TnDesc.ids], 0, rfl⟩ hprim
  obtain ⟨e, he, -⟩ := hm
  exact absurd he (by simp [deadDom, DomDesc.methods])

/-! ### Correctness -/

/-- **The doubling compilation is correct.** -/
theorem solvable_stripsToAc_iff {d : DomDesc} {q : InstDesc} (hd : d.IsStrips) (hq : q.IsStrips) :
    Solvable d q ↔ Solvable (stripsToAcDom d) (stripsToAcInst q) := by
  classical
  by_cases hempty : d.HasEmptyMethod
  · have hb : hasEmptyMethodB d = true := hasEmptyMethodB_iff.2 hempty
    rw [show stripsToAcDom d = acDom (usableActions d) (mutFacts d).length d.stepActs by
      rw [stripsToAcDom, hb]; rfl]
    set K := (mutFacts d).length with hK
    rw [solvable_isStrips_iff hd hq]
    constructor
    · rintro ⟨-, as, hus, happ, hgoal⟩
      -- a short plan over the offered actions
      have hmut : ∀ a ∈ {a : ℕ | a ∈ d.stepActs},
          (problem d q).toClassicalProblem.add a ⊆ ↑(mutFacts d).toFinset ∧
          (problem d q).toClassicalProblem.del a ⊆ ↑(mutFacts d).toFinset := by
        intro a ha
        constructor
        · intro f hf
          simpa using add_subset_mutFacts ha hf
        · intro f hf
          simpa using del_subset_mutFacts ha hf
      obtain ⟨bs, hbus, ⟨hbapp, hbgoal⟩, hblen⟩ :=
        ClassicalProblem.exists_short_solution (P := (problem d q).toClassicalProblem)
          (Acts := {a : ℕ | a ∈ d.stepActs}) (F₀ := (mutFacts d).toFinset) hmut hus ⟨happ, hgoal⟩
      have hcard : ((mutFacts d).toFinset).card ≤ K := List.toFinset_card_le _
      have hlen : bs.length ≤ 2 ^ K :=
        le_trans hblen.le (Nat.pow_le_pow_right (by omega) hcard)
      refine solvable_acDom_of_plan q.initList q.goalList hlen hbus ?_ ?_
      · rw [acDom_seqApplicable_iff K d.stepActs hbus]
        exact hbapp
      · rw [acDom_transitionSeq_eq K d.stepActs hbus]
        exact hbgoal
    · intro h
      refine ⟨hempty, ?_⟩
      obtain ⟨as, happ, hgoal⟩ := Problem.Solvable.classical h
      obtain ⟨bs, hbs, hb₁, hb₂⟩ :=
        exists_plan_mem_of_plan (acDom (usableActions d) K d.stepActs)
          {f | f ∈ q.initList} as happ
      have hbus : ∀ a ∈ bs, a ∈ d.stepActs :=
        fun a ha => mem_stepActs_of_mem_actNames K d.stepActs (hbs a ha)
      refine ⟨bs, hbus, ?_, ?_⟩
      · rw [← acDom_seqApplicable_iff K d.stepActs hbus]
        exact hb₁
      · rw [← acDom_transitionSeq_eq K d.stepActs hbus]
        rw [hb₂]
        exact hgoal
  · have hb : hasEmptyMethodB d = false := by
      rcases hc : hasEmptyMethodB d with _ | _
      · rfl
      · exact absurd (hasEmptyMethodB_iff.1 hc) hempty
    rw [show stripsToAcDom d = deadDom by rw [stripsToAcDom, hb]; rfl]
    constructor
    · intro h
      exact absurd (hasEmptyMethod_of_solvable hd hq h) hempty
    · intro h
      exact absurd h (not_solvable_deadDom q.initList q.goalList)


/-! ### The compiled description belongs to `TO-HTN-AC` -/

theorem stripsToAcDom_methodsTO (d : DomDesc) : (stripsToAcDom d).MethodsTO := by
  rcases hb : hasEmptyMethodB d with _ | _
  · rw [show stripsToAcDom d = deadDom by rw [stripsToAcDom, hb]; rfl]
    exact deadDom_methodsTO
  · rw [show stripsToAcDom d = acDom (usableActions d) (mutFacts d).length d.stepActs by
      rw [stripsToAcDom, hb]; rfl]
    exact acDom_methodsTO _ _ _

theorem stripsToAcDom_isAcyclic (d : DomDesc) : (stripsToAcDom d).IsAcyclic := by
  rcases hb : hasEmptyMethodB d with _ | _
  · rw [show stripsToAcDom d = deadDom by rw [stripsToAcDom, hb]; rfl]
    exact deadDom_isAcyclic
  · rw [show stripsToAcDom d = acDom (usableActions d) (mutFacts d).length d.stepActs by
      rw [stripsToAcDom, hb]; rfl]
    exact acDom_isAcyclic _ _ _

theorem stripsToAcInst_isTO (q : InstDesc) : (stripsToAcInst q).IsTO :=
  (stripsInst_isStrips q.initList q.goalList).isTO

/-! ### Size of the compiled description -/

/-- The offered actions are a sublist of the described actions, so they are no longer. -/
theorem sum_size_usableActions_le (d : DomDesc) :
    ((usableActions d).map ActionDesc.size).sum ≤ (d.actions.map ActionDesc.size).sum := by
  simp only [usableActions]
  induction d.actions with
  | nil => simp
  | cons ad ads ih =>
    rw [List.flatMap_cons]
    rcases hb : memB d.stepActs ad.1 with _ | _
    · simp only [cond_false, List.nil_append, List.map_cons, List.sum_cons]
      omega
    · simp only [cond_true, List.singleton_append, List.map_cons, List.sum_cons]
      omega

theorem length_flatMap_addDel_le (l : List ActionDesc) :
    (l.flatMap fun ad => ad.2.2.1 ++ ad.2.2.2).length ≤ (l.map ActionDesc.size).sum := by
  induction l with
  | nil => simp
  | cons ad ads ih =>
    have h₂ : ActionDesc.size ad = 1 + ad.2.1.length + ad.2.2.1.length + ad.2.2.2.length := rfl
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    omega

theorem length_mutFacts_le (d : DomDesc) :
    (mutFacts d).length ≤ (d.actions.map ActionDesc.size).sum :=
  le_trans (length_flatMap_addDel_le (usableActions d)) (sum_size_usableActions_le d)

theorem length_stepActs_le (d : DomDesc) :
    d.stepActs.length ≤ (d.methods.map MethodDesc.size).sum := by
  simp only [DomDesc.stepActs]
  induction d.methods with
  | nil => simp
  | cons e es ih =>
    have h₁ := TnDesc.length_actionNames_le e.2
    have h₂ : MethodDesc.size e = 1 + (e.2.ids.length + e.2.ordList.length + e.2.lbl.length) := rfl
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    omega

/-- A list of methods of constant size. -/
theorem sum_size_map_const {α : Type} (l : List α) (g : α → MethodDesc) (c : ℕ)
    (h : ∀ x, MethodDesc.size (g x) = c) :
    ((l.map g).map MethodDesc.size).sum = c * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, h]
    ring

theorem sum_size_acMethods (K : ℕ) (Acts : List ℕ) :
    ((acMethods K Acts).map MethodDesc.size).sum = 6 * K + 1 + 3 * Acts.length := by
  have h₁ : (((List.range K).map fun i => ((i, splitBody (i + 1)) : MethodDesc)).map
      MethodDesc.size).sum = 6 * K := by
    rw [sum_size_map_const _ _ 6 (fun _ => rfl), List.length_range]
  have h₂ : (((Acts.map fun a => ((K, leafBody a) : MethodDesc))).map MethodDesc.size).sum =
      3 * Acts.length := sum_size_map_const _ _ 3 (fun _ => rfl)
  simp only [acMethods, List.map_append, List.sum_append, List.map_cons, List.sum_cons, h₁, h₂,
    show MethodDesc.size (K, emptyBody) = 1 from rfl]
  omega

theorem size_stripsToAcDom_le (d : DomDesc) : (stripsToAcDom d).size ≤ 7 * d.size + 1 := by
  rcases hb : hasEmptyMethodB d with _ | _
  · rw [show stripsToAcDom d = deadDom by rw [stripsToAcDom, hb]; rfl]
    simp [deadDom, DomDesc.size, DomDesc.actions, DomDesc.methods]
  · rw [show stripsToAcDom d = acDom (usableActions d) (mutFacts d).length d.stepActs by
      rw [stripsToAcDom, hb]; rfl]
    have h₁ := sum_size_usableActions_le d
    have h₂ := length_mutFacts_le d
    have h₃ := length_stepActs_le d
    have h₄ := sum_size_acMethods (mutFacts d).length d.stepActs
    have hsize : (acDom (usableActions d) (mutFacts d).length d.stepActs).size =
        ((usableActions d).map ActionDesc.size).sum +
          ((acMethods (mutFacts d).length d.stepActs).map MethodDesc.size).sum := rfl
    have hd : d.size = (d.actions.map ActionDesc.size).sum +
        (d.methods.map MethodDesc.size).sum := rfl
    omega

theorem size_stripsToAcInst_le (q : InstDesc) : (stripsToAcInst q).size ≤ q.size + 2 := by
  have h : InstDesc.size (stripsToAcInst q) = q.initList.length + q.goalList.length + 2 := rfl
  have hq : q.size = q.initList.length + q.goalList.length + q.tnI.size := rfl
  omega

/-! ### The translations are computable -/

open Primrec

theorem primrec_hasEmptyMethodB : Primrec hasEmptyMethodB := by
  have hh : Primrec₂ (fun (_ : DomDesc) (z : MethodDesc × Bool) =>
      if z.1.2.ids = [] then true else z.2) := by
    apply Primrec.ite (c := fun w : DomDesc × (MethodDesc × Bool) => w.2.1.2.ids = [])
    · exact PrimrecRel.comp Primrec.eq
        (primrec_ids.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const [])
    · exact Primrec.const true
    · exact Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr primrec_methods (Primrec.const false) hh

theorem primrec_stepActs : Primrec DomDesc.stepActs :=
  Primrec.list_flatMap primrec_methods
    (primrec_actionNames.comp (Primrec.snd.comp Primrec.snd))

theorem primrec_usableActions : Primrec usableActions := by
  refine Primrec.list_flatMap primrec_actions ?_
  exact Primrec.cond
    (primrec_memB.comp (primrec_stepActs.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    (Primrec.const [])

theorem primrec_mutFacts : Primrec mutFacts := by
  refine Primrec.list_flatMap primrec_usableActions ?_
  exact Primrec.list_append.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem primrec_splitBody : Primrec splitBody :=
  Primrec.pair (Primrec.const [0, 1])
    (Primrec.pair (Primrec.const [(0, 1)])
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) Primrec.id))
        (Primrec.list_cons.comp
          (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) Primrec.id))
          (Primrec.const []))))

theorem primrec_leafBody : Primrec leafBody :=
  Primrec.pair (Primrec.const [0])
    (Primrec.pair (Primrec.const [])
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) Primrec.id))
        (Primrec.const [])))

theorem primrec_acMethods : Primrec₂ acMethods := by
  have hsplit : Primrec (fun w : ℕ × List ℕ =>
      (List.range w.1).map fun i => ((i, splitBody (i + 1)) : MethodDesc)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (Primrec.pair Primrec.snd (primrec_splitBody.comp (Primrec.succ.comp Primrec.snd)))
  have hleaf : Primrec (fun w : ℕ × List ℕ =>
      w.2.map fun a => ((w.1, leafBody a) : MethodDesc)) :=
    Primrec.list_map (Primrec.snd)
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (primrec_leafBody.comp Primrec.snd))
  exact Primrec.list_append.comp hsplit
    (Primrec.list_cons.comp (Primrec.pair Primrec.fst (Primrec.const emptyBody)) hleaf)

theorem primrec_stripsToAcDom : Primrec stripsToAcDom :=
  Primrec.cond primrec_hasEmptyMethodB
    (Primrec.pair primrec_usableActions
      (primrec_acMethods.comp (Primrec.list_length.comp primrec_mutFacts) primrec_stepActs))
    (Primrec.const deadDom)

theorem computable_stripsToAcDom : Computable stripsToAcDom := primrec_stripsToAcDom.to_comp

theorem primrec_stripsToAcInst : Primrec stripsToAcInst :=
  primrec_stripsInst.comp primrec_initList primrec_goalList

theorem computable_stripsToAcInst : Computable stripsToAcInst := primrec_stripsToAcInst.to_comp

end Syn

end HTN
