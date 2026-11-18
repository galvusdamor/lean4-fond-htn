import HtnComplexity.Computable.Rooted
import HtnComplexity.Regular.RegularToStrips
import HtnPlanning.Computable.Linearise
import HtnPlanning.Computable.MacroLists
import HtnComplexity.Computable.StripsTarget
import HtnPlanning.Computable.Classes
import HtnPlanning.Classes.Basic
import HtnPlanning.SynClasses.Basic
/-!
# Totally ordered regular problems compile into `STRIPS`, computably

This is the description-level counterpart of `HtnComplexity/Regular/RegularToStrips.lean`: the
compilation of the class `TO-HTN-REG` into `STRIPS` — the entry marked `1` of the compilability
table — carried out on the **finite descriptions** of
`HtnPlanning/Computable/Syntax.lean`, with a computable translation of descriptions and
a polynomial bound on the number of symbols of the result.

**The source class.**  As in `HTN.Classes.TO_HTN_REG_I` (and as in the compilability
literature) the initial task network of the source instance is a *single compound task*:
`HTN.Syn.InstDesc.IsRooted`.  This is not a technical convenience but a necessity for a target
in the class `STRIPS`: a described `STRIPS` instance carries no task network at all beyond the
single compound task `0`, so the only channel from the source instance into the *dynamics* of
the compiled problem is the initial state, of which the compiled domain can read only the
finitely many facts it mentions.  The general cell — with an arbitrary totally ordered initial
task network in the source instance — therefore stays open; see `TABLE.md`.

**The construction** is the one of `HtnComplexity/Regular/RegularToStrips.lean`: a method
`c ↦ o₁ … oₙ c'` becomes a single action, the *macro action* of `o₁ … oₙ`
(`HtnPlanning/Computable/MacroLists.lean`), guarded by the bookkeeping fact `pending c`
which it deletes, and adding `pending c'` — or `done` if the method leaves no compound task.
Unusable methods (whose body is not statically feasible) get the unsatisfiable precondition
`bot`.  The facts of the compiled description are the numbers

    state v = 4 v      pending c = 4 c + 1      done = 2      bot = 3

and the actions are numbered by the position of their method in the description.  Extracting
the body of a method from its description is what
`HtnPlanning/Computable/Linearise.lean` (and, under it,
`HtnPlanning/Computable/Reach.lean`) is for: the order of the subtasks is the transitive
closure of the *listed* ordering pairs, and has to be computed.

**What is proved.**

* `HTN.Syn.solvable_regStrips_iff` — the compiled description is solvable exactly when the
  source description is;
* `HTN.Syn.size_regStripsDom_le`, `HTN.Syn.size_regStripsInst_le` — the compiled description is
  polynomial in the source description;
* `HTN.Syn.computable_regStripsDom`, `HTN.Syn.computable_regStripsInst` — both translations are
  primitive recursive;
* hence the cell `HTN.Syn.compSyn_TO_HTN_REG_root_to_STRIPS`, and with the reverse inclusion
  `HTN.Syn.SynClass.sub_STRIPS_TO_HTN_REG_root` the two classes are inter-compilable.
-/

namespace HTN

namespace Syn

open Regular

/-! ### The encoding of the facts -/

/-- The facts of the compiled description: `state v = 4v`, `pending c = 4c+1`, `done = 2`,
`bot = 3`. -/
def encFact : RegFact ℕ ℕ → ℕ
  | RegFact.state v => 4 * v
  | RegFact.pending c => 4 * c + 1
  | RegFact.done => 2
  | RegFact.bot => 3

theorem encFact_injective : Function.Injective encFact := by
  intro a b h
  cases a <;> cases b <;>
    simp only [encFact, RegFact.state.injEq, RegFact.pending.injEq] at h ⊢ <;> omega

theorem encFact_image_subset_iff {X Y : Set (RegFact ℕ ℕ)} :
    encFact '' X ⊆ encFact '' Y ↔ X ⊆ Y :=
  Set.image_subset_image_iff encFact_injective

theorem image_encFact_state_list (l : List ℕ) :
    encFact '' (RegFact.state '' {v | v ∈ l}) = {f | f ∈ l.map fun v => 4 * v} := by
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨g, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨RegFact.state v, ⟨v, hv, rfl⟩, rfl⟩

theorem image_encFact_pending (c : ℕ) :
    encFact '' ({RegFact.pending c} : Set (RegFact ℕ ℕ)) = {4 * c + 1} :=
  Set.image_singleton

theorem image_encFact_done :
    encFact '' ({RegFact.done} : Set (RegFact ℕ ℕ)) = {2} :=
  Set.image_singleton

theorem image_encFact_bot :
    encFact '' ({RegFact.bot} : Set (RegFact ℕ ℕ)) = {3} :=
  Set.image_singleton

/-- Membership in an appended list, as a union of sets. -/
theorem setOf_mem_append (l₁ l₂ : List ℕ) :
    {f | f ∈ l₁ ++ l₂} = {f | f ∈ l₁} ∪ {f | f ∈ l₂} := by
  ext f; simp

/-! ### The compiled domain description -/

/-- The compiled action of the method description at position `i`. -/
def regAction (d : DomDesc) (i : ℕ) : ActionDesc :=
  let e := d.methods.getI i
  let b := TnDesc.bodyOf e.2
  let m := d.macroFold b.1
  (i,
    (m.1.1.map fun v => 4 * v) ++ (4 * e.1 + 1) :: (if m.2 then [] else [3]),
    (m.1.2.1.map fun v => 4 * v) ++
      (match b.2 with
        | none => [2]
        | some c' => [4 * c' + 1]),
    (m.1.2.2.map fun v => 4 * v) ++ [4 * e.1 + 1])

/-- The compiled actions: one per listed method. -/
def regActions (d : DomDesc) : List ActionDesc :=
  (List.range d.methods.length).map (regAction d)

/-- **The compiled domain description.** -/
def regStripsDom (d : DomDesc) : DomDesc := stripsDom (regActions d)

/-- **The compiled instance description.** -/
def regStripsInst (q : InstDesc) : InstDesc :=
  stripsInst ((q.initList.map fun v => 4 * v) ++ [4 * rootName q + 1])
    ((q.goalList.map fun v => 4 * v) ++ [2])

/-! ### Correctness -/

section Correct

variable {d : DomDesc} {q : InstDesc}

/-- A lookup in a list of key-tagged entries, all of whose keys are known. -/
theorem lookup_map_of_fst {β : Type} (f : ℕ → ℕ × β) (hf : ∀ i, (f i).1 = i) :
    ∀ (l : List ℕ) {i : ℕ}, i ∈ l → (l.map f).lookup i = some (f i).2 := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    intro i hi
    rw [List.map_cons, show f a = ((f a).1, (f a).2) from rfl, List.lookup_cons, hf a]
    by_cases h : i = a
    · subst h
      simp
    · have hb : (i == a) = false := by simp [h]
      rw [hb]
      exact ih (by rcases List.mem_cons.1 hi with rfl | hi; · exact absurd rfl h
                   · exact hi)

/-- The compiled domain description mentions exactly the compiled actions. -/
theorem lookup_regActions {i : ℕ} (hi : i < d.methods.length) :
    (regActions d).lookup i = some (regAction d i).2 :=
  lookup_map_of_fst (regAction d) (fun _ => rfl) _ (List.mem_range.2 hi)

theorem actNames_regStripsDom (d : DomDesc) :
    (regStripsDom d).actNames = List.range d.methods.length := by
  simp only [DomDesc.actNames, regStripsDom, stripsDom_actions, regActions, List.map_map]
  exact List.map_id'' (fun _ => rfl) _

theorem mem_methods_getI (hi : i < d.methods.length) : d.methods.getI i ∈ d.methods := by
  rw [List.getI_eq_getElem (l := d.methods) hi]
  exact List.getElem_mem hi

/-- The body a described method has, in the sense of `HTN.Method.HasBody`. -/
theorem body_getI (hTO : d.MethodsTO) (hreg : d.MethodsReg) {i : ℕ}
    (hi : i < d.methods.length) :
    Regular.body (d.methods.getI i).toMethod = TnDesc.bodyOf (d.methods.getI i).2 :=
  Regular.body_eq (TnDesc.hasBody_bodyOf (hTO _ (mem_methods_getI hi))
    (hreg _ (mem_methods_getI hi)) (d.methods.getI i).1)

/-- A described method is usable exactly when the described body is statically feasible. -/
theorem usable_getI_iff (hTO : d.MethodsTO) (hreg : d.MethodsReg) {i : ℕ}
    (hi : i < d.methods.length) :
    Regular.Usable d.toDomain (d.methods.getI i).toMethod ↔
      d.feasibleB (TnDesc.bodyOf (d.methods.getI i).2).1 = true := by
  have hb : Method.HasBody (d.methods.getI i).toMethod
      (TnDesc.bodyOf (d.methods.getI i).2).1 (TnDesc.bodyOf (d.methods.getI i).2).2 :=
    TnDesc.hasBody_bodyOf (hTO _ (mem_methods_getI hi)) (hreg _ (mem_methods_getI hi))
      (d.methods.getI i).1
  have hmem : (d.methods.getI i).toMethod ∈ d.toDomain.methods :=
    ⟨d.methods.getI i, mem_methods_getI hi, rfl⟩
  rw [Regular.Usable, body_getI hTO hreg hi, DomDesc.feasibleB_iff]
  simp only [hmem, true_and]
  exact ⟨fun h => h.2, fun h => ⟨⟨_, hb⟩, h⟩⟩

/-- **The compiled action has the precondition of the macro action of its method.** -/
theorem prec_regStripsDom (hTO : d.MethodsTO) (hreg : d.MethodsReg) {i : ℕ}
    (hi : i < d.methods.length) :
    (regStripsDom d).prec i =
      encFact '' (macroModel d.toDomain).prec (d.methods.getI i).toMethod := by
  have hlookup : (regStripsDom d).actions.lookup i = some (regAction d i).2 :=
    lookup_regActions hi
  have hbody := body_getI hTO hreg hi
  have hL : (regStripsDom d).prec i = {f | f ∈ (regAction d i).2.1} := by
    simp [DomDesc.prec, hlookup]
  rw [hL]
  by_cases hu : Usable d.toDomain (d.methods.getI i).toMethod
  · have hf : (d.macroFold (TnDesc.bodyOf (d.methods.getI i).2).1).2 = true := by
      have := (usable_getI_iff hTO hreg hi).1 hu
      simpa [DomDesc.feasibleB] using this
    have hR : (macroModel d.toDomain).prec (d.methods.getI i).toMethod =
        RegFact.state '' {v | v ∈ d.seqPreList (TnDesc.bodyOf (d.methods.getI i).2).1} ∪
          {RegFact.pending (d.methods.getI i).1} := by
      simp only [macroModel, MethodDesc.toMethod_abstractTask, hu, if_true, Set.union_empty]
      rw [hbody, ← DomDesc.seqPreList_eq]
    rw [hR, Set.image_union, image_encFact_state_list, image_encFact_pending]
    ext f
    simp only [regAction, DomDesc.seqPreList, hf, if_true, Set.mem_setOf_eq, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Set.mem_union, Set.mem_singleton_iff]
  · have hf : (d.macroFold (TnDesc.bodyOf (d.methods.getI i).2).1).2 = false := by
      rcases h : (d.macroFold (TnDesc.bodyOf (d.methods.getI i).2).1).2 with _ | _
      · rfl
      · exact absurd ((usable_getI_iff hTO hreg hi).2 (by simpa [DomDesc.feasibleB] using h)) hu
    have hR : (macroModel d.toDomain).prec (d.methods.getI i).toMethod =
        RegFact.state '' {v | v ∈ d.seqPreList (TnDesc.bodyOf (d.methods.getI i).2).1} ∪
          {RegFact.pending (d.methods.getI i).1} ∪ {RegFact.bot} := by
      simp only [macroModel, MethodDesc.toMethod_abstractTask, hu, if_false]
      rw [hbody, ← DomDesc.seqPreList_eq]
    rw [hR, Set.image_union, Set.image_union, image_encFact_state_list, image_encFact_pending,
      image_encFact_bot]
    ext f
    simp only [regAction, DomDesc.seqPreList, hf, Bool.false_eq_true, if_false,
      Set.mem_setOf_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_union, Set.mem_singleton_iff]
    tauto

theorem add_regStripsDom (hTO : d.MethodsTO) (hreg : d.MethodsReg) {i : ℕ}
    (hi : i < d.methods.length) :
    (regStripsDom d).add i =
      encFact '' (macroModel d.toDomain).add (d.methods.getI i).toMethod := by
  have hlookup : (regStripsDom d).actions.lookup i = some (regAction d i).2 :=
    lookup_regActions hi
  have hbody := body_getI hTO hreg hi
  have hL : (regStripsDom d).add i = {f | f ∈ (regAction d i).2.2.1} := by
    simp [DomDesc.add, hlookup]
  rw [hL]
  rcases hn : (TnDesc.bodyOf (d.methods.getI i).2).2 with _ | c'
  · have hR : (macroModel d.toDomain).add (d.methods.getI i).toMethod =
        RegFact.state '' {v | v ∈ d.seqAddList (TnDesc.bodyOf (d.methods.getI i).2).1} ∪
          {RegFact.done} := by
      simp only [macroModel]
      rw [hbody, ← DomDesc.seqAddList_eq, hn]
    rw [hR, Set.image_union, image_encFact_state_list, image_encFact_done]
    ext f
    simp only [regAction, DomDesc.seqAddList, hn, Set.mem_setOf_eq, List.mem_append,
      List.mem_singleton, Set.mem_union, Set.mem_singleton_iff]
  · have hR : (macroModel d.toDomain).add (d.methods.getI i).toMethod =
        RegFact.state '' {v | v ∈ d.seqAddList (TnDesc.bodyOf (d.methods.getI i).2).1} ∪
          {RegFact.pending c'} := by
      simp only [macroModel]
      rw [hbody, ← DomDesc.seqAddList_eq, hn]
    rw [hR, Set.image_union, image_encFact_state_list, image_encFact_pending]
    ext f
    simp only [regAction, DomDesc.seqAddList, hn, Set.mem_setOf_eq, List.mem_append,
      List.mem_singleton, Set.mem_union, Set.mem_singleton_iff]

theorem del_regStripsDom (hTO : d.MethodsTO) (hreg : d.MethodsReg) {i : ℕ}
    (hi : i < d.methods.length) :
    (regStripsDom d).del i =
      encFact '' (macroModel d.toDomain).del (d.methods.getI i).toMethod := by
  have hlookup : (regStripsDom d).actions.lookup i = some (regAction d i).2 :=
    lookup_regActions hi
  have hbody := body_getI hTO hreg hi
  have hL : (regStripsDom d).del i = {f | f ∈ (regAction d i).2.2.2} := by
    simp [DomDesc.del, hlookup]
  have hR : (macroModel d.toDomain).del (d.methods.getI i).toMethod =
      RegFact.state '' {v | v ∈ d.seqDelList (TnDesc.bodyOf (d.methods.getI i).2).1} ∪
        {RegFact.pending (d.methods.getI i).1} := by
    simp only [macroModel, MethodDesc.toMethod_abstractTask]
    rw [hbody, ← DomDesc.seqDelList_eq]
  rw [hL, hR, Set.image_union, image_encFact_state_list, image_encFact_pending]
  ext f
  simp only [regAction, DomDesc.seqDelList, Set.mem_setOf_eq, List.mem_append,
    List.mem_singleton, Set.mem_union, Set.mem_singleton_iff]

/-- The one-step correspondence between the compiled action model and the macro action
model. -/
theorem transition_regStripsDom (hTO : d.MethodsTO) (hreg : d.MethodsReg) {i : ℕ}
    (hi : i < d.methods.length) (S : Set (RegFact ℕ ℕ)) :
    (regStripsDom d).toDomain.transition i (encFact '' S) =
      encFact '' (macroModel d.toDomain).transition (d.methods.getI i).toMethod S := by
  show ((encFact '' S) \ (regStripsDom d).del i) ∪ (regStripsDom d).add i = _
  rw [del_regStripsDom hTO hreg hi, add_regStripsDom hTO hreg hi,
    ← Set.image_diff encFact_injective, ← Set.image_union]
  rfl

theorem applicable_regStripsDom (hTO : d.MethodsTO) (hreg : d.MethodsReg) {i : ℕ}
    (hi : i < d.methods.length) (S : Set (RegFact ℕ ℕ)) :
    (regStripsDom d).toDomain.Applicable i (encFact '' S) ↔
      (macroModel d.toDomain).Applicable (d.methods.getI i).toMethod S := by
  show (regStripsDom d).prec i ⊆ encFact '' S ↔ _
  rw [prec_regStripsDom hTO hreg hi]
  exact encFact_image_subset_iff

/-- An applicable method of the macro action model is usable, as long as the state does not
contain the unsatisfiable fact. -/
theorem usable_of_applicable {m : Method ℕ ℕ ℕ} {S : Set (RegFact ℕ ℕ)}
    (hbot : RegFact.bot ∉ S) (h : (macroModel d.toDomain).Applicable m S) :
    Usable d.toDomain m := by
  by_contra hcon
  refine hbot (h ?_)
  simp only [macroModel, Set.mem_union, if_neg hcon]
  exact Or.inr rfl

theorem bot_notMem_transition {m : Method ℕ ℕ ℕ} {S : Set (RegFact ℕ ℕ)}
    (hbot : RegFact.bot ∉ S) :
    RegFact.bot ∉ (macroModel d.toDomain).transition m S := by
  intro hmem
  rcases hmem with hmem | hmem
  · exact hbot hmem.1
  · simp only [macroModel, Set.mem_union] at hmem
    rcases hmem with hmem | hmem
    · obtain ⟨v, -, hv⟩ := hmem
      exact absurd hv (by simp)
    · rcases hnext : (Regular.body m).2 with _ | c' <;> rw [hnext] at hmem <;> simp at hmem

/-- Every plan of the macro action model is a plan of the compiled description. -/
theorem exists_plan_of_mplan (hTO : d.MethodsTO) (hreg : d.MethodsReg) :
    ∀ (mplan : List (Method ℕ ℕ ℕ)) (S : Set (RegFact ℕ ℕ)), RegFact.bot ∉ S →
      (macroModel d.toDomain).SeqApplicable mplan S →
      ∃ bs : List ℕ, (regStripsDom d).toDomain.SeqApplicable bs (encFact '' S) ∧
        (regStripsDom d).toDomain.transitionSeq bs (encFact '' S) =
          encFact '' (macroModel d.toDomain).transitionSeq mplan S := by
  intro mplan
  induction mplan with
  | nil => intro S _ _; exact ⟨[], trivial, rfl⟩
  | cons m rest ih =>
    intro S hbot happ
    obtain ⟨happ1, happ2⟩ := happ
    obtain ⟨hmem, -, -⟩ := usable_of_applicable hbot happ1
    obtain ⟨e, he, hem⟩ := hmem
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.1 he
    have hgetI : d.methods.getI i = e := by
      rw [List.getI_eq_getElem (l := d.methods) hi, hgi]
    have hm : (d.methods.getI i).toMethod = m := by rw [hgetI, hem]
    have happ1' : (regStripsDom d).toDomain.Applicable i (encFact '' S) := by
      rw [applicable_regStripsDom hTO hreg hi, hm]
      exact happ1
    have htr : (regStripsDom d).toDomain.transition i (encFact '' S) =
        encFact '' (macroModel d.toDomain).transition m S := by
      rw [transition_regStripsDom hTO hreg hi, hm]
    obtain ⟨bs, hbs1, hbs2⟩ := ih ((macroModel d.toDomain).transition m S)
      (bot_notMem_transition hbot) happ2
    refine ⟨i :: bs, ⟨happ1', by rw [htr]; exact hbs1⟩, ?_⟩
    rw [ActionModel.transitionSeq_cons, htr, hbs2, ActionModel.transitionSeq_cons]

/-- ... and conversely. -/
theorem exists_mplan_of_plan (hTO : d.MethodsTO) (hreg : d.MethodsReg) :
    ∀ (bs : List ℕ), (∀ b ∈ bs, b ∈ (regStripsDom d).actNames) →
      ∀ S : Set (RegFact ℕ ℕ), (regStripsDom d).toDomain.SeqApplicable bs (encFact '' S) →
        ∃ mplan : List (Method ℕ ℕ ℕ), (macroModel d.toDomain).SeqApplicable mplan S ∧
          (regStripsDom d).toDomain.transitionSeq bs (encFact '' S) =
            encFact '' (macroModel d.toDomain).transitionSeq mplan S := by
  intro bs
  induction bs with
  | nil => intro _ S _; exact ⟨[], trivial, rfl⟩
  | cons b rest ih =>
    intro hbs S happ
    obtain ⟨happ1, happ2⟩ := happ
    have hb : b < d.methods.length := by
      have := hbs b (by simp)
      rw [actNames_regStripsDom] at this
      exact List.mem_range.1 this
    set m := (d.methods.getI b).toMethod with hm
    have happ1' : (macroModel d.toDomain).Applicable m S :=
      (applicable_regStripsDom hTO hreg hb S).1 happ1
    have htr : (regStripsDom d).toDomain.transition b (encFact '' S) =
        encFact '' (macroModel d.toDomain).transition m S :=
      transition_regStripsDom hTO hreg hb S
    rw [htr] at happ2
    obtain ⟨mplan, hm1, hm2⟩ := ih (fun x hx => hbs x (List.mem_cons_of_mem _ hx))
      ((macroModel d.toDomain).transition m S) happ2
    refine ⟨m :: mplan, ⟨happ1', hm1⟩, ?_⟩
    rw [ActionModel.transitionSeq_cons, htr, hm2, ActionModel.transitionSeq_cons]

/-- The initial state of the compiled instance is the encoded initial state of the compiled
classical problem. -/
theorem init_regStripsInst (q : InstDesc) :
    {f | f ∈ (regStripsInst q).initList} =
      encFact '' encP q.toInstance.init (rootName q) := by
  rw [show (regStripsInst q).initList =
      (q.initList.map fun v => 4 * v) ++ [4 * rootName q + 1] from rfl,
    setOf_mem_append, encP, Set.image_union,
    show q.toInstance.init = {v | v ∈ q.initList} from rfl,
    image_encFact_state_list, image_encFact_pending]
  ext f
  simp

theorem goal_regStripsInst (q : InstDesc) :
    {f | f ∈ (regStripsInst q).goalList} =
      encFact '' (RegFact.state '' q.toInstance.goal ∪ {RegFact.done}) := by
  rw [show (regStripsInst q).goalList = (q.goalList.map fun v => 4 * v) ++ [2] from rfl,
    setOf_mem_append, Set.image_union,
    show q.toInstance.goal = {v | v ∈ q.goalList} from rfl,
    image_encFact_state_list, image_encFact_done]
  ext f
  simp

/-- **Correctness of the compilation.** -/
theorem solvable_regStrips_iff (hTO : d.MethodsTO) (hreg : d.MethodsReg) (hq : q.IsRooted) :
    Solvable d q ↔ Solvable (regStripsDom d) (regStripsInst q) := by
  obtain ⟨t₀, hT, hα⟩ := InstDesc.rootName_spec hq
  set c₀ := rootName q with hc₀
  have hclass : (Regular.toClassical d.toDomain q.toInstance).Solvable ↔ Solvable d q :=
    Regular.toClassical_solvable_iff (problem_wf d q) (isRegularM_problem hreg)
      (isTO_problem hTO hq.isTO).2 hT hα
  have hinit : (Regular.toClassical d.toDomain q.toInstance).init = encP q.toInstance.init c₀ :=
    Regular.toClassical_init hT hα
  rw [← hclass,
    show Solvable (regStripsDom d) (regStripsInst q) ↔
      ∃ as : List ℕ, (regStripsDom d).toDomain.SeqApplicable as
          {f | f ∈ (regStripsInst q).initList} ∧
        {f | f ∈ (regStripsInst q).goalList} ⊆
          (regStripsDom d).toDomain.transitionSeq as {f | f ∈ (regStripsInst q).initList} from
      solvable_strips_iff (regActions d) _ _]
  rw [init_regStripsInst q, goal_regStripsInst q]
  constructor
  · rintro ⟨mplan, happ, hgoal⟩
    rw [hinit] at happ hgoal
    obtain ⟨bs, hbs1, hbs2⟩ := exists_plan_of_mplan hTO hreg mplan _ (by simp [encP]) happ
    refine ⟨bs, hbs1, ?_⟩
    rw [hbs2]
    exact Set.image_mono hgoal
  · rintro ⟨bs, happ, hgoal⟩
    obtain ⟨cs, hcs, hc1, hc2⟩ :=
      exists_plan_mem_of_plan (regStripsDom d) _ bs happ
    obtain ⟨mplan, hm1, hm2⟩ := exists_mplan_of_plan hTO hreg cs hcs _ hc1
    refine ⟨mplan, by rw [hinit]; exact hm1, ?_⟩
    rw [hinit]
    rw [hc2] at hm2
    have := hgoal
    rw [hm2] at this
    exact encFact_image_subset_iff.1 this

end Correct

/-! ### The compiled description belongs to the class `STRIPS` -/

theorem regStripsDom_isStrips (d : DomDesc) : (regStripsDom d).IsStrips :=
  stripsDom_isStrips _

theorem regStripsInst_isStrips (q : InstDesc) : (regStripsInst q).IsStrips :=
  stripsInst_isStrips _ _


end Syn

end HTN
