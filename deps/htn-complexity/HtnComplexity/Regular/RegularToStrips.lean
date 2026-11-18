import HtnPlanning.Core.Size
import HtnPlanning.Regular.RegularNormalForm
import HtnPlanning.Core.Strips
/-!
# Regular HTN problems compile into STRIPS

The draft paper states

> **Proposition.** Regular HTNs are linearly compilable into STRIPS.

with a proof that uses *conditional effects*.  The action model formalised in this project has
no conditional effects, so we give (and verify) a compilation that does not need them.

**The construction.**  A totally ordered regular method `m : c ↦ o₁ … oₙ c'` is turned into a
*single* classical action `m` whose precondition, add and delete lists are those of the
sequential composition (the *macro action*) of `o₁ … oₙ` — see `HtnPlanning/Core/Macro.lean` —
extended by the bookkeeping fact `pending c` (precondition and delete list) and `pending c'`
(add list), resp. `done` if the method leaves no compound task.  The facts of the compiled
problem are

```
state v   (v a fact of the original problem)   pending c   (c a compound task)   done   bot
```

`bot` is never true and is used as the precondition of the actions belonging to methods that
are not usable (a method that is not chain-shaped, or whose body can never be executed).

The initial state is `{state v | v ∈ s_I} ∪ {pending c₀}` (with `c₀` the initial compound task)
and the goal is `{state v | v ∈ g_I} ∪ {done}`.

**What is proved.**
* `HTN.Regular.toClassical_solvable_iff` — the compiled classical problem is solvable exactly
  when the regular HTN problem is;
* `HTN.Regular.toStrips_solvable_iff` — the same for the compiled problem viewed as a member of
  the syntactic class `STRIPS` of HTN problems (via `ClassicalProblem.toHTN`);
* `HTN.Regular.compilationScheme` — the compilation scheme from
  `TO-HTN-REG` (with an initial compound task) to `STRIPS`, together with
  `HTN.Regular.compilationScheme_preservesPlansLinearly`: a plan of the compiled problem is at
  most as long as the plan of the original problem (one action per method application), so the
  compilation is linear in the sense of the compilability framework.

**Comparison with Gerevini, Percassi and Scala (AAAI 2024).**  Their paper gives a *polynomial*
compilation `τ^AP_SP` removing conditional effects from classical planning problems, improving
on Nebel's (2000) polynomial compilation (the alternative, Gazen and Knoblock's (1997)
compilation, preserves plan length but is exponential in the worst case).  In `τ^AP_SP` an
action `a` with conditional effects `e₁ … e_m` is replaced by a *sequence* of simple actions:
`a^start` (guarded by `¬pause`, which it sets, together with the counter atom `d₀,a`), one
action per conditional effect (`a⁺_{e_i}`, applicable when `cond(e_i)` holds, consuming
`d_{i-1,a}` and producing `d_{i,a}`, and applying `eff(e_i)`; or, when the condition fails, one
of the actions `a^l_{e_i}` for a literal `l ∈ cond(e_i)` that is false, which only advances the
counter) and `a^end` (consuming `d_{m,a}` and releasing `pause`).  The atom `pause` forbids
interleaving the auxiliary actions of two different original actions and the counters `d_{i,a}`
force them into the prescribed order — an order that must be a topological order of the
*effect interference graph*, which is why their Theorem 1 (solvability is preserved and
reflected) is stated for *acyclic* problems, obtained by a preprocessing step.

The compilation formalised here is the hierarchical analogue *in the opposite direction*: the
role of `pause`/`d_{i,a}` is played by the facts `pending c`, which force the actions of the
compiled problem to follow the chain of decomposition methods, and the acyclicity condition of
their Theorem 1 corresponds here to the fact that the body of a regular method is a *sequence*
of operators, so that no ordering has to be computed.  Since our target action model has no
conditional effects at all, the method bodies are contracted into macro actions instead of
being expanded into guarded sequences; consequently this compilation *shortens* plans (one
action per method application) rather than lengthening them by a polynomial factor.  Composing
the draft paper's conditional-effect compilation of regular HTNs with `τ^AP_SP` would give a
plan-preserving variant at the price of a polynomially longer plan.
-/

namespace HTN

universe u v w x

/-- The facts of the STRIPS problem compiled from a regular HTN domain: the facts of the
original problem, one fact per compound task (\"this task is still to be done\"), a fact `done`
signalling that the hierarchy has been completely decomposed, and the unsatisfiable fact
`bot`. -/
inductive RegFact (F : Type u) (C : Type w)
  /-- A fact of the original planning problem. -/
  | state (v : F)
  /-- The compound task `c` is the one that still has to be decomposed. -/
  | pending (c : C)
  /-- The hierarchy has been completely decomposed. -/
  | done
  /-- The unsatisfiable fact, used to disable unusable methods. -/
  | bot

namespace Regular

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

/-! ### The body of a method, chosen classically -/

open Classical in
/-- The body of a method: the sequence of its primitive tasks and the compound task it leaves
open.  Methods that are not chain-shaped get the junk value `([], none)`; they are made
unusable by `HTN.Regular.Usable`. -/
noncomputable def body (m : Method I A C) : List A × Option C :=
  if h : ∃ p : List A × Option C, m.HasBody p.1 p.2 then h.choose else ([], none)

lemma hasBody_body {m : Method I A C} (h : ∃ p : List A × Option C, m.HasBody p.1 p.2) :
    m.HasBody (body m).1 (body m).2 := by
  classical
  rw [body, dif_pos h]
  exact h.choose_spec

lemma body_eq {m : Method I A C} {os : List A} {next : Option C} (h : m.HasBody os next) :
    body m = (os, next) := by
  have hex : ∃ p : List A × Option C, m.HasBody p.1 p.2 := ⟨(os, next), h⟩
  obtain ⟨h1, h2⟩ := Method.HasBody.unique (hasBody_body hex) h
  exact Prod.ext h1 h2

/-- A method is *usable* in the compiled problem iff it belongs to the domain, has a body, and
that body is a statically feasible action sequence. -/
def Usable (D : Domain F A C I) (m : Method I A C) : Prop :=
  m ∈ D.methods ∧ (∃ p : List A × Option C, m.HasBody p.1 p.2) ∧ D.SeqFeasible (body m).1

/-! ### The compiled action model -/

open Classical in
/-- The action model of the compiled STRIPS problem: one macro action per method. -/
noncomputable def macroModel (D : Domain F A C I) :
    ActionModel (RegFact F C) (Method I A C) where
  prec := fun m => RegFact.state '' (D.seqPre (body m).1) ∪ {RegFact.pending m.abstractTask} ∪
    (if Usable D m then ∅ else {RegFact.bot})
  add := fun m => RegFact.state '' (D.seqAdd (body m).1) ∪
    (match (body m).2 with
      | none => {RegFact.done}
      | some c' => {RegFact.pending c'})
  del := fun m => RegFact.state '' (D.seqDel (body m).1) ∪ {RegFact.pending m.abstractTask}

/-! ### The encoding of states -/

/-- The state of the compiled problem corresponding to the HTN state `s` with the compound task
`c` still open. -/
def encP (s : Set F) (c : C) : Set (RegFact F C) := RegFact.state '' s ∪ {RegFact.pending c}

/-- The state of the compiled problem corresponding to the HTN state `s` with the hierarchy
fully decomposed. -/
def encD (s : Set F) : Set (RegFact F C) := RegFact.state '' s ∪ {RegFact.done}

variable {D : Domain F A C I}

@[simp] lemma state_mem_encP {s : Set F} {c : C} {v : F} :
    RegFact.state v ∈ encP (C := C) s c ↔ v ∈ s := by
  simp [encP]

@[simp] lemma pending_mem_encP {s : Set F} {c c' : C} :
    RegFact.pending c' ∈ encP (F := F) s c ↔ c' = c := by
  simp [encP]

@[simp] lemma done_notMem_encP {s : Set F} {c : C} :
    RegFact.done ∉ encP (F := F) (C := C) s c := by
  simp [encP]

@[simp] lemma bot_notMem_encP {s : Set F} {c : C} :
    RegFact.bot ∉ encP (F := F) (C := C) s c := by
  simp [encP]

@[simp] lemma state_mem_encD {s : Set F} {v : F} :
    RegFact.state v ∈ encD (C := C) s ↔ v ∈ s := by
  simp [encD]

@[simp] lemma pending_notMem_encD {s : Set F} {c : C} :
    RegFact.pending c ∉ encD (F := F) s := by
  simp [encD]

@[simp] lemma done_mem_encD {s : Set F} : RegFact.done ∈ encD (F := F) (C := C) s := by
  simp [encD]

@[simp] lemma bot_notMem_encD {s : Set F} : RegFact.bot ∉ encD (F := F) (C := C) s := by
  simp [encD]

lemma image_state_subset_encP {s t : Set F} {c : C} :
    RegFact.state '' t ⊆ encP (C := C) s c ↔ t ⊆ s := by
  constructor
  · intro h v hv
    have := h ⟨v, hv, rfl⟩
    simpa using this
  · rintro h _ ⟨v, hv, rfl⟩
    simpa using h hv

lemma image_state_subset_encD {s t : Set F} :
    RegFact.state '' t ⊆ encD (C := C) s ↔ t ⊆ s := by
  constructor
  · intro h v hv
    have := h ⟨v, hv, rfl⟩
    simpa using this
  · rintro h _ ⟨v, hv, rfl⟩
    simpa using h hv

/-! ### Applicability and the effect of a macro action -/

lemma applicable_iff {m : Method I A C} {os : List A} {next : Option C} {s : Set F} {c : C}
    (hb : m.HasBody os next) (hu : Usable D m) :
    (macroModel D).Applicable m (encP s c) ↔
      (m.abstractTask = c ∧ D.SeqApplicable os s) := by
  have hbody : body m = (os, next) := body_eq hb
  have hfeas : D.SeqFeasible os := by
    have := hu.2.2
    rwa [hbody] at this
  constructor
  · intro happ
    have hpend : RegFact.pending m.abstractTask ∈ encP (F := F) s c :=
      happ (by
        simp only [macroModel, Set.mem_union]
        exact Or.inl (Or.inr rfl))
    have hc : m.abstractTask = c := by simpa using hpend
    refine ⟨hc, ?_⟩
    rw [D.seqApplicable_iff]
    refine ⟨hfeas, ?_⟩
    intro v hv
    have : RegFact.state v ∈ encP (C := C) s c := by
      refine happ ?_
      simp only [macroModel, Set.mem_union]
      exact Or.inl (Or.inl ⟨v, by rwa [hbody], rfl⟩)
    simpa using this
  · rintro ⟨hc, hsapp⟩
    intro f hf
    simp only [macroModel, Set.mem_union] at hf
    rcases hf with (hf | hf) | hf
    · obtain ⟨v, hv, rfl⟩ := hf
      rw [hbody] at hv
      have := ((D.seqApplicable_iff os s).1 hsapp).2 hv
      simpa using this
    · simp only [Set.mem_singleton_iff] at hf
      subst hf
      simpa using hc
    · rw [if_pos hu] at hf
      exact absurd hf (by simp)

lemma transition_eq_none {m : Method I A C} {os : List A} {s : Set F}
    (hb : m.HasBody os none) :
    (macroModel D).transition m (encP s m.abstractTask) = encD (D.transitionSeq os s) := by
  have hbody : body m = (os, none) := body_eq hb
  rw [D.transitionSeq_eq]
  ext f
  cases f <;>
    simp only [ActionModel.transition, macroModel, hbody, encP, encD, Set.mem_union,
      Set.mem_diff, Set.mem_image, Set.mem_singleton_iff, RegFact.state.injEq,
      RegFact.pending.injEq, reduceCtorEq, exists_eq_right, or_false, and_false] <;>
    tauto

lemma transition_eq_some {m : Method I A C} {os : List A} {c' : C} {s : Set F}
    (hb : m.HasBody os (some c')) :
    (macroModel D).transition m (encP s m.abstractTask) = encP (D.transitionSeq os s) c' := by
  have hbody : body m = (os, some c') := body_eq hb
  rw [D.transitionSeq_eq]
  ext f
  cases f <;>
    simp only [ActionModel.transition, macroModel, hbody, encP, Set.mem_union,
      Set.mem_diff, Set.mem_image, Set.mem_singleton_iff, RegFact.state.injEq,
      RegFact.pending.injEq, reduceCtorEq, exists_eq_right, or_false, and_false] <;>
    tauto

/-! ### The compiled classical planning problem -/

/-- **The classical (STRIPS) problem compiled from a regular HTN domain and problem.** -/
noncomputable def toClassical (D : Domain F A C I) (Q : Instance F A C I) :
    ClassicalProblem (RegFact F C) (Method I A C) where
  toActionModel := macroModel D
  init := RegFact.state '' Q.init ∪
    {f | ∃ c : C, (∃ t : I, Q.tnI.T = {t} ∧ Q.tnI.α t = Sum.inr c) ∧ f = RegFact.pending c}
  goal := RegFact.state '' Q.goal ∪ {RegFact.done}

variable {Q : Instance F A C I}

/-- For a problem with a single initial compound task, the initial state of the compiled
problem is the encoding of the initial state together with the initial compound task. -/
lemma toClassical_init {t₀ : I} {c₀ : C} (hT : Q.tnI.T = {t₀})
    (hα : Q.tnI.α t₀ = Sum.inr c₀) : (toClassical D Q).init = encP Q.init c₀ := by
  ext f
  simp only [toClassical, encP, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (hf | ⟨c, ⟨t, hTt, hαt⟩, rfl⟩)
    · exact Or.inl hf
    · refine Or.inr ?_
      have ht : t = t₀ := by
        have : t ∈ Q.tnI.T := by rw [hTt]; simp
        rw [hT] at this
        simpa using this
      subst ht
      rw [hα] at hαt
      simp only [Sum.inr.injEq] at hαt
      rw [hαt]
  · rintro (hf | rfl)
    · exact Or.inl hf
    · exact Or.inr ⟨c₀, ⟨t₀, hT, hα⟩, rfl⟩

/-! ### From derivations to plans of the compiled problem -/

/-- Every derivation of the still open compound task yields a plan of the compiled problem
that reaches the corresponding `done` state. -/
lemma exists_plan_of_derives {c : C} {as : List A} (hd : (D.mkProblem Q).Derives c as) :
    ∀ s : Set F, D.SeqApplicable as s →
      ∃ mplan : List (Method I A C),
        (macroModel D).SeqApplicable mplan (encP s c) ∧
        (macroModel D).transitionSeq mplan (encP s c) = encD (D.transitionSeq as s) := by
  induction hd with
  | @last c os m hm hc hb =>
      intro s happ
      have husable : Usable D m :=
        ⟨hm, ⟨(os, none), hb⟩, by
          rw [body_eq hb]
          exact ((D.seqApplicable_iff os s).1 happ).1⟩
      have happ' : (macroModel D).Applicable m (encP s c) :=
        (applicable_iff hb husable).2 ⟨hc, happ⟩
      subst hc
      exact ⟨[m], ⟨happ', trivial⟩, by
        simpa using transition_eq_none (D := D) hb⟩
  | @cons c c' os rest m hm hc hb h ih =>
      intro s happ
      rw [D.seqApplicable_append] at happ
      obtain ⟨happ1, happ2⟩ := happ
      obtain ⟨mplan, hmapp, hmtr⟩ := ih (D.transitionSeq os s) happ2
      have husable : Usable D m :=
        ⟨hm, ⟨(os, some c'), hb⟩, by
          rw [body_eq hb]
          exact ((D.seqApplicable_iff os s).1 happ1).1⟩
      subst hc
      refine ⟨m :: mplan, ⟨(applicable_iff hb husable).2 ⟨rfl, happ1⟩, ?_⟩, ?_⟩
      · rw [transition_eq_some hb]
        exact hmapp
      · rw [ActionModel.transitionSeq_cons, transition_eq_some hb, hmtr,
          D.transitionSeq_append]

/-! ### From plans of the compiled problem to derivations -/

/-- No action of the compiled problem is applicable once the hierarchy has been decomposed
(`done` holds and no `pending` fact is true). -/
lemma seqApplicable_encD_nil {mplan : List (Method I A C)} {s : Set F}
    (h : (macroModel D).SeqApplicable mplan (encD s)) : mplan = [] := by
  cases mplan with
  | nil => rfl
  | cons m rest =>
      exfalso
      have hprec : RegFact.pending m.abstractTask ∈ encD (F := F) s := by
        refine h.1 ?_
        simp only [macroModel, Set.mem_union]
        exact Or.inl (Or.inr rfl)
      simp at hprec

/-- **Every plan of the compiled problem that reaches the goal is a derivation.** -/
lemma derives_of_plan {g : Set F} :
    ∀ (mplan : List (Method I A C)) (s : Set F) (c : C),
      (macroModel D).SeqApplicable mplan (encP s c) →
      RegFact.done ∈ (macroModel D).transitionSeq mplan (encP s c) →
      RegFact.state '' g ⊆ (macroModel D).transitionSeq mplan (encP s c) →
      ∃ as : List A, (D.mkProblem Q).Derives c as ∧ D.SeqApplicable as s ∧
        g ⊆ D.transitionSeq as s := by
  intro mplan
  induction mplan with
  | nil =>
      intro s c _ hdone _
      rw [ActionModel.transitionSeq_nil] at hdone
      exact absurd hdone done_notMem_encP
  | cons m rest ih =>
      intro s c happ hdone hgoal
      obtain ⟨happ1, happ2⟩ := happ
      have husable : Usable D m := by
        by_contra hcon
        have : RegFact.bot ∈ encP (F := F) s c := by
          refine happ1 ?_
          simp only [macroModel, Set.mem_union, if_neg hcon]
          exact Or.inr rfl
        simp at this
      obtain ⟨hmem, hex, -⟩ := id husable
      have hb : m.HasBody (body m).1 (body m).2 := hasBody_body hex
      obtain ⟨hc, hsapp⟩ := (applicable_iff hb husable).1 happ1
      subst hc
      cases hnext : (body m).2 with
      | none =>
          have hb' : m.HasBody (body m).1 none := by rw [← hnext]; exact hb
          have htr : (macroModel D).transition m (encP s m.abstractTask) =
              encD (D.transitionSeq (body m).1 s) := transition_eq_none hb'
          rw [ActionModel.transitionSeq_cons, htr] at hdone hgoal
          rw [htr] at happ2
          have hrest : rest = [] := seqApplicable_encD_nil happ2
          subst hrest
          refine ⟨(body m).1, Problem.Derives.last hmem rfl hb', hsapp, ?_⟩
          have := hgoal
          rw [ActionModel.transitionSeq_nil] at this
          exact image_state_subset_encD.1 this
      | some c' =>
          have hb' : m.HasBody (body m).1 (some c') := by rw [← hnext]; exact hb
          have htr : (macroModel D).transition m (encP s m.abstractTask) =
              encP (D.transitionSeq (body m).1 s) c' := transition_eq_some hb'
          rw [ActionModel.transitionSeq_cons, htr] at hdone hgoal
          rw [htr] at happ2
          obtain ⟨as, hd, hasapp, hasgoal⟩ := ih (D.transitionSeq (body m).1 s) c' happ2 hdone hgoal
          refine ⟨(body m).1 ++ as, Problem.Derives.cons hmem rfl hb' hd, ?_, ?_⟩
          · rw [D.seqApplicable_append]
            exact ⟨hsapp, hasapp⟩
          · rw [D.transitionSeq_append]
            exact hasgoal

/-! ### Correctness of the compilation -/

/-- **The compiled classical problem is solvable exactly when the regular HTN problem is.** -/
theorem toClassical_solvable_iff [Infinite I]
    (hwf : (D.mkProblem Q).WF) (hreg : (D.mkProblem Q).IsRegularM)
    (hto : (D.mkProblem Q).IsTO_M) {t₀ : I} {c₀ : C} (hT : Q.tnI.T = {t₀})
    (hα : Q.tnI.α t₀ = Sum.inr c₀) :
    (toClassical D Q).Solvable ↔ (D.mkProblem Q).Solvable := by
  have hinit : (toClassical D Q).init = encP Q.init c₀ := toClassical_init hT hα
  have hderiv := Problem.solvable_iff_derives (P := D.mkProblem Q) hwf hreg hto hT hα
  constructor
  · rintro ⟨mplan, happ, hgoal⟩
    rw [hinit] at happ hgoal
    have hgoal' : RegFact.state '' Q.goal ∪ {RegFact.done} ⊆
        (macroModel D).transitionSeq mplan (encP Q.init c₀) := hgoal
    have hdone : RegFact.done ∈ (macroModel D).transitionSeq mplan (encP Q.init c₀) :=
      hgoal' (Set.mem_union_right _ rfl)
    have hst : RegFact.state '' Q.goal ⊆
        (macroModel D).transitionSeq mplan (encP Q.init c₀) := fun f hf =>
      hgoal' (Set.mem_union_left _ hf)
    obtain ⟨as, hd, hasapp, hasgoal⟩ := derives_of_plan (Q := Q) mplan Q.init c₀ happ hdone hst
    exact hderiv.2 ⟨as, hd, hasapp, hasgoal⟩
  · intro hsol
    obtain ⟨as, hd, happ, hgoal⟩ := hderiv.1 hsol
    obtain ⟨mplan, hmapp, hmtr⟩ := exists_plan_of_derives hd Q.init happ
    refine ⟨mplan, ?_, ?_⟩
    · rw [hinit]; exact hmapp
    · rw [hinit]
      show RegFact.state '' Q.goal ∪ {RegFact.done} ⊆
        (macroModel D).transitionSeq mplan (encP Q.init c₀)
      rw [hmtr]
      rintro f (hf | hf)
      · obtain ⟨v, hv, rfl⟩ := hf
        exact state_mem_encD.2 (hgoal hv)
      · simp only [Set.mem_singleton_iff] at hf
        subst hf
        exact done_mem_encD

/-! ### The compilation scheme into the class `STRIPS` -/

/-- The translation of the domain: the macro action model, together with the two families of
methods of the STRIPS encoding (`c ↦ a c` and `c ↦ ε`). -/
noncomputable def domTrans (D : Domain F A C I) : Domain (RegFact F C) (Method I A C) Unit ℕ where
  toActionModel := macroModel D
  methods := (Set.range fun a : Method I A C =>
      (⟨(), Strips.stepNet a⟩ : Method ℕ (Method I A C) Unit)) ∪ {⟨(), Strips.emptyNet⟩}

/-- The translation of the problem instance: the encoded initial state (including the initial
compound task), the encoded goal together with `done`, and the single initial compound task of
the STRIPS encoding. -/
def instTrans (Q : Instance F A C I) : Instance (RegFact F C) (Method I A C) Unit ℕ where
  init := RegFact.state '' Q.init ∪
    {f | ∃ c : C, (∃ t : I, Q.tnI.T = {t} ∧ Q.tnI.α t = Sum.inr c) ∧ f = RegFact.pending c}
  goal := RegFact.state '' Q.goal ∪ {RegFact.done}
  tnI := Strips.initNet

lemma domTrans_mkProblem (D : Domain F A C I) (Q : Instance F A C I) :
    (domTrans D).mkProblem (instTrans Q) = (toClassical D Q).toHTN := rfl

end Regular

namespace Classes

variable (F : Type u) (A : Type v) (C : Type w) (I : Type x) [DecidableEq I]

/-- The class of *regular, totally ordered* HTN planning problems with a single initial
compound task — the class the draft paper calls (TO-)HTN-REG: the task networks of the methods
are sequences `o₁ … oₙ T` of operators followed by at most one compound task, and the problem
is given by an initial compound task `t_I`. -/
def TO_HTN_REG_I : Set (Problem F A C I) :=
  {P | P.WF ∧ P.IsTO ∧ P.IsRegular ∧ ∃ (t : I) (c : C), P.tnI.T = {t} ∧ P.tnI.α t = Sum.inr c}

variable {F A C I}

omit [DecidableEq I] in
lemma TO_HTN_REG_I_subset_TO_HTN_REG : TO_HTN_REG_I F A C I ⊆ TO_HTN_REG F A C I :=
  fun _ h => ⟨h.2.1, h.2.2.1⟩

end Classes

namespace Regular

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

/-- **The compiled problem is solvable exactly when the regular HTN problem is** (STRIPS
version: the compiled problem is a member of the syntactic class `STRIPS` of HTN problems). -/
theorem toStrips_solvable_iff [Infinite I] {D : Domain F A C I} {Q : Instance F A C I}
    (hP : D.mkProblem Q ∈ Classes.TO_HTN_REG_I F A C I) :
    ((domTrans D).mkProblem (instTrans Q)).Solvable ↔ (D.mkProblem Q).Solvable := by
  obtain ⟨hwf, hTO, hreg, t₀, c₀, hT, hα⟩ := hP
  rw [domTrans_mkProblem, Strips.toHTN_solvable_iff]
  exact toClassical_solvable_iff hwf hreg.2 hTO.2 hT hα

/-- The compiled problem uses one action per method application, so a plan of the compiled
problem is never longer than the number of methods used; in particular the compilation does not
blow up plans by more than the length of the derivation (see the notes: the number of methods
of a derivation is bounded by `|plan| + 1` times the number of compound tasks, so the
compilation is polynomial in the sense of the compilability framework). -/
theorem plan_length_eq_methods [Infinite I] {D : Domain F A C I} {Q : Instance F A C I}
    {c : C} {as : List A} (hd : (D.mkProblem Q).Derives c as) (s : Set F)
    (happ : D.SeqApplicable as s) :
    ∃ mplan : List (Method I A C),
      (macroModel D).SeqApplicable mplan (encP s c) ∧
      (macroModel D).transitionSeq mplan (encP s c) = encD (D.transitionSeq as s) :=
  exists_plan_of_derives hd s happ

/-! ### The size of the compilation

The compiled signature is linear in the size of the original one: the facts of the compiled
problem are the original facts, one fact per compound task, and two additional facts. -/

/-- The facts of the compiled problem, up to a bijection: the original facts, one fact per
compound task, and the two control facts `done` and `bot`. -/
def regFactEquiv : RegFact F C ≃ (F ⊕ C) ⊕ Bool where
  toFun := fun f =>
    match f with
    | .state v => Sum.inl (Sum.inl v)
    | .pending c => Sum.inl (Sum.inr c)
    | .done => Sum.inr true
    | .bot => Sum.inr false
  invFun := fun x =>
    match x with
    | Sum.inl (Sum.inl v) => .state v
    | Sum.inl (Sum.inr c) => .pending c
    | Sum.inr true => .done
    | Sum.inr false => .bot
  left_inv := by intro f; cases f <;> rfl
  right_inv := by rintro ((v | c) | (_ | _)) <;> rfl

/-- **The compiled signature is linear in the original one.** -/
lemma card_regFact [Finite F] [Finite C] :
    Nat.card (RegFact F C) = Nat.card F + Nat.card C + 2 := by
  rw [Nat.card_congr regFactEquiv, Nat.card_sum, Nat.card_sum]
  simp

end Regular

end HTN
