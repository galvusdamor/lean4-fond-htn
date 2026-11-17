import FondHtn.MethodPoliciesStrong
import FondHtn.FixedMethodsRelations
import HtnComplexity.Article.PlanEx
import HtnComplexity.Article.Valid
/-!
# Descriptions of FOND HTN problems and the plan-existence languages

Complexity results are statements about languages of bit strings.  As in the deterministic
development (`HtnComplexity/Article/PlanEx.lean`), a problem is given as the code of a finite,
well-formed *description*:

* `FOND.FActDesc` — an action: its name, `Π⁺`, `Π⁻`, and the list of its effects `(add, del)`;
* `FOND.FProbDesc` — a problem: actions and methods (the domain), the initial state and the
  initial task network.  Methods and task networks are described as in the deterministic case
  (`HTN.Syn.MethodDesc`, `HTN.Syn.TnDesc`);
* `FOND.FProbDesc.Valid` — well-formed descriptions: the deterministic conditions
  (`HTN.Article.TnValid`) plus *every action has at least one effect*.  Finiteness of all
  components is automatic for descriptions.

The languages are, for a class `Y` of problems,

* `FOND.PlanExFM c Y` — fixed methods [CB21], `c ∈ {weak LD, strong LD, weak OD, strong OD}`;
* `FOND.PlanExMP c Y` — method-based policies [CB22], `c ∈ {weak, strong cyclic, strong}`.

The structural classes are those of the deterministic article development, applied to the
*skeleton* `FOND.Problem.toArt` (same methods and initial task network, trivial actions).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-! ## Descriptions -/

/-- **An action description**: name, `Π⁺`, `Π⁻`, effects `(add, del)`. -/
abbrev FActDesc : Type := ℕ × List ℕ × List ℕ × List (List ℕ × List ℕ)

/-- **A problem description**: (actions, methods) and (initial state, initial task network). -/
abbrev FProbDesc : Type := (List FActDesc × List MethodDesc) × (List ℕ × TnDesc)

namespace FActDesc

/-- The name. -/
def name (a : FActDesc) : ℕ := a.1

/-- The effects. -/
def effs (a : FActDesc) : List (List ℕ × List ℕ) := a.2.2.2

/-- The described nondeterministic action. -/
def toAction (a : FActDesc) : Action ℕ where
  pre := {f | f ∈ a.2.1}
  preNeg := {f | f ∈ a.2.2.1}
  effs := {e | ∃ x ∈ a.effs, e = ({f | f ∈ x.1}, {f | f ∈ x.2})}

theorem toAction_wf {a : FActDesc} (h : a.effs ≠ []) : a.toAction.WF := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨_, x, hx, rfl⟩
  · have : a.toAction.effs = (fun x : List ℕ × List ℕ => (({f | f ∈ x.1} : Set ℕ),
        ({f | f ∈ x.2} : Set ℕ))) '' {x | x ∈ a.effs} := by
      ext e; simp [toAction, eq_comm]
    rw [this]
    exact (List.finite_toSet _).image _

end FActDesc

namespace FProbDesc

/-- The action descriptions. -/
def actions (p : FProbDesc) : List FActDesc := p.1.1

/-- The method descriptions. -/
def methods (p : FProbDesc) : List MethodDesc := p.1.2

/-- The initial state. -/
def init (p : FProbDesc) : List ℕ := p.2.1

/-- The initial task network. -/
def tnI (p : FProbDesc) : TnDesc := p.2.2

/-- The action mapping: the first action described under the name (an undeclared name denotes
an action without effects; it does not occur in well-formed descriptions). -/
def δ (p : FProbDesc) (a : ℕ) : Action ℕ :=
  match p.actions.find? (fun x => x.name == a) with
  | some x => x.toAction
  | none => ⟨∅, ∅, ∅⟩

/-- **The problem a description denotes.** -/
def toProblem (p : FProbDesc) : Problem ℕ ℕ ℕ ℕ where
  δ := p.δ
  methods := {m | ∃ e ∈ p.methods, e.toMethod = m}
  init := {f | f ∈ p.init}
  tnI := p.tnI.toTaskNetwork

/-- `a` is a declared action name. -/
def Declared (p : FProbDesc) (a : ℕ) : Prop := a ∈ p.actions.map FActDesc.name

/-- **Well-formed descriptions.** -/
structure Valid (p : FProbDesc) : Prop where
  names_nodup : (p.actions.map FActDesc.name).Nodup
  effs_ne : ∀ a ∈ p.actions, a.effs ≠ []
  tnI : TnValid p.Declared p.tnI
  methods : ∀ m ∈ p.methods, TnValid p.Declared m.2

/-- The test for well-formed descriptions. -/
def validB (p : FProbDesc) : Bool :=
  nodupB (p.actions.map FActDesc.name) &&
  p.actions.all (fun a => !a.effs.isEmpty) &&
  tnValidB (p.actions.map FActDesc.name) p.tnI &&
  p.methods.all fun m => tnValidB (p.actions.map FActDesc.name) m.2

theorem validB_iff (p : FProbDesc) : p.validB = true ↔ p.Valid := by
  simp only [validB, Bool.and_eq_true, List.all_eq_true, nodupB_iff, tnValidB_iff,
    Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · intro h
    exact ⟨⟨⟨h.names_nodup, h.effs_ne⟩, h.tnI⟩, h.methods⟩

instance (p : FProbDesc) : Decidable p.Valid := decidable_of_iff _ (validB_iff p)

theorem pt_validB : PT validB := by
  unfold validB
  have hacts : PT fun p : FProbDesc => p.actions := PT.fst.comp PT.fst
  have hn : PT fun p : FProbDesc => p.actions.map FActDesc.name :=
    PT.map hacts (PT.fst.comp PT.snd)
  refine PT.and (PT.and (PT.and (pt_nodupB hn) ?_)
    (PT.comp₂ pt_tnValidB hn (PT.snd.comp PT.snd))) ?_
  · exact PT.all hacts (PT.not (PT.isEmpty (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))
  · exact PT.all (PT.snd.comp PT.fst)
      (PT.comp₂ pt_tnValidB (hn.comp PT.fst) (PT.snd.comp PT.snd))

theorem δ_of_mem {p : FProbDesc} (hp : p.Valid) {a : FActDesc} (ha : a ∈ p.actions) :
    p.δ a.name = a.toAction := by
  unfold δ
  obtain ⟨x, hx⟩ : ∃ x, p.actions.find? (fun x => x.name == a.name) = some x := by
    cases h : p.actions.find? (fun x => x.name == a.name) with
    | none =>
      exact absurd (List.find?_eq_none.1 h a ha) (by simp)
    | some x => exact ⟨x, rfl⟩
  rw [hx]
  have hxm := List.mem_of_find?_eq_some hx
  have hxn : x.name = a.name := by simpa using List.find?_some hx
  rw [List.inj_on_of_nodup_map hp.names_nodup hxm ha hxn]

/-- In a well-formed description, every action that occurs in the problem is well formed. -/
theorem δ_wf {p : FProbDesc} (hp : p.Valid) {a : ℕ} (ha : p.Declared a) : (p.δ a).WF := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  rw [δ_of_mem hp hx]
  exact FActDesc.toAction_wf (hp.effs_ne x hx)

end FProbDesc

/-! ## Classes -/

/-- The **skeleton** of a FOND problem in the deterministic article model: same methods, initial
state and initial task network; trivial actions and no goal. -/
def Problem.toArt {F A C I : Type} (P : Problem F A C I) : HTN.Article.Problem F A C I where
  δ := fun _ => ⟨∅, ∅, ∅, ∅⟩
  methods := P.methods
  init := P.init
  tnI := P.tnI
  goalPos := ∅
  goalNeg := ∅

/-- A class of FOND problems (over `ℕ`). -/
abbrev FClass : Type := Problem ℕ ℕ ℕ ℕ → Prop

namespace FClass

/-- All problems. -/
def UNRES : FClass := fun _ => True

/-- Primitive problems (`noHTN`). -/
def PRIM : FClass := fun P => P.toArt.IsNoHTN

/-- Acyclic problems. -/
def ACYC : FClass := fun P => P.toArt.IsACYC

/-- Regular problems in the sense of Bercher et al. (all reachable methods regular). -/
def REG : FClass := fun P => P.toArt.IsREG

/-- Regular problems in the sense of [CB21, Def. 3.3] / Erol et al.: additionally the initial
task network is regular. -/
def REGtn : FClass := fun P => P.toArt.IsREG ∧ P.tnI.IsRegular

/-- Tail-recursive problems. -/
def TR : FClass := fun P => P.toArt.IsTailREC

/-- Totally ordered problems (initial task network and reachable methods). -/
def TO : FClass := fun P => P.toArt.IsTO

/-- Intersection of classes. -/
def inter (Y Z : FClass) : FClass := fun P => Y P ∧ Z P

end FClass

/-! ## Solution criteria and languages -/

/-- The four fixed-method criteria of [CB21]. -/
inductive FMCrit
  | weakLD
  | strongLD
  | weakOD
  | strongOD
  deriving DecidableEq

/-- Plan existence under a fixed-method criterion. -/
def FMCrit.Solvable : FMCrit → Problem ℕ ℕ ℕ ℕ → Prop
  | .weakLD, P => P.WeakLDSolvable
  | .strongLD, P => P.StrongLDSolvable
  | .weakOD, P => P.WeakODSolvable
  | .strongOD, P => P.StrongODSolvable

/-- The three method-based criteria of [CB22]. -/
inductive MPCrit
  | weak
  | strongCyclic
  | strong
  deriving DecidableEq

/-- Plan existence under a method-based criterion. -/
def MPCrit.Solvable : MPCrit → Problem ℕ ℕ ℕ ℕ → Prop
  | .weak, P => P.MPWeakSolvable
  | .strongCyclic, P => P.MPStrongCyclicSolvable
  | .strong, P => P.MPStrongSolvable

/-- **`PlanEx` for fixed methods**: codes of well-formed descriptions of problems of the class
`Y` that are solvable under the criterion `c`. -/
def PlanExFM (c : FMCrit) (Y : FClass) : Cx.Language := fun w =>
  ∃ p : FProbDesc, enc p = w ∧ p.Valid ∧ Y p.toProblem ∧ c.Solvable p.toProblem

/-- **`PlanEx` for method-based policies.** -/
def PlanExMP (c : MPCrit) (Y : FClass) : Cx.Language := fun w =>
  ∃ p : FProbDesc, enc p = w ∧ p.Valid ∧ Y p.toProblem ∧ c.Solvable p.toProblem

theorem planExFM_enc_iff {c : FMCrit} {Y : FClass} {p : FProbDesc} :
    PlanExFM c Y (enc p) ↔ p.Valid ∧ Y p.toProblem ∧ c.Solvable p.toProblem := by
  constructor
  · rintro ⟨p', hp', h⟩
    rwa [BEnc.inj hp'] at h
  · exact fun h => ⟨p, rfl, h⟩

theorem planExMP_enc_iff {c : MPCrit} {Y : FClass} {p : FProbDesc} :
    PlanExMP c Y (enc p) ↔ p.Valid ∧ Y p.toProblem ∧ c.Solvable p.toProblem := by
  constructor
  · rintro ⟨p', hp', h⟩
    rwa [BEnc.inj hp'] at h
  · exact fun h => ⟨p, rfl, h⟩

/-- **The code of a FOND description is primitive recursive.** -/
theorem primrec_enc_fprobDesc : Primrec (enc : FProbDesc → List Bool) := PEnc.primrec_enc

end FOND
