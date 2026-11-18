import HtnPlanning.Article.Classes
/-!
# Finite descriptions of the article's planning problems

The plan-existence problems of Def. 4.1 take planning problems as input, so a problem has to be
written down.  This file fixes the descriptions; their bit codes and the languages `PlanEx` are in
`HtnComplexity/Article/PlanEx.lean`.

* `HTN.Article.ActDesc` — an action: its name and the lists `prec⁺`, `prec⁻`, `eff⁺`, `eff⁻`;
* `HTN.Article.ProbDesc` — a problem: the actions and the methods (the domain), and the initial
  state, the initial task network and the goal `(g⁺, g⁻)`.  Task networks and methods are
  described as elsewhere (`HTN.Syn.TnDesc`, `HTN.Syn.MethodDesc`): a list of ids, a list of
  ordering pairs and a list of labels;
* `HTN.Article.ProbDesc.toProblem` — the problem a description denotes;
* `HTN.Article.ProbDesc.Valid` — **well-formed descriptions**: the action names are distinct; in
  every task network the ids are distinct, the ordering pairs relate listed ids and form a
  *strict partial order* (irreflexive and transitive, as in Def. 2.1 — the relation `≺` itself
  is listed, not merely a generating set), every id has exactly one label, and every primitive
  label names a declared action.

For a well-formed description the listed pairs are exactly the order of the denoted task network
(`HTN.Article.TnValid.ordOf_iff`).
-/

namespace HTN

namespace Article

open Syn

/-- **An action description**: the name, `prec⁺`, `prec⁻`, `eff⁺`, `eff⁻`. -/
abbrev ActDesc : Type := ℕ × List ℕ × List ℕ × List ℕ × List ℕ

/-- **A domain description**: actions and methods. -/
abbrev DomDescA : Type := List ActDesc × List MethodDesc

/-- **An instance description**: the initial state, the initial task network, `g⁺` and `g⁻`. -/
abbrev InstDescA : Type := List ℕ × TnDesc × List ℕ × List ℕ

/-- **A problem description**: a domain and an instance description. -/
abbrev ProbDesc : Type := DomDescA × InstDescA

namespace ActDesc

/-- The name of an action description. -/
def name (a : ActDesc) : ℕ := a.1

/-- The described action. -/
def toAction (a : ActDesc) : Action ℕ where
  pre := {f | f ∈ a.2.1}
  preNeg := {f | f ∈ a.2.2.1}
  add := {f | f ∈ a.2.2.2.1}
  del := {f | f ∈ a.2.2.2.2}

end ActDesc

namespace ProbDesc

/-- The action descriptions. -/
def actions (p : ProbDesc) : List ActDesc := p.1.1

/-- The method descriptions. -/
def methods (p : ProbDesc) : List MethodDesc := p.1.2

/-- The initial state. -/
def init (p : ProbDesc) : List ℕ := p.2.1

/-- The initial task network. -/
def tnI (p : ProbDesc) : TnDesc := p.2.2.1

/-- The positive goal. -/
def goalPos (p : ProbDesc) : List ℕ := p.2.2.2.1

/-- The negative goal. -/
def goalNeg (p : ProbDesc) : List ℕ := p.2.2.2.2

/-- The task name mapping `δ`: the first action described under the name; an undeclared name
denotes the empty action (it never occurs in a well-formed description). -/
def δ (p : ProbDesc) (a : ℕ) : Action ℕ :=
  match p.actions.find? (fun x => x.name == a) with
  | some x => x.toAction
  | none => ⟨∅, ∅, ∅, ∅⟩

/-- **The problem a description denotes.** -/
def toProblem (p : ProbDesc) : Problem ℕ ℕ ℕ ℕ where
  δ := p.δ
  methods := {m | ∃ e ∈ p.methods, e.toMethod = m}
  init := {f | f ∈ p.init}
  tnI := p.tnI.toTaskNetwork
  goalPos := {f | f ∈ p.goalPos}
  goalNeg := {f | f ∈ p.goalNeg}

end ProbDesc

/-- **A well-formed task network description** (Def. 2.1): distinct ids, the listed pairs form a
strict partial order on the listed ids, every id has exactly one label, and every primitive
label satisfies `prim`. -/
structure TnValid (prim : ℕ → Prop) (t : TnDesc) : Prop where
  nodup : t.ids.Nodup
  ord_mem : ∀ q ∈ t.ordList, q.1 ∈ t.ids ∧ q.2 ∈ t.ids
  irrefl : ∀ a, (a, a) ∉ t.ordList
  trans : ∀ a b c, (a, b) ∈ t.ordList → (b, c) ∈ t.ordList → (a, c) ∈ t.ordList
  lbl_perm : (t.lbl.map Prod.fst).Perm t.ids
  prim_ok : ∀ q ∈ t.lbl, q.2.1 = false → prim q.2.2

namespace ProbDesc

/-- `a` is a declared action name. -/
def Declared (p : ProbDesc) (a : ℕ) : Prop := a ∈ p.actions.map ActDesc.name

/-- **Well-formed problem descriptions.** -/
structure Valid (p : ProbDesc) : Prop where
  names_nodup : (p.actions.map ActDesc.name).Nodup
  tnI : TnValid p.Declared p.tnI
  methods : ∀ m ∈ p.methods, TnValid p.Declared m.2

end ProbDesc

namespace TnValid

variable {prim : ℕ → Prop} {t : TnDesc}

theorem transGen_iff (h : TnValid prim t) {a b : ℕ} :
    Relation.TransGen t.listRel a b ↔ (a, b) ∈ t.ordList := by
  constructor
  · intro hab
    induction hab with
    | single hab => exact hab
    | tail _ hbc ih => exact h.trans _ _ _ ih hbc
  · exact fun hab => Relation.TransGen.single hab

/-- **For a well-formed description the listed pairs are the order.** -/
theorem ordOf_iff (h : TnValid prim t) {a b : ℕ} : t.ordOf a b ↔ (a, b) ∈ t.ordList := by
  unfold TnDesc.ordOf TnDesc.preOrd
  rw [h.transGen_iff, h.transGen_iff]
  constructor
  · exact fun hab => hab.2.2.1
  · intro hab
    exact ⟨(h.ord_mem _ hab).1, (h.ord_mem _ hab).2, hab,
      fun hba => h.irrefl a (h.trans _ _ _ hab hba)⟩

end TnValid

end Article

end HTN
