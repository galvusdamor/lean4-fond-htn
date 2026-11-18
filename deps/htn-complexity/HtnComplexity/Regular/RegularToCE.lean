import HtnComplexity.Regular.RegularToStrips
import HtnPlanning.CE.Theory.Lemmas
/-!
# Regular HTN problems compile *linearly* into STRIPS with conditional effects

The draft paper `compilation.tex` states

> **Proposition.**  Regular HTNs are linearly compilable into STRIPS.

with the proof "We provide a linear compilation into STRIPS with conditional effects".

`HtnComplexity/Regular/RegularToStrips.lean` formalises a compilation into the *conditional-effect
free* action model of `HtnPlanning/Core/Classical.lean`: a method is compiled into the macro
action of its body.  That compilation is correct, and it even *shortens* plans, but its size is
only **quadratic** in the size of the source domain, because the precondition and the effects of
an operator are copied into every method body it occurs in.

This file gives the compilation the source paper describes — into STRIPS **with conditional
effects** (the action model of `HtnPlanning/CE/Basic.lean`) — and it is **linear**: the
compiled problem has one action per operator and one action per method, and the size of the
compiled domain is bounded by a fixed multiple of the size of the source domain
(`HtnCompilability/Regular/RegularToCESize.lean`).

## The construction

Let `D` be a totally ordered regular domain: every method `m` has a body `o₁ … oₙ` followed by
at most one compound task `next(m)` (`HTN.Regular.body`).  The compiled problem has the facts

```
state v   (v a fact of the source)      pending c   (c a compound task)
mark m k  (the body of `m` has been executed up to its position `k`)
run a     (the operator `a` is the one that has to be executed next)
done      bot
```

and the actions

* `start m` — applicable when `pending (abstractTask m)` holds; it hands the control over to the
  first position of the body of `m`;
* `op a` (one per operator `a` of the source!) — applicable when `run a` holds and the
  precondition of `a` holds; it applies the effects of `a` *unconditionally*, and it advances
  the position marker by a **conditional effect** `mark m k ▷ (mark m (k+1), run o_{k+1})`, one
  for each occurrence of `a` in a method body.

The position marker of a method is `HTN.RegularCE.posMark`:

```
posMark m k = {mark m k, run oₖ}            if k < |body m|
posMark m k = {pending (next m)} or {done}  if k = |body m|
```

so that the very same conditional effect that advances the marker inside a body also hands the
control back to the next compound task when the body is finished.  That is what makes every
conditional effect of `op a` a *constant size* object: an occurrence of `a` in a method body
costs `O(1)`, and the precondition and the effects of `a` are written down **once**.

## What is proved

* `HTN.RegularCE.ceProblem_solvable_iff` (in `HtnComplexity/Regular/RegularToCECorrect.lean`) — the
  compiled problem is solvable exactly when the regular HTN problem is;
* `HTN.RegularCE.ceProblem_sizeOn_le` (in `HtnCompilability/Regular/RegularToCESize.lean`) — the size
  of the compiled problem is at most a fixed multiple of the size of the source domain;
* the plan-length comparison (`HtnComplexity/Regular/RegularToCECorrect.lean`): the compiled plan
  performs one action per action of the source plan plus one per method application.

This file contains the construction itself and the analysis of a single step.
-/

namespace HTN

universe u v w x

/-- The facts of the STRIPS-with-conditional-effects problem compiled from a regular HTN
domain. -/
inductive CEFact (F : Type u) (A : Type v) (C : Type w) (I : Type x)
  /-- A fact of the source problem. -/
  | state (v : F)
  /-- The compound task `c` still has to be decomposed. -/
  | pending (c : C)
  /-- The body of the method `m` has been executed up to its position `k`. -/
  | mark (m : Method I A C) (k : ℕ)
  /-- The operator `a` is the one that has to be executed next. -/
  | run (a : A)
  /-- The hierarchy has been completely decomposed. -/
  | done
  /-- The unsatisfiable fact, used to disable unusable methods. -/
  | bot

/-- The actions of the compiled problem: one per method and one per operator. -/
inductive CEAct (A : Type v) (C : Type w) (I : Type x)
  /-- Start the execution of the body of the method `m`. -/
  | start (m : Method I A C)
  /-- Execute the operator `a`. -/
  | op (a : A)

namespace RegularCE

open CE

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### The encoding of a state -/

/-- The encoding of a state of the source problem. -/
def encS (s : Set F) : Set (CEFact F A C I) := CEFact.state '' s

@[simp] lemma state_mem_encS {s : Set F} {v : F} :
    (CEFact.state v : CEFact F A C I) ∈ encS s ↔ v ∈ s := by
  simp [encS]

@[simp] lemma pending_notMem_encS {s : Set F} {c : C} :
    (CEFact.pending c : CEFact F A C I) ∉ encS s := by
  simp [encS]

@[simp] lemma mark_notMem_encS {s : Set F} {m : Method I A C} {k : ℕ} :
    (CEFact.mark m k : CEFact F A C I) ∉ encS s := by
  simp [encS]

@[simp] lemma run_notMem_encS {s : Set F} {a : A} :
    (CEFact.run a : CEFact F A C I) ∉ encS s := by
  simp [encS]

@[simp] lemma done_notMem_encS {s : Set F} :
    (CEFact.done : CEFact F A C I) ∉ encS s := by
  simp [encS]

@[simp] lemma bot_notMem_encS {s : Set F} :
    (CEFact.bot : CEFact F A C I) ∉ encS s := by
  simp [encS]

variable [DecidableEq I]

/-! ### The body of a method -/

/-- The operators of the body of a method (the junk value `[]` for a method that is not
chain-shaped). -/
noncomputable def bodyOps (m : Method I A C) : List A := (Regular.body m).1

/-- The compound task a method leaves open (the junk value `none` for a method that is not
chain-shaped). -/
noncomputable def bodyNext (m : Method I A C) : Option C := (Regular.body m).2

lemma bodyOps_eq {m : Method I A C} {os : List A} {next : Option C} (h : m.HasBody os next) :
    bodyOps m = os := by rw [bodyOps, Regular.body_eq h]

lemma bodyNext_eq {m : Method I A C} {os : List A} {next : Option C} (h : m.HasBody os next) :
    bodyNext m = next := by rw [bodyNext, Regular.body_eq h]

/-- A method is *usable* in the compiled problem iff it belongs to the domain and has a body. -/
def Usable (D : Domain F A C I) (m : Method I A C) : Prop :=
  m ∈ D.methods ∧ ∃ p : List A × Option C, m.HasBody p.1 p.2

lemma hasBody_of_usable {D : Domain F A C I} {m : Method I A C} (h : Usable D m) :
    m.HasBody (bodyOps m) (bodyNext m) := Regular.hasBody_body h.2

/-! ### The markers -/

/-- The marker that hands the control back after the body of `m` has been executed: the
compound task `m` leaves open, or `done`. -/
noncomputable def tailMark (F : Type u) (m : Method I A C) : Set (CEFact F A C I) :=
  match bodyNext m with
  | none => {CEFact.done}
  | some c' => {CEFact.pending c'}

/-- The position marker of the method `m` at the position `k` of its body: inside the body, the
pair `mark m k, run oₖ`; at its end, the tail marker. -/
noncomputable def posMark (m : Method I A C) (k : ℕ) : Set (CEFact F A C I) :=
  match (bodyOps m)[k]? with
  | some a => {CEFact.mark m k, CEFact.run a}
  | none => tailMark F m

lemma posMark_of_getElem {m : Method I A C} {k : ℕ} {a : A} (h : (bodyOps m)[k]? = some a) :
    posMark (F := F) m k = {CEFact.mark m k, CEFact.run a} := by
  rw [posMark, h]

lemma posMark_of_getElem_none {m : Method I A C} {k : ℕ} (h : (bodyOps m)[k]? = none) :
    posMark (F := F) m k = tailMark F m := by
  rw [posMark, h]

lemma posMark_length (m : Method I A C) :
    posMark (F := F) m (bodyOps m).length = tailMark F m :=
  posMark_of_getElem_none (by simp)

/-- The tail marker contains no `state`, `mark` or `run` fact. -/
lemma tailMark_cases {m : Method I A C} {f : CEFact F A C I} (h : f ∈ tailMark F m) :
    (∃ c, f = CEFact.pending c) ∨ f = CEFact.done := by
  rw [tailMark] at h
  cases hb : bodyNext m with
  | none => rw [hb] at h; simp at h; exact Or.inr h
  | some c' => rw [hb] at h; simp at h; exact Or.inl ⟨c', h⟩

@[simp] lemma state_notMem_tailMark {m : Method I A C} {v : F} :
    CEFact.state v ∉ tailMark F m := by
  intro h
  rcases tailMark_cases h with ⟨c, hc⟩ | hc <;> simp at hc

@[simp] lemma run_notMem_tailMark {m : Method I A C} {a : A} :
    (CEFact.run a : CEFact F A C I) ∉ tailMark F m := by
  intro h
  rcases tailMark_cases h with ⟨c, hc⟩ | hc <;> simp at hc

@[simp] lemma mark_notMem_tailMark {m m' : Method I A C} {k : ℕ} :
    (CEFact.mark m' k : CEFact F A C I) ∉ tailMark F m := by
  intro h
  rcases tailMark_cases h with ⟨c, hc⟩ | hc <;> simp at hc

@[simp] lemma state_notMem_posMark {m : Method I A C} {k : ℕ} {v : F} :
    CEFact.state v ∉ posMark (F := F) m k := by
  rw [posMark]
  cases h : (bodyOps m)[k]? with
  | none => simp
  | some a => simp

/-! ### The conditional effects -/

/-- The conditional effect of the occurrence of an operator at the position `k` of the body of
the method `m`: when the marker of that position is set, advance it. -/
noncomputable def occEff (m : Method I A C) (k : ℕ) : CEff (CEFact F A C I) where
  cond := ⟨{CEFact.mark m k}, ∅⟩
  eff := ⟨posMark m (k + 1), posMark m k \ posMark m (k + 1)⟩

open scoped Classical in
/-- The positions of the body of the method `m` that carry the operator `a`. -/
noncomputable def occPos (m : Method I A C) (a : A) : List ℕ :=
  (List.range (bodyOps m).length).filter fun k => (bodyOps m)[k]? = some a

open scoped Classical in
/-- The conditional effects of the action of the operator `a`: one per occurrence of `a` in the
body of a method of the (finite) method set `ms`.

The occurrences inside one method body are listed in **decreasing** order of the position: the
effect of the position `k` writes the marker `mark m (k+1)` that the effect of the position
`k + 1` reads, so this is the interference-free order that the compilation `τ^AP_SP` of
`HtnCompilability/CE/TauApSp/TauApSp.lean` needs (`HTN.RegularCE.interfree_opAction`).  The order is
irrelevant for the semantics (`HTN.CE.Action.succ_congr_perm`). -/
noncomputable def occEffs (ms : Finset (Method I A C)) (a : A) : List (CEff (CEFact F A C I)) :=
  ms.toList.flatMap fun m => ((occPos m a).reverse.map (occEff m))

lemma mem_occPos {m : Method I A C} {a : A} {k : ℕ} :
    k ∈ occPos m a ↔ (bodyOps m)[k]? = some a := by
  classical
  simp only [occPos, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)

lemma mem_occEffs {ms : Finset (Method I A C)} {a : A} {e : CEff (CEFact F A C I)} :
    e ∈ occEffs ms a ↔
      ∃ m ∈ ms, ∃ k, (bodyOps m)[k]? = some a ∧ e = occEff m k := by
  simp only [occEffs, List.mem_flatMap, List.mem_map, List.mem_reverse, Finset.mem_toList,
    mem_occPos]
  constructor
  · rintro ⟨m, hm, k, hk, he⟩
    exact ⟨m, hm, k, hk, he.symm⟩
  · rintro ⟨m, hm, k, hk, rfl⟩
    exact ⟨m, hm, k, hk, rfl⟩

/-! ### The compiled action model -/

/-- The action of a method: it consumes the `pending` fact of the task it decomposes and sets
the marker of the first position of its body.  A method that is not usable is disabled by the
unsatisfiable fact `bot`. -/
noncomputable def startAction (D : Domain F A C I) (m : Method I A C) :
    Action (CEFact F A C I) where
  pre := ⟨{CEFact.pending m.abstractTask} ∪ {f | f = CEFact.bot ∧ ¬ Usable D m}, ∅⟩
  post := [⟨∅, ⟨posMark m 0, {CEFact.pending m.abstractTask} \ posMark m 0⟩⟩]

/-- The action of an operator: its own precondition and effects, guarded by `run a`, together
with one conditional effect per occurrence of `a` in a method body. -/
noncomputable def opAction (D : Domain F A C I) (ms : Finset (Method I A C)) (a : A) :
    Action (CEFact F A C I) where
  pre := ⟨encS (D.prec a) ∪ {CEFact.run a}, ∅⟩
  post := ⟨∅, ⟨encS (D.add a), encS (D.del a) \ encS (D.add a)⟩⟩ :: occEffs ms a

/-- The action model of the compiled problem. -/
noncomputable def actModel (D : Domain F A C I) (ms : Finset (Method I A C)) :
    CEAct A C I → Action (CEFact F A C I)
  | CEAct.start m => startAction D m
  | CEAct.op a => opAction D ms a

/-- **The compiled STRIPS-with-conditional-effects problem.** -/
noncomputable def ceProblem (D : Domain F A C I) (ms : Finset (Method I A C))
    (Q : Instance F A C I) : CE.Problem (CEFact F A C I) (CEAct A C I) where
  act := actModel D ms
  init := encS Q.init ∪
    {f | ∃ c : C, (∃ t : I, Q.tnI.T = {t} ∧ Q.tnI.α t = Sum.inr c) ∧ f = CEFact.pending c}
  goal := ⟨encS Q.goal ∪ {CEFact.done}, ∅⟩

end RegularCE

end HTN
