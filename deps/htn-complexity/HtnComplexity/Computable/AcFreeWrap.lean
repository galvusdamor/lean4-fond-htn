import HtnComplexity.Computable.AcFreeNames
import HtnPlanning.Computable.Relevance
/-!
# The vocabulary-free wrapper of a compiled acyclic domain

`HtnComplexity/Computable/AcSmall.lean` compiles a totally ordered source problem into an
acyclic one, but its *instance* translation uses the vocabulary of the source domain.  This file
defines the wrapper that removes that dependence.

The compiled instance writes only facts of its own: the **licences** `fLic u` (for `u` in its
initial state) and the **receipts** `fRes u` (likewise), and it demands the receipts of its goal
facts.  Its initial task network is the chain

    aBoot ; t_I ; tPost

of the boot action, the compiled initial task of the acyclic construction, and the compound task
of the verification phase.  The compiled domain, which knows its vocabulary `V`, provides

* `aBoot` — one action establishing the initial state the acyclic construction expects (`key₀`
  and `¬v^i` for every `v ∈ V` and every copy `i < 5`) and **deleting the receipts of its own
  facts**, so that the receipts of `V` have to be earned again while those of the facts outside
  `V` — which the domain never touches — survive;
* `tPost` — a chain of one **check** task `tChk v` and one **earn** task `tEarn v` per `v ∈ V`.
  A check task has the two methods "`v` is false in copy `0`" and "`v` is true in copy `0` *and*
  licensed", which together say that the state the acyclic construction guessed is contained in
  the initial state of the source; an earn task has the two methods "return the receipt of `v`,
  which requires `v` in copy `2`" and "do nothing".

`HTN.Syn.AcFree.wrapDom` and `HTN.Syn.AcFree.wrapInst` are the two translations.  The wrapper is
generic: it applies to any domain description whose facts, actions and compound task names have
the shape of the numbering of the acyclic construction (`HTN.Syn.AcFree.BaseShaped`).
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

/-! ### The two translations -/

/-- The actions the wrapper adds to the compiled domain. -/
def wrapActs (V : List ℕ) : List ActionDesc :=
  (aBoot, ([], fKey0 :: V.flatMap fun v => (List.range 5).map (fNeg v), V.map fRes)) ::
  (aSkip, ([], [], [])) ::
  V.flatMap fun v =>
    [(aChkN v, ([fNeg v 0], [], [])),
     (aChkP v, ([fPos v 0, fLic v], [], [])),
     (aEarn v, ([fPos v 2], [fRes v], []))]

/-- The body of the verification phase: one check task and one earn task per fact of the
vocabulary. -/
def postBody (V : List ℕ) : List (Bool × ℕ) :=
  (V.map fun v => pTsk (tChk v)) ++ (V.map fun v => pTsk (tEarn v))

/-- The methods the wrapper adds to the compiled domain. -/
def wrapMeths (V : List ℕ) : List MethodDesc :=
  (tPost, gridDesc [postBody V]) ::
  V.flatMap fun v =>
    [(tChk v, gridDesc [[pAct (aChkN v)]]),
     (tChk v, gridDesc [[pAct (aChkP v)]]),
     (tEarn v, gridDesc [[pAct (aEarn v)]]),
     (tEarn v, gridDesc [[pAct aSkip]])]

/-- **The wrapped domain description**: the compiled acyclic domain, together with the boot
action and the verification phase over the vocabulary `V`. -/
def wrapDom (V : List ℕ) (d₀ : DomDesc) : DomDesc :=
  (d₀.actions ++ wrapActs V, d₀.methods ++ wrapMeths V)

/-- **The wrapped instance description**: it mentions only facts of the source instance. -/
def wrapInst (q : InstDesc) : InstDesc :=
  (q.initList.map fLic ++ q.initList.map fRes,
   q.goalList.map fRes ++ [fTask (nC (rootName q))],
   gridDesc [[pAct aBoot, pTsk tTI, pTsk tPost]])

@[simp] lemma wrapDom_actions (V : List ℕ) (d₀ : DomDesc) :
    (wrapDom V d₀).actions = d₀.actions ++ wrapActs V := rfl

@[simp] lemma wrapDom_methods (V : List ℕ) (d₀ : DomDesc) :
    (wrapDom V d₀).methods = d₀.methods ++ wrapMeths V := rfl

@[simp] lemma wrapInst_initList (q : InstDesc) :
    (wrapInst q).initList = q.initList.map fLic ++ q.initList.map fRes := rfl

@[simp] lemma wrapInst_goalList (q : InstDesc) :
    (wrapInst q).goalList = q.goalList.map fRes ++ [fTask (nC (rootName q))] := rfl

@[simp] lemma wrapInst_tnI (q : InstDesc) :
    (wrapInst q).tnI = gridDesc [[pAct aBoot, pTsk tTI, pTsk tPost]] := rfl

/-! ### The shape of the description the wrapper is applied to -/

/-- A label of a method body is *base shaped* when its name is. -/
def GoodLabel : ℕ ⊕ ℕ → Prop
  | Sum.inl a => BaseAct a
  | Sum.inr c => BaseTask c

/-- **The description has the shape of the numbering of the acyclic construction**: its method
heads and the labels of its method bodies are base shaped, and so are all the facts its actions
mention.  This is all the wrapper needs to know about the description it wraps. -/
structure BaseShaped (d₀ : DomDesc) : Prop where
  /-- Every listed action has a base-shaped name. -/
  acts : ∀ e ∈ d₀.actions, BaseAct e.1
  /-- Every method head is base shaped. -/
  heads : ∀ e ∈ d₀.methods, BaseTask e.1
  /-- Every label of a method body is base shaped. -/
  bodies : ∀ e ∈ d₀.methods, ∀ t ∈ e.2.ids, GoodLabel (e.2.label t)
  /-- Every fact the actions mention is base shaped. -/
  facts : ∀ f ∈ d₀.domFacts, BaseFact f

end AcFree

end Syn

end HTN
