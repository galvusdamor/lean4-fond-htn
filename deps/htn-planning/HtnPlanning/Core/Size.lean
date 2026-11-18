import HtnPlanning.Core.Classes
import HtnPlanning.Basic
/-!
# Domains, problem instances and size measures

The domain part and the instance part of a planning problem, and the size `‖·‖` of the objects
of HTN planning.
-/

namespace HTN

universe u v w x

/-! ### Domains and problem instances -/

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- The domain part of a planning problem. -/
def Problem.domain (P : Problem F A C I) : Domain F A C I where
  toActionModel := P.toActionModel
  methods := P.methods

/-- The problem part of a planning problem. -/
def Problem.instance (P : Problem F A C I) : Instance F A C I where
  init := P.init
  goal := P.goal
  tnI := P.tnI

@[simp] lemma Problem.mkProblem_domain_instance (P : Problem F A C I) :
    P.domain.mkProblem P.instance = P := rfl

@[simp] lemma Domain.mkProblem_domain (D : Domain F A C I) (Q : Instance F A C I) :
    (D.mkProblem Q).domain = D := rfl

@[simp] lemma Domain.mkProblem_instance (D : Domain F A C I) (Q : Instance F A C I) :
    (D.mkProblem Q).instance = Q := rfl

/-! ### Size measures

The size `‖·‖` of a task network, a method, a domain and a problem instance.  Sizes are
measured in the natural way: a task network costs one unit per task id and one unit per
ordering constraint, an action costs one unit plus one unit per fact in its precondition, add
and delete list, and a domain costs the size of its signature plus the sizes of its actions
and methods. -/

/-- The size of a classical (STRIPS) planning domain: the size of the signature (`|V|`) plus
the sizes of all actions. -/
noncomputable def ActionModel.size (δ : ActionModel F A) : ℕ :=
  Nat.card F + ∑ᶠ a : A, δ.actionSize a

/-- The number of ordering constraints of a task network is at most quadratic in its number of
task ids. -/
lemma TaskNetwork.ordSize_le (tn : TaskNetwork I A C) : tn.ordSize ≤ tn.T.card * tn.T.card := by
  classical
  calc tn.ordSize ≤ (tn.T ×ˢ tn.T).card := Finset.card_filter_le _ _
    _ = tn.T.card * tn.T.card := Finset.card_product _ _

lemma TaskNetwork.size_le (tn : TaskNetwork I A C) :
    tn.size ≤ tn.T.card + tn.T.card * tn.T.card :=
  Nat.add_le_add_left tn.ordSize_le _

end HTN
