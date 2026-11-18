import HtnComplexity.Guard.Static
import HtnComplexity.Guard.Taint
/-!
# The re-split theorem

A construction that decides a language by a planning problem is usually written with the input
word inside the **domain**: the methods that write the word onto the simulated tape mention its
letters.  A *hardness family* in the sense of `HTN.Syn.Coded.HardFamilyPT` needs the opposite
split — one domain per input **length**, the word carried by the **instance** — because the
Karp–Lipton argument reads the compiled domain as advice, which may depend on the length only.

Re-splitting such a construction means:

* replacing, at each position of the input, the single method that writes *the* letter by one
  method **per letter of the alphabet** — this is the family domain `Dfam`, which no longer
  mentions the word;
* letting the instance carry a set `Gw` of *static* facts saying which letter belongs at which
  position, and guarding the letter-writing actions with them
  (`HtnComplexity/Guard/Static.lean`).

The theorem of this file says that the re-split problem is equivalent to the original one.  Its
two halves are exactly the two tools:

* the guards turn executability of a plan of `Dfam` into executability of a plan of `Dfam` whose
  actions are all admitted by `Gw` (`HTN.Guard.solvable_withGuards_iff`);
* a plan without forbidden actions never applies a method outside the word's own domain `Dspec`
  (`HTN.Taint.netYield_of_clean`), and conversely every plan of `Dspec` is admitted
  (a hypothesis, to be checked for the construction at hand).

## Main result

* `HTN.Guard.solvable_resplit_iff` — the guarded problem over the family domain is solvable
  exactly when the original problem over the word's domain is.
-/

namespace HTN

namespace Guard

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

open Taint

/-- **The re-split theorem.**  Let `Dfam` be a domain that offers, at each choice point, one
method per letter, and let `Dspec ⊆ Dfam` be the sub-domain of the methods that write the word
`Gw` describes.  Assume

* the two domains have the same actions (`hact`) — only the methods differ;
* the guard facts are static for the family domain (`hstat`), the instance's initial state and
  goal do not mention them (`hinit`, `hgoal`), and `Gw` consists of guard facts (`hGw`);
* every method of `Dfam` that is not one of `Dspec` inserts a forbidden action — one whose guard
  `Gw` does not grant — or a *tainted* task, from which a forbidden action can no longer be
  avoided (`hbad`, `htaint`);
* every plan of `Dspec` only uses actions that `Gw` grants (`hgranted`).

Then the re-split problem — the family domain, guarded, with the word in the initial state — is
solvable exactly when the original problem for that word is.  The correctness proof of the
original construction is thereby inherited verbatim. -/
theorem solvable_resplit_iff {Dfam Dspec : Domain F A C I} {Q : Instance F A C I}
    {G Gw : Set F} {g : A → Set F} {Taint : C → Prop}
    (hact : Dspec.toActionModel = Dfam.toActionModel)
    (hsub : Dspec.methods ⊆ Dfam.methods)
    (hstat : StaticGuards Dfam.toActionModel (Dfam.mkProblem Q).UsedAction G g)
    (hGw : Gw ⊆ G) (hinit : ∀ f ∈ Q.init, f ∉ G) (hgoal : ∀ f ∈ Q.goal, f ∉ G)
    (htaint : Taintable Dfam.methods (fun a => ¬ g a ⊆ Gw) Taint)
    (hbad : ∀ m ∈ Dfam.methods, m ∉ Dspec.methods → ∃ t ∈ m.subtasks.T,
      (∃ a, m.subtasks.α t = Sum.inl a ∧ ¬ g a ⊆ Gw) ∨
        (∃ c, m.subtasks.α t = Sum.inr c ∧ Taint c))
    (hgranted : ∀ as : List A, Dspec.NetYield Q.tnI as → ∀ a ∈ as, g a ⊆ Gw) :
    (guardedProblem (Dfam.mkProblem Q) g Gw).Solvable ↔ (Dspec.mkProblem Q).Solvable := by
  have hsame : (Dspec.mkProblem Q).toActionModel = (Dfam.mkProblem Q).toActionModel := hact
  rw [solvable_withGuards_iff hstat hGw hinit hgoal, Problem.solvable_iff_netYield]
  constructor
  · rintro ⟨as, hy, happ, hg, hgs⟩
    refine ⟨as, ?_, ?_, ?_⟩
    · refine netYield_of_clean (D := Dfam) (D' := Dspec) (BadAct := fun a => ¬ g a ⊆ Gw)
        (Taint := Taint) htaint hbad hy ?_
      intro a ha
      exact not_not_intro (hgs a ha)
    · rw [show (Dspec.mkProblem Q).SeqApplicable as (Dspec.mkProblem Q).init
          = (Dfam.mkProblem Q).SeqApplicable as (Dfam.mkProblem Q).init from by rw [hsame]; rfl]
      exact happ
    · rw [show (Dspec.mkProblem Q).GoalState
            ((Dspec.mkProblem Q).transitionSeq as (Dspec.mkProblem Q).init)
          = (Dfam.mkProblem Q).GoalState
            ((Dfam.mkProblem Q).transitionSeq as (Dfam.mkProblem Q).init) from by
        rw [hsame]; rfl]
      exact hg
  · rintro ⟨as, hy, happ, hg⟩
    have hyfam : Dfam.NetYield Q.tnI as := netYield_mono hsub hy
    refine ⟨as, hyfam, ?_, ?_, hgranted as hy⟩
    · rw [show (Dfam.mkProblem Q).SeqApplicable as (Dfam.mkProblem Q).init
          = (Dspec.mkProblem Q).SeqApplicable as (Dspec.mkProblem Q).init from by
        rw [hsame]; rfl]
      exact happ
    · rw [show (Dfam.mkProblem Q).GoalState
            ((Dfam.mkProblem Q).transitionSeq as (Dfam.mkProblem Q).init)
          = (Dspec.mkProblem Q).GoalState
            ((Dspec.mkProblem Q).transitionSeq as (Dspec.mkProblem Q).init) from by
        rw [hsame]; rfl]
      exact hg

end Guard

end HTN
