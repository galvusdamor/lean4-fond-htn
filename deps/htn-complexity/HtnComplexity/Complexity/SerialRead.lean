import ComplexityTheory.Complexity.CobhamDFA
import HtnComplexity.Complexity.PolyResource
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Reading a description in polynomial time

`HtnComplexity/Complexity/PolyResource.lean` isolates the one algorithmic ingredient the
polynomial-time reading of the rooting schema still owes, `HTN.Syn.ProfileReadable`: the bounded
profile a fixed domain description sees must be readable off the code of an instance description
in polynomial time.  `ComplexityTheory/Complexity/CobhamDFA.lean` supplies the tool such an
algorithm is written with — a finite-state scan of the code is a function of Cobham's class.

This file connects the two:

* `HTN.Syn.polyTimePred_of_dfa` — a predicate on descriptions that a finite-state scan of the
  serialisation computes is decided in polynomial time relative to the serialisation coding
  `HTN.Syn.codingSer`;
* `HTN.Syn.polyTimePred_initList_ne_nil` — the first predicate about descriptions actually
  exhibited in polynomial time: whether the initial state of an instance description is empty.
  The scan is a one-state one: the serialisation begins with the self-delimiting list of the
  initial state, so its very first bit answers the question.

The remaining components of the profile need scans that carry a fixed numeral and a position in
it; the last one — whether every goal fact outside the domain's vocabulary already holds — is
not a finite-state property at all and needs a genuine two-pointer algorithm.  See §23 of
`NOTES.md`.
-/

namespace HTN

namespace Syn

open PTime

/-- **A predicate computed by a finite-state scan of the serialisation is polynomial time.** -/
theorem polyTimePred_of_dfa {σ : Type} [Fintype σ] [DecidableEq σ] (init : σ)
    (step : σ → Bool → σ) (out : σ → Bool) {g : InstDesc → Bool}
    (hg : ∀ q, g q = out ((instSer q).foldl step init)) : PolyTimePred codingSer g :=
  ⟨fun x => [out (x.foldl step init)], polyTimeFun_dfa init step out, fun q => by
    rw [codingSer_code, hg q]⟩

/-- The same, for a state type given as a list of states closed under the transition. -/
theorem polyTimePred_of_dfaList {σ : Type} [DecidableEq σ] (states : List σ) (init : σ)
    (step : σ → Bool → σ) (out : σ → Bool) (hinit : init ∈ states)
    (hstep : ∀ s b, s ∈ states → step s b ∈ states) {g : InstDesc → Bool}
    (hg : ∀ q, g q = out ((instSer q).foldl step init)) : PolyTimePred codingSer g :=
  ⟨fun x => [out (x.foldl step init)], polyTimeFun_dfaFoldl states init step out hinit hstep,
    fun q => by rw [codingSer_code, hg q]⟩

/-! ### An example: is the initial state empty? -/

/-- The scan that remembers the first bit it reads. -/
def firstBitStep (s : Option Bool) (b : Bool) : Option Bool := s.getD b

theorem foldl_firstBitStep_some (b : Bool) : ∀ x : List Bool,
    x.foldl firstBitStep (some b) = some b := by
  intro x
  induction x with
  | nil => rfl
  | cons c x ih => simpa [firstBitStep] using ih

theorem foldl_firstBitStep_cons (b : Bool) (x : List Bool) :
    (b :: x).foldl firstBitStep none = some b := by
  simpa [firstBitStep] using foldl_firstBitStep_some b x

/-- The serialisation begins with a `true` exactly when the initial state is not empty. -/
theorem instSer_head_initList (q : InstDesc) :
    (instSer q).foldl firstBitStep none = some (decide (q.initList ≠ [])) := by
  cases hq : q.initList with
  | nil =>
    have h : instSer q = false :: (serNatList q.goalList ++ tnSer q.tnI) := by
      simp [instSer, hq, serNatList]
    rw [h, foldl_firstBitStep_cons]
    simp
  | cons a l =>
    have h : instSer q
        = true :: (bstr (bitsOfNat a) ++ blist (l.map bitsOfNat)
            ++ (serNatList q.goalList ++ tnSer q.tnI)) := by
      simp [instSer, hq, serNatList, List.append_assoc]
    rw [h, foldl_firstBitStep_cons]
    simp

/-- **Whether the initial state of an instance description is empty is decided in polynomial
time.** -/
theorem polyTimePred_initList_ne_nil :
    PolyTimePred codingSer (fun q => decide (q.initList ≠ [])) :=
  polyTimePred_of_dfa (σ := Option Bool) none firstBitStep (fun s => s == some true)
    (fun q => by rw [instSer_head_initList q]; cases h : decide (q.initList ≠ []) <;> simp)

end Syn

end HTN
