import HtnComplexity.TMEnc.TMEncoding
import HtnPlanning.Core.Size
/-!
# Correctness of the Turing-machine encoding, as a property

Split out of `HTN.TMEnc.NonCompilability`.
-/

namespace HTN

open TM

universe u' v' w' x'

variable {Q Γ : Type} {F' : Type u'} {A' : Type v'} {C' : Type w'} {I' : Type x'}
variable [DecidableEq I']

/-- The class `ACYC ∩ TO-tn_I` of Theorem 4.3.7: acyclic problems with a totally ordered
initial task network. -/
def Classes.HTN_AC_TOtnI (F : Type) (A : Type) (C : Type) (I : Type) : Set (Problem F A C I) :=
  {P | P.IsTO_tnI ∧ P.IsAcyclic}

/-- The encodings of Theorem 4.3.7 are acyclic and have a totally ordered initial task
network. -/
theorem TMEnc.mem_HTN_AC_TOtnI (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    TMEnc.problem N w K ∈
      Classes.HTN_AC_TOtnI (TMEnc.TMFact Q Γ) (TMEnc.TMAct Q Γ) (TMEnc.TMTask Q Γ) (ℕ × ℕ) :=
  ⟨TMEnc.isTO_tnI N w K, TMEnc.isAcyclic⟩

/-- **Correctness of the translation of Theorem 4.3.7**: the encoded planning problem is
solvable exactly when the machine accepts its input within `2 ^ p(|w|)` steps.

This is the simulation statement of the source (a solution plan is the witness
`W = #w₀#w₁#…#w_K` of an accepting run, and conversely).  It is not proved in this
development; it is used only as an explicit hypothesis.

**Warning.**  For the translation exactly as printed in the source this hypothesis is *false*:
`HTN.TMEnc.not_encodingCorrect` (in `HtnComplexity/TMEnc/TMEncCheck.lean`) shows that the encoded
problem is unsolvable, because the cell counters of the construction answer more synchronisation
requests than the tape issues.  The theorems below are therefore, as they stand, conditional on
a statement that a repaired version of the translation would have to satisfy; see `NOTES.md`. -/
def EncodingCorrect (N : NTM Q Γ) (p : Polynomial ℕ) : Prop :=
  ∀ w : List Γ, (TMEnc.problem N w (2 ^ p.eval w.length)).Solvable ↔ N.AcceptsExp p w

/-- **Polynomial-size deciders.**  The problem class `𝒞` contains, for every input `w` of the
machine `N`, a problem of size polynomial in `|w|` that is solvable exactly when `N` accepts
`w` in exponential time.  This is the planning counterpart of the statement
`EXPTIME ⊆ 𝒞/poly` used in the Karp–Lipton step of the argument. -/
def HasPolySizeDeciders (𝒞 : Set (Problem F' A' C' I')) (N : NTM Q Γ) (p : Polynomial ℕ) :
    Prop :=
  ∃ r : Polynomial ℕ, ∀ w : List Γ, ∃ (D : Domain F' A' C' I') (Q : Instance F' A' C' I'),
    D.size ≤ r.eval w.length ∧ Q.size ≤ r.eval w.length ∧ D.mkProblem Q ∈ 𝒞 ∧
      ((D.mkProblem Q).Solvable ↔ N.AcceptsExp p w)

/-- The problem instance produced by the translation is of size `2`: the initial state consists
of the single fact `q₀`, the goal is empty, and the initial task network is the single task
`sI`. -/
theorem Instance.size_tmEncoding (N : NTM Q Γ) : (TMEnc.instance_ N).size = 2 := by
  classical
  have hinit : ({TMEnc.TMFact.st N.init} : Set (TMEnc.TMFact Q Γ)).ncard = 1 :=
    Set.ncard_singleton _
  have hT : (TMEnc.instance_ N).tnI.T = {(0, 0)} := by
    ext p
    obtain ⟨i, j⟩ := p
    simp only [TMEnc.instance_, TaskNetwork.mem_seq_T, List.length_singleton,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  have hord : (TMEnc.instance_ N).tnI.ordSize = 0 := by
    rw [TaskNetwork.ordSize, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨p, q⟩ hpq
    rw [hT] at hpq
    simp only [Finset.mem_product, Finset.mem_singleton] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    rintro ⟨-, h, -⟩
    simp at h
  have htn : (TMEnc.instance_ N).tnI.size = 1 := by
    rw [TaskNetwork.size, hT, hord, Finset.card_singleton]
  rw [Instance.size, show (TMEnc.instance_ N).init = {TMEnc.TMFact.st N.init} from rfl,
    show (TMEnc.instance_ N).goal = ∅ from rfl, hinit, Set.ncard_empty, htn]

end HTN
