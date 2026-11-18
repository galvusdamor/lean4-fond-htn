import HtnComplexity.TMEnc.TMEncFixTrace
import HtnComplexity.TMEnc.Correct
/-!
# Correctness of the repaired encoding, as a property

Split out of `HTN.TMEnc.NonCompilabilityFix`.
-/

namespace HTN

open TM

universe u' v' w' x'

variable {Q Γ : Type} {F' : Type u'} {A' : Type v'} {C' : Type w'} {I' : Type x'}
variable [DecidableEq I']

namespace TMEnc

/-- **Soundness of the repaired encoding**: a solution of the repaired problem witnesses an
accepting run of the machine of at most `K` steps. -/
def EncodingSoundFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  (problemFix N w K).Solvable → N.AcceptsWithin w K

/-- **Completeness of the repaired encoding**: an accepting run of at most `K` steps can be
written out as a solution of the repaired problem. -/
def EncodingCompleteFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  N.AcceptsWithin w K → (problemFix N w K).Solvable

/-- The repaired encodings lie in `TO-tn_I ∩ ACYC`. -/
theorem mem_HTN_AC_TOtnI_fix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    problemFix N w K ∈
      Classes.HTN_AC_TOtnI (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) :=
  ⟨isTO_tnIFix, isAcyclicFix⟩

end TMEnc

/-- **Correctness of the repaired translation**: the repaired problem is solvable exactly when
the machine accepts its input within `2 ^ p(|w|)` steps.  Unlike `HTN.EncodingCorrect`, this
statement is not refuted by the counting arguments of this development; it is still not proved
here and is used only as an explicit hypothesis. -/
def EncodingCorrectFix (N : NTM Q Γ) (p : Polynomial ℕ) : Prop :=
  ∀ w : List Γ, (TMEnc.problemFix N w (2 ^ p.eval w.length)).Solvable ↔ N.AcceptsExp p w

/-- **Simulation correctness of the repaired encoding is soundness plus completeness.** -/
theorem encodingCorrectFix_of_sound_complete {N : NTM Q Γ} {p : Polynomial ℕ}
    (hs : ∀ w : List Γ, TMEnc.EncodingSoundFix N w (2 ^ p.eval w.length))
    (hc : ∀ w : List Γ, TMEnc.EncodingCompleteFix N w (2 ^ p.eval w.length)) :
    EncodingCorrectFix N p := fun w => ⟨hs w, hc w⟩

end HTN
