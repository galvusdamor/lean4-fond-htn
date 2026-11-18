import ComplexityTheory.Undec.Sim.Backward
/-!
# A two-stack machine simulating a Turing machine — correctness

`HTN.Undec.Sim.simTSM_halts_iff`: the two-stack machine `simTSM N S q₀` halts on the encoded
input `l` if and only if the `TM0` machine `N`, started in the control state `q₀` on the tape
`Tape.mk₁ l`, halts.  The only hypotheses are that `S` contains `q₀` and is closed under the
transition function of `N` — that is, `S` is a finite set of control states that supports the
run.
-/

namespace HTN

namespace Undec

namespace Sim

open Turing

open scoped Classical

variable {Γ : Type*} [Inhabited Γ] [Fintype Γ] {Λ : Type*} [Inhabited Λ]
variable {N : TM0.Machine Γ Λ} {S : Finset Λ} {q0 : Λ}

/-- **Correctness of the simulation.** -/
theorem simTSM_halts_iff
    (hcl : ∀ {q : Λ} {a : Γ} {q' : Λ} {st : TM0.Stmt Γ}, (q', st) ∈ N q a → q ∈ S → q' ∈ S)
    (hq0 : q0 ∈ S) (l : List Γ) :
    (simTSM N S q0).Halts (encL ([] : List Γ)) (encL l) ↔
      (Turing.eval (TM0.step N) ⟨q0, Tape.mk₁ l⟩).Dom :=
  ⟨dom_of_halts hcl hq0 l, halts_of_dom hcl hq0 l⟩

end Sim

end Undec

end HTN
