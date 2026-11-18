import Mathlib

/-!
# `n ↦ 2 ^ n` is primitive recursive

Split out of `HTN.Computable.AcNumPrimrec`.
-/

namespace HTN

namespace Syn

namespace Ac

open Primrec

theorem primrec_two_pow : Primrec (fun n : ℕ => 2 ^ n) := by
  have hstep : Primrec₂ (fun (_ : ℕ) (p : ℕ × ℕ) => 2 * p.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)
  have h := (Primrec.nat_rec (f := fun _ : ℕ => 1) (Primrec.const 1) hstep).comp
    Primrec.id Primrec.id
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ]; simp [← ih]; ring

end Ac

end Syn

end HTN
