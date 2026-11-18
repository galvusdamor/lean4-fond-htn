import Mathlib

/-!
# The computable functions are countable

A diagonal argument against a *uniform* half of a construction needs to run through all the
candidates for that half.  For the instance translation of a polynomial-advice decider the
candidates are the computable functions between two codeable types, and there are countably
many of them:

`HTN.exists_enum_computable` — for codeable `α` and `β` with `β` inhabited there is a sequence
`enum : ℕ → (α → β)` that contains every computable function `α → β`.

The sequence itself is of course not computable, and nothing here claims it is: it enumerates
the codes of the partial recursive functions and reads off the total ones.
-/

namespace HTN

open Classical in
/-- The function the code `e` computes, read off the enumeration of the partial recursive
functions; the default value stands for a computation that does not return. -/
noncomputable def enumComp {α β : Type} [Primcodable α] [Primcodable β] [Inhabited β]
    (e : ℕ) (a : α) : β :=
  let c : Nat.Partrec.Code :=
    (Encodable.decode (α := Nat.Partrec.Code) e).getD Nat.Partrec.Code.zero
  let r : Part ℕ := c.eval (Encodable.encode a)
  if h : r.Dom then (Encodable.decode (α := β) (r.get h)).getD default else default

/-- **A sequence containing every computable function** between two codeable types. -/
theorem exists_enum_computable {α β : Type} [Primcodable α] [Primcodable β] [Inhabited β] :
    ∃ enum : ℕ → (α → β), ∀ f : α → β, Computable f → ∃ e, enum e = f := by
  classical
  refine ⟨enumComp, fun f hf => ?_⟩
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  refine ⟨Encodable.encode c, ?_⟩
  funext a
  have hval : c.eval (Encodable.encode a) = Part.some (Encodable.encode (f a)) := by
    rw [hc]
    simp
  simp only [enumComp, Encodable.encodek, Option.getD_some, hval]
  simp

end HTN
