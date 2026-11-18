import ComplexityTheory.Compile.Gadget
import ComplexityTheory.Complexity.Cobham
/-!
# Uniform circuit families for the functions of Cobham's class

This file states what the source bridge needs of Cobham's class: **every function of the class
is computed, on arguments of a bounded length, by a circuit of polynomial size, and the circuit
is produced by an algorithm from the bound**.  That is one half of Cobham's theorem, in the
`P ⊆ P/poly` reading, with the uniformity that the hardness family of
`HtnComplexity/Complexity/RecMemUniform.lean` asks for (`Primrec` in the bound).

The bundle is `HTN.Compile.CircFam f k`: a circuit family `C` for the arity `k`, a polynomial
output bound `B`, and a polynomial dominating the size of the circuits.  The arguments come in
on the `2 * n * k` input wires as the cell encoding `HTN.Compile.encArgs k n`, and the
`2 * B.eval n` output wires carry `HTN.Compile.encStr (B.eval n)` of the value.

The construction is in `ComplexityTheory/Compile/CobCirc.lean`.
-/

namespace HTN

namespace Compile

open PTime

/-! ### Evaluating a polynomial is primitive recursive -/

theorem primrec_pow (e : ℕ) : Primrec fun n : ℕ => n ^ e := by
  induction e with
  | zero => simpa using Primrec.const 1
  | succ e ih =>
      have h : Primrec fun n : ℕ => n ^ e * n := Primrec.nat_mul.comp ih Primrec.id
      exact h.of_eq fun n => by ring

theorem primrec_polyList (l : List (ℕ × ℕ)) :
    Primrec fun n : ℕ => (l.map fun q => q.1 * n ^ q.2).sum := by
  induction l with
  | nil => simpa using Primrec.const 0
  | cons q l ih =>
      have h : Primrec fun n : ℕ => q.1 * n ^ q.2 :=
        Primrec.nat_mul.comp (Primrec.const q.1) (primrec_pow q.2)
      simpa using Primrec.nat_add.comp h ih

theorem sum_range_eq_listSum (m : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range m, f i = ((List.range m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, List.range_succ]; simp

/-- **Evaluating a fixed polynomial is primitive recursive.** -/
theorem primrec_poly_eval (p : Polynomial ℕ) : Primrec fun n : ℕ => p.eval n := by
  have hl := primrec_polyList ((List.range (p.natDegree + 1)).map fun i => (p.coeff i, i))
  refine hl.of_eq fun n => ?_
  rw [Polynomial.eval_eq_sum_range, sum_range_eq_listSum, List.map_map]
  rfl

/-! ### Uniform circuit families -/

/-- **A uniform circuit family for a function of Cobham's class at the arity `k`.**  The circuit
`C n` takes the cell encoding of `k` arguments of length at most `n` and outputs the cell
encoding of the value at the bound `B.eval n`; its size is dominated by the polynomial `bnd`,
and the circuits are produced by an algorithm from `n`. -/
structure CircFam (f : Fn) (k : ℕ) where
  /-- The circuit for the arguments of length at most `n`. -/
  C : ℕ → Circ
  /-- The polynomial bounding the length of the value. -/
  B : Polynomial ℕ
  /-- The polynomial bounding the size of the circuits. -/
  bnd : Polynomial ℕ
  /-- The circuit reads the cell encoding of `k` arguments of `n` cells each. -/
  nin_eq : ∀ n, (C n).nin = 2 * n * k
  /-- The circuits are produced by an algorithm. -/
  primC : Primrec C
  /-- The circuits are of polynomial size. -/
  size_le : ∀ n, (C n).size ≤ bnd.eval n
  /-- Every output wire is a wire the circuit has: an input or a gate.  This is what makes a
  circuit safe to place inside a larger one, whose further gates would otherwise give a meaning
  to an output index that reads `false` on its own. -/
  out_lt : ∀ n, ∀ j ∈ (C n).out, j < (C n).nin + (C n).gates.length
  /-- The value fits into the bound. -/
  len_le : ∀ (n : ℕ) (args : Args), args.length = k → (∀ a ∈ args, a.length ≤ n) →
      (f args).length ≤ B.eval n
  /-- **The circuit computes the function.** -/
  correct : ∀ (n : ℕ) (args : Args), args.length = k → (∀ a ∈ args, a.length ≤ n) →
      (C n).eval (encArgs k n args) = encStr (B.eval n) (f args)

namespace CircFam

variable {f : Fn} {k : ℕ}

/-- The number of output wires. -/
theorem out_length (F : CircFam f k) (n : ℕ) : (F.C n).out.length = 2 * F.B.eval n := by
  have h := F.correct n (List.replicate k []) (by simp) (by
    intro a ha
    rw [List.eq_of_mem_replicate ha]
    simp)
  have h2 := congrArg List.length h
  rwa [Circ.eval, List.length_map, length_encStr] at h2

end CircFam

end Compile

end HTN
