import ComplexityTheory.Petri.Rev
/-!
# Refutations of generalised problems

`Refutable bs` is the inductive predicate of **finite decomposition trees** whose leaves have an
infeasible characteristic system.  Each constructor is one decomposition step, with exactly the
side conditions under which the step preserves solvability:

* `noChar`: the characteristic system has no solution;
* `prune`, `split`: restriction to a forward-closed set, split along a backward-closed set;
* `edge`, `inp`, `out`: a variable bounded in all solutions of the characteristic system;
* `dF`, `dB`: replacement of a component by an exact graph (forward / backward).

`Refutable.not_solvable`: refutable generalised problems are unsolvable.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp Classical

variable {ι : Type*}

/-- Conditions (N1)–(N3) of step (d) for a block and a node list. -/
def DCert (b : Block ι) (Ns : List (ℕ × (ι → ℕ∞))) : Prop :=
  (∀ p ∈ Ns, ∀ j, b.comp.lab p.1 j ≠ ⊤ → p.2 j = b.comp.lab p.1 j) ∧
  (∃ p ∈ Ns, p.1 = b.comp.entry ∧ (∀ j, b.inp j = ⊤ → p.2 j = ⊤) ∧
      ∀ j, p.2 j ≠ ⊤ → p.2 j = b.inp j) ∧
  (∀ p ∈ Ns, ∀ e ∈ b.comp.edges, e.1 = p.1 →
      (∀ j, p.2 j ≠ ⊤ → 0 ≤ ((p.2 j).toNat : ℤ) + e.2.1 j) → ∃ p' ∈ Ns, p'.1 = e.2.2 ∧
        ∀ j, p'.2 j ≠ ⊤ → p.2 j ≠ ⊤ ∧ ((p'.2 j).toNat : ℤ) = (p.2 j).toNat + e.2.1 j)

/-- The number of uses of the edge `e₀` recorded by a candidate solution. -/
noncomputable def fib (C : Comp ι) (e₀ : Edge ι) (ψ : ℕ → ℕ) : ℕ :=
  ∑ k ∈ range C.edges.length, if C.edge k = e₀ then ψ k else 0

/-- **Refutation trees.** -/
inductive Refutable : List (Block ι) → Prop
  | noChar {bs : List (Block ι)} : (¬ ∃ ts, CharSol bs ts) → Refutable bs
  | prune {pre post : List (Block ι)} {b : Block ι} (R : List ℕ) :
      b.comp.entry ∈ R → (∀ e ∈ b.comp.edges, e.1 ∈ R → e.2.2 ∈ R) →
      (∀ A ∈ pruneAlts b (· ∈ R), Refutable (pre ++ A ++ post)) → Refutable (pre ++ b :: post)
  | split {pre post : List (Block ι)} {b : Block ι} (S : List ℕ) :
      b.comp.entry ∈ S → (∀ e ∈ b.comp.edges, e.2.2 ∈ S → e.1 ∈ S) →
      (∀ A ∈ splitAlts b (· ∈ S), Refutable (pre ++ A ++ post)) → Refutable (pre ++ b :: post)
  | edge {pre post : List (Block ι)} {b : Block ι} (e₀ : Edge ι) (B : ℕ) :
      e₀ ∈ b.comp.edges →
      (∀ ts, CharSol (pre ++ b :: post) ts → ∀ t ∈ ts[pre.length]?, fib b.comp e₀ t.ψ ≤ B) →
      (∀ A ∈ edgeAlts b e₀ B, Refutable (pre ++ A ++ post)) → Refutable (pre ++ b :: post)
  | inp {pre post : List (Block ι)} {b : Block ι} (j : ι) (B : ℕ) : b.inp j = ⊤ →
      (∀ ts, CharSol (pre ++ b :: post) ts → ∀ t ∈ ts[pre.length]?, t.M₁ j ≤ B) →
      (∀ A ∈ inpAlts b j B, Refutable (pre ++ A ++ post)) → Refutable (pre ++ b :: post)
  | out {pre post : List (Block ι)} {b : Block ι} (j : ι) (B : ℕ) : b.out j = ⊤ →
      (∀ ts, CharSol (pre ++ b :: post) ts → ∀ t ∈ ts[pre.length]?, t.M' j ≤ B) →
      (∀ A ∈ outAlts b j B, Refutable (pre ++ A ++ post)) → Refutable (pre ++ b :: post)
  | dF {pre post : List (Block ι)} {b : Block ι} (Ns : List (ℕ × (ι → ℕ∞))) :
      (∀ j, b.comp.lab b.comp.entry j ≠ ⊤ → b.inp j = b.comp.lab b.comp.entry j) → DCert b Ns →
      (∀ A ∈ dAlts b Ns, Refutable (pre ++ A ++ post)) → Refutable (pre ++ b :: post)
  | dB {pre post : List (Block ι)} {b : Block ι} (Ns : List (ℕ × (ι → ℕ∞))) :
      (∀ j, b.comp.lab b.comp.exit j ≠ ⊤ → b.out j = b.comp.lab b.comp.exit j) →
      DCert b.rev Ns →
      (∀ A ∈ dAltsB b Ns, Refutable (pre ++ A ++ post)) → Refutable (pre ++ b :: post)

/-- The validity of step (d) from a certificate. -/
theorem d_valid' {b : Block ι} {Ns : List (ℕ × (ι → ℕ∞))}
    (hin : ∀ j, b.comp.lab b.comp.entry j ≠ ⊤ → b.inp j = b.comp.lab b.comp.entry j)
    (h : DCert b Ns) (M M' : ι → ℤ) : BlockRun b M M' ↔ ∃ A ∈ dAlts b Ns, ListRun A M M' :=
  d_valid hin h.1 h.2.1 h.2.2 M M'

/-- **Soundness of refutations.** -/
theorem Refutable.not_solvable {bs : List (Block ι)} (h : Refutable bs) : ¬ Solvable bs := by
  induction h with
  | noChar h =>
    intro hs
    obtain ⟨ts, hts, -⟩ := charSol_of_solvable hs
    exact h ⟨ts, hts⟩
  | @prune pre post b R hR hcl _ ih =>
    rw [solvable_replace pre post b _ (prune_valid (R := (· ∈ R)) hR hcl)]
    rintro ⟨A, hA, hs⟩
    exact ih A hA hs
  | @split pre post b S hS hcl _ ih =>
    rw [solvable_replace pre post b _ (split_valid (S := (· ∈ S)) hS hcl)]
    rintro ⟨A, hA, hs⟩
    exact ih A hA hs
  | @edge pre post b e₀ B he hB _ ih =>
    rw [solvable_replace_of_bound pre post b (edgeAlts b e₀ B) (fun t => fib b.comp e₀ t.ψ ≤ B)
      hB (fun t ht hq => edge_local he B t ht hq) (edge_local' he B)]
    rintro ⟨A, hA, hs⟩
    exact ih A hA hs
  | @inp pre post b j B hj hB _ ih =>
    rw [solvable_replace_of_bound pre post b (inpAlts b j B) (fun t => t.M₁ j ≤ B)
      hB (fun t ht hq => inp_local B t ht hq) (inp_local' hj B)]
    rintro ⟨A, hA, hs⟩
    exact ih A hA hs
  | @out pre post b j B hj hB _ ih =>
    rw [solvable_replace_of_bound pre post b (outAlts b j B) (fun t => t.M' j ≤ B)
      hB (fun t ht hq => out_local B t ht hq) (out_local' hj B)]
    rintro ⟨A, hA, hs⟩
    exact ih A hA hs
  | @dF pre post b Ns hin hD _ ih =>
    rw [solvable_replace pre post b _ (d_valid' hin hD)]
    rintro ⟨A, hA, hs⟩
    exact ih A hA hs
  | @dB pre post b Ns hout hD _ ih =>
    rw [solvable_replace pre post b _ (dB_valid (d_valid' (b := b.rev) hout hD))]
    rintro ⟨A, hA, hs⟩
    exact ih A hA hs

end KLM

end Petri

end HTN
