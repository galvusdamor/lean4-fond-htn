import HtnPlanning.Core.DecompCommute
import HtnPlanning.Core.SolutionIso
/-!
# Unrolling every hole but one

Decomposition steps applied to different tasks commute (`HTN.DecomposesToN.pull_out`).  Hence a
decomposition sequence that ends in a primitive network can be reordered so that every compound
task *except a chosen one* `x₀` is decomposed first, down to primitive tasks, while `x₀` is not
touched at all (`HTN.DecomposesToN.unroll_except`).

For problems whose methods have at most one compound task this is the *isolation statement* of
`htn-complexity/HD2_LU.md` (§6.6): after unrolling all other holes, the problem that remains
starts from a network whose only compound task is `x₀`, i.e. it is a one-hole-digging problem
(`HTN.Problem.exists_unroll_except`), and Dekker and Behnke's Lemma 6 applies to it.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

section Unroll

variable [DecidableEq I] [Infinite I] {M : Set (Method I A C)}

/-- **Unroll everything except `x₀`.**  If `tn` decomposes in `n` steps into a primitive network,
then it decomposes into a network `tn₁` in which `x₀` is still present, with its label, and is the
only compound task; and `tn₁` decomposes further (in some number of steps) into a network
isomorphic to the original result. -/
theorem DecomposesToN.unroll_except {x₀ : I} : ∀ (n : ℕ) {tn tnStar : TaskNetwork I A C},
    DecomposesToN M n tn tnStar → tn.WF → tnStar.IsPrimitive → x₀ ∈ tn.T →
    ∃ (tn₁ tnStar' : TaskNetwork I A C) (k : ℕ), DecomposesTo M tn tn₁ ∧ tn₁.WF ∧
      x₀ ∈ tn₁.T ∧ tn₁.α x₀ = tn.α x₀ ∧ (∀ t ∈ tn₁.T, tn₁.IsAbstractId t → t = x₀) ∧
      DecomposesToN M k tn₁ tnStar' ∧ tnStar.Iso tnStar' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro tn tnStar h hwf hprim hx₀
  by_cases hall : ∀ t ∈ tn.T, tn.IsAbstractId t → t = x₀
  · exact ⟨tn, tnStar, n, Relation.ReflTransGen.refl, hwf, hx₀, rfl, hall, h,
      TaskNetwork.Iso.refl _⟩
  push_neg at hall
  obtain ⟨y, hy, ⟨c, hc⟩, hyx⟩ := hall
  -- decompose `y` first
  have hnot : y ∈ tnStar.T → ¬ tnStar.IsAbstractId y := by
    rintro hyS ⟨c', hc'⟩
    obtain ⟨a, ha⟩ := hprim y hyS
    rw [ha] at hc'
    cases hc'
  obtain ⟨m, tn', tnStar'', k, hk, hstep, hrest, hiso⟩ := h.pull_out hwf hy hc hnot
  have hwf' : tn'.WF := hstep.wf hwf
  obtain ⟨hmM, hyT, hαy, u, hu, huiso, hdisj, rfl⟩ := hstep
  have hxu : x₀ ∉ u.T := Finset.disjoint_left.1 hdisj hx₀
  have hx₀' : x₀ ∈ (decomposeWith tn y u).T := mem_decomposeWith_T.2 (Or.inl ⟨hx₀, hyx.symm⟩)
  have hα' : (decomposeWith tn y u).α x₀ = tn.α x₀ := by
    simp only [decomposeWith_α, if_neg hxu]
  obtain ⟨tn₁, tnStar', k', hreach, hwf₁, hx₁, hα₁, hall₁, hrest₁, hiso₁⟩ :=
    ih k hk hrest hwf' (hiso.isPrimitive hprim) hx₀'
  exact ⟨tn₁, tnStar', k',
    Relation.ReflTransGen.head ⟨y, m, hmM, hyT, hαy, u, hu, huiso, hdisj, rfl⟩ hreach,
    hwf₁, hx₁, hα₁.trans hα', hall₁, hrest₁, hiso.trans hiso₁⟩

/-- **The isolation statement, semantically.**  Let `x₀` be a task of the initial network of a
solvable problem.  Then a network `tn₁` reachable from the initial one exists in which `x₀` is
untouched (present, with its label) and is the only compound task, and the problem started from
`tn₁` instead is still solvable.  If the methods have at most one compound task, that problem is
one-hole-digging, so its search on pieces decomposes only isolated tasks (Lemma 6). -/
theorem Problem.exists_unroll_except (P : Problem F A C I) (hwf : P.tnI.WF) (hsol : P.Solvable)
    {x₀ : I} (hx₀ : x₀ ∈ P.tnI.T) :
    ∃ tn₁ : TaskNetwork I A C, P.Reachable tn₁ ∧ tn₁.WF ∧ x₀ ∈ tn₁.T ∧
      tn₁.α x₀ = P.tnI.α x₀ ∧ (∀ t ∈ tn₁.T, tn₁.IsAbstractId t → t = x₀) ∧
      (P.withTnI tn₁).Solvable := by
  obtain ⟨sol, hreach, hprim, hexec⟩ := hsol
  obtain ⟨n, hn⟩ := exists_decomposesToN hreach
  obtain ⟨tn₁, sol', k, h₁, hwf₁, hx, hα, hall, hk, hiso⟩ := hn.unroll_except n hwf hprim hx₀
  exact ⟨tn₁, h₁, hwf₁, hx, hα, hall, sol', hk.decomposesTo, hiso.isPrimitive hprim,
    hexec.iso hiso⟩

end Unroll

end HTN
