import HtnComplexity.Guard.TMFamily
import HtnComplexity.TMEnc.TMHoming
/-!
# The re-split construction decides acceptance

`HtnComplexity/Guard/TMFamily.lean` re-splits the encoding of Theorem 4.3.7: the domain
`HTN.TMEnc.Fam.famDomain N n K` depends on the input only through its length `n`, and the word is
carried by the instance `HTN.TMEnc.Fam.famInstance N w`.  `HtnComplexity/TMEnc/TMHoming.lean`
proves the correctness of the encoding, for the normalised ("homing") machine: the encoded
problem of `N⁺` on the marked input `w⁺` is solvable exactly when `N` accepts `w` in time `K`.

Putting the two together gives the statement a hardness *family* needs, and which the source side
of cells 3–5 of Table 3 asks for at the semantic level:

> **one domain per input length**, and an instance carrying the word, such that the pair is
> solvable exactly when the machine accepts the word within its time bound.

## Main results

* `HTN.TMEnc.solvable_famDomain_homingMachine_iff` — the family problem of the normalised
  machine is solvable exactly when `N` accepts `w` within `K` steps;
* `HTN.TMEnc.famDomain_correct_exp` — the same with the exponential time bound of the source;
* `HTN.TMEnc.isAcyclic_famDomain_homing`, `HTN.TMEnc.isTailRecursive_famDomain_homing`,
  `HTN.TMEnc.isTO_tnI_famDomain_homing`, `HTN.TMEnc.wf_famDomain_homing` — the class conditions,
  restated for that problem: it is well formed, acyclic (hence tail-recursive) and its initial
  task network is a single chain.
-/

namespace HTN

namespace TMEnc

open TM Fam

variable {Q Γ : Type} (N : NTM Q Γ)

/-- The family problem of the normalised machine, for the input word `w`: its **domain** depends
on `N`, on the length of `w` and on the time bound only, and its **instance** carries `w`. -/
def famProblem (w : List Γ) (K' : ℕ) :
    Problem (GFact (Q ⊕ Bool) (Γ × Bool)) (GAct (Q ⊕ Bool) (Γ × Bool))
      (TMTask (Q ⊕ Bool) (Γ × Bool)) (ℕ × ℕ) :=
  (famDomain (homingMachine N) w.length K').mkProblem
    (famInstance (homingMachine N) (markInput N w))

/-- The domain of the family problem is the one of every word of the same length. -/
lemma famProblem_eq (w : List Γ) (K' : ℕ) :
    famProblem N w K' =
      (famDomain (homingMachine N) (markInput N w).length K').mkProblem
        (famInstance (homingMachine N) (markInput N w)) := by
  rw [famProblem, markInput_length]

/-- **The family construction decides acceptance.**

For a machine that is clocked at `K` (`HTN.TMEnc.ClockedAt`: it cannot accept at all without
accepting within `K` steps), the family problem of the normalised machine with the bound
`K' ≥ 2K + 1` is solvable exactly when `N` accepts `w` within `K` steps.  The domain of that
problem is a function of `N`, of `|w|` and of `K'` alone. -/
theorem solvable_famDomain_homingMachine_iff {w : List Γ} {K K' : ℕ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ K) (hK' : 2 * K + 1 ≤ K') (hclock : ClockedAt N w K) :
    (famProblem N w K').Solvable ↔ N.AcceptsWithin w K := by
  rw [famProblem_eq, Fam.solvable_famDomain_iff]
  exact solvable_problemFix_homingMachine_iff N hw hwK hK' hclock

/-- **The family construction decides acceptance, in the exponential-time wording of the
source.** -/
theorem famDomain_correct_exp {p : Polynomial ℕ} {w : List Γ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ 2 ^ p.eval w.length)
    (hclock : ClockedAt N w (2 ^ p.eval w.length)) :
    (famProblem N w (2 ^ (p + Polynomial.C 2).eval w.length)).Solvable ↔ N.AcceptsExp p w := by
  have heval : (p + Polynomial.C 2).eval w.length = p.eval w.length + 2 := by simp
  have hpow : (2 : ℕ) ^ (p + Polynomial.C 2).eval w.length = 4 * 2 ^ p.eval w.length := by
    rw [heval, pow_add]; ring
  have hone : 1 ≤ 2 ^ p.eval w.length := Nat.one_le_two_pow
  rw [hpow, NTM.AcceptsExp]
  exact solvable_famDomain_homingMachine_iff N hw hwK (by omega) hclock

/-! ### The class conditions -/

/-- The family problem is acyclic. -/
theorem isAcyclic_famDomain_homing (w : List Γ) (K' : ℕ) : (famProblem N w K').IsAcyclic :=
  isAcyclic_famDomain _ _ _ _

/-- The family problem is tail-recursive. -/
theorem isTailRecursive_famDomain_homing (w : List Γ) (K' : ℕ) :
    (famProblem N w K').IsTailRecursive :=
  isTailRecursive_famDomain _ _ _ _

/-- The initial task network of the family problem is a single chain. -/
theorem isTO_tnI_famDomain_homing (w : List Γ) (K' : ℕ) : (famProblem N w K').IsTO_tnI :=
  isTO_tnI_famDomain _ _ _ _

/-- The family problem is well formed. -/
theorem wf_famDomain_homing (w : List Γ) (K' : ℕ) : (famProblem N w K').WF :=
  wf_famDomain _ _ _ _

end TMEnc

end HTN
