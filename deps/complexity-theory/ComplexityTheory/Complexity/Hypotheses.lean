import ComplexityTheory.Complexity.Basic
/-!
# Standard complexity-theoretic hypotheses

**Definitions only.**  The separations used as hypotheses of conditional results, all phrased in
the machine models of `ComplexityTheory/Complexity/Basic.lean` and `ComplexityTheory/TM/Basic.lean`:

* `HTN.Syn.PNeqNP` — `P ≠ NP`;
* `HTN.Space.NexpNotInExpPoly` — `NEXPTIME ⊄ EXPTIME/poly`;
* `HTN.Space.ExptimeNePspace` — `EXPTIME ≠ PSPACE`;
* `TM.NTM.ReachesSpace`, `TM.NTM.AcceptsInSpace` — space-bounded runs of Turing machines;
* `HTN.Space.InExpSpace`, `HTN.Space.InNExpPoly` — `EXPSPACE` and `NEXPTIME/poly`;
* `HTN.Space.ExpspaceNotInNexpPoly` — `EXPSPACE ⊄ NEXPTIME/poly`.
-/

namespace HTN

namespace Syn

open PTime

/-- **`P ≠ NP`**, as a statement about languages of bit strings: some language verified in
polynomial time is not decided in polynomial time.  This is one of the two classical inputs the
refutations of the rooted-target block need; it is not proved here, and is carried as an explicit
hypothesis wherever it is used. -/
def PNeqNP : Prop := ∃ L : List Bool → Prop, InNP L ∧ ¬ InP L

end Syn

end HTN

/-! ## `NEXPTIME ⊄ EXPTIME/poly` -/

namespace HTN

namespace Space

/-- **`NEXPTIME ⊄ EXPTIME/poly`**: some language of `NEXPTIME` is not decided by an alternating
polynomial-space machine (equivalently, an exponential-time machine) with polynomial advice. -/
def NexpNotInExpPoly : Prop := ∃ L : List Bool → Prop, InNExp L ∧ ¬ InAltSpacePoly L

end Space

end HTN

/-! ## `EXPTIME ≠ PSPACE` -/

namespace HTN

namespace Space

/-- **`EXPTIME ≠ PSPACE`**, in the models of this development: some language of alternating
polynomial space — `EXPTIME`, by Chandra–Kozen–Stockmeyer — is not in deterministic polynomial
space.  Since `PSPACE ⊆ EXPTIME` is the easy inclusion, this is exactly the separation. -/
def ExptimeNePspace : Prop :=
  ∃ L : List Bool → Prop, PSpace.InAPSpace L ∧ ¬ PSpace.InPSpace L

end Space

end HTN

/-! ## Space-bounded runs of a Turing machine -/

namespace TM

namespace NTM

variable {Q Γ : Type*} (N : NTM Q Γ)

/-- `N.ReachesSpace S n c c'`: `c'` is reachable from `c` in exactly `n` steps by a run all of
whose configurations (the first and the last included) have the head on one of the cells
`0, …, S - 1`. -/
def ReachesSpace (S : ℕ) : ℕ → Config Q Γ → Config Q Γ → Prop
  | 0, c, c' => c = c' ∧ c.head < S
  | n + 1, c, c' => c.head < S ∧ ∃ d, N.Step c d ∧ ReachesSpace S n d c'

/-- `N` accepts `w` in space `S`: some accepting configuration is reachable from the initial
configuration by a run that only visits the cells `0, …, S - 1`.  No bound on the number of
steps is imposed. -/
def AcceptsInSpace (w : List Γ) (S : ℕ) : Prop :=
  ∃ (n : ℕ) (c : Config Q Γ), N.ReachesSpace S n (N.initConfig w) c ∧ c.state ∈ N.accept

end NTM

end TM

/-! ## `EXPSPACE`, `NEXPTIME/poly` and the separation -/

namespace HTN

namespace Space

open PTime Hier TM

/-- **`EXPSPACE`**, in the machine model of `ComplexityTheory/TM/Basic.lean`: the languages of
nondeterministic machines with finitely many states that accept exactly the words of the
language within the space bound `2 ^ p(|w|)`.  (Nondeterministic exponential space; it equals
deterministic exponential space by Savitch's theorem, which is not used anywhere.) -/
def InExpSpace (L : Lang) : Prop :=
  ∃ (k : ℕ) (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ),
    ∀ w, L w ↔ N.AcceptsInSpace (w.map some) (2 ^ p.eval w.length)

/-- **`NEXPTIME/poly`**: `x ∈ L` iff some certificate `w` of length at most `2 ^ p(|x|)` makes a
predicate `V` of Cobham's class accept `[x, adv |x|, w]`, the advice `adv n` being of polynomial
length.  `V` runs in time polynomial in the length of its arguments, hence exponential in `|x|`:
this is the verifier characterisation of `NEXPTIME`, with advice. -/
def InNExpPoly (L : List Bool → Prop) : Prop :=
  ∃ (V : Args → Bool) (p r : Polynomial ℕ) (adv : ℕ → List Bool), CobhamB V ∧
    (∀ n, (adv n).length ≤ r.eval n) ∧
    ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ 2 ^ p.eval x.length ∧ V [x, adv x.length, w] = true

/-- **`EXPSPACE ⊄ NEXPTIME/poly`**: some language of `EXPSPACE` is not in `NEXPTIME/poly`.
A standard open separation (the non-uniform strengthening of `EXPSPACE ≠ NEXPTIME`), of the same
kind as `HTN.Space.NexpNotInExpPoly`, one level up. -/
def ExpspaceNotInNexpPoly : Prop := ∃ L : List Bool → Prop, InExpSpace L ∧ ¬ InNExpPoly L

end Space

end HTN

