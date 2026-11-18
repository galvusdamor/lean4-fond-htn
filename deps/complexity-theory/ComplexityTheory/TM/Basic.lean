import Mathlib

/-!
# Nondeterministic Turing machines

**Definitions only.**  The single-tape nondeterministic Turing machine model used to define
`NEXPTIME` (`HTN.Space.InNExp` in `ComplexityTheory/Complexity/Basic.lean`): machines, configurations,
the (n-step) transition relation and acceptance within a time bound.  Lemmas about these notions
are in `ComplexityTheory/TM/Theory/Machine.lean`.
-/

/-! ## Machines and runs -/

namespace TM

/-- A movement of the head of a Turing machine: left, stay, right (`-1`, `0`, `+1`). -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Repr

/-- The new head position after a movement.  Moving left at position `0` stays at `0`; the
machines we consider never do this. -/
def Move.apply : Move → ℕ → ℕ
  | .left, n => n - 1
  | .stay, n => n
  | .right, n => n + 1

/-- A nondeterministic Turing machine `N = (S, Γ, δ, q₀, F)` with a one-way infinite tape. -/
structure NTM (Q Γ : Type*) where
  /-- The transition relation `δ : S × Γ → 2^(S × Γ × {-1,0,1})`. -/
  step : Q → Γ → Set (Q × Γ × Move)
  /-- The initial state `q₀`. -/
  init : Q
  /-- The set `F` of accepting states. -/
  accept : Set Q
  /-- The blank symbol (`0` in the source), filling the tape beyond the input. -/
  blank : Γ

/-- A configuration of a Turing machine: the current state, the head position and the tape. -/
structure Config (Q Γ : Type*) where
  /-- The current state. -/
  state : Q
  /-- The current head position. -/
  head : ℕ
  /-- The current tape content, cell by cell. -/
  tape : ℕ → Γ

namespace NTM

variable {Q Γ : Type*} (N : NTM Q Γ)

/-- One step of the machine: read the symbol under the head, pick a transition, write the new
symbol and move the head. -/
def Step (c c' : Config Q Γ) : Prop :=
  ∃ q' : Q, ∃ γ' : Γ, ∃ m : Move,
    (q', γ', m) ∈ N.step c.state (c.tape c.head) ∧
      c' = ⟨q', m.apply c.head, Function.update c.tape c.head γ'⟩

/-- `N.Reaches n c c'` holds iff `c'` is reachable from `c` in exactly `n` steps. -/
def Reaches : ℕ → Config Q Γ → Config Q Γ → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ d, N.Step c d ∧ Reaches n d c'

/-- The initial configuration for the input `w`: state `q₀`, head at cell `0`, the input in the
first `|w|` cells and blanks everywhere else. -/
def initConfig (w : List Γ) : Config Q Γ where
  state := N.init
  head := 0
  tape := fun i => w.getD i N.blank

/-- `N` accepts the input `w` within `K` steps iff some accepting configuration is reachable in
at most `K` steps. -/
def AcceptsWithin (w : List Γ) (K : ℕ) : Prop :=
  ∃ n ≤ K, ∃ c : Config Q Γ, N.Reaches n (N.initConfig w) c ∧ c.state ∈ N.accept

/-- `N` accepts `w` in *exponential time* with respect to the polynomial `p` iff it accepts `w`
within `2 ^ p(|w|)` steps. -/
def AcceptsExp (p : Polynomial ℕ) (w : List Γ) : Prop :=
  N.AcceptsWithin w (2 ^ p.eval w.length)

end NTM

end TM
