import Mathlib
import ComplexityTheory.TM.Basic
import ComplexityTheory.Complexity.Poly
/-!
# Complexity classes

**Definitions only.**  The complexity classes in which the hypotheses of the five table files are
phrased.  All classes are classes of languages `List Bool → Prop` of bit strings.

* polynomial time: `HTN.PTime.PolyTimeFun` — Mathlib's `Turing.TM2ComputableInPolyTime` on bit
  strings; `HTN.Syn.InP`, `HTN.Syn.InNP` (polynomial-time verifier with a polynomially bounded
  certificate);
* the polynomial hierarchy: `HTN.PH.SigmaP`, `HTN.PH.PiP`, `HTN.PH.PHCollapsesTo`;
* deterministic polynomial space: `HTN.PSpace.InPSpace` (a polynomial-width state iterated
  exponentially often by a step function of Cobham's class);
* alternating polynomial space (= `EXPTIME`): `HTN.PSpace.InAPSpace`, and with polynomial advice
  `HTN.Space.InAltSpacePoly` (= `EXPTIME/poly`);
* nondeterministic exponential time: `HTN.Space.InNExp` (Turing machines of
  `ComplexityTheory/TM/Basic.lean`).

The space-bounded machine models describe their transition functions in Cobham's class
`HTN.PTime.Cobham` (the polynomial-time functions in the recursion-theoretic presentation); the
equivalence of Cobham's class with polynomial-time Turing machines is proved in
`ComplexityTheory/Complexity/CobhamTM/`.
-/

/-! ## Bit strings as a Turing-machine encoding -/

namespace HTN.PTime.CobhamTM

open Turing
attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.kFin FinTM2.Γk₀Fin

/-- The encoding of bit strings by themselves, over the alphabet `Bool`. -/
def finEncodingListBool : Computability.FinEncoding (List Bool) where
  Γ := Bool
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

end HTN.PTime.CobhamTM

/-! ## Bounded quantification over bit strings -/

namespace HTN

namespace PSpace

open PTime

/-- All bit strings of a given length. -/
def allLen : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allLen m).flatMap fun y => [false :: y, true :: y]

/-- "Some string of length `m` satisfies `q`", as a Boolean. -/
def anyLen (m : ℕ) (q : List Bool → Bool) : Bool := (allLen m).any q

/-- "Every string of length `m` satisfies `q`", as a Boolean. -/
def allLenB (m : ℕ) (q : List Bool → Bool) : Bool := (allLen m).all q

end PSpace

end HTN

/-! ## Cobham's class -/

namespace HTN

namespace PTime

/-- The arguments of a function of the class: a list of bit strings. -/
abbrev Args : Type := List (List Bool)

/-- A function of the class: bit strings in, one bit string out. -/
abbrev Fn : Type := Args → List Bool

/-- The `n`-th projection; a missing argument reads as the empty string. -/
def proj (n : ℕ) : Fn := fun args => args.getD n []

/-- The successor `x ↦ b :: x`, applied to the first argument. -/
def consFn (b : Bool) : Fn := fun args => b :: args.getD 0 []

/-- The smash function, in its length form: a string of length `|x| * |y|`. -/
def smashFn : Fn :=
  fun args => List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) false

/-- Composition: `g` applied to the results of the functions `hs` on the same arguments. -/
def compFn (g : Fn) (hs : List Fn) : Fn := fun args => g (hs.map fun h => h args)

/-- Recursion on notation, before the size bound is imposed: the recursion runs on the bits of
the first argument, `h0` handling a leading `false` and `h1` a leading `true`, and receives the
tail of the string, the recursive value and the remaining arguments. -/
def brnAux (g h0 h1 : Fn) : List Bool → Args → List Bool
  | [], v => g v
  | b :: x, v => (bif b then h1 else h0) (x :: brnAux g h0 h1 x v :: v)

/-- Recursion on notation on the first argument. -/
def brnFn (g h0 h1 : Fn) : Fn := fun args => brnAux g h0 h1 (args.getD 0 []) args.tail

/-- **Cobham's class**: the smallest class of functions on bit strings containing the constant
empty string, the projections, the two successors and the smash function, closed under
composition and under recursion on notation *bounded* by a function already in the class.

The bound is the side condition of the last constructor: the recursion may be formed only if
the function it defines is, at every argument, no longer than a function `bd` of the class.
This is the standard definition; by Cobham's theorem the class is exactly `FP` (formalised in
`ComplexityTheory/Complexity/CobhamTM/`, see the module docstring). -/
inductive Cobham : Fn → Prop
  /-- The constant empty string. -/
  | empty : Cobham (fun _ => [])
  /-- The projections. -/
  | proj (n : ℕ) : Cobham (proj n)
  /-- The two successors on notation. -/
  | cons (b : Bool) : Cobham (consFn b)
  /-- The smash function. -/
  | smash : Cobham smashFn
  /-- Closure under composition. -/
  | comp {g : Fn} {hs : List Fn} : Cobham g → (∀ h ∈ hs, Cobham h) → Cobham (compFn g hs)
  /-- Closure under bounded recursion on notation. -/
  | brn {g h0 h1 bd : Fn} : Cobham g → Cobham h0 → Cobham h1 → Cobham bd →
      (∀ args, (brnFn g h0 h1 args).length ≤ (bd args).length) → Cobham (brnFn g h0 h1)

end PTime

end HTN

/-! ## Boolean-valued functions of Cobham's class -/

namespace HTN

namespace PTime

/-- **A predicate of Cobham's class**: its one-bit answer is computed by a function of the
class. -/
def CobhamB (p : Args → Bool) : Prop := Cobham (fun args => [p args])

end PTime

end HTN

/-! ## Alternating polynomial space (`APSPACE = EXPTIME`) -/

namespace HTN

namespace PSpace

open PTime

/-- **An alternating machine with a polynomial memory.**  Configurations are bit strings, all of
the same width `|widthF [x]|` — a polynomially long string computed from the input; the initial
configuration, the acceptance test, the classification of a configuration as universal or
existential, and the transition test are all of Cobham's class. -/
structure ASpace where
  /-- `widthF [x]`: a template string, whose *length* is the width of a configuration. -/
  widthF : Fn
  /-- `initF [x]`: the initial configuration on input `x`. -/
  initF : Fn
  /-- `accB [c, x]`: the configuration `c` is accepting. -/
  accB : Args → Bool
  /-- `univB [c, x]`: the configuration `c` is universal (otherwise it is existential). -/
  univB : Args → Bool
  /-- `stepB [c', c, x]`: the machine may pass from `c` to `c'`. -/
  stepB : Args → Bool
  /-- The width is computed in polynomial time. -/
  cobham_widthF : Cobham widthF
  /-- The initial configuration is computed in polynomial time. -/
  cobham_initF : Cobham initF
  /-- The acceptance test is polynomial time. -/
  cobhamB_accB : CobhamB accB
  /-- The classification test is polynomial time. -/
  cobhamB_univB : CobhamB univB
  /-- The transition test is polynomial time. -/
  cobhamB_stepB : CobhamB stepB
  /-- The initial configuration has the width of a configuration. -/
  initF_length : ∀ x, (initF [x]).length = (widthF [x]).length

namespace ASpace

variable (M : ASpace)

/-- The width of a configuration. -/
def w (x : List Bool) : ℕ := (M.widthF [x]).length

/-- **Acceptance within `t` rounds**: an accepting configuration accepts; a universal
configuration accepts within `t + 1` rounds when all its successors accept within `t`; an
existential one when some successor does. -/
def accWithin (M : ASpace) (x : List Bool) : ℕ → List Bool → Bool
  | 0, c => M.accB [c, x]
  | t + 1, c => M.accB [c, x] ||
      (if M.univB [c, x] = true then
          allLenB (M.w x) (fun c' => !M.stepB [c', c, x] || accWithin M x t c')
        else anyLen (M.w x) (fun c' => M.stepB [c', c, x] && accWithin M x t c'))

/-- The number of rounds the language is read off at: the largest counter of `w + 1` bits. -/
def horizon (x : List Bool) : ℕ := 2 ^ (M.w x + 1) - 1

/-- **The language of the machine.** -/
def L (x : List Bool) : Prop := M.accWithin x (M.horizon x) (M.initF [x]) = true

end ASpace

/-- **Alternating polynomial space**, as a class of languages. -/
def InAPSpace (L : List Bool → Prop) : Prop := ∃ M : ASpace, ∀ x, L x ↔ M.L x

end PSpace

end HTN

/-! ## Deterministic polynomial space (`PSPACE`) -/

namespace HTN

namespace PSpace

open PTime

/-- The value of a bit string read as a binary numeral, least significant bit first. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: x => (if b then 1 else 0) + 2 * val x

/-- `loopAux F rest n st` is the function `F` applied `n` times to the state `st`, the remaining
arguments `rest` being passed along unchanged. -/
def loopAux (F : Fn) (rest : Args) : ℕ → List Bool → List Bool
  | 0, st => st
  | n + 1, st => F (loopAux F rest n st :: rest)

/-- **Exponential iteration**: the first argument is a *counter*, read as a binary numeral; the
second is the initial state; the remaining arguments are passed to the update function `F`
together with the current state. -/
def loopFn (F : Fn) : Fn :=
  fun args => loopAux F args.tail.tail (val (args.getD 0 [])) (args.getD 1 [])

/-- **Polynomial space**: the smallest class of bit-string functions containing Cobham's class
and closed under composition and under bounded exponential iteration. -/
inductive PSpaceF : Fn → Prop
  /-- Polynomial time is polynomial space. -/
  | cobham {f : Fn} : Cobham f → PSpaceF f
  /-- Closure under composition. -/
  | comp {g : Fn} {hs : List Fn} : PSpaceF g → (∀ h ∈ hs, PSpaceF h) → PSpaceF (compFn g hs)
  /-- Closure under iteration of the update `F` for exponentially many steps, provided the
  state stays bounded by a function of the class. -/
  | loop {F bd : Fn} : PSpaceF F → PSpaceF bd →
      (∀ args, (loopFn F args).length ≤ (bd args).length) → PSpaceF (loopFn F)

/-- A **predicate of the class**: its one-bit answer is computed by a function of the class. -/
def PSpaceB (p : Args → Bool) : Prop := PSpaceF (fun args => [p args])

/-- **`PSPACE`**: the languages whose characteristic predicate is in the class. -/
def InPSpace (L : List Bool → Prop) : Prop :=
  ∃ p : Args → Bool, PSpaceB p ∧ ∀ x, L x ↔ p [x] = true

end PSpace

end HTN

/-! ## Polynomial time -/

namespace HTN.PTime

open Turing Computability CobhamTM

/-- **A polynomial-time function on bit strings**: one computed in polynomial time by a TM2
machine in the sense of Mathlib (`Turing.TM2ComputableInPolyTime`), bit strings being encoded by
themselves over the alphabet `Bool`. -/
def PolyTimeFun (F : List Bool → List Bool) : Prop :=
  Nonempty (TM2ComputableInPolyTime finEncodingListBool finEncodingListBool F)

end HTN.PTime

/-! ## Binary numerals -/

namespace HTN

namespace PTime

/-- The binary digits of a number, least significant bit first; the empty string codes `0`. -/
def bitsOfNat : ℕ → List Bool
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: bitsOfNat ((n + 1) / 2)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

end PTime

end HTN

/-! ## `P` and `NP` -/

namespace HTN

namespace Syn

open PTime

/-- **A language of bit strings is in `P`**: some function computed in polynomial time by a Turing machine (`HTN.PTime.PolyTimeFun`, i.e. Mathlib's
`Turing.TM2ComputableInPolyTime` on bit strings) outputs, on `x`, a string
whose first bit is the answer.  Equivalently (`HTN.Syn.inP_iff_tm2`), the characteristic function
of `L` is `Turing.TM2ComputableInPolyTime` from bit strings to `Bool`. -/
def InP (L : List Bool → Prop) : Prop :=
  ∃ G : List Bool → List Bool, PolyTimeFun G ∧ ∀ x, (L x ↔ (G x).getD 0 false = true)

/-- A self-delimiting pairing of two bit strings: the first component is written with each bit
doubled and the pair is separated by `false, true`, which cannot occur inside the doubled part.
It is used only to give the verifier of `InNP` a single argument. -/
def pairStr (x w : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ w

/-- **A language of bit strings is in `NP`**: some polynomial-time verifier (a function
computed in polynomial time by a Turing machine (`HTN.PTime.PolyTimeFun`, i.e. Mathlib's
`Turing.TM2ComputableInPolyTime` on bit strings)) accepts `x` together
with a certificate whose length is bounded by a fixed power of the length of `x`. -/
def InNP (L : List Bool → Prop) : Prop :=
  ∃ (V : List Bool → List Bool) (k : ℕ), PolyTimeFun V ∧
    ∀ x, (L x ↔ ∃ w : List Bool, w.length ≤ (x.length + 1) ^ k ∧
      (V (pairStr x w)).getD 0 false = true)

end Syn

end HTN

/-! ## Languages -/

namespace HTN

namespace Hier

/-- Words are bit strings. -/
abbrev Word := List Bool

/-- A language. -/
abbrev Lang := Word → Prop

end Hier

end HTN

/-! ## The polynomial hierarchy -/

namespace HTN

namespace PH

open PTime

/-- **The bounded alternating quantifier prefix.**  `qblock B P k b ys` puts `k` alternating
quantifiers over strings of length at most `B`, the first one existential when `b = true`, in
front of `P`; the quantified strings are appended to `ys` in the order they are introduced. -/
def qblock (B : ℕ) (P : List (List Bool) → Prop) : ℕ → Bool → List (List Bool) → Prop
  | 0, _, ys => P ys
  | (k + 1), true, ys => ∃ y : List Bool, y.length ≤ B ∧ qblock B P k false (ys ++ [y])
  | (k + 1), false, ys => ∀ y : List Bool, y.length ≤ B → qblock B P k true (ys ++ [y])

/-- **`L ∈ Σₖᵖ`**: `x ∈ L` iff `∃ y₁ ∀ y₂ ∃ y₃ … p(x, y₁, …, yₖ)` with `|yᵢ| ≤ q(|x|)`, for a
predicate `p` of Cobham's class (polynomial time) and a polynomial `q`. -/
def SigmaP (k : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (p : Args → Bool) (q : Polynomial ℕ), CobhamB p ∧
    ∀ x, L x ↔ qblock (q.eval x.length) (fun ys => p (x :: ys) = true) k true []

/-- **`L ∈ Πₖᵖ`**: the complement of `L` is in `Σₖᵖ`. -/
def PiP (k : ℕ) (L : List Bool → Prop) : Prop := SigmaP k (fun x => ¬ L x)

/-- **The polynomial hierarchy collapses to its `k`-th level**: `Πₖᵖ ⊆ Σₖᵖ` (equivalently, by
complementation, `Σₖᵖ = Πₖᵖ`). -/
def PHCollapsesTo (k : ℕ) : Prop := ∀ L : List Bool → Prop, PiP k L → SigmaP k L

end PH

end HTN

/-! ## Alternating polynomial space with polynomial advice (`EXPTIME/poly`) -/

namespace HTN

namespace Space

open PTime

/-- **An alternating machine with a polynomial memory, reading an input and an advice.**
Configurations are `k`-tuples of bit strings; the four tests are predicates of Cobham's class; and
every configuration the machine can start in or step into is polynomially bounded in the length
of the input and of the advice. -/
structure AltSpace where
  /-- The number of components of a configuration. -/
  k : ℕ
  /-- `initB (x :: a :: c)`: `c` is an initial configuration. -/
  initB : Args → Bool
  /-- `accB (x :: a :: c)`: `c` is accepting. -/
  accB : Args → Bool
  /-- `univB (x :: a :: c)`: `c` is universal (otherwise it is existential). -/
  univB : Args → Bool
  /-- `stepB (x :: a :: (c' ++ c))`: the machine may pass from `c` to `c'`. -/
  stepB : Args → Bool
  cobham_initB : CobhamB initB
  cobham_accB : CobhamB accB
  cobham_univB : CobhamB univB
  cobham_stepB : CobhamB stepB
  /-- The space bound. -/
  bound : Polynomial ℕ
  /-- An initial configuration is polynomially bounded. -/
  initB_length : ∀ x a c, c.length = k → initB (x :: a :: c) = true →
    ∀ w ∈ c, w.length ≤ bound.eval (x.length + a.length)
  /-- A configuration the machine steps into is polynomially bounded. -/
  stepB_length : ∀ x a c' c, c'.length = k → c.length = k → stepB (x :: a :: (c' ++ c)) = true →
    ∀ w ∈ c', w.length ≤ bound.eval (x.length + a.length)

namespace AltSpace

variable (M : AltSpace)

/-- **Alternating acceptance**, the least fixpoint of the acceptance rule. -/
inductive Acc (x a : List Bool) : Args → Prop
  /-- An accepting configuration accepts. -/
  | acc {c : Args} : c.length = M.k → M.accB (x :: a :: c) = true → Acc x a c
  /-- A universal configuration accepts when all its successors accept. -/
  | univ {c : Args} : c.length = M.k → M.univB (x :: a :: c) = true →
      (∀ c' : Args, c'.length = M.k → M.stepB (x :: a :: (c' ++ c)) = true → Acc x a c') →
      Acc x a c
  /-- An existential configuration accepts when some successor accepts. -/
  | ex {c c' : Args} : c.length = M.k → M.univB (x :: a :: c) = false → c'.length = M.k →
      M.stepB (x :: a :: (c' ++ c)) = true → Acc x a c' → Acc x a c

/-- **The machine accepts** the input `x` with advice `a`: some initial configuration accepts. -/
def Accepts (x a : List Bool) : Prop :=
  ∃ c : Args, c.length = M.k ∧ M.initB (x :: a :: c) = true ∧ M.Acc x a c

end AltSpace

/-- **`EXPTIME/poly`**, read as alternating polynomial space with polynomial advice: the languages
a machine of the model accepts with an advice string of polynomial length depending on the length
of the input only. -/
def InAltSpacePoly (L : List Bool → Prop) : Prop :=
  ∃ (M : AltSpace) (adv : ℕ → List Bool) (r : Polynomial ℕ),
    (∀ n, (adv n).length ≤ r.eval n) ∧ ∀ x, L x ↔ M.Accepts x (adv x.length)

end Space

end HTN

/-! ## Nondeterministic exponential time (`NEXPTIME`) -/

namespace HTN

namespace Space

open Hier TM


variable {s : Scale}

/-- The tape alphabet: a bit, or the blank `none`. -/
abbrev TapeSym := Option Bool

/-- **The language of a nondeterministic machine with an exponential time bound**: the words the
machine accepts within `2 ^ p(|w|)` steps, the word being written on the tape one bit per
cell. -/
def NTMLang {k : ℕ} (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) : Lang :=
  fun w => N.AcceptsExp p (w.map some)

/-- **The machine is clocked at `2 ^ p(|w|)`**: whenever it accepts a word at all, it accepts it
within `2 ^ p(|w|)` steps.  This is the usual convention for a machine *deciding* a language in
exponential time — no accepting run is longer than the time bound — stated without asking every
run to halt. -/
def ClockedExp {k : ℕ} (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) : Prop :=
  ∀ (w : List Bool) (m : ℕ), N.AcceptsWithin (w.map some) m →
    N.AcceptsWithin (w.map some) (2 ^ p.eval w.length)

/-- **`NEXPTIME`**, in the machine model of `ComplexityTheory/TM/Theory/Machine.lean`: the languages of
nondeterministic machines with finitely many states that are clocked at an exponential time
bound (`HTN.Space.ClockedExp`). -/
def InNExp (L : Lang) : Prop :=
  ∃ (k : ℕ) (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ), ClockedExp N p ∧
    ∀ w, L w ↔ NTMLang N p w

end Space

end HTN
