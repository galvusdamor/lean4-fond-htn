import Mathlib.Computability.Halting
import Mathlib.Logic.Relation

/-!
# Two-stack machines

The undecidability of HTN plan existence needs a Turing-complete device that an HTN hierarchy
can simulate.  The device used here is a **nondeterministic two-stack machine**: a finite
control together with two stacks over the alphabet `ℕ`, where a transition

* is enabled in one control state `src`,
* pops one symbol `pop` from one of the two stacks (`stk`),
* pushes a word `push` back onto *the same* stack, and
* moves the control to `tgt`.

Pushing onto the stack that is popped is not a restriction — a pure push of `b` is the
transition that pops `a` and pushes `b a` — and it is exactly the shape an HTN method can
realise: the compound task standing for the top symbol of a stack is decomposed into the action
of the transition followed by the compound tasks of the pushed word (see
`HtnComplexity/Undec/Encoding.lean`).

Acceptance is by **empty stacks in the distinguished state `acc`**; this too is no restriction
(a machine can pop its stacks empty using a bottom marker before accepting) and it is what
makes the encoding into an HTN problem light: a plan has to consume *all* tasks, so it has to
empty both stacks anyway.

Two stacks over a finite control are Turing complete — the two stacks hold the two halves of a
Turing machine tape — so the halting problem of two-stack machines is undecidable.  That fact
is *not* proved here; the results of `ComplexityTheory/Undec/` are stated relative to a
machine whose halting problem is undecidable (see `HtnComplexity/Undec/Cell.lean`).
-/

namespace HTN

namespace Undec

/-- A **transition** of a two-stack machine. -/
structure Tr where
  /-- The control state the transition starts in. -/
  src : ℕ
  /-- The stack the transition acts on (`false` the first, `true` the second). -/
  stk : Bool
  /-- The symbol the transition pops off that stack. -/
  pop : ℕ
  /-- The word the transition pushes back onto that stack. -/
  push : List ℕ
  /-- The control state the transition ends in. -/
  tgt : ℕ
  deriving DecidableEq, Inhabited

/-- A **two-stack machine**: a finite list of transitions, an initial and an accepting control
state. -/
structure TSM where
  /-- The transitions; their positions in this list are their names. -/
  trans : List Tr
  /-- The initial control state. -/
  start : ℕ
  /-- The accepting control state. -/
  acc : ℕ
  deriving Inhabited

/-- A **configuration**: the control state and the contents of the two stacks, top first. -/
structure Cfg where
  /-- The control state. -/
  st : ℕ
  /-- The first stack, top first. -/
  s1 : List ℕ
  /-- The second stack, top first. -/
  s2 : List ℕ
  deriving DecidableEq, Inhabited

namespace TSM

variable (M : TSM)

/-- **One step of the machine**: some listed transition is enabled in the current state and pops
the top of its stack. -/
def Step (c c' : Cfg) : Prop :=
  ∃ t ∈ M.trans, c.st = t.src ∧
    ((t.stk = false ∧ ∃ rest, c.s1 = t.pop :: rest ∧ c' = ⟨t.tgt, t.push ++ rest, c.s2⟩) ∨
      (t.stk = true ∧ ∃ rest, c.s2 = t.pop :: rest ∧ c' = ⟨t.tgt, c.s1, t.push ++ rest⟩))

/-- Reachability in the machine. -/
def Reaches : Cfg → Cfg → Prop := Relation.ReflTransGen M.Step

/-- **The machine halts on the pair of initial stacks**: it reaches the accepting state with
both stacks empty. -/
def Halts (s1 s2 : List ℕ) : Prop := M.Reaches ⟨M.start, s1, s2⟩ ⟨M.acc, [], []⟩

variable {M}

theorem Reaches.refl (c : Cfg) : M.Reaches c c := Relation.ReflTransGen.refl

theorem Reaches.head {c c' c'' : Cfg} (h : M.Step c c') (h' : M.Reaches c' c'') :
    M.Reaches c c'' := Relation.ReflTransGen.head h h'

/-- The step that a transition on the first stack takes. -/
theorem step_left {t : Tr} (ht : t ∈ M.trans) (hs : t.stk = false) (q : ℕ) (hq : q = t.src)
    (rest s2 : List ℕ) : M.Step ⟨q, t.pop :: rest, s2⟩ ⟨t.tgt, t.push ++ rest, s2⟩ :=
  ⟨t, ht, hq, Or.inl ⟨hs, rest, rfl, rfl⟩⟩

/-- The step that a transition on the second stack takes. -/
theorem step_right {t : Tr} (ht : t ∈ M.trans) (hs : t.stk = true) (q : ℕ) (hq : q = t.src)
    (s1 rest : List ℕ) : M.Step ⟨q, s1, t.pop :: rest⟩ ⟨t.tgt, s1, t.push ++ rest⟩ :=
  ⟨t, ht, hq, Or.inr ⟨hs, rest, rfl, rfl⟩⟩

end TSM

end Undec

end HTN
