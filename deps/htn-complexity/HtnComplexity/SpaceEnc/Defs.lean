import ComplexityTheory.Complexity.Hypotheses
import HtnPlanning.Interleave.GridYield
import HtnPlanning.Interleave.InterleaveList
/-!
# A tail-recursive encoding of space-bounded Turing machines: the problem

The source side of the cells (`HTN-TR`, `HTN-AC`) asks for the `EXPSPACE`-hardness of
tail-recursive HTN planning with a rooted instance.  This file defines the semantic planning
problem of the encoding; its correctness is proved in the other files of
`HtnComplexity/SpaceEnc/`.

A nondeterministic machine `N` with a tape of `W = 2 ^ m` cells is simulated round by round,
one round per machine step.  A round sweeps the positions `c = 0, …, W - 1` with a binary
counter.  Two loops `A` (`true`) and `B` (`false`) produce, alternately, one *block* per round;
a block consists of `2 ^ m` *chain words* (one per position) and one *round end* word.  A chain
word of parity `p` is

`ws p · wb p 0 x₀ e₀ ⋯ wb p (m-1) x e · (rd) · (cp p γ | tr p δ) · (inc p k | wrap p) · rv p γ' ·
  rb p (m-1) x ⋯ rb p 0 x₀`

— the address `x` is checked against the counter when the word is *written* (`wb`) and again
when its tail is *read* in the next round (`rb`); the tail `rv p γ' · rb ⋯` thus stores the
symbol `γ'` of the cell at that address until the next round, played by the other loop, reads
it.  The other actions: `ri`/`rblank` read the input in round 0, `h*` move the head at the end
of a round, `fin` accepts and `drn` drains the last stored tails.

Facts: a single program counter `pc s`, the counter bits `cb`, the head bits `hb`, the state
`st`, the last read symbol `sym`, the head move `mv`, the parity `par` of the writing loop,
`first` (round 0), the input index `u` (round 0), `eqf`/`neqf` (is the counter equal to the
head?), the input facts `inp` (the instance) and `boot0`, `drain`.
-/

namespace HTN

namespace SpaceEnc

open TM

/-- The list of the three head movements. -/
def allMoves : List Move := [Move.left, Move.stay, Move.right]

theorem mem_allMoves (μ : Move) : μ ∈ allMoves := by cases μ <;> simp [allMoves]

/-! ### The vocabulary -/

/-- The facts of the encoding. -/
inductive Fct (Q Γ : Type) where
  | boot0
  | inp (i : ℕ) (b : Bool)
  | pc (s : ℕ)
  | cb (k : ℕ) (x : Bool)
  | hb (k : ℕ) (x : Bool)
  | st (q : Q)
  | sym (g : Γ)
  | mv (μ : Move)
  | par (p : Bool)
  | first
  | u (j : ℕ)
  | eqf
  | neqf
  | drain
  deriving DecidableEq

/-- The actions of the encoding.  Every action of a loop carries the parity `p` of the loop. -/
inductive Act (Q Γ : Type) where
  | boot
  | ws (p : Bool)
  | wb (p : Bool) (k : ℕ) (x e : Bool)
  | rb (p : Bool) (k : ℕ) (x : Bool)
  | rv (p : Bool) (g : Γ)
  | ri (i : ℕ) (b : Bool)
  | rblank
  | cp (p : Bool) (g : Γ)
  | tr (p : Bool) (q0 : Q) (g0 : Γ) (q1 : Q) (g1 : Γ) (μ : Move)
  | inc (p : Bool) (k : ℕ)
  | wrap (p : Bool)
  | hinc (p : Bool) (k : ℕ)
  | hdec (p : Bool) (k : ℕ)
  | hdec0 (p : Bool)
  | hstay (p : Bool)
  | fin (q : Q)
  | drn
  deriving DecidableEq

instance {Q Γ : Type} : Inhabited (Act Q Γ) := ⟨Act.boot⟩

/-- The compound tasks of the encoding. -/
inductive Cmp where
  | root
  | main
  | loop (p : Bool)
  | block (p : Bool)
  | tree (p : Bool) (k : ℕ)
  | bit (p : Bool) (k : ℕ)
  | rd0
  | core (p : Bool)
  | incT (p : Bool)
  | reT (p : Bool)
  | finish
  | drainT
  deriving DecidableEq

instance : Nonempty Cmp := ⟨Cmp.root⟩

/-- The parity tag of an action: the loop it belongs to (`ri`, `rblank` belong to `A`). -/
def tag {Q Γ : Type} : Act Q Γ → Option Bool
  | .ws p => some p
  | .wb p _ _ _ => some p
  | .rb p _ _ => some p
  | .rv p _ => some p
  | .ri _ _ => some true
  | .rblank => some true
  | .cp p _ => some p
  | .tr p _ _ _ _ _ => some p
  | .inc p _ => some p
  | .wrap p => some p
  | .hinc p _ => some p
  | .hdec p _ => some p
  | .hdec0 p => some p
  | .hstay p => some p
  | _ => none

variable {Q Γ : Type}

/-! ### The action model

`m` is the number of counter bits, `n'` the number of input positions read in round 0, `ι` the
tape symbol of an input bit and `N` the machine (its initial state and blank). -/

section Actions

variable [Fintype Γ] (m n' : ℕ) (ι : Bool → Γ) (N : NTM Q Γ)

/-- All symbol facts, deleted before a new symbol is recorded. -/
noncomputable def symFacts : List (Fct Q Γ) := (Finset.univ : Finset Γ).toList.map Fct.sym

/-- The precondition of an action, as a list. -/
noncomputable def precL : Act Q Γ → List (Fct Q Γ)
  | .boot => [.boot0]
  | .ws p => [.pc 0, .par p]
  | .wb p k x e => [.pc (k + 1), .cb k x, .hb k (if e then x else !x), .par p]
  | .rb _ k x => [.pc (2 * m + 1 - k), .cb k x]
  | .rv p _ => [.pc (m + 1), .par (!p)]
  | .ri i b => [.pc (m + 1), .first, .u i, .inp i b]
  | .rblank => [.pc (m + 1), .first, .u n']
  | .cp p g => [.pc (2 * m + 2), .neqf, .sym g, .par p]
  | .tr p q0 g0 _ _ _ => [.pc (2 * m + 2), .eqf, .sym g0, .st q0, .par p]
  | .inc p k => [.pc (2 * m + 3), .par p, .cb k false] ++ (List.range k).map (Fct.cb · true)
  | .wrap p => [.pc (2 * m + 3), .par p] ++ (List.range m).map (Fct.cb · true)
  | .hinc p k => [.pc (2 * m + 4), .par p, .mv .right, .hb k false] ++
      (List.range k).map (Fct.hb · true)
  | .hdec p k => [.pc (2 * m + 4), .par p, .mv .left, .hb k true] ++
      (List.range k).map (Fct.hb · false)
  | .hdec0 p => [.pc (2 * m + 4), .par p, .mv .left] ++ (List.range m).map (Fct.hb · false)
  | .hstay p => [.pc (2 * m + 4), .par p, .mv .stay]
  | .fin q => [.pc 0, .st q] ++ (List.range m).map (Fct.cb · false)
  | .drn => [.pc (2 * m + 2), .drain]

/-- The delete list of an action. -/
noncomputable def delL : Act Q Γ → List (Fct Q Γ)
  | .boot => [.boot0]
  | .ws _ => [.pc 0]
  | .wb _ k _ e => [.pc (k + 1)] ++ (if e then [] else [.eqf])
  | .rb _ k _ => [.pc (2 * m + 1 - k)]
  | .rv _ _ => [.pc (m + 1)] ++ symFacts
  | .ri i _ => [.pc (m + 1), .u i] ++ symFacts
  | .rblank => [.pc (m + 1)] ++ symFacts
  | .cp _ _ => [.pc (2 * m + 2)]
  | .tr _ q0 _ _ _ _ => [.pc (2 * m + 2), .st q0]
  | .inc _ k => [.pc (2 * m + 3), .cb k false, .neqf] ++ (List.range k).map (Fct.cb · true)
  | .wrap _ => [.pc (2 * m + 3), .neqf] ++ (List.range m).map (Fct.cb · true)
  | .hinc p k => [.pc (2 * m + 4), .par p, .mv .right, .first, .hb k false] ++
      (List.range k).map (Fct.hb · true)
  | .hdec p k => [.pc (2 * m + 4), .par p, .mv .left, .first, .hb k true] ++
      (List.range k).map (Fct.hb · false)
  | .hdec0 p => [.pc (2 * m + 4), .par p, .mv .left, .first]
  | .hstay p => [.pc (2 * m + 4), .par p, .mv .stay, .first]
  | .fin _ => [.pc 0]
  | .drn => [.pc (2 * m + 2)]

/-- The add list of an action. -/
noncomputable def addL : Act Q Γ → List (Fct Q Γ)
  | .boot => [.pc 0, .st N.init, .par true, .first, .u 0, .eqf] ++
      (List.range m).map (Fct.cb · false) ++ (List.range m).map (Fct.hb · false)
  | .ws _ => [.pc 1]
  | .wb _ k _ e => [.pc (k + 2)] ++ (if e then [] else [.neqf])
  | .rb _ k _ => [.pc (2 * m + 2 - k)]
  | .rv _ g => [.pc (m + 2), .sym g]
  | .ri i b => [.pc (2 * m + 2), .u (i + 1), .sym (ι b)]
  | .rblank => [.pc (2 * m + 2), .sym N.blank]
  | .cp _ _ => [.pc (2 * m + 3)]
  | .tr _ _ _ q1 _ μ => [.pc (2 * m + 3), .st q1, .mv μ]
  | .inc _ k => [.pc 0, .cb k true, .eqf] ++ (List.range k).map (Fct.cb · false)
  | .wrap _ => [.pc (2 * m + 4), .eqf] ++ (List.range m).map (Fct.cb · false)
  | .hinc p k => [.pc 0, .par (!p), .hb k true] ++ (List.range k).map (Fct.hb · false)
  | .hdec p k => [.pc 0, .par (!p), .hb k false] ++ (List.range k).map (Fct.hb · true)
  | .hdec0 p => [.pc 0, .par (!p)]
  | .hstay p => [.pc 0, .par (!p)]
  | .fin _ => [.pc (m + 1), .drain, .par true, .par false] ++
      (List.range m).map (Fct.cb · true) ++ (List.range m).map (Fct.cb · false)
  | .drn => [.pc (m + 1)]

/-- The action model of the encoding. -/
noncomputable def am : ActionModel (Fct Q Γ) (Act Q Γ) where
  prec := fun a => {f | f ∈ precL m n' a}
  add := fun a => {f | f ∈ addL m ι N a}
  del := fun a => {f | f ∈ delL m a}

end Actions

/-! ### The methods -/

section Methods

variable [Fintype Q] [Fintype Γ] (m n' : ℕ) (N : NTM Q Γ)

open Classical in
/-- The transitions of the machine, as a list of tuples `(q, γ, q', γ', μ)`. -/
noncomputable def transL : List (Q × Γ × Q × Γ × Move) :=
  (((Finset.univ : Finset (Q × Γ × Q × Γ)).toList.flatMap fun t =>
      allMoves.map fun μ => (t.1, t.2.1, t.2.2.1, t.2.2.2, μ))).filter fun d =>
    decide ((d.2.2.1, d.2.2.2.1, d.2.2.2.2) ∈ N.step d.1 d.2.1)

open Classical in
/-- The accepting states of the machine, as a list. -/
noncomputable def accL : List Q :=
  (Finset.univ : Finset Q).toList.filter fun q => decide (q ∈ N.accept)

/-- A single compound task. -/
abbrev cT (c : Cmp) : Act Q Γ ⊕ Cmp := Sum.inr c

/-- A single action. -/
abbrev aT (a : Act Q Γ) : Act Q Γ ⊕ Cmp := Sum.inl a

/-- The methods of one parity `p`, each a compound task and the rows of its grid body. -/
noncomputable def bodiesP (p : Bool) : List (Cmp × List (List (Act Q Γ ⊕ Cmp))) :=
  [(.loop p, [[cT (.block p), cT (.loop p)]]), (.loop p, []),
    (.block p, [[cT (.tree p m)], [cT (.reT p)]]),
    (.tree p 0, [[aT (.ws p), cT (.bit p 0)]])] ++
  (List.range m).map (fun k => (.tree p (k + 1), [[cT (.tree p k)], [cT (.tree p k)]])) ++
  (List.range m).flatMap (fun k => [true, false].flatMap fun x => [true, false].map fun e =>
    (.bit p k, [[aT (.wb p k x e), cT (.bit p (k + 1)), aT (.rb p k x)]])) ++
  [(.bit p m, if p then [[cT .rd0, cT (.core p)]] else [[cT (.core p)]])] ++
  (Finset.univ : Finset Γ).toList.map (fun g =>
    (.core p, [[aT (.cp p g), cT (.incT p), aT (.rv p g)]])) ++
  (transL N).map (fun d =>
    (.core p, [[aT (.tr p d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2), cT (.incT p),
      aT (.rv p d.2.2.2.1)]])) ++
  (List.range m).map (fun k => (.incT p, [[aT (.inc p k)]])) ++ [(.incT p, [[aT (.wrap p)]])] ++
  (List.range m).map (fun k => (.reT p, [[aT (.hinc p k)]])) ++
  (List.range m).map (fun k => (.reT p, [[aT (.hdec p k)]])) ++
  [(.reT p, [[aT (.hdec0 p)]]), (.reT p, [[aT (.hstay p)]])]

/-- **All methods of the encoding.** -/
noncomputable def bodies : List (Cmp × List (List (Act Q Γ ⊕ Cmp))) :=
  [(.root, [[aT .boot, cT .main]]),
    (.main, [[cT (.loop true)], [cT (.loop false)], [cT .finish]]),
    (.rd0, []), (.rd0, [[aT .rblank]])] ++
  (List.range n').flatMap (fun i => [true, false].map fun b => (.rd0, [[aT (.ri i b)]])) ++
  bodiesP m N true ++ bodiesP m N false ++
  (accL N).map (fun q => (.finish, [[aT (.fin q), cT .drainT]])) ++
  [(.drainT, [[aT .drn, cT .drainT]]), (.drainT, [])]

end Methods

/-! ### The problem -/

/-- The input facts of a word: the fact `inp i (w i)` for every position `i < |w|`. -/
def inpL (w : List Bool) : List (Fct Q Γ) :=
  (List.range w.length).map fun i => Fct.inp i (w.getD i false)

variable [Fintype Q] [Fintype Γ] (m n' : ℕ) (ι : Bool → Γ) (N : NTM Q Γ)

/-- **The planning problem of the encoding** for the input word `w`: the initial task network is
the single compound task `root`, the initial state the fact `boot0` and the input facts, the goal
is empty. -/
noncomputable def prob (w : List Bool) : Problem (Fct Q Γ) (Act Q Γ) Cmp (ℕ × ℕ) where
  toActionModel := am m n' ι N
  methods := {mt | ∃ b ∈ bodies m n' N, mt = ⟨b.1, TaskNetwork.grid b.2⟩}
  init := {f | f ∈ Fct.boot0 :: inpL w}
  goal := ∅
  tnI := TaskNetwork.grid [[Sum.inr Cmp.root]]

end SpaceEnc

end HTN
