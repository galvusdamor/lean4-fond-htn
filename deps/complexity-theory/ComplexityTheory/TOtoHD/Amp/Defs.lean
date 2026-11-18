import Mathlib

/-!
# Bounded counter machines inside vector addition systems: the definitions

This folder proves that a counter machine with **zero tests** whose two counters stay below the
doubly exponential bound `B L = 2 ^ (2 ^ L)` can be simulated by a vector addition system with
states (no zero tests), where acceptance means reaching a final control state with **all places
empty** (reachability).  The vector addition system has `O(L)` control states besides the copy of
the counter machine.  It is the building block that lets a one-hole-digging HTN problem (a single
compound task controlling a pool of primitive tokens) simulate a totally ordered HTN problem.

## The counter machine (`HTN.Amp.CM`)

Control states `Q`, a set of facts `Φ` (the boolean registers), two counters (indexed by `Bool`).
A transition has a source and a target control state, a precondition, an add and a delete list of
facts, and one counter operation: none, increment, decrement, or **zero test**.

## The amplifier (`HTN.Amp.IsRule`)

The places of the vector addition system are, for every level `k ≤ L`, two *pairs*
`(side k r false, side k r true)` (`r : Bool`) whose sum is kept at `B k`, and two budget places
`c k`, `d k`.  At level `L` the two pairs are the two counters of the machine (the counter value is
the number of tokens on the `true` side).  At a lower level they are loop counters.

A zero test of a side `z` of a pair at level `k` (other side `z̄`, sum `B k`) consumes one `d k`
token, moves the content of `z̄` to `z` and back, and consumes one `c k` token per move.  Since
`c k = 2 B k · d k` when the budget is set up and every place must be empty at the end, every test
must perform exactly `2 B k` moves, which is possible only if `z` was empty (the potential
argument of `Sound.lean`).  The budget and the pairs of level `k + 1` are set up with nested loops
of length `B k` over the two loop counters of level `k` (`B (k+1) = B k * B k`), whose loop exits
are zero tests of level `k`.
-/

namespace HTN

namespace Amp

/-! ### The bound -/

/-- **The bound at level `k`**: `B k = 2 ^ (2 ^ k)`. -/
irreducible_def B (k : ℕ) : ℕ := 2 ^ (2 ^ k)

theorem B_succ (k : ℕ) : B (k + 1) = B k * B k := by
  simp only [B_def, pow_succ, pow_mul]
  ring

theorem B_zero : B 0 = 2 := by
  simp [B_def]

theorem B_pos (k : ℕ) : 0 < B k := by
  rw [B_def]; positivity

theorem two_le_B (k : ℕ) : 2 ≤ B k := by
  rw [B_def]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)

/-! ### Counter machines -/

/-- A counter operation on one of the two counters. -/
inductive COp where
  | nop : COp
  | inc (r : Bool) : COp
  | dec (r : Bool) : COp
  | zero (r : Bool) : COp
  deriving DecidableEq

/-- A transition of a counter machine. -/
structure CTr (Q Φ : Type) where
  /-- The source control state. -/
  src : Q
  /-- The precondition (facts that must hold). -/
  pre : List Φ
  /-- The facts added. -/
  add : List Φ
  /-- The facts deleted. -/
  del : List Φ
  /-- The counter operation. -/
  op : COp
  /-- The target control state. -/
  dst : Q

/-- **A counter machine**: a list of transitions, an initial and a final control state. -/
structure CM (Q Φ : Type) where
  /-- The transitions. -/
  trs : List (CTr Q Φ)
  /-- The initial control state. -/
  q0 : Q
  /-- The final control state. -/
  qf : Q

variable {Q Φ : Type} [DecidableEq Φ]

/-- The STRIPS update of a set of facts. -/
def upd (S : Finset Φ) (add del : List Φ) : Finset Φ :=
  S.filter (fun f => f ∉ del) ∪ add.toFinset

/-- The effect of a counter operation on the two counters. -/
def OpRel : COp → (Bool → ℕ) → (Bool → ℕ) → Prop
  | .nop, v, v' => v' = v
  | .inc r, v, v' => v' = Function.update v r (v r + 1)
  | .dec r, v, v' => 1 ≤ v r ∧ v' = Function.update v r (v r - 1)
  | .zero r, v, v' => v r = 0 ∧ v' = v

/-- A configuration of a counter machine: control state, facts, counters. -/
abbrev CCfg (Q Φ : Type) : Type := Q × Finset Φ × (Bool → ℕ)

/-- **A step of a counter machine.** -/
inductive CStep (P : CM Q Φ) : CCfg Q Φ → CCfg Q Φ → Prop
  | mk (t : CTr Q Φ) (ht : t ∈ P.trs) (S : Finset Φ) (v v' : Bool → ℕ)
      (hpre : ∀ f ∈ t.pre, f ∈ S) (hop : OpRel t.op v v') :
      CStep P (t.src, S, v) (t.dst, upd S t.add t.del, v')

/-- A step whose target keeps both counters at most `N`. -/
def CStepB (P : CM Q Φ) (N : ℕ) (x y : CCfg Q Φ) : Prop := CStep P x y ∧ ∀ r, y.2.2 r ≤ N

/-- **Bounded acceptance**: the machine goes from the initial control state, the facts `s0` and
empty counters to the final control state with empty counters and facts containing `g`, all
counters staying at most `N`. -/
def CAcc (P : CM Q Φ) (N : ℕ) (s0 : Finset Φ) (g : List Φ) : Prop :=
  ∃ S : Finset Φ, Relation.ReflTransGen (CStepB P N) (P.q0, s0, fun _ => 0) (P.qf, S, fun _ => 0) ∧
    ∀ f ∈ g, f ∈ S

/-! ### The vector addition system: places and control states -/

/-- The places. -/
inductive Pl where
  /-- Side `b` of the pair `r` of level `k`. -/
  | side (k : ℕ) (r b : Bool) : Pl
  /-- The budget of moves of level `k`. -/
  | c (k : ℕ) : Pl
  /-- The budget of zero tests of level `k`. -/
  | d (k : ℕ) : Pl
  deriving DecidableEq

/-- The phases of a zero test. -/
inductive ZPh where
  | A : ZPh
  | A' : ZPh
  | B : ZPh
  | B' : ZPh
  deriving DecidableEq

/-- The positions inside a multiplication loop. -/
inductive SPos where
  | inner : SPos
  | restj : SPos
  | outer : SPos
  | resti : SPos
  deriving DecidableEq

/-- The places a multiplication loop of a level fills: the `false` side of one of its pairs, or
the move budget (first and second half of a budget round). -/
inductive Site where
  | comp (r : Bool) : Site
  | bud (b : Bool) : Site
  deriving DecidableEq

/-- The zero tests: inside the multiplication loop of level `k` at site `s`, of the inner counter
(`sj`) or the outer counter (`si`), side `b`; or of the counter `r` for the transition number `i`
of the machine (`m`). -/
inductive ZI where
  | sj (k : ℕ) (s : Site) (b : Bool) : ZI
  | si (k : ℕ) (s : Site) (b : Bool) : ZI
  | m (i : ℕ) (r : Bool) : ZI
  deriving DecidableEq

/-- The control states of the vector addition system. -/
inductive Loc (Q : Type) where
  | start : Loc Q
  | bl (k : ℕ) : Loc Q
  | sp (k : ℕ) (s : Site) (p : SPos) : Loc Q
  | zt (z : ZI) (ph : ZPh) : Loc Q
  | main (q : Q) : Loc Q
  | drain : Loc Q
  | done : Loc Q

/-- The level of a zero test (`L` for the tests of the machine).  The multiplication loops
`sp k _ _` and their tests `sj k _ _`, `si k _ _` use the pairs of level `k` as loop counters and
fill a place of level `k + 1`. -/
def ZI.lvl (L : ℕ) : ZI → ℕ
  | .sj k _ _ => k
  | .si k _ _ => k
  | .m _ _ => L

/-- The pair a zero test acts on. -/
def ZI.pr : ZI → Bool
  | .sj _ _ _ => true
  | .si _ _ _ => false
  | .m _ r => r

/-- The side a zero test tests. -/
def ZI.sd : ZI → Bool
  | .sj _ _ b => b
  | .si _ _ b => b
  | .m _ _ => true

/-- The place a multiplication loop over the counters of level `k` fills. -/
def tgt (k : ℕ) : Site → Pl
  | .comp r => .side (k + 1) r false
  | .bud _ => .c (k + 1)

/-- Where a multiplication loop over the counters of level `k` continues when it is done. -/
def after (k : ℕ) : Site → Loc Q
  | .comp false => .sp k (.comp true) .inner
  | .comp true => .bl (k + 1)
  | .bud false => .sp k (.bud true) .inner
  | .bud true => .bl (k + 1)

/-! ### Rules -/

/-- A rule of the vector addition system: a source and target control state, a precondition, an
add and delete list of facts, the tokens consumed (`dl`, at most one) and produced (`il`). -/
structure Rule (Q Φ : Type) where
  src : Loc Q
  pre : List Φ
  add : List Φ
  del : List Φ
  dl : List Pl
  il : List Pl
  dst : Loc Q

/-- **The rules of the amplifier** for the counter machine `P` and the number of levels `L`. -/
inductive IsRule (P : CM Q Φ) (L : ℕ) : Rule Q Φ → Prop
  | start : IsRule P L ⟨.start, [], [], [], [],
      [.side 0 false false, .side 0 false false, .side 0 true false, .side 0 true false], .bl 0⟩
  | bl0 : IsRule P L ⟨.bl 0, [], [], [], [], [.d 0, .c 0, .c 0, .c 0, .c 0], .bl 0⟩
  | blNext (k : ℕ) (hk : k < L) :
      IsRule P L ⟨.bl k, [], [], [], [], [], .sp k (.comp false) .inner⟩
  | blMain : IsRule P L ⟨.bl L, [], [], [], [], [], .main P.q0⟩
  | blBud (k : ℕ) (hk : k < L) :
      IsRule P L ⟨.bl (k + 1), [], [], [], [], [.d (k + 1)], .sp k (.bud false) .inner⟩
  | inner (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .inner, [], [], [], [.side k true false],
        [.side k true true, tgt k s], .sp k s .inner⟩
  | innerZ (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .inner, [], [], [], [.d k], [], .zt (.sj k s false) .A⟩
  | sjF (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.zt (.sj k s false) .B, [], [], [], [], [], .sp k s .restj⟩
  | restj (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .restj, [], [], [], [.side k true true],
        [.side k true false], .sp k s .restj⟩
  | restjZ (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .restj, [], [], [], [.d k], [], .zt (.sj k s true) .A⟩
  | sjT (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.zt (.sj k s true) .B, [], [], [], [.side k false false],
        [.side k false true], .sp k s .outer⟩
  | outerIn (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .outer, [], [], [], [], [], .sp k s .inner⟩
  | outerZ (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .outer, [], [], [], [.d k], [], .zt (.si k s false) .A⟩
  | siF (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.zt (.si k s false) .B, [], [], [], [], [], .sp k s .resti⟩
  | resti (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .resti, [], [], [], [.side k false true],
        [.side k false false], .sp k s .resti⟩
  | restiZ (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.sp k s .resti, [], [], [], [.d k], [], .zt (.si k s true) .A⟩
  | siT (k : ℕ) (s : Site) (hk : k < L) :
      IsRule P L ⟨.zt (.si k s true) .B, [], [], [], [], [], after k s⟩
  | zAA (z : ZI) : IsRule P L ⟨.zt z .A, [], [], [], [.c (z.lvl L)], [], .zt z .A'⟩
  | zA'A (z : ZI) : IsRule P L ⟨.zt z .A', [], [], [], [.side (z.lvl L) z.pr (!z.sd)],
      [.side (z.lvl L) z.pr z.sd], .zt z .A⟩
  | zAB (z : ZI) : IsRule P L ⟨.zt z .A, [], [], [], [], [], .zt z .B⟩
  | zBB (z : ZI) : IsRule P L ⟨.zt z .B, [], [], [], [.c (z.lvl L)], [], .zt z .B'⟩
  | zB'B (z : ZI) : IsRule P L ⟨.zt z .B', [], [], [], [.side (z.lvl L) z.pr z.sd],
      [.side (z.lvl L) z.pr (!z.sd)], .zt z .B⟩
  | mNop (t : CTr Q Φ) (ht : t ∈ P.trs) (hop : t.op = .nop) :
      IsRule P L ⟨.main t.src, t.pre, t.add, t.del, [], [], .main t.dst⟩
  | mInc (t : CTr Q Φ) (ht : t ∈ P.trs) (r : Bool) (hop : t.op = .inc r) :
      IsRule P L ⟨.main t.src, t.pre, t.add, t.del, [.side L r false], [.side L r true],
        .main t.dst⟩
  | mDec (t : CTr Q Φ) (ht : t ∈ P.trs) (r : Bool) (hop : t.op = .dec r) :
      IsRule P L ⟨.main t.src, t.pre, t.add, t.del, [.side L r true], [.side L r false],
        .main t.dst⟩
  | mZ (i : ℕ) (t : CTr Q Φ) (ht : P.trs[i]? = some t) (r : Bool) (hop : t.op = .zero r) :
      IsRule P L ⟨.main t.src, t.pre, [], [], [.d L], [], .zt (.m i r) .A⟩
  | mExit (i : ℕ) (t : CTr Q Φ) (ht : P.trs[i]? = some t) (r : Bool) (hop : t.op = .zero r) :
      IsRule P L ⟨.zt (.m i r) .B, [], t.add, t.del, [], [], .main t.dst⟩
  | toDrain : IsRule P L ⟨.main P.qf, [], [], [], [], [], .drain⟩
  | drain (k : ℕ) (r : Bool) (hk : k ≤ L) :
      IsRule P L ⟨.drain, [], [], [], [.side k r false], [], .drain⟩
  | toDone : IsRule P L ⟨.drain, [], [], [], [], [], .done⟩

/-! ### Configurations and steps -/

/-- A marking: the number of tokens on each place. -/
abbrev Mk : Type := Pl → ℕ

/-- Consume the tokens `dl` and produce the tokens `il`. -/
def mv (m : Mk) (dl il : List Pl) : Mk := fun x => m x - dl.count x + il.count x

/-- A configuration of the vector addition system. -/
abbrev ACfg (Q Φ : Type) : Type := Loc Q × Finset Φ × Mk

/-- **A step of the vector addition system.** -/
def AStep (P : CM Q Φ) (L : ℕ) (x y : ACfg Q Φ) : Prop :=
  ∃ ρ : Rule Q Φ, IsRule P L ρ ∧ x.1 = ρ.src ∧ (∀ f ∈ ρ.pre, f ∈ x.2.1) ∧
    (∀ p, ρ.dl.count p ≤ x.2.2 p) ∧
    y = (ρ.dst, upd x.2.1 ρ.add ρ.del, mv x.2.2 ρ.dl ρ.il)

/-- **Acceptance by the vector addition system**: from `start` with the facts `s0` and no tokens
to `done` with no tokens and facts containing `g`. -/
def AAcc (P : CM Q Φ) (L : ℕ) (s0 : Finset Φ) (g : List Φ) : Prop :=
  ∃ S : Finset Φ,
    Relation.ReflTransGen (AStep P L) (.start, s0, fun _ => 0) (.done, S, fun _ => 0) ∧
    ∀ f ∈ g, f ∈ S

end Amp

end HTN
