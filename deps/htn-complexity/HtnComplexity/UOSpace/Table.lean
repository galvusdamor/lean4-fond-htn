import HtnComplexity.UOSpace.Bound
import ComplexityTheory.UOSpace.Counter
import HtnComplexity.Space.StripsSystem
import HtnComplexity.Space.TblSolver
/-!
# Unordered HTN with bounded counters, as an action table

For the polynomial-space upper bound of unordered HTN with a rooted instance we simulate the
abstract progression system `HTN.Syn.uoSys d q` — configurations `(state, multiset of open task
labels)` — by an action table (`HTN.Space.Row`, a `STRIPS` domain written out) whose states carry

* the facts of the planning state, renamed `v ↦ 4 v + 2`;
* for every task label of the domain, a **binary counter of `W` bits** holding the number of open
  tasks with that label, bit `i` being represented by one of the two facts "bit `i` is one" and
  "bit `i` is zero";
* a control fact: `idle`, or "the method number `k` is being unfolded and its first `p` subtasks
  have been added".

The renaming is the one of `HtnComplexity/Space/RegRename.lean`: the instance facts are
`4 v + 2`, the initial compound task `c` is `4 c + 3`, and the goal marker is `0`.  Our own facts
are `4 k + 4`.  So the initial state and goal of the table problem are literally
`HTN.Space.regInitR q` and `HTN.Space.regGoalR q`, which the machine of
`HtnComplexity/Space/InstMachine.lean` reads off the code of the instance.

The rows (`HTN.UOTbl.uoTbl d W`):

* `startRow c` — consume the root fact `4 c + 3`, set every counter to `0` except the counter of
  `(true, c)`, which becomes `1`, and become `idle`;
* `exeRow l i` — for a primitive label `l = (false, a)`: apply the action `a` and decrement the
  counter of `l`, whose lowest one bit is `i`;
* `decRow k e i` — start unfolding method number `k` (that is `e`): decrement the counter of its
  head;
* `addRow k p l i` — add the `p`-th subtask `l` of method `k`: increment its counter, whose
  lowest zero bit is `i`;
* `endRow k n` — all `n` subtasks of method `k` are added: become `idle` again;
* `finRow` — every counter is zero: add the goal marker `0` and stop.

`HTN.UOTbl.tblSize_uoTbl_le` bounds the size of the table polynomially in `d.size + W`.
-/

namespace HTN

namespace UOTbl

open Syn Space

/-! ### Facts -/

/-- The goal marker. -/
def fDone : ℕ := 0

/-- A fact of the planning state. -/
def fSt (v : ℕ) : ℕ := 4 * v + 2

/-- The root fact. -/
def fRoot (c : ℕ) : ℕ := 4 * c + 3

/-- An internal fact. -/
def fI (k : ℕ) : ℕ := 4 * k + 4

/-- The code of `idle`. -/
def kIdle : ℕ := 0

/-- The code of the control fact "method `k`, `p` subtasks added". -/
def kCtl (k p : ℕ) : ℕ := 3 * Nat.pair k p + 1

/-- The code of the fact "bit `i` of the counter of `l` has value `v`". -/
def kBit (l : Bool × ℕ) (i : ℕ) (v : Bool) : ℕ :=
  3 * Nat.pair (Nat.pair (cond l.1 1 0) l.2) (Nat.pair i (cond v 1 0)) + 2

/-- The bit fact. -/
def bitF (l : Bool × ℕ) (i : ℕ) (v : Bool) : ℕ := fI (kBit l i v)

@[simp] theorem fI_inj {k k' : ℕ} : fI k = fI k' ↔ k = k' := by unfold fI; omega
@[simp] theorem fSt_inj {v v' : ℕ} : fSt v = fSt v' ↔ v = v' := by unfold fSt; omega
@[simp] theorem fRoot_inj {c c' : ℕ} : fRoot c = fRoot c' ↔ c = c' := by unfold fRoot; omega
@[simp] theorem fI_ne_fSt (k v : ℕ) : fI k ≠ fSt v := by unfold fI fSt; omega
@[simp] theorem fSt_ne_fI (k v : ℕ) : fSt v ≠ fI k := by unfold fI fSt; omega
@[simp] theorem fI_ne_fRoot (k c : ℕ) : fI k ≠ fRoot c := by unfold fI fRoot; omega
@[simp] theorem fRoot_ne_fI (k c : ℕ) : fRoot c ≠ fI k := by unfold fI fRoot; omega
@[simp] theorem fSt_ne_fRoot (v c : ℕ) : fSt v ≠ fRoot c := by unfold fSt fRoot; omega
@[simp] theorem fRoot_ne_fSt (v c : ℕ) : fRoot c ≠ fSt v := by unfold fSt fRoot; omega
@[simp] theorem fDone_ne_fI (k : ℕ) : fDone ≠ fI k := by unfold fDone fI; omega
@[simp] theorem fI_ne_fDone (k : ℕ) : fI k ≠ fDone := by unfold fDone fI; omega
@[simp] theorem fDone_ne_fSt (v : ℕ) : fDone ≠ fSt v := by unfold fDone fSt; omega
@[simp] theorem fSt_ne_fDone (v : ℕ) : fSt v ≠ fDone := by unfold fDone fSt; omega
@[simp] theorem fDone_ne_fRoot (c : ℕ) : fDone ≠ fRoot c := by unfold fDone fRoot; omega
@[simp] theorem fRoot_ne_fDone (c : ℕ) : fRoot c ≠ fDone := by unfold fDone fRoot; omega

@[simp] theorem kIdle_ne_kCtl (k p : ℕ) : kIdle ≠ kCtl k p := by unfold kIdle kCtl; omega
@[simp] theorem kCtl_ne_kIdle (k p : ℕ) : kCtl k p ≠ kIdle := by unfold kIdle kCtl; omega
@[simp] theorem kIdle_ne_kBit (l : Bool × ℕ) (i : ℕ) (v : Bool) : kIdle ≠ kBit l i v := by
  unfold kIdle kBit; omega
@[simp] theorem kBit_ne_kIdle (l : Bool × ℕ) (i : ℕ) (v : Bool) : kBit l i v ≠ kIdle := by
  unfold kIdle kBit; omega
@[simp] theorem kCtl_ne_kBit (k p : ℕ) (l : Bool × ℕ) (i : ℕ) (v : Bool) :
    kCtl k p ≠ kBit l i v := by unfold kCtl kBit; omega
@[simp] theorem kBit_ne_kCtl (k p : ℕ) (l : Bool × ℕ) (i : ℕ) (v : Bool) :
    kBit l i v ≠ kCtl k p := by unfold kCtl kBit; omega

@[simp] theorem kCtl_inj {k p k' p' : ℕ} : kCtl k p = kCtl k' p' ↔ k = k' ∧ p = p' := by
  unfold kCtl
  constructor
  · intro h
    have : Nat.pair k p = Nat.pair k' p' := by omega
    exact Nat.pair_eq_pair.1 this
  · rintro ⟨rfl, rfl⟩; rfl

theorem cond_inj {b b' : Bool} : cond b 1 0 = cond b' (1 : ℕ) 0 ↔ b = b' := by
  cases b <;> cases b' <;> simp

@[simp] theorem kBit_inj {l l' : Bool × ℕ} {i i' : ℕ} {v v' : Bool} :
    kBit l i v = kBit l' i' v' ↔ l = l' ∧ i = i' ∧ v = v' := by
  unfold kBit
  constructor
  · intro h
    have h1 : Nat.pair (Nat.pair (cond l.1 1 0) l.2) (Nat.pair i (cond v 1 0)) =
        Nat.pair (Nat.pair (cond l'.1 1 0) l'.2) (Nat.pair i' (cond v' 1 0)) := by omega
    rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair] at h1
    obtain ⟨⟨h2, h3⟩, h4, h5⟩ := h1
    exact ⟨Prod.ext (cond_inj.1 h2) h3, h4, cond_inj.1 h5⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

@[simp] theorem bitF_inj {l l' : Bool × ℕ} {i i' : ℕ} {v v' : Bool} :
    bitF l i v = bitF l' i' v' ↔ l = l' ∧ i = i' ∧ v = v' := by
  unfold bitF; rw [fI_inj, kBit_inj]

/-! ### The domain data -/

/-- The labels of the subtasks of a method, as `HTN.Syn.uoSys` reads them. -/
def body (e : MethodDesc) : List (Bool × ℕ) := e.2.ids.dedup.map e.2.lblPair

/-- The task labels of a domain: method heads and subtask labels. -/
def labs (d : DomDesc) : List (Bool × ℕ) :=
  d.methods.map (fun e => (true, e.1)) ++ d.methods.flatMap body

/-! ### Rows -/

/-- The facts "bit `j` has value `v`" for `j < i`. -/
def lowF (l : Bool × ℕ) (i : ℕ) (v : Bool) : List ℕ := (List.range i).map fun j => bitF l j v

/-- The bit pattern of a counter whose lowest one bit is `i`. -/
def decPre (l : Bool × ℕ) (i : ℕ) : List ℕ := bitF l i true :: lowF l i false

/-- The same counter after a decrement. -/
def decAdd (l : Bool × ℕ) (i : ℕ) : List ℕ := bitF l i false :: lowF l i true

/-- All counters zero. -/
def zerosAll (L : List (Bool × ℕ)) (W : ℕ) : List ℕ :=
  L.flatMap fun l => (List.range W).map fun i => bitF l i false

/-- **Start**: consume the root fact. -/
def startRow (L : List (Bool × ℕ)) (W c : ℕ) : Row :=
  ([fRoot c], fI kIdle :: bitF (true, c) 0 true ::
    (zerosAll L W).filter (fun f => f ≠ bitF (true, c) 0 false), [fRoot c])

/-- **Execute** the action of a primitive label, decrementing its counter. -/
def exeRow (d : DomDesc) (l : Bool × ℕ) (i : ℕ) : Row :=
  (fI kIdle :: decPre l i ++ (actOf d l.2).1.map fSt,
    decAdd l i ++ (actOf d l.2).2.1.map fSt,
    decPre l i ++ (actOf d l.2).2.2.map fSt)

/-- **Start unfolding** method number `k`, decrementing the counter of its head. -/
def decRow (k : ℕ) (e : MethodDesc) (i : ℕ) : Row :=
  (fI kIdle :: decPre (true, e.1) i, fI (kCtl k 0) :: decAdd (true, e.1) i,
    fI kIdle :: decPre (true, e.1) i)

/-- **Add** the `p`-th subtask `l` of method number `k`, incrementing its counter. -/
def addRow (k p : ℕ) (l : Bool × ℕ) (i : ℕ) : Row :=
  (fI (kCtl k p) :: decAdd l i, fI (kCtl k (p + 1)) :: decPre l i, fI (kCtl k p) :: decAdd l i)

/-- **End** unfolding method number `k` with `n` subtasks. -/
def endRow (k n : ℕ) : Row := ([fI (kCtl k n)], [fI kIdle], [fI (kCtl k n)])

/-- **Finish**: every counter is zero. -/
def finRow (L : List (Bool × ℕ)) (W : ℕ) : Row := (fI kIdle :: zerosAll L W, [fDone], [fI kIdle])

/-- The rows of method number `k`. -/
def methRows (W : ℕ) (x : MethodDesc × ℕ) : List Row :=
  (List.range W).map (decRow x.2 x.1) ++
    ((body x.1).zipIdx.flatMap fun y => (List.range W).map (addRow x.2 y.2 y.1)) ++
    [endRow x.2 (body x.1).length]

/-- **The action table of a domain with counters of `W` bits.** -/
def uoTbl (d : DomDesc) (W : ℕ) : List Row :=
  (d.methods.map fun e => startRow (labs d) W e.1) ++
    ((labs d).filter (fun l => l.1 = false)).flatMap (fun l => (List.range W).map (exeRow d l)) ++
    d.methods.zipIdx.flatMap (methRows W) ++
    [finRow (labs d) W]

end UOTbl

end HTN
