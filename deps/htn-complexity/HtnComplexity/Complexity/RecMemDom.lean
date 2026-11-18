import HtnComplexity.Complexity.AltMemDom
/-!
# A **recursive** encoding: the number of steps is not written into the description

`HtnComplexity/Complexity/AltMemDom.lean` encodes an alternating machine with a memory in a
domain description whose compound names carry the number of steps still to be made, so the
description has one copy of the machine per step and its size is *linear in the number of
steps*.  A machine of that shape makes one step per bit of its (padded) input, so the
computations it can describe are polynomially long.

This file drops the counter.  A configuration task is `rmCName q` — the state alone — and the
methods are

    0            ⟶  rmInit · rmCName start                  (the root)
    rmCName q    ⟶  rmFwd i · rmDName i                     (an existential step)
    rmDName i    ⟶  rmCName tgt · rmUndo i                   (… and its undoing)
    rmCName q    ⟶  rmGrd j · rmBrName j                    (a universal step)
    rmBrName j   ⟶  rmCName tgt₁ · rmCName tgt₂              (the branching)
    rmCName q    ⟶  rmAccA a                                 (acceptance)

The hierarchy is therefore **recursive**: `rmCName q` decomposes into `rmCName q'`, so the
refinements of the root task are of unbounded depth and the machine may run for any number of
steps — the description no longer bounds it.  Its size depends on the machine only, not on the
number of steps (`HtnComplexity/Complexity/RecMemFamily.lean`), and the input is read by
*explicit position*: a transition carries a list of input literals `(p, b)`, read as "the input
has the bit `b` at the position `p`", instead of consuming one bit per step.

The device that makes a mutable memory sound under universal branching is the one of
`AltMemDom.lean`, unchanged: every write is undone after the sub-computation it starts, so a
refinement of a configuration task returns the state it started in.

The acceptance predicate `HTN.Syn.RecAltMem.AccFromN` carries the **exact number of actions**
the encoding produces for the computation — one for an acceptance check, two more for an
existential step (the step and its undoing), and one more than the sum for a universal step.
This is what lets `HtnComplexity/Complexity/RecCounter.lean` exhibit a description of
linear size all of whose plans are exponentially long.

This file contains the machine, the names, the actions, the methods and the domain description
together with its membership in `TO-HTN` (it is totally ordered, and *not* acyclic — that is the
point); the simulation is in `HtnComplexity/Complexity/RecMemSim.lean`.
-/

namespace HTN

namespace Syn

open Binarise

/-! ### Recursive alternating machines with a memory -/

/-- An **input literal**: the input word has the bit `b` at the position `p`.  Positions are the
ones of `HTN.Syn.posFacts`, counted from the right. -/
abbrev InLit : Type := ℕ × Bool

/-- An **existential transition** of a recursive machine: source state, input guard, memory
guard, memory write, target state. -/
abbrev RmExTr : Type := ℕ × List InLit × List MemLit × MemWrite × ℕ

namespace RmExTr

/-- The source state. -/
def src (t : RmExTr) : ℕ := t.1

/-- The input guard. -/
def inG (t : RmExTr) : List InLit := t.2.1

/-- The memory guard. -/
def memG (t : RmExTr) : List MemLit := t.2.2.1

/-- The memory write. -/
def wr (t : RmExTr) : MemWrite := t.2.2.2.1

/-- The target state. -/
def tgt (t : RmExTr) : ℕ := t.2.2.2.2

end RmExTr

/-- A **universal transition** of a recursive machine: source state, input guard, memory guard,
and the two target states which both have to accept. -/
abbrev RmUnTr : Type := ℕ × List InLit × List MemLit × ℕ × ℕ

namespace RmUnTr

/-- The source state. -/
def src (t : RmUnTr) : ℕ := t.1

/-- The input guard. -/
def inG (t : RmUnTr) : List InLit := t.2.1

/-- The memory guard. -/
def memG (t : RmUnTr) : List MemLit := t.2.2.1

/-- The first target state. -/
def tgt₁ (t : RmUnTr) : ℕ := t.2.2.2.1

/-- The second target state. -/
def tgt₂ (t : RmUnTr) : ℕ := t.2.2.2.2

end RmUnTr

/-- An **accepting condition** of a recursive machine: a state, an input guard and a memory
guard. -/
abbrev RmAcc : Type := ℕ × List InLit × List MemLit

namespace RmAcc

/-- The accepting state. -/
def st (c : RmAcc) : ℕ := c.1

/-- The input guard. -/
def inG (c : RmAcc) : List InLit := c.2.1

/-- The memory guard. -/
def memG (c : RmAcc) : List MemLit := c.2.2

end RmAcc

/-- **A recursive alternating machine with a memory**: `mem` memory bits, an initial state, a
list of accepting conditions, and the existential and universal transitions.  Unlike
`HTN.Syn.BitAltMem` it consumes no input bit per step — it reads the input by position — so the
number of steps it makes is not bounded by the length of the input. -/
structure RecAltMem where
  /-- The number of memory bits. -/
  mem : ℕ
  /-- The initial state. -/
  start : ℕ
  /-- The accepting conditions. -/
  acc : List RmAcc
  /-- The existential transitions. -/
  ex : List RmExTr
  /-- The universal transitions. -/
  un : List RmUnTr

/-- **An input guard holds in the word**: every literal names a position of the word carrying
the bit the literal gives. -/
def InSat (W : List Bool) (g : List InLit) : Prop := ∀ p ∈ g, posFact p.1 p.2 ∈ posFacts W

/-- The positions a guard reads are below `n`. -/
def PosLt (n : ℕ) (g : List InLit) : Prop := ∀ p ∈ g, p.1 < n

namespace RecAltMem

/-- **The machine reads no position beyond `n`**: the well-formedness condition relating a
machine to the length of the words it runs on.  A machine that reads a position at or beyond the
end of the word could, in the encoding, read one of its own memory rails instead. -/
def PosBelow (M : RecAltMem) (n : ℕ) : Prop :=
  (∀ t ∈ M.ex, PosLt n (RmExTr.inG t)) ∧ (∀ t ∈ M.un, PosLt n (RmUnTr.inG t)) ∧
    (∀ c ∈ M.acc, PosLt n (RmAcc.inG c))

/-- **Acceptance from a state with a memory, counting the actions the encoding produces.**  An
accepting check is one action; an existential step is the step, the sub-computation and the
undoing of the write; a universal step is the guard and the two sub-computations. -/
inductive AccFromN (M : RecAltMem) (W : List Bool) : ℕ → ℕ → (ℕ → Bool) → Prop
  /-- Some accepting condition is met. -/
  | nil {q : ℕ} {μ : ℕ → Bool} {c : RmAcc} (hc : c ∈ M.acc) (hq : RmAcc.st c = q)
      (hin : InSat W (RmAcc.inG c)) (hg : MemSat M.mem μ (RmAcc.memG c)) : AccFromN M W 1 q μ
  /-- An existential transition writes one memory bit. -/
  | ex {k q : ℕ} {μ : ℕ → Bool} {t : RmExTr} (ht : t ∈ M.ex) (hq : RmExTr.src t = q)
      (hin : InSat W (RmExTr.inG t)) (hg : MemSat M.mem μ (RmExTr.memG t))
      (hw : (RmExTr.wr t).idx < M.mem) (hu : μ (RmExTr.wr t).idx = (RmExTr.wr t).old)
      (h' : AccFromN M W k (RmExTr.tgt t) (memUpd μ (RmExTr.wr t).idx (RmExTr.wr t).new)) :
      AccFromN M W (k + 2) q μ
  /-- A universal transition: both successors must accept, each with the memory the transition
  was taken in. -/
  | un {k₁ k₂ q : ℕ} {μ : ℕ → Bool} {t : RmUnTr} (ht : t ∈ M.un) (hq : RmUnTr.src t = q)
      (hin : InSat W (RmUnTr.inG t)) (hg : MemSat M.mem μ (RmUnTr.memG t))
      (h₁ : AccFromN M W k₁ (RmUnTr.tgt₁ t) μ) (h₂ : AccFromN M W k₂ (RmUnTr.tgt₂ t) μ) :
      AccFromN M W (k₁ + k₂ + 1) q μ

/-- **Acceptance**: some computation accepts, from the initial state with the empty memory. -/
def Accepts (M : RecAltMem) (W : List Bool) : Prop :=
  ∃ k, M.AccFromN W k M.start (fun _ => false)

theorem PosBelow.ex_getI {M : RecAltMem} {n i : ℕ} (h : M.PosBelow n) (hi : i < M.ex.length) :
    PosLt n (RmExTr.inG (M.ex.getI i)) := by
  refine h.1 _ ?_
  rw [List.getI_eq_getElem (l := M.ex) hi]
  exact List.getElem_mem hi

theorem PosBelow.un_getI {M : RecAltMem} {n j : ℕ} (h : M.PosBelow n) (hj : j < M.un.length) :
    PosLt n (RmUnTr.inG (M.un.getI j)) := by
  refine h.2.1 _ ?_
  rw [List.getI_eq_getElem (l := M.un) hj]
  exact List.getElem_mem hj

theorem PosBelow.acc_getI {M : RecAltMem} {n a : ℕ} (h : M.PosBelow n) (ha : a < M.acc.length) :
    PosLt n (RmAcc.inG (M.acc.getI a)) := by
  refine h.2.2 _ ?_
  rw [List.getI_eq_getElem (l := M.acc) ha]
  exact List.getElem_mem ha

end RecAltMem

/-! ### The names of the encoding

The root task is `0`; the three kinds of compound task are tagged by their residue mod `4`. -/

/-- **The configuration task**: the machine is in the state `q`. -/
def rmCName (q : ℕ) : ℕ := 4 * q + 1

/-- **The branching task** of the `j`-th universal transition. -/
def rmBrName (j : ℕ) : ℕ := 4 * j + 2

/-- **The undoing task**: run the sub-computation of the `i`-th existential transition, then undo
its write. -/
def rmDName (i : ℕ) : ℕ := 4 * i + 3

theorem rmCName_ne_zero (q : ℕ) : rmCName q ≠ 0 := by simp [rmCName]

theorem rmBrName_ne_zero (j : ℕ) : rmBrName j ≠ 0 := by simp [rmBrName]

theorem rmDName_ne_zero (i : ℕ) : rmDName i ≠ 0 := by simp [rmDName]

theorem rmCName_inj {q q' : ℕ} (h : rmCName q = rmCName q') : q = q' := by
  simp only [rmCName] at h; omega

theorem rmBrName_inj {j j' : ℕ} (h : rmBrName j = rmBrName j') : j = j' := by
  simp only [rmBrName] at h; omega

theorem rmDName_inj {i i' : ℕ} (h : rmDName i = rmDName i') : i = i' := by
  simp only [rmDName] at h; omega

theorem rmCName_ne_brName {q j : ℕ} : rmCName q ≠ rmBrName j := by
  simp only [rmCName, rmBrName]; omega

theorem rmCName_ne_dName {q i : ℕ} : rmCName q ≠ rmDName i := by
  simp only [rmCName, rmDName]; omega

theorem rmBrName_ne_dName {j i : ℕ} : rmBrName j ≠ rmDName i := by
  simp only [rmBrName, rmDName]; omega

/-! ### The actions of the encoding -/

variable {M : RecAltMem}

/-- The fact an input literal asks for. -/
def rmInFact (p : InLit) : ℕ := posFact p.1 p.2

/-- The action taking the `i`-th existential transition. -/
def rmFwd (i : ℕ) : ℕ := 4 * i

/-- The action undoing the write of the `i`-th existential transition. -/
def rmUndo (i : ℕ) : ℕ := 4 * i + 1

/-- The action guarding the `j`-th universal transition. -/
def rmGrd (j : ℕ) : ℕ := 4 * j + 2

/-- The action checking the `a`-th accepting condition. -/
def rmAccA (a : ℕ) : ℕ := 4 * a + 3

/-- The action initialising the memory. -/
def rmInit (M : RecAltMem) : ℕ := 4 * M.acc.length + 3

theorem rmFwd_inj {i i' : ℕ} (h : rmFwd i = rmFwd i') : i = i' := by
  simp only [rmFwd] at h; omega

theorem rmUndo_inj {i i' : ℕ} (h : rmUndo i = rmUndo i') : i = i' := by
  simp only [rmUndo] at h; omega

theorem rmGrd_inj {j j' : ℕ} (h : rmGrd j = rmGrd j') : j = j' := by
  simp only [rmGrd] at h; omega

theorem rmAccA_inj {a a' : ℕ} (h : rmAccA a = rmAccA a') : a = a' := by
  simp only [rmAccA] at h; omega

theorem rmFwd_ne_undo {i i' : ℕ} : rmFwd i ≠ rmUndo i' := by
  simp only [rmFwd, rmUndo]; omega

theorem rmFwd_ne_grd {i j : ℕ} : rmFwd i ≠ rmGrd j := by
  simp only [rmFwd, rmGrd]; omega

theorem rmFwd_ne_accA {i a : ℕ} : rmFwd i ≠ rmAccA a := by
  simp only [rmFwd, rmAccA]; omega

theorem rmUndo_ne_grd {i j : ℕ} : rmUndo i ≠ rmGrd j := by
  simp only [rmUndo, rmGrd]; omega

theorem rmUndo_ne_accA {i a : ℕ} : rmUndo i ≠ rmAccA a := by
  simp only [rmUndo, rmAccA]; omega

theorem rmGrd_ne_accA {j a : ℕ} : rmGrd j ≠ rmAccA a := by
  simp only [rmGrd, rmAccA]; omega

/-- The number of actions the domain lists. -/
def rmNumActs (M : RecAltMem) : ℕ :=
  4 * (M.ex.length + M.un.length + M.acc.length + 1)

/-- The data of a forward action. -/
def rmFwdData (M : RecAltMem) (n i : ℕ) : List ℕ × List ℕ × List ℕ :=
  ((M.ex.getI i).inG.map rmInFact ++
      amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.old
        :: (M.ex.getI i).memG.map (amRailOf n),
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.new],
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.old])

/-- The data of an undoing action: the write of the transition, read backwards. -/
def rmUndoData (M : RecAltMem) (n i : ℕ) : List ℕ × List ℕ × List ℕ :=
  ([amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.new],
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.old],
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.new])

/-- The data of the guard of a universal transition: it has no effect. -/
def rmGrdData (M : RecAltMem) (n j : ℕ) : List ℕ × List ℕ × List ℕ :=
  ((M.un.getI j).inG.map rmInFact ++ (M.un.getI j).memG.map (amRailOf n), [], [])

/-- The data of an accepting check: it has no effect. -/
def rmAccData (M : RecAltMem) (n a : ℕ) : List ℕ × List ℕ × List ℕ :=
  ((M.acc.getI a).inG.map rmInFact ++ (M.acc.getI a).memG.map (amRailOf n), [], [])

/-- The data of the initialising action: every memory bit is set to `false`. -/
def rmInitData (M : RecAltMem) (n : ℕ) : List ℕ × List ℕ × List ℕ :=
  ([], (List.range M.mem).map fun i => amRail n i false, [])

/-- **The data of the action `j`.**  The residue of `j` mod `4` says which kind of action it
is. -/
def rmActData (M : RecAltMem) (n j : ℕ) : List ℕ × List ℕ × List ℕ :=
  if j % 4 = 0 then rmFwdData M n (j / 4)
  else if j % 4 = 1 then rmUndoData M n (j / 4)
  else if j % 4 = 2 then rmGrdData M n (j / 4)
  else if j / 4 < M.acc.length then rmAccData M n (j / 4)
  else rmInitData M n

/-- **The actions of the encoding.** -/
def rmActions (M : RecAltMem) (n : ℕ) : List ActionDesc :=
  (List.range (rmNumActs M)).map fun j => (j, rmActData M n j)

/-! ### The action indices decode -/

theorem rmFwd_lt {i : ℕ} (hi : i < M.ex.length) : rmFwd i < rmNumActs M := by
  simp only [rmFwd, rmNumActs]; omega

theorem rmUndo_lt {i : ℕ} (hi : i < M.ex.length) : rmUndo i < rmNumActs M := by
  simp only [rmUndo, rmNumActs]; omega

theorem rmGrd_lt {j : ℕ} (hj : j < M.un.length) : rmGrd j < rmNumActs M := by
  simp only [rmGrd, rmNumActs]; omega

theorem rmAccA_lt {a : ℕ} (ha : a < M.acc.length) : rmAccA a < rmNumActs M := by
  simp only [rmAccA, rmNumActs]; omega

theorem rmInit_lt : rmInit M < rmNumActs M := by
  simp only [rmInit, rmNumActs]; omega

theorem rmActData_fwd (n i : ℕ) : rmActData M n (rmFwd i) = rmFwdData M n i := by
  have h4 : rmFwd i % 4 = 0 := by simp [rmFwd, Nat.mul_mod_right]
  have hdiv : rmFwd i / 4 = i := by simp [rmFwd, Nat.mul_div_cancel_left _ (by omega : 0 < 4)]
  rw [rmActData, if_pos h4, hdiv]

theorem rmActData_undo (n i : ℕ) : rmActData M n (rmUndo i) = rmUndoData M n i := by
  have h4 : rmUndo i % 4 = 1 := by simp [rmUndo]
  have hdiv : rmUndo i / 4 = i := by simp [rmUndo, Nat.mul_add_div (by omega : 0 < 4)]
  rw [rmActData, if_neg (by omega), if_pos h4, hdiv]

theorem rmActData_grd (n j : ℕ) : rmActData M n (rmGrd j) = rmGrdData M n j := by
  have h4 : rmGrd j % 4 = 2 := by simp [rmGrd]
  have hdiv : rmGrd j / 4 = j := by simp [rmGrd, Nat.mul_add_div (by omega : 0 < 4)]
  rw [rmActData, if_neg (by omega), if_neg (by omega), if_pos h4, hdiv]

theorem rmActData_acc {n a : ℕ} (ha : a < M.acc.length) :
    rmActData M n (rmAccA a) = rmAccData M n a := by
  have h4 : rmAccA a % 4 = 3 := by simp [rmAccA]
  have hdiv : rmAccA a / 4 = a := by simp [rmAccA, Nat.mul_add_div (by omega : 0 < 4)]
  rw [rmActData, if_neg (by omega), if_neg (by omega), if_neg (by omega), hdiv, if_pos ha]

theorem rmActData_init (n : ℕ) : rmActData M n (rmInit M) = rmInitData M n := by
  have h4 : rmInit M % 4 = 3 := by simp [rmInit]
  have hdiv : rmInit M / 4 = M.acc.length := by
    simp [rmInit, Nat.mul_add_div (by omega : 0 < 4)]
  rw [rmActData, if_neg (by omega), if_neg (by omega), if_neg (by omega), hdiv, if_neg (by omega)]

/-! ### The methods and the domain -/

/-- The root method: initialise the memory, then run the machine. -/
def rmRootMethods (M : RecAltMem) : List MethodDesc :=
  [(0, pairBody (Sum.inl (rmInit M)) (Sum.inr (rmCName M.start)))]

/-- The methods of the existential transitions: take the transition, then undo it. -/
def rmExMethods (M : RecAltMem) : List MethodDesc :=
  (List.range M.ex.length).map fun i =>
    (rmCName (M.ex.getI i).src, pairBody (Sum.inl (rmFwd i)) (Sum.inr (rmDName i)))

/-- The methods of the undoing tasks: the sub-computation, then the inverse write. -/
def rmDMethods (M : RecAltMem) : List MethodDesc :=
  (List.range M.ex.length).map fun i =>
    (rmDName i, pairBody (Sum.inr (rmCName (M.ex.getI i).tgt)) (Sum.inl (rmUndo i)))

/-- The methods of the universal transitions: check the guard, then branch. -/
def rmUnMethods (M : RecAltMem) : List MethodDesc :=
  (List.range M.un.length).map fun j =>
    (rmCName (M.un.getI j).src, pairBody (Sum.inl (rmGrd j)) (Sum.inr (rmBrName j)))

/-- The branching methods: a universal branch is refined into *both* of its successors. -/
def rmBrMethods (M : RecAltMem) : List MethodDesc :=
  (List.range M.un.length).map fun j =>
    (rmBrName j, pairBody (Sum.inr (rmCName (M.un.getI j).tgt₁))
      (Sum.inr (rmCName (M.un.getI j).tgt₂)))

/-- The accepting methods. -/
def rmAccMethods (M : RecAltMem) : List MethodDesc :=
  (List.range M.acc.length).map fun a => (rmCName (M.acc.getI a).st, singleBody (rmAccA a))

/-- **The domain description of the recursive encoding** for the words of length `n`. -/
def rmDom (M : RecAltMem) (n : ℕ) : DomDesc :=
  (rmActions M n,
    rmRootMethods M ++ rmExMethods M ++ rmDMethods M ++ rmUnMethods M ++ rmBrMethods M ++
      rmAccMethods M)

@[simp] theorem rmDom_actions (n : ℕ) : (rmDom M n).actions = rmActions M n := rfl

@[simp] theorem rmDom_methods (n : ℕ) :
    (rmDom M n).methods =
      rmRootMethods M ++ rmExMethods M ++ rmDMethods M ++ rmUnMethods M ++ rmBrMethods M ++
        rmAccMethods M := rfl

theorem mem_rmRootMethods {e : MethodDesc} (he : e ∈ rmRootMethods M) :
    e = (0, pairBody (Sum.inl (rmInit M)) (Sum.inr (rmCName M.start))) := by
  simpa [rmRootMethods] using he

theorem mem_rmExMethods {e : MethodDesc} (he : e ∈ rmExMethods M) :
    ∃ i < M.ex.length,
      e = (rmCName (M.ex.getI i).src, pairBody (Sum.inl (rmFwd i)) (Sum.inr (rmDName i))) := by
  simp only [rmExMethods, List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i, hi, rfl⟩

theorem mem_rmDMethods {e : MethodDesc} (he : e ∈ rmDMethods M) :
    ∃ i < M.ex.length,
      e = (rmDName i,
        pairBody (Sum.inr (rmCName (M.ex.getI i).tgt)) (Sum.inl (rmUndo i))) := by
  simp only [rmDMethods, List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i, hi, rfl⟩

theorem mem_rmUnMethods {e : MethodDesc} (he : e ∈ rmUnMethods M) :
    ∃ j < M.un.length,
      e = (rmCName (M.un.getI j).src, pairBody (Sum.inl (rmGrd j)) (Sum.inr (rmBrName j))) := by
  simp only [rmUnMethods, List.mem_map, List.mem_range] at he
  obtain ⟨j, hj, rfl⟩ := he
  exact ⟨j, hj, rfl⟩

theorem mem_rmBrMethods {e : MethodDesc} (he : e ∈ rmBrMethods M) :
    ∃ j < M.un.length,
      e = (rmBrName j, pairBody (Sum.inr (rmCName (M.un.getI j).tgt₁))
        (Sum.inr (rmCName (M.un.getI j).tgt₂))) := by
  simp only [rmBrMethods, List.mem_map, List.mem_range] at he
  obtain ⟨j, hj, rfl⟩ := he
  exact ⟨j, hj, rfl⟩

theorem mem_rmAccMethods {e : MethodDesc} (he : e ∈ rmAccMethods M) :
    ∃ a < M.acc.length, e = (rmCName (M.acc.getI a).st, singleBody (rmAccA a)) := by
  simp only [rmAccMethods, List.mem_map, List.mem_range] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact ⟨a, ha, rfl⟩

theorem mem_rmDom_methods {n : ℕ} {e : MethodDesc} (he : e ∈ (rmDom M n).methods) :
    e ∈ rmRootMethods M ∨ e ∈ rmExMethods M ∨ e ∈ rmDMethods M ∨ e ∈ rmUnMethods M ∨
      e ∈ rmBrMethods M ∨ e ∈ rmAccMethods M := by
  rw [rmDom_methods] at he
  simp only [List.mem_append] at he
  tauto

theorem mem_rmDom_of_root {n : ℕ} {e : MethodDesc} (h : e ∈ rmRootMethods M) :
    e ∈ (rmDom M n).methods := by
  rw [rmDom_methods]; simp only [List.mem_append]; tauto

theorem mem_rmDom_of_ex {n : ℕ} {e : MethodDesc} (h : e ∈ rmExMethods M) :
    e ∈ (rmDom M n).methods := by
  rw [rmDom_methods]; simp only [List.mem_append]; tauto

theorem mem_rmDom_of_d {n : ℕ} {e : MethodDesc} (h : e ∈ rmDMethods M) :
    e ∈ (rmDom M n).methods := by
  rw [rmDom_methods]; simp only [List.mem_append]; tauto

theorem mem_rmDom_of_un {n : ℕ} {e : MethodDesc} (h : e ∈ rmUnMethods M) :
    e ∈ (rmDom M n).methods := by
  rw [rmDom_methods]; simp only [List.mem_append]; tauto

theorem mem_rmDom_of_br {n : ℕ} {e : MethodDesc} (h : e ∈ rmBrMethods M) :
    e ∈ (rmDom M n).methods := by
  rw [rmDom_methods]; simp only [List.mem_append]; tauto

theorem mem_rmDom_of_acc {n : ℕ} {e : MethodDesc} (h : e ∈ rmAccMethods M) :
    e ∈ (rmDom M n).methods := by
  rw [rmDom_methods]; simp only [List.mem_append]; tauto

/-! ### The domain is totally ordered -/

theorem rmDom_methodsTO (n : ℕ) : (rmDom M n).MethodsTO := by
  intro e he
  rcases mem_rmDom_methods he with he | he | he | he | he | he
  · rw [mem_rmRootMethods he]
    exact pairBody_isTO _ _
  · obtain ⟨i, -, rfl⟩ := mem_rmExMethods he
    exact pairBody_isTO _ _
  · obtain ⟨i, -, rfl⟩ := mem_rmDMethods he
    exact pairBody_isTO _ _
  · obtain ⟨j, -, rfl⟩ := mem_rmUnMethods he
    exact pairBody_isTO _ _
  · obtain ⟨j, -, rfl⟩ := mem_rmBrMethods he
    exact pairBody_isTO _ _
  · obtain ⟨a, -, rfl⟩ := mem_rmAccMethods he
    exact singleBody_isTO _

theorem rmDom_domOk (n : ℕ) : SynClass.TO_HTN_root.domOk (rmDom M n) := rmDom_methodsTO n

/-! ### The bodies the domain offers -/

/-- **The bodies of the root task.** -/
theorem seqBody_rmDom_root_iff {n : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (rmDom M n).toDomain.SeqBody 0 xs ↔
      xs = [Sum.inl (rmInit M), Sum.inr (rmCName M.start)] := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_rmDom_methods he with he | he | he | he | he | he
    · rw [mem_rmRootMethods he] at hbody
      exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody
    · obtain ⟨i, -, rfl⟩ := mem_rmExMethods he
      exact absurd hc (rmCName_ne_zero _)
    · obtain ⟨i, -, rfl⟩ := mem_rmDMethods he
      exact absurd hc (rmDName_ne_zero _)
    · obtain ⟨j, -, rfl⟩ := mem_rmUnMethods he
      exact absurd hc (rmCName_ne_zero _)
    · obtain ⟨j, -, rfl⟩ := mem_rmBrMethods he
      exact absurd hc (rmBrName_ne_zero _)
    · obtain ⟨a, -, rfl⟩ := mem_rmAccMethods he
      exact absurd hc (rmCName_ne_zero _)
  · rintro rfl
    refine ⟨(0, pairBody (Sum.inl (rmInit M)) (Sum.inr (rmCName M.start))),
      mem_rmDom_of_root (by simp [rmRootMethods]), rfl, ?_⟩
    exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl

/-- **The bodies of a configuration task.** -/
theorem seqBody_rmDom_c_iff {n q : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (rmDom M n).toDomain.SeqBody (rmCName q) xs ↔
      (∃ i < M.ex.length, (M.ex.getI i).src = q ∧
        xs = [Sum.inl (rmFwd i), Sum.inr (rmDName i)]) ∨
      (∃ j < M.un.length, (M.un.getI j).src = q ∧
        xs = [Sum.inl (rmGrd j), Sum.inr (rmBrName j)]) ∨
      (∃ a < M.acc.length, (M.acc.getI a).st = q ∧ xs = [Sum.inl (rmAccA a)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_rmDom_methods he with he | he | he | he | he | he
    · rw [mem_rmRootMethods he] at hc
      exact absurd hc.symm (rmCName_ne_zero _)
    · obtain ⟨i, hi, rfl⟩ := mem_rmExMethods he
      exact Or.inl ⟨i, hi, rmCName_inj hc,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · obtain ⟨i, -, rfl⟩ := mem_rmDMethods he
      exact absurd hc rmCName_ne_dName.symm
    · obtain ⟨j, hj, rfl⟩ := mem_rmUnMethods he
      exact Or.inr (Or.inl ⟨j, hj, rmCName_inj hc,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩)
    · obtain ⟨j, -, rfl⟩ := mem_rmBrMethods he
      exact absurd hc rmCName_ne_brName.symm
    · obtain ⟨a, ha, rfl⟩ := mem_rmAccMethods he
      exact Or.inr (Or.inr ⟨a, ha, rmCName_inj hc,
        (Method.hasSeqBody_iff_of_isSeqNet (singleBody_isSeqNet _)).1 hbody⟩)
  · rintro (⟨i, hi, hq, rfl⟩ | ⟨j, hj, hq, rfl⟩ | ⟨a, ha, hq, rfl⟩)
    · refine ⟨(rmCName (M.ex.getI i).src,
        pairBody (Sum.inl (rmFwd i)) (Sum.inr (rmDName i))), mem_rmDom_of_ex ?_, by rw [hq],
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
      simp only [rmExMethods, List.mem_map, List.mem_range]
      exact ⟨i, hi, rfl⟩
    · refine ⟨(rmCName (M.un.getI j).src,
        pairBody (Sum.inl (rmGrd j)) (Sum.inr (rmBrName j))), mem_rmDom_of_un ?_, by rw [hq],
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
      simp only [rmUnMethods, List.mem_map, List.mem_range]
      exact ⟨j, hj, rfl⟩
    · refine ⟨(rmCName (M.acc.getI a).st, singleBody (rmAccA a)), mem_rmDom_of_acc ?_, by rw [hq],
        (Method.hasSeqBody_iff_of_isSeqNet (singleBody_isSeqNet _)).2 rfl⟩
      simp only [rmAccMethods, List.mem_map, List.mem_range]
      exact ⟨a, ha, rfl⟩

/-- **The bodies of an undoing task.** -/
theorem seqBody_rmDom_d_iff {n i : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (rmDom M n).toDomain.SeqBody (rmDName i) xs ↔
      (i < M.ex.length ∧
        xs = [Sum.inr (rmCName (M.ex.getI i).tgt), Sum.inl (rmUndo i)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_rmDom_methods he with he | he | he | he | he | he
    · rw [mem_rmRootMethods he] at hc
      exact absurd hc.symm (rmDName_ne_zero _)
    · obtain ⟨i', -, rfl⟩ := mem_rmExMethods he
      exact absurd hc rmCName_ne_dName
    · obtain ⟨i', hi', rfl⟩ := mem_rmDMethods he
      have : i' = i := rmDName_inj hc
      subst this
      exact ⟨hi', (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · obtain ⟨j, -, rfl⟩ := mem_rmUnMethods he
      exact absurd hc rmCName_ne_dName
    · obtain ⟨j, -, rfl⟩ := mem_rmBrMethods he
      exact absurd hc rmBrName_ne_dName
    · obtain ⟨a, -, rfl⟩ := mem_rmAccMethods he
      exact absurd hc rmCName_ne_dName
  · rintro ⟨hi, rfl⟩
    refine ⟨(rmDName i,
      pairBody (Sum.inr (rmCName (M.ex.getI i).tgt)) (Sum.inl (rmUndo i))),
      mem_rmDom_of_d ?_, rfl,
      (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
    simp only [rmDMethods, List.mem_map, List.mem_range]
    exact ⟨i, hi, rfl⟩

/-- **The bodies of a branching task.** -/
theorem seqBody_rmDom_br_iff {n j : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (rmDom M n).toDomain.SeqBody (rmBrName j) xs ↔
      (j < M.un.length ∧
        xs = [Sum.inr (rmCName (M.un.getI j).tgt₁), Sum.inr (rmCName (M.un.getI j).tgt₂)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_rmDom_methods he with he | he | he | he | he | he
    · rw [mem_rmRootMethods he] at hc
      exact absurd hc.symm (rmBrName_ne_zero _)
    · obtain ⟨i, -, rfl⟩ := mem_rmExMethods he
      exact absurd hc rmCName_ne_brName
    · obtain ⟨i, -, rfl⟩ := mem_rmDMethods he
      exact absurd hc rmBrName_ne_dName.symm
    · obtain ⟨j', -, rfl⟩ := mem_rmUnMethods he
      exact absurd hc rmCName_ne_brName
    · obtain ⟨j', hj', rfl⟩ := mem_rmBrMethods he
      have : j' = j := rmBrName_inj hc
      subst this
      exact ⟨hj', (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · obtain ⟨a, -, rfl⟩ := mem_rmAccMethods he
      exact absurd hc rmCName_ne_brName
  · rintro ⟨hj, rfl⟩
    refine ⟨(rmBrName j, pairBody (Sum.inr (rmCName (M.un.getI j).tgt₁))
      (Sum.inr (rmCName (M.un.getI j).tgt₂))), mem_rmDom_of_br ?_, rfl,
      (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
    simp only [rmBrMethods, List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩

/-! ### The preconditions and the effects of the actions -/

theorem lookup_rmActions {n j : ℕ} (hj : j < rmNumActs M) :
    (rmActions M n).lookup j = some (rmActData M n j) :=
  lookup_range_map (fun j => rmActData M n j) hj

theorem prec_rmDom {n j : ℕ} (hj : j < rmNumActs M) :
    (rmDom M n).prec j = {f | f ∈ (rmActData M n j).1} := by
  simp only [DomDesc.prec, rmDom_actions, lookup_rmActions hj]
  rfl

theorem add_rmDom {n j : ℕ} (hj : j < rmNumActs M) :
    (rmDom M n).add j = {f | f ∈ (rmActData M n j).2.1} := by
  simp only [DomDesc.add, rmDom_actions, lookup_rmActions hj]
  rfl

theorem del_rmDom {n j : ℕ} (hj : j < rmNumActs M) :
    (rmDom M n).del j = {f | f ∈ (rmActData M n j).2.2} := by
  simp only [DomDesc.del, rmDom_actions, lookup_rmActions hj]
  rfl

end Syn

end HTN
