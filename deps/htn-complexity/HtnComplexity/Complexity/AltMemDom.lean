import HtnComplexity.Complexity.AltFamily
import HtnComplexity.Complexity.StateFamily
/-!
# Alternation *with a memory*: the domain description

`HtnComplexity/Complexity/AltFamily.lean` puts an **alternating** automaton into the fixed
domain description, and `HtnComplexity/Complexity/StateFamily.lean` puts a machine with a
**memory** — the planning state — into it.  `NOTES.md` §5.5(1) records the combination of the two
as the shape the hardness construction of Theorem 6.1 of the complexity paper would need, and as
the one thing the two files do not give: the guards of `altDom` have no effect precisely so that
the two branches of a universal step inspect the same state, and with a mutable state that
argument breaks down — the first branch would hand its own final state to the second one.

This file and `HtnComplexity/Complexity/AltMemFamily.lean` supply the combination.  The
device is **backtracking**: every step of the machine is undone after the sub-computation it
starts has finished, so that a refinement of a configuration task is a plan which *returns the
state it started in*.  Universal branching is then sound with a mutable memory: the two branches
are run one after the other, and the second one starts in the state the first one restored.

    0                  ⟶  amInit · amCName n q₀                      (the root)
    amCName (k+1) q    ⟶  amFwd k i · amDName k i                    (an existential step)
    amDName k i        ⟶  amCName k q' · amUndo i                    (… and its undoing)
    amCName (k+1) q    ⟶  amGrd k j · amBrName k q₁ q₂               (a universal step)
    amBrName k q₁ q₂   ⟶  amCName k q₁ · amCName k q₂                (the branching)
    amCName 0 q        ⟶  amAcc a                                    (acceptance)

Every method body is a chain of two tasks, so the domain is totally ordered; the rank
`3k`, `3k+1`, `3k+1` of a configuration, a branching and an undoing task makes it acyclic; and
its size is linear in `n`.  The memory is *dual-railed* — the bit `i` is held by one of the two
facts `amRail n i false`, `amRail n i true`, which are position facts of
`HtnComplexity/Complexity/PosFamily.lean` for positions beyond the input word, hence free —
and every write carries the value it overwrites, which is what makes the undoing action an exact
inverse.

This file contains the machine, the names, the actions, the methods and the domain description
together with its membership in `TO-HTN-AC`; the simulation and the hardness family are in
`AltMemFamily.lean`.
-/

namespace HTN

namespace Syn

open Binarise

/-! ### Alternating machines with a memory -/

/-- A **memory literal**: the memory bit `i` holds the value `b`. -/
abbrev MemLit : Type := ℕ × Bool

/-- A **memory write**: the bit `idx`, whose value is `old`, is set to `new`.  Carrying the
overwritten value is what makes a write invertible; `old = new` is a write with no effect. -/
abbrev MemWrite : Type := ℕ × Bool × Bool

namespace MemWrite

/-- The bit a write changes. -/
def idx (w : MemWrite) : ℕ := w.1

/-- The value the write overwrites. -/
def old (w : MemWrite) : Bool := w.2.1

/-- The value the write installs. -/
def new (w : MemWrite) : Bool := w.2.2

end MemWrite

/-- An **existential transition**: source state, input bit, memory guard, memory write, target
state. -/
abbrev AmExTr : Type := ℕ × Bool × List MemLit × MemWrite × ℕ

namespace AmExTr

/-- The source state. -/
def src (t : AmExTr) : ℕ := t.1

/-- The input bit the transition reads. -/
def bit (t : AmExTr) : Bool := t.2.1

/-- The memory guard. -/
def guard (t : AmExTr) : List MemLit := t.2.2.1

/-- The memory write. -/
def wr (t : AmExTr) : MemWrite := t.2.2.2.1

/-- The target state. -/
def tgt (t : AmExTr) : ℕ := t.2.2.2.2

end AmExTr

/-- A **universal transition**: source state, input bit, memory guard, and the two target states
which both have to accept.  A universal step does not write. -/
abbrev AmUnTr : Type := ℕ × Bool × List MemLit × ℕ × ℕ

namespace AmUnTr

/-- The source state. -/
def src (t : AmUnTr) : ℕ := t.1

/-- The input bit the transition reads. -/
def bit (t : AmUnTr) : Bool := t.2.1

/-- The memory guard. -/
def guard (t : AmUnTr) : List MemLit := t.2.2.1

/-- The first target state. -/
def tgt₁ (t : AmUnTr) : ℕ := t.2.2.2.1

/-- The second target state. -/
def tgt₂ (t : AmUnTr) : ℕ := t.2.2.2.2

end AmUnTr

/-- An **accepting condition**: a state and a memory guard. -/
abbrev AmAcc : Type := ℕ × List MemLit

namespace AmAcc

/-- The accepting state. -/
def st (c : AmAcc) : ℕ := c.1

/-- The memory guard of the accepting condition. -/
def guard (c : AmAcc) : List MemLit := c.2

end AmAcc

/-- An **alternating machine with a memory**: `mem` memory bits, an initial state, a list of
accepting conditions, and the existential and universal transitions.  One input bit is consumed
per step. -/
structure BitAltMem where
  /-- The number of memory bits. -/
  mem : ℕ
  /-- The initial state. -/
  start : ℕ
  /-- The accepting conditions. -/
  acc : List AmAcc
  /-- The existential transitions. -/
  ex : List AmExTr
  /-- The universal transitions. -/
  un : List AmUnTr

/-- Writing the value `v` into the bit `i` of a memory. -/
def memUpd (μ : ℕ → Bool) (i : ℕ) (v : Bool) : ℕ → Bool := fun j => if j = i then v else μ j

@[simp] theorem memUpd_self (μ : ℕ → Bool) (i : ℕ) (v : Bool) : memUpd μ i v i = v := by
  simp [memUpd]

theorem memUpd_of_ne {μ : ℕ → Bool} {i j : ℕ} {v : Bool} (h : j ≠ i) : memUpd μ i v j = μ j := by
  simp [memUpd, h]

theorem memUpd_memUpd (μ : ℕ → Bool) (i : ℕ) (v u : Bool) :
    memUpd (memUpd μ i v) i u = memUpd μ i u := by
  funext j
  by_cases h : j = i <;> simp [memUpd, h]

theorem memUpd_eq_self {μ : ℕ → Bool} {i : ℕ} {u : Bool} (h : μ i = u) : memUpd μ i u = μ := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [memUpd, h]
  · simp [memUpd, hj]

/-- **A memory guard holds**: every literal names a bit of the memory and that bit has the value
the literal gives. -/
def MemSat (m : ℕ) (μ : ℕ → Bool) (g : List MemLit) : Prop := ∀ p ∈ g, p.1 < m ∧ μ p.1 = p.2

namespace BitAltMem

/-- **Acceptance from a state with a memory.**  An existential transition needs one accepting
successor, a universal transition needs both, and in either case the guard has to hold in the
memory reached so far; only an existential transition writes. -/
inductive AccFrom (M : BitAltMem) : ℕ → List Bool → (ℕ → Bool) → Prop
  /-- The empty word is accepted if some accepting condition is met. -/
  | nil {q : ℕ} {μ : ℕ → Bool} {c : AmAcc} (hc : c ∈ M.acc) (hq : c.st = q)
      (hg : MemSat M.mem μ c.guard) : AccFrom M q [] μ
  /-- An existential transition consumes the first bit and writes. -/
  | ex {q : ℕ} {b : Bool} {v : List Bool} {μ : ℕ → Bool} {t : AmExTr} (ht : t ∈ M.ex)
      (hq : t.src = q) (hb : t.bit = b) (hg : MemSat M.mem μ t.guard) (hw : t.wr.idx < M.mem)
      (hu : μ t.wr.idx = t.wr.old)
      (h' : AccFrom M t.tgt v (memUpd μ t.wr.idx t.wr.new)) : AccFrom M q (b :: v) μ
  /-- A universal transition consumes the first bit; both successors must accept, each with the
  memory the transition was taken in. -/
  | un {q : ℕ} {b : Bool} {v : List Bool} {μ : ℕ → Bool} {t : AmUnTr} (ht : t ∈ M.un)
      (hq : t.src = q) (hb : t.bit = b) (hg : MemSat M.mem μ t.guard)
      (h₁ : AccFrom M t.tgt₁ v μ) (h₂ : AccFrom M t.tgt₂ v μ) : AccFrom M q (b :: v) μ

/-- **The language of an alternating machine with a memory**: the memory starts empty. -/
def Accepts (M : BitAltMem) (w : List Bool) : Prop := M.AccFrom M.start w (fun _ => false)

end BitAltMem

/-! ### The names of the encoding

The root task is `0`, the name the root task of `HTN.Syn.posEnc` carries; the three other kinds
of compound task are tagged by their residue mod `4`, so no two of them can be confused. -/

/-- **The configuration task**: the machine is in the state `q` and `k` bits are still to be
read. -/
def amCName (k q : ℕ) : ℕ := 4 * Nat.pair k q + 1

/-- **The branching task** of a universal step into `q₁` and `q₂` with `k` bits still to be
read. -/
def amBrName (k q₁ q₂ : ℕ) : ℕ := 4 * Nat.pair k (Nat.pair q₁ q₂) + 2

/-- **The undoing task**: run the `i`-th existential transition's sub-computation with `k` bits
still to be read, then undo the write of that transition. -/
def amDName (k i : ℕ) : ℕ := 4 * Nat.pair k i + 3

theorem amCName_ne_zero (k q : ℕ) : amCName k q ≠ 0 := by simp [amCName]

theorem amBrName_ne_zero (k q₁ q₂ : ℕ) : amBrName k q₁ q₂ ≠ 0 := by simp [amBrName]

theorem amDName_ne_zero (k i : ℕ) : amDName k i ≠ 0 := by simp [amDName]

theorem amCName_inj {k q k' q' : ℕ} (h : amCName k q = amCName k' q') : k = k' ∧ q = q' :=
  Nat.pair_eq_pair.1 (by simp only [amCName] at h; omega)

theorem amBrName_inj {k q₁ q₂ k' q₁' q₂' : ℕ} (h : amBrName k q₁ q₂ = amBrName k' q₁' q₂') :
    k = k' ∧ q₁ = q₁' ∧ q₂ = q₂' := by
  obtain ⟨hk, hq⟩ := Nat.pair_eq_pair.1 (show Nat.pair k (Nat.pair q₁ q₂)
    = Nat.pair k' (Nat.pair q₁' q₂') by simp only [amBrName] at h; omega)
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 hq
  exact ⟨hk, h₁, h₂⟩

theorem amDName_inj {k i k' i' : ℕ} (h : amDName k i = amDName k' i') : k = k' ∧ i = i' :=
  Nat.pair_eq_pair.1 (by simp only [amDName] at h; omega)

theorem amCName_ne_brName {k q k' q₁ q₂ : ℕ} : amCName k q ≠ amBrName k' q₁ q₂ := by
  simp only [amCName, amBrName]
  omega

theorem amCName_ne_dName {k q k' i : ℕ} : amCName k q ≠ amDName k' i := by
  simp only [amCName, amDName]
  omega

theorem amBrName_ne_dName {k q₁ q₂ k' i : ℕ} : amBrName k q₁ q₂ ≠ amDName k' i := by
  simp only [amBrName, amDName]
  omega

/-! ### The actions of the encoding -/

variable {M : BitAltMem}

/-- The fact holding the value `b` of the memory bit `i`, for a word of length `n`: the position
fact of the position `n + i`, which the input word does not use. -/
def amRail (n i : ℕ) (b : Bool) : ℕ := posFact (n + i) b

/-- The fact a memory literal asks for. -/
def amRailOf (n : ℕ) (p : MemLit) : ℕ := amRail n p.1 p.2

/-- The action taking the `i`-th existential transition with `k` bits still to be read. -/
def amFwd (M : BitAltMem) (k i : ℕ) : ℕ := 4 * (i + M.ex.length * k)

/-- The action undoing the write of the `i`-th existential transition. -/
def amUndo (i : ℕ) : ℕ := 4 * i + 1

/-- The action guarding the `j`-th universal transition with `k` bits still to be read. -/
def amGrd (M : BitAltMem) (k j : ℕ) : ℕ := 4 * (j + M.un.length * k) + 2

/-- The action checking the `a`-th accepting condition. -/
def amAccA (a : ℕ) : ℕ := 4 * a + 3

/-- The action initialising the memory. -/
def amInit (M : BitAltMem) : ℕ := 4 * M.acc.length + 3

/-- The number of actions the domain lists. -/
def amNumActs (M : BitAltMem) (n : ℕ) : ℕ :=
  4 * (n * M.ex.length + n * M.un.length + M.ex.length + M.acc.length + 1)

/-- The data of a forward action. -/
def amFwdData (M : BitAltMem) (n k i : ℕ) : List ℕ × List ℕ × List ℕ :=
  (posFact k (M.ex.getI i).bit :: amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.old
      :: (M.ex.getI i).guard.map (amRailOf n),
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.new],
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.old])

/-- The data of an undoing action: the write of the transition, read backwards. -/
def amUndoData (M : BitAltMem) (n i : ℕ) : List ℕ × List ℕ × List ℕ :=
  ([amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.new],
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.old],
    [amRail n (M.ex.getI i).wr.idx (M.ex.getI i).wr.new])

/-- The data of the guard of a universal transition: it has no effect. -/
def amGrdData (M : BitAltMem) (n k j : ℕ) : List ℕ × List ℕ × List ℕ :=
  (posFact k (M.un.getI j).bit :: (M.un.getI j).guard.map (amRailOf n), [], [])

/-- The data of an accepting check: it has no effect. -/
def amAccData (M : BitAltMem) (n a : ℕ) : List ℕ × List ℕ × List ℕ :=
  ((M.acc.getI a).guard.map (amRailOf n), [], [])

/-- The data of the initialising action: every memory bit is set to `false`. -/
def amInitData (M : BitAltMem) (n : ℕ) : List ℕ × List ℕ × List ℕ :=
  ([], (List.range M.mem).map fun i => amRail n i false, [])

/-- **The data of the action `j`.**  The residue of `j` mod `4` says which kind of action it
is. -/
def amActData (M : BitAltMem) (n j : ℕ) : List ℕ × List ℕ × List ℕ :=
  if j % 4 = 0 then amFwdData M n (j / 4 / M.ex.length) (j / 4 % M.ex.length)
  else if j % 4 = 1 then amUndoData M n (j / 4)
  else if j % 4 = 2 then amGrdData M n (j / 4 / M.un.length) (j / 4 % M.un.length)
  else if j / 4 < M.acc.length then amAccData M n (j / 4)
  else amInitData M n

/-- **The actions of the encoding.** -/
def amActions (M : BitAltMem) (n : ℕ) : List ActionDesc :=
  (List.range (amNumActs M n)).map fun j => (j, amActData M n j)

/-! ### The action indices decode -/

theorem amFwd_lt {n k i : ℕ} (hk : k < n) (hi : i < M.ex.length) :
    amFwd M k i < amNumActs M n := by
  have h : i + M.ex.length * k < M.ex.length * n := by
    calc i + M.ex.length * k < M.ex.length * (k + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ M.ex.length * n := Nat.mul_le_mul_left _ hk
  have h' : M.ex.length * n = n * M.ex.length := Nat.mul_comm _ _
  simp only [amFwd, amNumActs]
  omega

theorem amUndo_lt {n i : ℕ} (hi : i < M.ex.length) : amUndo i < amNumActs M n := by
  simp only [amUndo, amNumActs]
  omega

theorem amGrd_lt {n k j : ℕ} (hk : k < n) (hj : j < M.un.length) :
    amGrd M k j < amNumActs M n := by
  have h : j + M.un.length * k < M.un.length * n := by
    calc j + M.un.length * k < M.un.length * (k + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ M.un.length * n := Nat.mul_le_mul_left _ hk
  have h' : M.un.length * n = n * M.un.length := Nat.mul_comm _ _
  simp only [amGrd, amNumActs]
  omega

theorem amAccA_lt {n a : ℕ} (ha : a < M.acc.length) : amAccA a < amNumActs M n := by
  simp only [amAccA, amNumActs]
  omega

theorem amInit_lt (n : ℕ) : amInit M < amNumActs M n := by
  simp only [amInit, amNumActs]
  omega

theorem amActData_fwd {n k i : ℕ} (hi : i < M.ex.length) :
    amActData M n (amFwd M k i) = amFwdData M n k i := by
  have h4 : amFwd M k i % 4 = 0 := by simp [amFwd, Nat.mul_mod_right]
  have hdiv : amFwd M k i / 4 = i + M.ex.length * k := by
    simp [amFwd, Nat.mul_div_cancel_left _ (by omega : 0 < 4)]
  have hk : (i + M.ex.length * k) / M.ex.length = k := by
    rw [Nat.add_mul_div_left _ _ (by omega : 0 < M.ex.length), Nat.div_eq_of_lt hi, Nat.zero_add]
  have hi' : (i + M.ex.length * k) % M.ex.length = i := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  rw [amActData, if_pos h4, hdiv, hk, hi']

theorem amActData_undo (n i : ℕ) : amActData M n (amUndo i) = amUndoData M n i := by
  have h4 : amUndo i % 4 = 1 := by simp [amUndo]
  have hdiv : amUndo i / 4 = i := by simp [amUndo, Nat.mul_add_div (by omega : 0 < 4)]
  rw [amActData, if_neg (by omega), if_pos h4, hdiv]

theorem amActData_grd {n k j : ℕ} (hj : j < M.un.length) :
    amActData M n (amGrd M k j) = amGrdData M n k j := by
  have h4 : amGrd M k j % 4 = 2 := by simp [amGrd]
  have hdiv : amGrd M k j / 4 = j + M.un.length * k := by
    simp [amGrd, Nat.mul_add_div (by omega : 0 < 4)]
  have hk : (j + M.un.length * k) / M.un.length = k := by
    rw [Nat.add_mul_div_left _ _ (by omega : 0 < M.un.length), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hj' : (j + M.un.length * k) % M.un.length = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [amActData, if_neg (by omega), if_neg (by omega), if_pos h4, hdiv, hk, hj']

theorem amActData_acc {n a : ℕ} (ha : a < M.acc.length) :
    amActData M n (amAccA a) = amAccData M n a := by
  have h4 : amAccA a % 4 = 3 := by simp [amAccA]
  have hdiv : amAccA a / 4 = a := by simp [amAccA, Nat.mul_add_div (by omega : 0 < 4)]
  rw [amActData, if_neg (by omega), if_neg (by omega), if_neg (by omega), hdiv, if_pos ha]

theorem amActData_init (n : ℕ) : amActData M n (amInit M) = amInitData M n := by
  have h4 : amInit M % 4 = 3 := by simp [amInit]
  have hdiv : amInit M / 4 = M.acc.length := by
    simp [amInit, Nat.mul_add_div (by omega : 0 < 4)]
  rw [amActData, if_neg (by omega), if_neg (by omega), if_neg (by omega), hdiv,
    if_neg (by omega)]

/-! ### The methods and the domain -/

/-- The root method: initialise the memory, then run the machine. -/
def amRootMethods (M : BitAltMem) (n : ℕ) : List MethodDesc :=
  [(0, pairBody (Sum.inl (amInit M)) (Sum.inr (amCName n M.start)))]

/-- The methods of the existential transitions: take the transition, then undo it. -/
def amExMethods (M : BitAltMem) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => (List.range M.ex.length).map fun i =>
    (amCName (k + 1) (M.ex.getI i).src,
      pairBody (Sum.inl (amFwd M k i)) (Sum.inr (amDName k i)))

/-- The methods of the undoing tasks: the sub-computation, then the inverse write. -/
def amDMethods (M : BitAltMem) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => (List.range M.ex.length).map fun i =>
    (amDName k i,
      pairBody (Sum.inr (amCName k (M.ex.getI i).tgt)) (Sum.inl (amUndo i)))

/-- The methods of the universal transitions: read the bit, then branch. -/
def amUnMethods (M : BitAltMem) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => (List.range M.un.length).map fun j =>
    (amCName (k + 1) (M.un.getI j).src,
      pairBody (Sum.inl (amGrd M k j))
        (Sum.inr (amBrName k (M.un.getI j).tgt₁ (M.un.getI j).tgt₂)))

/-- The branching methods: a universal branch is refined into *both* of its successors. -/
def amBrMethods (M : BitAltMem) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => (List.range M.un.length).map fun j =>
    (amBrName k (M.un.getI j).tgt₁ (M.un.getI j).tgt₂,
      pairBody (Sum.inr (amCName k (M.un.getI j).tgt₁))
        (Sum.inr (amCName k (M.un.getI j).tgt₂)))

/-- The accepting methods: with no bit left, check an accepting condition. -/
def amAccMethods (M : BitAltMem) : List MethodDesc :=
  (List.range M.acc.length).map fun a => (amCName 0 (M.acc.getI a).st, singleBody (amAccA a))

/-- **The domain description of the encoding** for the words of length `n`. -/
def amDom (M : BitAltMem) (n : ℕ) : DomDesc :=
  (amActions M n,
    amRootMethods M n ++ amExMethods M n ++ amDMethods M n ++ amUnMethods M n ++
      amBrMethods M n ++ amAccMethods M)

@[simp] theorem amDom_actions (n : ℕ) : (amDom M n).actions = amActions M n := rfl

@[simp] theorem amDom_methods (n : ℕ) :
    (amDom M n).methods =
      amRootMethods M n ++ amExMethods M n ++ amDMethods M n ++ amUnMethods M n ++
        amBrMethods M n ++ amAccMethods M := rfl

theorem mem_amRootMethods {n : ℕ} {e : MethodDesc} (he : e ∈ amRootMethods M n) :
    e = (0, pairBody (Sum.inl (amInit M)) (Sum.inr (amCName n M.start))) := by
  simpa [amRootMethods] using he

theorem mem_amExMethods {n : ℕ} {e : MethodDesc} (he : e ∈ amExMethods M n) :
    ∃ k < n, ∃ i < M.ex.length,
      e = (amCName (k + 1) (M.ex.getI i).src,
        pairBody (Sum.inl (amFwd M k i)) (Sum.inr (amDName k i))) := by
  simp only [amExMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, i, hi, rfl⟩ := he
  exact ⟨k, hk, i, hi, rfl⟩

theorem mem_amDMethods {n : ℕ} {e : MethodDesc} (he : e ∈ amDMethods M n) :
    ∃ k < n, ∃ i < M.ex.length,
      e = (amDName k i,
        pairBody (Sum.inr (amCName k (M.ex.getI i).tgt)) (Sum.inl (amUndo i))) := by
  simp only [amDMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, i, hi, rfl⟩ := he
  exact ⟨k, hk, i, hi, rfl⟩

theorem mem_amUnMethods {n : ℕ} {e : MethodDesc} (he : e ∈ amUnMethods M n) :
    ∃ k < n, ∃ j < M.un.length,
      e = (amCName (k + 1) (M.un.getI j).src,
        pairBody (Sum.inl (amGrd M k j))
          (Sum.inr (amBrName k (M.un.getI j).tgt₁ (M.un.getI j).tgt₂))) := by
  simp only [amUnMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, j, hj, rfl⟩ := he
  exact ⟨k, hk, j, hj, rfl⟩

theorem mem_amBrMethods {n : ℕ} {e : MethodDesc} (he : e ∈ amBrMethods M n) :
    ∃ k < n, ∃ j < M.un.length,
      e = (amBrName k (M.un.getI j).tgt₁ (M.un.getI j).tgt₂,
        pairBody (Sum.inr (amCName k (M.un.getI j).tgt₁))
          (Sum.inr (amCName k (M.un.getI j).tgt₂))) := by
  simp only [amBrMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, j, hj, rfl⟩ := he
  exact ⟨k, hk, j, hj, rfl⟩

theorem mem_amAccMethods {e : MethodDesc} (he : e ∈ amAccMethods M) :
    ∃ a < M.acc.length, e = (amCName 0 (M.acc.getI a).st, singleBody (amAccA a)) := by
  simp only [amAccMethods, List.mem_map, List.mem_range] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact ⟨a, ha, rfl⟩

theorem mem_amDom_methods {n : ℕ} {e : MethodDesc} (he : e ∈ (amDom M n).methods) :
    e ∈ amRootMethods M n ∨ e ∈ amExMethods M n ∨ e ∈ amDMethods M n ∨ e ∈ amUnMethods M n ∨
      e ∈ amBrMethods M n ∨ e ∈ amAccMethods M := by
  rw [amDom_methods] at he
  simp only [List.mem_append] at he
  tauto

theorem mem_amDom_of_root {n : ℕ} {e : MethodDesc} (h : e ∈ amRootMethods M n) :
    e ∈ (amDom M n).methods := by
  rw [amDom_methods]
  simp only [List.mem_append]
  tauto

theorem mem_amDom_of_ex {n : ℕ} {e : MethodDesc} (h : e ∈ amExMethods M n) :
    e ∈ (amDom M n).methods := by
  rw [amDom_methods]
  simp only [List.mem_append]
  tauto

theorem mem_amDom_of_d {n : ℕ} {e : MethodDesc} (h : e ∈ amDMethods M n) :
    e ∈ (amDom M n).methods := by
  rw [amDom_methods]
  simp only [List.mem_append]
  tauto

theorem mem_amDom_of_un {n : ℕ} {e : MethodDesc} (h : e ∈ amUnMethods M n) :
    e ∈ (amDom M n).methods := by
  rw [amDom_methods]
  simp only [List.mem_append]
  tauto

theorem mem_amDom_of_br {n : ℕ} {e : MethodDesc} (h : e ∈ amBrMethods M n) :
    e ∈ (amDom M n).methods := by
  rw [amDom_methods]
  simp only [List.mem_append]
  tauto

theorem mem_amDom_of_acc {n : ℕ} {e : MethodDesc} (h : e ∈ amAccMethods M) :
    e ∈ (amDom M n).methods := by
  rw [amDom_methods]
  simp only [List.mem_append]
  tauto

/-! ### The domain is in the class -/

theorem amDom_methodsTO (n : ℕ) : (amDom M n).MethodsTO := by
  intro e he
  rcases mem_amDom_methods he with he | he | he | he | he | he
  · rw [mem_amRootMethods he]
    exact pairBody_isTO _ _
  · obtain ⟨k, -, i, -, rfl⟩ := mem_amExMethods he
    exact pairBody_isTO _ _
  · obtain ⟨k, -, i, -, rfl⟩ := mem_amDMethods he
    exact pairBody_isTO _ _
  · obtain ⟨k, -, j, -, rfl⟩ := mem_amUnMethods he
    exact pairBody_isTO _ _
  · obtain ⟨k, -, j, -, rfl⟩ := mem_amBrMethods he
    exact pairBody_isTO _ _
  · obtain ⟨a, -, rfl⟩ := mem_amAccMethods he
    exact singleBody_isTO _

/-- The rank of a compound task name: three times the number of bits still to be read for a
configuration, one more for a branching or an undoing task, and the root above everything. -/
def amRank (n c : ℕ) : ℕ :=
  if c = 0 then 3 * n + 3
  else if c % 4 = 1 then 3 * (Nat.unpair (c / 4)).1
  else 3 * (Nat.unpair (c / 4)).1 + 1

@[simp] theorem amRank_zero (n : ℕ) : amRank n 0 = 3 * n + 3 := by simp [amRank]

@[simp] theorem amRank_cName (n k q : ℕ) : amRank n (amCName k q) = 3 * k := by
  have h1 : amCName k q ≠ 0 := amCName_ne_zero k q
  have h2 : amCName k q % 4 = 1 := by simp [amCName]
  have h3 : amCName k q / 4 = Nat.pair k q := by
    simp [amCName, Nat.mul_add_div (by omega : 0 < 4)]
  rw [amRank, if_neg h1, if_pos h2, h3, Nat.unpair_pair]

@[simp] theorem amRank_brName (n k q₁ q₂ : ℕ) : amRank n (amBrName k q₁ q₂) = 3 * k + 1 := by
  have h1 : amBrName k q₁ q₂ ≠ 0 := amBrName_ne_zero k q₁ q₂
  have h2 : amBrName k q₁ q₂ % 4 = 2 := by simp [amBrName]
  have h3 : amBrName k q₁ q₂ / 4 = Nat.pair k (Nat.pair q₁ q₂) := by
    simp [amBrName, Nat.mul_add_div (by omega : 0 < 4)]
  rw [amRank, if_neg h1, if_neg (by omega), h3, Nat.unpair_pair]

@[simp] theorem amRank_dName (n k i : ℕ) : amRank n (amDName k i) = 3 * k + 1 := by
  have h1 : amDName k i ≠ 0 := amDName_ne_zero k i
  have h2 : amDName k i % 4 = 3 := by simp [amDName]
  have h3 : amDName k i / 4 = Nat.pair k i := by
    simp [amDName, Nat.mul_add_div (by omega : 0 < 4)]
  rw [amRank, if_neg h1, if_neg (by omega), h3, Nat.unpair_pair]

theorem amDom_isAcyclic (n : ℕ) : (amDom M n).IsAcyclic := by
  refine ⟨amRank n, ?_⟩
  intro e he t ht c hc
  have hpair : ∀ x y : ℕ ⊕ ℕ, t ∈ (pairBody x y).toTaskNetwork.T → t = 0 ∨ t = 1 := by
    intro x y ht
    simpa [TnDesc.toTaskNetwork, pairBody, TnDesc.ids] using ht
  rcases mem_amDom_methods he with he | he | he | he | he | he
  · have hee := mem_amRootMethods he
    subst hee
    rcases hpair _ _ ht with rfl | rfl
    · simp [TnDesc.toTaskNetwork] at hc
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      show amRank n (amCName n M.start) < amRank n 0
      simp only [amRank_cName, amRank_zero]
      omega
  · obtain ⟨k, -, i, -, rfl⟩ := mem_amExMethods he
    rcases hpair _ _ ht with rfl | rfl
    · simp [TnDesc.toTaskNetwork] at hc
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp only [amRank_cName, amRank_dName]
      omega
  · obtain ⟨k, -, i, -, rfl⟩ := mem_amDMethods he
    rcases hpair _ _ ht with rfl | rfl
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_zero, Sum.inr.injEq] at hc
      subst hc
      simp only [amRank_cName, amRank_dName]
      omega
    · simp [TnDesc.toTaskNetwork] at hc
  · obtain ⟨k, -, j, -, rfl⟩ := mem_amUnMethods he
    rcases hpair _ _ ht with rfl | rfl
    · simp [TnDesc.toTaskNetwork] at hc
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp only [amRank_cName, amRank_brName]
      omega
  · obtain ⟨k, -, j, -, rfl⟩ := mem_amBrMethods he
    rcases hpair _ _ ht with rfl | rfl
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_zero, Sum.inr.injEq] at hc
      subst hc
      simp only [amRank_cName, amRank_brName]
      omega
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp only [amRank_cName, amRank_brName]
      omega
  · obtain ⟨a, -, rfl⟩ := mem_amAccMethods he
    have ht' : t = 0 := by
      simpa [TnDesc.toTaskNetwork, singleBody, TnDesc.ids] using ht
    subst ht'
    simp [TnDesc.toTaskNetwork, TnDesc.label, singleBody, TnDesc.lbl] at hc

theorem amDom_domOk (n : ℕ) : SynClass.TO_HTN_AC_root.domOk (amDom M n) :=
  ⟨amDom_methodsTO n, amDom_isAcyclic n⟩

/-! ### The bodies the domain offers -/

/-- **The bodies of the root task.** -/
theorem seqBody_amDom_root_iff {n : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (amDom M n).toDomain.SeqBody 0 xs ↔
      xs = [Sum.inl (amInit M), Sum.inr (amCName n M.start)] := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_amDom_methods he with he | he | he | he | he | he
    · rw [mem_amRootMethods he] at hbody
      exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody
    · obtain ⟨k, -, i, -, rfl⟩ := mem_amExMethods he
      exact absurd hc (amCName_ne_zero _ _)
    · obtain ⟨k, -, i, -, rfl⟩ := mem_amDMethods he
      exact absurd hc (amDName_ne_zero _ _)
    · obtain ⟨k, -, j, -, rfl⟩ := mem_amUnMethods he
      exact absurd hc (amCName_ne_zero _ _)
    · obtain ⟨k, -, j, -, rfl⟩ := mem_amBrMethods he
      exact absurd hc (amBrName_ne_zero _ _ _)
    · obtain ⟨a, -, rfl⟩ := mem_amAccMethods he
      exact absurd hc (amCName_ne_zero _ _)
  · rintro rfl
    refine ⟨(0, pairBody (Sum.inl (amInit M)) (Sum.inr (amCName n M.start))),
      mem_amDom_of_root (by simp [amRootMethods]), rfl, ?_⟩
    exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl

/-- **The bodies of a configuration task.** -/
theorem seqBody_amDom_c_iff {n k q : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (amDom M n).toDomain.SeqBody (amCName k q) xs ↔
      (∃ j < n, k = j + 1 ∧ ∃ i < M.ex.length, (M.ex.getI i).src = q ∧
        xs = [Sum.inl (amFwd M j i), Sum.inr (amDName j i)]) ∨
      (∃ j < n, k = j + 1 ∧ ∃ i < M.un.length, (M.un.getI i).src = q ∧
        xs = [Sum.inl (amGrd M j i),
          Sum.inr (amBrName j (M.un.getI i).tgt₁ (M.un.getI i).tgt₂)]) ∨
      (k = 0 ∧ ∃ a < M.acc.length, (M.acc.getI a).st = q ∧ xs = [Sum.inl (amAccA a)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_amDom_methods he with he | he | he | he | he | he
    · rw [mem_amRootMethods he] at hc
      exact absurd hc.symm (amCName_ne_zero _ _)
    · obtain ⟨j, hj, i, hi, rfl⟩ := mem_amExMethods he
      obtain ⟨hk, hq⟩ := amCName_inj hc
      subst hk
      exact Or.inl ⟨j, hj, rfl, i, hi, hq,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · obtain ⟨j, -, i, -, rfl⟩ := mem_amDMethods he
      exact absurd hc amCName_ne_dName.symm
    · obtain ⟨j, hj, i, hi, rfl⟩ := mem_amUnMethods he
      obtain ⟨hk, hq⟩ := amCName_inj hc
      subst hk
      exact Or.inr (Or.inl ⟨j, hj, rfl, i, hi, hq,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩)
    · obtain ⟨j, -, i, -, rfl⟩ := mem_amBrMethods he
      exact absurd hc amCName_ne_brName.symm
    · obtain ⟨a, ha, rfl⟩ := mem_amAccMethods he
      obtain ⟨hk, hq⟩ := amCName_inj hc
      subst hk
      exact Or.inr (Or.inr ⟨rfl, a, ha, hq,
        (Method.hasSeqBody_iff_of_isSeqNet (singleBody_isSeqNet _)).1 hbody⟩)
  · rintro (⟨j, hj, rfl, i, hi, hq, rfl⟩ | ⟨j, hj, rfl, i, hi, hq, rfl⟩ |
      ⟨rfl, a, ha, hq, rfl⟩)
    · refine ⟨(amCName (j + 1) (M.ex.getI i).src,
        pairBody (Sum.inl (amFwd M j i)) (Sum.inr (amDName j i))), mem_amDom_of_ex ?_, by
          rw [hq], (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
      simp only [amExMethods, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨j, hj, i, hi, rfl⟩
    · refine ⟨(amCName (j + 1) (M.un.getI i).src,
        pairBody (Sum.inl (amGrd M j i))
          (Sum.inr (amBrName j (M.un.getI i).tgt₁ (M.un.getI i).tgt₂))),
        mem_amDom_of_un ?_, by rw [hq],
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
      simp only [amUnMethods, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨j, hj, i, hi, rfl⟩
    · refine ⟨(amCName 0 (M.acc.getI a).st, singleBody (amAccA a)), mem_amDom_of_acc ?_, by
        rw [hq], (Method.hasSeqBody_iff_of_isSeqNet (singleBody_isSeqNet _)).2 rfl⟩
      simp only [amAccMethods, List.mem_map, List.mem_range]
      exact ⟨a, ha, rfl⟩

/-- **The bodies of an undoing task.** -/
theorem seqBody_amDom_d_iff {n k i : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (amDom M n).toDomain.SeqBody (amDName k i) xs ↔
      (k < n ∧ i < M.ex.length ∧
        xs = [Sum.inr (amCName k (M.ex.getI i).tgt), Sum.inl (amUndo i)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_amDom_methods he with he | he | he | he | he | he
    · rw [mem_amRootMethods he] at hc
      exact absurd hc.symm (amDName_ne_zero _ _)
    · obtain ⟨j, -, i', -, rfl⟩ := mem_amExMethods he
      exact absurd hc amCName_ne_dName
    · obtain ⟨j, hj, i', hi', rfl⟩ := mem_amDMethods he
      obtain ⟨hk, hi⟩ := amDName_inj hc
      subst hk
      subst hi
      exact ⟨hj, hi', (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · obtain ⟨j, -, i', -, rfl⟩ := mem_amUnMethods he
      exact absurd hc amCName_ne_dName
    · obtain ⟨j, -, i', -, rfl⟩ := mem_amBrMethods he
      exact absurd hc amBrName_ne_dName
    · obtain ⟨a, -, rfl⟩ := mem_amAccMethods he
      exact absurd hc amCName_ne_dName
  · rintro ⟨hk, hi, rfl⟩
    refine ⟨(amDName k i,
      pairBody (Sum.inr (amCName k (M.ex.getI i).tgt)) (Sum.inl (amUndo i))),
      mem_amDom_of_d ?_, rfl,
      (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
    simp only [amDMethods, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨k, hk, i, hi, rfl⟩

/-- **The bodies of a branching task.** -/
theorem seqBody_amDom_br_iff {n k q₁ q₂ : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (amDom M n).toDomain.SeqBody (amBrName k q₁ q₂) xs ↔
      (k < n ∧ (∃ j < M.un.length, (M.un.getI j).tgt₁ = q₁ ∧ (M.un.getI j).tgt₂ = q₂) ∧
        xs = [Sum.inr (amCName k q₁), Sum.inr (amCName k q₂)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_amDom_methods he with he | he | he | he | he | he
    · rw [mem_amRootMethods he] at hc
      exact absurd hc.symm (amBrName_ne_zero _ _ _)
    · obtain ⟨j, -, i', -, rfl⟩ := mem_amExMethods he
      exact absurd hc amCName_ne_brName
    · obtain ⟨j, -, i', -, rfl⟩ := mem_amDMethods he
      exact absurd hc amBrName_ne_dName.symm
    · obtain ⟨j, -, i', -, rfl⟩ := mem_amUnMethods he
      exact absurd hc amCName_ne_brName
    · obtain ⟨j, hj, i', hi', rfl⟩ := mem_amBrMethods he
      obtain ⟨hk, h₁, h₂⟩ := amBrName_inj hc
      subst hk
      subst h₁
      subst h₂
      exact ⟨hj, ⟨i', hi', rfl, rfl⟩,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · obtain ⟨a, -, rfl⟩ := mem_amAccMethods he
      exact absurd hc amCName_ne_brName
  · rintro ⟨hk, ⟨j, hj, h₁, h₂⟩, rfl⟩
    subst h₁
    subst h₂
    refine ⟨(amBrName k (M.un.getI j).tgt₁ (M.un.getI j).tgt₂,
      pairBody (Sum.inr (amCName k (M.un.getI j).tgt₁))
        (Sum.inr (amCName k (M.un.getI j).tgt₂))), mem_amDom_of_br ?_, rfl,
      (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
    simp only [amBrMethods, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨k, hk, j, hj, rfl⟩

/-! ### The preconditions and the effects of the actions -/

theorem lookup_amActions {n j : ℕ} (hj : j < amNumActs M n) :
    (amActions M n).lookup j = some (amActData M n j) :=
  lookup_range_map (fun j => amActData M n j) hj

theorem prec_amDom {n j : ℕ} (hj : j < amNumActs M n) :
    (amDom M n).prec j = {f | f ∈ (amActData M n j).1} := by
  simp only [DomDesc.prec, amDom_actions, lookup_amActions hj]
  rfl

theorem add_amDom {n j : ℕ} (hj : j < amNumActs M n) :
    (amDom M n).add j = {f | f ∈ (amActData M n j).2.1} := by
  simp only [DomDesc.add, amDom_actions, lookup_amActions hj]
  rfl

theorem del_amDom {n j : ℕ} (hj : j < amNumActs M n) :
    (amDom M n).del j = {f | f ∈ (amActData M n j).2.2} := by
  simp only [DomDesc.del, amDom_actions, lookup_amActions hj]
  rfl

end Syn

end HTN
