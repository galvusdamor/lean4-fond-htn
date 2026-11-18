import HtnComplexity.Complexity.RecMemFamily
/-!
# Alternating bit programs, and their translation into recursive alternating machines

`HtnComplexity/Complexity/RecMemDom.lean` gives the machine model the hardness family of
`HtnComplexity/Complexity/RecMemUniform.lean` runs on: a `HTN.Syn.RecAltMem`, whose
transitions are guarded by conjunctions of literals over the memory bits and over the positions
of the input word.  Writing a simulation directly as such a list of transitions is unpleasant,
so this file interposes a small **imperative language** and translates it once and for all.

An **alternating bit program** is a list of instructions, addressed by a program counter:

| instruction | effect |
| --- | --- |
| `iNand i j d` | `mem d := !(mem i && mem j)`, then `pc + 1` |
| `iRdIn p d` | `mem d :=` the bit of the input word at the position `p`, then `pc + 1` |
| `iBrIf i t` | `pc := t` if `mem i`, else `pc + 1` |
| `iJmp t` | `pc := t` |
| `iEx d` | *existentially*: `mem d := false` or `mem d := true`, then `pc + 1` |
| `iAll d` | *universally*: both, then `pc + 1` |
| `iSet0 d`, `iSet1 d` | `mem d := false`, resp. `true`, then `pc + 1` |
| `iCopy s d` | `mem d := mem s`, then `pc + 1` |
| `iAcc` | accept |
| `iRej` | reject — also what an address outside the program does |

Instructions are quadruples of numbers rather than a datatype, so that a program is an object
for which the `Primrec` bookkeeping of a uniform family is available without a new encoding.

The translation `HTN.Compile.progMach` uses three machine states per program point: `3 * pc` is
the program point itself, and `3 * pc + 1`, `3 * pc + 2` are the two branches of a universal
instruction, in which the bit is written.  Its correctness is
`HTN.Compile.accepts_progMach_iff`.
-/

namespace HTN

namespace Compile

open Syn

/-! ### Instructions -/

/-- An **instruction**: an opcode and three operands. -/
abbrev Instr : Type := ℕ × ℕ × ℕ × ℕ

/-- `mem d := !(mem i && mem j)`. -/
def iNand (i j d : ℕ) : Instr := (1, i, j, d)

/-- `mem d :=` the bit of the input word at the position `p`. -/
def iRdIn (p d : ℕ) : Instr := (2, p, 0, d)

/-- Jump to `t` if the bit `i` is set. -/
def iBrIf (i t : ℕ) : Instr := (3, i, t, 0)

/-- Set the bit `d` existentially. -/
def iEx (d : ℕ) : Instr := (4, 0, 0, d)

/-- Set the bit `d` universally: both values must lead to acceptance. -/
def iAll (d : ℕ) : Instr := (5, 0, 0, d)

/-- Accept. -/
def iAcc : Instr := (6, 0, 0, 0)

/-- Jump to `t`. -/
def iJmp (t : ℕ) : Instr := (7, 0, t, 0)

/-- Reject. -/
def iRej : Instr := (0, 0, 0, 0)

/-- `mem d := false`. -/
def iSet0 (d : ℕ) : Instr := (8, 0, 0, d)

/-- `mem d := true`. -/
def iSet1 (d : ℕ) : Instr := (9, 0, 0, d)

/-- `mem d := mem s`. -/
def iCopy (s d : ℕ) : Instr := (10, s, 0, d)

/-! ### The semantics -/

/-- The bit of the word at the position `p`, counted from the right — the convention of
`HTN.Syn.posFacts`. -/
def inBit (W : List Bool) (p : ℕ) : Bool := W.reverse.getI p

/-- **A position literal holds exactly when the word carries that bit there.** -/
theorem mem_posFacts_iff_inBit {W : List Bool} {p : ℕ} {b : Bool} :
    posFact p b ∈ posFacts W ↔ p < W.length ∧ inBit W p = b := by
  rw [mem_posFacts_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu⟩ := hv
    have hlen : W.length = u.length + (v.length + 1) := by
      rw [← hu]; simp
    refine ⟨by omega, ?_⟩
    rw [inBit, ← hu]
    rw [List.reverse_append, List.reverse_cons]
    rw [List.getI_append _ _ _ (by simp)]
    rw [List.getI_eq_getElem _ (by simp)]
    simp
  · rintro ⟨hp, hb⟩
    refine ⟨(W.drop (W.length - p)), ?_, by simp; omega⟩
    have hsuf : W.drop (W.length - p - 1) <:+ W := List.drop_suffix _ _
    have hd : W.drop (W.length - p - 1) = b :: W.drop (W.length - p) := by
      have h1 : W.length - p - 1 < W.length := by omega
      rw [List.drop_eq_getElem_cons h1]
      congr 1
      · rw [← hb, inBit, List.getI_eq_getElem _ (by simp; omega)]
        simp only [List.getElem_reverse]
        congr 1
        omega
      · congr 1; omega
    rw [← hd]
    exact hsuf

/-- **Acceptance of an alternating bit program** from a program point with a memory. -/
inductive Acc (P : List Instr) (W : List Bool) : ℕ → (ℕ → Bool) → Prop
  /-- The accepting instruction accepts. -/
  | acc {pc : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iAcc) : Acc P W pc μ
  /-- A `nand` writes and goes on. -/
  | nand {pc i j d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iNand i j d)
      (h' : Acc P W (pc + 1) (memUpd μ d (!(μ i && μ j)))) : Acc P W pc μ
  /-- A read writes the bit of the word and goes on. -/
  | rdIn {pc p d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iRdIn p d)
      (h' : Acc P W (pc + 1) (memUpd μ d (inBit W p))) : Acc P W pc μ
  /-- A taken branch. -/
  | brT {pc i t : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iBrIf i t) (hi : μ i = true)
      (h' : Acc P W t μ) : Acc P W pc μ
  /-- A branch that is not taken. -/
  | brF {pc i t : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iBrIf i t) (hi : μ i = false)
      (h' : Acc P W (pc + 1) μ) : Acc P W pc μ
  /-- A jump. -/
  | jmp {pc t : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iJmp t) (h' : Acc P W t μ) : Acc P W pc μ
  /-- An existential choice. -/
  | ex {pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iEx d) (b : Bool)
      (h' : Acc P W (pc + 1) (memUpd μ d b)) : Acc P W pc μ
  /-- A universal choice. -/
  | all {pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iAll d)
      (h0 : Acc P W (pc + 1) (memUpd μ d false))
      (h1 : Acc P W (pc + 1) (memUpd μ d true)) : Acc P W pc μ
  /-- Clearing a bit. -/
  | set0 {pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iSet0 d)
      (h' : Acc P W (pc + 1) (memUpd μ d false)) : Acc P W pc μ
  /-- Setting a bit. -/
  | set1 {pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iSet1 d)
      (h' : Acc P W (pc + 1) (memUpd μ d true)) : Acc P W pc μ
  /-- Copying a bit. -/
  | copy {pc s d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iCopy s d)
      (h' : Acc P W (pc + 1) (memUpd μ d (μ s))) : Acc P W pc μ

/-! ### Inverting the semantics

The instruction at the program point determines which clause of the semantics applies, so each
instruction gives an equivalence.  They are what the reasoning about a program is carried out
with. -/

section Inversion

variable {P : List Instr} {W : List Bool} {pc i j d p s t : ℕ} {μ : ℕ → Bool}

/-- **The clause that applies is the one of the instruction at the program point.** -/
theorem acc_inv (hacc : Acc P W pc μ) :
    (P.getI pc = iAcc) ∨
    (∃ i j d, P.getI pc = iNand i j d ∧ Acc P W (pc + 1) (memUpd μ d (!(μ i && μ j)))) ∨
    (∃ p d, P.getI pc = iRdIn p d ∧ Acc P W (pc + 1) (memUpd μ d (inBit W p))) ∨
    (∃ i t, P.getI pc = iBrIf i t ∧ μ i = true ∧ Acc P W t μ) ∨
    (∃ i t, P.getI pc = iBrIf i t ∧ μ i = false ∧ Acc P W (pc + 1) μ) ∨
    (∃ t, P.getI pc = iJmp t ∧ Acc P W t μ) ∨
    (∃ d b, P.getI pc = iEx d ∧ Acc P W (pc + 1) (memUpd μ d b)) ∨
    (∃ d, P.getI pc = iAll d ∧ Acc P W (pc + 1) (memUpd μ d false) ∧
      Acc P W (pc + 1) (memUpd μ d true)) ∨
    (∃ d, P.getI pc = iSet0 d ∧ Acc P W (pc + 1) (memUpd μ d false)) ∨
    (∃ d, P.getI pc = iSet1 d ∧ Acc P W (pc + 1) (memUpd μ d true)) ∨
    (∃ s d, P.getI pc = iCopy s d ∧ Acc P W (pc + 1) (memUpd μ d (μ s))) := by
  cases hacc with
  | acc h => exact Or.inl h
  | nand h h' => exact Or.inr (Or.inl ⟨_, _, _, h, h'⟩)
  | rdIn h h' => exact Or.inr (Or.inr (Or.inl ⟨_, _, h, h'⟩))
  | brT h hi h' => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, h, hi, h'⟩)))
  | brF h hi h' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, h, hi, h'⟩))))
  | jmp h h' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h, h'⟩)))))
  | ex h b h' =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, b, h, h'⟩))))))
  | all h h0 h1 =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h, h0, h1⟩)))))))
  | set0 h h' =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨_, h, h'⟩))))))))
  | set1 h h' =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨_, h, h'⟩)))))))))
  | copy h h' =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨_, _, h, h'⟩)))))))))

-- The tactic closing every clause of the inversion but the one that applies.
local macro "acc_inv_tac" h:ident : tactic =>
  `(tactic| (rcases acc_inv ‹Acc _ _ _ _› with
      h'|⟨_,_,_,h',h''⟩|⟨_,_,h',h''⟩|⟨_,_,h',hi,h''⟩|⟨_,_,h',hi,h''⟩|⟨_,h',h''⟩|
      ⟨_,b,h',h''⟩|⟨_,h',h0,h1⟩|⟨_,h',h''⟩|⟨_,h',h''⟩|⟨_,_,h',h''⟩ <;>
    rw [$h:ident] at h' <;> (try cases ‹Bool›) <;>
    simp_all [iNand, iRdIn, iBrIf, iEx, iAll, iAcc, iJmp, iSet0, iSet1, iCopy, iRej]))

/-- A `nand`. -/
theorem acc_nand_iff (h : P.getI pc = iNand i j d) :
    Acc P W pc μ ↔ Acc P W (pc + 1) (memUpd μ d (!(μ i && μ j))) := by
  refine ⟨fun hacc => ?_, fun hh => Acc.nand h hh⟩
  acc_inv_tac h

/-- A read of the input word. -/
theorem acc_rdIn_iff (h : P.getI pc = iRdIn p d) :
    Acc P W pc μ ↔ Acc P W (pc + 1) (memUpd μ d (inBit W p)) := by
  refine ⟨fun hacc => ?_, fun hh => Acc.rdIn h hh⟩
  acc_inv_tac h

/-- A branch that is taken. -/
theorem acc_brIf_true_iff (h : P.getI pc = iBrIf i t) (hi : μ i = true) :
    Acc P W pc μ ↔ Acc P W t μ := by
  refine ⟨fun hacc => ?_, fun hh => Acc.brT h hi hh⟩
  acc_inv_tac h

/-- A branch that is not taken. -/
theorem acc_brIf_false_iff (h : P.getI pc = iBrIf i t) (hi : μ i = false) :
    Acc P W pc μ ↔ Acc P W (pc + 1) μ := by
  refine ⟨fun hacc => ?_, fun hh => Acc.brF h hi hh⟩
  acc_inv_tac h

/-- A jump. -/
theorem acc_jmp_iff (h : P.getI pc = iJmp t) : Acc P W pc μ ↔ Acc P W t μ := by
  refine ⟨fun hacc => ?_, fun hh => Acc.jmp h hh⟩
  acc_inv_tac h

/-- An existential choice. -/
theorem acc_ex_iff (h : P.getI pc = iEx d) :
    Acc P W pc μ ↔ ∃ b, Acc P W (pc + 1) (memUpd μ d b) := by
  refine ⟨fun hacc => ?_, fun hh => hh.elim fun b hb => Acc.ex h b hb⟩
  acc_inv_tac h

/-- A universal choice. -/
theorem acc_all_iff (h : P.getI pc = iAll d) :
    Acc P W pc μ ↔
      (Acc P W (pc + 1) (memUpd μ d false) ∧ Acc P W (pc + 1) (memUpd μ d true)) := by
  refine ⟨fun hacc => ?_, fun hh => Acc.all h hh.1 hh.2⟩
  acc_inv_tac h

/-- Clearing a bit. -/
theorem acc_set0_iff (h : P.getI pc = iSet0 d) :
    Acc P W pc μ ↔ Acc P W (pc + 1) (memUpd μ d false) := by
  refine ⟨fun hacc => ?_, fun hh => Acc.set0 h hh⟩
  acc_inv_tac h

/-- Setting a bit. -/
theorem acc_set1_iff (h : P.getI pc = iSet1 d) :
    Acc P W pc μ ↔ Acc P W (pc + 1) (memUpd μ d true) := by
  refine ⟨fun hacc => ?_, fun hh => Acc.set1 h hh⟩
  acc_inv_tac h

/-- Copying a bit. -/
theorem acc_copy_iff (h : P.getI pc = iCopy s d) :
    Acc P W pc μ ↔ Acc P W (pc + 1) (memUpd μ d (μ s)) := by
  refine ⟨fun hacc => ?_, fun hh => Acc.copy h hh⟩
  acc_inv_tac h

/-- The rejecting instruction — and an address outside the program — rejects. -/
theorem not_acc_rej (h : P.getI pc = iRej) : ¬ Acc P W pc μ := by
  intro hacc
  acc_inv_tac h

/-- An address outside the program rejects. -/
theorem not_acc_of_le_length (h : P.length ≤ pc) : ¬ Acc P W pc μ :=
  not_acc_rej (by rw [List.getI_eq_default _ h]; rfl)

/-- An instruction that is not the rejecting one lies inside the program. -/
theorem lt_length_of_ne_rej (h : P.getI pc ≠ iRej) : pc < P.length := by
  by_contra hcon
  exact h (by rw [List.getI_eq_default _ (by omega)]; rfl)

end Inversion

/-! ### Well-formedness -/

/-- **A well-formed instruction**: its memory indices are below `mm`, its input position below
`n`, and the destination of a `nand` differs from its two sources. -/
def instrWf (I : Instr) (mm n : ℕ) : Prop :=
  if I.1 = 1 then
    I.2.1 < mm ∧ I.2.2.1 < mm ∧ I.2.2.2 < mm ∧ I.2.2.2 ≠ I.2.1 ∧ I.2.2.2 ≠ I.2.2.1
  else if I.1 = 2 then I.2.1 < n ∧ I.2.2.2 < mm
  else if I.1 = 3 then I.2.1 < mm
  else if I.1 = 4 then I.2.2.2 < mm
  else if I.1 = 5 then I.2.2.2 < mm
  else if I.1 = 8 then I.2.2.2 < mm
  else if I.1 = 9 then I.2.2.2 < mm
  else if I.1 = 10 then I.2.1 < mm ∧ I.2.2.2 < mm
  else True

/-- **A canonical instruction**: the operands an instruction of its opcode does not use are
`0`, so that the opcode determines the instruction.  The translation dispatches on the opcode
alone, so this is what makes the two readings of an instruction agree. -/
def instrCanon (I : Instr) : Prop :=
  if I.1 = 2 then I.2.2.1 = 0
  else if I.1 = 3 then I.2.2.2 = 0
  else if I.1 = 4 then I.2.1 = 0 ∧ I.2.2.1 = 0
  else if I.1 = 5 then I.2.1 = 0 ∧ I.2.2.1 = 0
  else if I.1 = 6 then I.2.1 = 0 ∧ I.2.2.1 = 0 ∧ I.2.2.2 = 0
  else if I.1 = 7 then I.2.1 = 0 ∧ I.2.2.2 = 0
  else if I.1 = 8 then I.2.1 = 0 ∧ I.2.2.1 = 0
  else if I.1 = 9 then I.2.1 = 0 ∧ I.2.2.1 = 0
  else if I.1 = 10 then I.2.2.1 = 0
  else True

/-- **A well-formed program**: at least one memory bit, and every instruction well-formed and
canonical. -/
def Wf (P : List Instr) (mm n : ℕ) : Prop := 0 < mm ∧ ∀ I ∈ P, instrWf I mm n ∧ instrCanon I

/-! ### The machine -/

/-- The existential transitions of the instruction at `pc`. -/
def progEx (P : List Instr) (pc : ℕ) : List RmExTr :=
  let I := P.getI pc
  if I.1 = 1 then
    -- `iNand i j d`
    [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].map fun old =>
      ((3 * pc, [], [(I.2.1, a), (I.2.2.1, b)], (I.2.2.2, old, !(a && b)), 3 * (pc + 1)) : RmExTr)
  else if I.1 = 2 then
    -- `iRdIn p d`
    [false, true].flatMap fun b => [false, true].map fun old =>
      ((3 * pc, [(I.2.1, b)], [], (I.2.2.2, old, b), 3 * (pc + 1)) : RmExTr)
  else if I.1 = 3 then
    -- `iBrIf i t`
    [((3 * pc, [], [(I.2.1, true)], (I.2.1, true, true), 3 * I.2.2.1) : RmExTr),
      ((3 * pc, [], [(I.2.1, false)], (I.2.1, false, false), 3 * (pc + 1)) : RmExTr)]
  else if I.1 = 4 then
    -- `iEx d`
    [false, true].flatMap fun old => [false, true].map fun new =>
      ((3 * pc, [], [], (I.2.2.2, old, new), 3 * (pc + 1)) : RmExTr)
  else if I.1 = 5 then
    -- `iAll d`: the two branches, in which the bit is written
    ([false, true].map fun old =>
      ((3 * pc + 1, [], [], (I.2.2.2, old, false), 3 * (pc + 1)) : RmExTr)) ++
    ([false, true].map fun old =>
      ((3 * pc + 2, [], [], (I.2.2.2, old, true), 3 * (pc + 1)) : RmExTr))
  else if I.1 = 7 then
    -- `iJmp t`
    [false, true].map fun v => ((3 * pc, [], [(0, v)], (0, v, v), 3 * I.2.2.1) : RmExTr)
  else if I.1 = 8 then
    -- `iSet0 d`
    [false, true].map fun old => ((3 * pc, [], [], (I.2.2.2, old, false), 3 * (pc + 1)) : RmExTr)
  else if I.1 = 9 then
    -- `iSet1 d`
    [false, true].map fun old => ((3 * pc, [], [], (I.2.2.2, old, true), 3 * (pc + 1)) : RmExTr)
  else if I.1 = 10 then
    -- `iCopy s d`
    [false, true].flatMap fun v => [false, true].map fun old =>
      ((3 * pc, [], [(I.2.1, v)], (I.2.2.2, old, v), 3 * (pc + 1)) : RmExTr)
  else []

/-- The universal transitions of the instruction at `pc`. -/
def progUn (P : List Instr) (pc : ℕ) : List RmUnTr :=
  let I := P.getI pc
  if I.1 = 5 then [((3 * pc, [], [], 3 * pc + 1, 3 * pc + 2) : RmUnTr)] else []

/-- The accepting conditions of the instruction at `pc`. -/
def progAcc (P : List Instr) (pc : ℕ) : List RmAcc :=
  let I := P.getI pc
  if I.1 = 6 then [((3 * pc, [], []) : RmAcc)] else []

/-- **The machine of a program.** -/
def progMach (P : List Instr) (mm : ℕ) : RecAltMem where
  mem := mm
  start := 0
  acc := (List.range P.length).flatMap (progAcc P)
  ex := (List.range P.length).flatMap (progEx P)
  un := (List.range P.length).flatMap (progUn P)

/-! ### Reading the transitions of the machine off the program -/

section Machine

variable {P : List Instr} {mm n pc i j d p s t : ℕ} {μ : ℕ → Bool} {W : List Bool}

theorem getI_mem (h : pc < P.length) : P.getI pc ∈ P := by
  rw [List.getI_eq_getElem _ h]; exact List.getElem_mem h

theorem mem_ex_of_mem_progEx {t : RmExTr} (hpc : pc < P.length) (ht : t ∈ progEx P pc) :
    t ∈ (progMach P mm).ex := List.mem_flatMap.2 ⟨pc, List.mem_range.2 hpc, ht⟩

theorem mem_un_of_mem_progUn {t : RmUnTr} (hpc : pc < P.length) (ht : t ∈ progUn P pc) :
    t ∈ (progMach P mm).un := List.mem_flatMap.2 ⟨pc, List.mem_range.2 hpc, ht⟩

theorem mem_acc_of_mem_progAcc {t : RmAcc} (hpc : pc < P.length) (ht : t ∈ progAcc P pc) :
    t ∈ (progMach P mm).acc := List.mem_flatMap.2 ⟨pc, List.mem_range.2 hpc, ht⟩

/-! The well-formedness conditions, instruction by instruction. -/

theorem wf_nand (hwf : Wf P mm n) (h : P.getI pc = iNand i j d) :
    i < mm ∧ j < mm ∧ d < mm ∧ d ≠ i ∧ d ≠ j := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iNand, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iNand] using hI

theorem wf_rdIn (hwf : Wf P mm n) (h : P.getI pc = iRdIn p d) : p < n ∧ d < mm := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iRdIn, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iRdIn] using hI

theorem wf_brIf (hwf : Wf P mm n) (h : P.getI pc = iBrIf i t) : i < mm := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iBrIf, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iBrIf] using hI

theorem wf_ex (hwf : Wf P mm n) (h : P.getI pc = iEx d) : d < mm := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iEx, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iEx] using hI

theorem wf_all (hwf : Wf P mm n) (h : P.getI pc = iAll d) : d < mm := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iAll, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iAll] using hI

theorem wf_set0 (hwf : Wf P mm n) (h : P.getI pc = iSet0 d) : d < mm := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iSet0, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iSet0] using hI

theorem wf_set1 (hwf : Wf P mm n) (h : P.getI pc = iSet1 d) : d < mm := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iSet1, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iSet1] using hI

theorem wf_copy (hwf : Wf P mm n) (h : P.getI pc = iCopy s d) : s < mm ∧ d < mm := by
  have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iCopy, iRej])
  have hI := (hwf.2 _ (getI_mem hpc)).1
  rw [h] at hI
  simpa [instrWf, iCopy] using hI

/-! The transitions each instruction contributes. -/

theorem mem_progEx_nand (h : P.getI pc = iNand i j d) (a b old : Bool) :
    ((3 * pc, [], [(i, a), (j, b)], (d, old, !(a && b)), 3 * (pc + 1)) : RmExTr)
      ∈ progEx P pc := by
  cases a <;> cases b <;> cases old <;> simp [progEx, h, iNand]

theorem mem_progEx_rdIn (h : P.getI pc = iRdIn p d) (b old : Bool) :
    ((3 * pc, [(p, b)], [], (d, old, b), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  cases b <;> cases old <;> simp [progEx, h, iRdIn]

theorem mem_progEx_brT (h : P.getI pc = iBrIf i t) :
    ((3 * pc, [], [(i, true)], (i, true, true), 3 * t) : RmExTr) ∈ progEx P pc := by
  simp [progEx, h, iBrIf]

theorem mem_progEx_brF (h : P.getI pc = iBrIf i t) :
    ((3 * pc, [], [(i, false)], (i, false, false), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  simp [progEx, h, iBrIf]

theorem mem_progEx_ex (h : P.getI pc = iEx d) (old new : Bool) :
    ((3 * pc, [], [], (d, old, new), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  cases old <;> cases new <;> simp [progEx, h, iEx]

theorem mem_progEx_all0 (h : P.getI pc = iAll d) (old : Bool) :
    ((3 * pc + 1, [], [], (d, old, false), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  cases old <;> simp [progEx, h, iAll]

theorem mem_progEx_all1 (h : P.getI pc = iAll d) (old : Bool) :
    ((3 * pc + 2, [], [], (d, old, true), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  cases old <;> simp [progEx, h, iAll]

theorem mem_progEx_jmp (h : P.getI pc = iJmp t) (v : Bool) :
    ((3 * pc, [], [(0, v)], (0, v, v), 3 * t) : RmExTr) ∈ progEx P pc := by
  cases v <;> simp [progEx, h, iJmp]

theorem mem_progEx_set0 (h : P.getI pc = iSet0 d) (old : Bool) :
    ((3 * pc, [], [], (d, old, false), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  cases old <;> simp [progEx, h, iSet0]

theorem mem_progEx_set1 (h : P.getI pc = iSet1 d) (old : Bool) :
    ((3 * pc, [], [], (d, old, true), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  cases old <;> simp [progEx, h, iSet1]

theorem mem_progEx_copy (h : P.getI pc = iCopy s d) (v old : Bool) :
    ((3 * pc, [], [(s, v)], (d, old, v), 3 * (pc + 1)) : RmExTr) ∈ progEx P pc := by
  cases v <;> cases old <;> simp [progEx, h, iCopy]

/-! Satisfaction of the small guards the translation produces. -/

theorem inSat_nil : InSat W [] := by intro q hq; cases hq

theorem memSat_nil : MemSat mm μ [] := by intro q hq; cases hq

theorem inSat_one (hp : p < W.length) : InSat W [(p, inBit W p)] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  exact mem_posFacts_iff_inBit.2 ⟨hp, rfl⟩

theorem memSat_one (hi : i < mm) : MemSat mm μ [(i, μ i)] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  exact ⟨hi, rfl⟩

theorem memSat_two (hi : i < mm) (hj : j < mm) : MemSat mm μ [(i, μ i), (j, μ j)] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨hi, rfl⟩
  · exact ⟨hj, rfl⟩

theorem mem_progUn_all (h : P.getI pc = iAll d) :
    ((3 * pc, [], [], 3 * pc + 1, 3 * pc + 2) : RmUnTr) ∈ progUn P pc := by
  simp [progUn, h, iAll]

theorem mem_progAcc_acc (h : P.getI pc = iAcc) :
    ((3 * pc, [], []) : RmAcc) ∈ progAcc P pc := by
  simp [progAcc, h, iAcc]

/-! ### Classifying the transitions -/

theorem mem_boolMap {α : Type*} {f : Bool → α} {a : α} (h : a ∈ [false, true].map f) :
    ∃ b, a = f b := by
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

theorem mem_boolFlatMap {α : Type*} {f : Bool → List α} {a : α}
    (h : a ∈ [false, true].flatMap f) : ∃ b, a ∈ f b := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at h
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- **Every transition of the machine comes from an instruction, in one of the listed
shapes.** -/
theorem progEx_cases (hcan : instrCanon (P.getI pc)) {tr : RmExTr} (htr : tr ∈ progEx P pc) :
    (∃ i j d a b old, P.getI pc = iNand i j d ∧
        tr = (3 * pc, [], [(i, a), (j, b)], (d, old, !(a && b)), 3 * (pc + 1))) ∨
    (∃ p d b old, P.getI pc = iRdIn p d ∧
        tr = (3 * pc, [(p, b)], [], (d, old, b), 3 * (pc + 1))) ∨
    (∃ i t, P.getI pc = iBrIf i t ∧
        (tr = (3 * pc, [], [(i, true)], (i, true, true), 3 * t) ∨
         tr = (3 * pc, [], [(i, false)], (i, false, false), 3 * (pc + 1)))) ∨
    (∃ d old new, P.getI pc = iEx d ∧ tr = (3 * pc, [], [], (d, old, new), 3 * (pc + 1))) ∨
    (∃ d old, P.getI pc = iAll d ∧
        (tr = (3 * pc + 1, [], [], (d, old, false), 3 * (pc + 1)) ∨
         tr = (3 * pc + 2, [], [], (d, old, true), 3 * (pc + 1)))) ∨
    (∃ t v, P.getI pc = iJmp t ∧ tr = (3 * pc, [], [(0, v)], (0, v, v), 3 * t)) ∨
    (∃ d old, P.getI pc = iSet0 d ∧ tr = (3 * pc, [], [], (d, old, false), 3 * (pc + 1))) ∨
    (∃ d old, P.getI pc = iSet1 d ∧ tr = (3 * pc, [], [], (d, old, true), 3 * (pc + 1))) ∨
    (∃ s d v old, P.getI pc = iCopy s d ∧
        tr = (3 * pc, [], [(s, v)], (d, old, v), 3 * (pc + 1))) := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [hI] at hcan
  rw [progEx, hI] at htr
  dsimp only at htr hcan
  by_cases h1 : op = 1
  · subst h1
    rw [if_pos rfl] at htr
    obtain ⟨a, htr⟩ := mem_boolFlatMap htr
    obtain ⟨b, htr⟩ := mem_boolFlatMap htr
    obtain ⟨old, rfl⟩ := mem_boolMap htr
    exact Or.inl ⟨x, y, z, a, b, old, rfl, rfl⟩
  by_cases h2 : op = 2
  · subst h2
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_pos rfl] at hcan
    subst hcan
    rw [if_neg h1, if_pos rfl] at htr
    obtain ⟨b, htr⟩ := mem_boolFlatMap htr
    obtain ⟨old, rfl⟩ := mem_boolMap htr
    exact Or.inr (Or.inl ⟨x, z, b, old, rfl, rfl⟩)
  by_cases h3 : op = 3
  · subst h3
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg h2, if_pos rfl] at hcan
    subst hcan
    rw [if_neg h1, if_neg h2, if_pos rfl] at htr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htr
    refine Or.inr (Or.inr (Or.inl ⟨x, y, rfl, ?_⟩))
    rcases htr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  by_cases h4 : op = 4
  · subst h4
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg h2, if_neg h3, if_pos rfl] at hcan
    obtain ⟨rfl, rfl⟩ := hcan
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos rfl] at htr
    obtain ⟨old, htr⟩ := mem_boolFlatMap htr
    obtain ⟨new, rfl⟩ := mem_boolMap htr
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨z, old, new, rfl, rfl⟩)))
  by_cases h5 : op = 5
  · subst h5
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg h2, if_neg h3, if_neg h4, if_pos rfl] at hcan
    obtain ⟨rfl, rfl⟩ := hcan
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos rfl] at htr
    rw [List.mem_append] at htr
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rcases htr with htr | htr
    · obtain ⟨old, rfl⟩ := mem_boolMap htr
      exact ⟨z, old, rfl, Or.inl rfl⟩
    · obtain ⟨old, rfl⟩ := mem_boolMap htr
      exact ⟨z, old, rfl, Or.inr rfl⟩
  by_cases h7 : op = 7
  · subst h7
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos rfl] at hcan
    obtain ⟨rfl, rfl⟩ := hcan
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos rfl] at htr
    obtain ⟨v, rfl⟩ := mem_boolMap htr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, v, rfl, rfl⟩)))))
  by_cases h8 : op = 8
  · subst h8
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h7, if_pos rfl] at hcan
    obtain ⟨rfl, rfl⟩ := hcan
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h7, if_pos rfl] at htr
    obtain ⟨old, rfl⟩ := mem_boolMap htr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨z, old, rfl, rfl⟩))))))
  by_cases h9 : op = 9
  · subst h9
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h7, if_neg h8, if_pos rfl] at hcan
    obtain ⟨rfl, rfl⟩ := hcan
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h7, if_neg h8,
      if_pos rfl] at htr
    obtain ⟨old, rfl⟩ := mem_boolMap htr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨z, old, rfl, rfl⟩)))))))
  by_cases h10 : op = 10
  · subst h10
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h7, if_neg h8, if_neg h9,
      if_pos rfl] at hcan
    subst hcan
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h7, if_neg h8, if_neg h9,
      if_pos rfl] at htr
    obtain ⟨v, htr⟩ := mem_boolFlatMap htr
    obtain ⟨old, rfl⟩ := mem_boolMap htr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨x, z, v, old, rfl, rfl⟩)))))))
  · exfalso
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h7, if_neg h8, if_neg h9,
      if_neg h10] at htr
    exact absurd htr List.not_mem_nil

/-- The universal transitions come from a universal instruction. -/
theorem progUn_cases (hcan : instrCanon (P.getI pc)) {tr : RmUnTr} (htr : tr ∈ progUn P pc) :
    ∃ d, P.getI pc = iAll d ∧ tr = (3 * pc, [], [], 3 * pc + 1, 3 * pc + 2) := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [hI] at hcan
  rw [progUn, hI] at htr
  dsimp only at htr hcan
  by_cases h5 : op = 5
  · subst h5
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg (by omega : ¬(5 = 2)), if_neg (by omega : ¬(5 = 3)), if_neg (by omega : ¬(5 = 4)),
      if_pos rfl] at hcan
    obtain ⟨rfl, rfl⟩ := hcan
    rw [if_pos rfl] at htr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htr
    exact ⟨z, rfl, htr⟩
  · rw [if_neg h5] at htr
    exact absurd htr List.not_mem_nil

/-- The accepting conditions come from an accepting instruction. -/
theorem progAcc_cases (hcan : instrCanon (P.getI pc)) {c : RmAcc} (hc : c ∈ progAcc P pc) :
    P.getI pc = iAcc ∧ c = (3 * pc, [], []) := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [hI] at hcan
  rw [progAcc, hI] at hc
  dsimp only at hc hcan
  by_cases h6 : op = 6
  · subst h6
    rw [instrCanon] at hcan
    dsimp only at hcan
    rw [if_neg (by omega : ¬(6 = 2)), if_neg (by omega : ¬(6 = 3)), if_neg (by omega : ¬(6 = 4)),
      if_neg (by omega : ¬(6 = 5)), if_pos rfl] at hcan
    obtain ⟨rfl, rfl, rfl⟩ := hcan
    rw [if_pos rfl] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    exact ⟨rfl, hc⟩
  · rw [if_neg h6] at hc
    exact absurd hc List.not_mem_nil

/-! ### The machine accepts whenever the program does -/

/-- **Forward simulation**: an accepting computation of the program is one of the machine. -/
theorem accFromN_of_acc (hwf : Wf P mm n) (hW : W.length = n) {pc : ℕ} {μ : ℕ → Bool}
    (hacc : Acc P W pc μ) : ∃ k, (progMach P mm).AccFromN W k (3 * pc) μ := by
  induction hacc with
  | @acc pc μ h =>
      exact ⟨1, RecAltMem.AccFromN.nil (c := ((3 * pc, [], []) : RmAcc))
        (mem_acc_of_mem_progAcc (lt_length_of_ne_rej (by rw [h]; simp [iAcc, iRej]))
          (mem_progAcc_acc h)) rfl inSat_nil memSat_nil⟩
  | @nand pc i j d μ h _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨hi, hj, hd, -, -⟩ := wf_nand hwf h
      exact ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [(i, μ i), (j, μ j)], (d, μ d, !(μ i && μ j)), 3 * (pc + 1)) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iNand, iRej]))
          (mem_progEx_nand h (μ i) (μ j) (μ d))) rfl inSat_nil (memSat_two hi hj) hd rfl hk⟩
  | @rdIn pc p d μ h _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨hp, hd⟩ := wf_rdIn hwf h
      exact ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [(p, inBit W p)], [], (d, μ d, inBit W p), 3 * (pc + 1)) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iRdIn, iRej]))
          (mem_progEx_rdIn h _ (μ d))) rfl (inSat_one (by omega)) memSat_nil hd rfl hk⟩
  | @brT pc i t μ h hi _ ih =>
      obtain ⟨k, hk⟩ := ih
      have him := wf_brIf hwf h
      refine ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [(i, true)], (i, true, true), 3 * t) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iBrIf, iRej]))
          (mem_progEx_brT h)) rfl inSat_nil ?_ him hi ?_⟩
      · show MemSat mm μ [(i, true)]
        rw [← hi]
        exact memSat_one him
      · show (progMach P mm).AccFromN W k (3 * t) (memUpd μ i true)
        have hmu : memUpd μ i true = μ := by
          funext y
          by_cases hy : y = i
          · subst hy; rw [memUpd_self, hi]
          · rw [memUpd_of_ne hy]
        rw [hmu]
        exact hk
  | @brF pc i t μ h hi _ ih =>
      obtain ⟨k, hk⟩ := ih
      have him := wf_brIf hwf h
      refine ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [(i, false)], (i, false, false), 3 * (pc + 1)) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iBrIf, iRej]))
          (mem_progEx_brF h)) rfl inSat_nil ?_ him hi ?_⟩
      · show MemSat mm μ [(i, false)]
        rw [← hi]
        exact memSat_one him
      · show (progMach P mm).AccFromN W k (3 * (pc + 1)) (memUpd μ i false)
        have hmu : memUpd μ i false = μ := by
          funext y
          by_cases hy : y = i
          · subst hy; rw [memUpd_self, hi]
          · rw [memUpd_of_ne hy]
        rw [hmu]
        exact hk
  | @jmp pc t μ h _ ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [(0, μ 0)], (0, μ 0, μ 0), 3 * t) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iJmp, iRej]))
          (mem_progEx_jmp h (μ 0))) rfl inSat_nil (memSat_one hwf.1) hwf.1 rfl ?_⟩
      show (progMach P mm).AccFromN W k (3 * t) (memUpd μ 0 (μ 0))
      have hmu : memUpd μ 0 (μ 0) = μ := by
        funext y
        by_cases hy : y = 0
        · subst hy; rw [memUpd_self]
        · rw [memUpd_of_ne hy]
      rw [hmu]
      exact hk
  | @ex pc d μ h b _ ih =>
      obtain ⟨k, hk⟩ := ih
      have hd := wf_ex hwf h
      exact ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [], (d, μ d, b), 3 * (pc + 1)) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iEx, iRej]))
          (mem_progEx_ex h (μ d) b)) rfl inSat_nil memSat_nil hd rfl hk⟩
  | @all pc d μ h _ _ ih0 ih1 =>
      obtain ⟨k0, hk0⟩ := ih0
      obtain ⟨k1, hk1⟩ := ih1
      have hd := wf_all hwf h
      have hpc : pc < P.length := lt_length_of_ne_rej (by rw [h]; simp [iAll, iRej])
      exact ⟨(k0 + 2) + (k1 + 2) + 1, RecAltMem.AccFromN.un
        (t := ((3 * pc, [], [], 3 * pc + 1, 3 * pc + 2) : RmUnTr))
        (mem_un_of_mem_progUn hpc (mem_progUn_all h)) rfl inSat_nil memSat_nil
        (RecAltMem.AccFromN.ex
          (t := ((3 * pc + 1, [], [], (d, μ d, false), 3 * (pc + 1)) : RmExTr))
          (mem_ex_of_mem_progEx hpc (mem_progEx_all0 h (μ d))) rfl inSat_nil memSat_nil hd rfl
          hk0)
        (RecAltMem.AccFromN.ex
          (t := ((3 * pc + 2, [], [], (d, μ d, true), 3 * (pc + 1)) : RmExTr))
          (mem_ex_of_mem_progEx hpc (mem_progEx_all1 h (μ d))) rfl inSat_nil memSat_nil hd rfl
          hk1)⟩
  | @set0 pc d μ h _ ih =>
      obtain ⟨k, hk⟩ := ih
      have hd := wf_set0 hwf h
      exact ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [], (d, μ d, false), 3 * (pc + 1)) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iSet0, iRej]))
          (mem_progEx_set0 h (μ d))) rfl inSat_nil memSat_nil hd rfl hk⟩
  | @set1 pc d μ h _ ih =>
      obtain ⟨k, hk⟩ := ih
      have hd := wf_set1 hwf h
      exact ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [], (d, μ d, true), 3 * (pc + 1)) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iSet1, iRej]))
          (mem_progEx_set1 h (μ d))) rfl inSat_nil memSat_nil hd rfl hk⟩
  | @copy pc s d μ h _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨hs, hd⟩ := wf_copy hwf h
      exact ⟨k + 2, RecAltMem.AccFromN.ex
        (t := ((3 * pc, [], [(s, μ s)], (d, μ d, μ s), 3 * (pc + 1)) : RmExTr))
        (mem_ex_of_mem_progEx (lt_length_of_ne_rej (by rw [h]; simp [iCopy, iRej]))
          (mem_progEx_copy h (μ s) (μ d))) rfl inSat_nil (memSat_one hs) hd rfl hk⟩

end Machine

/-! ### The program accepts whenever the machine does -/

section Backward

variable {P : List Instr} {mm n pc : ℕ} {μ : ℕ → Bool} {W : List Bool}

/-- Writing into a bit the value it already carries changes nothing. -/
theorem memUpd_eq_self {μ : ℕ → Bool} {i : ℕ} {v : Bool} (h : μ i = v) : memUpd μ i v = μ := by
  funext y
  by_cases hy : y = i
  · subst hy; rw [memUpd_self, h]
  · rw [memUpd_of_ne hy]

theorem exists_pc_ex {tr : RmExTr} (ht : tr ∈ (progMach P mm).ex) :
    ∃ pc, pc < P.length ∧ tr ∈ progEx P pc := by
  obtain ⟨pc, hpc, h⟩ := List.mem_flatMap.1 ht
  exact ⟨pc, List.mem_range.1 hpc, h⟩

theorem exists_pc_un {tr : RmUnTr} (ht : tr ∈ (progMach P mm).un) :
    ∃ pc, pc < P.length ∧ tr ∈ progUn P pc := by
  obtain ⟨pc, hpc, h⟩ := List.mem_flatMap.1 ht
  exact ⟨pc, List.mem_range.1 hpc, h⟩

theorem exists_pc_acc {c : RmAcc} (hc : c ∈ (progMach P mm).acc) :
    ∃ pc, pc < P.length ∧ c ∈ progAcc P pc := by
  obtain ⟨pc, hpc, h⟩ := List.mem_flatMap.1 hc
  exact ⟨pc, List.mem_range.1 hpc, h⟩

theorem canon_of_lt (hwf : Wf P mm n) (hpc : pc < P.length) : instrCanon (P.getI pc) :=
  (hwf.2 _ (getI_mem hpc)).2

/-- **What a state of the machine claims about the program.**  The state `3 * pc` claims that
the program accepts at `pc`; the two branch states `3 * pc + 1` and `3 * pc + 2` of a universal
instruction claim that it accepts at `pc + 1` once the branch has written its bit. -/
def MState (P : List Instr) (W : List Bool) (q : ℕ) (μ : ℕ → Bool) : Prop :=
  if q % 3 = 0 then Acc P W (q / 3) μ
  else if q % 3 = 1 then Acc P W (q / 3 + 1) (memUpd μ (P.getI (q / 3)).2.2.2 false)
  else Acc P W (q / 3 + 1) (memUpd μ (P.getI (q / 3)).2.2.2 true)

theorem mState_zero_iff : MState P W (3 * pc) μ ↔ Acc P W pc μ := by
  have h1 : 3 * pc % 3 = 0 := by omega
  have h2 : 3 * pc / 3 = pc := by omega
  rw [MState, h1, h2]
  norm_num

theorem mState_one_iff :
    MState P W (3 * pc + 1) μ ↔ Acc P W (pc + 1) (memUpd μ (P.getI pc).2.2.2 false) := by
  have h1 : (3 * pc + 1) % 3 = 1 := by omega
  have h2 : (3 * pc + 1) / 3 = pc := by omega
  rw [MState, h1, h2]
  norm_num

theorem mState_two_iff :
    MState P W (3 * pc + 2) μ ↔ Acc P W (pc + 1) (memUpd μ (P.getI pc).2.2.2 true) := by
  have h1 : (3 * pc + 2) % 3 = 2 := by omega
  have h2 : (3 * pc + 2) / 3 = pc := by omega
  rw [MState, h1, h2]
  norm_num

/-- **Backward simulation**: an accepting computation of the machine is one of the program. -/
theorem mState_of_accFromN (hwf : Wf P mm n) {k q : ℕ} {μ : ℕ → Bool}
    (h : (progMach P mm).AccFromN W k q μ) : MState P W q μ := by
  induction h with
  | @nil q μ c hc hq _ _ =>
      obtain ⟨pc, hpc, hcp⟩ := exists_pc_acc hc
      obtain ⟨hI, rfl⟩ := progAcc_cases (canon_of_lt hwf hpc) hcp
      dsimp only [RmAcc.st] at hq
      subst hq
      exact mState_zero_iff.2 (Acc.acc hI)
  | @ex k q μ tr ht hq hin hg _ hu _ ih =>
      obtain ⟨pc, hpc, htp⟩ := exists_pc_ex ht
      rcases progEx_cases (canon_of_lt hwf hpc) htp with
        ⟨i, j, d, a, b, old, hI, rfl⟩ | ⟨pos, d, b, old, hI, rfl⟩ | ⟨i, tgt, hI, rfl | rfl⟩ |
        ⟨d, old, new, hI, rfl⟩ | ⟨d, old, hI, rfl | rfl⟩ | ⟨tgt, v, hI, rfl⟩ |
        ⟨d, old, hI, rfl⟩ | ⟨d, old, hI, rfl⟩ | ⟨s, d, v, old, hI, rfl⟩
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        have ha : μ i = a := (hg (i, a) (by simp)).2
        have hb : μ j = b := (hg (j, b) (by simp)).2
        refine mState_zero_iff.2 (Acc.nand hI ?_)
        rw [ha, hb]
        exact mState_zero_iff.1 ih
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        have hbit : inBit W pos = b := (mem_posFacts_iff_inBit.1 (hin (pos, b) (by simp))).2
        refine mState_zero_iff.2 (Acc.rdIn hI ?_)
        rw [hbit]
        exact mState_zero_iff.1 ih
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        have hi : μ i = true := (hg (i, true) (by simp)).2
        refine mState_zero_iff.2 (Acc.brT hI hi ?_)
        rw [memUpd_eq_self hi] at ih
        exact mState_zero_iff.1 ih
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        have hi : μ i = false := (hg (i, false) (by simp)).2
        refine mState_zero_iff.2 (Acc.brF hI hi ?_)
        rw [memUpd_eq_self hi] at ih
        exact mState_zero_iff.1 ih
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        exact mState_zero_iff.2 (Acc.ex hI new (mState_zero_iff.1 ih))
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        refine mState_one_iff.2 ?_
        rw [hI]
        exact mState_zero_iff.1 ih
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        refine mState_two_iff.2 ?_
        rw [hI]
        exact mState_zero_iff.1 ih
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        have h0 : μ 0 = v := (hg (0, v) (by simp)).2
        refine mState_zero_iff.2 (Acc.jmp hI ?_)
        rw [memUpd_eq_self h0] at ih
        exact mState_zero_iff.1 ih
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        exact mState_zero_iff.2 (Acc.set0 hI (mState_zero_iff.1 ih))
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        exact mState_zero_iff.2 (Acc.set1 hI (mState_zero_iff.1 ih))
      · dsimp only [RmExTr.src, RmExTr.inG, RmExTr.memG, RmExTr.wr, RmExTr.tgt,
          MemWrite.idx, MemWrite.old, MemWrite.new] at hq hin hg hu ih
        subst hq
        have hs : μ s = v := (hg (s, v) (by simp)).2
        refine mState_zero_iff.2 (Acc.copy hI ?_)
        rw [hs]
        exact mState_zero_iff.1 ih
  | @un k₁ k₂ q μ tr ht hq _ _ _ _ ih₁ ih₂ =>
      obtain ⟨pc, hpc, htp⟩ := exists_pc_un ht
      obtain ⟨d, hI, rfl⟩ := progUn_cases (canon_of_lt hwf hpc) htp
      dsimp only [RmUnTr.src, RmUnTr.tgt₁, RmUnTr.tgt₂] at hq ih₁ ih₂
      subst hq
      rw [mState_one_iff, hI] at ih₁
      rw [mState_two_iff, hI] at ih₂
      exact mState_zero_iff.2 (Acc.all hI ih₁ ih₂)

end Backward

/-! ### What the translation satisfies -/

/-- **The machine of a program accepts exactly when the program does.** -/
theorem accepts_progMach_iff {P : List Instr} {mm n : ℕ} (hwf : Wf P mm n) {W : List Bool}
    (hW : W.length = n) :
    (progMach P mm).Accepts W ↔ Acc P W 0 (fun _ => false) := by
  constructor
  · rintro ⟨k, hk⟩
    have h : MState P W (3 * 0) (fun _ => false) := mState_of_accFromN hwf hk
    exact mState_zero_iff.1 h
  · intro h
    obtain ⟨k, hk⟩ := accFromN_of_acc hwf hW h
    exact ⟨k, hk⟩

/-- The machine of a well-formed program reads no position beyond the end of the word. -/
theorem posBelow_progMach {P : List Instr} {mm n : ℕ} (hwf : Wf P mm n) :
    (progMach P mm).PosBelow n := by
  refine ⟨fun tr htr => ?_, fun tr htr => ?_, fun c hc => ?_⟩
  · obtain ⟨pc, hpc, htp⟩ := exists_pc_ex htr
    intro q hq
    rcases progEx_cases (canon_of_lt hwf hpc) htp with
      ⟨i, j, d, a, b, old, hI, rfl⟩ | ⟨pos, d, b, old, hI, rfl⟩ | ⟨i, tgt, hI, rfl | rfl⟩ |
      ⟨d, old, new, hI, rfl⟩ | ⟨d, old, hI, rfl | rfl⟩ | ⟨tgt, v, hI, rfl⟩ |
      ⟨d, old, hI, rfl⟩ | ⟨d, old, hI, rfl⟩ | ⟨s, d, v, old, hI, rfl⟩
    all_goals first
      | exact absurd hq List.not_mem_nil
      | skip
    simp only [RmExTr.inG, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact (wf_rdIn hwf hI).1
  · obtain ⟨pc, hpc, htp⟩ := exists_pc_un htr
    obtain ⟨d, hI, rfl⟩ := progUn_cases (canon_of_lt hwf hpc) htp
    intro q hq
    exact absurd hq (by simp [RmUnTr.inG])
  · obtain ⟨pc, hpc, hcp⟩ := exists_pc_acc hc
    obtain ⟨hI, rfl⟩ := progAcc_cases (canon_of_lt hwf hpc) hcp
    intro q hq
    exact absurd hq (by simp [RmAcc.inG])

/-! ### The size of the machine -/

section Size

variable {P : List Instr} {pc : ℕ}

theorem length_progEx_le : (progEx P pc).length ≤ 8 := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [progEx, hI]
  dsimp only
  split_ifs <;> simp

theorem length_progUn_le : (progUn P pc).length ≤ 1 := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [progUn, hI]
  dsimp only
  split_ifs <;> simp

theorem length_progAcc_le : (progAcc P pc).length ≤ 1 := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [progAcc, hI]
  dsimp only
  split_ifs <;> simp

theorem guard_progEx_le (P : List Instr) (pc : ℕ) :
    ∀ tr ∈ progEx P pc, (RmExTr.inG tr).length + (RmExTr.memG tr).length ≤ 2 := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [progEx, hI]
  dsimp only
  split_ifs <;> simp [RmExTr.inG, RmExTr.memG]

theorem guard_progUn_le (P : List Instr) (pc : ℕ) :
    ∀ tr ∈ progUn P pc, (RmUnTr.inG tr).length + (RmUnTr.memG tr).length ≤ 2 := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [progUn, hI]
  dsimp only
  split_ifs <;> simp [RmUnTr.inG, RmUnTr.memG]

theorem guard_progAcc_le (P : List Instr) (pc : ℕ) :
    ∀ c ∈ progAcc P pc, (RmAcc.inG c).length + (RmAcc.memG c).length ≤ 2 := by
  rcases hI : P.getI pc with ⟨op, x, y, z⟩
  rw [progAcc, hI]
  dsimp only
  split_ifs <;> simp [RmAcc.inG, RmAcc.memG]

/-- The length of a list flat-mapped over the program points, from a bound per point. -/
theorem length_flatMap_range_le {α : Type*} {f : ℕ → List α} {c m : ℕ}
    (h : ∀ i, (f i).length ≤ c) : ((List.range m).flatMap f).length ≤ c * m := by
  rw [List.length_flatMap]
  have hb : ∀ x ∈ (List.range m).map fun i => (f i).length, x ≤ c := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact h i
  have := List.sum_le_card_nsmul _ c hb
  simpa [mul_comm] using this

/-- The sum of the guard lengths, from a bound per element. -/
theorem sum_guard_le {α : Type*} {l : List α} {g : α → ℕ} {c : ℕ} (h : ∀ x ∈ l, g x ≤ c) :
    (l.map g).sum ≤ c * l.length := by
  have := List.sum_le_card_nsmul _ c (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)
  simpa [mul_comm] using this

theorem length_ex_progMach (mm : ℕ) : ((progMach P mm).ex).length ≤ 8 * P.length :=
  length_flatMap_range_le fun _ => length_progEx_le

theorem length_un_progMach (mm : ℕ) : ((progMach P mm).un).length ≤ P.length := by
  have h := length_flatMap_range_le (f := progUn P) (c := 1) (m := P.length)
    fun _ => length_progUn_le
  rw [one_mul] at h
  exact h

theorem length_acc_progMach (mm : ℕ) : ((progMach P mm).acc).length ≤ P.length := by
  have h := length_flatMap_range_le (f := progAcc P) (c := 1) (m := P.length)
    fun _ => length_progAcc_le
  rw [one_mul] at h
  exact h

end Size

/-- The description of the machine of a program is quadratic in the program and its memory. -/
theorem rmConst_progMach_le (P : List Instr) (mm : ℕ) :
    rmConst (progMach P mm) ≤ 2000 * (P.length + mm + 1) * (P.length + mm + 1) := by
  set L := P.length with hL
  have hex : ((progMach P mm).ex).length ≤ 8 * L := length_ex_progMach mm
  have hun : ((progMach P mm).un).length ≤ L := length_un_progMach mm
  have hac : ((progMach P mm).acc).length ≤ L := length_acc_progMach mm
  have hsex : (((progMach P mm).ex).map fun t => (RmExTr.inG t).length +
      (RmExTr.memG t).length).sum ≤ 2 * ((progMach P mm).ex).length :=
    sum_guard_le fun tr htr => by
      obtain ⟨pc, -, htp⟩ := exists_pc_ex htr
      exact guard_progEx_le P pc tr htp
  have hsun : (((progMach P mm).un).map fun t => (RmUnTr.inG t).length +
      (RmUnTr.memG t).length).sum ≤ 2 * ((progMach P mm).un).length :=
    sum_guard_le fun tr htr => by
      obtain ⟨pc, -, htp⟩ := exists_pc_un htr
      exact guard_progUn_le P pc tr htp
  have hsac : (((progMach P mm).acc).map fun c => (RmAcc.inG c).length +
      (RmAcc.memG c).length).sum ≤ 2 * ((progMach P mm).acc).length :=
    sum_guard_le fun c hc => by
      obtain ⟨pc, -, hcp⟩ := exists_pc_acc hc
      exact guard_progAcc_le P pc c hcp
  have hmem : (progMach P mm).mem = mm := rfl
  have hbud : rmBudget (progMach P mm) ≤ 4 + mm + 2 * (8 * L) + 2 * L + 2 * L := by
    rw [rmBudget, hmem]
    have h1 : 2 * ((progMach P mm).ex).length ≤ 2 * (8 * L) := by omega
    have h2 : 2 * ((progMach P mm).un).length ≤ 2 * L := by omega
    have h3 : 2 * ((progMach P mm).acc).length ≤ 2 * L := by omega
    omega
  have hnum : rmNumActs (progMach P mm) ≤ 4 * (8 * L + L + L + 1) := by
    rw [rmNumActs]
    have : ((progMach P mm).ex).length + ((progMach P mm).un).length +
        ((progMach P mm).acc).length + 1 ≤ 8 * L + L + L + 1 := by omega
    omega
  have hmain : rmConst (progMach P mm) ≤
      (4 * (8 * L + L + L + 1)) * (4 + mm + 2 * (8 * L) + 2 * L + 2 * L) +
        6 * (2 * (8 * L) + 2 * L + L + 1) := by
    rw [rmConst]
    have hprod := Nat.mul_le_mul hnum hbud
    have hrest : 6 * (2 * ((progMach P mm).ex).length + 2 * ((progMach P mm).un).length +
        ((progMach P mm).acc).length + 1) ≤ 6 * (2 * (8 * L) + 2 * L + L + 1) := by omega
    omega
  refine le_trans hmain ?_
  set X := L + mm + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have e1 : 4 * (8 * L + L + L + 1) ≤ 44 * X := by omega
  have e2 : 4 + mm + 2 * (8 * L) + 2 * L + 2 * L ≤ 24 * X := by omega
  have e3 : 6 * (2 * (8 * L) + 2 * L + L + 1) ≤ 120 * X := by omega
  have eprod := Nat.mul_le_mul e1 e2
  nlinarith [eprod, e3, hX1]

end Compile

end HTN
