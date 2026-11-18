import HtnComplexity.Compile.CircProg
import HtnComplexity.Compile.Region
import HtnComplexity.Compile.Guess
/-!
# The layout of the compiled program

This file is the **syntax** of the program that simulates an alternating machine with a
polynomial memory: the memory layout, the list of blocks, and where each block sits.  Nothing
here mentions the machine; the semantic hypotheses enter in
`HtnComplexity/Compile/Loop.lean`.

The data is a `HTN.Compile.Lay`: the input length `n`, the cell bound `NN` at which a
configuration is encoded, and the five circuits — the width, the initial configuration, the
acceptance test, the classification test and the transition test.  The memory is

    0     the cell that is always false          aS   the wires of the three loop circuits
    1     the cell that is always true           aMW  the width mask, `NN` cells
    aG    the guessed configuration, `2*NN`      aT   the scratch of the guess, `2*NN`
    aC    the configuration, `2*NN`              aXW  `encStr n x`, then the width wires
    aX    the input word, `2*NN`                 aXI  `encStr n x`, then the initial wires

`aG`, `aC` and `aX` are contiguous, so the transition circuit reads `encArgs 3 NN [c', c, x]` at
`aG` and the two tests read `encArgs 2 NN [c, x]` at `aC`; both then have their wires at `aS`,
which is harmless because the two are never live at the same time.
-/

namespace HTN

namespace Compile

open Syn

/-- **The data the compiled program is laid out from.** -/
structure Lay where
  /-- The length of the input word. -/
  n : ℕ
  /-- The number of cells a configuration is encoded in. -/
  NN : ℕ
  /-- The circuit of the width. -/
  CW : Circ
  /-- The circuit of the initial configuration. -/
  CI : Circ
  /-- The circuit of the acceptance test. -/
  CA : Circ
  /-- The circuit of the classification test. -/
  CU : Circ
  /-- The circuit of the transition test. -/
  CS : Circ
  /-- The bound at which the width circuit writes its value. -/
  BW : ℕ
  /-- The bound at which the initial-configuration circuit writes its value. -/
  BI : ℕ

namespace Lay

variable (L : Lay)

/-! ### The addresses -/

/-- The guessed configuration.  It is the first cell after the two constants. -/
def aG : ℕ := 2

/-- The current configuration. -/
def aC : ℕ := 2 + 2 * L.NN

/-- The input word, encoded at the cell bound. -/
def aX : ℕ := 2 + 4 * L.NN

/-- The wires of the three circuits of the loop. -/
def aS : ℕ := 2 + 6 * L.NN

/-- The room the wires of the three circuits of the loop need. -/
def gmax : ℕ := max L.CA.gates.length (max L.CU.gates.length L.CS.gates.length)

/-- The width mask. -/
def aMW : ℕ := L.aS + L.gmax

/-- The scratch cells of the guess. -/
def aT : ℕ := L.aMW + L.NN

/-- The input word at the bound `n`, and the wires of the width circuit. -/
def aXW : ℕ := L.aT + 2 * L.NN

/-- The input word at the bound `n`, and the wires of the initial-configuration circuit. -/
def aXI : ℕ := L.aXW + 2 * L.n + L.CW.gates.length

/-- The number of memory cells. -/
def mm : ℕ := L.aXI + 2 * L.n + L.CI.gates.length

/-! ### The cells the program reads a circuit's answer off -/

/-- The cell carrying the acceptance bit. -/
def accBit : ℕ := L.aC + L.CA.out.getI 1

/-- The cell carrying the classification bit. -/
def univBit : ℕ := L.aC + L.CU.out.getI 1

/-- The cell carrying the transition bit. -/
def stepBit : ℕ := aG + L.CS.out.getI 1

/-- The cell the `i`-th bit of the width mask is gathered from. -/
def maskSrc (i : ℕ) : ℕ := if i < L.BW then L.aXW + L.CW.out.getI (2 * i) else 0

/-- The cell the `r`-th bit of the initial configuration is gathered from. -/
def initSrc (r : ℕ) : ℕ := if r < 2 * L.BI then L.aXI + L.CI.out.getI r else 0

/-! ### The labels -/

/-- The head of the loop. -/
def lL : ℕ :=
  1 + 2 * L.n + L.CW.gates.length + L.NN + 2 * L.n + L.CI.gates.length + 2 * L.NN + 2 * L.NN

/-- The universal copy of the guess. -/
def lUNI : ℕ :=
  L.lL + L.CA.gates.length + 1 + L.CU.gates.length + 1 + 4 * L.NN + L.CS.gates.length + 2

/-- Where the two copies meet again. -/
def lCONT : ℕ := L.lUNI + 4 * L.NN + L.CS.gates.length + 2

/-- The accepting instruction. -/
def lACC : ℕ := L.lCONT + 2 * L.NN + 1

/-! ### The program -/

/-- The blocks of the program. -/
def blocks : List (List Instr) :=
  [ [iSet1 1],
    encInpProg L.aXW L.n L.n,
    circProg L.aXW 0 (2 * L.n) L.CW.gates,
    gatherProg L.aMW L.maskSrc L.NN,
    encInpProg L.aXI L.n L.n,
    circProg L.aXI 0 (2 * L.n) L.CI.gates,
    gatherProg L.aC L.initSrc (2 * L.NN),
    encInpProg L.aX L.NN L.n,
    circProg L.aC 0 (4 * L.NN) L.CA.gates,
    [iBrIf L.accBit L.lACC],
    circProg L.aC 0 (4 * L.NN) L.CU.gates,
    [iBrIf L.univBit L.lUNI],
    guessProg false aG L.aMW L.aT 0 L.NN,
    circProg aG 0 (6 * L.NN) L.CS.gates,
    [iBrIf L.stepBit L.lCONT, iRej],
    guessProg true aG L.aMW L.aT 0 L.NN,
    circProg aG 0 (6 * L.NN) L.CS.gates,
    [iBrIf L.stepBit L.lCONT, iAcc],
    gatherProg L.aC (fun i => aG + i) (2 * L.NN),
    [iJmp L.lL],
    [iAcc] ]

/-- **The program.** -/
def prog : List Instr := L.blocks.flatten

theorem length_blocks : L.blocks.length = 21 := rfl

/-- The `i`-th block is found at the sum of the lengths of the blocks before it. -/
theorem getI_prog {i : ℕ} (hi : i < 21) {t : ℕ} (ht : t < (L.blocks.getI i).length) :
    L.prog.getI (((L.blocks.take i).map List.length).sum + t) = (L.blocks.getI i).getI t :=
  getI_flatten (by rw [length_blocks]; exact hi) ht

/-- The length of the program. -/
theorem length_prog : L.prog.length = L.lACC + 1 := by
  rw [prog, List.length_flatten, blocks]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, length_encInpProg, length_circProg, length_gatherProg, length_guessProg]
  rw [lACC, lCONT, lUNI, lL]
  ring


/-! ### Where each block sits

The blocks are placed one after another; these are the program points each of them starts at.
The four that control jumps to — the head of the loop, the universal copy, the point where the
two copies meet again, and the accepting instruction — are the labels above. -/

/-- The offset of the width circuit. -/
def oCircW : ℕ := 1 + 2 * L.n

/-- The offset of the block gathering the width mask. -/
def oMask : ℕ := L.oCircW + L.CW.gates.length

/-- The offset of the block writing the input word for the initial circuit. -/
def oEncXI : ℕ := L.oMask + L.NN

/-- The offset of the initial-configuration circuit. -/
def oCircI : ℕ := L.oEncXI + 2 * L.n

/-- The offset of the block gathering the initial configuration. -/
def oInitC : ℕ := L.oCircI + L.CI.gates.length

/-- The offset of the block writing the input word at the cell bound. -/
def oEncX : ℕ := L.oInitC + 2 * L.NN

/-- The offset of the branch on the acceptance bit. -/
def oBrA : ℕ := L.lL + L.CA.gates.length

/-- The offset of the classification circuit. -/
def oCircU : ℕ := L.oBrA + 1

/-- The offset of the branch on the classification bit. -/
def oBrU : ℕ := L.oCircU + L.CU.gates.length

/-- The offset of the existential guess. -/
def oGuessE : ℕ := L.oBrU + 1

/-- The offset of the transition circuit of the existential copy. -/
def oCircSE : ℕ := L.oGuessE + 4 * L.NN

/-- The offset of the branch on the transition bit of the existential copy. -/
def oBrSE : ℕ := L.oCircSE + L.CS.gates.length

/-- The offset of the transition circuit of the universal copy. -/
def oCircSA : ℕ := L.lUNI + 4 * L.NN

/-- The offset of the branch on the transition bit of the universal copy. -/
def oBrSA : ℕ := L.oCircSA + L.CS.gates.length

/-- The offset of the jump back to the head of the loop. -/
def oJmp : ℕ := L.lCONT + 2 * L.NN

/-- Where the block sits. -/
theorem at_setOne : ∀ t < ([iSet1 1] : List Instr).length, L.prog.getI (0 + t) = ([iSet1 1]).getI t := by
  intro t ht
  have hb : L.blocks.getI 0 = ([iSet1 1]) := rfl
  have ho : ((L.blocks.take 0).map List.length).sum = 0 := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 0) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_encXW : ∀ t < 2 * L.n, L.prog.getI (1 + t) = (encInpProg L.aXW L.n L.n).getI t := by
  intro t ht
  have hb : L.blocks.getI 1 = (encInpProg L.aXW L.n L.n) := rfl
  have ho : ((L.blocks.take 1).map List.length).sum = 1 := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 1) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_circW : ∀ t < L.CW.gates.length, L.prog.getI (L.oCircW + t) = (circProg L.aXW 0 (2 * L.n) L.CW.gates).getI t := by
  intro t ht
  have hb : L.blocks.getI 2 = (circProg L.aXW 0 (2 * L.n) L.CW.gates) := rfl
  have ho : ((L.blocks.take 2).map List.length).sum = L.oCircW := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 2) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_mask : ∀ t < L.NN, L.prog.getI (L.oMask + t) = (gatherProg L.aMW L.maskSrc L.NN).getI t := by
  intro t ht
  have hb : L.blocks.getI 3 = (gatherProg L.aMW L.maskSrc L.NN) := rfl
  have ho : ((L.blocks.take 3).map List.length).sum = L.oMask := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 3) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_encXI : ∀ t < 2 * L.n, L.prog.getI (L.oEncXI + t) = (encInpProg L.aXI L.n L.n).getI t := by
  intro t ht
  have hb : L.blocks.getI 4 = (encInpProg L.aXI L.n L.n) := rfl
  have ho : ((L.blocks.take 4).map List.length).sum = L.oEncXI := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 4) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_circI : ∀ t < L.CI.gates.length, L.prog.getI (L.oCircI + t) = (circProg L.aXI 0 (2 * L.n) L.CI.gates).getI t := by
  intro t ht
  have hb : L.blocks.getI 5 = (circProg L.aXI 0 (2 * L.n) L.CI.gates) := rfl
  have ho : ((L.blocks.take 5).map List.length).sum = L.oCircI := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 5) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_initC : ∀ t < 2 * L.NN, L.prog.getI (L.oInitC + t) = (gatherProg L.aC L.initSrc (2 * L.NN)).getI t := by
  intro t ht
  have hb : L.blocks.getI 6 = (gatherProg L.aC L.initSrc (2 * L.NN)) := rfl
  have ho : ((L.blocks.take 6).map List.length).sum = L.oInitC := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 6) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_encX : ∀ t < 2 * L.NN, L.prog.getI (L.oEncX + t) = (encInpProg L.aX L.NN L.n).getI t := by
  intro t ht
  have hb : L.blocks.getI 7 = (encInpProg L.aX L.NN L.n) := rfl
  have ho : ((L.blocks.take 7).map List.length).sum = L.oEncX := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 7) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_circA : ∀ t < L.CA.gates.length, L.prog.getI (L.lL + t) = (circProg L.aC 0 (4 * L.NN) L.CA.gates).getI t := by
  intro t ht
  have hb : L.blocks.getI 8 = (circProg L.aC 0 (4 * L.NN) L.CA.gates) := rfl
  have ho : ((L.blocks.take 8).map List.length).sum = L.lL := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 8) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_brA : ∀ t < ([iBrIf L.accBit L.lACC] : List Instr).length, L.prog.getI (L.oBrA + t) = ([iBrIf L.accBit L.lACC]).getI t := by
  intro t ht
  have hb : L.blocks.getI 9 = ([iBrIf L.accBit L.lACC]) := rfl
  have ho : ((L.blocks.take 9).map List.length).sum = L.oBrA := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 9) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_circU : ∀ t < L.CU.gates.length, L.prog.getI (L.oCircU + t) = (circProg L.aC 0 (4 * L.NN) L.CU.gates).getI t := by
  intro t ht
  have hb : L.blocks.getI 10 = (circProg L.aC 0 (4 * L.NN) L.CU.gates) := rfl
  have ho : ((L.blocks.take 10).map List.length).sum = L.oCircU := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 10) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_brU : ∀ t < ([iBrIf L.univBit L.lUNI] : List Instr).length, L.prog.getI (L.oBrU + t) = ([iBrIf L.univBit L.lUNI]).getI t := by
  intro t ht
  have hb : L.blocks.getI 11 = ([iBrIf L.univBit L.lUNI]) := rfl
  have ho : ((L.blocks.take 11).map List.length).sum = L.oBrU := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 11) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_guessEx : ∀ t < 4 * L.NN, L.prog.getI (L.oGuessE + t) = (guessProg false aG L.aMW L.aT 0 L.NN).getI t := by
  intro t ht
  have hb : L.blocks.getI 12 = (guessProg false aG L.aMW L.aT 0 L.NN) := rfl
  have ho : ((L.blocks.take 12).map List.length).sum = L.oGuessE := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 12) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_circSE : ∀ t < L.CS.gates.length, L.prog.getI (L.oCircSE + t) = (circProg aG 0 (6 * L.NN) L.CS.gates).getI t := by
  intro t ht
  have hb : L.blocks.getI 13 = (circProg aG 0 (6 * L.NN) L.CS.gates) := rfl
  have ho : ((L.blocks.take 13).map List.length).sum = L.oCircSE := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 13) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_brSE : ∀ t < ([iBrIf L.stepBit L.lCONT, iRej] : List Instr).length, L.prog.getI (L.oBrSE + t) = ([iBrIf L.stepBit L.lCONT, iRej]).getI t := by
  intro t ht
  have hb : L.blocks.getI 14 = ([iBrIf L.stepBit L.lCONT, iRej]) := rfl
  have ho : ((L.blocks.take 14).map List.length).sum = L.oBrSE := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 14) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_guessAll : ∀ t < 4 * L.NN, L.prog.getI (L.lUNI + t) = (guessProg true aG L.aMW L.aT 0 L.NN).getI t := by
  intro t ht
  have hb : L.blocks.getI 15 = (guessProg true aG L.aMW L.aT 0 L.NN) := rfl
  have ho : ((L.blocks.take 15).map List.length).sum = L.lUNI := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 15) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_circSA : ∀ t < L.CS.gates.length, L.prog.getI (L.oCircSA + t) = (circProg aG 0 (6 * L.NN) L.CS.gates).getI t := by
  intro t ht
  have hb : L.blocks.getI 16 = (circProg aG 0 (6 * L.NN) L.CS.gates) := rfl
  have ho : ((L.blocks.take 16).map List.length).sum = L.oCircSA := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 16) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_brSA : ∀ t < ([iBrIf L.stepBit L.lCONT, iAcc] : List Instr).length, L.prog.getI (L.oBrSA + t) = ([iBrIf L.stepBit L.lCONT, iAcc]).getI t := by
  intro t ht
  have hb : L.blocks.getI 17 = ([iBrIf L.stepBit L.lCONT, iAcc]) := rfl
  have ho : ((L.blocks.take 17).map List.length).sum = L.oBrSA := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 17) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_copyGC : ∀ t < 2 * L.NN, L.prog.getI (L.lCONT + t) = (gatherProg L.aC (fun i => aG + i) (2 * L.NN)).getI t := by
  intro t ht
  have hb : L.blocks.getI 18 = (gatherProg L.aC (fun i => aG + i) (2 * L.NN)) := rfl
  have ho : ((L.blocks.take 18).map List.length).sum = L.lCONT := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 18) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_jmp : ∀ t < ([iJmp L.lL] : List Instr).length, L.prog.getI (L.oJmp + t) = ([iJmp L.lL]).getI t := by
  intro t ht
  have hb : L.blocks.getI 19 = ([iJmp L.lL]) := rfl
  have ho : ((L.blocks.take 19).map List.length).sum = L.oJmp := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 19) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

/-- Where the block sits. -/
theorem at_acc : ∀ t < ([iAcc] : List Instr).length, L.prog.getI (L.lACC + t) = ([iAcc]).getI t := by
  intro t ht
  have hb : L.blocks.getI 20 = ([iAcc]) := rfl
  have ho : ((L.blocks.take 20).map List.length).sum = L.lACC := by
    simp only [blocks, List.take, List.map, List.sum_cons, List.sum_nil,
      length_encInpProg, length_circProg, length_gatherProg, length_guessProg,
      List.length_cons, List.length_nil]
    all_goals try simp only [oCircW, oMask, oEncXI, oCircI, oInitC, oEncX, lL, oBrA,
      oCircU, oBrU, oGuessE, oCircSE, oBrSE, lUNI, oCircSA, oBrSA, lCONT, oJmp, lACC]
    all_goals ring
  have h := L.getI_prog (i := 20) (by omega) (t := t) (by rw [hb]; simpa using ht)
  rwa [ho, hb] at h

end Lay

end Compile

end HTN
