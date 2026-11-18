import HtnComplexity.Compile.Layout
import ComplexityTheory.Compile.Base
import ComplexityTheory.Compile.Fix
/-!
# The data the compiled program is built from, and its memory invariant

`HtnComplexity/Compile/Layout.lean` gives the *syntax* of the program simulating an
alternating machine with a polynomial memory.  This file bolts the syntax onto the machine: a
`HTN.Compile.Sim` is a machine of `HTN.PSpace.ASpace` together with a uniform circuit family for
each of its five components, and an input length; from it the layout `HTN.Compile.Sim.lay` is
read off.

The **memory invariant** `HTN.Compile.Sim.MemOk` says what the memory carries at the head of the
loop: the two constants, the width mask, the input word at the cell bound, and the current
configuration.  The rest of the memory — the wires of the circuits and the scratch cells of the
guess — is unconstrained, and the blocks of the program only ever write there, which is what
`HTN.Compile.Sim.MemOk.of_agree` is for.

The other tool of this file is `HTN.Compile.circRead`: over a memory whose wire area carries the
cell encoding of the arguments, the block of a circuit of a family leaves the output wires
carrying the cell encoding of the value.
-/

namespace HTN

namespace Compile

open Syn PSpace PTime

/-! ### Reading the value of a circuit of a family off the memory -/

/-- **The block of a circuit of a uniform family computes the function**: the cell `mbase + w`,
for `w` the `i`-th output wire, carries the `i`-th bit of the cell encoding of the value. -/
theorem circRead {f : Fn} {k : ℕ} (F : CircFam f k) (N : ℕ) (args : Args)
    (hk : args.length = k) (hlen : ∀ a ∈ args, a.length ≤ N)
    {W : List Bool} {μ : ℕ → Bool} {mbase zc : ℕ} (hz : zc < mbase) (hzf : μ zc = false)
    (hin : ∀ w < 2 * N * k, μ (mbase + w) = (encArgs k N args).getI w)
    {i : ℕ} (hi : i < 2 * F.B.eval N) :
    runInstrs W μ (circProg mbase zc (2 * N * k) (F.C N).gates) (mbase + (F.C N).out.getI i)
      = (encStr (F.B.eval N) (f args)).getI i := by
  have hnin : (F.C N).nin = 2 * N * k := F.nin_eq N
  have hout : i < (F.C N).out.length := by rw [F.out_length N]; exact hi
  have hlt : (F.C N).out.getI i < (F.C N).nin + (F.C N).gates.length :=
    F.out_lt N _ (by rw [List.getI_eq_getElem _ hout]; exact List.getElem_mem hout)
  have hrun := runInstrs_circProg (W := W) (mbase := mbase) (zc := zc) hz
    (nin := 2 * N * k) (gs := (F.C N).gates) (inp := encArgs k N args) (μ := μ)
    hzf (by simp) hin ((F.C N).out.getI i) (by rw [← hnin]; exact hlt)
  rw [hrun]
  have : (runGates (encArgs k N args) (F.C N).gates).getI ((F.C N).out.getI i)
      = ((F.C N).eval (encArgs k N args)).getI i := (getI_eval _ _ hout).symm
  rw [this, F.correct N args hk hlen]

/-- **The block of a circuit of a uniform family for a predicate computes it**: the cell
`mbase + w`, for `w` the output wire `1`, carries the value of the predicate. -/
theorem circReadB {p : Args → Bool} {k : ℕ} (F : CircFam (fun args => [p args]) k) (N : ℕ)
    (args : Args) (hk : args.length = k) (hlen : ∀ a ∈ args, a.length ≤ N)
    {W : List Bool} {μ : ℕ → Bool} {mbase zc : ℕ} (hz : zc < mbase) (hzf : μ zc = false)
    (hin : ∀ w < 2 * N * k, μ (mbase + w) = (encArgs k N args).getI w) :
    runInstrs W μ (circProg mbase zc (2 * N * k) (F.C N).gates) (mbase + (F.C N).out.getI 1)
      = p args := by
  have h1 : 1 ≤ F.B.eval N := by
    have := F.len_le N args hk hlen
    simpa using this
  rw [circRead F N args hk hlen hz hzf hin (by omega)]
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, getI_encStr_val _ (by omega)]
  simp

/-- **The block of a circuit of a uniform family computes the function**, with the number of
input wires given in whatever form the layout writes it. -/
theorem circRead' {f : Fn} {k : ℕ} (F : CircFam f k) (N : ℕ) (args : Args)
    (hk : args.length = k) (hlen : ∀ a ∈ args, a.length ≤ N)
    {W : List Bool} {μ : ℕ → Bool} {mbase zc width : ℕ} (hwidth : width = 2 * N * k)
    (hz : zc < mbase) (hzf : μ zc = false)
    (hin : ∀ w < width, μ (mbase + w) = (encArgs k N args).getI w)
    {i : ℕ} (hi : i < 2 * F.B.eval N) :
    runInstrs W μ (circProg mbase zc width (F.C N).gates) (mbase + (F.C N).out.getI i)
      = (encStr (F.B.eval N) (f args)).getI i := by
  subst hwidth
  exact circRead F N args hk hlen hz hzf hin hi

/-! ### The data -/

/-- **What the compiled program is built from**: an alternating machine with a polynomial
memory, an input length, and a uniform circuit family for each of the five components of the
machine. -/
structure Sim where
  /-- The machine. -/
  M : ASpace
  /-- The length of the inputs the program is built for. -/
  n : ℕ
  /-- The circuits of the width. -/
  FW : CircFam M.widthF 1
  /-- The circuits of the initial configuration. -/
  FI : CircFam M.initF 1
  /-- The circuits of the acceptance test. -/
  FA : CircFam (fun args => [M.accB args]) 2
  /-- The circuits of the classification test. -/
  FU : CircFam (fun args => [M.univB args]) 2
  /-- The circuits of the transition test. -/
  FS : CircFam (fun args => [M.stepB args]) 3

namespace Sim

variable (S : Sim)

/-- The bound on the length of the width template. -/
def BW : ℕ := S.FW.B.eval S.n

/-- The bound on the length of the initial configuration. -/
def BI : ℕ := S.FI.B.eval S.n

/-- The number of cells a configuration is encoded in. -/
def NN : ℕ := S.n + S.BW + S.BI

/-- **The layout of the compiled program.** -/
def lay : Lay where
  n := S.n
  NN := S.NN
  CW := S.FW.C S.n
  CI := S.FI.C S.n
  CA := S.FA.C S.NN
  CU := S.FU.C S.NN
  CS := S.FS.C S.NN
  BW := S.BW
  BI := S.BI

@[simp] theorem lay_n : S.lay.n = S.n := rfl
@[simp] theorem lay_NN : S.lay.NN = S.NN := rfl
@[simp] theorem lay_CW : S.lay.CW = S.FW.C S.n := rfl
@[simp] theorem lay_CI : S.lay.CI = S.FI.C S.n := rfl
@[simp] theorem lay_CA : S.lay.CA = S.FA.C S.NN := rfl
@[simp] theorem lay_CU : S.lay.CU = S.FU.C S.NN := rfl
@[simp] theorem lay_CS : S.lay.CS = S.FS.C S.NN := rfl
@[simp] theorem lay_BW : S.lay.BW = S.BW := rfl
@[simp] theorem lay_BI : S.lay.BI = S.BI := rfl

/-- The program. -/
def prog : List Instr := S.lay.prog

/-! ### The addresses -/

theorem aG_eq : Lay.aG = 2 := rfl

theorem aC_eq : S.lay.aC = 2 + 2 * S.NN := rfl

theorem aX_eq : S.lay.aX = 2 + 4 * S.NN := rfl

theorem aS_eq : S.lay.aS = 2 + 6 * S.NN := rfl

theorem aMW_eq : S.lay.aMW = S.lay.aS + S.lay.gmax := rfl

theorem aT_eq : S.lay.aT = S.lay.aMW + S.NN := rfl

theorem gA_le : (S.FA.C S.NN).gates.length ≤ S.lay.gmax := le_max_left _ _

theorem gmaxA : S.lay.CA.gates.length ≤ S.lay.gmax := by rw [Lay.gmax]; exact le_max_left _ _

theorem gmaxU : S.lay.CU.gates.length ≤ S.lay.gmax := by
  rw [Lay.gmax]; exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem gmaxS : S.lay.CS.gates.length ≤ S.lay.gmax := by
  rw [Lay.gmax]; exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem gU_le : (S.FU.C S.NN).gates.length ≤ S.lay.gmax :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem gS_le : (S.FS.C S.NN).gates.length ≤ S.lay.gmax :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-! ### The memory invariant -/

/-- **What the memory carries at the head of the loop.** -/
structure MemOk (x c : List Bool) (μ : ℕ → Bool) : Prop where
  /-- The cell `0` is always false. -/
  z : μ 0 = false
  /-- The cell `1` is always true. -/
  one : μ 1 = true
  /-- The width mask. -/
  mask : ∀ i < S.NN, μ (S.lay.aMW + i) = decide (i < S.M.w x)
  /-- The input word, at the cell bound. -/
  inp : ∀ r < 2 * S.NN, μ (S.lay.aX + r) = (encStr S.NN x).getI r
  /-- The current configuration. -/
  cfg : ∀ r < 2 * S.NN, μ (S.lay.aC + r) = (encStr S.NN c).getI r

/-- The cells the invariant speaks about. -/
def Inv (a : ℕ) : Prop :=
  a = 0 ∨ a = 1 ∨ (∃ i < S.NN, a = S.lay.aMW + i) ∨ (∃ r < 2 * S.NN, a = S.lay.aX + r) ∨
    (∃ r < 2 * S.NN, a = S.lay.aC + r)

/-- The cells the blocks of the loop leave alone: those below the wire area, and those of the
width mask. -/
def Safe (a : ℕ) : Prop := a < S.lay.aS ∨ (S.lay.aMW ≤ a ∧ a < S.lay.aMW + S.NN)

variable {S}

/-- **A memory agreeing on the cells of the invariant satisfies the same invariant.** -/
theorem MemOk.of_agree {x c : List Bool} {μ ν : ℕ → Bool} (h : S.MemOk x c μ)
    (hag : ∀ a, S.Inv a → ν a = μ a) : S.MemOk x c ν where
  z := by rw [hag 0 (Or.inl rfl)]; exact h.z
  one := by rw [hag 1 (Or.inr (Or.inl rfl))]; exact h.one
  mask := fun i hi => by
    rw [hag _ (Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩)))]; exact h.mask i hi
  inp := fun r hr => by
    rw [hag _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩))))]; exact h.inp r hr
  cfg := fun r hr => by
    rw [hag _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩))))]; exact h.cfg r hr

/-- Every cell of the invariant is either below the wire area or inside the mask. -/
theorem safe_of_inv {a : ℕ} (h : S.Inv a) : S.Safe a := by
  rw [Safe]
  have hS := S.aS_eq
  have hC := S.aC_eq
  have hX := S.aX_eq
  rcases h with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · left; omega
  · left; omega
  · right; omega
  · left; omega
  · left; omega

/-- The cells of the guessed configuration are left alone by the circuits of the loop. -/
theorem safe_aG {r : ℕ} (hr : r < 2 * S.NN) : S.Safe (Lay.aG + r) := by
  have hS := S.aS_eq
  have hG := aG_eq
  left; omega

/-- A safe cell is not a wire of a circuit of the loop. -/
theorem safe_ne_wire {a t : ℕ} (h : S.Safe a) (ht : t < S.lay.gmax) : a ≠ S.lay.aS + t := by
  have hmw := S.aMW_eq
  rcases h with h' | ⟨h1, h2⟩ <;> omega

/-! ### The arguments of the circuits, read off the memory -/

/-- The cells from `aC` on carry the arguments of the acceptance and classification tests. -/
theorem args2 {x c : List Bool} {μ : ℕ → Bool} (h : S.MemOk x c μ) :
    ∀ w < 2 * S.NN * 2, μ (S.lay.aC + w) = (encArgs 2 S.NN [c, x]).getI w := by
  intro w hw
  rw [show (2 : ℕ) = 1 + 1 from rfl, encArgs_cons]
  by_cases hlt : w < 2 * S.NN
  · rw [List.getI_append _ _ _ (by simpa using hlt)]
    exact h.cfg w hlt
  · have hw' : w - 2 * S.NN < 2 * S.NN := by omega
    rw [List.getI_append_right _ _ _ (by simpa using hlt), length_encStr,
      show S.lay.aC + w = S.lay.aX + (w - 2 * S.NN) by rw [S.aC_eq, S.aX_eq]; omega,
      h.inp _ hw', show (1 : ℕ) = 0 + 1 from rfl, encArgs_cons,
      List.getI_append _ _ _ (by simpa using hw')]

/-- The cells from `aG` on carry the arguments of the transition test. -/
theorem args3 {x c c' : List Bool} {μ : ℕ → Bool} (h : S.MemOk x c μ)
    (hg : ∀ r < 2 * S.NN, μ (Lay.aG + r) = (encStr S.NN c').getI r) :
    ∀ w < 2 * S.NN * 3, μ (Lay.aG + w) = (encArgs 3 S.NN [c', c, x]).getI w := by
  intro w hw
  rw [show (3 : ℕ) = 2 + 1 from rfl, encArgs_cons]
  by_cases hlt : w < 2 * S.NN
  · rw [List.getI_append _ _ _ (by simpa using hlt)]
    exact hg w hlt
  · have hw' : w - 2 * S.NN < 2 * S.NN * 2 := by omega
    rw [List.getI_append_right _ _ _ (by simpa using hlt), length_encStr,
      show Lay.aG + w = S.lay.aC + (w - 2 * S.NN) by rw [S.aC_eq, aG_eq]; omega,
      args2 h _ hw']

end Sim

end Compile

end HTN
