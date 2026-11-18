import HtnComplexity.Compile.Block
import ComplexityTheory.Compile.Gadget
/-!
# Evaluating a circuit inside an alternating bit program

`HtnComplexity/Compile/Prog.lean` gives the alternating bit programs, and
`ComplexityTheory/Compile/Circ.lean` the straight-line NAND circuits.  This file compiles a
circuit into a **straight-line block of `nand` instructions** of a program, and computes the
memory the block produces: over a memory whose wire area carries the inputs, the block leaves
the wire area carrying the wires of the circuit, and changes nothing else.

The layout is fixed by three numbers:

* `mbase` — the memory cell the wire `0` of the circuit lives in; the wire `w` lives in
  `mbase + w`;
* `zc` — a cell below `mbase` that is known to hold `false`;
* `nin` — the number of wires already written, that is the number of inputs of the circuit.

The `t`-th gate is one instruction, `HTN.Compile.circInstr`, writing into `mbase + nin + t`.  A
gate index that names a wire which has not been written yet reads `zc` instead, which is exactly
the `false` that `List.getI` returns out of range: this removes any well-formedness condition on
the circuit, and makes the destination of the instruction automatically different from its two
sources, which is what `HTN.Compile.instrWf` asks of a `nand`.

The results are `HTN.Compile.runInstrs_circProg` and `HTN.Compile.runInstrs_circProg_of_ne`
(the memory after the block), together with the bookkeeping lemmas
`HTN.Compile.length_circProg`, `HTN.Compile.getI_circProg`, `HTN.Compile.simple_circProg`,
`HTN.Compile.wf_circProg` and `HTN.Compile.primrec_circProg`.  Acceptance is then handled once
and for all by `HTN.Compile.acc_block_iff` and `HTN.Compile.accN_block`.
-/

namespace HTN

namespace Compile

open Syn

/-! ### The block -/

/-- The instruction computing the `t`-th gate of a circuit whose wires live from `mbase` on.  A
source that is not a wire yet reads the always-false cell `zc`. -/
def circInstr (mbase zc nin t : ℕ) (g : Gate) : Instr :=
  iNand (if g.1 < nin + t then mbase + g.1 else zc)
    (if g.2 < nin + t then mbase + g.2 else zc) (mbase + nin + t)

/-- The straight-line block of instructions evaluating a list of gates. -/
def circProg (mbase zc nin : ℕ) (gs : List Gate) : List Instr :=
  (List.range gs.length).map fun t => circInstr mbase zc nin t (gs.getI t)

@[simp] theorem length_circProg (mbase zc nin : ℕ) (gs : List Gate) :
    (circProg mbase zc nin gs).length = gs.length := by
  simp [circProg]

theorem getI_circProg {mbase zc nin t : ℕ} {gs : List Gate} (ht : t < gs.length) :
    (circProg mbase zc nin gs).getI t = circInstr mbase zc nin t (gs.getI t) := by
  rw [circProg, List.getI_eq_getElem _ (by simp [ht])]
  simp

/-- The cell an instruction of the block writes. -/
@[simp] theorem wrIdx_circInstr (mbase zc nin t : ℕ) (g : Gate) :
    wrIdx (circInstr mbase zc nin t g) = mbase + nin + t := rfl

/-- Every instruction of the block is simple. -/
theorem simple_circProg {mbase zc nin : ℕ} {gs : List Gate} :
    ∀ I ∈ circProg mbase zc nin gs, Simple I := by
  intro I hI
  rw [circProg, List.mem_map] at hI
  obtain ⟨t, -, rfl⟩ := hI
  exact simple_iNand _ _ _

/-- Shifting the base of the numbering by one is shifting the index of the gate by one. -/
theorem circInstr_succ (mbase zc nin t : ℕ) (g : Gate) :
    circInstr mbase zc nin (t + 1) g = circInstr mbase zc (nin + 1) t g := by
  rw [circInstr, circInstr, show nin + (t + 1) = nin + 1 + t by omega,
    show mbase + nin + (t + 1) = mbase + (nin + 1) + t by omega]

/-- The block of a gate list, from the front. -/
theorem circProg_cons (mbase zc nin : ℕ) (g : Gate) (gs : List Gate) :
    circProg mbase zc nin (g :: gs)
      = circInstr mbase zc nin 0 g :: circProg mbase zc (nin + 1) gs := by
  rw [circProg, circProg, List.length_cons, List.range_succ_eq_map, List.map_cons,
    List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro a _
  show circInstr mbase zc nin (a + 1) ((g :: gs).getI (a + 1))
    = circInstr mbase zc (nin + 1) a (gs.getI a)
  rw [show (g :: gs).getI (a + 1) = gs.getI a by simp, circInstr_succ]

/-! ### The memory after the block -/

/-- A cell outside the wires the block writes keeps its value. -/
theorem runInstrs_circProg_of_ne {W : List Bool} {mbase zc nin : ℕ} {gs : List Gate}
    {μ : ℕ → Bool} {a : ℕ} (ha : ∀ t < gs.length, a ≠ mbase + nin + t) :
    runInstrs W μ (circProg mbase zc nin gs) a = μ a := by
  refine runInstrs_of_forall_ne ?_
  intro I hI
  rw [circProg, List.mem_map] at hI
  obtain ⟨t, ht, rfl⟩ := hI
  rw [List.mem_range] at ht
  rw [wrIdx_circInstr]
  exact ha t ht

/-- **The block of a circuit computes its wires**: over a memory whose wire area carries the
inputs, the block leaves the wire area carrying the wires of the circuit. -/
theorem runInstrs_circProg {W : List Bool} {mbase zc : ℕ} (hzlt : zc < mbase) :
    ∀ {nin : ℕ} {gs : List Gate} {inp : List Bool} {μ : ℕ → Bool},
      μ zc = false → inp.length = nin → (∀ w < nin, μ (mbase + w) = inp.getI w) →
      ∀ w < nin + gs.length,
        runInstrs W μ (circProg mbase zc nin gs) (mbase + w) = (runGates inp gs).getI w := by
  intro nin gs
  induction gs generalizing nin with
  | nil =>
      intro inp μ _ _ hin w hw
      rw [circProg]
      simpa using hin w (by simpa using hw)
  | cons g gs ih =>
      intro inp μ hz hinp hin w hw
      -- the value the first instruction writes
      have hs1 : μ (if g.1 < nin + 0 then mbase + g.1 else zc) = inp.getI g.1 := by
        by_cases h : g.1 < nin
        · rw [if_pos (by omega), hin _ h]
        · rw [if_neg (by omega), hz, getI_of_le_length (by omega)]
      have hs2 : μ (if g.2 < nin + 0 then mbase + g.2 else zc) = inp.getI g.2 := by
        by_cases h : g.2 < nin
        · rw [if_pos (by omega), hin _ h]
        · rw [if_neg (by omega), hz, getI_of_le_length (by omega)]
      set val : Bool := !(inp.getI g.1 && inp.getI g.2) with hval
      have hstep : stepMem W μ (circInstr mbase zc nin 0 g) = memUpd μ (mbase + nin) val := by
        rw [circInstr, stepMem_iNand, hs1, hs2, show mbase + nin + 0 = mbase + nin by omega]
      set μ' : ℕ → Bool := memUpd μ (mbase + nin) val with hμ'
      have hgate : gateStep inp g = inp ++ [val] := by rw [gateStep_eq, hval]
      have hsnoc : (inp ++ [val]).getI nin = val := by
        rw [← hinp]; exact getI_snoc_self inp val
      have hz' : μ' zc = false := by rw [hμ', memUpd, if_neg (by omega), hz]
      have hlen' : (gateStep inp g).length = nin + 1 := by simp [hinp]
      have hin' : ∀ w < nin + 1, μ' (mbase + w) = (gateStep inp g).getI w := by
        intro w hw
        rcases Nat.lt_succ_iff_lt_or_eq.1 hw with h | rfl
        · rw [hμ', memUpd, if_neg (by omega), hin _ h, hgate, getI_snoc_lt (by omega)]
        · rw [hμ', memUpd, if_pos rfl, hgate, hsnoc]
      have := ih (nin := nin + 1) (inp := gateStep inp g) (μ := μ') hz' hlen' hin' w (by
        simp at hw; omega)
      rw [circProg_cons, runInstrs_cons, hstep, runGates_cons]
      exact this

/-! ### Well-formedness and uniformity -/

/-- Every instruction of the block is well-formed and canonical. -/
theorem wf_circInstr {mbase zc nin t mm n : ℕ} {g : Gate} (hzlt : zc < mbase)
    (hlt : mbase + nin + t < mm) :
    instrWf (circInstr mbase zc nin t g) mm n ∧ instrCanon (circInstr mbase zc nin t g) := by
  constructor
  · rw [instrWf, circInstr, iNand]
    refine ⟨?_, ?_, by omega, ?_, ?_⟩ <;> dsimp only <;> split_ifs <;> omega
  · rw [instrCanon, circInstr, iNand]
    norm_num

/-- **The block of a circuit is well-formed** whenever its wire area fits into the memory. -/
theorem wf_circProg {mbase zc nin mm n : ℕ} {gs : List Gate} (hzlt : zc < mbase)
    (hfit : mbase + nin + gs.length ≤ mm) :
    ∀ I ∈ circProg mbase zc nin gs, instrWf I mm n ∧ instrCanon I := by
  intro I hI
  rw [circProg, List.mem_map] at hI
  obtain ⟨t, ht, rfl⟩ := hI
  rw [List.mem_range] at ht
  exact wf_circInstr hzlt (by omega)

/-- The block of a circuit is produced by an algorithm. -/
theorem primrec_circProg {mb zcf nf : ℕ → ℕ} {gf : ℕ → List Gate} (hmb : Primrec mb)
    (hzc : Primrec zcf) (hn : Primrec nf) (hg : Primrec gf) :
    Primrec fun n => circProg (mb n) (zcf n) (nf n) (gf n) := by
  have hrange : Primrec fun n : ℕ => List.range (gf n).length :=
    Primrec.list_range.comp (Primrec.list_length.comp hg)
  refine Primrec.list_map hrange ?_
  -- the pair is `(n, t)`
  have hn1 : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have ht : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have hgate : Primrec fun p : ℕ × ℕ => (gf p.1).getI p.2 :=
    Primrec.list_getI.comp (hg.comp hn1) ht
  have hg1 : Primrec fun p : ℕ × ℕ => ((gf p.1).getI p.2).1 := Primrec.fst.comp hgate
  have hg2 : Primrec fun p : ℕ × ℕ => ((gf p.1).getI p.2).2 := Primrec.snd.comp hgate
  have hmb' : Primrec fun p : ℕ × ℕ => mb p.1 := hmb.comp hn1
  have hzc' : Primrec fun p : ℕ × ℕ => zcf p.1 := hzc.comp hn1
  have hnn : Primrec fun p : ℕ × ℕ => nf p.1 + p.2 := Primrec.nat_add.comp (hn.comp hn1) ht
  have hd : Primrec fun p : ℕ × ℕ => mb p.1 + nf p.1 + p.2 :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hmb' (hn.comp hn1)) ht
  have hsrc1 : Primrec fun p : ℕ × ℕ =>
      if ((gf p.1).getI p.2).1 < nf p.1 + p.2 then mb p.1 + ((gf p.1).getI p.2).1
      else zcf p.1 :=
    Primrec.ite (PrimrecRel.comp Primrec.nat_lt hg1 hnn)
      (Primrec.nat_add.comp hmb' hg1) hzc'
  have hsrc2 : Primrec fun p : ℕ × ℕ =>
      if ((gf p.1).getI p.2).2 < nf p.1 + p.2 then mb p.1 + ((gf p.1).getI p.2).2
      else zcf p.1 :=
    Primrec.ite (PrimrecRel.comp Primrec.nat_lt hg2 hnn)
      (Primrec.nat_add.comp hmb' hg2) hzc'
  exact Primrec.pair (Primrec.const 1) (Primrec.pair hsrc1 (Primrec.pair hsrc2 hd))

end Compile

end HTN
