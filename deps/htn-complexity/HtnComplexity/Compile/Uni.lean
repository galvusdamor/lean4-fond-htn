import HtnComplexity.Compile.Wf
import HtnComplexity.Compile.ProgPrim
/-!
# The compiled program, as a uniform family

The last two things a uniform family of machines (`HTN.Syn.UniRecMem`) asks of the compiled
program are that it be **produced by an algorithm** from the input length, and that its
description be of **polynomial size**.  This file supplies both:

* `HTN.Compile.primrec_encInpProg`, `HTN.Compile.primrec_gatherProg`,
  `HTN.Compile.primrec_guessProg` — the blocks that `HtnComplexity/Compile/CircProg.lean`
  did not already cover;
* `HTN.Compile.Sim.primrec_prog`, `HTN.Compile.Sim.primrec_mm` — the program and the memory
  width of the layout, for the family of `HTN.Compile.Sim.simAt`;
* `HTN.Compile.Sim.size_le` — the program and the memory width are bounded by a polynomial in
  the input length.
-/

namespace HTN

namespace Compile

open Syn PSpace PTime

/-! ### The blocks are produced by an algorithm -/

/-- The block writing the cell encoding of the input word is produced by an algorithm. -/
theorem primrec_encInpProg {df mf nf : ℕ → ℕ} (hd : Primrec df) (hm : Primrec mf)
    (hn : Primrec nf) : Primrec fun n => encInpProg (df n) (mf n) (nf n) := by
  refine Primrec.list_flatMap (Primrec.list_range.comp hm) ?_
  have hd' : Primrec fun p : ℕ × ℕ => df p.1 := hd.comp Primrec.fst
  have hn' : Primrec fun p : ℕ × ℕ => nf p.1 := hn.comp Primrec.fst
  have hi : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have h2i : Primrec fun p : ℕ × ℕ => df p.1 + 2 * p.2 :=
    Primrec.nat_add.comp hd' (Primrec.nat_mul.comp (Primrec.const 2) hi)
  have h2i1 : Primrec fun p : ℕ × ℕ => df p.1 + 2 * p.2 + 1 :=
    Primrec.nat_add.comp h2i (Primrec.const 1)
  have hpos : Primrec fun p : ℕ × ℕ => nf p.1 - 1 - p.2 :=
    Primrec.nat_sub.comp (Primrec.nat_sub.comp hn' (Primrec.const 1)) hi
  have hset1 : Primrec fun p : ℕ × ℕ => iSet1 (df p.1 + 2 * p.2) :=
    Primrec.pair (Primrec.const 9)
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const 0) h2i))
  have hset0 : Primrec fun p : ℕ × ℕ => iSet0 (df p.1 + 2 * p.2) :=
    Primrec.pair (Primrec.const 8)
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const 0) h2i))
  have hset0' : Primrec fun p : ℕ × ℕ => iSet0 (df p.1 + 2 * p.2 + 1) :=
    Primrec.pair (Primrec.const 8)
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const 0) h2i1))
  have hrd : Primrec fun p : ℕ × ℕ => iRdIn (nf p.1 - 1 - p.2) (df p.1 + 2 * p.2 + 1) :=
    Primrec.pair (Primrec.const 2)
      (Primrec.pair hpos (Primrec.pair (Primrec.const 0) h2i1))
  exact Primrec.ite (PrimrecRel.comp Primrec.nat_lt hi hn')
    (Primrec.list_cons.comp hset1 (Primrec.list_cons.comp hrd (Primrec.const [])))
    (Primrec.list_cons.comp hset0 (Primrec.list_cons.comp hset0' (Primrec.const [])))

/-- The block gathering a list of cells is produced by an algorithm. -/
theorem primrec_gatherProg {df lf : ℕ → ℕ} {sf : ℕ → ℕ → ℕ} (hd : Primrec df)
    (hs : Primrec fun p : ℕ × ℕ => sf p.1 p.2) (hl : Primrec lf) :
    Primrec fun n => gatherProg (df n) (sf n) (lf n) := by
  refine Primrec.list_map (Primrec.list_range.comp hl) ?_
  have hd' : Primrec fun p : ℕ × ℕ => df p.1 := hd.comp Primrec.fst
  have hi : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  exact Primrec.pair (Primrec.const 10)
    (Primrec.pair hs (Primrec.pair (Primrec.const 0) (Primrec.nat_add.comp hd' hi)))

/-- The block guessing a configuration is produced by an algorithm. -/
theorem primrec_guessProg (uni : Bool) {gf mwf tf jf mf : ℕ → ℕ} (hg : Primrec gf)
    (hmw : Primrec mwf) (ht : Primrec tf) (hj : Primrec jf) (hm : Primrec mf) :
    Primrec fun n => guessProg uni (gf n) (mwf n) (tf n) (jf n) (mf n) := by
  refine Primrec.list_flatMap (Primrec.list_range.comp hm) ?_
  have hg' : Primrec fun p : ℕ × ℕ => gf p.1 := hg.comp Primrec.fst
  have hmw' : Primrec fun p : ℕ × ℕ => mwf p.1 := hmw.comp Primrec.fst
  have ht' : Primrec fun p : ℕ × ℕ => tf p.1 := ht.comp Primrec.fst
  have hj' : Primrec fun p : ℕ × ℕ => jf p.1 := hj.comp Primrec.fst
  have hidx : Primrec fun p : ℕ × ℕ => jf p.1 + p.2 := Primrec.nat_add.comp hj' Primrec.snd
  have h2 : Primrec fun p : ℕ × ℕ => 2 * (jf p.1 + p.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) hidx
  have hT0 : Primrec fun p : ℕ × ℕ => tf p.1 + 2 * (jf p.1 + p.2) := Primrec.nat_add.comp ht' h2
  have hT1 : Primrec fun p : ℕ × ℕ => tf p.1 + 2 * (jf p.1 + p.2) + 1 :=
    Primrec.nat_add.comp hT0 (Primrec.const 1)
  have hG0 : Primrec fun p : ℕ × ℕ => gf p.1 + 2 * (jf p.1 + p.2) := Primrec.nat_add.comp hg' h2
  have hG1 : Primrec fun p : ℕ × ℕ => gf p.1 + 2 * (jf p.1 + p.2) + 1 :=
    Primrec.nat_add.comp hG0 (Primrec.const 1)
  have hMW : Primrec fun p : ℕ × ℕ => mwf p.1 + (jf p.1 + p.2) := Primrec.nat_add.comp hmw' hidx
  have hfirst : Primrec fun p : ℕ × ℕ =>
      (if uni then iAll (tf p.1 + 2 * (jf p.1 + p.2)) else iEx (tf p.1 + 2 * (jf p.1 + p.2))) := by
    cases uni
    · simpa [iEx] using Primrec.pair (Primrec.const 4)
        (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const 0) hT0))
    · simpa [iAll] using Primrec.pair (Primrec.const 5)
        (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const 0) hT0))
  have hnand1 : Primrec fun p : ℕ × ℕ =>
      iNand (tf p.1 + 2 * (jf p.1 + p.2)) (mwf p.1 + (jf p.1 + p.2))
        (tf p.1 + 2 * (jf p.1 + p.2) + 1) :=
    Primrec.pair (Primrec.const 1) (Primrec.pair hT0 (Primrec.pair hMW hT1))
  have hnand2 : Primrec fun p : ℕ × ℕ =>
      iNand (tf p.1 + 2 * (jf p.1 + p.2) + 1) (tf p.1 + 2 * (jf p.1 + p.2) + 1)
        (gf p.1 + 2 * (jf p.1 + p.2) + 1) :=
    Primrec.pair (Primrec.const 1) (Primrec.pair hT1 (Primrec.pair hT1 hG1))
  have hcopy : Primrec fun p : ℕ × ℕ =>
      iCopy (mwf p.1 + (jf p.1 + p.2)) (gf p.1 + 2 * (jf p.1 + p.2)) :=
    Primrec.pair (Primrec.const 10) (Primrec.pair hMW (Primrec.pair (Primrec.const 0) hG0))
  exact Primrec.list_cons.comp hfirst
    (Primrec.list_cons.comp hnand1
      (Primrec.list_cons.comp hnand2 (Primrec.list_cons.comp hcopy (Primrec.const []))))

namespace Sim

/-! ### The family of layouts of a machine -/

variable (M : ASpace) (FW : CircFam M.widthF 1) (FI : CircFam M.initF 1)
  (FA : CircFam (fun args => [M.accB args]) 2) (FU : CircFam (fun args => [M.univB args]) 2)
  (FS : CircFam (fun args => [M.stepB args]) 3)

/-- The data the program for the inputs of length `n` is built from. -/
def simAt (n : ℕ) : Sim := ⟨M, n, FW, FI, FA, FU, FS⟩

@[simp] theorem simAt_n (n : ℕ) : (simAt M FW FI FA FU FS n).n = n := rfl

/-- The number of cells a configuration is held in, as a polynomial. -/
noncomputable def NNp : Polynomial ℕ := Polynomial.X + FW.B + FI.B

theorem NNp_eval (n : ℕ) : (NNp M FW FI).eval n = (simAt M FW FI FA FU FS n).NN := by
  simp [NNp, NN, BW, BI, simAt]

/-! ### The layout is produced by an algorithm -/

theorem primrec_max {f g : ℕ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun n => max (f n) (g n) :=
  (Primrec.ite (PrimrecRel.comp Primrec.nat_le hf hg) hg hf).of_eq fun _ => (max_def _ _).symm

section Prim

variable {M FW FI FA FU FS}

theorem primrec_NN : Primrec fun n => (simAt M FW FI FA FU FS n).NN :=
  (primrec_poly_eval (NNp M FW FI)).of_eq (NNp_eval M FW FI FA FU FS)

theorem primrec_CW : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CW := FW.primC

theorem primrec_CI : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CI := FI.primC

theorem primrec_CA : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CA :=
  FA.primC.comp primrec_NN

theorem primrec_CU : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CU :=
  FU.primC.comp primrec_NN

theorem primrec_CS : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CS :=
  FS.primC.comp primrec_NN

theorem primrec_gW : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CW.gates.length :=
  Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp primrec_CW))

theorem primrec_gI : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CI.gates.length :=
  Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp primrec_CI))

theorem primrec_gA : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CA.gates.length :=
  Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp primrec_CA))

theorem primrec_gU : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CU.gates.length :=
  Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp primrec_CU))

theorem primrec_gS : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CS.gates.length :=
  Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp primrec_CS))

theorem primrec_outW : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CW.out :=
  Primrec.snd.comp (Primrec.snd.comp primrec_CW)

theorem primrec_outI : Primrec fun n => (simAt M FW FI FA FU FS n).lay.CI.out :=
  Primrec.snd.comp (Primrec.snd.comp primrec_CI)

theorem primrec_aC : Primrec fun n => (simAt M FW FI FA FU FS n).lay.aC :=
  (Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.const 2) primrec_NN)).of_eq fun _ => (Sim.aC_eq _).symm

theorem primrec_aX : Primrec fun n => (simAt M FW FI FA FU FS n).lay.aX :=
  (Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.const 4) primrec_NN)).of_eq fun _ => (Sim.aX_eq _).symm

theorem primrec_aS : Primrec fun n => (simAt M FW FI FA FU FS n).lay.aS :=
  (Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.const 6) primrec_NN)).of_eq fun _ => (Sim.aS_eq _).symm

theorem primrec_gmax : Primrec fun n => (simAt M FW FI FA FU FS n).lay.gmax :=
  (primrec_max primrec_gA (primrec_max primrec_gU primrec_gS)).of_eq fun _ => rfl

theorem primrec_aMW : Primrec fun n => (simAt M FW FI FA FU FS n).lay.aMW :=
  (Primrec.nat_add.comp primrec_aS primrec_gmax).of_eq fun _ => rfl

theorem primrec_aT : Primrec fun n => (simAt M FW FI FA FU FS n).lay.aT :=
  (Primrec.nat_add.comp primrec_aMW primrec_NN).of_eq fun _ => rfl

theorem primrec_aXW : Primrec fun n => (simAt M FW FI FA FU FS n).lay.aXW :=
  (Primrec.nat_add.comp primrec_aT
    (Primrec.nat_mul.comp (Primrec.const 2) primrec_NN)).of_eq fun _ => rfl

theorem primrec_aXI : Primrec fun n => (simAt M FW FI FA FU FS n).lay.aXI :=
  (Primrec.nat_add.comp
    (Primrec.nat_add.comp primrec_aXW (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    primrec_gW).of_eq fun _ => rfl

theorem primrec_mm : Primrec fun n => (simAt M FW FI FA FU FS n).lay.mm :=
  (Primrec.nat_add.comp
    (Primrec.nat_add.comp primrec_aXI (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    primrec_gI).of_eq fun _ => rfl

theorem primrec_accBit : Primrec fun n => (simAt M FW FI FA FU FS n).lay.accBit :=
  (Primrec.nat_add.comp primrec_aC
    (Primrec.list_getI.comp (Primrec.snd.comp (Primrec.snd.comp primrec_CA))
      (Primrec.const 1))).of_eq fun _ => rfl

theorem primrec_univBit : Primrec fun n => (simAt M FW FI FA FU FS n).lay.univBit :=
  (Primrec.nat_add.comp primrec_aC
    (Primrec.list_getI.comp (Primrec.snd.comp (Primrec.snd.comp primrec_CU))
      (Primrec.const 1))).of_eq fun _ => rfl

theorem primrec_stepBit : Primrec fun n => (simAt M FW FI FA FU FS n).lay.stepBit :=
  (Primrec.nat_add.comp (Primrec.const Lay.aG)
    (Primrec.list_getI.comp (Primrec.snd.comp (Primrec.snd.comp primrec_CS))
      (Primrec.const 1))).of_eq fun _ => rfl

theorem primrec_lL : Primrec fun n => (simAt M FW FI FA FU FS n).lay.lL := by
  have h : Primrec fun n : ℕ => 1 + 2 * n + (simAt M FW FI FA FU FS n).lay.CW.gates.length +
      (simAt M FW FI FA FU FS n).NN + 2 * n +
      (simAt M FW FI FA FU FS n).lay.CI.gates.length + 2 * (simAt M FW FI FA FU FS n).NN +
      2 * (simAt M FW FI FA FU FS n).NN := by
    have h2n : Primrec fun n : ℕ => 2 * n := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
    have h2N : Primrec fun n : ℕ => 2 * (simAt M FW FI FA FU FS n).NN :=
      Primrec.nat_mul.comp (Primrec.const 2) primrec_NN
    exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.const 1) h2n) primrec_gW) primrec_NN) h2n)
        primrec_gI) h2N) h2N
  exact h.of_eq fun _ => rfl

theorem primrec_lUNI : Primrec fun n => (simAt M FW FI FA FU FS n).lay.lUNI := by
  have h4N : Primrec fun n : ℕ => 4 * (simAt M FW FI FA FU FS n).NN :=
    Primrec.nat_mul.comp (Primrec.const 4) primrec_NN
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp primrec_lL primrec_gA) (Primrec.const 1)) primrec_gU)
      (Primrec.const 1)) h4N) primrec_gS) (Primrec.const 2)).of_eq fun _ => rfl

theorem primrec_lCONT : Primrec fun n => (simAt M FW FI FA FU FS n).lay.lCONT := by
  have h4N : Primrec fun n : ℕ => 4 * (simAt M FW FI FA FU FS n).NN :=
    Primrec.nat_mul.comp (Primrec.const 4) primrec_NN
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    primrec_lUNI h4N) primrec_gS) (Primrec.const 2)).of_eq fun _ => rfl

theorem primrec_lACC : Primrec fun n => (simAt M FW FI FA FU FS n).lay.lACC := by
  have h2N : Primrec fun n : ℕ => 2 * (simAt M FW FI FA FU FS n).NN :=
    Primrec.nat_mul.comp (Primrec.const 2) primrec_NN
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp primrec_lCONT h2N)
    (Primrec.const 1)).of_eq fun _ => rfl

theorem primrec_maskSrc :
    Primrec fun p : ℕ × ℕ => (simAt M FW FI FA FU FS p.1).lay.maskSrc p.2 := by
  have hBW : Primrec fun p : ℕ × ℕ => (simAt M FW FI FA FU FS p.1).lay.BW :=
    (primrec_poly_eval FW.B).comp Primrec.fst
  have hXW : Primrec fun p : ℕ × ℕ => (simAt M FW FI FA FU FS p.1).lay.aXW :=
    primrec_aXW.comp Primrec.fst
  have hout : Primrec fun p : ℕ × ℕ => (simAt M FW FI FA FU FS p.1).lay.CW.out :=
    primrec_outW.comp Primrec.fst
  have hidx : Primrec fun p : ℕ × ℕ => 2 * p.2 :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd
  exact (Primrec.ite (PrimrecRel.comp Primrec.nat_lt Primrec.snd hBW)
    (Primrec.nat_add.comp hXW (Primrec.list_getI.comp hout hidx))
    (Primrec.const 0)).of_eq fun _ => rfl

theorem primrec_initSrc :
    Primrec fun p : ℕ × ℕ => (simAt M FW FI FA FU FS p.1).lay.initSrc p.2 := by
  have hBI : Primrec fun p : ℕ × ℕ => 2 * (simAt M FW FI FA FU FS p.1).lay.BI :=
    Primrec.nat_mul.comp (Primrec.const 2) ((primrec_poly_eval FI.B).comp Primrec.fst)
  have hXI : Primrec fun p : ℕ × ℕ => (simAt M FW FI FA FU FS p.1).lay.aXI :=
    primrec_aXI.comp Primrec.fst
  have hout : Primrec fun p : ℕ × ℕ => (simAt M FW FI FA FU FS p.1).lay.CI.out :=
    primrec_outI.comp Primrec.fst
  exact (Primrec.ite (PrimrecRel.comp Primrec.nat_lt Primrec.snd hBI)
    (Primrec.nat_add.comp hXI (Primrec.list_getI.comp hout Primrec.snd))
    (Primrec.const 0)).of_eq fun _ => rfl

/-- **The compiled program is produced by an algorithm.** -/
theorem primrec_prog : Primrec fun n => (simAt M FW FI FA FU FS n).lay.prog := by
  have h2n : Primrec fun n : ℕ => 2 * n := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
  have h2N : Primrec fun n : ℕ => 2 * (simAt M FW FI FA FU FS n).NN :=
    Primrec.nat_mul.comp (Primrec.const 2) primrec_NN
  have h4N : Primrec fun n : ℕ => 4 * (simAt M FW FI FA FU FS n).NN :=
    Primrec.nat_mul.comp (Primrec.const 4) primrec_NN
  have h6N : Primrec fun n : ℕ => 6 * (simAt M FW FI FA FU FS n).NN :=
    Primrec.nat_mul.comp (Primrec.const 6) primrec_NN
  have hgates : ∀ {Cf : ℕ → Circ}, Primrec Cf → Primrec fun n => (Cf n).gates :=
    fun hC => Primrec.fst.comp (Primrec.snd.comp hC)
  -- the twenty-one blocks
  have b0 : Primrec fun _ : ℕ => ([iSet1 1] : List Instr) := Primrec.const _
  have b1 : Primrec fun n => encInpProg (simAt M FW FI FA FU FS n).lay.aXW n n :=
    primrec_encInpProg primrec_aXW Primrec.id Primrec.id
  have b2 : Primrec fun n => circProg (simAt M FW FI FA FU FS n).lay.aXW 0 (2 * n)
      (simAt M FW FI FA FU FS n).lay.CW.gates :=
    primrec_circProg primrec_aXW (Primrec.const 0) h2n (hgates primrec_CW)
  have b3 : Primrec fun n => gatherProg (simAt M FW FI FA FU FS n).lay.aMW
      (simAt M FW FI FA FU FS n).lay.maskSrc (simAt M FW FI FA FU FS n).NN :=
    primrec_gatherProg primrec_aMW primrec_maskSrc primrec_NN
  have b4 : Primrec fun n => encInpProg (simAt M FW FI FA FU FS n).lay.aXI n n :=
    primrec_encInpProg primrec_aXI Primrec.id Primrec.id
  have b5 : Primrec fun n => circProg (simAt M FW FI FA FU FS n).lay.aXI 0 (2 * n)
      (simAt M FW FI FA FU FS n).lay.CI.gates :=
    primrec_circProg primrec_aXI (Primrec.const 0) h2n (hgates primrec_CI)
  have b6 : Primrec fun n => gatherProg (simAt M FW FI FA FU FS n).lay.aC
      (simAt M FW FI FA FU FS n).lay.initSrc (2 * (simAt M FW FI FA FU FS n).NN) :=
    primrec_gatherProg primrec_aC primrec_initSrc h2N
  have b7 : Primrec fun n => encInpProg (simAt M FW FI FA FU FS n).lay.aX
      (simAt M FW FI FA FU FS n).NN n :=
    primrec_encInpProg primrec_aX primrec_NN Primrec.id
  have b8 : Primrec fun n => circProg (simAt M FW FI FA FU FS n).lay.aC 0
      (4 * (simAt M FW FI FA FU FS n).NN) (simAt M FW FI FA FU FS n).lay.CA.gates :=
    primrec_circProg primrec_aC (Primrec.const 0) h4N (hgates primrec_CA)
  have b9 : Primrec fun n => ([iBrIf (simAt M FW FI FA FU FS n).lay.accBit
      (simAt M FW FI FA FU FS n).lay.lACC] : List Instr) :=
    Primrec.list_cons.comp (Primrec.pair (Primrec.const 3)
      (Primrec.pair primrec_accBit (Primrec.pair primrec_lACC (Primrec.const 0))))
      (Primrec.const [])
  have b10 : Primrec fun n => circProg (simAt M FW FI FA FU FS n).lay.aC 0
      (4 * (simAt M FW FI FA FU FS n).NN) (simAt M FW FI FA FU FS n).lay.CU.gates :=
    primrec_circProg primrec_aC (Primrec.const 0) h4N (hgates primrec_CU)
  have b11 : Primrec fun n => ([iBrIf (simAt M FW FI FA FU FS n).lay.univBit
      (simAt M FW FI FA FU FS n).lay.lUNI] : List Instr) :=
    Primrec.list_cons.comp (Primrec.pair (Primrec.const 3)
      (Primrec.pair primrec_univBit (Primrec.pair primrec_lUNI (Primrec.const 0))))
      (Primrec.const [])
  have b12 : Primrec fun n => guessProg false Lay.aG (simAt M FW FI FA FU FS n).lay.aMW
      (simAt M FW FI FA FU FS n).lay.aT 0 (simAt M FW FI FA FU FS n).NN :=
    primrec_guessProg false (Primrec.const _) primrec_aMW primrec_aT (Primrec.const 0) primrec_NN
  have b13 : Primrec fun n => circProg Lay.aG 0 (6 * (simAt M FW FI FA FU FS n).NN)
      (simAt M FW FI FA FU FS n).lay.CS.gates :=
    primrec_circProg (Primrec.const _) (Primrec.const 0) h6N (hgates primrec_CS)
  have b14 : Primrec fun n => ([iBrIf (simAt M FW FI FA FU FS n).lay.stepBit
      (simAt M FW FI FA FU FS n).lay.lCONT, iRej] : List Instr) :=
    Primrec.list_cons.comp (Primrec.pair (Primrec.const 3)
      (Primrec.pair primrec_stepBit (Primrec.pair primrec_lCONT (Primrec.const 0))))
      (Primrec.const [iRej])
  have b15 : Primrec fun n => guessProg true Lay.aG (simAt M FW FI FA FU FS n).lay.aMW
      (simAt M FW FI FA FU FS n).lay.aT 0 (simAt M FW FI FA FU FS n).NN :=
    primrec_guessProg true (Primrec.const _) primrec_aMW primrec_aT (Primrec.const 0) primrec_NN
  have b17 : Primrec fun n => ([iBrIf (simAt M FW FI FA FU FS n).lay.stepBit
      (simAt M FW FI FA FU FS n).lay.lCONT, iAcc] : List Instr) :=
    Primrec.list_cons.comp (Primrec.pair (Primrec.const 3)
      (Primrec.pair primrec_stepBit (Primrec.pair primrec_lCONT (Primrec.const 0))))
      (Primrec.const [iAcc])
  have b18 : Primrec fun n => gatherProg (simAt M FW FI FA FU FS n).lay.aC
      (fun i => Lay.aG + i) (2 * (simAt M FW FI FA FU FS n).NN) :=
    primrec_gatherProg primrec_aC
      (Primrec.nat_add.comp (Primrec.const Lay.aG) Primrec.snd) h2N
  have b19 : Primrec fun n => ([iJmp (simAt M FW FI FA FU FS n).lay.lL] : List Instr) :=
    Primrec.list_cons.comp (Primrec.pair (Primrec.const 7)
      (Primrec.pair (Primrec.const 0) (Primrec.pair primrec_lL (Primrec.const 0))))
      (Primrec.const [])
  have b20 : Primrec fun _ : ℕ => ([iAcc] : List Instr) := Primrec.const _
  have happ : ∀ {f g : ℕ → List Instr}, Primrec f → Primrec g → Primrec fun n => f n ++ g n :=
    fun hf hg => Primrec.list_append.comp hf hg
  have hall := happ b0 (happ b1 (happ b2 (happ b3 (happ b4 (happ b5 (happ b6 (happ b7
    (happ b8 (happ b9 (happ b10 (happ b11 (happ b12 (happ b13 (happ b14 (happ b15
      (happ b13 (happ b17 (happ b18 (happ b19 b20)))))))))))))))))))
  refine hall.of_eq fun n => ?_
  rw [Lay.prog, Lay.blocks]
  simp [List.flatten]

end Prim

/-! ### The compiled program is of polynomial size -/

section Size

/-- A polynomial bounding the program and the memory of the layout. -/
noncomputable def sizeP : Polynomial ℕ :=
  Polynomial.C 100 * (Polynomial.X + FW.bnd + FI.bnd + FA.bnd.comp (NNp M FW FI)
    + FU.bnd.comp (NNp M FW FI) + FS.bnd.comp (NNp M FW FI) + NNp M FW FI + 1)

variable {M FW FI FA FU FS}

theorem sizeP_eval (n : ℕ) :
    (sizeP M FW FI FA FU FS).eval n
      = 100 * (n + FW.bnd.eval n + FI.bnd.eval n
          + FA.bnd.eval (simAt M FW FI FA FU FS n).NN
          + FU.bnd.eval (simAt M FW FI FA FU FS n).NN
          + FS.bnd.eval (simAt M FW FI FA FU FS n).NN
          + (simAt M FW FI FA FU FS n).NN + 1) := by
  simp [sizeP, Polynomial.eval_comp, NNp_eval M FW FI FA FU FS n]

/-- The gates of a circuit of a family are within its size bound. -/
theorem gates_le {f : Fn} {k : ℕ} (F : CircFam f k) (N : ℕ) :
    (F.C N).gates.length ≤ F.bnd.eval N := by
  have := F.size_le N
  rw [Circ.size] at this
  omega

/-- **The program and the memory of the layout are of polynomial size.** -/
theorem size_le (n : ℕ) :
    (simAt M FW FI FA FU FS n).lay.prog.length + (simAt M FW FI FA FU FS n).lay.mm + 1
      ≤ (sizeP M FW FI FA FU FS).eval n := by
  set S := simAt M FW FI FA FU FS n with hS
  obtain ⟨hG, hC, hX, hSa, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have hlen : S.lay.prog.length = S.lay.lACC + 1 := S.lay.length_prog
  have e1 : S.lay.lACC = S.lay.lCONT + 2 * S.NN + 1 := rfl
  have e2 : S.lay.lCONT = S.lay.lUNI + 4 * S.NN + S.lay.CS.gates.length + 2 := rfl
  have e3 : S.lay.lUNI = S.lay.lL + S.lay.CA.gates.length + 1 + S.lay.CU.gates.length + 1
      + 4 * S.NN + S.lay.CS.gates.length + 2 := rfl
  have e4 : S.lay.lL = 1 + 2 * n + S.lay.CW.gates.length + S.NN + 2 * n
      + S.lay.CI.gates.length + 2 * S.NN + 2 * S.NN := rfl
  have hgmax : S.lay.gmax ≤ S.lay.CA.gates.length + S.lay.CU.gates.length
      + S.lay.CS.gates.length := by
    rw [Lay.gmax]
    rcases le_total S.lay.CU.gates.length S.lay.CS.gates.length with h | h <;>
      rcases le_total S.lay.CA.gates.length (max S.lay.CU.gates.length S.lay.CS.gates.length)
        with h' | h' <;>
      simp only [max_def] <;> split_ifs <;> omega
  have hW : S.lay.CW.gates.length ≤ FW.bnd.eval n := gates_le FW n
  have hI : S.lay.CI.gates.length ≤ FI.bnd.eval n := gates_le FI n
  have hA : S.lay.CA.gates.length ≤ FA.bnd.eval S.NN := gates_le FA S.NN
  have hU : S.lay.CU.gates.length ≤ FU.bnd.eval S.NN := gates_le FU S.NN
  have hSg : S.lay.CS.gates.length ≤ FS.bnd.eval S.NN := gates_le FS S.NN
  have hn : S.n = n := rfl
  rw [sizeP_eval, ← hS]
  omega

end Size

end Sim

end Compile

end HTN
