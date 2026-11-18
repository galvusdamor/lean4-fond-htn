import HtnComplexity.Compile.Mem
/-!
# One round of the loop

The loop of the compiled program runs, from its head `lL`, the acceptance circuit, the
classification circuit, a guess of a successor configuration, the transition circuit, and the
copy of the guess into the configuration; then it jumps back to `lL`.  This file says what
acceptance at `lL` is, in terms of acceptance at `lL` after one round:

* `HTN.Compile.Sim.round_acc`, `HTN.Compile.Sim.round_ex`, `HTN.Compile.Sim.round_all` — the
  three ways in which the program accepts at the head of the loop;
* `HTN.Compile.Sim.round_elim` — the converse, with the fuel of
  `HtnComplexity/Compile/Fuel.lean`, which is what an induction on a computation of the
  program needs.

The memories the round passes through are named `mA`, `mU`, `mG`, `mS`, `mC`; what they carry is
the subject of `HtnComplexity/Compile/Mem.lean`.
-/

namespace HTN

namespace Compile

namespace Sim

open Syn PSpace PTime

variable {S : Sim} {x c : List Bool}

/-! ### The memories of a round -/

/-- The memory after the acceptance circuit. -/
def mA (S : Sim) (x : List Bool) (μ : ℕ → Bool) : ℕ → Bool :=
  runInstrs x μ (circProg S.lay.aC 0 (4 * S.NN) S.lay.CA.gates)

/-- The memory after the classification circuit. -/
def mU (S : Sim) (x : List Bool) (μ : ℕ → Bool) : ℕ → Bool :=
  runInstrs x (mA S x μ) (circProg S.lay.aC 0 (4 * S.NN) S.lay.CU.gates)

/-- The memory after the guess. -/
def mG (S : Sim) (x : List Bool) (μ : ℕ → Bool) (bs : List Bool) : ℕ → Bool :=
  guessMem Lay.aG S.lay.aMW S.lay.aT 0 (mU S x μ) bs

/-- The memory after the transition circuit. -/
def mS (S : Sim) (x : List Bool) (μ : ℕ → Bool) (bs : List Bool) : ℕ → Bool :=
  runInstrs x (mG S x μ bs) (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates)

/-- The memory after the copy of the guess into the configuration. -/
def mC (S : Sim) (x : List Bool) (μ : ℕ → Bool) (bs : List Bool) : ℕ → Bool :=
  runInstrs x (mS S x μ bs) (gatherProg S.lay.aC (fun i => Lay.aG + i) (2 * S.NN))

section Mems

variable {μ : ℕ → Bool} {bs : List Bool}

theorem mA_def : mA S x μ = runInstrs x μ (circProg S.lay.aC 0 (4 * S.NN) S.lay.CA.gates) := rfl

theorem mU_def :
    mU S x μ = runInstrs x (mA S x μ) (circProg S.lay.aC 0 (4 * S.NN) S.lay.CU.gates) := rfl

theorem mS_def :
    mS S x μ bs = runInstrs x (mG S x μ bs) (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates) := rfl

theorem mC_def : mC S x μ bs
    = runInstrs x (mS S x μ bs) (gatherProg S.lay.aC (fun i => Lay.aG + i) (2 * S.NN)) := rfl

theorem memOk_mA (h : S.MemOk x c μ) : S.MemOk x c (mA S x μ) :=
  memOk_circ aC_add S.gA_le h

theorem memOk_mU (h : S.MemOk x c μ) : S.MemOk x c (mU S x μ) :=
  memOk_circ aC_add S.gU_le (memOk_mA h)

theorem memOk_mG (hbs : bs.length = S.NN) (h : S.MemOk x c μ) : S.MemOk x c (mG S x μ bs) :=
  memOk_guess hbs (memOk_mU h)

theorem memOk_mS (hbs : bs.length = S.NN) (h : S.MemOk x c μ) : S.MemOk x c (mS S x μ bs) :=
  memOk_circ aG_add S.gS_le (memOk_mG hbs h)

/-- The guessed configuration, in the memory after the guess. -/
theorem cfg_mG (hbs : bs.length = S.NN) (hw : S.M.w x ≤ S.NN) (h : S.MemOk x c μ) :
    ∀ r < 2 * S.NN, mG S x μ bs (Lay.aG + r) = (encStr S.NN (S.gcfg x bs)).getI r :=
  guess_cfg hbs hw (memOk_mU h)

/-- The guessed configuration, in the memory after the transition circuit. -/
theorem cfg_mS (hbs : bs.length = S.NN) (hw : S.M.w x ≤ S.NN) (h : S.MemOk x c μ) :
    ∀ r < 2 * S.NN, mS S x μ bs (Lay.aG + r) = (encStr S.NN (S.gcfg x bs)).getI r :=
  aG_circ aG_add S.gS_le (cfg_mG hbs hw h)

/-- **After a round the invariant holds of the guessed configuration.** -/
theorem memOk_mC (hbs : bs.length = S.NN) (hw : S.M.w x ≤ S.NN) (h : S.MemOk x c μ) :
    S.MemOk x (S.gcfg x bs) (mC S x μ bs) :=
  memOk_gather (memOk_mS hbs h) (cfg_mS hbs hw h)

/-- The acceptance bit, in the memory after the acceptance circuit. -/
theorem bit_mA (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (h : S.MemOk x c μ) :
    mA S x μ S.lay.accBit = S.M.accB [c, x] := read_accBit hx hc h

/-- The classification bit, in the memory after the classification circuit. -/
theorem bit_mU (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (h : S.MemOk x c μ) :
    mU S x μ S.lay.univBit = S.M.univB [c, x] := read_univBit hx hc (memOk_mA h)

/-- The transition bit, in the memory after the transition circuit. -/
theorem bit_mS (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (hbs : bs.length = S.NN)
    (hw : S.M.w x ≤ S.NN) (h : S.MemOk x c μ) :
    mS S x μ bs S.lay.stepBit = S.M.stepB [S.gcfg x bs, c, x] :=
  read_stepBit hx hc (by rw [length_gcfg hbs hw]; exact hw) (memOk_mG hbs h) (cfg_mG hbs hw h)

end Mems

/-! ### Where the blocks sit, in the form the block lemmas ask for -/

theorem at_circA' : ∀ t < (circProg S.lay.aC 0 (4 * S.NN) S.lay.CA.gates).length,
    S.lay.prog.getI (S.lay.lL + t) = (circProg S.lay.aC 0 (4 * S.NN) S.lay.CA.gates).getI t :=
  fun t ht => S.lay.at_circA t (by simpa using ht)

theorem at_circU' : ∀ t < (circProg S.lay.aC 0 (4 * S.NN) S.lay.CU.gates).length,
    S.lay.prog.getI (S.lay.oCircU + t) = (circProg S.lay.aC 0 (4 * S.NN) S.lay.CU.gates).getI t :=
  fun t ht => S.lay.at_circU t (by simpa using ht)

theorem at_circSE' : ∀ t < (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates).length,
    S.lay.prog.getI (S.lay.oCircSE + t) = (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates).getI t :=
  fun t ht => S.lay.at_circSE t (by simpa using ht)

theorem at_circSA' : ∀ t < (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates).length,
    S.lay.prog.getI (S.lay.oCircSA + t) = (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates).getI t :=
  fun t ht => S.lay.at_circSA t (by simpa using ht)

theorem at_copy' : ∀ t < (gatherProg S.lay.aC (fun i => Lay.aG + i) (2 * S.NN)).length,
    S.lay.prog.getI (S.lay.lCONT + t)
      = (gatherProg S.lay.aC (fun i => Lay.aG + i) (2 * S.NN)).getI t :=
  fun t ht => S.lay.at_copyGC t (by simpa using ht)

theorem instr_brA : S.lay.prog.getI S.lay.oBrA = iBrIf S.lay.accBit S.lay.lACC := by
  have h := S.lay.at_brA 0 (by simp)
  simpa using h

theorem instr_brU : S.lay.prog.getI S.lay.oBrU = iBrIf S.lay.univBit S.lay.lUNI := by
  have h := S.lay.at_brU 0 (by simp)
  simpa using h

theorem instr_brSE : S.lay.prog.getI S.lay.oBrSE = iBrIf S.lay.stepBit S.lay.lCONT := by
  have h := S.lay.at_brSE 0 (by simp)
  simpa using h

theorem instr_rej : S.lay.prog.getI (S.lay.oBrSE + 1) = iRej := by
  have h := S.lay.at_brSE 1 (by simp)
  simpa using h

theorem instr_brSA : S.lay.prog.getI S.lay.oBrSA = iBrIf S.lay.stepBit S.lay.lCONT := by
  have h := S.lay.at_brSA 0 (by simp)
  simpa using h

theorem instr_accSA : S.lay.prog.getI (S.lay.oBrSA + 1) = iAcc := by
  have h := S.lay.at_brSA 1 (by simp)
  simpa using h

theorem instr_jmp : S.lay.prog.getI S.lay.oJmp = iJmp S.lay.lL := by
  have h := S.lay.at_jmp 0 (by simp)
  simpa using h

theorem instr_acc : S.lay.prog.getI S.lay.lACC = iAcc := by
  have h := S.lay.at_acc 0 (by simp)
  simpa using h

theorem at_guessE' : ∀ t < 4 * S.NN,
    S.lay.prog.getI (S.lay.oGuessE + t)
      = (guessProg false Lay.aG S.lay.aMW S.lay.aT 0 S.NN).getI t :=
  fun t ht => S.lay.at_guessEx t ht

theorem at_guessA' : ∀ t < 4 * S.NN,
    S.lay.prog.getI (S.lay.lUNI + t)
      = (guessProg true Lay.aG S.lay.aMW S.lay.aT 0 S.NN).getI t :=
  fun t ht => S.lay.at_guessAll t ht

/-! ### The program points of a round -/

theorem pt_brA : S.lay.lL + (circProg S.lay.aC 0 (4 * S.NN) S.lay.CA.gates).length
    = S.lay.oBrA := by rw [length_circProg]; rfl

theorem pt_brU : S.lay.oCircU + (circProg S.lay.aC 0 (4 * S.NN) S.lay.CU.gates).length
    = S.lay.oBrU := by rw [length_circProg]; rfl

theorem pt_circU : S.lay.oBrA + 1 = S.lay.oCircU := rfl

theorem pt_guessE : S.lay.oBrU + 1 = S.lay.oGuessE := rfl

theorem pt_circSE : S.lay.oGuessE + 4 * S.NN = S.lay.oCircSE := rfl

theorem pt_brSE : S.lay.oCircSE + (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates).length
    = S.lay.oBrSE := by rw [length_circProg]; rfl

theorem pt_circSA : S.lay.lUNI + 4 * S.NN = S.lay.oCircSA := rfl

theorem pt_brSA : S.lay.oCircSA + (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates).length
    = S.lay.oBrSA := by rw [length_circProg]; rfl

theorem pt_jmp : S.lay.lCONT + (gatherProg S.lay.aC (fun i => Lay.aG + i) (2 * S.NN)).length
    = S.lay.oJmp := by rw [length_gatherProg]; rfl

/-! ### From the head of the loop to the guess -/

section Head

variable {μ : ℕ → Bool}

/-- The acceptance circuit, as a step of the program. -/
theorem acc_circA_iff :
    Acc S.lay.prog x S.lay.lL μ ↔ Acc S.lay.prog x S.lay.oBrA (mA S x μ) := by
  have h := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.lL) (μ := μ)
    at_circA' simple_circProg
  rwa [pt_brA] at h

/-- The classification circuit, as a step of the program. -/
theorem acc_circU_iff :
    Acc S.lay.prog x S.lay.oCircU (mA S x μ) ↔ Acc S.lay.prog x S.lay.oBrU (mU S x μ) := by
  have h := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oCircU) (μ := mA S x μ)
    at_circU' simple_circProg
  rwa [pt_brU] at h

/-- **From the head of the loop to the guess**, when the configuration is not accepting. -/
theorem head_iff (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (h : S.MemOk x c μ)
    (hnacc : S.M.accB [c, x] = false) :
    Acc S.lay.prog x S.lay.lL μ ↔
      Acc S.lay.prog x (if S.M.univB [c, x] = true then S.lay.lUNI else S.lay.oGuessE)
        (mU S x μ) := by
  rw [acc_circA_iff,
    acc_brIf_false_iff instr_brA ((bit_mA hx hc h).trans hnacc),
    pt_circU, acc_circU_iff]
  by_cases hu : S.M.univB [c, x] = true
  · rw [if_pos hu, acc_brIf_true_iff instr_brU ((bit_mU hx hc h).trans hu)]
  · rw [if_neg hu,
      acc_brIf_false_iff instr_brU ((bit_mU hx hc h).trans (by simpa using hu)), pt_guessE]

/-- **The program accepts at the head of the loop when the configuration is accepting.** -/
theorem round_acc (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (h : S.MemOk x c μ)
    (hacc : S.M.accB [c, x] = true) : Acc S.lay.prog x S.lay.lL μ := by
  rw [acc_circA_iff, acc_brIf_true_iff instr_brA ((bit_mA hx hc h).trans hacc)]
  exact Acc.acc instr_acc

end Head

/-! ### From the guess back to the head of the loop -/

section Tail

variable {μ : ℕ → Bool} {bs : List Bool}

/-- The transition circuit and the copy, as steps of the program, in the existential copy. -/
theorem tail_ex_iff (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (hw : S.M.w x ≤ S.NN)
    (hbs : bs.length = S.NN) (h : S.MemOk x c μ) :
    Acc S.lay.prog x S.lay.oCircSE (mG S x μ bs) ↔
      (S.M.stepB [S.gcfg x bs, c, x] = true ∧ Acc S.lay.prog x S.lay.lL (mC S x μ bs)) := by
  have hcirc := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oCircSE)
    (μ := mG S x μ bs) at_circSE' simple_circProg
  rw [pt_brSE] at hcirc
  rw [hcirc, ← mS_def]
  by_cases hst : S.M.stepB [S.gcfg x bs, c, x] = true
  · have hbit : mS S x μ bs S.lay.stepBit = true := by rw [bit_mS hx hc hbs hw h]; exact hst
    rw [acc_brIf_true_iff instr_brSE hbit]
    have hg := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.lCONT)
      (μ := mS S x μ bs) at_copy' simple_gatherProg
    rw [pt_jmp] at hg
    rw [hg, acc_jmp_iff instr_jmp]
    simp [hst, mC]
  · have hbit : mS S x μ bs S.lay.stepBit = false := by
      rw [bit_mS hx hc hbs hw h]; simpa using hst
    rw [acc_brIf_false_iff instr_brSE hbit]
    have hst' : S.M.stepB [S.gcfg x bs, c, x] = false := by simpa using hst
    simp only [hst', Bool.false_eq_true, false_and, iff_false]
    exact not_acc_rej instr_rej

/-- The transition circuit and the copy, as steps of the program, in the universal copy. -/
theorem tail_all_iff (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (hw : S.M.w x ≤ S.NN)
    (hbs : bs.length = S.NN) (h : S.MemOk x c μ) :
    Acc S.lay.prog x S.lay.oCircSA (mG S x μ bs) ↔
      (S.M.stepB [S.gcfg x bs, c, x] = true → Acc S.lay.prog x S.lay.lL (mC S x μ bs)) := by
  have hcirc := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oCircSA)
    (μ := mG S x μ bs) at_circSA' simple_circProg
  rw [pt_brSA] at hcirc
  rw [hcirc, ← mS_def]
  by_cases hst : S.M.stepB [S.gcfg x bs, c, x] = true
  · have hbit : mS S x μ bs S.lay.stepBit = true := by rw [bit_mS hx hc hbs hw h]; exact hst
    rw [acc_brIf_true_iff instr_brSA hbit]
    have hg := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.lCONT)
      (μ := mS S x μ bs) at_copy' simple_gatherProg
    rw [pt_jmp] at hg
    rw [hg, acc_jmp_iff instr_jmp]
    simp [hst, mC]
  · have hbit : mS S x μ bs S.lay.stepBit = false := by
      rw [bit_mS hx hc hbs hw h]; simpa using hst
    rw [acc_brIf_false_iff instr_brSA hbit]
    have hst' : S.M.stepB [S.gcfg x bs, c, x] = false := by simpa using hst
    simp only [hst', Bool.false_eq_true, false_implies, iff_true]
    exact Acc.acc instr_accSA

end Tail

/-! ### The three ways of accepting at the head of the loop -/

section Intro

variable {μ : ℕ → Bool} {bs : List Bool}

/-- **The existential case.** -/
theorem round_ex (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (hw : S.M.w x ≤ S.NN)
    (h : S.MemOk x c μ) (hnacc : S.M.accB [c, x] = false) (hu : S.M.univB [c, x] = false)
    (hbs : bs.length = S.NN) (hst : S.M.stepB [S.gcfg x bs, c, x] = true)
    (hnext : Acc S.lay.prog x S.lay.lL (mC S x μ bs)) : Acc S.lay.prog x S.lay.lL μ := by
  rw [head_iff hx hc h hnacc, if_neg (by simp [hu])]
  rw [acc_guessEx (P := S.lay.prog) (W := x) (NN := S.NN) guessSep (m := S.NN) (j := 0)
    (pc := S.lay.oGuessE) (μ := mU S x μ) (by omega) at_guessE']
  refine ⟨bs, hbs, ?_⟩
  rw [pt_circSE]
  exact (tail_ex_iff hx hc hw hbs h).2 ⟨hst, hnext⟩

/-- **The universal case.** -/
theorem round_all (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (hw : S.M.w x ≤ S.NN)
    (h : S.MemOk x c μ) (hnacc : S.M.accB [c, x] = false) (hu : S.M.univB [c, x] = true)
    (hnext : ∀ bs : List Bool, bs.length = S.NN → S.M.stepB [S.gcfg x bs, c, x] = true →
      Acc S.lay.prog x S.lay.lL (mC S x μ bs)) : Acc S.lay.prog x S.lay.lL μ := by
  rw [head_iff hx hc h hnacc, if_pos hu]
  rw [acc_guessAll (P := S.lay.prog) (W := x) (NN := S.NN) guessSep (m := S.NN) (j := 0)
    (pc := S.lay.lUNI) (μ := mU S x μ) (by omega) at_guessA']
  intro bs hbs
  rw [pt_circSA]
  exact (tail_all_iff hx hc hw hbs h).2 (hnext bs hbs)

end Intro

/-! ### The converse, with the fuel -/

section Elim

variable {μ : ℕ → Bool} {k : ℕ}

/-- **What an accepting computation of the program at the head of the loop does.** -/
theorem round_elim (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN) (hw : S.M.w x ≤ S.NN)
    (h : S.MemOk x c μ) (hacc : AccN S.lay.prog x k S.lay.lL μ) :
    S.M.accB [c, x] = true ∨
      (S.M.univB [c, x] = false ∧ ∃ bs : List Bool, bs.length = S.NN ∧
        S.M.stepB [S.gcfg x bs, c, x] = true ∧
        ∃ k' < k, AccN S.lay.prog x k' S.lay.lL (mC S x μ bs)) ∨
      (S.M.univB [c, x] = true ∧ ∀ bs : List Bool, bs.length = S.NN →
        S.M.stepB [S.gcfg x bs, c, x] = true →
        ∃ k' < k, AccN S.lay.prog x k' S.lay.lL (mC S x μ bs)) := by
  by_cases hnacc : S.M.accB [c, x] = true
  · exact Or.inl hnacc
  have hnacc' : S.M.accB [c, x] = false := by simpa using hnacc
  -- the acceptance circuit
  obtain ⟨k1, hk1, hacc1⟩ := accN_block (P := S.lay.prog) (W := x) (pc := S.lay.lL) (μ := μ)
    (k := k) at_circA' simple_circProg hacc
  rw [pt_brA] at hacc1
  -- the branch on the acceptance bit
  obtain ⟨k2, hk2, hacc2⟩ := accN_brIf_false hacc1 instr_brA
    ((bit_mA hx hc h).trans hnacc')
  rw [pt_circU] at hacc2
  -- the classification circuit
  obtain ⟨k3, hk3, hacc3⟩ := accN_block (P := S.lay.prog) (W := x) (pc := S.lay.oCircU)
    (μ := mA S x μ) at_circU' simple_circProg hacc2
  rw [pt_brU] at hacc3
  -- the tail of a round, from the point where the guess has been made
  have htail : ∀ (bs : List Bool) (k' : ℕ), bs.length = S.NN →
      AccN S.lay.prog x k' S.lay.oCircSE (mG S x μ bs) →
      S.M.stepB [S.gcfg x bs, c, x] = true ∧
        ∃ k'' ≤ k', AccN S.lay.prog x k'' S.lay.lL (mC S x μ bs) := by
    intro bs k' hbs hk'
    obtain ⟨k4, hk4, hacc4⟩ := accN_block (P := S.lay.prog) (W := x) (pc := S.lay.oCircSE)
      (μ := mG S x μ bs) at_circSE' simple_circProg hk'
    rw [pt_brSE] at hacc4
    by_cases hst : S.M.stepB [S.gcfg x bs, c, x] = true
    · refine ⟨hst, ?_⟩
      obtain ⟨k5, hk5, hacc5⟩ := accN_brIf_true hacc4 instr_brSE
        ((bit_mS hx hc hbs hw h).trans hst)
      obtain ⟨k6, hk6, hacc6⟩ := accN_block (P := S.lay.prog) (W := x) (pc := S.lay.lCONT)
        (μ := mS S x μ bs) at_copy' simple_gatherProg hacc5
      rw [pt_jmp] at hacc6
      obtain ⟨k7, hk7, hacc7⟩ := accN_jmp hacc6 instr_jmp
      exact ⟨k7, by omega, hacc7⟩
    · exfalso
      obtain ⟨k5, hk5, hacc5⟩ := accN_brIf_false hacc4 instr_brSE
        ((bit_mS hx hc hbs hw h).trans (by simpa using hst))
      exact not_accN_rej instr_rej hacc5
  -- the tail of a round, in the universal copy
  have htailA : ∀ (bs : List Bool) (k' : ℕ), bs.length = S.NN →
      AccN S.lay.prog x k' S.lay.oCircSA (mG S x μ bs) →
      S.M.stepB [S.gcfg x bs, c, x] = true →
        ∃ k'' ≤ k', AccN S.lay.prog x k'' S.lay.lL (mC S x μ bs) := by
    intro bs k' hbs hk' hst
    obtain ⟨k4, hk4, hacc4⟩ := accN_block (P := S.lay.prog) (W := x) (pc := S.lay.oCircSA)
      (μ := mG S x μ bs) at_circSA' simple_circProg hk'
    rw [pt_brSA] at hacc4
    obtain ⟨k5, hk5, hacc5⟩ := accN_brIf_true hacc4 instr_brSA
      ((bit_mS hx hc hbs hw h).trans hst)
    obtain ⟨k6, hk6, hacc6⟩ := accN_block (P := S.lay.prog) (W := x) (pc := S.lay.lCONT)
      (μ := mS S x μ bs) at_copy' simple_gatherProg hacc5
    rw [pt_jmp] at hacc6
    obtain ⟨k7, hk7, hacc7⟩ := accN_jmp hacc6 instr_jmp
    exact ⟨k7, by omega, hacc7⟩
  by_cases hu : S.M.univB [c, x] = true
  · -- the universal copy
    refine Or.inr (Or.inr ⟨hu, ?_⟩)
    obtain ⟨k4, hk4, hacc4⟩ := accN_brIf_true hacc3 instr_brU
      ((bit_mU hx hc h).trans hu)
    obtain ⟨k5, hk5, hall⟩ := accN_guessAll (P := S.lay.prog) (W := x) (NN := S.NN) guessSep
      (m := S.NN) (j := 0) (pc := S.lay.lUNI) (μ := mU S x μ) (by omega) at_guessA' hacc4
    intro bs hbs hst
    have := hall bs hbs
    rw [pt_circSA] at this
    obtain ⟨k6, hk6, hacc6⟩ := htailA bs k5 hbs this hst
    exact ⟨k6, by omega, hacc6⟩
  · -- the existential copy
    refine Or.inr (Or.inl ⟨by simpa using hu, ?_⟩)
    obtain ⟨k4, hk4, hacc4⟩ := accN_brIf_false hacc3 instr_brU
      ((bit_mU hx hc h).trans (by simpa using hu))
    rw [pt_guessE] at hacc4
    obtain ⟨k5, hk5, bs, hbs, hacc5⟩ := accN_guessEx (P := S.lay.prog) (W := x) (NN := S.NN)
      guessSep (m := S.NN) (j := 0) (pc := S.lay.oGuessE) (μ := mU S x μ) (by omega)
      at_guessE' hacc4
    rw [pt_circSE] at hacc5
    obtain ⟨hst, k6, hk6, hacc6⟩ := htail bs k5 hbs hacc5
    exact ⟨bs, hbs, hst, k6, by omega, hacc6⟩

end Elim

end Sim

end Compile

end HTN
