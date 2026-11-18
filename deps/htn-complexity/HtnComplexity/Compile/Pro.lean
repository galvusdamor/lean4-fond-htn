import HtnComplexity.Compile.Loop
/-!
# The prologue of the compiled program

Before the loop, the program sets the cell that is always true, writes two copies of the cell
encoding of the input word, runs the circuits of the width and of the initial configuration,
gathers the width mask and the initial configuration, and writes the input word at the cell
bound.  All eight blocks are straight line, so the whole prologue is transparent: from the
program point `0` with the empty memory, the program accepts exactly when it accepts at the head
of the loop with a memory satisfying the invariant for the initial configuration
(`HTN.Compile.Sim.pro_iff`).
-/

namespace HTN

namespace Compile

namespace Sim

open Syn PSpace PTime

variable {S : Sim} {x : List Bool}

/-! ### The memories of the prologue -/

/-- After setting the cell that is always true. -/
def p1 (x : List Bool) : ℕ → Bool := runInstrs x (fun _ => false) [iSet1 1]

/-- After writing the input word for the width circuit. -/
def p2 (S : Sim) (x : List Bool) : ℕ → Bool :=
  runInstrs x (p1 x) (encInpProg S.lay.aXW S.n S.n)

/-- After the width circuit. -/
def p3 (S : Sim) (x : List Bool) : ℕ → Bool :=
  runInstrs x (p2 S x) (circProg S.lay.aXW 0 (2 * S.n) S.lay.CW.gates)

/-- After gathering the width mask. -/
def p4 (S : Sim) (x : List Bool) : ℕ → Bool :=
  runInstrs x (p3 S x) (gatherProg S.lay.aMW S.lay.maskSrc S.NN)

/-- After writing the input word for the initial circuit. -/
def p5 (S : Sim) (x : List Bool) : ℕ → Bool :=
  runInstrs x (p4 S x) (encInpProg S.lay.aXI S.n S.n)

/-- After the initial circuit. -/
def p6 (S : Sim) (x : List Bool) : ℕ → Bool :=
  runInstrs x (p5 S x) (circProg S.lay.aXI 0 (2 * S.n) S.lay.CI.gates)

/-- After gathering the initial configuration. -/
def p7 (S : Sim) (x : List Bool) : ℕ → Bool :=
  runInstrs x (p6 S x) (gatherProg S.lay.aC S.lay.initSrc (2 * S.NN))

/-- After writing the input word at the cell bound: the memory at the head of the loop. -/
def p8 (S : Sim) (x : List Bool) : ℕ → Bool :=
  runInstrs x (p7 S x) (encInpProg S.lay.aX S.NN S.n)

theorem p4_def : p4 S x = runInstrs x (p3 S x) (gatherProg S.lay.aMW S.lay.maskSrc S.NN) := rfl

theorem p7_def :
    p7 S x = runInstrs x (p6 S x) (gatherProg S.lay.aC S.lay.initSrc (2 * S.NN)) := rfl

/-! ### The addresses of the prologue -/

theorem aXW_eq : S.lay.aXW = S.lay.aT + 2 * S.NN := rfl

theorem aXI_eq : S.lay.aXI = S.lay.aXW + 2 * S.n + S.lay.CW.gates.length := rfl

theorem mm_eq : S.lay.mm = S.lay.aXI + 2 * S.n + S.lay.CI.gates.length := rfl

/-- All the addresses of the layout, as linear equations. -/
theorem addr2 :
    Lay.aG = 2 ∧ S.lay.aC = 2 + 2 * S.NN ∧ S.lay.aX = 2 + 4 * S.NN ∧ S.lay.aS = 2 + 6 * S.NN ∧
      S.lay.aMW = S.lay.aS + S.lay.gmax ∧ S.lay.aT = S.lay.aMW + S.NN ∧
      S.lay.aXW = S.lay.aT + 2 * S.NN ∧
      S.lay.aXI = S.lay.aXW + 2 * S.n + S.lay.CW.gates.length ∧
      S.lay.mm = S.lay.aXI + 2 * S.n + S.lay.CI.gates.length :=
  ⟨aG_eq, S.aC_eq, S.aX_eq, S.aS_eq, S.aMW_eq, S.aT_eq, aXW_eq, aXI_eq, mm_eq⟩

/-! ### What the prologue writes -/

theorem p1_apply (a : ℕ) : p1 x a = decide (a = 1) := by
  rw [p1, runInstrs_cons, runInstrs_nil, stepMem_iSet1, memUpd]
  by_cases h : a = 1 <;> simp [h]

/-- The input word, for the width circuit. -/
theorem p2_word (hx : x.length = S.n) {r : ℕ} (hr : r < 2 * S.n) :
    p2 S x (S.lay.aXW + r) = (encStr S.n x).getI r :=
  runInstrs_encInpProg hx hr

theorem p2_of_ne {a : ℕ} (ha : ∀ r < 2 * S.n, a ≠ S.lay.aXW + r) : p2 S x a = p1 x a :=
  runInstrs_encInpProg_of_ne ha

theorem p3_of_ne {a : ℕ} (ha : ∀ t < S.lay.CW.gates.length,
    a ≠ S.lay.aXW + 2 * S.n + t) : p3 S x a = p2 S x a :=
  runInstrs_circProg_of_ne ha

theorem p4_of_ne {a : ℕ} (ha : ∀ i < S.NN, a ≠ S.lay.aMW + i) : p4 S x a = p3 S x a :=
  runInstrs_gatherProg_of_ne ha

theorem p5_of_ne {a : ℕ} (ha : ∀ r < 2 * S.n, a ≠ S.lay.aXI + r) : p5 S x a = p4 S x a :=
  runInstrs_encInpProg_of_ne ha

theorem p6_of_ne {a : ℕ} (ha : ∀ t < S.lay.CI.gates.length,
    a ≠ S.lay.aXI + 2 * S.n + t) : p6 S x a = p5 S x a :=
  runInstrs_circProg_of_ne ha

theorem p7_of_ne {a : ℕ} (ha : ∀ r < 2 * S.NN, a ≠ S.lay.aC + r) : p7 S x a = p6 S x a :=
  runInstrs_gatherProg_of_ne ha

theorem p8_of_ne {a : ℕ} (ha : ∀ r < 2 * S.NN, a ≠ S.lay.aX + r) : p8 S x a = p7 S x a :=
  runInstrs_encInpProg_of_ne ha

/-- The two constants are written by the first block and never again. -/
theorem p8_const {a : ℕ} (ha : a < 2) : p8 S x a = decide (a = 1) := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  rw [p8_of_ne (by intro r hr; omega), p7_of_ne (by intro r hr; omega),
    p6_of_ne (by intro t ht; omega), p5_of_ne (by intro r hr; omega),
    p4_of_ne (by intro i hi; omega), p3_of_ne (by intro t ht; omega),
    p2_of_ne (by intro r hr; omega), p1_apply]

theorem p2_zero : p2 S x 0 = false := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  rw [p2_of_ne (by intro r hr; omega), p1_apply]
  simp

theorem p5_zero : p5 S x 0 = false := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  rw [p5_of_ne (by intro r hr; omega), p4_of_ne (by intro i hi; omega),
    p3_of_ne (by intro t ht; omega), p2_of_ne (by intro r hr; omega), p1_apply]
  simp

/-- The arguments of the width and initial circuits. -/
theorem args1 {μ : ℕ → Bool} {b : ℕ}
    (hb : ∀ r < 2 * S.n, μ (b + r) = (encStr S.n x).getI r) :
    ∀ w < 2 * S.n, μ (b + w) = (encArgs 1 S.n [x]).getI w := by
  intro w hw
  rw [show (1 : ℕ) = 0 + 1 from rfl, encArgs_cons,
    List.getI_append _ _ _ (by simp; omega)]
  exact hb w hw

/-- The width template, in the wires of the width circuit. -/
theorem p3_width (hx : x.length = S.n) {j : ℕ} (hj : j < 2 * S.BW) :
    p3 S x (S.lay.aXW + S.lay.CW.out.getI j) = (encStr S.BW (S.M.widthF [x])).getI j := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  exact circRead' S.FW S.n [x] rfl
    (by intro a ha; rw [List.mem_singleton] at ha; subst ha; omega)
    (by ring) (by omega) p2_zero (args1 (fun r hr => p2_word hx hr)) hj

/-- The initial configuration, in the wires of the initial circuit. -/
theorem p6_init (hx : x.length = S.n) {j : ℕ} (hj : j < 2 * S.BI) :
    p6 S x (S.lay.aXI + S.lay.CI.out.getI j) = (encStr S.BI (S.M.initF [x])).getI j := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  refine circRead' S.FI S.n [x] rfl
    (by intro a ha; rw [List.mem_singleton] at ha; subst ha; omega)
    (by ring) (by omega) p5_zero (args1 ?_) hj
  intro r hr
  exact runInstrs_encInpProg hx hr

/-! ### The width mask and the initial configuration -/

/-- **The width mask.** -/
theorem p4_mask (hx : x.length = S.n) {i : ℕ} (hi : i < S.NN) :
    p4 S x (S.lay.aMW + i) = decide (i < S.M.w x) := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have hsrc : ∀ i < S.NN, ∀ i' < S.NN, S.lay.maskSrc i ≠ S.lay.aMW + i' := by
    intro i hi i' hi'
    rw [Lay.maskSrc]
    split_ifs <;> omega
  rw [p4_def, runInstrs_gatherProg hsrc hi, Lay.maskSrc]
  have hBWe : S.lay.BW = S.BW := rfl
  by_cases hb : i < S.lay.BW
  · rw [if_pos hb, p3_width hx (by omega), getI_encStr_pres _ (by omega)]
    rfl
  · rw [if_neg hb]
    have hz : p3 S x 0 = false := by
      rw [p3_of_ne (by intro t ht; omega), p2_of_ne (by intro r hr; omega), p1_apply]
      simp
    rw [hz]
    have := w_le_BW (S := S) (x := x) (le_of_eq hx)
    symm
    simp only [decide_eq_false_iff_not, not_lt]
    omega

/-- **The initial configuration.** -/
theorem p7_cfg (hx : x.length = S.n) {r : ℕ} (hr : r < 2 * S.NN) :
    p7 S x (S.lay.aC + r) = (encStr S.NN (S.M.initF [x])).getI r := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have hsrc : ∀ r < 2 * S.NN, ∀ r' < 2 * S.NN, S.lay.initSrc r ≠ S.lay.aC + r' := by
    intro r hr r' hr'
    rw [Lay.initSrc]
    split_ifs <;> omega
  have hlenI : (S.M.initF [x]).length ≤ S.BI := initF_le_BI (le_of_eq hx)
  have hBI : S.BI ≤ S.NN := BI_le_NN
  rw [p7_def, runInstrs_gatherProg hsrc hr, Lay.initSrc]
  have hBIe : S.lay.BI = S.BI := rfl
  by_cases hb : r < 2 * S.lay.BI
  · rw [if_pos hb, p6_init hx (by omega)]
    -- the two encodings agree below `2 * BI`
    obtain ⟨i, s, hs, rfl⟩ : ∃ i s, s < 2 ∧ r = 2 * i + s := ⟨r / 2, r % 2, by omega, by omega⟩
    interval_cases s
    · rw [show 2 * i + 0 = 2 * i by omega, getI_encStr_pres _ (by omega),
        getI_encStr_pres _ (by omega)]
    · rw [getI_encStr_val _ (by omega), getI_encStr_val _ (by omega)]
  · rw [if_neg hb]
    have hz : p6 S x 0 = false := by
      rw [p6_of_ne (by intro t ht; omega), p5_of_ne (by intro r hr; omega),
        p4_of_ne (by intro i hi; omega), p3_of_ne (by intro t ht; omega),
        p2_of_ne (by intro r hr; omega), p1_apply]
      simp
    rw [hz]
    obtain ⟨i, s, hs, rfl⟩ : ∃ i s, s < 2 ∧ r = 2 * i + s := ⟨r / 2, r % 2, by omega, by omega⟩
    interval_cases s
    · rw [show 2 * i + 0 = 2 * i by omega, getI_encStr_pres _ (by omega)]
      symm
      simp only [decide_eq_false_iff_not, not_lt]
      omega
    · rw [getI_encStr_val _ (by omega), getI_of_le_length (by omega)]

/-! ### The invariant at the head of the loop -/

/-- **The prologue establishes the invariant for the initial configuration.** -/
theorem memOk_p8 (hx : x.length = S.n) : S.MemOk x (S.M.initF [x]) (p8 S x) := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [p8_const (by omega)]; simp
  · rw [p8_const (by omega)]; simp
  · intro i hi
    rw [p8_of_ne (by intro r hr; omega), p7_of_ne (by intro r hr; omega),
      p6_of_ne (by intro t ht; omega), p5_of_ne (by intro r hr; omega), p4_mask hx hi]
  · intro r hr
    exact runInstrs_encInpProg hx hr
  · intro r hr
    rw [p8_of_ne (by intro r' hr'; omega), p7_cfg hx hr]

/-! ### The prologue is transparent -/

theorem at_setOne' : ∀ t < ([iSet1 1] : List Instr).length,
    S.lay.prog.getI (0 + t) = ([iSet1 1] : List Instr).getI t := S.lay.at_setOne

theorem at_encXW' : ∀ t < (encInpProg S.lay.aXW S.n S.n).length,
    S.lay.prog.getI (1 + t) = (encInpProg S.lay.aXW S.n S.n).getI t :=
  fun t ht => S.lay.at_encXW t (by simpa using ht)

theorem at_circW' : ∀ t < (circProg S.lay.aXW 0 (2 * S.n) S.lay.CW.gates).length,
    S.lay.prog.getI (S.lay.oCircW + t)
      = (circProg S.lay.aXW 0 (2 * S.n) S.lay.CW.gates).getI t :=
  fun t ht => S.lay.at_circW t (by simpa using ht)

theorem at_mask' : ∀ t < (gatherProg S.lay.aMW S.lay.maskSrc S.NN).length,
    S.lay.prog.getI (S.lay.oMask + t) = (gatherProg S.lay.aMW S.lay.maskSrc S.NN).getI t :=
  fun t ht => S.lay.at_mask t (by simpa using ht)

theorem at_encXI' : ∀ t < (encInpProg S.lay.aXI S.n S.n).length,
    S.lay.prog.getI (S.lay.oEncXI + t) = (encInpProg S.lay.aXI S.n S.n).getI t :=
  fun t ht => S.lay.at_encXI t (by simpa using ht)

theorem at_circI' : ∀ t < (circProg S.lay.aXI 0 (2 * S.n) S.lay.CI.gates).length,
    S.lay.prog.getI (S.lay.oCircI + t)
      = (circProg S.lay.aXI 0 (2 * S.n) S.lay.CI.gates).getI t :=
  fun t ht => S.lay.at_circI t (by simpa using ht)

theorem at_initC' : ∀ t < (gatherProg S.lay.aC S.lay.initSrc (2 * S.NN)).length,
    S.lay.prog.getI (S.lay.oInitC + t)
      = (gatherProg S.lay.aC S.lay.initSrc (2 * S.NN)).getI t :=
  fun t ht => S.lay.at_initC t (by simpa using ht)

theorem at_encX' : ∀ t < (encInpProg S.lay.aX S.NN S.n).length,
    S.lay.prog.getI (S.lay.oEncX + t) = (encInpProg S.lay.aX S.NN S.n).getI t :=
  fun t ht => S.lay.at_encX t (by simpa using ht)

/-- **The prologue is transparent**: the program accepts from the start exactly when it accepts
at the head of the loop with the memory the prologue leaves. -/
theorem pro_iff :
    Acc S.lay.prog x 0 (fun _ => false) ↔ Acc S.lay.prog x S.lay.lL (p8 S x) := by
  have h1 := acc_block_iff (P := S.lay.prog) (W := x) (pc := 0) (μ := fun _ => false)
    at_setOne' (by intro I hI; simp at hI; subst hI; exact simple_iSet1 1)
  have h2 := acc_block_iff (P := S.lay.prog) (W := x) (pc := 1) (μ := p1 x)
    at_encXW' simple_encInpProg
  have h3 := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oCircW) (μ := p2 S x)
    at_circW' simple_circProg
  have h4 := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oMask) (μ := p3 S x)
    at_mask' simple_gatherProg
  have h5 := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oEncXI) (μ := p4 S x)
    at_encXI' simple_encInpProg
  have h6 := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oCircI) (μ := p5 S x)
    at_circI' simple_circProg
  have h7 := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oInitC) (μ := p6 S x)
    at_initC' simple_gatherProg
  have h8 := acc_block_iff (P := S.lay.prog) (W := x) (pc := S.lay.oEncX) (μ := p7 S x)
    at_encX' simple_encInpProg
  rw [show (0 : ℕ) + ([iSet1 1] : List Instr).length = 1 from rfl] at h1
  rw [length_encInpProg, show 1 + 2 * S.n = S.lay.oCircW from rfl] at h2
  rw [length_circProg, show S.lay.oCircW + S.lay.CW.gates.length = S.lay.oMask from rfl] at h3
  rw [length_gatherProg, show S.lay.oMask + S.NN = S.lay.oEncXI from rfl] at h4
  rw [length_encInpProg, show S.lay.oEncXI + 2 * S.n = S.lay.oCircI from rfl] at h5
  rw [length_circProg, show S.lay.oCircI + S.lay.CI.gates.length = S.lay.oInitC from rfl] at h6
  rw [length_gatherProg, show S.lay.oInitC + 2 * S.NN = S.lay.oEncX from rfl] at h7
  rw [length_encInpProg, show S.lay.oEncX + 2 * S.NN = S.lay.lL from rfl] at h8
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))

end Sim

end Compile

end HTN
