import HtnComplexity.Compile.Pro
/-!
# The compiled program is well formed

`HTN.Compile.Wf` asks that every instruction of a program write and read inside the memory, read
the input word inside its length, and be canonical.  This file checks it for the program of
`HtnComplexity/Compile/Layout.lean`, with the memory width `mm` of the layout and the input
length `n` (`HTN.Compile.Sim.wf_prog`).

Everything is arithmetic on the addresses, except for the outputs of the circuits, which are
wires of the circuit they come from — that is what `HTN.Compile.CircFam.out_lt` is for.
-/

namespace HTN

namespace Compile

/-! ### The guess -/

/-- Every instruction of a group of the guess is well formed. -/
theorem wf_guessGroup {uni : Bool} {Gb MWb Tb i mm n : ℕ}
    (hG : Gb + 2 * i + 1 < MWb) (hM : MWb + i < Tb) (hT : Tb + 2 * i + 1 < mm) :
    ∀ I ∈ guessGroup uni Gb MWb Tb i, instrWf I mm n ∧ instrCanon I := by
  intro I hI
  rw [guessGroup] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl
  · cases uni
    · exact ⟨by simp only [instrWf, iEx]; norm_num; omega, by simp [instrCanon, iEx]⟩
    · exact ⟨by simp only [instrWf, iAll]; norm_num; omega, by simp [instrCanon, iAll]⟩
  · exact ⟨by simp only [instrWf, iNand]; norm_num; omega, by simp [instrCanon, iNand]⟩
  · exact ⟨by simp only [instrWf, iNand]; norm_num; omega, by simp [instrCanon, iNand]⟩
  · exact ⟨by simp only [instrWf, iCopy]; norm_num; omega, by simp [instrCanon, iCopy]⟩

/-- **Every instruction of the guess is well formed.** -/
theorem wf_guessProg {uni : Bool} {Gb MWb Tb j m mm n : ℕ}
    (hG : Gb + 2 * (j + m) ≤ MWb) (hM : MWb + (j + m) ≤ Tb) (hT : Tb + 2 * (j + m) ≤ mm) :
    ∀ I ∈ guessProg uni Gb MWb Tb j m, instrWf I mm n ∧ instrCanon I := by
  intro I hI
  rw [guessProg, List.mem_flatMap] at hI
  obtain ⟨r, hr, hI⟩ := hI
  rw [List.mem_range] at hr
  exact wf_guessGroup (by omega) (by omega) (by omega) I hI

namespace Sim

open Syn PSpace PTime

variable {S : Sim}

/-! ### The outputs of the circuits lie inside their wires -/

theorem lenW_out : S.lay.CW.out.length = 2 * S.BW := S.FW.out_length S.n

theorem lenI_out : S.lay.CI.out.length = 2 * S.BI := S.FI.out_length S.n

/-- An output wire of the width circuit is a wire of it. -/
theorem outW_lt' {j : ℕ} (hj : j < S.lay.CW.out.length) :
    S.lay.aXW + S.lay.CW.out.getI j < S.lay.aXI := by
  have hmem : S.lay.CW.out.getI j ∈ S.lay.CW.out := by
    rw [List.getI_eq_getElem _ hj]; exact List.getElem_mem hj
  have h := S.FW.out_lt S.n _ hmem
  rw [S.FW.nin_eq S.n] at h
  have h' : S.lay.CW.out.getI j < 2 * S.n * 1 + S.lay.CW.gates.length := h
  have : S.lay.aXI = S.lay.aXW + 2 * S.n + S.lay.CW.gates.length := aXI_eq
  omega

/-- An output wire of the initial circuit is a wire of it. -/
theorem outI_lt' {j : ℕ} (hj : j < S.lay.CI.out.length) :
    S.lay.aXI + S.lay.CI.out.getI j < S.lay.mm := by
  have hmem : S.lay.CI.out.getI j ∈ S.lay.CI.out := by
    rw [List.getI_eq_getElem _ hj]; exact List.getElem_mem hj
  have h := S.FI.out_lt S.n _ hmem
  rw [S.FI.nin_eq S.n] at h
  have h' : S.lay.CI.out.getI j < 2 * S.n * 1 + S.lay.CI.gates.length := h
  have : S.lay.mm = S.lay.aXI + 2 * S.n + S.lay.CI.gates.length := mm_eq
  omega

/-- A circuit family for a predicate has at least one output cell. -/
theorem B_pos {p : Args → Bool} {k : ℕ} (F : CircFam (fun args => [p args]) k) (N : ℕ) :
    1 ≤ F.B.eval N := by
  have := F.len_le N (List.replicate k []) (by simp)
    (by intro a ha; rw [List.eq_of_mem_replicate ha]; simp)
  simpa using this

/-- The output wire the answer of a predicate circuit is read off is a wire of the circuit. -/
theorem out1_lt {p : Args → Bool} {k : ℕ} (F : CircFam (fun args => [p args]) k) (N : ℕ) :
    (F.C N).out.getI 1 < 2 * N * k + (F.C N).gates.length := by
  have hlen : (F.C N).out.length = 2 * F.B.eval N := F.out_length N
  have h1 : 1 < (F.C N).out.length := by rw [hlen]; have := B_pos F N; omega
  have hmem : (F.C N).out.getI 1 ∈ (F.C N).out := by
    rw [List.getI_eq_getElem _ h1]; exact List.getElem_mem h1
  have := F.out_lt N _ hmem
  rw [F.nin_eq N] at this
  exact this

theorem outA_lt : S.lay.aC + S.lay.CA.out.getI 1 < S.lay.aMW := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have h' : S.lay.CA.out.getI 1 < 2 * S.NN * 2 + S.lay.CA.gates.length := out1_lt S.FA S.NN
  have := gmaxA (S := S)
  omega

theorem outU_lt : S.lay.aC + S.lay.CU.out.getI 1 < S.lay.aMW := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have h' : S.lay.CU.out.getI 1 < 2 * S.NN * 2 + S.lay.CU.gates.length := out1_lt S.FU S.NN
  have := gmaxU (S := S)
  omega

theorem outS_lt : Lay.aG + S.lay.CS.out.getI 1 < S.lay.aMW := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have h' : S.lay.CS.out.getI 1 < 2 * S.NN * 3 + S.lay.CS.gates.length := out1_lt S.FS S.NN
  have := gmaxS (S := S)
  omega

/-! ### The memory is large enough -/

theorem aMW_le_mm : S.lay.aMW ≤ S.lay.mm := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  omega

theorem accBit_lt : S.lay.accBit < S.lay.mm := by
  have h := aMW_le_mm (S := S)
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have h' := outA_lt (S := S)
  rw [Lay.accBit]
  omega

theorem univBit_lt : S.lay.univBit < S.lay.mm := by
  have h := aMW_le_mm (S := S)
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have h' := outU_lt (S := S)
  rw [Lay.univBit]
  omega

theorem stepBit_lt : S.lay.stepBit < S.lay.mm := by
  have h := aMW_le_mm (S := S)
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have h' := outS_lt (S := S)
  rw [Lay.stepBit]
  omega

/-! ### The program is well formed -/

/-- **The compiled program is well formed.** -/
theorem wf_prog : Wf S.lay.prog S.lay.mm S.n := by
  obtain ⟨hG, hC, hX, hS, hMW, hT, hXW, hXI, hmm⟩ := addr2 (S := S)
  have hgA := gmaxA (S := S)
  have hgU := gmaxU (S := S)
  have hgS := gmaxS (S := S)
  have hn : S.lay.n = S.n := rfl
  have hNN : S.lay.NN = S.NN := rfl
  refine ⟨by omega, ?_⟩
  intro I hI
  rw [Lay.prog, List.mem_flatten] at hI
  obtain ⟨b, hb, hIb⟩ := hI
  rw [Lay.blocks] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- `[iSet1 1]`
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hIb
    subst hIb
    exact ⟨by simp only [instrWf, iSet1]; norm_num; omega, by simp [instrCanon, iSet1]⟩
  -- the input word for the width circuit
  · exact wf_encInpProg (by omega) I hIb
  -- the width circuit
  · exact wf_circProg (by omega) (by omega) I hIb
  -- the width mask
  · refine wf_gatherProg (by omega) ?_ I hIb
    intro i hi
    rw [Lay.maskSrc]
    split_ifs with hib
    · have hBW : S.lay.BW = S.BW := rfl
      have hj : 2 * i < S.lay.CW.out.length := by rw [lenW_out]; omega
      have := outW_lt' (S := S) hj
      omega
    · omega
  -- the input word for the initial circuit
  · exact wf_encInpProg (by omega) I hIb
  -- the initial circuit
  · exact wf_circProg (by omega) (by omega) I hIb
  -- the initial configuration
  · refine wf_gatherProg (by omega) ?_ I hIb
    intro r hr
    rw [Lay.initSrc]
    split_ifs with hrb
    · have hBI : S.lay.BI = S.BI := rfl
      have hj : r < S.lay.CI.out.length := by rw [lenI_out]; omega
      have := outI_lt' (S := S) hj
      omega
    · omega
  -- the input word at the cell bound
  · exact wf_encInpProg (by omega) I hIb
  -- the acceptance circuit
  · exact wf_circProg (by omega) (by omega) I hIb
  -- the branch on the acceptance bit
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hIb
    subst hIb
    have := accBit_lt (S := S)
    exact ⟨by simp only [instrWf, iBrIf]; norm_num; omega, by simp [instrCanon, iBrIf]⟩
  -- the classification circuit
  · exact wf_circProg (by omega) (by omega) I hIb
  -- the branch on the classification bit
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hIb
    subst hIb
    have := univBit_lt (S := S)
    exact ⟨by simp only [instrWf, iBrIf]; norm_num; omega, by simp [instrCanon, iBrIf]⟩
  -- the existential guess
  · exact wf_guessProg (by omega) (by omega) (by omega) I hIb
  -- the transition circuit of the existential copy
  · exact wf_circProg (by omega) (by omega) I hIb
  -- the branch on the transition bit of the existential copy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hIb
    have := stepBit_lt (S := S)
    rcases hIb with rfl | rfl
    · exact ⟨by simp only [instrWf, iBrIf]; norm_num; omega, by simp [instrCanon, iBrIf]⟩
    · exact ⟨by simp [instrWf, iRej], by simp [instrCanon, iRej]⟩
  -- the universal guess
  · exact wf_guessProg (by omega) (by omega) (by omega) I hIb
  -- the transition circuit of the universal copy
  · exact wf_circProg (by omega) (by omega) I hIb
  -- the branch on the transition bit of the universal copy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hIb
    have := stepBit_lt (S := S)
    rcases hIb with rfl | rfl
    · exact ⟨by simp only [instrWf, iBrIf]; norm_num; omega, by simp [instrCanon, iBrIf]⟩
    · exact ⟨by simp [instrWf, iAcc], by simp [instrCanon, iAcc]⟩
  -- the copy of the guess into the configuration
  · refine wf_gatherProg (by omega) ?_ I hIb
    intro i hi
    omega
  -- the jump back to the head of the loop
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hIb
    subst hIb
    exact ⟨by simp [instrWf, iJmp], by simp [instrCanon, iJmp]⟩
  -- the accepting instruction
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hIb
    subst hIb
    exact ⟨by simp [instrWf, iAcc], by simp [instrCanon, iAcc]⟩

end Sim

end Compile

end HTN
