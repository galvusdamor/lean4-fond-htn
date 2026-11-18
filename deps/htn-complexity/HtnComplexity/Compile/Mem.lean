import HtnComplexity.Compile.Sim
/-!
# What each block of the loop does to the memory

The loop of the compiled program is made of five kinds of block: the three circuits (the
acceptance test, the classification test and the transition test), the guess of a successor
configuration, and the copy of the guess into the configuration.  This file says, for each of
them, **what it computes and what it leaves alone**, in terms of the memory invariant
`HTN.Compile.Sim.MemOk` of `HtnComplexity/Compile/Sim.lean`.

Nothing here mentions acceptance: a block is a list of instructions, and the statements are
about `HTN.Compile.runInstrs` and `HTN.Compile.guessMem`.  Acceptance across a block is handled
once and for all by `HTN.Compile.acc_block_iff`, `HTN.Compile.acc_guessEx` and their fuelled
forms, and is put together in `HtnComplexity/Compile/Round.lean`.
-/

namespace HTN

namespace Compile

/-- A prefix of a bit string, read out of range. -/
theorem getI_take {l : List Bool} {m i : ℕ} : (l.take m).getI i = (l.getI i && decide (i < m)) := by
  by_cases him : i < m
  · by_cases hil : i < l.length
    · rw [List.getI_eq_getElem _ (by simp; omega), List.getI_eq_getElem _ hil]
      simp [him]
    · rw [getI_of_le_length (by simp; omega), getI_of_le_length (by omega)]
      simp
  · rw [getI_of_le_length (by simp; omega)]
    simp [him]

namespace Sim

open Syn PSpace PTime

variable {S : Sim} {x : List Bool}

/-! ### The sizes -/

theorem n_le_NN : S.n ≤ S.NN := by rw [NN]; omega

theorem BW_le_NN : S.BW ≤ S.NN := by rw [NN]; omega

theorem BI_le_NN : S.BI ≤ S.NN := by rw [NN]; omega

/-- The width of a configuration is within the bound of the width circuits. -/
theorem w_le_BW (hx : x.length ≤ S.n) : S.M.w x ≤ S.BW := by
  exact S.FW.len_le S.n [x] rfl (by intro a ha; rw [List.mem_singleton] at ha; subst ha; exact hx)

theorem w_le_NN (hx : x.length ≤ S.n) : S.M.w x ≤ S.NN :=
  le_trans (w_le_BW hx) BW_le_NN

/-- The initial configuration is within the bound of the initial circuits. -/
theorem initF_le_BI (hx : x.length ≤ S.n) : (S.M.initF [x]).length ≤ S.BI :=
  S.FI.len_le S.n [x] rfl (by intro a ha; rw [List.mem_singleton] at ha; subst ha; exact hx)

/-! ### The addresses, as arithmetic -/

/-- All the addresses of the layout, as linear equations. -/
theorem addr :
    Lay.aG = 2 ∧ S.lay.aC = 2 + 2 * S.NN ∧ S.lay.aX = 2 + 4 * S.NN ∧ S.lay.aS = 2 + 6 * S.NN ∧
      S.lay.aMW = S.lay.aS + S.lay.gmax ∧ S.lay.aT = S.lay.aMW + S.NN :=
  ⟨aG_eq, S.aC_eq, S.aX_eq, S.aS_eq, S.aMW_eq, S.aT_eq⟩

theorem aC_add : S.lay.aC + 4 * S.NN = S.lay.aS := by
  obtain ⟨-, h1, -, h2, -⟩ := addr (S := S); omega

theorem aG_add : Lay.aG + 6 * S.NN = S.lay.aS := by
  obtain ⟨h0, -, -, h2, -⟩ := addr (S := S); omega

/-! ### A circuit of the loop -/

/-- A safe cell is left alone by the block of a circuit of the loop. -/
theorem circ_agree {base width : ℕ} {gs : List Gate} (hbase : base + width = S.lay.aS)
    (hg : gs.length ≤ S.lay.gmax) {μ : ℕ → Bool} {a : ℕ} (ha : S.Safe a) :
    runInstrs x μ (circProg base 0 width gs) a = μ a := by
  refine runInstrs_circProg_of_ne ?_
  intro t ht
  rw [show base + width + t = S.lay.aS + t by omega]
  exact safe_ne_wire ha (lt_of_lt_of_le ht hg)

/-- **The block of a circuit of the loop preserves the invariant.** -/
theorem memOk_circ {c : List Bool} {base width : ℕ} {gs : List Gate}
    (hbase : base + width = S.lay.aS) (hg : gs.length ≤ S.lay.gmax) {μ : ℕ → Bool}
    (h : S.MemOk x c μ) : S.MemOk x c (runInstrs x μ (circProg base 0 width gs)) :=
  h.of_agree fun _ ha => circ_agree hbase hg (safe_of_inv ha)

/-- The block of a circuit of the loop leaves the guessed configuration alone. -/
theorem aG_circ {base width : ℕ} {gs : List Gate} (hbase : base + width = S.lay.aS)
    (hg : gs.length ≤ S.lay.gmax) {μ : ℕ → Bool} {c' : List Bool}
    (hgc : ∀ r < 2 * S.NN, μ (Lay.aG + r) = (encStr S.NN c').getI r) :
    ∀ r < 2 * S.NN,
      runInstrs x μ (circProg base 0 width gs) (Lay.aG + r) = (encStr S.NN c').getI r :=
  fun r hr => by rw [circ_agree hbase hg (safe_aG hr)]; exact hgc r hr

/-! ### What the three circuits compute -/

theorem zero_lt_aC : 0 < S.lay.aC := by obtain ⟨-, h1, -⟩ := addr (S := S); omega

theorem zero_lt_aG : 0 < Lay.aG := by rw [aG_eq]; omega

/-- **The acceptance circuit computes the acceptance test.** -/
theorem read_accBit {c : List Bool} {μ : ℕ → Bool} (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN)
    (h : S.MemOk x c μ) :
    runInstrs x μ (circProg S.lay.aC 0 (4 * S.NN) S.lay.CA.gates) S.lay.accBit
      = S.M.accB [c, x] := by
  have hargs : ∀ a ∈ [c, x], a.length ≤ S.NN := by
    intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption
  have hread := circReadB S.FA S.NN [c, x] rfl hargs (zero_lt_aC (S := S)) h.z (args2 h)
    (W := x)
  rw [Lay.accBit, show (4 : ℕ) * S.NN = 2 * S.NN * 2 by ring]
  exact hread

/-- **The classification circuit computes the classification test.** -/
theorem read_univBit {c : List Bool} {μ : ℕ → Bool} (hx : x.length ≤ S.NN) (hc : c.length ≤ S.NN)
    (h : S.MemOk x c μ) :
    runInstrs x μ (circProg S.lay.aC 0 (4 * S.NN) S.lay.CU.gates) S.lay.univBit
      = S.M.univB [c, x] := by
  have hargs : ∀ a ∈ [c, x], a.length ≤ S.NN := by
    intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption
  have hread := circReadB S.FU S.NN [c, x] rfl hargs (zero_lt_aC (S := S)) h.z (args2 h)
    (W := x)
  rw [Lay.univBit, show (4 : ℕ) * S.NN = 2 * S.NN * 2 by ring]
  exact hread

/-- **The transition circuit computes the transition test.** -/
theorem read_stepBit {c c' : List Bool} {μ : ℕ → Bool} (hx : x.length ≤ S.NN)
    (hc : c.length ≤ S.NN) (hc' : c'.length ≤ S.NN) (h : S.MemOk x c μ)
    (hg : ∀ r < 2 * S.NN, μ (Lay.aG + r) = (encStr S.NN c').getI r) :
    runInstrs x μ (circProg Lay.aG 0 (6 * S.NN) S.lay.CS.gates) S.lay.stepBit
      = S.M.stepB [c', c, x] := by
  have hargs : ∀ a ∈ [c', c, x], a.length ≤ S.NN := by
    intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> assumption
  have hread := circReadB S.FS S.NN [c', c, x] rfl hargs zero_lt_aG h.z
    (args3 h hg) (W := x)
  rw [Lay.stepBit, show (6 : ℕ) * S.NN = 2 * S.NN * 3 by ring]
  exact hread

/-! ### The guess -/

theorem guessSep : GuessSep Lay.aG S.lay.aMW S.lay.aT S.NN where
  gm := by obtain ⟨h0, -, -, h2, h3, -⟩ := addr (S := S); omega
  mt := by obtain ⟨-, -, -, -, -, h⟩ := addr (S := S); omega

/-- A cell of the invariant is touched by no group of the guess. -/
theorem inv_guess_ne {a : ℕ} (ha : S.Inv a) {i : ℕ} (hi : i < S.NN) :
    a ≠ Lay.aG + 2 * i ∧ a ≠ Lay.aG + 2 * i + 1 ∧ a ≠ S.lay.aT + 2 * i ∧
      a ≠ S.lay.aT + 2 * i + 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := addr (S := S)
  rcases ha with rfl | rfl | ⟨j, hj, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;>
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The guess preserves the invariant.** -/
theorem memOk_guess {c : List Bool} {μ : ℕ → Bool} {bs : List Bool} (hbs : bs.length = S.NN)
    (h : S.MemOk x c μ) : S.MemOk x c (guessMem Lay.aG S.lay.aMW S.lay.aT 0 μ bs) :=
  h.of_agree fun a ha => by
    refine guessMem_of_ne ?_
    intro i _ hi2
    exact inv_guess_ne ha (by omega)

/-- The configuration the guessed bits stand for. -/
def gcfg (S : Sim) (x bs : List Bool) : List Bool := bs.take (S.M.w x)

theorem length_gcfg {bs : List Bool} (hbs : bs.length = S.NN) (hw : S.M.w x ≤ S.NN) :
    (S.gcfg x bs).length = S.M.w x := by
  rw [gcfg, List.length_take, hbs]
  omega

/-- **The guess writes the cell encoding of a configuration of the machine's width.** -/
theorem guess_cfg {c : List Bool} {μ : ℕ → Bool} {bs : List Bool} (hbs : bs.length = S.NN)
    (hw : S.M.w x ≤ S.NN) (h : S.MemOk x c μ) :
    ∀ r < 2 * S.NN, guessMem Lay.aG S.lay.aMW S.lay.aT 0 μ bs (Lay.aG + r)
      = (encStr S.NN (S.gcfg x bs)).getI r := by
  have hlen : (S.gcfg x bs).length = S.M.w x := length_gcfg hbs hw
  intro r hr
  obtain ⟨i, s, hs, rfl⟩ : ∃ i s, s < 2 ∧ r = 2 * i + s := ⟨r / 2, r % 2, by omega, by omega⟩
  have hi : i < S.NN := by omega
  interval_cases s
  · have hp := guessMem_pres (Gb := Lay.aG) (MWb := S.lay.aMW) (Tb := S.lay.aT) (NN := S.NN)
      guessSep (bs := bs) (j := 0) (μ := μ) (r := i) (by omega) (by omega)
    rw [show 2 * i + 0 = 2 * i by omega, show (2 : ℕ) * i = 2 * (0 + i) by omega, hp,
      h.mask (0 + i) (by omega), Nat.zero_add, getI_encStr_pres _ hi, hlen]
  · have hv := guessMem_val (Gb := Lay.aG) (MWb := S.lay.aMW) (Tb := S.lay.aT) (NN := S.NN)
      guessSep (bs := bs) (j := 0) (μ := μ) (r := i) (by omega) (by omega)
    rw [show Lay.aG + (2 * i + 1) = Lay.aG + 2 * (0 + i) + 1 by omega, hv,
      h.mask (0 + i) (by omega), getI_encStr_val _ hi]
    simp only [gcfg, getI_take, Nat.zero_add]

/-! ### Copying the guess into the configuration -/

/-- **The copy of the guess into the configuration restores the invariant, for the guessed
configuration.** -/
theorem memOk_gather {c c' : List Bool} {μ : ℕ → Bool} (h : S.MemOk x c μ)
    (hg : ∀ r < 2 * S.NN, μ (Lay.aG + r) = (encStr S.NN c').getI r) :
    S.MemOk x c' (runInstrs x μ (gatherProg S.lay.aC (fun i => Lay.aG + i) (2 * S.NN))) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := addr (S := S)
  have hout : ∀ a : ℕ, (a = 0 ∨ a = 1 ∨ (∃ i < S.NN, a = S.lay.aMW + i) ∨
      (∃ r < 2 * S.NN, a = S.lay.aX + r)) →
      runInstrs x μ (gatherProg S.lay.aC (fun i => Lay.aG + i) (2 * S.NN)) a = μ a := by
    intro a ha
    refine runInstrs_gatherProg_of_ne ?_
    intro i hi
    rcases ha with rfl | rfl | ⟨j, hj, rfl⟩ | ⟨r, hr, rfl⟩ <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hout 0 (Or.inl rfl)]; exact h.z
  · rw [hout 1 (Or.inr (Or.inl rfl))]; exact h.one
  · intro i hi
    rw [hout _ (Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩)))]; exact h.mask i hi
  · intro r hr
    rw [hout _ (Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩)))]; exact h.inp r hr
  · intro r hr
    rw [runInstrs_gatherProg (by intro i hi i' hi'; omega) hr]
    exact hg r hr

end Sim

end Compile

end HTN
