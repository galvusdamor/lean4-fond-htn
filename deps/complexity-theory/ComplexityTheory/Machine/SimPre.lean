import ComplexityTheory.Machine.SimStep
/-!
# A single-tape Turing machine simulating a stack machine: the preamble

`HTN.Mach.sim_pre`: from the initial configuration on input `x`, the simulating machine reaches
`good |x| ⟨0, inStore kin x⟩` — the stack machine at address `0` with `x` reversed on stack `kin`
and all other stacks empty — deterministically, in at most `(|x| + 1) * (6 * (|x| + 2) * (K + 1))`
steps and within the space `|x| + 2 + (|x| + 1) * (K + 1)`.

During the preamble the cells `0, …, n` hold what is left of the input (`HTN.Mach.preTape`): the
bits not yet moved, right-aligned against cell `n`, blanks to their left.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM

variable {C : List Ins} {K kin : ℕ}

/-- The tape `t`, with the cells `0, …, n` replaced by `low`. -/
def mix (n : ℕ) (low t : ℕ → Sym) : ℕ → Sym := fun c => if c ≤ n then low c else t c

/-- The remaining input bits `rem`, right-aligned against cell `n`. -/
def remLow (n : ℕ) (rem : List Bool) : ℕ → Sym := fun c =>
  if c + rem.length < n then none else if c < n then rem[c + rem.length - n]? else none

/-- The tape during the preamble. -/
def preTape (K n : ℕ) (rem : List Bool) (S : Store) : ℕ → Sym := mix n (remLow n rem) (lay K n S)

/-- The stacks after the input `p` has been read: `p` reversed on stack `kin`. -/
def inStore (kin : ℕ) (p : List Bool) : Store := Function.update (fun _ => []) kin p.reverse

theorem mix_high {n : ℕ} {low t : ℕ → Sym} {c : ℕ} (h : n < c) : mix n low t c = t c := by
  unfold mix; rw [if_neg (by omega)]

theorem update_mix {n : ℕ} {low t : ℕ → Sym} {c : ℕ} (h : n < c) (v : Sym) :
    Function.update (mix n low t) c v = mix n low (Function.update t c v) := by
  funext i
  unfold mix
  by_cases hi : i = c
  · subst hi; simp [show ¬ i ≤ n by omega]
  · simp only [Function.update_of_ne hi]

theorem cell_gt (n j r : ℕ) : n < cell K n j r := by unfold cell; omega

theorem home_gt (n : ℕ) : n < home K n := by unfold home; omega

theorem preTape_nil (n : ℕ) (S : Store) : preTape K n [] S = lay K n S := by
  funext c
  unfold preTape mix remLow
  by_cases hc : c ≤ n
  · simp only [if_pos hc, lay_low _ hc]; split_ifs <;> simp
  · simp only [if_neg hc]

/-! ### Walking over input bits -/

theorem seg_walk_right {Sp : ℕ} (P : Phase) (hP : ∀ pc, P ≠ .exec pc)
    (hδ : ∀ c, phaseTr C K kin P (some c) = [(.base P, some c, .right)]) (tp : ℕ → Sym) :
    ∀ d i, (∀ e < d, ∃ c, tp (i + e) = some c) → i + d < Sp →
      (simM C K kin).Seg Sp ⟨.base P, i, tp⟩ ⟨.base P, i + d, tp⟩ d := by
  intro d
  induction d with
  | zero => intro i _ hS; exact NTM.Seg.refl (by simpa using hS)
  | succ d ih =>
    intro i hb hS
    obtain ⟨c, hc⟩ := hb 0 (by omega)
    simp only [Nat.add_zero] at hc
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp) (c := ⟨.base P, i, tp⟩)
      (t := (.base P, some c, .right)) (by simp only [δ]; rw [hc, hδ]) (notAcc_base hP)
      (show i < Sp by omega) (show i + 1 < Sp by omega)
    rw [nxt_same' hc] at h1
    simp only [Move.apply] at h1
    have h2 := ih (i + 1) (fun e he => by
      obtain ⟨c', hc'⟩ := hb (e + 1) (by omega); exact ⟨c', by rw [← hc']; ring_nf⟩) (by omega)
    rw [show i + (d + 1) = i + 1 + d by omega]
    exact (h1.trans h2).of_eq (by omega)

theorem seg_walk_left {Sp : ℕ} (P : Phase) (hP : ∀ pc, P ≠ .exec pc)
    (hδ : ∀ c, phaseTr C K kin P (some c) = [(.base P, some c, .left)]) (tp : ℕ → Sym) :
    ∀ d i, (∀ e < d, ∃ c, tp (i - e) = some c) → d ≤ i → i < Sp →
      (simM C K kin).Seg Sp ⟨.base P, i, tp⟩ ⟨.base P, i - d, tp⟩ d := by
  intro d
  induction d with
  | zero => intro i _ _ hS; exact NTM.Seg.refl (by simpa using hS)
  | succ d ih =>
    intro i hb hd hS
    obtain ⟨c, hc⟩ := hb 0 (by omega)
    simp only [Nat.sub_zero] at hc
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp) (c := ⟨.base P, i, tp⟩)
      (t := (.base P, some c, .left)) (by simp only [δ]; rw [hc, hδ]) (notAcc_base hP)
      (show i < Sp by omega) (show i - 1 < Sp by omega)
    rw [nxt_same' hc] at h1
    simp only [Move.apply] at h1
    have h2 := ih (i - 1) (fun e he => by
      obtain ⟨c', hc'⟩ := hb (e + 1) (by omega)
      exact ⟨c', by rw [← hc']; congr 1; omega⟩) (by omega) (by omega)
    rw [show i - (d + 1) = i - 1 - d by omega]
    exact (h1.trans h2).of_eq (by omega)

/-! ### Routines on tapes that agree with the layout behind the input -/

theorem seg_scanUpT {Sp n : ℕ} (S : Store) (low : ℕ → Sym) {k : ℕ} (hk : k < K) (act : Act)
    (cont : Option ℕ) (hSp : cell K n (S k).length k < Sp) :
    ∀ d j, j + d = (S k).length →
      (simM C K kin).Seg Sp ⟨.base (.scan act k cont (decide (j = 0))), cell K n j k,
          mix n low (lay K n S)⟩
        ⟨.base (.scan act k cont (decide ((S k).length = 0))), cell K n (S k).length k,
          mix n low (lay K n S)⟩ (d * (K + 1)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    simp only [Nat.add_zero] at hj; subst hj
    exact (NTM.Seg.refl (N := simM C K kin) (c := ⟨QS.base (.scan act k cont
      (decide ((S k).length = 0))), cell K n (S k).length k, mix n low (lay K n S)⟩) hSp).of_eq
      (by ring)
  | succ d ih =>
    intro j hj
    have hjl : j < (S k).length := by omega
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, mix n low (lay K n S) (cell K n j k) = some c₀ := by
      rw [mix_high (cell_gt n j k), lay_track _ hk]
      exact ⟨_, List.getElem?_eq_getElem (by simpa using hjl)⟩
    have hle : cell K n (j + 1) k ≤ cell K n (S k).length k := by unfold cell; nlinarith
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.scan act k cont (decide (j = 0))), cell K n j k, mix n low (lay K n S)⟩)
      (t := (mvTo true K (.scan act k cont false), some c₀, .right))
      (by simp only; rw [hc₀]; rfl) (notAcc_base (by intro pc h; cases h))
      (show cell K n j k < Sp by rw [cell_succ] at hle; omega)
      (show cell K n j k + 1 < Sp by rw [cell_succ] at hle; omega)
    rw [nxt_same' hc₀] at h1
    have h2 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp)
      (.scan act k cont false) (mix n low (lay K n S)) K (cell K n j k + 1)
      (by rw [cell_succ] at hle; omega)
    have h3 := ih (j + 1) (by omega)
    simp only [show decide (j + 1 = 0) = false by simp] at h3
    rw [show cell K n j k + 1 + K = cell K n (j + 1) k by rw [cell_succ]; ring] at h2
    exact ((h1.trans h2).trans h3).of_eq (by ring)

theorem seg_rScanT {Sp n : ℕ} (S : Store) (low : ℕ → Sym) (cont : Option ℕ) :
    ∀ j, cell K n j K < Sp →
      (simM C K kin).Seg Sp ⟨.base (.rScan cont), cell K n j K, mix n low (lay K n S)⟩
        ⟨.base (contPh cont), home K n, mix n low (lay K n S)⟩ (j * (K + 1) + 1) := by
  intro j
  induction j with
  | zero =>
    intro hSp
    have hm : mix n low (lay K n S) (cell K n 0 K) = some true := by
      rw [mix_high (cell_gt n 0 K), lay_marker]; rfl
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.rScan cont), cell K n 0 K, mix n low (lay K n S)⟩)
      (t := (.base (contPh cont), some true, .stay))
      (by simp only; rw [hm]; rfl) (notAcc_base (by intro pc h; cases h)) hSp
      (by simpa [Move.apply] using hSp)
    rw [nxt_same' hm] at h1
    simpa [Move.apply, home_eq] using h1
  | succ j ih =>
    intro hSp
    have hm : mix n low (lay K n S) (cell K n (j + 1) K) = none := by
      rw [mix_high (cell_gt n (j + 1) K), lay_marker]; simp
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.rScan cont), cell K n (j + 1) K, mix n low (lay K n S)⟩)
      (t := (mvTo false K (.rScan cont), none, .left))
      (by simp only; rw [hm]; rfl) (notAcc_base (by intro pc h; cases h)) hSp
      (by simp only [Move.apply]; omega)
    rw [nxt_same' hm] at h1
    simp only [Move.apply] at h1
    have h2 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp) (.rScan cont)
      (mix n low (lay K n S)) K (cell K n (j + 1) K - 1) (by rw [cell_succ]; omega) (by omega)
    rw [show cell K n (j + 1) K - 1 - K = cell K n j K by rw [cell_succ]; omega] at h2
    have h3 := ih (by rw [cell_succ] at hSp; omega)
    exact ((h1.trans h2).trans h3).of_eq (by ring)

/-- **Pushing a bit during the preamble**, from the track of stack `kin` in block `0`, then back
home into the preamble loop. -/
theorem seg_prePush {Sp n : ℕ} (hk : kin < K) (S : Store) (low : ℕ → Sym) (b : Bool)
    (hS0 : (S kin).length = 0 ∨ True) (hSp : cell K n (S kin).length K < Sp) :
    ∃ m ≤ 2 * ((S kin).length + 1) * (K + 1) + 2,
      (simM C K kin).Seg Sp ⟨.base (.scan (.push b) kin none true), cell K n 0 kin,
          mix n low (lay K n S)⟩
        ⟨.base .pre, home K n, mix n low (lay K n (Function.update S kin (b :: S kin)))⟩ m := by
  clear hS0
  have h1 := seg_scanUpT (C := C) (kin := kin) (Sp := Sp) (n := n) S low hk (.push b) none
    (by unfold cell at hSp ⊢; omega) (S kin).length 0 (by simp)
  simp only [decide_true] at h1
  have hb : mix n low (lay K n S) (cell K n (S kin).length kin) = none := by
    rw [mix_high (cell_gt _ _ _), lay_blank S hk]
  have h2 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base (.scan (.push b) kin none (decide ((S kin).length = 0))),
      cell K n (S kin).length kin, mix n low (lay K n S)⟩)
    (t := (mvTo true (K - kin) (.rScan none), some b, .stay))
    (by simp only; rw [hb]; rfl) (notAcc_base (by intro pc h; cases h))
    (show cell K n (S kin).length kin < Sp by unfold cell at hSp ⊢; omega)
    (show cell K n (S kin).length kin < Sp by unfold cell at hSp ⊢; omega)
  simp only [nxt_write, Move.apply] at h2
  rw [update_mix (cell_gt _ _ _), lay_push S hk b] at h2
  set S' := Function.update S kin (b :: S kin)
  have h3 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp) (.rScan none)
    (mix n low (lay K n S')) (K - kin) (cell K n (S kin).length kin)
    (by rw [cell_add, show kin + (K - kin) = K by omega]; exact hSp)
  rw [cell_add, show kin + (K - kin) = K by omega] at h3
  have h4 := seg_rScanT (C := C) (kin := kin) (Sp := Sp) (n := n) S' low none (S kin).length hSp
  refine ⟨_, ?_, ((h1.trans h2).trans h3).trans h4⟩
  have : K - kin ≤ K := by omega
  nlinarith

/-! ### Tapes of the preamble -/

theorem lay_empty (n c : ℕ) :
    lay K n (fun _ => []) c = if c = home K n then some true else none := by
  by_cases hc : c ≤ n
  · rw [lay_low _ hc, if_neg (by unfold home; omega)]
  rw [eq_cell (K := K) (n := n) (by omega : n + 1 ≤ c)]
  set j := (c - (n + 1)) / (K + 1)
  set r := (c - (n + 1)) % (K + 1)
  have hr : r < K + 1 := Nat.mod_lt _ (by omega)
  by_cases hrK : r < K
  · rw [lay_track _ hrK, if_neg]
    · simp
    · unfold home cell; intro h
      rcases Nat.eq_zero_or_pos j with hj | hj
      · rw [hj] at h; simp at h; omega
      · have := Nat.le_mul_of_pos_left (K + 1) hj; omega
  · have hrK' : r = K := by omega
    rw [hrK', lay_marker]
    by_cases hj : j = 0
    · rw [if_pos hj, if_pos (by rw [hj, home_eq])]
    · rw [if_neg hj, if_neg (by unfold home cell; intro h; apply hj; nlinarith)]

theorem pre_erase {n : ℕ} (r₀ : Bool) (rs : List Bool) (S : Store) (h : rs.length + 1 ≤ n) :
    Function.update (preTape K n (r₀ :: rs) S) (n - (rs.length + 1)) none = preTape K n rs S := by
  funext c
  by_cases hc : c = n - (rs.length + 1)
  · subst hc
    rw [Function.update_self]
    unfold preTape mix remLow
    rw [if_pos (by omega), if_pos (by omega)]
  · rw [Function.update_of_ne hc]
    unfold preTape mix remLow
    simp only [List.length_cons]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> first | rfl | omega | skip
    all_goals first
      | (rw [show c + (rs.length + 1) - n = (c + rs.length - n) + 1 by omega]; rfl)
      | omega

theorem start_tape (b₀ : Bool) (xs : List Bool) :
    Function.update (Function.update (fun i => ((b₀ :: xs).map some).getD i none) 0 none)
      (home K (xs.length + 1)) (some true) = preTape K (xs.length + 1) xs (fun _ => []) := by
  funext c
  set n := xs.length + 1
  by_cases hh : c = home K n
  · subst hh
    rw [Function.update_self]
    unfold preTape
    rw [mix_high (home_gt n), lay_empty, if_pos rfl]
  rw [Function.update_of_ne hh]
  by_cases h0 : c = 0
  · subst h0
    rw [Function.update_self]
    unfold preTape mix remLow
    rw [if_pos (by omega), if_pos (by omega)]
  rw [Function.update_of_ne h0]
  unfold preTape mix
  by_cases hcn : c ≤ n
  · rw [if_pos hcn]
    unfold remLow
    rw [if_neg (by omega)]
    by_cases hcn' : c < n
    · rw [if_pos hcn']
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      simp only [List.map_cons, List.getD_cons_succ]
      rw [show c' + 1 + xs.length - n = c' by omega, List.getD_eq_getElem?_getD,
        List.getElem?_map]
      rw [List.getElem?_eq_getElem (by omega)]
      simp
    · rw [if_neg hcn', show c = n by omega]
      simp [List.getD_eq_getElem?_getD, n]
  · rw [if_neg hcn, lay_empty, if_neg hh]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

/-! ### The preamble loop -/

/-- **One round of the preamble loop**: fetch the leftmost remaining input bit and push it. -/
theorem seg_preIter (hk : kin < K) {n : ℕ} (r₀ : Bool) (rs : List Bool) (S : Store)
    (hlen : rs.length + 2 ≤ n) (hH : (S kin).length ≤ n) :
    ∃ m ≤ 5 * (n + 2) * (K + 1),
      (simM C K kin).Seg (n + 2 + (n + 1) * (K + 1))
        ⟨.base .pre, home K n, preTape K n (r₀ :: rs) S⟩
        ⟨.base .pre, home K n, preTape K n rs (Function.update S kin (r₀ :: S kin))⟩ m := by
  obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = n + 2 + (n + 1) * (K + 1) := ⟨_, rfl⟩
  rw [← hSp]
  have hSpK : n + 2 + K ≤ Sp := by rw [hSp]; nlinarith
  have hhome : home K n < Sp := by unfold home; omega
  have hcell : cell K n (S kin).length K < Sp := by rw [hSp]; unfold cell; nlinarith
  -- `pre`: to cell `n - 1`
  have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base .pre, home K n, preTape K n (r₀ :: rs) S⟩)
    (t := (mvTo false (K + 1) .pChk, preTape K n (r₀ :: rs) S (home K n), .left)) rfl
    (notAcc_base (by intro pc h; cases h)) hhome (by simp [Move.apply]; omega)
  rw [nxt_same] at h1
  simp only [Move.apply] at h1
  have h2 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp) .pChk
    (preTape K n (r₀ :: rs) S) (K + 1) (home K n - 1) (by unfold home; omega) (by omega)
  rw [show home K n - 1 - (K + 1) = n - 1 by unfold home; omega] at h2
  -- `pChk`: the last remaining bit
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, preTape K n (r₀ :: rs) S (n - 1) = some c₁ := by
    unfold preTape mix remLow
    simp only [List.length_cons]
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    exact ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
  have h3 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base .pChk, n - 1, preTape K n (r₀ :: rs) S⟩)
    (t := (.base .pSeek, some c₁, .left)) (by simp only [δ]; rw [hc₁]; rfl)
    (notAcc_base (by intro pc h; cases h)) (by dsimp only; omega) (by simp [Move.apply]; omega)
  rw [nxt_same' hc₁] at h3
  simp only [Move.apply] at h3
  -- `pSeek`: to the blank left of the remaining bits
  have h4 := seg_walk_left (C := C) (K := K) (kin := kin) (Sp := Sp) .pSeek
    (by intro pc h; cases h) (fun c => rfl) (preTape K n (r₀ :: rs) S) rs.length (n - 1 - 1)
    (fun e he => by
      unfold preTape mix remLow
      simp only [List.length_cons]
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      exact ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩) (by omega) (by omega)
  have hbl : preTape K n (r₀ :: rs) S (n - 1 - 1 - rs.length) = none := by
    unfold preTape mix remLow
    simp only [List.length_cons]
    rw [if_pos (by omega), if_pos (by omega)]
  have h5 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base .pSeek, n - 1 - 1 - rs.length, preTape K n (r₀ :: rs) S⟩)
    (t := (.base .pTake, none, .right)) (by simp only [δ]; rw [hbl]; rfl)
    (notAcc_base (by intro pc h; cases h)) (by dsimp only; omega) (by simp [Move.apply]; omega)
  rw [nxt_same' hbl] at h5
  simp only [Move.apply] at h5
  rw [show n - 1 - 1 - rs.length + 1 = n - (rs.length + 1) by omega] at h5
  -- `pTake`: erase the bit
  have hr₀ : preTape K n (r₀ :: rs) S (n - (rs.length + 1)) = some r₀ := by
    unfold preTape mix remLow
    simp only [List.length_cons]
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega),
      show n - (rs.length + 1) + (rs.length + 1) - n = 0 by omega]
    rfl
  have h6 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base .pTake, n - (rs.length + 1), preTape K n (r₀ :: rs) S⟩)
    (t := (.base (.pRet r₀), none, .right)) (by simp only [δ]; rw [hr₀]; rfl)
    (notAcc_base (by intro pc h; cases h)) (by dsimp only; omega) (by simp [Move.apply]; omega)
  simp only [nxt_write, Move.apply] at h6
  rw [pre_erase r₀ rs S (by omega)] at h6
  -- `pRet`: back to cell `n`
  have h7 := seg_walk_right (C := C) (K := K) (kin := kin) (Sp := Sp) (.pRet r₀)
    (by intro pc h; cases h) (fun c => rfl) (preTape K n rs S) rs.length
    (n - (rs.length + 1) + 1)
    (fun e he => by
      unfold preTape mix remLow
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩) (by omega)
  rw [show n - (rs.length + 1) + 1 + rs.length = n by omega] at h7
  have hn : preTape K n rs S n = none := by
    unfold preTape mix remLow
    rw [if_pos le_rfl, if_neg (by omega), if_neg (lt_irrefl _)]
  have h8 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base (.pRet r₀), n, preTape K n rs S⟩)
    (t := (mvTo true kin (.scan (.push r₀) kin none true), none, .right))
    (by simp only [δ]; rw [hn]; rfl) (notAcc_base (by intro pc h; cases h)) (by dsimp only; omega)
    (by simp [Move.apply]; omega)
  rw [nxt_same' hn] at h8
  simp only [Move.apply] at h8
  have h9 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp)
    (.scan (.push r₀) kin none true) (preTape K n rs S) kin (n + 1) (by unfold cell at hcell; omega)
  rw [show n + 1 + kin = cell K n 0 kin by unfold cell; ring] at h9
  -- push
  obtain ⟨m₁, hm₁, h10⟩ := seg_prePush (C := C) (Sp := Sp) (n := n) hk S (remLow n rs) r₀
    (Or.inr trivial) hcell
  refine ⟨_, ?_, (((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans
    h8).trans h9).trans h10)⟩
  have : 1 ≤ K := by omega
  nlinarith

/-- **The end of the preamble loop.** -/
theorem seg_preEnd {n : ℕ} (hn : 1 ≤ n) (S : Store) :
    (simM C K kin).Seg (n + 2 + (n + 1) * (K + 1)) ⟨.base .pre, home K n, preTape K n [] S⟩
      (good K n ⟨0, S⟩) (2 * K + 4) := by
  obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = n + 2 + (n + 1) * (K + 1) := ⟨_, rfl⟩
  rw [← hSp]
  have hSpK : n + 2 + K ≤ Sp := by rw [hSp]; nlinarith
  have hhome : home K n < Sp := by unfold home; omega
  have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base .pre, home K n, preTape K n [] S⟩)
    (t := (mvTo false (K + 1) .pChk, preTape K n [] S (home K n), .left)) rfl
    (notAcc_base (by intro pc h; cases h)) hhome (by simp [Move.apply]; omega)
  rw [nxt_same] at h1
  simp only [Move.apply] at h1
  have h2 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp) .pChk
    (preTape K n [] S) (K + 1) (home K n - 1) (by unfold home; omega) (by omega)
  rw [show home K n - 1 - (K + 1) = n - 1 by unfold home; omega] at h2
  have hb : preTape K n [] S (n - 1) = none := by
    unfold preTape mix remLow
    rw [if_pos (by omega), if_pos (by simp; omega)]
  have h3 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base .pChk, n - 1, preTape K n [] S⟩)
    (t := (mvTo true (K + 1) (.exec 0), none, .right)) (by simp only [δ]; rw [hb]; rfl)
    (notAcc_base (by intro pc h; cases h)) (by dsimp only; omega) (by simp [Move.apply]; omega)
  rw [nxt_same' hb] at h3
  simp only [Move.apply] at h3
  have h4 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp) (.exec 0)
    (preTape K n [] S) (K + 1) (n - 1 + 1) (show n - 1 + 1 + (K + 1) < Sp by unfold home at hhome; omega)
  rw [show n - 1 + 1 + (K + 1) = home K n by unfold home; omega, preTape_nil] at h4
  rw [preTape_nil] at h1 h2 h3
  have := ((h1.trans h2).trans h3).trans h4
  rw [preTape_nil]
  exact this.of_eq (by omega : 1 + (K + 1) + 1 + (K + 1) = 2 * K + 4)

theorem inStore_snoc (p : List Bool) (r₀ : Bool) :
    Function.update (inStore kin p) kin (r₀ :: inStore kin p kin) = inStore kin (p ++ [r₀]) := by
  unfold inStore; simp

/-- **The preamble loop.** -/
theorem seg_preLoop (hk : kin < K) (x : List Bool) :
    ∀ rem p, p ≠ [] → p ++ rem = x →
      ∃ m ≤ (rem.length + 1) * (5 * (x.length + 2) * (K + 1)),
        (simM C K kin).Seg (x.length + 2 + (x.length + 1) * (K + 1))
          ⟨.base .pre, home K x.length, preTape K x.length rem (inStore kin p)⟩
          (good K x.length ⟨0, inStore kin x⟩) m := by
  intro rem
  induction rem with
  | nil =>
    intro p hp hx
    simp only [List.append_nil] at hx
    subst hx
    have hn : 1 ≤ p.length := List.length_pos_of_ne_nil hp
    refine ⟨_, ?_, seg_preEnd (C := C) (kin := kin) hn (inStore kin p)⟩
    simp only [List.length_nil, zero_add, one_mul]; nlinarith
  | cons r₀ rs ih =>
    intro p hp hx
    have hn : (p ++ r₀ :: rs).length = p.length + rs.length + 1 := by simp; omega
    have hp1 : 1 ≤ p.length := List.length_pos_of_ne_nil hp
    obtain ⟨m₁, hm₁, h1⟩ := seg_preIter (C := C) (n := x.length) hk r₀ rs (inStore kin p)
      (by rw [← hx, hn]; omega) (by unfold inStore; simp; rw [← hx]; simp)
    rw [inStore_snoc] at h1
    obtain ⟨m₂, hm₂, h2⟩ := ih (p ++ [r₀]) (by simp) (by rw [← hx]; simp)
    refine ⟨_, ?_, h1.trans h2⟩
    simp only [List.length_cons]
    nlinarith

/-- **The preamble.** -/
theorem sim_pre (hk : kin < K) (x : List Bool) :
    ∃ m ≤ (x.length + 1) * (6 * (x.length + 2) * (K + 1)),
      (simM C K kin).Seg (x.length + 2 + (x.length + 1) * (K + 1))
        ((simM C K kin).initConfig (x.map some)) (good K x.length ⟨0, inStore kin x⟩) m := by
  obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = x.length + 2 + (x.length + 1) * (K + 1) := ⟨_, rfl⟩
  rw [← hSp]
  have hSpK : x.length + 2 + K ≤ Sp := by rw [hSp]; nlinarith
  have hhome : home K x.length < Sp := by unfold home; omega
  rcases x with _ | ⟨b₀, xs⟩
  · -- empty input
    have h0 : ((simM C K kin).initConfig (([] : List Bool).map some)).tape 0 = none := rfl
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := (simM C K kin).initConfig (([] : List Bool).map some))
      (t := (mvTo true K (.pMark none), none, .right)) rfl
      (notAcc_base (by intro pc h; cases h)) (by simp [NTM.initConfig]; omega)
      (by simp [NTM.initConfig, Move.apply]; omega)
    rw [nxt_same' h0] at h1
    simp only [NTM.initConfig, Move.apply] at h1
    have h2 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp) (.pMark none)
      (fun i => (([] : List Bool).map some).getD i none) K (0 + 1) (by unfold home at hhome; simp at hhome ⊢; omega)
    have h3 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.pMark none), 0 + 1 + K, fun i => (([] : List Bool).map some).getD i none⟩)
      (t := (.base (.exec 0), some true, .stay)) rfl
      (notAcc_base (by intro pc h; cases h)) (by unfold home at hhome; simp at hhome ⊢; omega)
      (by unfold home at hhome; simp [Move.apply] at hhome ⊢; omega)
    simp only [nxt_write, Move.apply] at h3
    have htape : Function.update (fun i => (([] : List Bool).map some).getD i none) (0 + 1 + K)
        (some true) = lay K 0 (inStore kin []) := by
      have : inStore kin [] = fun _ => [] := by unfold inStore; simp
      rw [this]
      funext c
      rw [lay_empty]
      by_cases hc : c = home K 0
      · rw [if_pos hc, hc, show home K 0 = 0 + 1 + K by unfold home; rfl, Function.update_self]
      · rw [if_neg hc, Function.update_of_ne (by unfold home at hc; omega)]; rfl
    rw [htape] at h3
    refine ⟨_, ?_, ((h1.trans h2).trans h3).of_eq rfl⟩
    simp only [List.length_nil]; nlinarith
  · -- the first bit
    set n := xs.length + 1
    have hlen : (b₀ :: xs).length = n := rfl
    rw [hlen] at hhome ⊢
    have h0 : ((simM C K kin).initConfig ((b₀ :: xs).map some)).tape 0 = some b₀ := rfl
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := (simM C K kin).initConfig ((b₀ :: xs).map some))
      (t := (.base (.pEnd b₀), none, .right)) rfl
      (notAcc_base (by intro pc h; cases h)) (by simp [NTM.initConfig]; omega)
      (by simp [NTM.initConfig, Move.apply]; omega)
    simp only [nxt_write, NTM.initConfig, Move.apply] at h1
    set t₁ := Function.update (fun i => ((b₀ :: xs).map some).getD i none) 0 none
    have h2 := seg_walk_right (C := C) (K := K) (kin := kin) (Sp := Sp) (.pEnd b₀)
      (by intro pc h; cases h) (fun c => rfl) t₁ xs.length (0 + 1)
      (fun e he => ⟨xs[e], by
        simp only [t₁]
        rw [Function.update_of_ne (by omega)]
        simp only [List.map_cons, show 0 + 1 + e = e + 1 by omega, List.getD_cons_succ]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem he]
        rfl⟩) (by unfold home at hhome; omega)
    have hn : t₁ (0 + 1 + xs.length) = none := by
      simp only [t₁]
      rw [Function.update_of_ne (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp)]
      rfl
    have h3 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.pEnd b₀), 0 + 1 + xs.length, t₁⟩)
      (t := (mvTo true K (.pMark (some b₀)), none, .right)) (by simp only [δ]; rw [hn]; try rfl)
      (notAcc_base (by intro pc h; cases h)) (by dsimp only; unfold home at hhome; omega)
      (by simp [Move.apply]; unfold home at hhome; omega)
    rw [nxt_same' hn] at h3
    simp only [Move.apply] at h3
    have h4 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp) (.pMark (some b₀)) t₁ K
      (0 + 1 + xs.length + 1) (by unfold home at hhome; omega)
    rw [show 0 + 1 + xs.length + 1 + K = home K n by unfold home; omega] at h4
    have h5 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.pMark (some b₀)), home K n, t₁⟩)
      (t := (mvTo false (K - kin - 1) (.scan (.push b₀) kin none true), some true, .left)) rfl
      (notAcc_base (by intro pc h; cases h)) hhome (by simp [Move.apply]; omega)
    simp only [nxt_write, Move.apply] at h5
    rw [start_tape b₀ xs] at h5
    have h6 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp)
      (.scan (.push b₀) kin none true) (preTape K n xs (fun _ => [])) (K - kin - 1) (home K n - 1)
      (by unfold home; omega) (by omega)
    rw [show home K n - 1 - (K - kin - 1) = cell K n 0 kin by unfold home cell; omega] at h6
    obtain ⟨m₁, hm₁, h7⟩ := seg_prePush (C := C) (Sp := Sp) (n := n) hk (fun _ => [])
      (remLow n xs) b₀ (Or.inr trivial) (by unfold cell; simp; nlinarith)
    have hst : Function.update (fun _ : ℕ => ([] : List Bool)) kin [b₀] = inStore kin [b₀] := by
      unfold inStore; simp
    simp only [List.length_nil] at hm₁
    rw [hst] at h7
    obtain ⟨m₂, hm₂, h8⟩ := seg_preLoop (C := C) hk (b₀ :: xs) xs [b₀] (by simp) rfl
    rw [hlen] at h8 hm₂
    rw [show n + 2 + (n + 1) * (K + 1) = Sp by rw [hSp, hlen]] at h8
    refine ⟨_, ?_, (((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans
      h8)⟩
    have hxs : xs.length + 1 = n := rfl
    rw [hxs] at hm₂
    have hP1 : 2 * (K + 1) ≤ (n + 2) * (K + 1) := Nat.mul_le_mul_right _ (by omega)
    have hP2 : n + 2 ≤ (n + 2) * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have e1 : (n + 1) * (6 * (n + 2) * (K + 1)) = n * (5 * (n + 2) * (K + 1)) +
        n * ((n + 2) * (K + 1)) + 6 * ((n + 2) * (K + 1)) := by ring
    rw [e1]
    omega

end Mach

end HTN
