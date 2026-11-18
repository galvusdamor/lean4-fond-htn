import ComplexityTheory.Machine.SDec
/-!
# Realizing exponential iteration with bounded stacks

`HTN.Mach.srealizer_loop`: from a space realizer of `F` and a polynomial bound `qb` on all results
of the iteration `HTN.PSpace.loopFn F`, a space realizer of `loopFn F` — the state updated
`val s` times by `F`, `s` being the first argument read as a binary numeral.

The program copies the counter `s` to the stack `C` and the state to the stack `Z`, and then
repeats: decrement `C` (`HTN.Mach.decP`); if it was `0`, stop; otherwise apply `F` to `Z`.  The
stacks stay polynomial: `C` and the borrow stack `D` hold at most `|s|` bits, and every
intermediate state is the result of the iteration for a smaller counter of the same length, hence
bounded by `qb`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog PSpace

noncomputable section

/-- Iterating `F` once more, at the front. -/
theorem loopAux_succ' (F : Fn) (rest : Args) (n : ℕ) (st : List Bool) :
    loopAux F rest (n + 1) st = loopAux F rest n (F (st :: rest)) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => rw [loopAux_succ, ih, loopAux_succ]

section Loop

variable {F : Fn} (RF : SRealizer F)

/-- The stacks of the loop, relative to the base `b`. -/
def lC (b : ℕ) : ℕ := b
def lD (b : ℕ) : ℕ := b + 1
def lG (b : ℕ) : ℕ := b + 2
def lFL (b : ℕ) : ℕ := b + 3
def lG2 (b : ℕ) : ℕ := b + 4
def lZ (b : ℕ) : ℕ := b + 5
def lT (b : ℕ) : ℕ := b + 6
def lU (b : ℕ) : ℕ := b + 7

/-- The input stacks of `F`: the state, then the remaining arguments. -/
def lInp (inp : ℕ → ℕ) (b : ℕ) : ℕ → ℕ := fun i => if i = 0 then lZ b else inp (i + 1)

/-- Applying `F` to the state. -/
def applyP (inp : ℕ → ℕ) (b : ℕ) : Prog :=
  seq (RF.P (lInp inp b) (lT b) (b + 8)) (seq (clear (lZ b)) (seq (moveRev (lT b) (lU b))
    (moveRev (lU b) (lZ b))))

/-- One round of the loop. -/
def loopBody (inp : ℕ → ℕ) (b : ℕ) : Prog :=
  seq (decP (lC b) (lD b) (lG b) (lFL b))
    (ifTop (lFL b) (seq (clear (lD b)) (pop (lG2 b))) skip
      (seq (pop (lFL b)) (seq (restoreP (lC b) (lD b)) (applyP RF inp b))))

/-- The program of the iteration. -/
def loopProg (inp : ℕ → ℕ) (out b : ℕ) : Prog :=
  seq (copy (inp 0) (lC b) (lU b)) (seq (copy (inp 1) (lZ b) (lU b)) (seq (push (lG2 b) true)
    (seq (loop (lG2 b) (loopBody RF inp b)) (seq (moveRev (lZ b) (lU b)) (moveRev (lU b) out)))))

end Loop

theorem EvalH.congr_end {h : ℕ} {p : Prog} {S S' S'' : Store} (e : EvalH h p S S') (hS : S' = S'') :
    EvalH h p S S'' := hS ▸ e

/-! ### The loop body -/

/-- The store at the head of the loop. -/
def LS (S : Store) (b : ℕ) (c z g2 : List Bool) : Store :=
  Function.update (Function.update (Function.update S (lC b) c) (lZ b) z) (lG2 b) g2

section LSlemmas

variable {S : Store} {b : ℕ}

theorem ls_C (c z g2 : List Bool) : LS S b c z g2 (lC b) = c := by simp [LS, lC, lZ, lG2]
theorem ls_Z (c z g2 : List Bool) : LS S b c z g2 (lZ b) = z := by simp [LS, lC, lZ, lG2]
theorem ls_G2 (c z g2 : List Bool) : LS S b c z g2 (lG2 b) = g2 := by simp [LS, lC, lZ, lG2]
theorem ls_other (c z g2 : List Bool) {j : ℕ} (h1 : j ≠ lC b) (h2 : j ≠ lZ b) (h3 : j ≠ lG2 b) :
    LS S b c z g2 j = S j := by
  simp [LS, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

theorem hb_ls {h₀ : ℕ} (hb : HB h₀ S) {c z g2 : List Bool} {m : ℕ} (hcm : c.length ≤ m)
    (hzm : z.length ≤ m) (hg : g2.length ≤ m) : HB (h₀ + m) (LS S b c z g2) :=
  (((hb.mono (by omega)).update (by omega)).update (by omega)).update (by omega)

end LSlemmas

section Body2

variable {F : Fn} (RF : SRealizer F) {inp : ℕ → ℕ} {b : ℕ} {S : Store}
  (hinp : ∀ i < RF.A + 2, inp i < b) (hc : Clean b S)
include hinp hc

/-- The remaining arguments of the iteration. -/
def restOf (RF : SRealizer F) (inp : ℕ → ℕ) (S : Store) : Args :=
  (argsOf (RF.A + 2) inp S).tail.tail

theorem f_apply {z : List Bool} {S' : Store} (hZ : S' (lZ b) = z)
    (hrest : ∀ i < RF.A + 2, S' (inp i) = S (inp i)) :
    F (argsOf RF.A (lInp inp b) S') = F (z :: restOf RF inp S) := by
  refine (RF.reads.congr fun i hi => ?_).trans (RF.reads _).symm
  rw [getD_argsOf hi, CobhamTM.getD_padArgs hi]
  rcases i with _ | i
  · simp [lInp, hZ]
  · simp only [lInp, show i + 1 ≠ 0 by omega, if_false]
    rw [hrest _ (by omega)]
    simp only [restOf, argsOf, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_tail, List.getElem?_tail, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl

/-- **The last round**: the counter is `0`. -/
theorem body_zero {k : ℕ} {z : List Bool} {h₀ M : ℕ} (hb : HB h₀ S) (hk : k ≤ M)
    (hz : z.length ≤ M) :
    EvalH (h₀ + 8 * M + 10) (loopBody RF inp b)
      (LS S b (List.replicate k false) z [true]) (LS S b [] z []) := by
  have hL : HB (h₀ + (M + 1)) (LS S b (List.replicate k false) z [true]) :=
    hb_ls (m := M + 1) hb (by simp; omega) (by omega) (by simp)
  have hLD : LS S b (List.replicate k false) z [true] (lD b) = [] := by
    rw [ls_other] <;> simp [lD, lC, lZ, lG2]; exact hc _ (by omega)
  have hLG : LS S b (List.replicate k false) z [true] (lG b) = [] := by
    rw [ls_other] <;> simp [lG, lC, lZ, lG2]; exact hc _ (by omega)
  have hLF : LS S b (List.replicate k false) z [true] (lFL b) = [] := by
    rw [ls_other] <;> simp [lFL, lC, lZ, lG2]; exact hc _ (by omega)
  obtain ⟨t₁, ht₁, e₁⟩ := dec_zero (C := lC b) (D := lD b) (G := lG b) (FL := lFL b)
    (by simp [lC, lD]) (by simp [lC, lG]) (by simp [lC, lFL]) (by simp [lD, lG]) (by simp [lD, lFL])
    (by simp [lG, lFL]) (ls_C _ _ _) hLG
  rw [hLD, List.append_nil] at e₁
  have h₁ := evalH_of_eval e₁ hL
  obtain ⟨t₂, ht₂, e₂⟩ := runs_clear (lD b) (Function.update (Function.update
    (LS S b (List.replicate k false) z [true]) (lC b) []) (lD b) (List.replicate k true))
  have h₂ := evalH_of_eval e₂ h₁.hb_end
  have h₃ := EvalH.pop (k := lG2 b) h₂.hb_end
  have hF₁ : Function.update (Function.update (LS S b (List.replicate k false) z [true]) (lC b) [])
      (lD b) (List.replicate k true) (lFL b) = [] := by
    rw [Function.update_of_ne (by simp [lFL, lD]), Function.update_of_ne (by simp [lFL, lC])]
    exact hLF
  have hfin : ∀ X : Store, X = Function.update (Function.update (Function.update
      (LS S b (List.replicate k false) z [true]) (lC b) []) (lD b) (List.replicate k true)) (lD b) [] →
      Function.update X (lG2 b) (X (lG2 b)).tail = LS S b [] z [] := by
    rintro X rfl
    have hb1 : S (b + 1) = [] := hc _ (by omega)
    funext j
    simp only [LS, Function.update_apply, lC, lD, lZ, lG2]
    split_ifs <;> simp_all
  rw [hfin _ rfl] at h₃
  simp only [Function.update_self, List.length_replicate] at ht₂
  exact .seq (h₁.mono (by omega)) (.ifNil hF₁ (.seq (h₂.mono (by omega)) (h₃.mono (by omega))))

/-- **A round with a positive counter**: decrement it and apply `F` to the state. -/
theorem body_pos {k : ℕ} {r z : List Bool} {h₀ M : ℕ} (hb : HB h₀ S)
    (hk : k + 1 + r.length ≤ M) (hz : z.length ≤ M)
    (hFz : (F (z :: restOf RF inp S)).length ≤ M) (hin : ∀ i < RF.A + 2, (S (inp i)).length ≤ M) :
    EvalH (h₀ + 20 * M + 20 + RF.space.eval M) (loopBody RF inp b)
      (LS S b (List.replicate k false ++ true :: r) z [true])
      (LS S b (List.replicate k true ++ false :: r) (F (z :: restOf RF inp S)) [true]) := by
  set c := List.replicate k false ++ true :: r
  have hcl : c.length ≤ M := by simp [c]; omega
  have hL : HB (h₀ + (M + 1)) (LS S b c z [true]) := hb_ls (m := M + 1) hb (by omega) (by omega) (by simp)
  have hLD : LS S b c z [true] (lD b) = [] := by
    rw [ls_other] <;> simp [lD, lC, lZ, lG2]; exact hc _ (by omega)
  have hLG : LS S b c z [true] (lG b) = [] := by
    rw [ls_other] <;> simp [lG, lC, lZ, lG2]; exact hc _ (by omega)
  have hLF : LS S b c z [true] (lFL b) = [] := by
    rw [ls_other] <;> simp [lFL, lC, lZ, lG2]; exact hc _ (by omega)
  have hb3 : S (b + 3) = [] := hc _ (by omega)
  have hb1 : S (b + 1) = [] := hc _ (by omega)
  have hb6 : S (b + 6) = [] := hc _ (by omega)
  have hb7 : S (b + 7) = [] := hc _ (by omega)
  -- decrement
  obtain ⟨t₁, ht₁, e₁⟩ := dec_pos (C := lC b) (D := lD b) (G := lG b) (FL := lFL b)
    (by simp [lC, lD]) (by simp [lC, lG]) (by simp [lC, lFL]) (by simp [lD, lG]) (by simp [lD, lFL])
    (by simp [lG, lFL]) (ls_C _ _ _) hLG
  rw [hLD, hLF, List.append_nil] at e₁
  have h₁ := evalH_of_eval e₁ hL
  set S₁ := Function.update (Function.update (Function.update (LS S b c z [true]) (lC b) (false :: r))
    (lD b) (List.replicate k true)) (lFL b) [true]
  have hS₁F : S₁ (lFL b) = true :: [] := by simp [S₁]
  -- pop the flag
  have h₂ := EvalH.pop (k := lFL b) h₁.hb_end
  set S₂ := Function.update S₁ (lFL b) (S₁ (lFL b)).tail
  have hS₂D : S₂ (lD b) = List.replicate k true := by simp [S₂, S₁, lD, lFL]
  -- restore the counter
  obtain ⟨t₃, ht₃, e₃⟩ := restore_loop (C := lC b) (D := lD b) (by simp [lC, lD]) k S₂ hS₂D
  have h₃ := evalH_of_eval e₃ h₂.hb_end
  set S₃ := Function.update (Function.update S₂ (lD b) []) (lC b) (List.replicate k true ++ S₂ (lC b))
  -- apply `F`
  have hS₃Z : S₃ (lZ b) = z := by
    have := ls_Z (S := S) (b := b) c z [true]
    simp only [lZ] at this
    simp [S₃, S₂, S₁, lZ, lC, lD, lFL, this]
  have hS₃in : ∀ i < RF.A + 2, S₃ (inp i) = S (inp i) := by
    intro i hi
    have := hinp i hi
    simp only [S₃, S₂, S₁]
    rw [Function.update_of_ne (by simp [lC]; omega), Function.update_of_ne (by simp [lD]; omega),
      Function.update_of_ne (by simp [lFL]; omega), Function.update_of_ne (by simp [lFL]; omega),
      Function.update_of_ne (by simp [lD]; omega), Function.update_of_ne (by simp [lC]; omega),
      ls_other _ _ _ (by simp [lC]; omega) (by simp [lZ]; omega) (by simp [lG2]; omega)]
  have hS₃T : S₃ (lT b) = [] := by simp [S₃, S₂, S₁, lT, lC, lD, lFL, LS, lZ, lG2, hb6]
  have hS₃c : Clean (b + 8) S₃ := fun j hj => by
    simp only [S₃, S₂, S₁, LS]
    rw [Function.update_of_ne (by simp [lC]; omega), Function.update_of_ne (by simp [lD]; omega),
      Function.update_of_ne (by simp [lFL]; omega), Function.update_of_ne (by simp [lFL]; omega),
      Function.update_of_ne (by simp [lD]; omega), Function.update_of_ne (by simp [lC]; omega),
      Function.update_of_ne (by simp [lG2]; omega), Function.update_of_ne (by simp [lZ]; omega),
      Function.update_of_ne (by simp [lC]; omega)]
    exact hc j (by omega)
  have h₄ := RF.spec (lInp inp b) (lT b) (b + 8) S₃ _
    (fun i hi => by unfold lInp; split_ifs <;> [simp [lZ]; (have := hinp (i + 1) (by omega); omega)])
    (by simp [lT]) (fun i hi => by unfold lInp; split_ifs <;> [simp [lZ, lT];
      (have := hinp (i + 1) (by omega); simp [lT]; omega)]) hS₃T hS₃c h₃.hb_end
  rw [f_apply RF hinp hc hS₃Z hS₃in] at h₄
  have hsz : argSize (argsOf RF.A (lInp inp b) S₃) ≤ M := by
    refine argSize_le_of fun x hx => ?_
    simp only [argsOf, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    unfold lInp
    split_ifs
    · rw [hS₃Z]; exact hz
    · rw [hS₃in _ (by omega)]; exact hin _ (by omega)
  set FZ := F (z :: restOf RF inp S)
  obtain ⟨t₅, ht₅, e₅⟩ := runs_clear (lZ b) (Function.update S₃ (lT b) FZ)
  have h₅ := evalH_of_eval e₅ h₄.hb_end
  obtain ⟨t₆, ht₆, e₆⟩ := runs_moveRev (show lT b ≠ lU b by simp [lT, lU])
    (Function.update (Function.update S₃ (lT b) FZ) (lZ b) [])
  have h₆ := evalH_of_eval e₆ h₅.hb_end
  obtain ⟨t₇, ht₇, e₇⟩ := runs_moveRev (show lU b ≠ lZ b by simp [lU, lZ])
    (Function.update (Function.update (Function.update (Function.update S₃ (lT b) FZ) (lZ b) []) (lT b) [])
      (lU b) (((Function.update (Function.update S₃ (lT b) FZ) (lZ b) []) (lT b)).reverse ++
        (Function.update (Function.update S₃ (lT b) FZ) (lZ b) []) (lU b)))
  have h₇ := evalH_of_eval e₇ h₆.hb_end
  replace h₇ := h₇.congr_end (S'' := LS S b (List.replicate k true ++ false :: r) FZ [true]) (by
    funext j
    simp only [lC, lD, lFL, lZ, lG2, lT, lU] at *
    rcases eq_or_ne j b with rfl | h0
    · simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, hb1, hb3, hb6, hb7]
    rcases eq_or_ne j (b + 1) with rfl | h1
    · simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, hb1]
    rcases eq_or_ne j (b + 3) with rfl | h3
    · simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, hb3]
    rcases eq_or_ne j (b + 4) with rfl | h4
    · simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, hb1, hb3, hb6, hb7]
    rcases eq_or_ne j (b + 5) with rfl | h5
    · simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, hb1, hb3, hb6, hb7]
    rcases eq_or_ne j (b + 6) with rfl | h6
    · simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, hb6]
    rcases eq_or_ne j (b + 7) with rfl | h7
    · simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, hb7]
    simp [S₃, S₂, S₁, LS, lC, lD, lFL, lZ, lG2, lT, lU, Function.update_of_ne, h0, h1, h3, h4, h5,
      h6, h7])
  -- bounds
  have e1 := Polynomial.eval_mono_nat RF.space hsz
  have hU3 : S₃ (lU b) = [] := by simp [S₃, S₂, S₁, lU, lC, lD, lFL, LS, lZ, lG2, hb7]
  have hX5 : (Function.update S₃ (lT b) FZ) (lZ b) = z := by
    rw [Function.update_of_ne (by simp [lZ, lT])]; exact hS₃Z
  have hX6 : (Function.update (Function.update S₃ (lT b) FZ) (lZ b) []) (lT b) = FZ := by
    rw [Function.update_of_ne (by simp [lZ, lT]), Function.update_self]
  have hX6' : (Function.update (Function.update S₃ (lT b) FZ) (lZ b) []) (lU b) = [] := by
    rw [Function.update_of_ne (by simp [lZ, lU]), Function.update_of_ne (by simp [lT, lU])]; exact hU3
  rw [hX5] at ht₅
  rw [hX6] at ht₆
  rw [Function.update_self, hX6, hX6'] at ht₇
  simp only [List.length_append, List.length_reverse, List.length_nil, add_zero] at ht₇
  refine .seq (h₁.mono ?_) (.ifT (r := []) hS₁F (.seq (h₂.mono ?_) (.seq (h₃.mono ?_)
    (.seq (h₄.mono ?_) (.seq (h₅.mono ?_) (.seq (h₆.mono ?_) (h₇.mono ?_))))))) <;> omega


/-- **The loop**, by induction on the value of the counter. -/
theorem iter_run {h₀ M : ℕ} (hb : HB h₀ S) (hin : ∀ i < RF.A + 2, (S (inp i)).length ≤ M) :
    ∀ v (c z : List Bool), val c = v → c.length ≤ M → z.length ≤ M →
      (∀ j, 1 ≤ j → j ≤ v → (loopAux F (restOf RF inp S) j z).length ≤ M) →
      EvalH (h₀ + 20 * M + 20 + RF.space.eval M) (loop (lG2 b) (loopBody RF inp b))
        (LS S b c z [true]) (LS S b [] (loopAux F (restOf RF inp S) v z) []) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro c z hv hcl hz hit
    rcases falses_or_true c with ⟨k, rfl⟩ | ⟨k, r, rfl⟩
    · rw [val_replicate_false] at hv
      subst hv
      have h1 := body_zero RF hinp hc (z := z) (k := k) (M := M) hb (by simpa using hcl) hz
      exact .loopCons (by simp [ls_G2]) (h1.mono (by omega))
        (.loopNil ((hb_ls (m := M) hb (by simp) hz (by simp)).mono (by omega)) (by simp [ls_G2]))
    · have hv' := val_dec k r
      rw [hv] at hv'
      have hF1 : (F (z :: restOf RF inp S)).length ≤ M := by
        have := hit 1 le_rfl (by omega)
        simpa using this
      have h1 := body_pos RF hinp hc (z := z) (k := k) (r := r) (M := M) hb
        (by simp at hcl; omega) hz hF1 hin
      have h2 := ih (v - 1) (by omega) (List.replicate k true ++ false :: r) (F (z :: restOf RF inp S))
        (by omega) (by simp at hcl ⊢; omega) hF1 (fun j hj1 hj2 => by
          rw [← loopAux_succ']; exact hit (j + 1) (by omega) (by omega))
      rw [← loopAux_succ', show v - 1 + 1 = v by omega] at h2
      exact .loopCons (by simp [ls_G2]) (h1.mono (by omega)) h2

end Body2

/-! ### The realizer of the iteration -/

theorem loopAux_congr {F : Fn} {A : ℕ} (hF : ReadsFirst A F) {rest rest' : Args}
    (h : ∀ i < A, rest.getD i [] = rest'.getD i []) :
    ∀ n st, loopAux F rest n st = loopAux F rest' n st := by
  intro n
  induction n with
  | zero => intro st; rfl
  | succ n ih =>
    intro st
    rw [loopAux_succ, loopAux_succ, ih]
    exact hF.congr fun i hi => by
      rcases i with _ | i
      · rfl
      · simp only [List.getD_cons_succ]; exact h i (by omega)

theorem readsFirst_loopFn {F : Fn} {A : ℕ} (hF : ReadsFirst A F) : ReadsFirst (A + 2) (loopFn F) := by
  intro args
  simp only [loopFn]
  rw [CobhamTM.getD_padArgs (by omega), CobhamTM.getD_padArgs (by omega),
    show A + 2 = A + 1 + 1 from rfl, padArgs_succ_tail, padArgs_succ_tail]
  exact loopAux_congr hF (fun i hi => by rw [CobhamTM.getD_padArgs hi]) _ _

theorem argsOf_eq_cons {A : ℕ} (inp : ℕ → ℕ) (S : Store) :
    argsOf (A + 2) inp S = S (inp 0) :: S (inp 1) :: (argsOf (A + 2) inp S).tail.tail := by
  simp [argsOf, List.range_succ_eq_map]

set_option maxHeartbeats 2000000 in
theorem loopProg_bound {F : Fn} (RF : SRealizer F) {inp : ℕ → ℕ} {out b : ℕ}
    (hinp : ∀ i < RF.A + 2, inp i < b) (hout : out < b) :
    maxStack (loopProg RF inp out b) ≤ b + (8 + RF.W) := by
    have hR := RF.bound (lInp inp b) (lT b) (b + 8)
      (fun i hi => by unfold lInp; split_ifs <;> [simp [lZ]; (have := hinp (i + 1) (by omega); omega)])
      (by simp [lT])
    have h0 := hinp 0 (by omega)
    have h1 := hinp 1 (by omega)
    have eC : lC b = b := rfl
    have eD : lD b = b + 1 := rfl
    have eG : lG b = b + 2 := rfl
    have eF : lFL b = b + 3 := rfl
    have eG2 : lG2 b = b + 4 := rfl
    have eZ : lZ b = b + 5 := rfl
    have eT : lT b = b + 6 := rfl
    have eU : lU b = b + 7 := rfl
    have hd : maxStack (decP (lC b) (lD b) (lG b) (lFL b)) ≤ b + 3 := by
      simp only [decP, decBody, maxStack]; omega
    have hr : maxStack (restoreP (lC b) (lD b)) ≤ b + 1 := by
      simp only [restoreP, maxStack]; omega
    have ha : maxStack (applyP RF inp b) ≤ b + 8 + RF.W := by
      simp only [applyP, maxStack, maxStack_clear, maxStack_moveRev]
      omega
    have hbody : maxStack (loopBody RF inp b) ≤ b + 8 + RF.W := by
      simp only [loopBody, maxStack, maxStack_clear]
      omega
    simp only [loopProg, maxStack, maxStack_copy, maxStack_moveRev]
    omega

/-- **Exponential iteration with bounded stacks.** -/
def srealizer_loop {F : Fn} (RF : SRealizer F) (qb : Polynomial ℕ)
    (hqb : ∀ args, (loopFn F args).length ≤ qb.eval (argSize args)) : SRealizer (loopFn F) where
  A := RF.A + 2
  P inp out b := loopProg RF inp out b
  W := 8 + RF.W
  space := 30 * Polynomial.X + 28 * qb + 30 + RF.space.comp (Polynomial.X + qb)
  reads := readsFirst_loopFn RF.reads
  bound inp out b hinp hout := loopProg_bound RF hinp hout
  spec inp out b S h₀ hinp hout hne hS hc hb := by
    set args := argsOf (RF.A + 2) inp S
    set n := argSize args
    set rest := restOf RF inp S
    set s₀ := S (inp 0)
    set st := S (inp 1)
    have hin : ∀ i < RF.A + 2, (S (inp i)).length ≤ n := fun i hi => length_le_argSize_argsOf hi inp S
    have hargs : args = s₀ :: st :: rest := argsOf_eq_cons inp S
    set M := n + qb.eval n
    -- the iterates stay below `qb n`
    have hit : ∀ j, 1 ≤ j → j ≤ val s₀ → (loopAux F rest j st).length ≤ M := by
      intro j _ hj
      obtain ⟨s', hs'l, hs'v⟩ := exists_val_eq s₀.length j
        (lt_of_le_of_lt hj (val_lt_two_pow s₀))
      have := hqb (s' :: st :: rest)
      rw [loopFn_apply, hs'v] at this
      have hsz : argSize (s' :: st :: rest) = n := by
        rw [show n = argSize args from rfl, hargs, argSize_cons, argSize_cons, argSize_cons,
          argSize_cons, hs'l]
      rw [hsz] at this
      omega
    have hS0 : s₀.length ≤ n := hin 0 (by omega)
    have hS1 : st.length ≤ n := hin 1 (by omega)
    -- copy the counter and the state
    have hbC : S (lC b) = [] := hc _ (by simp [lC])
    have hbU : S (lU b) = [] := hc _ (by simp [lU])
    have hbZ : S (lZ b) = [] := hc _ (by simp [lZ])
    have hbG2 : S (lG2 b) = [] := hc _ (by simp [lG2])
    have hbU' : S (b + 7) = [] := hbU
    have h0 := hinp 0 (by omega)
    have h1 := hinp 1 (by omega)
    obtain ⟨t₁, ht₁, e₁⟩ := runs_copy (src := inp 0) (dst := lC b) (tmp := lU b)
      (by simp [lC]; omega) (by simp [lU]; omega) (by simp [lC, lU]) S hbU
    rw [hbC, List.append_nil] at e₁
    have h₁ := evalH_of_eval e₁ hb
    obtain ⟨t₂, ht₂, e₂⟩ := runs_copy (src := inp 1) (dst := lZ b) (tmp := lU b)
      (by simp [lZ]; omega) (by simp [lU]; omega) (by simp [lZ, lU]) (Function.update S (lC b) s₀)
      (by rw [Function.update_of_ne (by simp [lC, lU])]; exact hbU)
    rw [Function.update_of_ne (by simp [lC]; omega), Function.update_of_ne (by simp [lC, lZ]),
      hbZ, List.append_nil] at e₂
    have h₂ := evalH_of_eval e₂ h₁.hb_end
    have h₃ := EvalH.push (k := lG2 b) (b := true) (h₂.hb_end.mono (Nat.le_succ _))
      ((Eval.push (lG2 b) true _).hb h₂.hb_end)
    have hLS : Function.update (Function.update (Function.update S (lC b) s₀) (lZ b) st) (lG2 b)
        (true :: Function.update (Function.update S (lC b) s₀) (lZ b) st (lG2 b)) = LS S b s₀ st [true] := by
      rw [Function.update_of_ne (by simp [lZ, lG2]), Function.update_of_ne (by simp [lC, lG2]), hbG2]
      rfl
    rw [hLS] at h₃
    -- the loop
    have h₄ := iter_run RF hinp hc (h₀ := h₀) (M := M) hb (fun i hi => (hin i hi).trans (by omega))
      (val s₀) s₀ st rfl (by omega) (by omega) hit
    -- move the result out
    set res := loopAux F rest (val s₀) st
    have hres : res = loopFn F args := by rw [hargs, loopFn_apply]
    have hresl : res.length ≤ M := by
      rw [hres]; have h := hqb args; change (loopFn F args).length ≤ qb.eval n at h; omega
    obtain ⟨t₅, ht₅, e₅⟩ := runs_moveRev (show lZ b ≠ lU b by simp [lZ, lU]) (LS S b [] res [])
    have h₅ := evalH_of_eval e₅ h₄.hb_end
    obtain ⟨t₆, ht₆, e₆⟩ := runs_moveRev (show lU b ≠ out by simp [lU]; omega)
      (Function.update (Function.update (LS S b [] res []) (lZ b) []) (lU b)
        ((LS S b [] res [] (lZ b)).reverse ++ LS S b [] res [] (lU b)))
    have h₆ := evalH_of_eval e₆ h₅.hb_end
    have hfin : Function.update (Function.update (Function.update (Function.update (LS S b [] res [])
        (lZ b) []) (lU b) ((LS S b [] res [] (lZ b)).reverse ++ LS S b [] res [] (lU b))) (lU b) [])
        out ((Function.update (Function.update (LS S b [] res []) (lZ b) []) (lU b)
          ((LS S b [] res [] (lZ b)).reverse ++ LS S b [] res [] (lU b)) (lU b)).reverse ++
          Function.update (Function.update (LS S b [] res []) (lZ b) []) (lU b)
            ((LS S b [] res [] (lZ b)).reverse ++ LS S b [] res [] (lU b)) out) =
        Function.update S out (loopFn F args) := by
      have hZ : LS S b [] res [] (lZ b) = res := ls_Z _ _ _
      have hU : LS S b [] res [] (lU b) = [] := by
        rw [ls_other] <;> simp [lU, lC, lZ, lG2, hbU']
      have hO : Function.update (Function.update (LS S b [] res []) (lZ b) []) (lU b)
          (res.reverse ++ []) out = [] := by
        rw [Function.update_of_ne (by simp [lU]; omega), Function.update_of_ne (by simp [lZ]; omega),
          ls_other _ _ _ (by simp [lC]; omega) (by simp [lZ]; omega) (by simp [lG2]; omega)]
        exact hS
      rw [hZ, hU, Function.update_self, hO, ← hres]
      have hb0 : S b = [] := hbC
      have hb4 : S (b + 4) = [] := hbG2
      have hb5 : S (b + 5) = [] := hbZ
      have hb7 : S (b + 7) = [] := hbU
      funext j
      simp only [LS, Function.update_apply, lC, lZ, lG2, lU]
      split_ifs <;> simp_all
    rw [hfin] at h₆
    -- the bounds
    have hR := Polynomial.eval_mono_nat RF.space (show M ≤ n + qb.eval n from le_rfl)
    simp only [Function.update_self, List.length_append, List.length_reverse, List.length_nil,
      add_zero] at ht₆
    rw [ls_Z] at ht₅
    have hU0 : LS S b [] res [] (lU b) = [] := by rw [ls_other] <;> simp [lU, lC, lZ, lG2, hbU']
    rw [ls_Z, hU0] at ht₆
    simp only [List.length_nil, add_zero] at ht₆
    have q1 : argSize args = n := rfl
    have q2 : (S (inp 0)).length = s₀.length := rfl
    have q3 : (Function.update S (lC b) s₀ (inp 1)).length = st.length := by
      rw [Function.update_of_ne (by simp [lC]; omega)]
    have q4 : Polynomial.eval (argSize args) qb = qb.eval n := rfl
    refine .seq (h₁.mono ?_) (.seq (h₂.mono ?_) (.seq (h₃.mono ?_) (.seq (h₄.mono ?_)
      (.seq (h₅.mono ?_) (h₆.mono ?_))))) <;>
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
      Polynomial.eval_comp] <;> omega

end

end Mach

end HTN
