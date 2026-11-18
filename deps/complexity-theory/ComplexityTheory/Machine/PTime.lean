import ComplexityTheory.Machine.Det
import ComplexityTheory.Machine.Kit
import ComplexityTheory.Complexity.CobhamTable
/-!
# `P` is decided by deterministic Turing machines in polynomial time

**Main theorem** (`HTN.Mach.exists_dtm_of_inP`). Every language of `P` (`HTN.Syn.InP`) is the set
of inputs accepted by a *deterministic* single-tape Turing machine with finitely many states over
`Option Bool` (at most one transition per state and symbol), within a polynomial time bound; and
the machine accepts no other input at all.

The machine is the simulation (`HTN.Mach.exists_tm_det`) of the stack machine `HTN.Mach.pCode`:
move the input to stack `1`, run the compiled stack program of a realizer of the decider (from
Cobham's theorem), and accept iff it outputs `true`.  The program has no `guess` and no `choose`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog

section Decider

variable {V : Args → Bool} (R : Realizer (fun args => [V args]))

/-- The input stacks of the decider: `x` on stack `1`, the empty stack `0` for further
arguments. -/
def pInp : ℕ → ℕ := fun i => if i = 0 then 1 else 0

/-- The address of the decider. -/
def pG : ℕ := size (moveRev 0 1)

/-- The address after the decider. -/
def pA : ℕ := pG + size (R.P pInp 2 3)

/-- The code before the final test. -/
def pPre : List Ins :=
  (compile (moveRev 0 1) 0).map Ins.ofInstr ++ (compile (R.P pInp 2 3) pG).map Ins.ofInstr

/-- **The deciding stack machine.** -/
def pCode : List Ins := pPre R ++ ([.br 2 (pA R + 2) (pA R + 2) (pA R + 1), .accept] : List Ins)

theorem pPre_len : (pPre R).length = pA R := by
  simp [pPre, pA, pG, length_compile]

theorem pCode_tail (i : ℕ) : (pCode R)[pA R + i]? =
    ([.br 2 (pA R + 2) (pA R + 2) (pA R + 1), .accept] : List Ins)[i]? := by
  have h := getElem?_append_at (pPre R) ([.br 2 (pA R + 2) (pA R + 2) (pA R + 1), .accept] : List Ins)
    (i := i)
  rw [pPre_len] at h
  exact h

theorem pCode_br : (pCode R)[pA R]? = some (.br 2 (pA R + 2) (pA R + 2) (pA R + 1)) := by
  simpa using pCode_tail R 0

theorem pCode_accept : (pCode R)[pA R + 1]? = some .accept := pCode_tail R 1

theorem pCode_end : (pCode R)[pA R + 2]? = none := pCode_tail R 2

theorem pCode_at₀ : AtS (pCode R) 0 (compile (moveRev 0 1) 0) :=
  atS_of_append (pre := []) (post := (compile (R.P pInp 2 3) pG).map Ins.ofInstr ++
    ([.br 2 (pA R + 2) (pA R + 2) (pA R + 1), .accept] : List Ins))
    (by simp [pCode, pPre]) rfl

theorem pCode_at₁ : AtS (pCode R) pG (compile (R.P pInp 2 3) pG) :=
  atS_of_append (pre := (compile (moveRev 0 1) 0).map Ins.ofInstr)
    (post := ([.br 2 (pA R + 2) (pA R + 2) (pA R + 1), .accept] : List Ins))
    (by simp [pCode, pPre]) (by simp [pG, length_compile])

/-- The number of stacks of the machine. -/
def pK : ℕ := 4 + R.W

theorem pCode_wf : ProgWF (pCode R) (pK R) := by
  intro pc ins hins k hk
  have hmem : ins ∈ pCode R := List.mem_of_getElem? hins
  have hb := R.bound pInp 2 3 (fun i _ => by unfold pInp; split_ifs <;> omega) (by omega)
  unfold pCode pPre at hmem
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  unfold pK
  rcases hmem with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | h
  · have := stk_compile _ _ _ hi k hk
    simp [maxStack, moveRev, move1] at this; omega
  · have := stk_compile _ _ _ hi k hk; omega
  · rcases h with rfl | rfl <;> simp [Ins.stk] at hk; omega

theorem ofInstr_noChoice (i : Prog.Instr) :
    (∀ k, Ins.ofInstr i ≠ .guess k) ∧ ∀ a b, Ins.ofInstr i ≠ .choose a b := by
  cases i <;> simp [Ins.ofInstr]

theorem pCode_noChoice : NoChoice (pCode R) := by
  intro ins hmem
  unfold pCode pPre at hmem
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | h
  · exact ofInstr_noChoice i
  · exact ofInstr_noChoice i
  · rcases h with rfl | rfl <;> simp

theorem pDecide (x : List Bool) {S : Store} (h0 : S 0 = []) (h1 : S 1 = x) (h2 : S 2 = [])
    (hc : Clean 3 S) :
    ∃ t ≤ R.time.eval x.length, Eval (R.P pInp 2 3) S (Function.update S 2 [V [x]]) t := by
  have h := realizer_eval R pInp 2 3 [x] S (fun i _ => by unfold pInp; split_ifs <;> omega)
    (by omega) (fun i _ => by unfold pInp; split_ifs <;> omega)
    (fun i _ => by unfold pInp; rcases i with _ | i <;> simp [h0, h1]) h2 hc
  simpa [argSize] using h

/-- The store after moving the input. -/
theorem pStore (x : List Bool) :
    let S₀ := inStore 0 x
    let S₁ := Function.update (Function.update S₀ 0 []) 1 ((S₀ 0).reverse ++ S₀ 1)
    S₁ 0 = [] ∧ S₁ 1 = x ∧ S₁ 2 = [] ∧ Clean 3 S₁ := by
  intro S₀ S₁
  have hS₀ : ∀ j, j ≠ 0 → S₀ j = [] := fun j hj => by simp [S₀, inStore, Function.update_of_ne hj]
  refine ⟨by simp [S₁], by simp [S₁, S₀, inStore, hS₀ 1 (by omega)], by simp [S₁, hS₀ 2 (by omega)],
    fun j hj => ?_⟩
  simp [S₁, Function.update_of_ne (show j ≠ 1 by omega), Function.update_of_ne (show j ≠ 0 by omega),
    hS₀ j (by omega)]

/-- **Soundness of the deciding machine.** -/
theorem pCode_sound {x : List Bool} (h : AccFrom (pCode R) ⟨0, inStore 0 x⟩) : V [x] = true := by
  set S₀ := inStore 0 x
  obtain ⟨t₀, -, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) S₀
  have h1 := h.of_sRunD (reach_compileD e₀ (pCode_at₀ R))
  simp only [zero_add] at h1
  set S₁ := Function.update (Function.update S₀ 0 []) 1 ((S₀ 0).reverse ++ S₀ 1)
  obtain ⟨e0, e1, e2, hc⟩ := pStore x
  obtain ⟨t, -, e⟩ := pDecide R x e0 e1 e2 hc
  have h2 := h1.of_sRunD (reach_compileD e (pCode_at₁ R))
  rw [show pG + size (R.P pInp 2 3) = pA R from rfl] at h2
  by_contra hV
  rw [Bool.not_eq_true] at hV
  rw [hV] at h2
  have hd : DetAt (pCode R) ⟨pA R, Function.update S₁ 2 [false]⟩ := ⟨.br 2 _ _ _, pCode_br R⟩
  rcases h2.inv with ha | ⟨τ, hs, hτ⟩
  · exact hd.not_accepting ha
  · have hs' : SStep (pCode R) ⟨pA R, Function.update S₁ 2 [false]⟩
        ⟨pA R + 2, Function.update S₁ 2 [false]⟩ :=
      SStep.brF (r := []) (pCode_br R) (by simp)
    obtain rfl := SStep.det hd hs hs'
    exact not_accFrom_of_none (pCode_end R) hτ

/-- **Completeness of the deciding machine.** -/
theorem pCode_complete {x : List Bool} (hV : V [x] = true) :
    ∃ σ', SRun (pCode R) ⟨0, inStore 0 x⟩ σ' (2 * (4 * x.length + 1) + 2 * R.time.eval x.length + 1) ∧
      Accepting (pCode R) σ' := by
  set S₀ := inStore 0 x
  obtain ⟨t₀, ht₀, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) S₀
  have r₀ := (reach_compileD e₀ (pCode_at₀ R)).sRun
  simp only [zero_add] at r₀
  set S₁ := Function.update (Function.update S₀ 0 []) 1 ((S₀ 0).reverse ++ S₀ 1)
  obtain ⟨e0, e1, e2, hc⟩ := pStore x
  obtain ⟨t, ht, e⟩ := pDecide R x e0 e1 e2 hc
  have r₂ := (reach_compileD e (pCode_at₁ R)).sRun
  rw [show pG + size (R.P pInp 2 3) = pA R from rfl, hV] at r₂
  have r₃ : SRun (pCode R) ⟨pA R, Function.update S₁ 2 [true]⟩
      ⟨pA R + 1, Function.update S₁ 2 [true]⟩ 1 := SRun.single (SStep.brT (r := []) (pCode_br R) (by simp))
  have hlen : (S₀ 0).length = x.length := by simp [S₀, inStore]
  refine ⟨_, ((r₀.trans r₂).trans r₃).mono ?_, pCode_accept R⟩
  rw [hlen] at ht₀
  omega

end Decider

/-! ### The theorem -/

/-- **`P` is decided by deterministic Turing machines in polynomial time.** -/
theorem exists_dtm_of_inP {L : List Bool → Prop} (hL : Syn.InP L) :
    ∃ (k : ℕ) (M : NTM (Fin k) (Option Bool)) (r : Polynomial ℕ), M.blank = none ∧
      (∀ q γ, (M.step q γ).Subsingleton) ∧ ∀ x,
      (L x → M.AcceptsWithin (x.map some) (r.eval x.length)) ∧
      ((∃ N c, M.Reaches N (M.initConfig (x.map some)) c ∧ c.state ∈ M.accept) → L x) := by
  obtain ⟨G, hG, hLG⟩ := hL
  obtain ⟨f, hf, hFf⟩ := hG.firstBit.cobham
  set V : Args → Bool := fun args => (G (args.getD 0 [])).getD 0 false
  have hV : CobhamB V := by
    refine (cobham_c1 hf (Cobham.proj 0)).of_fun_eq fun args => ?_
    simp [compFn, proj, ← hFf, V]
  obtain ⟨R⟩ := Prog.nonempty_realizer hV
  obtain ⟨k, M, hblank, hdet, hM⟩ := exists_tm_det (pCode R) (pK R) 0 (pCode_wf R)
    (by unfold pK; omega) (pCode_noChoice R)
  set K := pK R
  let PT : Polynomial ℕ := 2 * (4 * Polynomial.X + 1) + 2 * R.time + 1
  let r : Polynomial ℕ := (Polynomial.X + 1) * (6 * (Polynomial.X + 2) * (Polynomial.C (K : ℕ) + 1)) +
    PT * (3 * (Polynomial.X + PT + 2) * (Polynomial.C (K : ℕ) + 1))
  refine ⟨k, M, r, hblank, hdet, fun x => ⟨fun hx => ?_, fun h => ?_⟩⟩
  · have hVx : V [x] = true := by simpa [V] using (hLG x).1 hx
    obtain ⟨σ', ⟨T, hT, hr⟩, ha⟩ := pCode_complete R hVx
    have hrP := sReachP_of_sReach (K := K) (H := x.length) T hr (hgt_inStore (kin := 0) x le_rfl)
    obtain ⟨hW, -⟩ := (hM x).2 T (x.length + T) σ' (by omega) hrP ha
    refine NTM.acceptsWithin_mono M ?_ hW
    have hTP : T ≤ PT.eval x.length := by
      simp only [PT, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_ofNat]
      omega
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    exact Nat.add_le_add le_rfl (Nat.mul_le_mul hTP (Nat.mul_le_mul (Nat.mul_le_mul le_rfl
      (by omega)) le_rfl))
  · obtain ⟨T, σ', hr, ha⟩ := (hM x).1 h
    have := pCode_sound R ⟨T, σ', hr, ha⟩
    exact (hLG x).2 (by simpa [V] using this)

end Mach

end HTN
