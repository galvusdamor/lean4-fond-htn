import ComplexityTheory.Machine.Kit
/-!
# `NEXPTIME` from polynomial-time verifiers of exponentially long certificates

**Main theorem** (`HTN.Mach.inNExp_of_verifier`). Let `V` be a predicate of Cobham's class and
`p` a polynomial such that `V` accepts `[x, w]` only for certificates `w` of length at most
`2 ^ p(|x|)`.  Then the language `{x | ∃ w, V [x, w] = true}` is in `NEXPTIME`
(`HTN.Space.InNExp`, nondeterministic single-tape Turing machines clocked at an exponential time
bound).

This is the "guess and check" characterisation of `NEXPTIME`.  The machine is the simulation
(`HTN.Mach.exists_tm`) of the stack machine `HTN.Mach.nCode`: move the input to stack `1`, guess
the certificate onto stack `2` bit by bit, run the compiled stack program of a realizer of `V`
(`HTN.PTime.CobhamTM.Prog.Realizer`, from Cobham's theorem), and accept iff it outputs `true`.
The verifier runs in time polynomial in `|x| + |w| ≤ |x| + 2 ^ p(|x|)`, which is at most
`2 ^ q(|x|)` for a polynomial `q`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog

/-! ### The guess-and-check machine -/

section Verifier

variable {V : Args → Bool} (R : Realizer (fun args => [V args]))

/-- The input stacks of the verifier: `x` on stack `1`, `w` on stack `2`, empty stack `0`. -/
def nInp : ℕ → ℕ := fun i => if i = 0 then 1 else if i = 1 then 2 else 0

/-- The address of the guessing loop. -/
def nG : ℕ := size (moveRev 0 1)

/-- The address after the verifier. -/
def nA : ℕ := nG + 3 + size (R.P nInp 3 4)

/-- The code before the final test. -/
def nPre : List Ins :=
  (compile (moveRev 0 1) 0).map Ins.ofInstr ++
    ([.choose (nG + 1) (nG + 3), .guess 2, .jmp nG] : List Ins) ++
    (compile (R.P nInp 3 4) (nG + 3)).map Ins.ofInstr

/-- **The guess-and-check stack machine.** -/
def nCode : List Ins := nPre R ++ ([.br 3 (nA R + 2) (nA R + 2) (nA R + 1), .accept] : List Ins)

theorem len_c₀ : ((compile (moveRev 0 1) 0).map Ins.ofInstr).length = nG := by
  simp [nG, length_compile]

theorem nPre_len : (nPre R).length = nA R := by
  simp only [nPre, List.length_append, len_c₀, List.length_map, length_compile, List.length_cons,
    List.length_nil, nA, nG]

theorem nCode_loop (i : ℕ) (hi : i < 3) : (nCode R)[nG + i]? =
    ([.choose (nG + 1) (nG + 3), .guess 2, .jmp nG] : List Ins)[i]? := by
  unfold nCode nPre
  rw [List.append_assoc, List.append_assoc, ← len_c₀, getElem?_append_at,
    List.getElem?_append_left (by simp; omega)]

theorem nCode_choose : (nCode R)[nG]? = some (.choose (nG + 1) (nG + 3)) := by
  simpa using nCode_loop R 0 (by omega)

theorem nCode_guess : (nCode R)[nG + 1]? = some (.guess 2) := nCode_loop R 1 (by omega)

theorem nCode_jmp : (nCode R)[nG + 2]? = some (.jmp nG) := nCode_loop R 2 (by omega)

theorem nCode_tail (i : ℕ) : (nCode R)[nA R + i]? =
    ([.br 3 (nA R + 2) (nA R + 2) (nA R + 1), .accept] : List Ins)[i]? := by
  have h := getElem?_append_at (nPre R) ([.br 3 (nA R + 2) (nA R + 2) (nA R + 1), .accept] : List Ins)
    (i := i)
  rw [nPre_len] at h
  exact h

theorem nCode_br : (nCode R)[nA R]? = some (.br 3 (nA R + 2) (nA R + 2) (nA R + 1)) := by
  simpa using nCode_tail R 0

theorem nCode_accept : (nCode R)[nA R + 1]? = some .accept := nCode_tail R 1

theorem nCode_end : (nCode R)[nA R + 2]? = none := nCode_tail R 2

theorem nCode_at₀ : AtS (nCode R) 0 (compile (moveRev 0 1) 0) :=
  atS_of_append (pre := []) (post := ([.choose (nG + 1) (nG + 3), .guess 2, .jmp nG] : List Ins) ++
    (compile (R.P nInp 3 4) (nG + 3)).map Ins.ofInstr ++
    ([.br 3 (nA R + 2) (nA R + 2) (nA R + 1), .accept] : List Ins))
    (by simp [nCode, nPre]) rfl

theorem nCode_at₁ : AtS (nCode R) (nG + 3) (compile (R.P nInp 3 4) (nG + 3)) :=
  atS_of_append (pre := (compile (moveRev 0 1) 0).map Ins.ofInstr ++
    ([.choose (nG + 1) (nG + 3), .guess 2, .jmp nG] : List Ins))
    (post := ([.br 3 (nA R + 2) (nA R + 2) (nA R + 1), .accept] : List Ins)) rfl
    (by simp [nG, length_compile])

/-- The number of stacks of the machine. -/
def nK : ℕ := 5 + R.W

theorem nCode_wf : ProgWF (nCode R) (nK R) := by
  intro pc ins hins k hk
  have hmem : ins ∈ nCode R := List.mem_of_getElem? hins
  have hb := R.bound nInp 3 4 (fun i _ => by unfold nInp; split_ifs <;> omega) (by omega)
  unfold nCode nPre at hmem
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  unfold nK
  rcases hmem with ((⟨i, hi, rfl⟩ | h) | ⟨i, hi, rfl⟩) | h
  · have := stk_compile _ _ _ hi k hk
    simp [maxStack, moveRev, move1] at this; omega
  · rcases h with rfl | rfl | rfl <;> simp [Ins.stk] at hk; omega
  · have := stk_compile _ _ _ hi k hk; omega
  · rcases h with rfl | rfl <;> simp [Ins.stk] at hk; omega

/-! #### Soundness -/

theorem nInp_spec {x w : List Bool} {S : Store} (h0 : S 0 = []) (h1 : S 1 = x) (h2 : S 2 = w)
    {i : ℕ} (hi : i < R.A) : S (nInp i) = [x, w].getD i [] := by
  unfold nInp
  rcases i with _ | _ | i
  · simp [h1]
  · simp [h2]
  · simp [h0]

theorem nVerify (x w : List Bool) {S : Store} (h0 : S 0 = []) (h1 : S 1 = x) (h2 : S 2 = w)
    (h3 : S 3 = []) (hc : Clean 4 S) :
    ∃ t ≤ R.time.eval (x.length + w.length),
      Eval (R.P nInp 3 4) S (Function.update S 3 [V [x, w]]) t := by
  have r := R.spec nInp 3 4 S (fun i _ => by unfold nInp; split_ifs <;> omega) (by omega)
    (fun i _ => by unfold nInp; split_ifs <;> omega) h3 hc
  have hget : ∀ i < R.A, S (nInp i) = [x, w].getD i [] := fun i hi => nInp_spec R h0 h1 h2 hi
  have hf : [V (argsOf R.A nInp S)] = [V [x, w]] :=
    (R.reads.congr fun i hi => by rw [getD_argsOf hi, hget i hi, getD_padArgs hi]).trans
      (R.reads _).symm
  have hsz : argSize (argsOf R.A nInp S) ≤ x.length + w.length :=
    (Prog.argSize_argsOf_le_of_getD hget).trans (by simp [argSize]; try omega)
  rw [hf] at r
  obtain ⟨t, ht, e⟩ := r
  exact ⟨t, le_trans ht (Polynomial.eval_mono_nat _ hsz), e⟩

theorem nLoop_sound :
    ∀ T (S : Store) (σ' : SCfg), SReach (nCode R) T ⟨nG, S⟩ σ' → Accepting (nCode R) σ' →
      ∃ w, AccFrom (nCode R) ⟨nG + 3, Function.update S 2 (w ++ S 2)⟩ := by
  have hc := nCode_choose R
  have hg := nCode_guess R
  have hj : (nCode R)[nG + 1 + 1]? = some (.jmp nG) := nCode_jmp R
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    intro S σ' hr hacc
    rcases T with _ | T
    · cases hr; unfold Accepting at hacc; rw [nCode_choose] at hacc; cases hacc
    obtain ⟨τ, hs, hr'⟩ := hr
    cases hs with
    | choose₁ h =>
      rw [nCode_choose] at h; cases h
      -- `guess`
      rcases T with _ | T
      · cases hr'; unfold Accepting at hacc; rw [nCode_guess] at hacc; cases hacc
      obtain ⟨τ₂, hs₂, hr₂⟩ := hr'
      cases hs₂ with
      | guess b h₂ =>
        rw [nCode_guess] at h₂; cases h₂
        rcases T with _ | T
        · cases hr₂; unfold Accepting at hacc; rw [nCode_jmp] at hacc; cases hacc
        obtain ⟨τ₃, hs₃, hr₃⟩ := hr₂
        cases hs₃ with
        | jmp h₃ =>
          rw [nCode_jmp] at h₃; cases h₃
          obtain ⟨w, hw⟩ := ih T (by omega) _ σ' hr₃ hacc
          refine ⟨w ++ [b], ?_⟩
          simpa [Function.update_idem] using hw
        | _ => simp_all
      | _ => simp_all
    | choose₂ h =>
      rw [nCode_choose] at h; cases h
      exact ⟨[], by simpa [Function.update_eq_self] using (⟨T, σ', hr', hacc⟩ : AccFrom _ _)⟩
    | _ => simp_all

/-- **Soundness of the guess-and-check machine.** -/
theorem nCode_sound {x : List Bool} (h : AccFrom (nCode R) ⟨0, inStore 0 x⟩) :
    ∃ w, V [x, w] = true := by
  set S₀ := inStore 0 x
  obtain ⟨t₀, -, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) S₀
  have h1 := h.of_sRunD (reach_compileD e₀ (nCode_at₀ R))
  simp only [zero_add] at h1
  set S₁ := Function.update (Function.update S₀ 0 []) 1 ((S₀ 0).reverse ++ S₀ 1)
  obtain ⟨T, σ', hr, hacc⟩ := h1
  obtain ⟨w, hw⟩ := nLoop_sound R T S₁ σ' hr hacc
  set S₂ := Function.update S₁ 2 (w ++ S₁ 2)
  have hS₀ : ∀ j, j ≠ 0 → S₀ j = [] := fun j hj => by simp [S₀, inStore, Function.update_of_ne hj]
  have e0 : S₂ 0 = [] := by simp [S₂, S₁]
  have e1 : S₂ 1 = x := by simp [S₂, S₁, S₀, inStore, hS₀ 1 (by omega)]
  have e2 : S₂ 2 = w := by simp [S₂, S₁, hS₀ 2 (by omega)]
  have e3 : S₂ 3 = [] := by simp [S₂, S₁, hS₀ 3 (by omega)]
  have hc : Clean 4 S₂ := fun j hj => by simp [S₂, S₁, Function.update_of_ne (show j ≠ 2 by omega),
    Function.update_of_ne (show j ≠ 1 by omega), Function.update_of_ne (show j ≠ 0 by omega),
    hS₀ j (by omega)]
  obtain ⟨t, -, e⟩ := nVerify R x w e0 e1 e2 e3 hc
  have h2 := hw.of_sRunD (reach_compileD e (nCode_at₁ R))
  rw [show nG + 3 + size (R.P nInp 3 4) = nA R from rfl] at h2
  refine ⟨w, ?_⟩
  by_contra hV
  rw [Bool.not_eq_true] at hV
  rw [hV] at h2
  have hd : DetAt (nCode R) ⟨nA R, Function.update S₂ 3 [false]⟩ := ⟨.br 3 _ _ _, nCode_br R⟩
  rcases h2.inv with ha | ⟨τ, hs, hτ⟩
  · exact hd.not_accepting ha
  · have hs' : SStep (nCode R) ⟨nA R, Function.update S₂ 3 [false]⟩
        ⟨nA R + 2, Function.update S₂ 3 [false]⟩ :=
      SStep.brF (r := []) (nCode_br R) (by simp)
    obtain rfl := SStep.det hd hs hs'
    exact not_accFrom_of_none (nCode_end R) hτ

/-! #### Completeness -/

theorem nLoop_run : ∀ (u : List Bool) (S : Store),
    SRun (nCode R) ⟨nG, S⟩ ⟨nG + 3, Function.update S 2 (u.reverse ++ S 2)⟩ (3 * u.length + 1) := by
  intro u
  induction u with
  | nil =>
    intro S
    simpa [Function.update_eq_self] using SRun.single (SStep.choose₂ (S := S) (nCode_choose R))
  | cons b u ih =>
    intro S
    have r₁ : SRun (nCode R) ⟨nG, S⟩ ⟨nG, Function.update S 2 (b :: S 2)⟩ 3 :=
      ((SRun.single (SStep.choose₁ (nCode_choose R))).trans
        (SRun.single (SStep.guess b (nCode_guess R)))).trans
        (SRun.single (SStep.jmp (nCode_jmp R)))
    have r₂ := ih (Function.update S 2 (b :: S 2))
    have e : Function.update (Function.update S 2 (b :: S 2)) 2
        (u.reverse ++ Function.update S 2 (b :: S 2) 2) =
        Function.update S 2 ((b :: u).reverse ++ S 2) := by simp
    rw [e] at r₂
    exact (r₁.trans r₂).mono (by simp; omega)

/-- **Completeness of the guess-and-check machine.** -/
theorem nCode_complete {x w : List Bool} (hV : V [x, w] = true) :
    ∃ σ', SRun (nCode R) ⟨0, inStore 0 x⟩ σ'
      (2 * (4 * x.length + 1) + (3 * w.length + 1) + 2 * R.time.eval (x.length + w.length) + 1) ∧
      Accepting (nCode R) σ' := by
  set S₀ := inStore 0 x
  obtain ⟨t₀, ht₀, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) S₀
  have r₀ := (reach_compileD e₀ (nCode_at₀ R)).sRun
  simp only [zero_add] at r₀
  set S₁ := Function.update (Function.update S₀ 0 []) 1 ((S₀ 0).reverse ++ S₀ 1)
  have r₁ := nLoop_run R w.reverse S₁
  rw [List.reverse_reverse] at r₁
  set S₂ := Function.update S₁ 2 (w ++ S₁ 2)
  have hS₀ : ∀ j, j ≠ 0 → S₀ j = [] := fun j hj => by simp [S₀, inStore, Function.update_of_ne hj]
  have e0 : S₂ 0 = [] := by simp [S₂, S₁]
  have e1 : S₂ 1 = x := by simp [S₂, S₁, S₀, inStore, hS₀ 1 (by omega)]
  have e2 : S₂ 2 = w := by simp [S₂, S₁, hS₀ 2 (by omega)]
  have e3 : S₂ 3 = [] := by simp [S₂, S₁, hS₀ 3 (by omega)]
  have hc : Clean 4 S₂ := fun j hj => by simp [S₂, S₁, Function.update_of_ne (show j ≠ 2 by omega),
    Function.update_of_ne (show j ≠ 1 by omega), Function.update_of_ne (show j ≠ 0 by omega),
    hS₀ j (by omega)]
  obtain ⟨t, ht, e⟩ := nVerify R x w e0 e1 e2 e3 hc
  have r₂ := (reach_compileD e (nCode_at₁ R)).sRun
  rw [show nG + 3 + size (R.P nInp 3 4) = nA R from rfl, hV] at r₂
  have r₃ : SRun (nCode R) ⟨nA R, Function.update S₂ 3 [true]⟩
      ⟨nA R + 1, Function.update S₂ 3 [true]⟩ 1 := SRun.single (SStep.brT (r := []) (nCode_br R) (by simp))
  have hlen : (S₀ 0).length = x.length := by simp [S₀, inStore]
  refine ⟨_, (((r₀.trans r₁).trans r₂).trans r₃).mono ?_, nCode_accept R⟩
  simp only [List.length_reverse]
  rw [hlen] at ht₀
  omega

end Verifier

/-! ### The theorem -/

/-- **Guess and check: `NEXPTIME` contains every language with exponentially long certificates
that are checked in polynomial time.** -/
theorem inNExp_of_verifier {L : List Bool → Prop} (V : Args → Bool) (hV : CobhamB V)
    (p : Polynomial ℕ) (hshort : ∀ x w, V [x, w] = true → w.length ≤ 2 ^ p.eval x.length)
    (hL : ∀ x, L x ↔ ∃ w, V [x, w] = true) : Space.InNExp L := by
  obtain ⟨R⟩ := Prog.nonempty_realizer hV
  obtain ⟨k, M, hblank, hM⟩ := exists_tm (nCode R) (nK R) 0 (nCode_wf R) (by unfold nK; omega)
  -- the bound on the time of an accepting run, as a polynomial in `|x| + |w|`
  set K := nK R
  let PT : Polynomial ℕ := 2 * (4 * Polynomial.X + 1) + (3 * Polynomial.X + 1) + 2 * R.time + 1
  let PB : Polynomial ℕ := (Polynomial.X + 1) * (6 * (Polynomial.X + 2) * (Polynomial.C (K : ℕ) + 1)) +
    PT * (3 * (Polynomial.X + PT + 2) * (Polynomial.C (K : ℕ) + 1))
  obtain ⟨q, hq⟩ := exists_two_pow_bound PB (p + Polynomial.X)
  -- from a certificate to an accepting run within `2 ^ q(|x|)` steps
  have hacc : ∀ x w, V [x, w] = true → M.AcceptsWithin (x.map some) (2 ^ q.eval x.length) := by
    intro x w hVw
    have hw := hshort x w hVw
    obtain ⟨σ', ⟨T, hT, hr⟩, ha⟩ := nCode_complete R hVw
    set m := x.length + w.length
    have hTm : T ≤ PT.eval m := by
      simp only [PT, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_ofNat]
      have := Polynomial.eval_mono_nat R.time (show x.length + w.length ≤ m from le_rfl)
      omega
    have hrP := sReachP_of_sReach (K := K) (H := x.length) T hr
      (hgt_inStore (kin := 0) x le_rfl)
    obtain ⟨hW, -⟩ := (hM x).2 T (x.length + T) σ' (by omega) hrP ha
    refine NTM.acceptsWithin_mono M ?_ hW
    have hm : m ≤ 2 ^ (p + Polynomial.X).eval x.length := by
      simp only [Polynomial.eval_add, Polynomial.eval_X, pow_add]
      have h1 : x.length < 2 ^ x.length := Nat.lt_two_pow_self
      have h2 : 1 ≤ 2 ^ p.eval x.length := Nat.one_le_two_pow
      obtain ⟨a, ha⟩ : ∃ a, 2 ^ p.eval x.length = a + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h2).symm⟩
      obtain ⟨b, hb⟩ : ∃ b, 2 ^ x.length = b + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
        (lt_of_le_of_lt (Nat.zero_le _) h1)).symm⟩
      have hw' : w.length ≤ a + 1 := ha ▸ hw
      have h1' : x.length < b + 1 := hb ▸ h1
      have hm' : m = x.length + w.length := rfl
      have : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
      rw [ha, hb, this]
      omega
    refine le_trans ?_ (hq x.length m hm)
    simp only [PB, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    have hxm : x.length ≤ m := by omega
    have h6 : (x.length + 1) * (6 * (x.length + 2) * (K + 1)) ≤ (m + 1) * (6 * (m + 2) * (K + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) le_rfl)
    have h7 : T * (3 * (x.length + T + 2) * (K + 1)) ≤
        PT.eval m * (3 * (m + PT.eval m + 2) * (K + 1)) :=
      Nat.mul_le_mul hTm (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) le_rfl)
    omega
  -- acceptance at all means a certificate
  have hsound : ∀ x, (∃ N c, M.Reaches N (M.initConfig (x.map some)) c ∧ c.state ∈ M.accept) →
      ∃ w, V [x, w] = true := by
    intro x h
    obtain ⟨T, σ', hr, ha⟩ := (hM x).1 h
    exact nCode_sound R ⟨T, σ', hr, ha⟩
  refine ⟨k, M, q, fun x m hm => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨n, -, c, hr, hc⟩ := hm
    obtain ⟨w, hw⟩ := hsound x ⟨n, c, hr, hc⟩
    exact hacc x w hw
  · obtain ⟨w, hw⟩ := (hL x).1 hx
    unfold Space.NTMLang NTM.AcceptsExp
    rw [List.length_map]
    exact hacc x w hw
  · obtain ⟨n, -, c, hr, hc⟩ := hx
    exact (hL x).2 (hsound x ⟨n, c, hr, hc⟩)

end Mach

end HTN
