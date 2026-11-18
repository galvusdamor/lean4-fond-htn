import ComplexityTheory.Machine.SLoop
import ComplexityTheory.Machine.NExp
import ComplexityTheory.Machine.ExpSpace
/-!
# `PSPACE` is decided by Turing machines in polynomial space

`PSPACE` is defined in this development as a function algebra (`HTN.PSpace.InPSpace`, the class
`HTN.PSpace.PSpaceF`: Cobham's class closed under composition and bounded exponential
iteration).  This file proves the half of its identification with machine space that hardness
proofs need:

* `HTN.Mach.nonempty_srealizer` — every function of the class has a space realizer
  (`HTN.Mach.SRealizer`): a stack program computing it whose stacks stay polynomial;
* **`HTN.Mach.exists_tm_of_inPSpace`** — every language of `PSPACE` is the set of inputs that a
  single-tape Turing machine with finitely many states (over `Option Bool`) accepts within a
  polynomial space bound.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog PSpace

/-- **Every function of the polynomial-space class has a space realizer.** -/
theorem nonempty_srealizer {f : Fn} (hf : PSpaceF f) : Nonempty (SRealizer f) := by
  induction hf with
  | cobham h =>
    obtain ⟨R⟩ := Prog.nonempty_realizer h
    exact ⟨SRealizer.ofRealizer R⟩
  | @comp g hs _ hhs ihg ihhs =>
    obtain ⟨Rg⟩ := ihg
    obtain ⟨q, hq⟩ := exists_common_bound (fun f hf => (hhs f hf).poly_length)
    exact ⟨srealizer_comp Rg (smultiOf hs fun h hh => Classical.choice (ihhs h hh)) q hq⟩
  | @loop F bd _ hbd hbound ihF _ =>
    obtain ⟨RF⟩ := ihF
    obtain ⟨p, hp⟩ := hbd.poly_length
    exact ⟨srealizer_loop RF p (fun args => (hbound args).trans (hp args))⟩

/-! ### The decision machine -/

section Decide

variable {p : Args → Bool} (R : SRealizer (fun args => [p args]))

/-- The input stacks of the predicate: `x` on stack `1`. -/
def dInp : ℕ → ℕ := fun i => if i = 0 then 1 else 0

def dA : ℕ := size (moveRev 0 1) + size (R.P dInp 2 3)

def dPre : List Ins :=
  (compile (moveRev 0 1) 0).map Ins.ofInstr ++
    (compile (R.P dInp 2 3) (size (moveRev 0 1))).map Ins.ofInstr

/-- **The decision machine**: move the input, evaluate the predicate, accept iff it holds. -/
def dCode : List Ins := dPre R ++ ([.br 2 (dA R + 2) (dA R + 2) (dA R + 1), .accept] : List Ins)

theorem dPre_len : (dPre R).length = dA R := by simp [dPre, dA, length_compile]

theorem dCode_tail (i : ℕ) : (dCode R)[dA R + i]? =
    ([.br 2 (dA R + 2) (dA R + 2) (dA R + 1), .accept] : List Ins)[i]? := by
  have h := getElem?_append_at (dPre R) ([.br 2 (dA R + 2) (dA R + 2) (dA R + 1), .accept] : List Ins)
    (i := i)
  rw [dPre_len] at h
  exact h

theorem dCode_br : (dCode R)[dA R]? = some (.br 2 (dA R + 2) (dA R + 2) (dA R + 1)) := by
  simpa using dCode_tail R 0
theorem dCode_accept : (dCode R)[dA R + 1]? = some .accept := dCode_tail R 1
theorem dCode_end : (dCode R)[dA R + 2]? = none := dCode_tail R 2

theorem dCode_at₀ : AtS (dCode R) 0 (compile (moveRev 0 1) 0) :=
  atS_of_append (pre := []) (post := (compile (R.P dInp 2 3) (size (moveRev 0 1))).map Ins.ofInstr ++
    ([.br 2 (dA R + 2) (dA R + 2) (dA R + 1), .accept] : List Ins)) (by simp [dCode, dPre]) rfl

theorem dCode_at₁ : AtS (dCode R) (size (moveRev 0 1)) (compile (R.P dInp 2 3) (size (moveRev 0 1))) :=
  atS_of_append (pre := (compile (moveRev 0 1) 0).map Ins.ofInstr)
    (post := ([.br 2 (dA R + 2) (dA R + 2) (dA R + 1), .accept] : List Ins)) (by simp [dCode, dPre])
    (by simp [length_compile])

def dK : ℕ := 4 + R.W

theorem dCode_wf : ProgWF (dCode R) (dK R) := by
  intro pc ins hins k hk
  have hmem : ins ∈ dCode R := List.mem_of_getElem? hins
  have hb := R.bound dInp 2 3 (fun i _ => by unfold dInp; split_ifs <;> omega) (by omega)
  unfold dCode dPre at hmem
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  unfold dK
  rcases hmem with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | h
  · have := stk_compile _ _ _ hi k hk; simp [maxStack, moveRev, move1] at this; omega
  · have := stk_compile _ _ _ hi k hk; omega
  · rcases h with rfl | rfl <;> simp [Ins.stk] at hk; omega

/-- The store after moving the input. -/
def dS₁ (x : List Bool) : Store :=
  Function.update (Function.update (inStore 0 x) 0 []) 1 ((inStore 0 x 0).reverse ++ inStore 0 x 1)

theorem dS₁_spec (x : List Bool) : dS₁ x 1 = x ∧ dS₁ x 2 = [] ∧ Clean 3 (dS₁ x) ∧ dS₁ x 0 = [] := by
  refine ⟨by simp [dS₁, inStore], by simp [dS₁, inStore], fun j hj => ?_, by simp [dS₁]⟩
  simp [dS₁, inStore, Function.update_of_ne (show j ≠ 1 by omega),
    Function.update_of_ne (show j ≠ 0 by omega)]

theorem dEval (x : List Bool) {h₀ : ℕ} (hb : HB h₀ (dS₁ x)) :
    EvalH (h₀ + R.space.eval x.length) (R.P dInp 2 3) (dS₁ x)
      (Function.update (dS₁ x) 2 [p [x]]) := by
  obtain ⟨h1, h2, hc, h0⟩ := dS₁_spec x
  have r := R.spec dInp 2 3 (dS₁ x) h₀ (fun i _ => by unfold dInp; split_ifs <;> omega) (by omega)
    (fun i _ => by unfold dInp; split_ifs <;> omega) h2 hc hb
  have hget : ∀ i < R.A, dS₁ x (dInp i) = [x].getD i [] := by
    intro i _
    unfold dInp
    rcases i with _ | i
    · simp [h1]
    · simp [h0]
  have hf : [p (argsOf R.A dInp (dS₁ x))] = [p [x]] :=
    (R.reads.congr fun i hi => by rw [getD_argsOf hi, hget i hi, CobhamTM.getD_padArgs hi]).trans
      (R.reads _).symm
  have hsz : argSize (argsOf R.A dInp (dS₁ x)) ≤ x.length :=
    (Prog.argSize_argsOf_le_of_getD hget).trans (by simp [argSize])
  rw [hf] at r
  exact r.mono (by have := Polynomial.eval_mono_nat R.space hsz; omega)

/-- **Soundness of the decision machine.** -/
theorem dCode_sound {x : List Bool} (h : AccFrom (dCode R) ⟨0, inStore 0 x⟩) : p [x] = true := by
  obtain ⟨t₀, -, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) (inStore 0 x)
  have h1 := h.of_sRunD (reach_compileD e₀ (dCode_at₀ R))
  simp only [zero_add] at h1
  obtain ⟨t, e⟩ := (dEval R x (h₀ := (x.length + 1)) (fun j => by
    unfold dS₁ inStore
    by_cases h1 : j = 1
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h0 : j = 0
      · subst h0; simp
      · rw [Function.update_of_ne h0, Function.update_of_ne h0]; simp)).eval
  have h2 := h1.of_sRunD (reach_compileD e (dCode_at₁ R))
  rw [show size (moveRev 0 1) + size (R.P dInp 2 3) = dA R from rfl] at h2
  by_contra hp
  rw [Bool.not_eq_true] at hp
  rw [hp] at h2
  have hd : DetAt (dCode R) ⟨dA R, Function.update (dS₁ x) 2 [false]⟩ := ⟨.br 2 _ _ _, dCode_br R⟩
  rcases h2.inv with ha | ⟨τ, hs, hτ⟩
  · exact hd.not_accepting ha
  · have hs' : SStep (dCode R) ⟨dA R, Function.update (dS₁ x) 2 [false]⟩
        ⟨dA R + 2, Function.update (dS₁ x) 2 [false]⟩ := SStep.brF (r := []) (dCode_br R) (by simp)
    obtain rfl := SStep.det hd hs hs'
    exact not_accFrom_of_none (dCode_end R) hτ

/-- **Completeness of the decision machine**, with the heights of the stacks. -/
theorem dCode_complete {x : List Bool} (hp : p [x] = true) :
    ∃ n σ', Accepting (dCode R) σ' ∧ SReachP (dCode R)
      (fun τ => Hgt (dK R) (9 * x.length + 3 + R.space.eval x.length) τ.S) n ⟨0, inStore 0 x⟩ σ' := by
  obtain ⟨t₀, ht₀, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) (inStore 0 x)
  have r₀ := (reach_compileD e₀ (dCode_at₀ R)).sRun
  simp only [zero_add] at r₀
  have hlen : (inStore 0 x 0).length = x.length := by simp [inStore]
  have hs₀ : Hgt (dK R) x.length (inStore 0 x) := by
    intro j _; unfold inStore
    by_cases hj : j = 0
    · subst hj; simp
    · rw [Function.update_of_ne hj]; simp
  obtain ⟨n₀, -, p₀⟩ := sReachP_of_sRun r₀ hs₀
  have hb₁ : HB (x.length + 1) (dS₁ x) := fun j => by
    unfold dS₁ inStore
    by_cases h1 : j = 1
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h0 : j = 0
      · subst h0; simp
      · rw [Function.update_of_ne h0, Function.update_of_ne h0]; simp
  have e₁ := dEval R x hb₁
  rw [hp] at e₁
  obtain ⟨n₁, p₁⟩ := reach_compileH e₁ (dCode_at₁ R)
  rw [show size (moveRev 0 1) + size (R.P dInp 2 3) = dA R from rfl] at p₁
  have hfin : HB (x.length + 1 + R.space.eval x.length) (Function.update (dS₁ x) 2 [true]) :=
    e₁.hb_end
  have p₂ : SReachP (dCode R) (fun τ => HB (x.length + 1 + R.space.eval x.length) τ.S) 1
      ⟨dA R, Function.update (dS₁ x) 2 [true]⟩ ⟨dA R + 1, Function.update (dS₁ x) 2 [true]⟩ :=
    SReachP.single' (SStep.brT (r := []) (dCode_br R) (by simp)) hfin hfin
  refine ⟨_, ⟨dA R + 1, Function.update (dS₁ x) 2 [true]⟩, dCode_accept R,
    (p₀.mono fun τ h => hgt_mono h ?_).trans ((p₁.trans p₂).mono fun τ h r _ => le_trans (h r) ?_)⟩
  · have := hlen; omega
  · omega

end Decide

/-- **`PSPACE` is accepted by Turing machines in polynomial space.** -/
theorem exists_tm_of_inPSpace {L : List Bool → Prop} (hL : InPSpace L) :
    ∃ (k : ℕ) (M : NTM (Fin k) (Option Bool)) (q : Polynomial ℕ), M.blank = none ∧ ∀ x,
      (L x ↔ M.AcceptsInSpace (x.map some) (q.eval x.length)) ∧
      ((∃ N c, M.Reaches N (M.initConfig (x.map some)) c ∧ c.state ∈ M.accept) → L x) := by
  obtain ⟨p, hp, hpL⟩ := hL
  obtain ⟨R⟩ := nonempty_srealizer hp
  obtain ⟨k, M, hblank, hM⟩ := exists_tm (dCode R) (dK R) 0 (dCode_wf R) (by unfold dK; omega)
  set K := dK R
  let q : Polynomial ℕ := Polynomial.X + 2 + (9 * Polynomial.X + 4 + R.space) * (Polynomial.C (K : ℕ) + 1)
  refine ⟨k, M, q, hblank, fun x => ⟨⟨fun hx => ?_, fun hx => ?_⟩, fun hx => ?_⟩⟩
  · obtain ⟨n, σ', ha, hr⟩ := dCode_complete R ((hpL x).1 hx)
    obtain ⟨-, hsp⟩ := (hM x).2 n _ σ' (by omega) hr ha
    refine acceptsInSpace_mono hsp (le_of_eq ?_)
    simp [q]; ring
  · obtain ⟨n, c, hr, hc⟩ := hx
    obtain ⟨T, σ', hr', ha⟩ := (hM x).1 ⟨n, c, hr.reaches M, hc⟩
    exact (hpL x).2 (dCode_sound R ⟨T, σ', hr', ha⟩)
  · obtain ⟨T, σ', hr', ha⟩ := (hM x).1 hx
    exact (hpL x).2 (dCode_sound R ⟨T, σ', hr', ha⟩)

end Mach

end HTN
