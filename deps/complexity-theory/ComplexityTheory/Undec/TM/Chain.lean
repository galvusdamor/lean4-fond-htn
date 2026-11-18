import Mathlib.Computability.TMToPartrec
import Mathlib.Computability.TuringMachine

/-!
# A fixed Turing machine with an undecidable halting problem

Mathlib provides a `TM2` machine `Turing.PartrecToTM2.tr` that evaluates the codes of
`Turing.ToPartrec` (`Turing.PartrecToTM2.tr_eval`), together with the translations of a `TM2`
machine into a `TM1` machine (`Turing.TM2to1`) and of a `TM1` machine into a `TM0` machine
(`Turing.TM1to0`).  Composing the three gives, for every fixed code `c₀`, a *plain Turing
machine* `N0` on a two-way infinite tape over the finite alphabet `Gam1` which

* halts, started in the control state `q0 c₀` on the tape holding `initTape v`, exactly when
  `c₀` converges on the input `v` (`HTN.Undec.TMChain.dom_chain`), and
* only ever visits control states in the finite set `S0 c₀` (`HTN.Undec.TMChain.supports`).

This is the input to the two-stack simulation of `ComplexityTheory/Undec/Sim/`.
-/

namespace HTN

namespace Undec

namespace TMChain

open Turing Turing.PartrecToTM2 Turing.ToPartrec

instance : Fintype K' := ⟨{K'.main, K'.rev, K'.aux, K'.stack}, by intro x; cases x <;> decide⟩

/-- The stack alphabet of the `TM2` machine: the same alphabet for each of the four stacks. -/
abbrev Gam : K' → Type := fun _ => Γ'

/-- The internal state of the `TM2` machine. -/
abbrev Sig := Option Γ'

/-- The control states of the `TM1` machine. -/
abbrev Lam1 := TM2to1.Λ' K' Gam Λ' Sig

/-- The tape alphabet of the `TM1` and `TM0` machines. -/
abbrev Gam1 := TM2to1.Γ' K' Gam

/-- The `TM1` machine simulating `Turing.PartrecToTM2.tr`. -/
noncomputable def M1 : Lam1 → TM1.Stmt Gam1 Lam1 Sig := TM2to1.tr PartrecToTM2.tr

/-- The control states of the `TM0` machine. -/
abbrev Lam0 := TM1to0.Λ' M1

/-- **The Turing machine**: a `TM0` machine over the finite alphabet `Gam1`. -/
noncomputable def N0 : Lam0 → Gam1 → Option (Lam0 × TM0.Stmt Gam1) := TM1to0.tr M1

/-- The control state in which the machine starts evaluating the code `c0`. -/
noncomputable def q0 (c0 : Code) : Lam0 :=
  (some (M1 (TM2to1.Λ'.normal (trNormal c0 Cont'.halt))), (none : Sig))

/-- The finite set of control states of the `TM1` machine relevant to `c0`. -/
noncomputable def S1 (c0 : Code) : Finset Lam1 :=
  TM2to1.trSupp PartrecToTM2.tr (codeSupp c0 Cont'.halt)

/-- The finite set of control states of the `TM0` machine relevant to `c0`. -/
noncomputable def S0 (c0 : Code) : Finset Lam0 := TM1to0.trStmts M1 (S1 c0)

/-- The initial tape: the input `v`, laid out as the `TM2` emulator expects it. -/
noncomputable def initTape (v : List ℕ) : List Gam1 := TM2to1.trInit K'.main (trList v)

/-! ### The finite support -/

theorem start_mem_supp (c0 : Code) : q0 c0 ∈ S0 c0 := by
  letI : Inhabited Λ' := ⟨trNormal c0 Cont'.halt⟩
  exact (TM1to0.tr_supports _ (TM2to1.tr_supports _ (PartrecToTM2.tr_supports c0 Cont'.halt))).1

theorem supports (c0 : Code) {q : Lam0} {a : Gam1} {q' : Lam0} {st : TM0.Stmt Gam1}
    (h : (q', st) ∈ N0 q a) (hq : q ∈ S0 c0) : q' ∈ S0 c0 := by
  letI : Inhabited Λ' := ⟨trNormal c0 Cont'.halt⟩
  exact (TM1to0.tr_supports _
    (TM2to1.tr_supports _ (PartrecToTM2.tr_supports c0 Cont'.halt))).2 h hq

/-! ### The translation of configurations -/

theorem trCfg_inv {q : Option Λ'} {v : Sig} {S : ∀ k, List (Gam k)}
    {d : TM1.Cfg Gam1 Lam1 Sig}
    (h : TM2to1.TrCfg (⟨q, v, S⟩ : TM2.Cfg Gam Λ' Sig) d) :
    ∃ L, (∀ k, ListBlank.map (Turing.proj k) L = ListBlank.mk (((S k).map some).reverse)) ∧
      d = ⟨q.map TM2to1.Λ'.normal, v, Tape.mk' ∅ (TM2to1.addBottom L)⟩ := by
  cases h with | mk L hL => exact ⟨L, hL, rfl⟩

theorem trCfg_gen (q : Option Λ') (v : Sig) (k : K') (L : List (Gam k)) :
    TM2to1.TrCfg (⟨q, v, Function.update (fun _ => []) k L⟩ : TM2.Cfg Gam Λ' Sig)
      ⟨q.map TM2to1.Λ'.normal, v, Tape.mk₁ (TM2to1.trInit k L)⟩ := by
  obtain ⟨L', hL', heq⟩ := trCfg_inv (TM2to1.trCfg_init (Λ := Λ') (σ := Sig) k L)
  have htape : (Tape.mk₁ (TM2to1.trInit k L) : Tape Gam1)
      = Tape.mk' ∅ (TM2to1.addBottom L') := congrArg TM1.Cfg.Tape heq
  rw [htape]
  exact ⟨L', hL'⟩

theorem stk_eq (v : List ℕ) :
    K'.elim (trList v) [] [] [] = Function.update (fun _ => []) K'.main (trList v) := by
  funext k; cases k <;> simp [Function.update]

/-! ### Correctness -/

/-- **The Turing machine halts exactly when the code converges.** -/
theorem dom_chain (c0 : Code) (v : List ℕ) :
    (Turing.eval (TM0.step N0) ⟨q0 c0, Tape.mk₁ (initTape v)⟩).Dom ↔ (Code.eval c0 v).Dom := by
  set B : TM1.Cfg Gam1 Lam1 Sig :=
    ⟨some (TM2to1.Λ'.normal (trNormal c0 Cont'.halt)), none, Tape.mk₁ (initTape v)⟩ with hB
  have hA : TM2to1.TrCfg (PartrecToTM2.init c0 v) B := by
    have := trCfg_gen (some (trNormal c0 Cont'.halt)) none K'.main (trList v)
    rw [PartrecToTM2.init, stk_eq]
    exact this
  have h1 : (Turing.eval (TM1.step M1) B).Dom
      ↔ (Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c0 v)).Dom :=
    Turing.tr_eval_dom (TM2to1.tr_respects PartrecToTM2.tr) hA
  have h0 : (Turing.eval (TM0.step (TM1to0.tr M1)) (TM1to0.trCfg M1 B)).Dom
      ↔ (Turing.eval (TM1.step M1) B).Dom :=
    Turing.tr_eval_dom (TM1to0.tr_respects M1) rfl
  have hcfg : TM1to0.trCfg M1 B = ⟨q0 c0, Tape.mk₁ (initTape v)⟩ := rfl
  rw [hcfg] at h0
  rw [show (TM0.step (TM1to0.tr M1)) = TM0.step N0 from rfl] at h0
  rw [h0, h1, PartrecToTM2.tr_eval]
  rfl

end TMChain

end Undec

end HTN
