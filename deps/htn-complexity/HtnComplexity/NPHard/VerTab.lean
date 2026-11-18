import HtnComplexity.NPHard.CodeTab
import ComplexityTheory.Complexity.Hypotheses
/-!
# The tableau of a polynomial-time verifier

For the machine `topTM R` of a realizer `R` of a function `f` of Cobham's class
(`CobhamTM/CobhamToTM.lean`) and a certificate bound `(|x| + 1)^k`, the tableau `verTab R k x`
(`StackCNF.lean`) has the doubled bits of `x` followed by the separator `false, true` as fixed
beginning of the input stack, and the certificate as free part.

* `HTN.NPHard.satisfiable_verTab_iff` — its formula is satisfiable exactly when some
  certificate `w` with `|w| ≤ (|x| + 1)^k` makes `f [pairStr x w]` start with `true`.
-/

namespace HTN.NPHard

open HTN.PTime HTN.PTime.CobhamTM HTN.PTime.CobhamTM.Prog Turing HTN.Syn

/-- The fixed beginning of the verifier's input: `x` with every bit doubled, then `false, true`. -/
def pairPre (x : List Bool) : List Bool := (x.flatMap fun b => [b, b]) ++ [false, true]

theorem pairStr_eq (x w : List Bool) : pairStr x w = pairPre x ++ w := by
  simp [pairStr, pairPre]

theorem length_pairPre (x : List Bool) : (pairPre x).length = 2 * x.length + 2 := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairPre] at ih ⊢; omega

section

variable {f : Fn} (R : Realizer f) (k : ℕ)

/-- The code of the verifier. -/
noncomputable abbrev vC : List Instr := topCode R

/-- The largest stack of the verifier. -/
noncomputable abbrev vN : ℕ := topN R

/-- The certificate bound. -/
def vB (x : List Bool) : ℕ := (x.length + 1) ^ k

/-- The number of steps. -/
noncomputable def vT (x : List Bool) : ℕ := (topTime R).eval ((pairPre x).length + vB k x)

/-- **The tableau of the verifier on the input `x`.** -/
noncomputable def verTab (x : List Bool) : Tab (Fin ((vC R).length + 1)) (Fin (vN R + 1)) Bool where
  step := codeStep (vC R) (vN R)
  c0 := lab (vC R).length 0
  k0 := 0
  a0 := false
  a1 := true
  pre := pairPre x
  B := vB k x
  T := vT R k x
  W := (pairPre x).length + vB k x + vT R k x + 1
  acc := [Fin.last _]
  k1 := stk (vN R) 2
  aT := true

theorem verTab_next (x : List Bool) : (verTab R k x).next = codeNext (vC R) (vN R) := rfl

theorem map_bsym (x w : List Bool) : w.map (verTab R k x).bsym = w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all [Tab.bsym, verTab]

theorem init_verTab (x w : List Bool) :
    (verTab R k x).init w = projCfg (C := vC R) (N := vN R)
      (initList (topTM R) (pairStr x w)) := by
  simp only [Tab.init, map_bsym, projCfg, initList, Option.getD_some, pairStr_eq]
  refine Prod.ext rfl ?_
  funext j
  simp only
  split_ifs with h1 h2 h2
  · subst h1; rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem head?_eq_some_true_iff (l : List Bool) : l.head? = some true ↔ l.getD 0 false = true := by
  cases l <;> simp

/-- **One certificate.** -/
theorem accepts_verTab_iff (x w : List Bool) (hw : w.length ≤ vB k x) :
    (verTab R k x).Accepts ((verTab R k x).next^[(verTab R k x).T] ((verTab R k x).init w)) ↔
      (f [pairStr x w]).getD 0 false = true := by
  obtain ⟨⟨⟨s, hs⟩, hsle⟩⟩ := topTM_outputs R (pairStr x w)
  have hsT : s ≤ (verTab R k x).T := by
    refine hsle.trans (Polynomial.eval_mono_nat _ ?_)
    rw [pairStr_eq, List.length_append]; omega
  have hrun := iterate_next_eq_halt (vC R) (vN R) hsT
    (initList (topTM R) (pairStr x w)) _ _ hs
  rw [verTab_next, init_verTab, hrun]
  simp only [Tab.Accepts, verTab, List.mem_singleton, true_and]
  rw [← head?_eq_some_true_iff]
  rw [dif_pos (show stk (vN R) 2 = (topTM R).k₁ from rfl)]
  rfl

/-- **The tableau formula of the verifier.** -/
theorem satisfiable_verTab_iff (x : List Bool) :
    Satisfiable (verTab R k x).cnf ↔
      ∃ w : List Bool, w.length ≤ (x.length + 1) ^ k ∧ (f [pairStr x w]).getD 0 false = true := by
  rw [Tab.satisfiable_cnf_iff _ (by simp [verTab])]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, (accepts_verTab_iff R k x w hw).1 h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, (accepts_verTab_iff R k x w hw).2 h⟩

end

end HTN.NPHard
