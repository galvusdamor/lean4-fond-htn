import HtnComplexity.Article.NoHTNTOSteps
/-!
# The execution check in logarithmic space

`HTN.Article.NoHTNTO.hPT`, `HTN.Article.NoHTNTO.hNT` follow one fact through the first `k`
steps of the plan by ranks (a fold over the steps with one bit), and
`HTN.Article.NoHTNTO.execT` checks every precondition and the goal
(`HTN.Article.NoHTNTO.eval_execT`).
-/

namespace HTN

namespace Article

namespace NoHTNTO

open Cx Cx.LTerm Syn Syn.PolyDom Logspace NoHTN

variable {y : List Bool} {M : ℕ}

theorem eval_memKeyT_val (hM : y.length + 2 ≤ M) {dx d : ℕ} {X L : LTerm} {env : List ℕ} {x : ℕ}
    {F : Fmt} {l : List F.ty} {key : F.ty → ℕ} (hx : At y dx (eval y M env X) .nat x)
    (h : At y d (eval y M env L) (.list F) l) (hk : Key y (d + 1) F key) :
    eval y M env (memKeyT dx X d L) = if x ∈ l.map key then 1 else 0 := by
  have hiff := eval_memKeyT hM hx h hk
  have h01 : eval y M env (memKeyT dx X d L) = 0 ∨ eval y M env (memKeyT dx X d L) = 1 := by
    rw [memKeyT, exE, eval_existsB]; split_ifs <;> simp
  by_cases hm : x ∈ l.map key
  · rw [if_pos hm]; have := hiff.2 hm; omega
  · rw [if_neg hm]; by_contra hne; exact hm (hiff.1 hne)

/-- `f` (at `(dx, F)`) holds after the first `k` steps. -/
def hPT (kT : LTerm) (dx : ℕ) (F : LTerm) : LTerm :=
  .fold kT (memKeyT dx F 0 locInst)
    (.ite (memKeyT dx (lift 2 F) 1 (effPLoc (.var 1))) (.lit 1)
      (and (.var 0) (not (memKeyT dx (lift 2 F) 1 (effNLoc (.var 1))))))

/-- `f` (at `(dx, F)`) does not hold after the first `k` steps. -/
def hNT (kT : LTerm) (dx : ℕ) (F : LTerm) : LTerm :=
  .fold kT (not (memKeyT dx F 0 locInst))
    (.ite (and (memKeyT dx (lift 2 F) 1 (effNLoc (.var 1))) (not (memKeyT dx (lift 2 F) 1 (effPLoc (.var 1)))))
      (.lit 1) (and (.var 0) (not (memKeyT dx (lift 2 F) 1 (effPLoc (.var 1))))))

section Exec

variable (hM : y.length + 2 ≤ M) {p : ProbDesc} (hp : At y 0 0 fProb p) (hv : p.Valid)
  (hn : ∀ q ∈ p.tnI.lbl, q.2.1 = false) (hto : TOL p.tnI)
include hM hp hv hn hto

theorem at_effs {kT : LTerm} {env : List ℕ} {k : ℕ} (hk : eval y M env kT = k) (hkn : k < p.tnI.ids.length) :
    At y 1 (eval y M env (precPLoc kT)) fNL (actOf p ((planActs p).getD k 0)).2.1 ∧
    At y 1 (eval y M env (precNLoc kT)) fNL (actOf p ((planActs p).getD k 0)).2.2.1 ∧
    At y 1 (eval y M env (effPLoc kT)) fNL (actOf p ((planActs p).getD k 0)).2.2.2.1 ∧
    At y 1 (eval y M env (effNLoc kT)) fNL (actOf p ((planActs p).getD k 0)).2.2.2.2 := by
  have h0 := at_actLoc hM hp hv hto hn hk hkn
  have h1 := At.p2 hM h0
  have h2 := At.p2 hM h1
  have h3 := At.p2 hM h2
  exact ⟨At.p1 h1, At.p1 h2, At.p1 h3, At.p2 hM h3⟩

theorem eval_hPT {kT : LTerm} {dx : ℕ} {F : LTerm} {env : List ℕ} {k f : ℕ} (hk : eval y M env kT = k)
    (hkn : k ≤ p.tnI.ids.length) (hf : At y dx (eval y M env F) .nat f) :
    eval y M env (hPT kT dx F) = if hP p (planActs p) k f then 1 else 0 := by
  rw [hPT, eval, hk]
  clear hk
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, hP]
    rw [eval_memKeyT_val hM hf (At.p1 (at_inst hM hp env)) (key_nat _), List.map_id]
    simp [ProbDesc.init]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have key : ∀ acc, eval y M (acc :: k :: env) (.ite (memKeyT dx (lift 2 F) 1 (effPLoc (.var 1))) (.lit 1)
        (and (.var 0) (not (memKeyT dx (lift 2 F) 1 (effNLoc (.var 1)))))) =
        if f ∈ (actOf p ((planActs p).getD k 0)).2.2.2.1 then 1 else
          if acc ≠ 0 ∧ f ∉ (actOf p ((planActs p).getD k 0)).2.2.2.2 then 1 else 0 := by
      intro acc
      have hf' : At y dx (eval y M (acc :: k :: env) (lift 2 F)) .nat f := by rw [eval_lift2]; exact hf
      obtain ⟨-, -, hE, hN⟩ := at_effs hM hp hv hn hto (env := acc :: k :: env) (kT := .var 1) (k := k)
        (by simp [eval]) (by omega)
      simp only [eval, eval_and, eval_not, List.getD_cons_zero,
        eval_memKeyT_val hM hf' hE (key_nat _), eval_memKeyT_val hM hf' hN (key_nat _), List.map_id]
      by_cases h1 : f ∈ (actOf p ((planActs p).getD k 0)).2.2.2.1 <;>
        by_cases h2 : f ∈ (actOf p ((planActs p).getD k 0)).2.2.2.2 <;> simp [h1, h2]
    rw [key, hP]
    generalize actOf p ((planActs p).getD k 0) = A
    by_cases h1 : f ∈ A.2.2.2.1 <;> by_cases h2 : f ∈ A.2.2.2.2 <;>
      by_cases h3 : hP p (planActs p) k f = true <;> simp [h1, h2, h3]

theorem eval_hNT {kT : LTerm} {dx : ℕ} {F : LTerm} {env : List ℕ} {k f : ℕ} (hk : eval y M env kT = k)
    (hkn : k ≤ p.tnI.ids.length) (hf : At y dx (eval y M env F) .nat f) :
    eval y M env (hNT kT dx F) = if hN p (planActs p) k f then 1 else 0 := by
  rw [hNT, eval, hk]
  clear hk
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, hN, eval_not]
    rw [eval_memKeyT_val hM hf (At.p1 (at_inst hM hp env)) (key_nat _), List.map_id]
    by_cases h : f ∈ p.init
    · simp only [ProbDesc.init] at h; simp [ProbDesc.init, h]
    · simp only [ProbDesc.init] at h; simp [ProbDesc.init, h]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have key : ∀ acc, eval y M (acc :: k :: env)
        (.ite (and (memKeyT dx (lift 2 F) 1 (effNLoc (.var 1))) (not (memKeyT dx (lift 2 F) 1 (effPLoc (.var 1)))))
          (.lit 1) (and (.var 0) (not (memKeyT dx (lift 2 F) 1 (effPLoc (.var 1)))))) =
        if f ∈ (actOf p ((planActs p).getD k 0)).2.2.2.2 ∧ f ∉ (actOf p ((planActs p).getD k 0)).2.2.2.1 then 1
        else if acc ≠ 0 ∧ f ∉ (actOf p ((planActs p).getD k 0)).2.2.2.1 then 1 else 0 := by
      intro acc
      have hf' : At y dx (eval y M (acc :: k :: env) (lift 2 F)) .nat f := by rw [eval_lift2]; exact hf
      obtain ⟨-, -, hE, hN'⟩ := at_effs hM hp hv hn hto (env := acc :: k :: env) (kT := .var 1) (k := k)
        (by simp [eval]) (by omega)
      simp only [eval, eval_and, eval_not, List.getD_cons_zero,
        eval_memKeyT_val hM hf' hE (key_nat _), eval_memKeyT_val hM hf' hN' (key_nat _), List.map_id]
      by_cases h1 : f ∈ (actOf p ((planActs p).getD k 0)).2.2.2.1 <;>
        by_cases h2 : f ∈ (actOf p ((planActs p).getD k 0)).2.2.2.2 <;> simp [h1, h2]
    rw [key, hN]
    generalize actOf p ((planActs p).getD k 0) = A
    by_cases h1 : f ∈ A.2.2.2.1 <;> by_cases h2 : f ∈ A.2.2.2.2 <;>
      by_cases h3 : hN p (planActs p) k f = true <;> simp [h1, h2, h3]

end Exec

/-- **The execution check**: the preconditions of every step and the goal. -/
def execT : LTerm :=
  and (forallB (lenT 0 IDS)
      (and (allE 1 (precPLoc (.var 1)) (hPT (.var 3) 2 (E1 1 (precPLoc (.var 1)))))
        (allE 1 (precNLoc (.var 1)) (hNT (.var 3) 2 (E1 1 (precNLoc (.var 1)))))))
    (and (allE 0 locGP (hPT (lenT 0 IDS) 1 (E1 0 locGP)))
      (allE 0 locGN (hNT (lenT 0 IDS) 1 (E1 0 locGN))))

theorem length_planActs (p : ProbDesc) : (planActs p).length = p.tnI.ids.length := by
  simp [planActs, actsOf, linOf]

theorem eval_execT (hM : y.length + 2 ≤ M) {p : ProbDesc} (hp : At y 0 0 fProb p) (hv : p.Valid)
    (hn : ∀ q ∈ p.tnI.lbl, q.2.1 = false) (hto : TOL p.tnI) (env : List ℕ) :
    eval y M env execT ≠ 0 ↔ ExecF p (planActs p) := by
  have hlen := length_planActs p
  rw [execT, ne0_and, ne0_and, ExecF, hlen]
  refine and_congr ?_ (and_congr ?_ ?_)
  · rw [eval_forallB, lenT_IDS hM hp env]
    have key : ∀ k < p.tnI.ids.length, eval y M (1 :: k :: env)
        (and (allE 1 (precPLoc (.var 1)) (hPT (.var 3) 2 (E1 1 (precPLoc (.var 1)))))
          (allE 1 (precNLoc (.var 1)) (hNT (.var 3) 2 (E1 1 (precNLoc (.var 1)))))) ≠ 0 ↔
        (∀ f ∈ (actOf p ((planActs p).getD k 0)).2.1, hP p (planActs p) k f = true) ∧
          ∀ f ∈ (actOf p ((planActs p).getD k 0)).2.2.1, hN p (planActs p) k f = true := by
      intro k hk
      obtain ⟨hPP, hPN, -, -⟩ := at_effs hM hp hv hn hto (env := 1 :: k :: env) (kT := .var 1)
        (by simp [eval]) hk
      rw [ne0_and, eval_allE hM hPP, eval_allE hM hPN, ← List.forall_getElem, ← List.forall_getElem]
      refine and_congr (forall_congr' fun i => forall_congr' fun hi => ?_)
        (forall_congr' fun i => forall_congr' fun hi => ?_)
      · rw [eval_hPT hM hp hv hn hto (by simp [eval]) hk.le (At.entry2 hM hPP hi 1)]
        simp
      · rw [eval_hNT hM hp hv hn hto (by simp [eval]) hk.le (At.entry2 hM hPN hi 1)]
        simp
    constructor
    · intro h k hk
      have h' : ∀ i < p.tnI.ids.length, eval y M (1 :: i :: env)
          (and (allE 1 (precPLoc (.var 1)) (hPT (.var 3) 2 (E1 1 (precPLoc (.var 1)))))
            (allE 1 (precNLoc (.var 1)) (hNT (.var 3) 2 (E1 1 (precNLoc (.var 1)))))) ≠ 0 := by
        by_contra hc; rw [if_neg hc] at h; exact h rfl
      exact (key k hk).1 (h' k hk)
    · intro h
      rw [if_pos (fun k hk => (key k hk).2 (h k hk))]; simp
  · have hG := at_gP hM hp env
    rw [eval_allE hM hG, ← List.forall_getElem]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    rw [eval_hPT hM hp hv hn hto (lenT_IDS hM hp _) le_rfl (At.entry2 hM hG hi 1)]
    simp
  · have hG := at_gN hM hp env
    rw [eval_allE hM hG, ← List.forall_getElem]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    rw [eval_hNT hM hp hv hn hto (lenT_IDS hM hp _) le_rfl (At.entry2 hM hG hi 1)]
    simp

end NoHTNTO

end Article

end HTN
