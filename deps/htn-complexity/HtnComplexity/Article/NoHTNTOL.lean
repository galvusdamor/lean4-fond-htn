import HtnComplexity.Article.NoHTNTOExecT
import HtnComplexity.Article.PlanEx
import ComplexityTheory.Lang.LogDSL
/-!
# Thm. 4.2.10: totally ordered non-hierarchical HTN planning is in `L`

A non-hierarchical problem with a totally ordered initial task network has one plan: its tasks
by rank (`HtnComplexity/Article/NoHTNTORank.lean`).  A deterministic machine with a constant
number of registers of `O(log n)` bits checks, on the input,

1. that it is the code of a description (the parser `HTN.Logspace.parseT`),
2. that the description is well formed, non-hierarchical and totally ordered
   (`HTN.Article.NoHTNTO.validT`, `noHTNT`, `toT`),
3. that the plan by ranks is executable and reaches the goal, fact by fact: whether a fact holds
   after `k` steps is a fold over the steps with one bit, the step `j` being found by counting
   ranks (`HTN.Article.NoHTNTO.execT`).

The machine is written as a term of the fold language `HTN.Cx.LTerm`, compiled to a register
program by `HTN.Cx.inL_of_term`.

* **`HTN.Article.thm_4_2_10`** — `PlanEx^{noHTN ∩ TO}_htn ∈ L`.
-/

namespace HTN

namespace Article

namespace NoHTNTO

open Cx Cx.LTerm Syn Syn.PolyDom Logspace NoHTN

/-! ### Non-hierarchical networks, on the labels -/

theorem filter_key_eq {l : List (ℕ × Bool × ℕ)} (hnd : (l.map Prod.fst).Nodup) {q : ℕ × Bool × ℕ}
    (hq : q ∈ l) : l.filter (fun r => r.1 == q.1) = [q] := by
  induction l with
  | nil => simp at hq
  | cons r l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hq with rfl | hq'
    · have : l.filter (fun r => r.1 == q.1) = [] := by
        rw [List.filter_eq_nil_iff]
        intro r' hr' he
        have he' : r'.1 = q.1 := by simpa using he
        exact hnd.1 (he' ▸ List.mem_map_of_mem hr')
      simp [List.filter_cons, this]
    · have hne : r.1 ≠ q.1 := fun he => hnd.1 (by rw [he]; exact List.mem_map_of_mem hq')
      simp [List.filter_cons, hne, ih hnd.2 hq']

theorem isNoHTN_iff {p : ProbDesc} (hv : p.Valid) :
    p.toProblem.IsNoHTN ↔ ∀ q ∈ p.tnI.lbl, q.2.1 = false := by
  show p.tnI.toTaskNetwork.IsPrimitive ↔ _
  rw [← noHTNB_iff, noHTNB, List.all_eq_true]
  have hperm := hv.tnI.lbl_perm
  have hnd : (p.tnI.lbl.map Prod.fst).Nodup := hperm.nodup_iff.2 hv.tnI.nodup
  constructor
  · intro h q hq
    have hi : q.1 ∈ p.tnI.ids := hperm.subset (List.mem_map_of_mem hq)
    have := h _ hi
    rw [labelB, filter_key_eq hnd hq] at this
    simpa using this
  · intro h i hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (hperm.symm.subset hi)
    rw [labelB, filter_key_eq hnd hq]
    simp [h q hq]

/-! ### The check -/

/-- **The decision term.** -/
def checkT : LTerm :=
  and (eq (parseT fProb 0 (.lit 0) .len (.lit 0)) .len) (and validT (and noHTNT (and toT execT)))

theorem virt_self (y : List Bool) : virt y 0 0 y.length = y := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [virt, rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem parse_ok_iff (y : List Bool) : prs fProb y 0 = y.length ↔ ∃ p : ProbDesc, enc p = y := by
  constructor
  · intro h
    obtain ⟨a, r, ha⟩ := exists_of_prs_le fProb y 0 (by omega)
    have he := prs_enc fProb y 0 a r ha
    simp only [List.drop_zero] at ha
    have hr : r = [] := by
      have := congrArg List.length ha
      simp only [List.length_append] at this
      rw [h] at he
      exact List.length_eq_zero_iff.1 (by omega)
    subst hr
    exact ⟨a, by rw [← enc_fProb]; simpa using ha.symm⟩
  · rintro ⟨p, rfl⟩
    have := prs_enc fProb (enc p) 0 p [] (by rw [enc_fProb]; simp)
    rw [this, enc_fProb]; simp

/-- **The meaning of the decision term.** -/
theorem eval_checkT {y : List Bool} {M : ℕ} (hM : y.length + 2 ≤ M) :
    eval y M [] checkT ≠ 0 ↔ PlanEx (fun P => P.IsNoHTN ∧ P.IsTO) y := by
  have hpar : eval y M [] (parseT fProb 0 (.lit 0) .len (.lit 0)) = prs fProb y 0 := by
    rw [eval_parseT hM fProb 0 _ _ _ [] (by simp [eval])]
    simp only [eval]; rw [virt_self]
  rw [checkT, ne0_and, eval_eq _ _ _ (by omega), hpar]
  simp only [eval]
  by_cases hc : ∃ p : ProbDesc, enc p = y
  · obtain ⟨p, rfl⟩ := hc
    have hp : At (enc p) 0 0 fProb p := by
      have := at_input (enc p); rw [← enc_fProb] at this ⊢; exact this
    rw [if_pos ((parse_ok_iff _).2 ⟨p, rfl⟩), planEx_enc_iff, ne0_and, ne0_and, ne0_and,
      eval_validT hM hp, eval_noHTNT hM hp, eval_toT hM hp]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, true_and]
    constructor
    · rintro ⟨hv, hn, hto, he⟩
      have hnh := (isNoHTN_iff hv).2 hn
      refine ⟨hv, ⟨hnh, (isTO_tnI_iff hv).2 hto, isTO_M_of_noHTN hnh⟩, ?_⟩
      rw [solvable_iff_execB hv hnh hto, execB_iff_execF]
      exact (eval_execT hM hp hv hn hto []).1 he
    · rintro ⟨hv, ⟨hnh, hto, -⟩, hs⟩
      have hn := (isNoHTN_iff hv).1 hnh
      have hto' := (isTO_tnI_iff hv).1 hto
      refine ⟨hv, hn, hto', (eval_execT hM hp hv hn hto' []).2 ?_⟩
      rw [solvable_iff_execB hv hnh hto', execB_iff_execF] at hs
      exact hs
  · rw [if_neg (fun h => hc ((parse_ok_iff y).1 h))]
    simp only [ne_eq, not_true_eq_false, false_and, false_iff]
    rintro ⟨p, hp, -⟩
    exact hc ⟨p, hp⟩

end NoHTNTO

open NoHTNTO in
/-- **Thm. 4.2.10**: plan existence for totally ordered problems without compound tasks in the
initial task network is in `L`. -/
theorem thm_4_2_10 : Cx.L (PlanEx fun P => P.IsNoHTN ∧ P.IsTO) :=
  Cx.inL_of_term checkT (checkT.maxLit + 3) (by omega) fun y =>
    (eval_checkT (M := y.length + (checkT.maxLit + 3)) (by omega)).symm

end Article

end HTN
