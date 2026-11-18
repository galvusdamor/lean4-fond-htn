import HtnComplexity.Article.TICors
import HtnPlanning.Article.Unfold
/-!
# Cor. 4.2.23 for unrestricted problems

`HTN.Article.cor_4_2_23_unres`: `PlanEx^{UNRES ∩ TO-M}_tihtn ∈ PSPACE`.  The certificate is a list
`R` of names closed under reachability (`HTN.Article.closedB`), with the total-order check of the
methods of its names; the progression bound is the TIHTN bound for totally ordered methods
obtained by unfolding the ancestors (`HTN.Article.Problem.tihtn_bound_TOM`).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- **`R` is closed under reachability.** -/
def closedB (x : ProbDesc × List ℕ) : Bool :=
  x.1.tnI.ids.all (fun y => !(lblOf x.1.tnI y).1 || decide ((lblOf x.1.tnI y).2 ∈ x.2)) &&
    x.1.methods.all fun e => !decide (e.1 ∈ x.2) || e.2.ids.all fun y => !(lblOf e.2 y).1 ||
      decide ((lblOf e.2 y).2 ∈ x.2)

theorem closedB_iff (p : ProbDesc) (R : List ℕ) : closedB (p, R) = true ↔
    (∀ x ∈ p.tnI.ids, ∀ c, lblOf p.tnI x = (true, c) → c ∈ R) ∧
      ∀ e ∈ p.methods, e.1 ∈ R → ∀ x ∈ e.2.ids, ∀ c, lblOf e.2 x = (true, c) → c ∈ R := by
  unfold closedB
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx c hc => ?_, fun e he hR x hx c hc => ?_⟩
    · rcases h1 x hx with h | h
      · rw [hc] at h; cases h
      · rw [hc] at h; exact h
    · rcases h2 e he with h | h
      · exact absurd hR h
      · rcases h x hx with h' | h'
        · rw [hc] at h'; cases h'
        · rw [hc] at h'; exact h'
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun e he => ?_⟩
    · rcases hl : lblOf p.tnI x with ⟨_ | _, c⟩
      · exact Or.inl rfl
      · exact Or.inr (h1 x hx c hl)
    · by_cases hR : e.1 ∈ R
      · refine Or.inr fun x hx => ?_
        rcases hl : lblOf e.2 x with ⟨_ | _, c⟩
        · exact Or.inl rfl
        · exact Or.inr (h2 e he hR x hx c hl)
      · exact Or.inl hR

theorem pt_closedB : PT closedB := by
  have hR : PT fun x : ProbDesc × List ℕ => x.2 := PT.snd
  have htn : PT fun x : ProbDesc × List ℕ => x.1.tnI := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))
  have hA : PT fun x : ProbDesc × List ℕ =>
      x.1.tnI.ids.all (fun y => !(lblOf x.1.tnI y).1 || decide ((lblOf x.1.tnI y).2 ∈ x.2)) :=
    PT.all (PT.fst.comp htn) (PT.or (PT.not (PT.fst.comp (pt_lblOf (htn.comp PT.fst) PT.snd)))
      (PT.elem (hR.comp PT.fst) (PT.snd.comp (pt_lblOf (htn.comp PT.fst) PT.snd))))
  have hl := pt_lblOf (α := ((ProbDesc × List ℕ) × MethodDesc) × ℕ) (PT.snd.comp (PT.snd.comp PT.fst))
    PT.snd
  have hB : PT fun x : ProbDesc × List ℕ => x.1.methods.all fun e => !decide (e.1 ∈ x.2) ||
      e.2.ids.all fun y => !(lblOf e.2 y).1 || decide ((lblOf e.2 y).2 ∈ x.2) :=
    PT.all (PT.snd.comp (PT.fst.comp PT.fst)) (PT.or (PT.not (PT.elem (hR.comp PT.fst)
      (PT.fst.comp PT.snd))) (PT.all (p := fun (r : (ProbDesc × List ℕ) × MethodDesc) (y : ℕ) =>
        !(lblOf r.2.2 y).1 || decide ((lblOf r.2.2 y).2 ∈ r.1.2))
        (PT.fst.comp (PT.snd.comp PT.snd)) (PT.or (PT.not (PT.fst.comp hl))
          (PT.elem (hR.comp (PT.fst.comp PT.fst)) (PT.snd.comp hl)))))
  exact (PT.and hA hB).of_eq fun _ => rfl

/-- The check of `UNRES ∩ TO-M`. -/
def unresTOMB (x : ProbDesc × List ℕ) : Bool := closedB x && methodsRB toB x.1 x.2

theorem pt_unresTOMB : PT unresTOMB :=
  (PT.and pt_closedB (pt_methodsRB pt_toB PT.fst PT.snd)).of_eq fun _ => rfl

theorem reach_finite (p : ProbDesc) (hp : p.Valid) :
    {c | p.toProblem.toPos.ReachableName c}.Finite ∧
      {c | p.toProblem.toPos.ReachableName c}.ncard ≤ sz p := by
  have hsub : {c | p.toProblem.toPos.ReachableName c} ⊆ ((numsOf p).toFinset : Set ℕ) :=
    fun c hc => by simpa using reach_numsOf hp hc
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc {c | p.toProblem.toPos.ReachableName c}.ncard ≤ ((numsOf p).toFinset : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (numsOf p).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (numsOf p).length := List.toFinset_card_le _
    _ ≤ sz p := length_numsOf_le p

open Classical in
/-- **Corollary 4.2.23 (UNRES ∩ TO-M).** `PlanEx^{UNRES ∩ TO-M}_tihtn ∈ PSPACE`. -/
theorem cor_4_2_23_unres : Cx.PSPACE (PlanExTI fun P => UNRES P ∧ P.IsTO_M) := by
  let r : Polynomial ℕ := Polynomial.X * (2 * Polynomial.X + 2) + 1 +
    Polynomial.X * (1 + Polynomial.X * (2 * Polynomial.X + 2))
  have hr : ∀ n, r.eval n = n * (2 * n + 2) + 1 + n * (1 + n * (2 * n + 2)) := fun n => by simp [r]
  refine inPSpace_planExTI pt_unresTOMB (fun p R hp hb => ?_) r fun p hp hY => ⟨?_, ?_⟩
  · simp only [unresTOMB, Bool.and_eq_true] at hb
    obtain ⟨h1, h2⟩ := (closedB_iff p R).1 hb.1
    exact ⟨trivial, methodsRB_sound hp (fun _ hc => reach_mem_of_closed h1 h2 hc)
      (fun ht => toB_iff ht) hb.2⟩
  · let R := (numsOf p).dedup.filter fun c => decide (p.toProblem.toPos.ReachableName c)
    have hRch : ∀ c ∈ R, p.toProblem.toPos.ReachableName c := fun c hc => by
      simpa using (List.mem_filter.1 hc).2
    have hRmem : ∀ c, p.toProblem.toPos.ReachableName c → c ∈ R := fun c h1 =>
      List.mem_filter.2 ⟨List.mem_dedup.2 (reach_numsOf hp h1), by simpa using h1⟩
    refine ⟨R, ?_, ?_⟩
    · simp only [unresTOMB, Bool.and_eq_true]
      refine ⟨(closedB_iff p R).2 ⟨fun x hx c hc => hRmem c ?_, fun e he hR x hx c hc => hRmem c ?_⟩,
        methodsRB_complete hp hRch (fun ht => toB_iff ht) hY.2⟩
      · have hxT : x ∈ p.toProblem.toPos.tnI.T := by
          simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
        exact HTN.Problem.ReachableName.tnI hxT (label_eq_inr.2 hc)
      · have hxT : x ∈ (MethodDesc.toMethod e).subtasks.T := by
          simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hx
        exact HTN.Problem.ReachableName.method
          (show MethodDesc.toMethod e ∈ p.toProblem.methods from ⟨e, he, rfl⟩) (hRch _ hR) hxT
          (label_eq_inr.2 hc)
    · rw [hr]
      have hK : (numsOf p).length ≤ sz p := length_numsOf_le p
      have hRl : R.length ≤ sz p :=
        ((List.length_filter_le _ _).trans (List.dedup_sublist _).length_le).trans hK
      have : sz R ≤ R.length * (2 * sz p + 2) + 1 := sz_list_le fun a ha =>
        sz_le_of_mem_numsOf (List.mem_dedup.1 (List.mem_filter.1 ha).1)
      have : R.length * (2 * sz p + 2) ≤ sz p * (2 * sz p + 2) := Nat.mul_le_mul_right _ hRl
      omega
  · obtain ⟨hfin, hN⟩ := reach_finite p hp
    have hb := p.toProblem.tihtn_bound_TOM (wf_toProblem p) hY.2 hfin (tnI_card_le p)
      (meth_card_le p)
    refine IsTIHTNProgBound.mono hb ?_
    rw [hr]
    have : (sz p - 1) * (2 * {c | p.toProblem.toPos.ReachableName c}.ncard + 2) ≤
        sz p * (2 * sz p + 2) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    have : sz p * (1 + (sz p - 1) * (2 * {c | p.toProblem.toPos.ReachableName c}.ncard + 2)) ≤
        sz p * (1 + sz p * (2 * sz p + 2)) := Nat.mul_le_mul_left _ (by omega)
    omega

end Article

end HTN
